// For open-source license, please refer to
// [License](https://github.com/HikariObfuscator/Hikari/wiki/License).
//===----------------------------------------------------------------------===//
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/ADT/Triple.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/NoFolder.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

// Shamefully borrowed from ../Scalar/RegToMem.cpp and .../IR/Instruction.cpp :(
bool valueEscapes(Instruction *Inst) {
  // https://reviews.llvm.org/D137700
  if (!Inst->getType()->isSized())
    return false;

  for (User *U : Inst->users()) {
    Instruction *I = cast<Instruction>(U);
    if (I->getParent() != Inst->getParent()) {
      if (!isa<PHINode>(I)) {
        if (isa<StoreInst>(I) && isa<InvokeInst>(Inst))
          if (I->getParent() == dyn_cast<InvokeInst>(Inst)->getNormalDest() &&
              isa<AllocaInst>(I->getOperand(1)))
            continue;
        return true;
      }
      return true;
    }
  }
  return false;
}
bool hasApplePtrauth(Module *M) {
  for (GlobalVariable &GV : M->globals())
    if (GV.getSection() == "llvm.ptrauth")
      return true;
  return false;
}

void FixFunctionConstantExpr(Function *Func) {
  // Replace ConstantExpr with equal instructions
  // Otherwise replacing on Constant will crash the compiler
  for (BasicBlock &BB : *Func)
    FixBasicBlockConstantExpr(&BB);
}
void FixBasicBlockConstantExpr(BasicBlock *BB) {
  // Replace ConstantExpr with equal instructions
  // Otherwise replacing on Constant will crash the compiler
  // Things to note:
  // - Phis must be placed at BB start so CEs must be placed prior to current BB
  assert(!BB->empty() && "BasicBlock is empty!");
  assert(BB->getParent() && "BasicBlock must be in a Function!");
  Instruction *FunctionInsertPt =
      &*(BB->getParent()->getEntryBlock().getFirstInsertionPt());

  for (Instruction &I : *BB) {
    if (isa<LandingPadInst>(I) || isa<FuncletPadInst>(I) ||
        isa<IntrinsicInst>(I))
      continue;
    for (unsigned int i = 0; i < I.getNumOperands(); i++)
      if (ConstantExpr *C = dyn_cast<ConstantExpr>(I.getOperand(i))) {
        IRBuilder<NoFolder> IRB(&I);
        if (isa<PHINode>(I))
          IRB.SetInsertPoint(FunctionInsertPt);
        Instruction *Inst = IRB.Insert(C->getAsInstruction());
        I.setOperand(i, Inst);
      }
  }
}

#if 0
map<GlobalValue *, StringRef> BuildAnnotateMap(Module &M) {
  map<GlobalValue *, StringRef> VAMap;
  GlobalVariable *glob = M.getGlobalVariable("llvm.global.annotations");
  if (glob != nullptr && glob->hasInitializer()) {
    ConstantArray *CDA = cast<ConstantArray>(glob->getInitializer());
    for (Value *op : CDA->operands()) {
      ConstantStruct *anStruct = cast<ConstantStruct>(op);
      /*
        Structure: [Value,Annotation,SourceFilePath,LineNumber]
        Usually wrapped inside GEP/BitCast
        We only care about Value and Annotation Here
      */
      GlobalValue *Value =
          cast<GlobalValue>(anStruct->getOperand(0)->getOperand(0));
      GlobalVariable *Annotation =
          cast<GlobalVariable>(anStruct->getOperand(1)->getOperand(0));
      if (Annotation->hasInitializer()) {
        VAMap[Value] =
            cast<ConstantDataSequential>(Annotation->getInitializer())
                ->getAsCString();
      }
    }
  }
  return VAMap;
}
#endif

void fixStack(Function *f) {
  // Try to remove phi node and demote reg to stack
  std::vector<PHINode *> tmpPhi;
  std::vector<Instruction *> tmpReg;
  BasicBlock *bbEntry = &*f->begin();
  // Find first non-alloca instruction and create insertion point. This is
  // safe if block is well-formed: it always have terminator, otherwise
  // we'll get and assertion.
  BasicBlock::iterator I = bbEntry->begin();
  while (isa<AllocaInst>(I))
    ++I;
  CastInst *AllocaInsertionPoint = new BitCastInst(
      Constant::getNullValue(Type::getInt32Ty(f->getContext())),
      Type::getInt32Ty(f->getContext()), "reg2mem alloca point", &*I);
  do {
    tmpPhi.clear();
    tmpReg.clear();
    for (BasicBlock &i : *f) {
      for (Instruction &j : i) {
        if (isa<PHINode>(&j)) {
          PHINode *phi = cast<PHINode>(&j);
          tmpPhi.emplace_back(phi);
          continue;
        }
        if (!(isa<AllocaInst>(&j) && j.getParent() == bbEntry) &&
            valueEscapes(&j)) {
          tmpReg.emplace_back(&j);
          continue;
        }
      }
    }
    for (Instruction *I : tmpReg)
      DemoteRegToStack(*I, false, AllocaInsertionPoint);
    for (PHINode *P : tmpPhi)
      DemotePHIToStack(P, AllocaInsertionPoint);
  } while (tmpReg.size() != 0 || tmpPhi.size() != 0);
}

static GlobalVariable *createAnnoStringGV(Module *M, StringRef Str) {
  Constant *s = ConstantDataArray::getString(M->getContext(), Str);
  GlobalVariable *GV = new GlobalVariable(
      *M, s->getType(), true, llvm::GlobalValue::PrivateLinkage, s, ".str");
  GV->setSection("llvm.metadata");
  GV->setUnnamedAddr(llvm::GlobalValue::UnnamedAddr::Global);
  return GV;
}

static Constant *createNewCSForAnnotationWithAppendedStr(
    Function *f, std::vector<Constant *> &Annotations, std::string str) {
  PointerType *GlobalsInt8PtrTy =
      Type::getInt8Ty(f->getParent()->getContext())
          ->getPointerTo(
              f->getParent()->getDataLayout().getDefaultGlobalsAddressSpace());
  Constant *GVInGlobalsAS = f;
  if (f->getAddressSpace() !=
      f->getParent()->getDataLayout().getDefaultGlobalsAddressSpace())
    GVInGlobalsAS = llvm::ConstantExpr::getAddrSpaceCast(
        f,
        f->getValueType()->getPointerTo(
            f->getParent()->getDataLayout().getDefaultGlobalsAddressSpace()));
  Constant *Fields[] = {
      ConstantExpr::getBitCast(GVInGlobalsAS, GlobalsInt8PtrTy),
      ConstantExpr::getBitCast(createAnnoStringGV(f->getParent(), str),
                               GlobalsInt8PtrTy),
      ConstantExpr::getBitCast(
          createAnnoStringGV(f->getParent(),
                             f->getParent()->getSourceFileName()),
          GlobalsInt8PtrTy),
      ConstantInt::get(Type::getInt32Ty(f->getParent()->getContext()), 0),
      ConstantPointerNull::get(GlobalsInt8PtrTy)};
  return ConstantStruct::getAnon(Fields);
}

std::string readAnnotate(Function *f) {
  std::string annotation = "";

  // Get annotation variable
  GlobalVariable *glob =
      f->getParent()->getGlobalVariable("llvm.global.annotations");

  if (glob)
    if (ConstantArray *ca = dyn_cast<ConstantArray>(glob->getInitializer())) {
      for (unsigned i = 0; i < ca->getNumOperands(); ++i)
        if (ConstantStruct *structAn =
                dyn_cast<ConstantStruct>(ca->getOperand(i))) {
          if (ConstantExpr *expr =
                  dyn_cast<ConstantExpr>(structAn->getOperand(0))) {
            if (expr->getOpcode() == Instruction::BitCast &&
                expr->getOperand(0) == f) {
              ConstantExpr *note = cast<ConstantExpr>(structAn->getOperand(1));
              // If it's a GetElementPtr, that means we found the variable
              // containing the annotations
              if (note->getOpcode() == Instruction::GetElementPtr)
                if (GlobalVariable *annoteStr =
                        dyn_cast<GlobalVariable>(note->getOperand(0)))
                  if (ConstantDataSequential *data =
                          dyn_cast<ConstantDataSequential>(
                              annoteStr->getInitializer()))
                    if (data->isString())
                      annotation += data->getAsString().lower() + " ";
            }
          } else if (structAn->getOperand(0) == f) { // opaque pointer
            Constant *note = structAn->getOperand(1);
            if (GlobalVariable *annoteStr =
                    dyn_cast<GlobalVariable>(note->getOperand(0)))
              if (ConstantDataSequential *data =
                      dyn_cast<ConstantDataSequential>(
                          annoteStr->getInitializer()))
                if (data->isString())
                  annotation += data->getAsString().lower() + " ";
          }
        }
    }
  return annotation;
}

void writeAnnotation(Function *f, std::string annotation) {
  Module *M = f->getParent();
  GlobalVariable *glob = M->getGlobalVariable("llvm.global.annotations");
  if (glob) {
    if (ConstantArray *ca = dyn_cast<ConstantArray>(glob->getInitializer())) {
      bool fHasAnnotation = false;
      for (unsigned i = 0; i < ca->getNumOperands(); ++i)
        if (ConstantStruct *structAn =
                dyn_cast<ConstantStruct>(ca->getOperand(i))) {
          if (ConstantExpr *expr =
                  dyn_cast<ConstantExpr>(structAn->getOperand(0))) {
            if (expr->getOpcode() == Instruction::BitCast &&
                expr->getOperand(0) == f) {
              fHasAnnotation = true;
              ConstantExpr *note = cast<ConstantExpr>(structAn->getOperand(1));
              // If it's a GetElementPtr, that means we found the variable
              // containing the annotations
              if (note->getOpcode() == Instruction::GetElementPtr)
                if (GlobalVariable *annoteStr =
                        dyn_cast<GlobalVariable>(note->getOperand(0)))
                  if (ConstantDataSequential *data =
                          dyn_cast<ConstantDataSequential>(
                              annoteStr->getInitializer()))
                    if (data->isString())
                      annoteStr->setInitializer(ConstantDataArray::getString(
                          M->getContext(),
                          data->getAsString().str() + " " + annotation));
            }
          } else if (structAn->getOperand(0) == f) { // opaque pointer
            Constant *note = structAn->getOperand(1);
            if (GlobalVariable *annoteStr =
                    dyn_cast<GlobalVariable>(note->getOperand(0)))
              if (ConstantDataSequential *data =
                      dyn_cast<ConstantDataSequential>(
                          annoteStr->getInitializer()))
                if (data->isString())
                  annoteStr->setInitializer(ConstantDataArray::getString(
                      M->getContext(),
                      data->getAsString().str() + " " + annotation));
          }
        }
      if (!fHasAnnotation) {
        std::vector<Constant *> Annotations;
        for (unsigned int i = 0; i < ca->getNumOperands(); i++)
          Annotations.emplace_back(ca->getOperand(i));
        Annotations.emplace_back(createNewCSForAnnotationWithAppendedStr(
            f, Annotations, annotation));
        Constant *newCA = ConstantArray::get(
            ArrayType::get(Annotations[0]->getType(), Annotations.size()),
            Annotations);
        glob->setInitializer(newCA);
      }
    }
  } else {
    Type *Int32Ty = Type::getInt32Ty(M->getContext());
    Type *Int8PtrTy = Type::getInt8PtrTy(M->getContext());
    StructType *ST = StructType::get(
        M->getContext(), {Int8PtrTy, Int8PtrTy, Int8PtrTy, Int32Ty, Int8PtrTy});
    ArrayType *AT = ArrayType::get(ST, 1);
    std::vector<Constant *> Annotations = {};
    ConstantArray *CA = cast<ConstantArray>(ConstantArray::get(
        AT,
        {createNewCSForAnnotationWithAppendedStr(f, Annotations, annotation)}));
    GlobalVariable *newGV = new GlobalVariable(*M, CA->getType(), false,
                                               GlobalValue::AppendingLinkage,
                                               CA, "llvm.global.annotations");
    newGV->setSection("llvm.metadata");
  }
}

// Unlike O-LLVM which uses __attribute__ that is not supported by the ObjC
// CFE. We use a dummy call here and remove the call later Very dumb and
// definitely slower than the function attribute method Merely a hack
bool readFlag(Function *f, std::string attribute) {
  for (Instruction &I : instructions(f)) {
    Instruction *Inst = &I;
    if (CallInst *CI = dyn_cast<CallInst>(Inst)) {
      if (CI->getCalledFunction() != nullptr &&
          CI->getCalledFunction()->getName().contains("hikari_" + attribute)) {
        CI->eraseFromParent();
        return true;
      }
    }
  }
  return false;
}
bool toObfuscate(bool flag, Function *f, std::string attribute) {
  // Check if declaration and external linkage
  if (f->isDeclaration() || f->hasAvailableExternallyLinkage()) {
    return false;
  }
  std::string attr = attribute;
  std::string attrNo = "no" + attr;
  // We have to check the nofla flag first
  // Because .find("fla") is true for a string like "fla" or
  // "nofla"
  if (readAnnotate(f).find(attrNo) != std::string::npos ||
      readFlag(f, attrNo)) {
    return false;
  }
  if (readAnnotate(f).find(attr) != std::string::npos || readFlag(f, attr)) {
    return true;
  }
  return flag;
}
