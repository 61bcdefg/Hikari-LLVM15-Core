// For open-source license, please refer to
// [License](https://github.com/HikariObfuscator/Hikari/wiki/License).
//===----------------------------------------------------------------------===//
#include "llvm/Transforms/Obfuscation/IndirectBranch.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/NoFolder.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Obfuscation/CryptoUtils.h"
#include "llvm/Transforms/Obfuscation/SubstituteImpl.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/Transforms/Obfuscation/compat/LegacyLowerSwitch.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

using namespace llvm;

static cl::opt<bool>
    UseStack("indibran-use-stack", cl::init(false), cl::NotHidden,
             cl::desc("[IndirectBranch]Stack-based indirect jumps"));
static cl::opt<bool>
    EncryptJumpTarget("indibran-enc-jump-target", cl::init(false),
                      cl::NotHidden,
                      cl::desc("[IndirectBranch]Encrypt jump target"));

namespace llvm {
struct IndirectBranch : public FunctionPass {
  static char ID;
  bool flag;
  bool initialized;
  Function *valwrapfunc;
  std::map<BasicBlock *, unsigned long long> indexmap;
  std::map<Function *, ConstantInt *> encmap;
  IndirectBranch() : FunctionPass(ID) {
    this->flag = true;
    this->initialized = false;
  }
  IndirectBranch(bool flag) : FunctionPass(ID) {
    this->flag = flag;
    this->initialized = false;
  }
  StringRef getPassName() const override { return "IndirectBranch"; }
  bool initialize(Module &M) {
    std::vector<Constant *> BBs;
    unsigned long long i = 0;
    for (Function &F : M) {
      if (!toObfuscate(flag, &F, "indibr"))
        continue;
      if (UseStack)
        turnOffOptimization(&F);
      // See https://github.com/NeHyci/Hikari-LLVM15/issues/32
      createLegacyLowerSwitchPass()->runOnFunction(F);
      if (EncryptJumpTarget)
        encmap[&F] = ConstantInt::get(
            Type::getInt32Ty(M.getContext()),
            cryptoutils->get_range(UINT8_MAX, UINT16_MAX * 2) * 4);
      for (BasicBlock &BB : F)
        if (!BB.isEntryBlock()) {
          indexmap[&BB] = i++;
          BBs.emplace_back(EncryptJumpTarget
                               ? ConstantExpr::getGetElementPtr(
                                     Type::getInt8Ty(M.getContext()),
                                     ConstantExpr::getBitCast(
                                         BlockAddress::get(&BB),
                                         Type::getInt8PtrTy(M.getContext())),
                                     encmap[&F])
                               : BlockAddress::get(&BB));
        }
    }
    ArrayType *AT =
        ArrayType::get(Type::getInt8PtrTy(M.getContext()), BBs.size());
    Constant *BlockAddressArray =
        ConstantArray::get(AT, ArrayRef<Constant *>(BBs));
    GlobalVariable *Table = new GlobalVariable(
        M, AT, false, GlobalValue::LinkageTypes::PrivateLinkage,
        BlockAddressArray, "IndirectBranchingGlobalTable");
    appendToCompilerUsed(M, {Table});
    // valwrap - make what IDA Pro displays in the pseudocode window even
    // weirder.
    // In IDA Pro 7.7.220118
    // Original
    /* void __cdecl -[ViewController viewDidLoad](ViewController *self, SEL a2)
     * {
     * return off_10000D0D0();
     * }
     */
    // New
    /* void __cdecl -[ViewController viewDidLoad](ViewController *self, SEL a2)
     * {
     * __int64 v2; // kr00_8
     * v2 = nullsub_1(off_10000D0D0);
     * __asm { BR              X0 }
     * }
     */
    Function *valwrap = Function::Create(
        FunctionType::get(Type::getInt8PtrTy(M.getContext()),
                          {Type::getInt8PtrTy(M.getContext())}, false),
        GlobalValue::LinkageTypes::PrivateLinkage,
        "HikariIndirectBranchTargetWrapper", M);
    BasicBlock *BB = BasicBlock::Create(valwrap->getContext(), "", valwrap);
    ReturnInst::Create(valwrap->getContext(), valwrap->getArg(0), BB);
    appendToCompilerUsed(M, {valwrap});
    this->valwrapfunc = valwrap;
    this->initialized = true;
    return true;
  }
  bool runOnFunction(Function &Func) override {
    if (!toObfuscate(flag, &Func, "indibr"))
      return false;
    Module *M = Func.getParent();
    if (!this->initialized)
      initialize(*M);
    errs() << "Running IndirectBranch On " << Func.getName() << "\n";
    std::vector<BranchInst *> BIs;
    for (Instruction &Inst : instructions(Func))
      if (BranchInst *BI = dyn_cast<BranchInst>(&Inst))
        BIs.emplace_back(BI);

    Type *Int8Ty = Type::getInt8Ty(M->getContext());
    Type *Int32Ty = Type::getInt32Ty(M->getContext());
    Type *Int8PtrTy = Type::getInt8PtrTy(M->getContext());

    Value *zero = ConstantInt::get(Int32Ty, 0);

    IRBuilder<NoFolder> *IRBEntry = new IRBuilder<NoFolder>(Func.getEntryBlock().getTerminator());
    for (BranchInst *BI : BIs) {
      if (UseStack &&
          IRBEntry->GetInsertPoint() !=
              (BasicBlock::iterator)Func.getEntryBlock().getTerminator())
        IRBEntry->SetInsertPoint(Func.getEntryBlock().getTerminator());
      IRBuilder<NoFolder> *IRBBI = new IRBuilder<NoFolder>(BI);
      std::vector<BasicBlock *> BBs;
      // We use the condition's evaluation result to generate the GEP
      // instruction  False evaluates to 0 while true evaluates to 1.  So here
      // we insert the false block first
      if (BI->isConditional() && !BI->getSuccessor(1)->isEntryBlock())
        BBs.emplace_back(BI->getSuccessor(1));
      if (!BI->getSuccessor(0)->isEntryBlock())
        BBs.emplace_back(BI->getSuccessor(0));

      GlobalVariable *LoadFrom = nullptr;
      if (BI->isConditional() ||
          indexmap.find(BI->getSuccessor(0)) == indexmap.end()) {
        ArrayType *AT = ArrayType::get(Int8PtrTy, BBs.size());
        std::vector<Constant *> BlockAddresses;
        for (BasicBlock *BB : BBs)
          BlockAddresses.emplace_back(
              EncryptJumpTarget ? ConstantExpr::getGetElementPtr(
                                      Int8Ty,
                                      ConstantExpr::getBitCast(
                                          BlockAddress::get(BB), Int8PtrTy),
                                      encmap[&Func])
                                : BlockAddress::get(BB));
        // Create a new GV
        Constant *BlockAddressArray =
            ConstantArray::get(AT, ArrayRef<Constant *>(BlockAddresses));
        LoadFrom = new GlobalVariable(
            *M, AT, false, GlobalValue::LinkageTypes::PrivateLinkage,
            BlockAddressArray, "HikariConditionalLocalIndirectBranchingTable");
        appendToCompilerUsed(*Func.getParent(), {LoadFrom});
      } else {
        LoadFrom = M->getGlobalVariable("IndirectBranchingGlobalTable", true);
      }
      Value *index, *RealIndex = nullptr;
      if (BI->isConditional()) {
        Value *condition = BI->getCondition();
        index = (UseStack ? IRBEntry : IRBBI)->CreateZExt(condition, Int32Ty);
        RealIndex = index;
      } else {
        Value *indexval = nullptr;
        ConstantInt *IndexEncKey =
            EncryptJumpTarget ? cast<ConstantInt>(ConstantInt::get(
                                    Int32Ty, cryptoutils->get_uint32_t()))
                              : nullptr;
        if (EncryptJumpTarget) {
          GlobalVariable *indexgv = new GlobalVariable(
              *M, Int32Ty, false, GlobalValue::LinkageTypes::PrivateLinkage,
              ConstantInt::get(Int32Ty, IndexEncKey->getValue() ^
                                            indexmap[BI->getSuccessor(0)]),
              "IndirectBranchingIndex");
          appendToCompilerUsed(*M, {indexgv});
          indexval = (UseStack ? IRBEntry : IRBBI)->CreateLoad(indexgv->getValueType(), indexgv);
        } else {
          indexval = ConstantInt::get(Int32Ty, indexmap[BI->getSuccessor(0)]);
        }
        if (UseStack) {
          AllocaInst *AI =
              IRBEntry->CreateAlloca(indexval->getType());
          IRBEntry->CreateStore(indexval, AI);
          index = IRBEntry->CreateLoad(AI->getAllocatedType(), AI);
        } else {
          index = indexval;
        }
        RealIndex =
            EncryptJumpTarget ? (UseStack ? IRBEntry : IRBBI)->CreateXor(index, IndexEncKey) : index;
      }
      Value *LI, *enckeyLoad, *gepptr = nullptr;
      if (UseStack) {
        Value *GEP = IRBEntry->CreateGEP(LoadFrom->getValueType(), LoadFrom,
                                         {zero, RealIndex});
        AllocaInst *AI = IRBEntry->CreateAlloca(GEP->getType());
        IRBEntry->CreateStore(GEP, AI);
        if (!EncryptJumpTarget)
          LI = IRBBI->CreateLoad(
              Int8PtrTy, IRBEntry->CreateLoad(AI->getAllocatedType(), AI),
              "IndirectBranchingTargetAddress");
        else
          gepptr = IRBBI->CreateLoad(
              Int8PtrTy, IRBBI->CreateLoad(AI->getAllocatedType(), AI));
      } else {
        Value *GEP = IRBBI->CreateGEP(LoadFrom->getValueType(), LoadFrom,
                                     {zero, RealIndex});
        if (!EncryptJumpTarget)
          LI = IRBBI->CreateLoad(Int8PtrTy, GEP,
                                "IndirectBranchingTargetAddress");
        else
          gepptr = IRBBI->CreateLoad(Int8PtrTy, GEP);
      }
      if (EncryptJumpTarget) {
        ConstantInt *encenckey = cast<ConstantInt>(
            ConstantInt::get(Int32Ty, cryptoutils->get_uint32_t()));
        GlobalVariable *enckeyGV = new GlobalVariable(
            *M, Int32Ty, false, GlobalValue::LinkageTypes::PrivateLinkage,
            ConstantInt::get(Int32Ty,
                             encenckey->getValue() ^ encmap[&Func]->getValue()),
            "IndirectBranchingAddressEncryptKey");
        appendToCompilerUsed(*M, enckeyGV);
        enckeyLoad = IRBBI->CreateXor(
            IRBBI->CreateLoad(enckeyGV->getValueType(), enckeyGV), encenckey);
        LI = IRBBI->CreateGEP(Int8Ty, gepptr, IRBBI->CreateSub(zero, enckeyLoad),
                             "IndirectBranchingTargetAddress");
        SubstituteImpl::substituteXor(dyn_cast<BinaryOperator>(enckeyLoad));
      }
      IndirectBrInst *indirBr = IndirectBrInst::Create(
          CallInst::Create(valwrapfunc, {LI}, "", BI), BBs.size());
      for (BasicBlock *BB : BBs)
        indirBr->addDestination(BB);
      ReplaceInstWithInst(BI, indirBr);
    }
    return true;
  }
};
} // namespace llvm

FunctionPass *llvm::createIndirectBranchPass(bool flag) {
  return new IndirectBranch(flag);
}
char IndirectBranch::ID = 0;
INITIALIZE_PASS(IndirectBranch, "indibran", "IndirectBranching", true, true)
