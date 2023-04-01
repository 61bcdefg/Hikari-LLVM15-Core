// For open-source license, please refer to
// [License](https://github.com/HikariObfuscator/Hikari/wiki/License).
//===----------------------------------------------------------------------===//
#include "llvm/Transforms/Obfuscation/Flattening.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Obfuscation/CryptoUtils.h"
#include "llvm/Transforms/Obfuscation/Utils.h"

using namespace llvm;

namespace {
struct Flattening : public FunctionPass {
  static char ID; // Pass identification, replacement for typeid
  bool flag;
  Flattening() : FunctionPass(ID) { this->flag = true; }
  Flattening(bool flag) : FunctionPass(ID) { this->flag = flag; }
  bool runOnFunction(Function &F) override;
  void flatten(Function *f);
};
} // namespace

char Flattening::ID = 0;
FunctionPass *llvm::createFlatteningPass(bool flag) {
  return new Flattening(flag);
}
INITIALIZE_PASS(Flattening, "cffobf", "Enable Control Flow Flattening.", false,
                false)
bool Flattening::runOnFunction(Function &F) {
  Function *tmp = &F;
  // Do we obfuscate
  if (toObfuscate(flag, tmp, "fla") && !F.isPresplitCoroutine()) {
    errs() << "Running ControlFlowFlattening On " << F.getName() << "\n";
    flatten(tmp);
  }

  return true;
}

void Flattening::flatten(Function *f) {
  std::vector<BasicBlock *> origBB, exceptPredBB, exceptSuccBB;
  BasicBlock *loopEntry, *loopEnd;
  LoadInst *load, *loadAddr;
  SwitchInst *switchI;
  AllocaInst *switchVar, *switchVarAddr;
  const DataLayout &DL = f->getParent()->getDataLayout();

  // SCRAMBLER
  std::map<uint32_t, uint32_t> scrambling_key;
  // END OF SCRAMBLER

  for (BasicBlock &BB : *f) {
    if (isa<BranchInst>(BB.getTerminator()) ||
        isa<ReturnInst>(BB.getTerminator()))
      origBB.emplace_back(&BB);
    else
      for (BasicBlock *B : successors(&BB))
        exceptSuccBB.emplace_back(B);
  }
  for (BasicBlock *BB : origBB)
    for (BasicBlock *B : successors(BB)) {
      if (std::find(origBB.begin(), origBB.end(), B) == origBB.end())
        exceptPredBB.emplace_back(BB);
      if (std::find(exceptSuccBB.begin(), exceptSuccBB.end(), B) !=
          exceptSuccBB.end())
        exceptSuccBB.erase(
            std::find(exceptSuccBB.begin(), exceptSuccBB.end(), B));
    }

  // Nothing to flatten
  if (origBB.size() <= 1)
    return;

  Function::iterator iter = f->begin();
  BasicBlock *insert = &*f->begin();

  while (!isa<BranchInst>(insert->getTerminator()) ||
         std::find(exceptPredBB.begin(), exceptPredBB.end(), insert) !=
             exceptPredBB.end()) {
    iter++;
    insert = &*iter;
    if (insert == &f->back())
      return;
  }

  origBB.erase(std::find(origBB.begin(), origBB.end(), insert));

  BasicBlock::iterator i = insert->end();
  --i;
  if (insert->size() > 1)
    --i;
  BasicBlock *tmpBB = insert->splitBasicBlock(i, "first");
  bool tmpBBIsExceptPred = false;
  for (BasicBlock *B : successors(tmpBB))
    if (!(isa<BranchInst>(B->getTerminator()) ||
          isa<ReturnInst>(B->getTerminator()))) {
      tmpBBIsExceptPred = true;
      break;
    }
  origBB.insert(origBB.begin(), tmpBB);
  if (tmpBBIsExceptPred)
    exceptPredBB.emplace_back(tmpBB);

  BasicBlock::iterator I = f->getEntryBlock().begin();
  while (isa<AllocaInst>(I))
    ++I;
  Instruction *AllocaInsertionPoint = &*I;

  // Create switch variable and set as it
  switchVar =
      new AllocaInst(Type::getInt32Ty(f->getContext()), DL.getAllocaAddrSpace(),
                     "switchVar", AllocaInsertionPoint);
  switchVarAddr =
      new AllocaInst(Type::getInt32PtrTy(f->getContext()),
                     DL.getAllocaAddrSpace(), "", AllocaInsertionPoint);

  // Remove jump
  insert->getTerminator()->eraseFromParent();

  new StoreInst(ConstantInt::get(Type::getInt32Ty(f->getContext()),
                                 cryptoutils->scramble32(0, scrambling_key)),
                switchVar, &f->getEntryBlock().back());
  new StoreInst(switchVar, switchVarAddr, &f->getEntryBlock().back());

  // Create main loop
  loopEntry = BasicBlock::Create(f->getContext(), "loopEntry", f, insert);
  loopEnd = BasicBlock::Create(f->getContext(), "loopEnd", f, insert);

  load = new LoadInst(switchVar->getAllocatedType(), switchVar, "switchVar",
                      loopEntry);

  // Move first BB on top
  insert->moveBefore(loopEntry);
  BranchInst::Create(loopEntry, insert);

  loadAddr = new LoadInst(switchVarAddr->getAllocatedType(), switchVarAddr,
                          "switchVarAddr", &f->getEntryBlock().back());

  // loopEnd jump to loopEntry
  BranchInst::Create(loopEntry, loopEnd);

  BasicBlock *swDefault =
      BasicBlock::Create(f->getContext(), "switchDefault", f, loopEnd);
  BranchInst::Create(loopEnd, swDefault);

  // Create switch instruction itself and set condition
  switchI = SwitchInst::Create(load, swDefault, 0, loopEntry);

  // Put BB in the switch
  for (BasicBlock *i : origBB) {
    if (std::find(exceptSuccBB.begin(), exceptSuccBB.end(), i) !=
        exceptSuccBB.end())
      continue;

    ConstantInt *numCase = nullptr;

    // Move the BB inside the switch (only visual, no code logic)
    i->moveBefore(loopEnd);

    // Add case to switch
    numCase = cast<ConstantInt>(ConstantInt::get(
        switchI->getCondition()->getType(),
        cryptoutils->scramble32(switchI->getNumCases(), scrambling_key)));
    switchI->addCase(numCase, i);
  }

  // Recalculate switchVar
  for (BasicBlock *i : origBB) {
    if (std::find(exceptPredBB.begin(), exceptPredBB.end(), i) !=
        exceptPredBB.end())
      continue;

    ConstantInt *numCase = nullptr;

    // If it's a non-conditional jump
    if (i->getTerminator()->getNumSuccessors() == 1) {
      // Get successor and delete terminator
      BasicBlock *succ = i->getTerminator()->getSuccessor(0);
      i->getTerminator()->eraseFromParent();

      // Get next case
      numCase = switchI->findCaseDest(succ);

      // If next case == default case (switchDefault)
      if (!numCase) {
        numCase = cast<ConstantInt>(
            ConstantInt::get(switchI->getCondition()->getType(),
                             cryptoutils->scramble32(switchI->getNumCases() - 1,
                                                     scrambling_key)));
      }

      // Update switchVar and jump to the end of loop
      new StoreInst(numCase, loadAddr, i);
      BranchInst::Create(loopEnd, i);
      continue;
    }

    // If it's a conditional jump
    if (i->getTerminator()->getNumSuccessors() == 2) {
      // Get next cases
      ConstantInt *numCaseTrue =
          switchI->findCaseDest(i->getTerminator()->getSuccessor(0));
      ConstantInt *numCaseFalse =
          switchI->findCaseDest(i->getTerminator()->getSuccessor(1));

      // Check if next case == default case (switchDefault)
      if (!numCaseTrue) {
        numCaseTrue = cast<ConstantInt>(
            ConstantInt::get(switchI->getCondition()->getType(),
                             cryptoutils->scramble32(switchI->getNumCases() - 1,
                                                     scrambling_key)));
      }

      if (!numCaseFalse) {
        numCaseFalse = cast<ConstantInt>(
            ConstantInt::get(switchI->getCondition()->getType(),
                             cryptoutils->scramble32(switchI->getNumCases() - 1,
                                                     scrambling_key)));
      }

      // Create a SelectInst
      BranchInst *br = cast<BranchInst>(i->getTerminator());
      SelectInst *sel =
          SelectInst::Create(br->getCondition(), numCaseTrue, numCaseFalse, "",
                             i->getTerminator());

      // Erase terminator
      i->getTerminator()->eraseFromParent();
      // Update switchVar and jump to the end of loop
      new StoreInst(sel, loadAddr, i);
      BranchInst::Create(loopEnd, i);
      continue;
    }
  }
  errs() << "Fixing Stack\n";
  fixStack(f);
  errs() << "Fixed Stack\n";

  if (exceptPredBB.size() || exceptSuccBB.size())
    turnOffOptimization(f);
}
