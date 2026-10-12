import Lax455465Proofs.RamLpScope

namespace Lax455465Proofs.RamLpNoWrite
open Lax808846Proofs.Imp

theorem instruction (i : Lax808846.Ram.Instr) : (RamVirtualProgram.instruction i).NoWrite := by
  cases i <;> dsimp [RamVirtualProgram.instruction,RamVirtualProgram.writeBack,RamVirtualProgram.increment,
    RamVirtualProgram.operands,RamVirtualProgram.binary,RamVirtualProgram.stop,RamSparseRead.read,RamSparseRead.write,
    RamSparseMemory.lookup,RamSparseMemory.scanStep,RamSparseMemory.put,RamWordOps.binary,RamWordOps.reduce,
    RamWordOps.shift,RamWordOps.complement,Com.NoWrite] <;> decide

theorem dispatch (p : List Lax808846.Ram.Instr) (offset : ℕ) : (RamVirtualProgram.dispatch p offset).NoWrite := by
  induction p generalizing offset with
  | nil => trivial
  | cons i p ih => exact ⟨instruction i,ih (offset+1)⟩

theorem execute (p : Lax808846.Ram.Program) : (RamVirtualProgram.execute p).NoWrite := by
  exact ⟨by decide,by decide,dispatch p 0⟩

theorem polynomial (coefficients : List ℕ) : (RamPolynomial.command coefficients).NoWrite := by
  induction coefficients with
  | nil => trivial
  | cons a rest ih => exact ⟨ih,by trivial⟩

theorem prepare (coefficients : List ℕ) : (RamLpPrepare.command coefficients).NoWrite := by
  simpa [RamLpPrepare.command,RamBitSize.array,RamBitSize.arrayStep,RamBitSize.word,RamBitSize.wordLoop,
    RamBitSize.wordStep,RamLpInputFrame.command,RamLpInputFrame.step,RamWordBuffer.append,Com.NoWrite] using polynomial coefficients

/-- The LP program writes to its private virtual output buffer, leaving
the physical LR certificate tape untouched. -/
theorem solver (p : Lax808846.Ram.Program) (coefficients : List ℕ) :
    (RamFlowLpSolver.command p coefficients).NoWrite := by
  exact ⟨by decide,prepare coefficients,execute p⟩

end Lax455465Proofs.RamLpNoWrite
