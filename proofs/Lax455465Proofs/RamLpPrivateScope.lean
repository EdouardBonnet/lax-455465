import Lax455465Proofs.RamLpScope

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Lax455465Proofs.RamLpPrivateScope
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- Representatives of all instruction constructors. Operand numbers affect
expressions, but never the names of host variables or arrays written. -/
def representatives : List Lax808846.Ram.Instr :=
  [.set 0 0,.load 0 0,.store 0 0,.add 0 0 0,.sub 0 0 0,.mul 0 0 0,
   .div 0 0 0,.and 0 0 0,.shiftl 0 0 0,.not 0 0,.jump 0,.jzero 0 0,
   .jeof 0,.inputLength 0,.inputLoad 0 0,.halt,.read 0,.write 0]

def instructionVars : List String := representatives.flatMap fun i =>
  (RamVirtualProgram.instruction i).wvars

def instructionArrays : List String := representatives.flatMap fun i =>
  (RamVirtualProgram.instruction i).warrs

/-- A finite, program-independent footprint of the virtual LP solver. -/
def vars : List String := instructionVars ++
  RamWordOps.modulus.wvars ++ RamVirtualProgram.initCommand.wvars ++
  (RamLpPrepare.command []).wvars

def arrays : List String := instructionArrays ++
  RamWordOps.modulus.warrs ++ RamVirtualProgram.initCommand.warrs ++
  (RamLpPrepare.command []).warrs

theorem instruction_vars (i : Lax808846.Ram.Instr) (x : String)
    (hx : x ∉ instructionVars) : x ∉ (RamVirtualProgram.instruction i).wvars := by
  cases i <;> simp_all [instructionVars,representatives,RamVirtualProgram.instruction,
    RamVirtualProgram.writeBack,RamVirtualProgram.increment,RamVirtualProgram.operands,
    RamVirtualProgram.binary,RamVirtualProgram.stop,RamSparseRead.read,RamSparseRead.write,
    RamSparseMemory.lookup,RamSparseMemory.scanStep,RamSparseMemory.put,
    RamWordOps.binary,RamWordOps.reduce,RamWordOps.shift,RamWordOps.complement,
    Com.wvars,Com.warrs]

theorem instruction_arrays (i : Lax808846.Ram.Instr) (a : String)
    (ha : a ∉ instructionArrays) : a ∉ (RamVirtualProgram.instruction i).warrs := by
  cases i <;> simp_all [instructionArrays,representatives,RamVirtualProgram.instruction,
    RamVirtualProgram.writeBack,RamVirtualProgram.increment,RamVirtualProgram.operands,
    RamVirtualProgram.binary,RamVirtualProgram.stop,RamSparseRead.read,RamSparseRead.write,
    RamSparseMemory.lookup,RamSparseMemory.scanStep,RamSparseMemory.put,
    RamWordOps.binary,RamWordOps.reduce,RamWordOps.shift,RamWordOps.complement,
    Com.wvars,Com.warrs]

theorem dispatch_vars (p : List Lax808846.Ram.Instr) (offset : ℕ) (x : String)
    (hx : x ∉ instructionVars) : x ∉ (RamVirtualProgram.dispatch p offset).wvars := by
  induction p generalizing offset with
  | nil => exact instruction_vars .halt x hx
  | cons i p ih =>
    simp only [RamVirtualProgram.dispatch,Com.wvars,List.mem_append,not_or]
    exact ⟨instruction_vars i x hx,ih (offset+1)⟩

theorem dispatch_arrays (p : List Lax808846.Ram.Instr) (offset : ℕ) (a : String)
    (ha : a ∉ instructionArrays) : a ∉ (RamVirtualProgram.dispatch p offset).warrs := by
  induction p generalizing offset with
  | nil => exact instruction_arrays .halt a ha
  | cons i p ih =>
    simp only [RamVirtualProgram.dispatch,Com.warrs,List.mem_append,not_or]
    exact ⟨instruction_arrays i a ha,ih (offset+1)⟩

theorem prepare_vars (coefficients : List ℕ) (x : String)
    (hx : x ∉ (RamLpPrepare.command []).wvars) :
    x ∉ (RamLpPrepare.command coefficients).wvars := by
  have hxp : x ≠ "poly.value" := by
    intro he
    subst x
    exact hx (by decide)
  have hp := RamPolynomial.variable_frame coefficients x hxp
  simpa [RamLpPrepare.command,RamBitSize.array,RamBitSize.arrayStep,RamBitSize.word,
    RamBitSize.wordLoop,RamBitSize.wordStep,RamLpInputFrame.command,
    RamLpInputFrame.step,RamWordBuffer.append,Com.wvars,RamPolynomial.command,hp,hxp] using hx

theorem prepare_arrays (coefficients : List ℕ) (a : String)
    (ha : a ∉ (RamLpPrepare.command []).warrs) :
    a ∉ (RamLpPrepare.command coefficients).warrs := by
  simpa [RamLpPrepare.command,RamBitSize.array,RamBitSize.arrayStep,RamBitSize.word,
    RamBitSize.wordLoop,RamBitSize.wordStep,RamLpInputFrame.command,
    RamLpInputFrame.step,RamWordBuffer.append,Com.warrs,RamPolynomial.arrays_frame] using ha

theorem invocation_vars (p : Lax808846.Ram.Program) (coefficients : List ℕ)
    (x : String) (hx : x ∉ vars) :
    x ∉ (RegisteredLpInvocation.command p coefficients).wvars := by
  simp only [vars,List.mem_append,not_or] at hx
  simpa only [RegisteredLpInvocation.command,RamVirtualProgram.execute,Com.wvars,
    List.mem_append,not_or] using
      And.intro (prepare_vars coefficients x hx.2) ⟨hx.1.1.2,hx.1.2,dispatch_vars p 0 x hx.1.1.1⟩

theorem invocation_arrays (p : Lax808846.Ram.Program) (coefficients : List ℕ)
    (a : String) (ha : a ∉ arrays) :
    a ∉ (RegisteredLpInvocation.command p coefficients).warrs := by
  simp only [arrays,List.mem_append,not_or] at ha
  simpa only [RegisteredLpInvocation.command,RamVirtualProgram.execute,Com.warrs,
    List.mem_append,not_or] using
      And.intro (prepare_arrays coefficients a ha.2) ⟨ha.1.1.2,ha.1.2,dispatch_arrays p 0 a ha.1.1.1⟩

end Lax455465Proofs.RamLpPrivateScope
