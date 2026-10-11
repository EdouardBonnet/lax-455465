import Lax455465Proofs.RamFlowLpSolver

namespace Lax455465Proofs.RamLpScope

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def protectedVars : List String :=
  ["lp.n","lp.n2","lp.n3","lp.rows","lp.columns","lp.matrixLength","flow.kind","input.length"]
def arrays : List String := ["input.data","flow.weights","flow.capacities"]

theorem instruction_vars (i : Lax808846.Ram.Instr) (x : String) (hx : x ∈ protectedVars) :
    x ∉ (RamVirtualProgram.instruction i).wvars := by
  simp only [protectedVars,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases i <;> dsimp [RamVirtualProgram.instruction,RamVirtualProgram.writeBack,RamVirtualProgram.increment,
    RamVirtualProgram.operands,RamVirtualProgram.binary,RamVirtualProgram.stop,RamSparseRead.read,RamSparseRead.write,
    RamSparseMemory.lookup,RamSparseMemory.scanStep,RamSparseMemory.put,RamWordOps.binary,RamWordOps.reduce,
    RamWordOps.shift,RamWordOps.complement,Com.wvars,Com.warrs] <;> decide

theorem instruction_arrays (i : Lax808846.Ram.Instr) (a : String) (ha : a ∈ arrays) :
    a ∉ (RamVirtualProgram.instruction i).warrs := by
  simp only [arrays,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl <;> cases i <;> dsimp [RamVirtualProgram.instruction,RamVirtualProgram.writeBack,RamVirtualProgram.increment,
    RamVirtualProgram.operands,RamVirtualProgram.binary,RamVirtualProgram.stop,RamSparseRead.read,RamSparseRead.write,
    RamSparseMemory.lookup,RamSparseMemory.scanStep,RamSparseMemory.put,RamWordOps.binary,RamWordOps.reduce,
    RamWordOps.shift,RamWordOps.complement,Com.wvars,Com.warrs] <;> decide

theorem dispatch_vars (p : List Lax808846.Ram.Instr) (offset : ℕ) (x : String) (hx : x ∈ protectedVars) :
    x ∉ (RamVirtualProgram.dispatch p offset).wvars := by
  induction p generalizing offset with
  | nil =>
    simp only [protectedVars,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      dsimp [RamVirtualProgram.dispatch,RamVirtualProgram.stop,Com.wvars] <;> decide
  | cons i p ih =>
    simp only [RamVirtualProgram.dispatch,Com.wvars,List.mem_append,not_or]
    exact ⟨instruction_vars i x hx,ih (offset+1)⟩

theorem dispatch_arrays (p : List Lax808846.Ram.Instr) (offset : ℕ) (a : String) (ha : a ∈ arrays) :
    a ∉ (RamVirtualProgram.dispatch p offset).warrs := by
  induction p generalizing offset with
  | nil => simp [RamVirtualProgram.dispatch,RamVirtualProgram.stop,Com.warrs]
  | cons i p ih =>
    simp only [RamVirtualProgram.dispatch,Com.warrs,List.mem_append,not_or]
    exact ⟨instruction_arrays i a ha,ih (offset+1)⟩

theorem execute_vars (p : Lax808846.Ram.Program) (x : String) (hx : x ∈ protectedVars) :
    x ∉ (RamVirtualProgram.execute p).wvars := by
  have hdispatch := dispatch_vars p 0 x hx
  simp only [protectedVars,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simpa [RamVirtualProgram.execute,RamVirtualProgram.initCommand,RamWordOps.modulus,Com.wvars] using hdispatch

theorem execute_arrays (p : Lax808846.Ram.Program) (a : String) (ha : a ∈ arrays) :
    a ∉ (RamVirtualProgram.execute p).warrs := by
  simpa [RamVirtualProgram.execute,RamVirtualProgram.initCommand,RamWordOps.modulus,Com.warrs]
    using dispatch_arrays p 0 a ha

theorem prepare_vars (coefficients : List ℕ) (x : String) (hx : x ∈ protectedVars) :
    x ∉ (RamLpPrepare.command coefficients).wvars := by
  have hxp : x ≠ "poly.value" := by
    simp only [protectedVars,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hp := RamPolynomial.variable_frame coefficients x hxp
  simp only [protectedVars,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simpa [RamLpPrepare.command,RamBitSize.array,RamBitSize.arrayStep,RamBitSize.word,RamBitSize.wordLoop,
      RamBitSize.wordStep,RamLpInputFrame.command,RamLpInputFrame.step,RamWordBuffer.append,Com.wvars] using hp

theorem prepare_arrays (coefficients : List ℕ) (a : String) (ha : a ∈ arrays) :
    a ∉ (RamLpPrepare.command coefficients).warrs := by
  have hp := RamPolynomial.arrays_frame coefficients
  simp only [arrays,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl <;>
    simp [RamLpPrepare.command,RamBitSize.array,RamBitSize.arrayStep,RamBitSize.word,RamBitSize.wordLoop,
      RamBitSize.wordStep,RamLpInputFrame.command,RamLpInputFrame.step,RamWordBuffer.append,Com.warrs,hp]

/-- The black-box solver cannot overwrite the source graph or its model
and dimension registers; it executes inside its proved private buffers. -/
theorem invocation_vars (p : Lax808846.Ram.Program) (coefficients : List ℕ) (x : String) (hx : x ∈ protectedVars) :
    x ∉ (RegisteredLpInvocation.command p coefficients).wvars := by
  simpa only [RegisteredLpInvocation.command,Com.wvars,List.mem_append,not_or] using
    And.intro (prepare_vars coefficients x hx) (execute_vars p x hx)

theorem invocation_arrays (p : Lax808846.Ram.Program) (coefficients : List ℕ) (a : String) (ha : a ∈ arrays) :
    a ∉ (RegisteredLpInvocation.command p coefficients).warrs := by
  simpa only [RegisteredLpInvocation.command,Com.warrs,List.mem_append,not_or] using
    And.intro (prepare_arrays coefficients a ha) (execute_arrays p a ha)

theorem build_vars (x : String) (hx : x ∈ protectedVars) :
    x ∉ RamFlowLp.command.wvars := by
  simp only [protectedVars,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem build_arrays (a : String) (ha : a ∈ arrays) :
    a ∉ RamFlowLp.command.warrs := by
  simp only [arrays,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl <;> decide

theorem solver_vars (p : Lax808846.Ram.Program) (coefficients : List ℕ)
    (x : String) (hx : x ∈ protectedVars) :
    x ∉ (RamFlowLpSolver.command p coefficients).wvars := by
  simpa only [RamFlowLpSolver.command,Com.wvars,List.mem_append,not_or] using
    And.intro (build_vars x hx) (invocation_vars p coefficients x hx)

theorem solver_arrays (p : Lax808846.Ram.Program) (coefficients : List ℕ)
    (a : String) (ha : a ∈ arrays) :
    a ∉ (RamFlowLpSolver.command p coefficients).warrs := by
  simpa only [RamFlowLpSolver.command,Com.warrs,List.mem_append,not_or] using
    And.intro (build_arrays a ha) (invocation_arrays p coefficients a ha)

/-- Source data survive the entire native LP construction and invocation. -/
theorem solver_data {B K : ℕ} {p : Lax808846.Ram.Program} {coefficients : List ℕ}
    {σ τ : Env} (hr : Run B (RamFlowLpSolver.command p coefficients) σ τ K)
    {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n) (h : RamFlowData.Data I σ) :
    RamFlowData.Data I τ := by
  apply RamFlowData.frame hr I h
  · intro a ha
    apply solver_arrays p coefficients a
    simp only [arrays] 
    simp_all
  · intro x hx
    apply solver_vars p coefficients x
    simp only [protectedVars]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    rcases hx with h | h | h | h | h | h <;> simp [h]

end Lax455465Proofs.RamLpScope

