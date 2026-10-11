import Lax455465Proofs.RamVirtualDispatch
import Lax455465Proofs.RamVirtualTraceBounds

namespace Lax455465Proofs.RamVirtualLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualProgram RamVirtualState RamVirtualInstruction

/-- The dispatch loop depends only on the running flag, rather than on a
proof-supplied instruction count. The count is used solely in its analysis. -/
def command (p : Lax808846.Ram.Program) : Com :=
  .while (.lt (.lit 0) (.var "vm.running")) (dispatch p 0)

private theorem running_test {B : ℕ} {σ : Env} {v : ℕ}
    (hB : 0 < B) (hv : v < B) (hflag : σ.vars "vm.running" = v) :
    (Cond.lt (.lit 0) (.var "vm.running")).evalB B σ = some (decide (0 < v)) := by
  apply evalB_condLt (evalB_lit hB)
  rw [evalB_var_iff]
  exact ⟨hflag.symm, hflag ▸ hv⟩

private theorem while_true {B K K' : ℕ} {p : Lax808846.Ram.Program} {σ ν τ : Env}
    (hcond : (Cond.lt (.lit 0) (.var "vm.running")).evalB B σ = some true)
    (hbody : Run B (dispatch p 0) σ ν K) (htail : Run B (command p) ν τ K') :
    Run B (command p) σ τ (4 + K + K') := by
  obtain ⟨k, hk, hb⟩ := hbody
  obtain ⟨k', hk', ht⟩ := htail
  exact ⟨4 + k + k', by omega, BigStepB.while_true hcond hb ht⟩

/-- A complete successful sparse trace followed by its real halt is
simulated by the native loop. Reserved buffers need only linear space,
and the proven instruction bound is quadratic in the source time. -/
theorem loop_spec (B w N k : ℕ) (p : Lax808846.Ram.Program) (s f : SparseRam.SparseState)
    (hB : 2 * (2 ^ w) ^ 2 + 3 < B) (hN : N + 1 < B)
    (hp : p.length < B) (hlit : ∀ i ∈ p, LiteralsFit B i)
    (hwords : SparseBounds.MemoryWords w s.memory)
    (hinput : s.input.length < B) (hinputWords : ∀ x ∈ s.input, x < B)
    (hm : s.memory.length + k ≤ N) (ho : s.out.length + k ≤ N)
    (hpcs : ∀ j ≤ k, ∀ t, SparseRam.run w p j s = some t → t.pc + 1 < B)
    (hr : SparseRam.run w p k s = some f) (hhalt : SparseRam.step w p f = none) :
    Spec B (fun σ => Represents w s σ ∧ σ.vars "vm.running" = 1 ∧
      N < (σ.arrs "vm.addresses").length ∧ N < (σ.arrs "vm.values").length ∧
      N < (σ.arrs "vm.output").length) (command p)
      (fun _ τ => Represents w f τ ∧ τ.vars "vm.running" = 0)
      ((k + 1) * (4 * p.length + 32 * N + 104) + 4) := by
  have h1 : 1 < B := by omega
  induction k generalizing s with
  | zero =>
    have heq : s = f := Option.some.inj hr
    subst s
    rintro σ ⟨hrep, hflag, hA, hV, hO⟩
    have hpc := hpcs 0 (by omega) f rfl
    obtain ⟨τ, hbody, hpost⟩ := RamVirtualDispatch.dispatch_spec B w f p 0 hB hlit
      (by simpa using hp) hwords hinput hinputWords hpc (by omega) (by omega) σ
      ⟨hrep, hflag, by omega, by omega, by omega⟩
    rw [RamVirtualDispatch.result_zero, hhalt] at hpost
    have htrue : (Cond.lt (.lit 0) (.var "vm.running")).evalB B σ = some true :=
      running_test (by omega) h1 hflag
    have hfalse : (Cond.lt (.lit 0) (.var "vm.running")).evalB B τ = some false :=
      running_test (by omega) (by omega) hpost.2
    exact ⟨τ, (while_true htrue hbody (Run.while_false hfalse)).mono
      (by simp only [Cond.size, Expr.size, Nat.zero_add, Nat.one_mul] ; omega), hpost⟩
  | succ k ih =>
    obtain ⟨u, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hr
    have hmu := SparseRam.step_memory_le w p s u hstep
    have hou := SparseBounds.step_output_le w p s u hstep
    have hwordsu := SparseBounds.step_words w p s u hwords hstep
    have hinputu := RamVirtualTraceBounds.step_input w p s u hstep
    have hpc := hpcs 0 (by omega) s rfl
    have hpcsu : ∀ j ≤ k, ∀ t, SparseRam.run w p j u = some t → t.pc + 1 < B := by
      intro j hj t ht
      apply hpcs (j + 1) (by omega) t
      simp only [SparseRam.run, hstep, Option.bind_some, ht]
    rintro σ ⟨hrep, hflag, hA, hV, hO⟩
    obtain ⟨ν, hbody, hpost⟩ := RamVirtualDispatch.dispatch_spec B w s p 0 hB hlit
      (by simpa using hp) hwords hinput hinputWords hpc (by omega) (by omega) σ
      ⟨hrep, hflag, by omega, by omega, by omega⟩
    rw [RamVirtualDispatch.result_zero, hstep] at hpost
    have hAν : N < (ν.arrs "vm.addresses").length := by
      rwa [RamFrames.run_array_length hbody "vm.addresses"]
    have hVν : N < (ν.arrs "vm.values").length := by
      rwa [RamFrames.run_array_length hbody "vm.values"]
    have hOν : N < (ν.arrs "vm.output").length := by
      rwa [RamFrames.run_array_length hbody "vm.output"]
    obtain ⟨τ, htail, hfinal⟩ := ih u hwordsu (by rwa [hinputu])
      (by simpa only [hinputu] using hinputWords) (by omega) (by omega) hpcsu hrest ν
      ⟨hpost.1, hpost.2, hAν, hVν, hOν⟩
    have htrue : (Cond.lt (.lit 0) (.var "vm.running")).evalB B σ = some true :=
      running_test (by omega) h1 hflag
    refine ⟨τ, (while_true htrue hbody htail).mono ?_, hfinal⟩
    simp only [Nat.add_mul, Nat.one_mul]
    omega

end Lax455465Proofs.RamVirtualLoop
