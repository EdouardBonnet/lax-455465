import Lax455465Proofs.RamShortContext
import Lax455465Proofs.RamLayeredScope
import Lax455465Proofs.RamLayeredValue
import Lax455465Proofs.RamShortTest

namespace Lax455465Proofs.RamShortTrial
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open RamShortContext LayeredFlowLP LayeredFlowDual
open Lax455465.RationalEncoding Lax109476.RationalEncoding
open scoped NNRat

/-- At the full simple-path budget, accept even if the ratio test fails. -/
def fallback : Com := .ite (.eq (.var "short.layer") (.sub (.var "lp.n") (.lit 1)))
  (.assign "find.ok" (.lit 1)) .skip

theorem fallback_spec (B n L : ℕ) (P : Prop) [Decidable P] (hn : n<B) (hL : L<B) (h1 : 1<B) :
    Spec B (fun σ => σ.vars "lp.n"=n ∧ σ.vars "short.layer"=L ∧
      σ.vars "find.ok"=if P then 1 else 0) fallback
      (fun _ τ => τ.vars "find.ok"=if P ∨ L=n-1 then 1 else 0) 8 := by
  rintro σ ⟨hnσ,hLσ,hpσ⟩
  run_vcg
  all_goals simp_all

def command (p : Lax808846.Ram.Program) (coefficients : List ℕ) : Com :=
  .seq (.assign "short.layer" (.add (.var "find.i") (.lit 1)))
  (.seq RamLayeredData.dimensions
  (.seq (RamLayeredLpSolver.command p coefficients)
  (.seq RamLayeredValue.command (.seq RamShortTest.command fallback))))

theorem solver_frame {B K : ℕ} {p : Lax808846.Ram.Program} {coefficients : List ℕ}
    {σ τ : Env} (hr : Run B (RamLayeredLpSolver.command p coefficients) σ τ K)
    {n words time : ℕ} {I : RationalInstance n} {R : ℚ≥0} (h : Context I R words time σ) :
    Context I R words time τ := by
  apply RamShortContext.frame hr h _ (RamLayeredScope.solver_capacities p coefficients)
  intro x hx
  have hb : x∉RamLayeredLp.command.wvars := by
    simp only [RamShortContext.names,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> decide
  have hi : x∉(RegisteredLpInvocation.command p coefficients).wvars := by
    apply RamLpPrivateScope.invocation_vars
    simp only [RamShortContext.names,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> decide
  exact fun hh => (List.mem_append.mp hh).elim hb hi

/-- Each trial constructs and solves its runtime layer budget, reads the
same emitted primal value, and computes the exact stopping bit. -/
theorem command_spec (B M K n words time i : ℕ) (I : RationalInstance n) (R f : ℚ≥0)
    (x : Arc n (i+1) → ℚ) (y : Dual n (i+1))
    (p : Lax808846.Ram.Program) (coefficients : List ℕ)
    (hshape : RamLayeredData.shapeSize n (i+1)<B)
    (htest : RamShortTest.space n (i+1) M<B)
    (hRn : R.num≤M) (hRd : R.den≤M) (hfn : f.num≤M) (hfd : f.den≤M)
    (hwords : ∀ k∈encodeCertificate (.optimal (vector (f : ℚ) x) y),k<B)
    (hsolve : Spec B (fun σ => Context I R words time σ ∧ RamLayeredData.Data I (i+1) σ)
      (RamLayeredLpSolver.command p coefficients)
      (fun _ τ => Prefix (encodeCertificate (.optimal (vector (f : ℚ) x) y)) "vm.output" τ) K) :
    Spec B (fun σ => Context I R words time σ ∧ σ.vars "find.i"=i)
      (command p coefficients)
      (fun _ τ => Context I R words time τ ∧
        τ.vars "find.ok"=if (R : ℚ) ≤ 4*n*(i+1)*(f : ℚ) ∨ i+1=n-1 then 1 else 0) (K+100) := by
  have hsmall : n<B ∧ i+1<B ∧ 4<B := by
    dsimp only [RamLayeredData.shapeSize] at hshape
    omega
  rintro σ ⟨hctx,hi⟩
  let σ1 := σ.setVar "short.layer" (i+1)
  have r1 : Run B (.assign "short.layer" (.add (.var "find.i") (.lit 1))) σ σ1 4 :=
    Run.assign (evalB_bin (op := .add)
      (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ (by omega : i<B)⟩)
      (evalB_lit (by omega)) hsmall.2.1)
  have hc1 := RamShortContext.set_var hctx "short.layer" (i+1) (by decide)
  obtain ⟨σ2,r2,hdata⟩ := RamLayeredSource.from_source B I (i+1) hshape σ1 ⟨hc1.source,by simp [σ1]⟩
  have hc2 := RamShortContext.frame r2 hc1 (by decide) (by decide)
  obtain ⟨σ3,r3,hcert⟩ := hsolve σ2 ⟨hc2,hdata⟩
  have hc3 := solver_frame r3 hc2
  have hd3 := RamLayeredScope.solver_data r3 I hdata
  obtain ⟨σ4,r4,hvalue⟩ := RamLayeredValue.command_spec B (f : ℚ) x y hsmall.2.2 hwords σ3 hcert
  have hc4 := RamShortContext.frame r4 hc3 (by decide) (by decide)
  have hL4 := (r4.frame_var "short.layer" (by decide)).trans hd3.layer
  obtain ⟨σ5,r5,ht⟩ := RamShortTest.command_spec B M n (i+1) R f htest hRn hRd hfn hfd σ4
    ⟨hc4.source.order,hL4,hc4.maximum,hvalue⟩
  have hc5 := RamShortContext.frame r5 hc4 (by decide) (by decide)
  have hL5 := (r5.frame_var "short.layer" (by decide)).trans hL4
  obtain ⟨σ6,r6,hf⟩ := fallback_spec B n (i+1) ((R : ℚ) ≤ 4*n*(i+1)*(f : ℚ))
    hsmall.1 hsmall.2.1 (by omega) σ5 ⟨hc5.source.order,hL5,by simpa only [Nat.cast_add,Nat.cast_one] using ht⟩
  exact ⟨σ6,(r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))).mono (by omega),
    RamShortContext.frame r6 hc5 (by decide) (by decide),hf⟩

theorem scan_frame (p : Lax808846.Ram.Program) (coefficients : List ℕ)
    (x : String) (hx : x∈["find.i","find.found","find.result","find.count"]) :
    x∉(command p coefficients).wvars := by
  have hs : x∉(RamLayeredLpSolver.command p coefficients).wvars := by
    have hb : x∉RamLayeredLp.command.wvars := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide
    have hi : x∉(RegisteredLpInvocation.command p coefficients).wvars := by
      apply RamLpPrivateScope.invocation_vars
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide
    exact fun hh => (List.mem_append.mp hh).elim hb hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    simpa [command,RamLayeredData.dimensions,RamLayeredValue.command,RamLpRationalRead.command,
      RamShortTest.command,fallback,Com.wvars] using hs

end Lax455465Proofs.RamShortTrial
