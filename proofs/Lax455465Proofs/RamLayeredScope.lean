import Lax455465Proofs.RamLayeredLpSolver
import Lax455465Proofs.RamLpPrivateScope
import Lax455465Proofs.RamLpNoWrite

namespace Lax455465Proofs.RamLayeredScope
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamLayeredData

set_option maxRecDepth 8192

theorem solver_vars (p : Lax808846.Ram.Program) (coefficients : List ℕ)
    (x : String) (hx : x ∈ protectedVars) :
    x ∉ (RamLayeredLpSolver.command p coefficients).wvars := by
  have hbuild : x ∉ RamLayeredLp.command.wvars := by
    simp only [protectedVars,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hinvoke : x ∉ (RegisteredLpInvocation.command p coefficients).wvars := by
    apply RamLpPrivateScope.invocation_vars
    simp only [protectedVars,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact fun h => (List.mem_append.mp h).elim hbuild hinvoke

theorem solver_capacities (p : Lax808846.Ram.Program) (coefficients : List ℕ) :
    "flow.capacities" ∉ (RamLayeredLpSolver.command p coefficients).warrs := by
  have hb : "flow.capacities" ∉ RamLayeredLp.command.warrs := by decide
  have hi := RamLpPrivateScope.invocation_arrays p coefficients "flow.capacities" (by decide)
  exact fun h => (List.mem_append.mp h).elim hb hi

theorem solver_data {B K : ℕ} {p : Lax808846.Ram.Program} {coefficients : List ℕ}
    {σ τ : Env} (hr : Run B (RamLayeredLpSolver.command p coefficients) σ τ K)
    {n L : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n) (h : Data I L σ) :
    Data I L τ :=
  frame hr I L h (solver_capacities p coefficients) (solver_vars p coefficients)

theorem solver_nowrite (p : Lax808846.Ram.Program) (coefficients : List ℕ) :
    (RamLayeredLpSolver.command p coefficients).NoWrite :=
  ⟨by decide,RamLpNoWrite.prepare coefficients,RamLpNoWrite.execute p⟩

end Lax455465Proofs.RamLayeredScope
