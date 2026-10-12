import Lax455465.ProductFlowCut
import Lax455465Proofs.MaxFlowBounds

open scoped BigOperators NNReal
namespace Lax455465Proofs.ProductFlowCut
open Lax455465.ProductNetwork Lax455465.ConcurrentFlow Lax455465.RationalEncoding

/--
---
conclusion: Lax455465.ProductFlowCut.exists_flow_cut_bound
---
The deterministic algorithm supplies an admissible cut and a feasible arc
flow. Public arc-to-path conversion puts its value in the feasible set defining
`maxFlow`; the boundedness lemma makes that value at most the supremum. The
admissible cut bounds the infimum defining `sparsestCut`, yielding the classical
inequality with the algorithm's same universal approximation constant.
-/
theorem exists_flow_cut_bound :
  ∃ C : ℝ, 0 < C ∧
    ∀ (kind : EdgeKind) (n : ℕ) (I : RationalInstance n),
      (kind = .undirected → I.network.IsUndirected) →
      2 ≤ supportCount I.weights →
      (sparsestCut I.network I.weights : ℝ) ≤
        C * logFactor (supportCount I.weights) * (maxFlow kind I.network I.weights : ℝ) := by
  obtain ⟨solve, C, _, hC, hsolve⟩ := Lax455465.RamProductFlowCut.exists_polynomial_time_flow_cut
  refine ⟨C, hC, ?_⟩
  intro kind n I hsym hp
  obtain ⟨certificate, _, hvalid⟩ := hsolve kind n I hsym hp
  obtain ⟨hcut, hflow, hratio⟩ := hvalid
  obtain ⟨P, hP, _⟩ := Lax455465.ArcToPath.exists_path_flow kind I.network I.weights
    (certificate.flow.value : ℝ≥0) certificate.flow.flow hflow
  have hf : (certificate.flow.value : ℝ≥0) ≤ maxFlow kind I.network I.weights :=
    le_csSup (MaxFlowBounds.bounded_values kind I.network I.weights hp) ⟨P, hP⟩
  have hf' : (certificate.flow.value : ℝ) ≤ (maxFlow kind I.network I.weights : ℝ) := by
    exact_mod_cast hf
  have hlog : 0 ≤ logFactor (supportCount I.weights) := by
    have h1 : 1 ≤ supportCount I.weights := by omega
    have hp' : (1 : ℝ) ≤ supportCount I.weights := by exact_mod_cast h1
    exact div_nonneg (Real.log_nonneg hp') (Real.log_nonneg (by norm_num))
  have hbound := mul_le_mul_of_nonneg_left hf' (mul_nonneg hC.le hlog)
  have hmin : sparsestCut I.network I.weights ≤ ratioCost I.network I.weights certificate.cut :=
    csInf_le (OrderBot.bddBelow _) ⟨certificate.cut, hcut, rfl⟩
  have hmin' : (sparsestCut I.network I.weights : ℝ) ≤
      (ratioCost I.network I.weights certificate.cut : ℝ) := by exact_mod_cast hmin
  exact hmin'.trans (hratio.trans hbound)

end Lax455465Proofs.ProductFlowCut
