import Lax455465.ArcToPath
import Lax455465Proofs.PathFlowSums

open scoped BigOperators NNReal
namespace Lax455465Proofs.ArcToPath
open Lax455465.ProductNetwork Lax455465.ConcurrentFlow
open RealPositivePath RealFlowDecomposition PathFlowSums

theorem commodity {n : ℕ} (s t : Fin n) (g : Fin n → Fin n → ℝ≥0)
    (a : ℝ≥0) (hst : s ≠ t)
    (hbal : Balance (fun u v => (g u v : ℝ)) s t (a : ℝ)) :
    ∃ P : PathFlow n, IsPathFlow P ∧ (∀ u v, arcLoad P u v ≤ g u v) ∧
      routed P s t = a := by
  obtain ⟨rs, hvalid, hmass, hload, _⟩ := exists_records (fun u v => (g u v : ℝ))
    (fun u v => (g u v).coe_nonneg) s t hst (a : ℝ) a.coe_nonneg hbal
  have hpos : ∀ r ∈ rs, 0 ≤ r.2 := fun r hr => (hvalid r hr).1.le
  refine ⟨RealPathFlow.flow rs, RealPathFlow.isPathFlow hst hvalid, ?_, ?_⟩
  · intro u v
    apply NNReal.coe_le_coe.mp
    rw [RealPathFlow.arcLoad_cast rs hpos]
    exact hload u v
  · apply NNReal.coe_injective
    rw [RealPathFlow.routed_self hvalid, hmass]

/--
---
conclusion: Lax455465.ArcToPath.exists_path_flow
---
Extract simple positive paths by repeated bottleneck subtraction for each
off-diagonal commodity. Conservation supplies a path whenever residual supply
is positive, even if the residual contains cycles. Each subtraction either
finishes the supply or removes a positive arc, giving finite termination.
Adding the commodity path flows preserves capacities and the common value.
-/
theorem exists_path_flow {n : ℕ} (kind : EdgeKind) (N : Network n)
    (π : VertexWeight n) (f : ℝ≥0) (F : ArcFlow n)
    (hF : IsArcConcurrentFlow kind N π f F) :
    ∃ P : PathFlow n, IsConcurrentFlow kind N π f P ∧
      ∀ u v, arcLoad P u v ≤ totalArcLoad F u v := by
  classical
  have hc : ∀ s t, ∃ P : PathFlow n, IsPathFlow P ∧
      (∀ u v, arcLoad P u v ≤ F s t u v) ∧
      (s ≠ t → f * pairDemand kind π s t ≤ routed P s t) := by
    intro s t
    by_cases hst : s = t
    · refine ⟨0, by simp [IsPathFlow], ?_, ?_⟩
      · intro u v
        simp [arcLoad]
      · intro hne
        exact (hne hst).elim
    · have hb : Balance (fun u v => (F s t u v : ℝ)) s t
          (f * pairDemand kind π s t : ℝ≥0) := by
        intro u
        simpa only [requiredSupply, if_neg hst, apply_ite, NNReal.coe_zero] using hF.2 s t u
      obtain ⟨P, hP, hload, hrouted⟩ := commodity s t (F s t) (f * pairDemand kind π s t) hst hb
      exact ⟨P, hP, hload, fun _ => hrouted.ge⟩
  choose P hP hload hdemand using hc
  let Q : PathFlow n := ∑ s, ∑ t, P s t
  have hQ : IsPathFlow Q :=
    isPathFlow_sum _ _ (fun s _ => isPathFlow_sum _ _ (fun t _ => hP s t))
  have hloadQ : ∀ u v, arcLoad Q u v ≤ totalArcLoad F u v := by
    intro u v
    simp only [Q, arcLoad_sum, totalArcLoad]
    exact Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ => hload s t u v
  refine ⟨Q, ⟨hQ, ?_, ?_⟩, hloadQ⟩
  · intro u v
    cases kind with
    | directed => exact (hloadQ u v).trans (hF.1 u v)
    | undirected => exact (add_le_add (hloadQ u v) (hloadQ v u)).trans (hF.1 u v)
  · intro s t hst
    apply (hdemand s t hst).trans
    simp only [Q, routed_sum]
    have h₁ : routed (P s t) s t ≤ ∑ j, routed (P s j) s t :=
      Finset.single_le_sum (f := fun j => routed (P s j) s t)
        (fun _ _ => bot_le) (Finset.mem_univ t)
    have h₂ : (∑ j, routed (P s j) s t) ≤ ∑ i, ∑ j, routed (P i j) s t :=
      Finset.single_le_sum (f := fun i => ∑ j, routed (P i j) s t)
        (fun _ _ => bot_le) (Finset.mem_univ s)
    exact h₁.trans h₂

end Lax455465Proofs.ArcToPath
