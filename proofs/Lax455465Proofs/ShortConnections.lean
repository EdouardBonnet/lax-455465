import Lax455465Proofs.BoundedDistances
import Lax455465Proofs.RegionBudget

open scoped BigOperators
namespace Lax455465Proofs.ShortConnections
open Lax455465.RationalEncoding BoundedDistances UniformCutBounds

/-- A bounded number of relaxations produces short connections to a large
set with a controlled sum of costs. All returned costs have real walk
witnesses; initial capped values cannot survive the final estimate. -/
theorem connections {n : ℕ} (I : RationalInstance n) (hw : ∀ v,I.weight v=1)
    (s R d E : ℚ) (hs : 0 ≤ s) (hR : 0 < R) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hE : 0 < E)
    (hcut : CutLower I s) (hcap : ∀ v,(∑ u,(I.capacity u v : ℚ)) ≤ R)
    (T : Finset (Fin n)) (hT : d*R ≤ s*(T.card : ℚ))
    (ell : Length n) (hell : ∀ u v,0 ≤ ell u v)
    (hcost : (∑ u,∑ v,(I.capacity u v : ℚ)*ell u v) ≤ d*R*E)
    (m K : ℕ) (hm : 1 ≤ m*d) (hK : (1/2 : ℚ)^K*(4*n) ≤ 1) :
    (∑ v,run ell T (4*E) (m*K) v) ≤ 2*E ∧
    ∀ v,∃ t∈T,∃ h ≤ m*K,∃ c ≤ run ell T (4*E) (m*K) v,Route ell t v h c := by
  let D : ℕ → ℚ := fun k => ∑ v,run ell T (4*E) k v
  have hnonneg (k : ℕ) : ∀ v,0 ≤ run ell T (4*E) k v := nonnegative ell T _ hell (by positivity) k
  have hD (k : ℕ) : 0 ≤ D k := Finset.sum_nonneg fun v _ => hnonneg k v
  have hinitial : D 0 ≤ 4*(n : ℚ)*E := by
    calc
      D 0 ≤ ∑ _v : Fin n,4*E := by
        apply Finset.sum_le_sum
        intro v _
        dsimp [run,initial]
        split_ifs <;> linarith
      _ = _ := by simp; ring
  have hstep (k : ℕ) : D (k+1) ≤ (1-d)*D k+(1-(1-d))*E := by
    have hc := large_set_coarea I hw s hs hcut T (run ell T (4*E) k)
      (hnonneg k) (zero_on_set ell T _ hell (by positivity) k)
    have he := HopContraction.energy_drop I ell hell R hcap (run ell T (4*E) k)
      (run ell T (4*E) (k+1)) (step_le ell _) (step_edge ell _)
    have hmT := mul_le_mul_of_nonneg_right hT (hD k)
    change s*(T.card : ℚ)*D k ≤ _ at hc
    change _ ≤ (∑ u,∑ v,(I.capacity u v : ℚ)*ell u v)+R*(D k-D (k+1)) at he
    nlinarith
  have hr : 0 ≤ 1-d := by linarith
  have hgeom := HopContraction.iterate_bound D (1-d) E hr hstep (m*K)
  have hpow : (1-d)^(m*K) ≤ (1/2 : ℚ)^K := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg hr _) (HopContraction.block_half d hd0 hd1 m hm) K
  have hupper : D (m*K) ≤ 2*E := by
    have hp0 := pow_nonneg hr (m*K)
    have hp1 := pow_nonneg (show (0 : ℚ) ≤ 1/2 by norm_num) K
    have ha := mul_le_mul_of_nonneg_left hinitial hp1
    have hb := mul_le_mul_of_nonneg_right hpow (hD 0)
    have hc := mul_le_mul_of_nonneg_right hK hE.le
    nlinarith
  refine ⟨hupper,?_⟩
  intro v
  have hv : run ell T (4*E) (m*K) v ≤ D (m*K) :=
    Finset.single_le_sum (fun u _ => hnonneg _ u) (Finset.mem_univ v)
  exact route_of_lt ell T (4*E) hell (m*K) v (by linarith)

/-- The existing integer logarithmic budget is enough for the contraction
as well as for region growth. -/
theorem budget_decay (n : ℕ) (hn : 0 < n) :
    (1/2 : ℚ)^(RegionBudget.steps n)*(4*n) ≤ 1 := by
  have hp := RegionBudget.exceeds_budget n hn
  have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hbase : (0 : ℚ) < 2^RegionBudget.steps n := pow_pos (by norm_num) _
  calc
    (1/2 : ℚ)^(RegionBudget.steps n)*(4*n) = (4*n)/(2^RegionBudget.steps n) := by
      rw [one_div_pow]
      ring
    _ ≤ 1 := (div_le_iff₀ hbase).mpr (by nlinarith)

end Lax455465Proofs.ShortConnections
