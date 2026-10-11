import Lax455465.FlowCutCertificate
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators NNReal NNRat

namespace Lax455465Proofs.UndirectedConversion

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow Lax455465.RationalEncoding

/-- Convert a directed flow in a symmetric capacity matrix to shared-capacity
undirected flow. The common demand fraction is retained. -/
def halve {n : ℕ} (F : ArcCertificate n) : ArcCertificate n where
  value := F.value
  arcs s t u v := F.arcs s t u v / 2

private theorem arc_halved {n : ℕ} (F : ArcCertificate n) (s t u v : Fin n) :
    ((halve F).flow s t u v : ℝ) = (F.flow s t u v : ℝ) / 2 := by
  simp [halve, ArcCertificate.flow, NNRat.cast_div]

private theorem load_halved {n : ℕ} (F : ArcCertificate n) (u v : Fin n) :
    (totalArcLoad (halve F).flow u v : ℝ) = (totalArcLoad F.flow u v : ℝ) / 2 := by
  simp only [totalArcLoad, NNReal.coe_sum, arc_halved]
  simp only [Finset.sum_div]

private theorem supply_halved {n : ℕ} (π : VertexWeight n) (f : ℝ≥0)
    (s t u : Fin n) :
    requiredSupply .undirected π f s t u = requiredSupply .directed π f s t u / 2 := by
  simp only [requiredSupply, pairDemand, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_ofNat]
  split_ifs <;> simp [NNReal.coe_mul, NNReal.coe_div] <;> ring

/-- The directed product construction covers undirected shared capacities by halving
its commodity arc amounts. -/
theorem halve_valid {n : ℕ} (I : RationalInstance n) (F : ArcCertificate n)
    (hsym : I.network.IsUndirected)
    (hF : IsArcConcurrentFlow .directed I.network I.weights (F.value : ℝ≥0) F.flow) :
    IsArcConcurrentFlow .undirected I.network I.weights
      ((halve F).value : ℝ≥0) (halve F).flow := by
  constructor
  · intro u v
    have huv := hF.1 u v
    have hvu := hF.1 v u
    simp only [totalEdgeLoad] at huv hvu
    rw [hsym v u] at hvu
    apply NNReal.coe_le_coe.mp
    simp only [totalEdgeLoad, NNReal.coe_add, load_halved]
    have huvR := NNReal.coe_le_coe.mpr huv
    have hvuR := NNReal.coe_le_coe.mpr hvu
    linarith
  · intro s t u
    change (∑ v, ((halve F).flow s t u v : ℝ)) -
      (∑ v, ((halve F).flow s t v u : ℝ)) =
      requiredSupply .undirected I.weights (F.value : ℝ≥0) s t u
    simp only [arc_halved]
    rw [← Finset.sum_div, ← Finset.sum_div, ← sub_div, hF.2 s t u, supply_halved]

end Lax455465Proofs.UndirectedConversion
