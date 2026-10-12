import Lax455465Proofs.RamRegionSetup
import Lax455465Proofs.RegionRounding
import Lax455465Proofs.RamRegionBranch
import Lax455465Proofs.ResidualData
import Lax455465Proofs.RamLargeThreshold

open scoped BigOperators NNRat
namespace Lax455465Proofs.RegionExecutionData
open Lax455465.RationalEncoding RegionQueryData

def query {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (active : Finset (Fin n)) (root : Fin n) (seed beta : ℚ≥0) : Query n :=
  RamRegionSetup.query (ResidualData.weights I active) (ResidualData.capacity I active) length root seed beta

def region {n : ℕ} (q : Query n) (root : Fin n) : RegionLoop.Region n :=
  ⟨root,q.radius,direction q q.radius⟩

/-- The native test of both ball masses is equivalent to the mathematical
loop's test of the smaller selected ball. -/
theorem large_iff {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (active : Finset (Fin n)) (root : Fin n) (seed beta r total : ℚ≥0) :
    RamRegionBranch.large (RadiusSearchData.atRadius (query I length active root seed beta) r)
      (RamLargeThreshold.threshold total) ↔
      (2/3 : ℚ)*(total : ℚ)≤∑ v∈(region (RadiusSearchData.atRadius (query I length active root seed beta) r) root).ball
        (MetricMatrix.rational length), RegionLoop.weights I active v := by
  let q := RadiusSearchData.atRadius (query I length active root seed beta) r
  have hmass := RegionSelection.chosen_mass (RegionLoop.weights I active)
    (fun v => (length root v : ℚ)) (fun v => (length v root : ℚ)) (r : ℚ)
  have hball : (region q root).ball (MetricMatrix.rational length)=RegionCharging.chosenBall
      (fun v => (length root v : ℚ)) (fun v => (length v root : ℚ))
      (RegionLoop.chooseDirection I (MetricMatrix.rational length) active root) r := by
    unfold region RegionLoop.Region.ball RegionCharging.chosenBall
    simp only [q,query,RamRegionSetup.query,RadiusSearchData.atRadius,direction,
      ResidualData.rational_weights,RegionLoop.chooseDirection,MetricMatrix.rational]
    rfl
  change _ ↔ _≤∑ v∈(region q root).ball (MetricMatrix.rational length), _
  rw [hball]
  change _ ↔ _≤∑ v∈RegionCharging.chosenBall (fun v => (length root v : ℚ))
    (fun v => (length v root : ℚ)) (RegionSelection.direction (RegionLoop.weights I active)
      (fun v => (length root v : ℚ)) (fun v => (length v root : ℚ))) r, RegionLoop.weights I active v
  rw [hmass]
  unfold RamRegionBranch.large
  rw [RamLargeThreshold.coe_threshold]
  have hout : (BallMassData.mass q.weights q.outDistance q.radius : ℚ)=
      RegionSelection.ballMass (RegionLoop.weights I active) (fun v => (length root v : ℚ)) r := by
    rw [BallMassData.coe_mass]
    simp only [q,query,RamRegionSetup.query,RadiusSearchData.atRadius,ResidualData.rational_weights]
  have hin : (BallMassData.mass q.weights q.inDistance q.radius : ℚ)=
      RegionSelection.ballMass (RegionLoop.weights I active) (fun v => (length v root : ℚ)) r := by
    rw [BallMassData.coe_mass]
    simp only [q,query,RamRegionSetup.query,RadiusSearchData.atRadius,ResidualData.rational_weights]
  rw [hout,hin,le_min_iff]
  have he : 2*(total : ℚ)/3=(2/3 : ℚ)*(total : ℚ) := by ring
  rw [he]

/-- Successful residual searches follow from the region-growing theorem;
this is a proof about the stored graph, not an extra input to the program. -/
theorem search_exists {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n)
    (active : Finset (Fin n)) (root : Fin n) (seed delta : ℚ≥0) (p : ℕ)
    (hseed : 0<(seed : ℚ)) (hdelta : 0<(delta : ℚ)) (hp : 0<p)
    (htri : ∀ u v w, (length u w : ℚ)≤(length u v : ℚ)+(length v w : ℚ))
    (hcost : RegionRounding.metricCost I (MetricMatrix.rational length)≤(p : ℚ)*(seed : ℚ)) :
    ∃ r, RegionSearch.search (RegionLoop.capacity I active) (MetricMatrix.rational length)
      (fun v => (length root v : ℚ)) (fun v => (length v root : ℚ)) seed delta p
      (RegionLoop.chooseDirection I (MetricMatrix.rational length) active root)=some r := by
  have hd : RationalDistances.Nonnegative (MetricMatrix.rational length) := fun u v => (length u v).coe_nonneg
  obtain ⟨r,hr,_,_,_⟩ := RegionSearch.search_correct (RegionLoop.capacity I active) (MetricMatrix.rational length)
    (fun v => (length root v : ℚ)) (fun v => (length v root : ℚ)) seed delta p
    (RegionLoop.chooseDirection I (MetricMatrix.rational length) active root)
    (RegionLoop.capacity_nonnegative I active) hd hseed hdelta hp
    ((RegionLoop.residual_cost_le I _ active hd).trans hcost)
    (fun u v => by dsimp only [MetricMatrix.rational]; linarith [htri root u v])
    (fun u v => by dsimp only [MetricMatrix.rational]; linarith [htri v u root])
  exact ⟨r,hr⟩

end Lax455465Proofs.RegionExecutionData
