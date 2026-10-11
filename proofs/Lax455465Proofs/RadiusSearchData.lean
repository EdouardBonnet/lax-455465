import Lax455465Proofs.RamFind
import Lax455465Proofs.RegionQueryData
import Lax455465Proofs.RadiusData

namespace Lax455465Proofs.RadiusSearchData
open RegionQueryData
open scoped NNRat

def atRadius {n : ℕ} (q : Query n) (r : ℚ≥0) : Query n := {q with radius := r}
def predicate {n : ℕ} (q : Query n) (radii : List ℚ≥0) (i : ℕ) : Bool := accepted (atRadius q (radii.getD i 0))

theorem index_values (radii : List ℚ≥0) :
    (List.range radii.length).map (fun i => radii.getD i 0) = radii := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_map,List.getElem_range,
      List.getD_eq_get radii 0 (⟨i,h₂⟩ : Fin radii.length),List.get_eq_getElem]

theorem first_value {n : ℕ} (q : Query n) (radii : List ℚ≥0) :
    (RamFind.first (predicate q radii) radii.length).map (fun i => radii.getD i 0) =
      radii.find? (fun r => accepted (atRadius q r)) := by
  have h := List.find?_map (p := fun r => accepted (atRadius q r))
    (f := fun i => radii.getD i 0) (l := List.range radii.length)
  unfold RamFind.first RadiusSearchData.predicate
  simpa only [index_values,Function.comp_def] using h.symm

theorem search_value {n : ℕ} (q : Query n) (delta : ℚ≥0) (p : ℕ)
    (hb : (q.beta : ℚ)=RegionSearch.slope (RegionBudget.steps p) delta) :
    ((RadiusData.candidates q.outDistance q.inDistance (RegionBudget.steps p) delta).find?
      (fun r => accepted (atRadius q r))).map (fun r : ℚ≥0 => (r : ℚ)) =
      RegionSearch.search (MetricMatrix.rational q.capacity) (MetricMatrix.rational q.length)
        (fun v => (q.outDistance v : ℚ)) (fun v => (q.inDistance v : ℚ)) q.seed delta p (direction q) := by
  unfold RegionSearch.search
  rw [← RadiusData.coe_candidates,List.find?_map]
  congr 2
  funext r
  simp only [Function.comp_def,accepted,atRadius,hb]
  rfl

end Lax455465Proofs.RadiusSearchData
