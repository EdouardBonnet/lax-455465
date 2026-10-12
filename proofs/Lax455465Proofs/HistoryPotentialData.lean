import Lax455465Proofs.RamRegionWhole
import Lax455465Proofs.RamPotentialSweep

set_option backward.isDefEq.respectTransparency false

namespace Lax455465Proofs.HistoryPotentialData
open Lax455465.RationalEncoding RamRegionRecord RegionHistory RegionOrdering
open scoped BigOperators NNRat

def contains {n : ℕ} (d : MetricMatrix.Matrix n) (e : Entry n) (v : Fin n) : Bool :=
  if e.outward then decide (d e.root v<e.radius) else decide (d v e.root<e.radius)
def predicate {n : ℕ} (d : MetricMatrix.Matrix n) (history : List (Entry n)) (v : Fin n) (i : ℕ) : Bool :=
  ((history[i]?).map (fun e => contains d e v)).getD false

theorem contains_eq {n : ℕ} (d : MetricMatrix.Matrix n) (e : Entry n) (v : Fin n) :
    contains d e v=decide (v∈e.region.ball (MetricMatrix.rational d)) := by
  cases he : e.outward <;> simp [contains,Entry.region,RegionLoop.Region.ball,RegionCharging.ball,MetricMatrix.rational,he]

theorem predicate_at {n : ℕ} (d : MetricMatrix.Matrix n) (history : List (Entry n)) (v : Fin n)
    (i : ℕ) (hi : i<history.length) : predicate d history v i=contains d history[i] v := by
  simp only [predicate,List.getElem?_eq_getElem hi,Option.map_some,Option.getD_some]

theorem index_findIdx_regions {n : ℕ} (d : RationalDistances.Distance n) (history : List (RegionLoop.Region n)) (v : Fin n) :
    (index d history v).val=history.findIdx (fun e => decide (v ∈ e.ball d)) := by
  induction history with
  | nil => rfl
  | cons e rest ih =>
    by_cases hv : v ∈ e.ball d <;> simp [RegionHistory.index, List.findIdx_cons, hv, ih]

theorem index_findIdx {n : ℕ} (d : MetricMatrix.Matrix n) (history : List (Entry n)) (v : Fin n) :
    (index (MetricMatrix.rational d) (history.map Entry.region) v).val=history.findIdx (fun e => contains d e v) := by
  rw [index_findIdx_regions, List.findIdx_map]
  simp only [Function.comp_def, contains_eq]

theorem first_index {n : ℕ} (d : MetricMatrix.Matrix n) (history : List (Entry n)) (v : Fin n) :
    (RamFind.first (predicate d history v) history.length).getD history.length=
      (index (MetricMatrix.rational d) (history.map Entry.region) v).val := by
  rw [index_findIdx]
  cases he : RamFind.first (predicate d history v) history.length with
  | none =>
    simp only [Option.getD_none]
    symm
    apply List.findIdx_eq_length_of_false
    intro e he
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp he
    have hf := RamFind.first_none (predicate d history v) history.length (by assumption) i hi
    simpa only [predicate_at d history v i hi] using hf
  | some j =>
    simp only [Option.getD_some]
    have hs := List.find?_range_eq_some.mp he
    have hj := List.mem_range.mp hs.2.1
    symm
    apply (List.findIdx_eq hj).mpr
    exact ⟨by simpa only [predicate_at d history v j hj] using hs.1,
      fun i hi => by simpa [predicate_at d history v i (hi.trans hj)] using hs.2.2 i hi⟩

def values {n : ℕ} (d : MetricMatrix.Matrix n) (history : List (Entry n)) (v : Fin n) : ℚ≥0 :=
  (position history.length (orientation (history.map Entry.region))
    (index (MetricMatrix.rational d) (history.map Entry.region) v).val : ℕ)

theorem value_none {n : ℕ} (d : MetricMatrix.Matrix n) (history : List (Entry n)) (v : Fin n)
    (h : RamFind.first (predicate d history v) history.length=none) :
    values d history v=(history.length : ℚ≥0) := by
  have hi := first_index d history v
  rw [h,Option.getD_none] at hi
  unfold values
  rw [←hi]
  simp [position]

theorem value_some {n : ℕ} (d : MetricMatrix.Matrix n) (history : List (Entry n)) (v : Fin n)
    (j : ℕ) (h : RamFind.first (predicate d history v) history.length=some j)
    (hj : j < history.length) :
    values d history v=((if history[j].outward then 2*history.length-j else j : ℕ) : ℚ≥0) := by
  have hi := first_index d history v
  rw [h,Option.getD_some] at hi
  unfold values
  rw [←hi]
  have ho : orientation (history.map Entry.region) j=history[j].outward := by
    simp only [orientation,List.getElem?_map,List.getElem?_eq_getElem hj,Option.map_some,Option.getD_some,Entry.region]
  simp only [position,if_neg (Nat.ne_of_lt hj),ho]

theorem value_height {n : ℕ} (d : MetricMatrix.Matrix n) (history : List (Entry n)) (M : ℕ)
    (h1 : 1≤M) (hm : 2*history.length≤M) (v : Fin n) : LpInputSize.Height M (values d history v : ℚ) := by
  have hj : (index (MetricMatrix.rational d) (history.map Entry.region) v).val≤history.length := by
    have h := (index (MetricMatrix.rational d) (history.map Entry.region) v).isLt
    simp only [List.length_map] at h
    omega
  have hp : position history.length (orientation (history.map Entry.region))
      (index (MetricMatrix.rational d) (history.map Entry.region) v).val≤M := by
    unfold position
    split_ifs <;> omega
  exact ⟨by simpa [values] using hp,by simpa [values] using h1⟩

theorem late_mem {n k : ℕ} (labels : Fin n → Fin (k+1)) (orientation : ℕ → Bool) (t : ℕ)
    (hnonempty : (lateCut labels orientation t).Nonempty) :
    lateCut labels orientation t∈ThresholdCutData.candidates true
      (fun v => (position k orientation (labels v).val : ℕ)) := by
  let S := lateCut labels orientation t
  let pos := fun v => position k orientation (labels v).val
  obtain ⟨v,hv,hmin⟩ := Finset.exists_mem_eq_inf' hnonempty pos
  have hvt : t<pos v := (Finset.mem_filter.mp hv).2
  have he : S=ThresholdCutData.shore true (fun u => (pos u : ℚ≥0)) (pos v) := by
    ext u
    simp only [S,lateCut,ThresholdCutData.shore,Finset.mem_filter,Finset.mem_univ,true_and,
      RamThresholdMask.chosen,if_true,decide_eq_true_eq]
    constructor
    · intro hu
      have hm := Finset.inf'_le pos (show u∈lateCut labels orientation t by simpa [lateCut] using hu)
      rw [hmin] at hm
      exact_mod_cast hm
    · intro hu
      have hpos : pos v≤pos u := by exact_mod_cast hu
      exact hvt.trans_le hpos
  rw [show lateCut labels orientation t=S from rfl,he]
  exact List.mem_map.mpr ⟨v,List.mem_finRange _,rfl⟩

theorem round_mem {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n) (history : List (Entry n))
    (S : Finset (Fin n))
    (hs : BalancedRegionCut.round I (index (MetricMatrix.rational d) (history.map Entry.region))
      (orientation (history.map Entry.region))=some S) (hv : CutSweeps.admissibleQ I S) :
    S∈CutSweeps.candidates (ThresholdCutData.potential true (values d history)) := by
  unfold BalancedRegionCut.round at hs
  obtain ⟨t,ht,he⟩ := Option.map_eq_some_iff.mp hs
  have hnonempty : S.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simpa only [he,CutSweeps.massQ,Finset.sum_empty,lt_self_iff_false] using hv.1
  subst S
  rw [←ThresholdCutData.candidates_eq]
  change _ ∈ ThresholdCutData.candidates true (fun v =>
    (position history.length (orientation (history.map Entry.region))
      (index (MetricMatrix.rational d) (history.map Entry.region) v).val : ℚ≥0))
  simpa only [List.length_map] using late_mem
    (index (MetricMatrix.rational d) (history.map Entry.region)) (orientation (history.map Entry.region)) t hnonempty

end Lax455465Proofs.HistoryPotentialData
