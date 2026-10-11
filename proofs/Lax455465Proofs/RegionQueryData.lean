import Lax455465Proofs.BoundaryData
import Lax455465Proofs.VolumeData

namespace Lax455465Proofs.RegionQueryData

open MetricMatrix
open scoped NNRat

structure Query (n : ℕ) where
  weights : Fin n → ℚ≥0
  capacity : Matrix n
  length : Matrix n
  outDistance : Fin n → ℚ≥0
  inDistance : Fin n → ℚ≥0
  seed : ℚ≥0
  beta : ℚ≥0
  radius : ℚ≥0

def direction {n : ℕ} (q : Query n) (r : ℚ) : Bool :=
  RegionSelection.direction (fun v => (q.weights v : ℚ)) (fun v => (q.outDistance v : ℚ))
    (fun v => (q.inDistance v : ℚ)) r

def distance {n : ℕ} (q : Query n) (outward : Bool) : Fin n → ℚ≥0 :=
  if outward then q.outDistance else q.inDistance

def boundaryAt {n : ℕ} (q : Query n) (outward : Bool) : ℚ≥0 :=
  BoundaryData.value outward q.capacity (distance q outward) q.radius

def volumeAt {n : ℕ} (q : Query n) (outward : Bool) : ℚ≥0 :=
  VolumeData.value outward q.capacity q.length (distance q outward) q.seed q.radius

def boundary {n : ℕ} (q : Query n) : ℚ≥0 := boundaryAt q (direction q q.radius)
def volume {n : ℕ} (q : Query n) : ℚ≥0 := volumeAt q (direction q q.radius)
def bound {n : ℕ} (q : Query n) : ℚ≥0 := q.beta*volume q

def accepted {n : ℕ} (q : Query n) : Bool := decide (0 < (q.radius : ℚ) ∧
  RegionSearch.Good (rational q.capacity) (rational q.length)
    (fun v => (q.outDistance v : ℚ)) (fun v => (q.inDistance v : ℚ)) q.seed q.beta (direction q) q.radius)

theorem coe_boundary {n : ℕ} (q : Query n) :
    (boundary q : ℚ) = RegionSearch.selectedBoundary (rational q.capacity)
      (fun v => (q.outDistance v : ℚ)) (fun v => (q.inDistance v : ℚ)) (direction q) q.radius := by
  rw [boundary,boundaryAt,BoundaryData.coe_value]
  unfold RegionSearch.selectedBoundary distance
  cases direction q q.radius <;> rfl

theorem coe_volume {n : ℕ} (q : Query n) :
    (volume q : ℚ) = RegionSearch.selectedVolume (rational q.capacity) (rational q.length)
      (fun v => (q.outDistance v : ℚ)) (fun v => (q.inDistance v : ℚ)) q.seed (direction q) q.radius := by
  rw [volume,volumeAt,VolumeData.coe_value]
  unfold RegionSearch.selectedVolume distance
  cases direction q q.radius <;> rfl

/-- The native positive-radius and rational-comparison test is precisely the
predicate searched by the deterministic radius-selection procedure. -/
theorem accepted_eq {n : ℕ} (q : Query n) :
    accepted q = decide (0 < q.radius.num ∧ (boundary q : ℚ) ≤ (bound q : ℚ)) := by
  unfold accepted bound
  simp only [NNRat.coe_mul,coe_boundary,coe_volume,RegionSearch.Good]
  congr 1
  apply propext
  constructor
  · rintro ⟨hr,hb⟩
    refine ⟨?_,hb⟩
    exact NNRat.num_pos.mpr (by exact_mod_cast hr)
  · rintro ⟨hr,hb⟩
    refine ⟨?_,hb⟩
    exact_mod_cast NNRat.num_pos.mp hr

end Lax455465Proofs.RegionQueryData
