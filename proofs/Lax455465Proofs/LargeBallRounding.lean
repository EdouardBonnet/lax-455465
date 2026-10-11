import Lax455465Proofs.PotentialLayers
import Lax455465Proofs.SetDistances

open scoped BigOperators

namespace Lax455465Proofs.LargeBallRounding

open Lax455465.RationalEncoding CutSweeps SetDistances RationalDistances

def total {n : ℕ} (I : RationalInstance n) : ℚ := ∑ v, (I.weight v : ℚ)

def mass {n : ℕ} (I : RationalInstance n) (S : Finset (Fin n)) : ℚ :=
  ∑ v ∈ S, (I.weight v : ℚ)

def distanceSeparation {n : ℕ} (I : RationalInstance n) (d : Distance n) : ℚ :=
  ∑ u, ∑ v, (I.weight u : ℚ) * I.weight v * d u v

def fromAverage {n : ℕ} (I : RationalInstance n) (d : Distance n)
    (S : Finset (Fin n)) (hS : S.Nonempty) : ℚ :=
  ∑ v, (I.weight v : ℚ) * fromSet d S hS v

def toAverage {n : ℕ} (I : RationalInstance n) (d : Distance n)
    (S : Finset (Fin n)) (hS : S.Nonempty) : ℚ :=
  ∑ v, (I.weight v : ℚ) * toSet d S hS v

/-- Compare the two exact weighted distances, selecting the larger one. -/
def potential {n : ℕ} (I : RationalInstance n) (d : Distance n)
    (Tin Tout : Finset (Fin n)) (hin : Tin.Nonempty) (hout : Tout.Nonempty) : Fin n → ℚ :=
  if toAverage I d Tin hin ≤ fromAverage I d Tout hout then fromSet d Tout hout
  else fun v => -toSet d Tin hin v

private theorem separation_neg {n : ℕ} (I : RationalInstance n) (a : Fin n → ℚ) :
    PotentialLayers.separation I (fun v => -a v) = PotentialLayers.separation I a := by
  unfold PotentialLayers.separation
  have ht : ∀ u v : Fin n,
      (I.weight u : ℚ) * I.weight v * max (-a v - -a u) 0 =
      (I.weight v : ℚ) * I.weight u * max (a u - a v) 0 := by
    intro u v
    rw [neg_sub_neg]
    ring
  simp_rw [ht]
  rw [Finset.sum_comm]

/-- A nonnegative potential zero on S gains at least mass(S) times its
 weighted average in product-demand separation. -/
theorem separation_lower {n : ℕ} (I : RationalInstance n) (a : Fin n → ℚ)
    (S : Finset (Fin n)) (ha : ∀ v, 0 ≤ a v) (hzero : ∀ v ∈ S, a v = 0) :
    mass I S * (∑ v, (I.weight v : ℚ) * a v) ≤ PotentialLayers.separation I a := by
  calc
    mass I S * (∑ v, (I.weight v : ℚ) * a v) =
        ∑ u ∈ S, ∑ v, (I.weight u : ℚ) * I.weight v * max (a v - a u) 0 := by
      unfold mass
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [hzero u hu, sub_zero, max_eq_left (ha v)]
      ring
    _ ≤ PotentialLayers.separation I a := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      intro u _ _
      exact Finset.sum_nonneg fun v _ =>
        mul_nonneg (mul_nonneg (NNRat.coe_nonneg _) (NNRat.coe_nonneg _)) (le_max_right _ _)

private theorem pair_linear_identity {n : ℕ} (w a b : Fin n → ℚ) (r : ℚ) :
    (∑ u, ∑ v, w u * w v * (a u + 2 * r + b v)) =
      (∑ v, w v) * (∑ u, w u * a u) + 2 * r * (∑ v, w v) ^ 2 +
        (∑ u, w u) * (∑ v, w v * b v) := by
  have ht : ∀ u v : Fin n, w u * w v * (a u + 2 * r + b v) =
      (w u * a u) * w v + (2 * r * w u) * w v + w u * (w v * b v) := by
    intro u v
    ring
  simp_rw [ht, Finset.sum_add_distrib]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- At radius 1/(4M²), at least half the metric separation comes from the
 two distances to/from the root balls. -/
theorem average_bound {n : ℕ} (I : RationalInstance n) (d : Distance n)
    (Tin Tout : Finset (Fin n)) (hin : Tin.Nonempty) (hout : Tout.Nonempty) (root : Fin n)
    (hM : 0 < total I) (hsep : 1 ≤ distanceSeparation I d)
    (htri : ∀ u v w, d u w ≤ d u v + d v w)
    (hinRadius : ∀ s ∈ Tin, d s root ≤ 1 / (4 * total I ^ 2))
    (houtRadius : ∀ t ∈ Tout, d root t ≤ 1 / (4 * total I ^ 2)) :
    (1 / 2 : ℚ) ≤ total I * toAverage I d Tin hin + total I * fromAverage I d Tout hout := by
  have hpair : distanceSeparation I d ≤
      ∑ u, ∑ v, (I.weight u : ℚ) * I.weight v *
        (toSet d Tin hin u + 2 * (1 / (4 * total I ^ 2)) + fromSet d Tout hout v) := by
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    exact mul_le_mul_of_nonneg_left
      (root_balls_bound d Tin Tout hin hout root _ htri hinRadius houtRadius u v)
      (mul_nonneg (NNRat.coe_nonneg _) (NNRat.coe_nonneg _))
  rw [pair_linear_identity] at hpair
  change distanceSeparation I d ≤ total I * toAverage I d Tin hin +
    2 * (1 / (4 * total I ^ 2)) * total I ^ 2 + total I * fromAverage I d Tout hout at hpair
  have hr : 2 * (1 / (4 * total I ^ 2)) * total I ^ 2 = (1 / 2 : ℚ) := by
    field_simp [ne_of_gt hM]
    norm_num
  linarith

/-- A pair of large root balls yields separation at least 1/6 in the actual
 rational potential chosen by comparison. -/
theorem potential_separation {n : ℕ} (I : RationalInstance n) (d : Distance n)
    (Tin Tout : Finset (Fin n)) (hin : Tin.Nonempty) (hout : Tout.Nonempty) (root : Fin n)
    (hM : 0 < total I) (hd : Nonnegative d) (hdiag : ∀ v, d v v = 0)
    (hsep : 1 ≤ distanceSeparation I d) (htri : ∀ u v w, d u w ≤ d u v + d v w)
    (hinRadius : ∀ s ∈ Tin, d s root ≤ 1 / (4 * total I ^ 2))
    (houtRadius : ∀ t ∈ Tout, d root t ≤ 1 / (4 * total I ^ 2))
    (hinMass : (2 / 3 : ℚ) * total I ≤ mass I Tin)
    (houtMass : (2 / 3 : ℚ) * total I ≤ mass I Tout) :
    (1 / 6 : ℚ) ≤ PotentialLayers.separation I (potential I d Tin Tout hin hout) := by
  have hab := average_bound I d Tin Tout hin hout root hM hsep htri hinRadius houtRadius
  have hfromNN : 0 ≤ fromAverage I d Tout hout :=
    Finset.sum_nonneg fun v _ => mul_nonneg (NNRat.coe_nonneg _) (from_nonnegative d Tout hout hd v)
  have htoNN : 0 ≤ toAverage I d Tin hin :=
    Finset.sum_nonneg fun v _ => mul_nonneg (NNRat.coe_nonneg _) (to_nonnegative d Tin hin hd v)
  unfold potential
  by_cases hcompare : toAverage I d Tin hin ≤ fromAverage I d Tout hout
  · rw [if_pos hcompare]
    have havg : (1 / 4 : ℚ) ≤ total I * fromAverage I d Tout hout := by
      have hle := mul_le_mul_of_nonneg_left hcompare hM.le
      linarith
    have hmass := mul_le_mul_of_nonneg_right houtMass hfromNN
    have hbound := separation_lower I (fromSet d Tout hout) Tout
      (from_nonnegative d Tout hout hd) (from_zero d Tout hout hd hdiag)
    change mass I Tout * fromAverage I d Tout hout ≤ _ at hbound
    nlinarith
  · rw [if_neg hcompare, separation_neg]
    have havg : (1 / 4 : ℚ) ≤ total I * toAverage I d Tin hin := by
      have hle := mul_le_mul_of_nonneg_left (le_of_not_ge hcompare) hM.le
      linarith
    have hmass := mul_le_mul_of_nonneg_right hinMass htoNN
    have hbound := separation_lower I (toSet d Tin hin) Tin
      (to_nonnegative d Tin hin hd) (to_zero d Tin hin hd hdiag)
    change mass I Tin * toAverage I d Tin hin ≤ _ at hbound
    nlinarith

/-- Both branches preserve the orientation required by directed arc costs. -/
theorem potential_lipschitz {n : ℕ} (I : RationalInstance n) (d : Distance n)
    (Tin Tout : Finset (Fin n)) (hin : Tin.Nonempty) (hout : Tout.Nonempty)
    (htri : ∀ u v w, d u w ≤ d u v + d v w) (u v : Fin n) :
    potential I d Tin Tout hin hout v - potential I d Tin Tout hin hout u ≤ d u v := by
  unfold potential
  split_ifs
  · exact from_lipschitz d Tout hout htri u v
  · exact negative_to_lipschitz d Tin hin htri u v

/-- The large-ball branch is an exact finite sweep, not a choice of a cut witness. -/
def round {n : ℕ} (I : RationalInstance n) (d : Distance n)
    (Tin Tout : Finset (Fin n)) (hin : Tin.Nonempty) (hout : Tout.Nonempty) : Option (Finset (Fin n)) :=
  PotentialLayers.round I (potential I d Tin Tout hin hout)

theorem round_correct {n : ℕ} (I : RationalInstance n) (d : Distance n)
    (Tin Tout : Finset (Fin n)) (hin : Tin.Nonempty) (hout : Tout.Nonempty) (root : Fin n)
    (hM : 0 < total I) (hd : Nonnegative d) (hdiag : ∀ v, d v v = 0)
    (hsep : 1 ≤ distanceSeparation I d) (htri : ∀ u v w, d u w ≤ d u v + d v w)
    (hinRadius : ∀ s ∈ Tin, d s root ≤ 1 / (4 * total I ^ 2))
    (houtRadius : ∀ t ∈ Tout, d root t ≤ 1 / (4 * total I ^ 2))
    (hinMass : (2 / 3 : ℚ) * total I ≤ mass I Tin)
    (houtMass : (2 / 3 : ℚ) * total I ≤ mass I Tout) :
    ∃ S, round I d Tin Tout hin hout = some S ∧ admissibleQ I S ∧
      ratioQ I S ≤ 6 * (∑ u, ∑ v, (I.capacity u v : ℚ) * d u v) := by
  have hsepBound := potential_separation I d Tin Tout hin hout root hM hd hdiag hsep htri
    hinRadius houtRadius hinMass houtMass
  have hsepPos : 0 < PotentialLayers.separation I (potential I d Tin Tout hin hout) := by linarith
  obtain ⟨S, hS, hvalid, hratio⟩ := PotentialLayers.round_spec I _ hsepPos
  refine ⟨S, hS, hvalid, hratio.trans ?_⟩
  have hcost := PotentialLayers.edgeCost_le I (potential I d Tin Tout hin hout) d hd
    (potential_lipschitz I d Tin Tout hin hout htri)
  have hW : 0 ≤ ∑ u, ∑ v, (I.capacity u v : ℚ) * d u v :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
      mul_nonneg (NNRat.coe_nonneg _) (hd u v)
  apply (div_le_iff₀ hsepPos).mpr
  nlinarith

end Lax455465Proofs.LargeBallRounding
