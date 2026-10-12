import Lax455465Proofs.SetDistanceData
import Lax455465Proofs.ThresholdCutData

namespace Lax455465Proofs.LargePotentialData
open Lax455465.RationalEncoding LpInputSize
open scoped NNRat

def vector {n : ℕ} (toSet : Bool) (d : MetricMatrix.Matrix n) (S : Finset (Fin n)) (hS : S.Nonempty) : List ℚ≥0 :=
  List.ofFn (SetDistanceData.distance toSet d S hS)
def products {n : ℕ} (I : RationalInstance n) (toSet : Bool) (d : MetricMatrix.Matrix n)
    (S : Finset (Fin n)) (hS : S.Nonempty) : List ℚ≥0 := RamProductSum.products (List.ofFn I.weight) (vector toSet d S hS)
def average {n : ℕ} (I : RationalInstance n) (toSet : Bool) (d : MetricMatrix.Matrix n)
    (S : Finset (Fin n)) (hS : S.Nonempty) : ℚ≥0 := (products I toSet d S hS).sum

theorem coe_average {n : ℕ} (I : RationalInstance n) (toSet : Bool) (d : MetricMatrix.Matrix n)
    (S : Finset (Fin n)) (hS : S.Nonempty) : (average I toSet d S hS : ℚ)=
      if toSet then LargeBallRounding.toAverage I (MetricMatrix.rational d) S hS
      else LargeBallRounding.fromAverage I (MetricMatrix.rational d) S hS := by
  have he : products I toSet d S hS=List.ofFn (fun v => I.weight v*SetDistanceData.distance toSet d S hS v) := by
    apply List.ext_getElem
    · simp [products,RamProductSum.products]
    · intro i hi hj
      change (RamProductSum.products (List.ofFn I.weight) (vector toSet d S hS))[i]=_
      erw [RamProductSum.value_at (List.ofFn I.weight) (vector toSet d S hS) (by simp [vector]) i (by simpa using hj)]
      simp only [vector,List.getElem_ofFn]
  simp only [average,he,List.sum_ofFn,NNRat.cast_sum,NNRat.coe_mul,SetDistanceData.coe_distance]
  cases toSet <;> rfl

def reversed {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (Tin Tout : Finset (Fin n)) (hin : Tin.Nonempty) (hout : Tout.Nonempty) : Bool :=
  if average I true d Tin hin≤average I false d Tout hout then false else true
def values {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (Tin Tout : Finset (Fin n)) (hin : Tin.Nonempty) (hout : Tout.Nonempty) : Fin n → ℚ≥0 :=
  if reversed I d Tin Tout hin hout then SetDistanceData.distance true d Tin hin
    else SetDistanceData.distance false d Tout hout

theorem potential_eq {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (Tin Tout : Finset (Fin n)) (hin : Tin.Nonempty) (hout : Tout.Nonempty) :
    ThresholdCutData.potential (reversed I d Tin Tout hin hout) (values I d Tin Tout hin hout)=
      LargeBallRounding.potential I (MetricMatrix.rational d) Tin Tout hin hout := by
  have hc : average I true d Tin hin≤average I false d Tout hout ↔
      LargeBallRounding.toAverage I (MetricMatrix.rational d) Tin hin≤
        LargeBallRounding.fromAverage I (MetricMatrix.rational d) Tout hout := by
    rw [←NNRat.coe_le_coe,coe_average,coe_average]
    rfl
  funext v
  by_cases h : average I true d Tin hin≤average I false d Tout hout
  · simp [ThresholdCutData.potential,values,reversed,h,LargeBallRounding.potential,hc.mp h,SetDistanceData.coe_distance]
  · simp [ThresholdCutData.potential,values,reversed,h,LargeBallRounding.potential,not_congr hc |>.mp h,SetDistanceData.coe_distance]

def exponent (n w : ℕ) : ℕ := 2*w*(n+1)+n+1

structure Bounds {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (Tin Tout : Finset (Fin n)) (hin : Tin.Nonempty) (hout : Tout.Nonempty) (M : ℕ) : Prop where
  weights : ∀ v,Height M (I.weight v : ℚ)
  distances : ∀ u v,Height M (d u v : ℚ)
  fromProducts : ∀ q∈products I false d Tout hout,Height M (q : ℚ)
  toProducts : ∀ q∈products I true d Tin hin,Height M (q : ℚ)
  fromPrefix : ∀ i,Height M ((((products I false d Tout hout).take i).sum : ℚ≥0) : ℚ)
  toPrefix : ∀ i,Height M ((((products I true d Tin hin).take i).sum : ℚ≥0) : ℚ)

theorem bounds {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (Tin Tout : Finset (Fin n)) (hin : Tin.Nonempty) (hout : Tout.Nonempty) (w : ℕ)
    (hw : ∀ v,Height (2^w) (I.weight v : ℚ)) (hd : ∀ u v,Height (2^w) (d u v : ℚ)) :
    Bounds I d Tin Tout hin hout (2^(exponent n w)) := by
  have hdom : 2*w≤exponent n w := by dsimp [exponent]; nlinarith
  have hpow : 2^w≤2^(exponent n w) := Nat.pow_le_pow_right (by decide) (by omega)
  have hp (toSet : Bool) (S : Finset (Fin n)) (hS : S.Nonempty) :
      ∀ q∈products I toSet d S hS,Height (2^(2*w)) (q : ℚ) := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hq
    have hi' : i<n := by simpa [products,RamProductSum.products] using hi
    change Height (2^(2*w)) ((RamProductSum.products (List.ofFn I.weight) (vector toSet d S hS))[i] : ℚ)
    erw [RamProductSum.value_at (List.ofFn I.weight) (vector toSet d S hS) (by simp [vector]) i (by simpa using hi')]
    simp only [vector,List.getElem_ofFn,NNRat.coe_mul]
    have hh := height_mul (hw ⟨i,hi'⟩) (SetDistanceData.height toSet d S hS (2^w) hd ⟨i,hi'⟩)
    simpa only [←Nat.pow_add,two_mul] using hh
  have hprod (toSet : Bool) (S : Finset (Fin n)) (hS : S.Nonempty) :
      ∀ q∈products I toSet d S hS,Height (2^(exponent n w)) (q : ℚ) :=
    fun q hq => height_mono (hp toSet S hS q hq) (Nat.pow_le_pow_right (by decide) hdom)
  have hprefix (toSet : Bool) (S : Finset (Fin n)) (hS : S.Nonempty) (i : ℕ) :
      Height (2^(exponent n w)) ((((products I toSet d S hS).take i).sum : ℚ≥0) : ℚ) := by
    have hh := RationalSumHeight.prefix_dyadic_height (products I toSet d S hS) (2*w)
      (fun q hq => RamRegionContext.num_bound (hp toSet S hS q hq))
      (fun q hq => RamRegionContext.den_bound (hp toSet S hS q hq)) i
    simpa only [products,RamProductSum.products,List.length_ofFn,exponent] using hh
  exact ⟨fun v => height_mono (hw v) hpow,fun u v => height_mono (hd u v) hpow,
    hprod false Tout hout,hprod true Tin hin,hprefix false Tout hout,hprefix true Tin hin⟩

end Lax455465Proofs.LargePotentialData
