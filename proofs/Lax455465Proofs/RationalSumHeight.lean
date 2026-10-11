import Lax455465Proofs.MetricHeight

namespace Lax455465Proofs.RationalSumHeight

open scoped NNRat

/-- A shared denominator for every partial sum of an unsigned vector. -/
def denominator (qs : List ℚ≥0) : ℕ := (qs.map NNRat.den).prod

theorem denominator_pos (qs : List ℚ≥0) : 0 < denominator qs := by
  induction qs with
  | nil => simp [denominator]
  | cons a qs ih => simpa only [denominator,List.map_cons,List.prod_cons] using Nat.mul_pos a.den_pos ih

theorem denominator_dvd (qs : List ℚ≥0) (q : ℚ≥0) (hq : q ∈ qs) :
    q.den ∣ denominator qs := by
  exact List.dvd_prod (List.mem_map.mpr ⟨q,hq,rfl⟩)

theorem sum_denominator (qs : List ℚ≥0) (D : ℕ) (h : ∀ q ∈ qs, q.den ∣ D) :
    ((qs.sum : ℚ≥0) : ℚ).den ∣ D := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    simp only [List.sum_cons,NNRat.coe_add]
    exact (Rat.add_den_dvd_lcm _ _).trans (Nat.lcm_dvd (h q (by simp))
      (ih (fun a ha => h a (by simp [ha]))))

theorem sum_value (qs : List ℚ≥0) (M : ℕ) (hnum : ∀ q ∈ qs, q.num ≤ M) :
    ((qs.sum : ℚ≥0) : ℚ) ≤ qs.length*M := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    have hq := MetricHeight.value_bound (q : ℚ) q.coe_nonneg M (by simpa only [NNRat.natAbs_num_coe] using hnum q (by simp))
    have hi := ih (fun a ha => hnum a (by simp [ha]))
    simp only [List.sum_cons,NNRat.coe_add,List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

/-- All prefixes use one denominator lattice and a linear value bound. -/
theorem prefix_height (qs : List ℚ≥0) (M : ℕ) (hM : 1 ≤ M)
    (hnum : ∀ q ∈ qs, q.num ≤ M) (k : ℕ) :
    LpInputSize.Height ((qs.length+1)*M*denominator qs) (((qs.take k).sum : ℚ≥0) : ℚ) := by
  apply MetricHeight.height_of_denominator _ (NNRat.coe_nonneg _) ((qs.length+1)*M) (denominator qs)
    (by nlinarith) (denominator_pos qs)
    (sum_denominator (qs.take k) _ (fun q hq => denominator_dvd qs q (List.mem_of_mem_take hq)))
  have hval := sum_value (qs.take k) M (fun q hq => hnum q (List.mem_of_mem_take hq))
  have hlen : (qs.take k).length ≤ qs.length+1 := by simp only [List.length_take]; omega
  push_cast
  exact hval.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) (Nat.cast_nonneg M))

theorem denominator_bound (qs : List ℚ≥0) (w : ℕ) (hden : ∀ q ∈ qs, q.den ≤ 2^w) :
    denominator qs ≤ 2^(w*qs.length) := by
  induction qs with
  | nil => simp [denominator]
  | cons q qs ih =>
    have hd := hden q (by simp)
    have hi := ih (fun a ha => hden a (by simp [ha]))
    calc
      denominator (q::qs) = q.den*denominator qs := by simp [denominator]
      _ ≤ 2^w*2^(w*qs.length) := Nat.mul_le_mul hd hi
      _ = 2^(w*(q::qs).length) := by simp only [List.length_cons]; rw [←Nat.pow_add]; congr 1; ring

/-- Summing a polynomial-length rational list has polynomial bit height;
bounding each addition separately would lose this denominator invariant. -/
theorem prefix_word_height (qs : List ℚ≥0) (w : ℕ)
    (hnum : ∀ q ∈ qs, q.num ≤ 2^w) (hden : ∀ q ∈ qs, q.den ≤ 2^w) (k : ℕ) :
    LpInputSize.Height ((qs.length+1)*2^(w*(qs.length+1))) (((qs.take k).sum : ℚ≥0) : ℚ) := by
  apply LpInputSize.height_mono (prefix_height qs (2^w) (by have := Nat.two_pow_pos w; omega) hnum k)
  calc
    (qs.length+1)*2^w*denominator qs ≤ (qs.length+1)*2^w*2^(w*qs.length) :=
      Nat.mul_le_mul_left _ (denominator_bound qs w hden)
    _ = _ := by rw [Nat.mul_assoc,←Nat.pow_add]; congr 2; ring

/-- A dyadic form convenient for uniform native word-width budgets. -/
theorem prefix_dyadic_height (qs : List ℚ≥0) (w : ℕ)
    (hnum : ∀ q ∈ qs, q.num ≤ 2^w) (hden : ∀ q ∈ qs, q.den ≤ 2^w) (k : ℕ) :
    LpInputSize.Height (2^(w*(qs.length+1)+qs.length+1)) (((qs.take k).sum : ℚ≥0) : ℚ) := by
  apply LpInputSize.height_mono (prefix_word_height qs w hnum hden k)
  calc
    (qs.length+1)*2^(w*(qs.length+1)) ≤ 2^(qs.length+1)*2^(w*(qs.length+1)) :=
      Nat.mul_le_mul_right _ (Nat.lt_two_pow_self.le)
    _ = _ := by rw [←Nat.pow_add]; congr 1; omega

end Lax455465Proofs.RationalSumHeight
