/-
Generic RAM utilities reused from the registered LP development, Apache-2.0:
https://github.com/EdouardBonnet/lax-109476/tree/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864
Only namespaces and imports are adapted here. The LP solver itself is used
through its registered concept theorem, rather than its proof package.
-/
import Lax455465Proofs.RamArithmetic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field

namespace Lax455465Proofs.RamRational

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamArithmetic

def fractionValue (s n d : ℕ) : ℚ := if s = 1 then -(n : ℚ) / d else (n : ℚ) / d

theorem fractionValue_reduce (s n d : ℕ) :
    fractionValue s (n / Nat.gcd n d) (d / Nat.gcd n d) = fractionValue s n d := by
  have h : ((n / Nat.gcd n d : ℕ) : ℚ) / ((d / Nat.gcd n d : ℕ) : ℚ) = (n : ℚ) / d :=
    Nat.cast_div_div_div_cancel_right (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
  unfold fractionValue
  split_ifs
  · simpa only [neg_div] using congrArg Neg.neg h
  · exact h

theorem normalizeFraction_signed_spec (B s n d : ℕ) (hn : n < B) (hd : d < B) (hdpos : 0 < d) :
    Spec B (fun σ => σ.vars "rat.n" = n ∧ σ.vars "rat.d" = d ∧ σ.vars "rat.s" = s)
      normalizeFraction (fun _ σ' => σ'.vars "rat.n" = n / Nat.gcd n d ∧
        σ'.vars "rat.d" = d / Nat.gcd n d ∧ σ'.vars "rat.s" = s) (36 * d.size + 16) := by
  rintro σ ⟨hσn, hσd, hσs⟩
  obtain ⟨τ, hr, hτn, hτd⟩ := normalizeFraction_spec B n d hn hd hdpos σ ⟨hσn, hσd⟩
  have hτs := hr.frame_var "rat.s" (by decide)
  exact ⟨τ, hr, hτn, hτd, hτs.trans hσs⟩

theorem fractionValue_num_den (s n d : ℕ) (hd : 0 < d) :
    (fractionValue s n d).num.natAbs = n / Nat.gcd n d ∧
      (fractionValue s n d).den = d / Nat.gcd n d := by
  have h : (((n : ℚ) / d).num.natAbs = n / Nat.gcd n d) ∧
      ((n : ℚ) / d).den = d / Nat.gcd n d := by
    have he : (n : ℚ) / d = mkRat (n : ℤ) d := by simp [Rat.mkRat_eq_div]
    rw [he]
    simp [Rat.num_mkRat, Rat.den_mkRat, ne_of_gt hd,
      Int.natAbs_ediv_of_nonneg (by positivity : (0 : ℤ) ≤ n), Nat.gcd_comm]
  unfold fractionValue
  split_ifs
  · simpa only [neg_div, Rat.neg_num, Rat.neg_den, Int.natAbs_neg] using h
  · exact h

def FractionOutput (q : ℚ) (σ : Env) : Prop :=
  fractionValue (σ.vars "rat.s") (σ.vars "rat.n") (σ.vars "rat.d") = q ∧
    σ.vars "rat.n" = q.num.natAbs ∧ σ.vars "rat.d" = q.den ∧ σ.vars "rat.s" ≤ 1

theorem normalizeFraction_output_spec (B s n d : ℕ) (hs : s ≤ 1)
    (hn : n < B) (hd : d < B) (hdpos : 0 < d) :
    Spec B (fun σ => σ.vars "rat.n" = n ∧ σ.vars "rat.d" = d ∧ σ.vars "rat.s" = s)
      normalizeFraction (fun _ σ' => FractionOutput (fractionValue s n d) σ')
      (36 * d.size + 16) := by
  apply (normalizeFraction_signed_spec B s n d hn hd hdpos).post
  rintro σ τ _ ⟨hτn, hτd, hτs⟩
  obtain ⟨hnum, hden⟩ := fractionValue_num_den s n d hdpos
  exact ⟨by rw [hτs, hτn, hτd]; exact fractionValue_reduce s n d,
    hτn.trans hnum.symm, hτd.trans hden.symm, hτs ▸ hs⟩

theorem fractionValue_inv (s n d : ℕ) : fractionValue s d n = (fractionValue s n d)⁻¹ := by
  unfold fractionValue
  split_ifs <;> simp [inv_div, neg_div]

def invertFraction : Com :=
  .ite (.eq (.var "left.n") (.lit 0))
    (.seq (.assign "rat.n" (.lit 0))
      (.seq (.assign "rat.d" (.lit 1)) (.assign "rat.s" (.lit 0))))
    (.seq (.assign "rat.n" (.var "left.d"))
      (.seq (.assign "rat.d" (.var "left.n"))
        (.seq (.assign "rat.s" (.var "left.s")) normalizeFraction)))

theorem invertFraction_spec (B s n d : ℕ) (h1 : 1 < B) (hs : s ≤ 1)
    (hn : n < B) (hd : d < B) :
    Spec B (fun σ => σ.vars "left.s" = s ∧ σ.vars "left.n" = n ∧ σ.vars "left.d" = d)
      invertFraction (fun _ σ' => FractionOutput (fractionValue s n d)⁻¹ σ')
      (36 * n.size + 40) := by
  have hsB := hs.trans_lt h1
  by_cases hz : n = 0
  · subst n
    have hzero : Spec B (fun _ => True)
        (.seq (.assign "rat.n" (.lit 0))
          (.seq (.assign "rat.d" (.lit 1)) (.assign "rat.s" (.lit 0))))
        (fun _ σ' => FractionOutput 0 σ') 6 := by
      run_vcg
      all_goals simp [FractionOutput, fractionValue]
    rintro σ ⟨hσs, hσn, hσd⟩
    have hc : (Cond.eq (.var "left.n") (.lit 0)).evalB B σ = some true := by
      rw [evalB_condEq (evalB_var (hσn ▸ hn)) (evalB_lit (by omega)), hσn]
      rfl
    obtain ⟨τ, hr, hτ⟩ := hzero σ True.intro
    exact ⟨τ, (Run.ite_true hc hr).mono (by simp [Nat.size]),
      by simpa [fractionValue] using hτ⟩
  · have hnorm := normalizeFraction_output_spec B s d n hs hd hn (Nat.pos_of_ne_zero hz)
    have hv := fractionValue_inv s n d
    run_vcg [hnorm]
    all_goals simp_all

def fractionInputs (s₁ n₁ d₁ s₂ n₂ d₂ : ℕ) (σ : Env) : Prop :=
  σ.vars "left.s" = s₁ ∧ σ.vars "left.n" = n₁ ∧ σ.vars "left.d" = d₁ ∧
    σ.vars "right.s" = s₂ ∧ σ.vars "right.n" = n₂ ∧ σ.vars "right.d" = d₂

def multiplyFraction : Com :=
  .seq (.assign "rat.n" (.mul (.var "left.n") (.var "right.n")))
    (.seq (.assign "rat.d" (.mul (.var "left.d") (.var "right.d")))
      (.seq (.ite (.eq (.var "left.s") (.var "right.s"))
        (.assign "rat.s" (.lit 0)) (.assign "rat.s" (.lit 1))) normalizeFraction))

theorem multiplyFraction_spec (B M s₁ n₁ d₁ s₂ n₂ d₂ : ℕ)
    (hB : 2 * M ^ 2 + 3 < B) (hs₁ : s₁ ≤ 1) (hs₂ : s₂ ≤ 1)
    (hn₁ : n₁ ≤ M) (hd₁ : d₁ ≤ M) (hn₂ : n₂ ≤ M) (hd₂ : d₂ ≤ M)
    (hd₁pos : 0 < d₁) (hd₂pos : 0 < d₂) :
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) multiplyFraction
      (fun _ σ' => FractionOutput (fractionValue s₁ n₁ d₁ * fractionValue s₂ n₂ d₂) σ')
      (36 * (d₁ * d₂).size + 64) := by
  have hM : M < B := by nlinarith
  have hn₁B := hn₁.trans_lt hM
  have hd₁B := hd₁.trans_lt hM
  have hn₂B := hn₂.trans_lt hM
  have hd₂B := hd₂.trans_lt hM
  have hnn : n₁ * n₂ < B := (Nat.mul_le_mul hn₁ hn₂).trans_lt (by nlinarith)
  have hdd : d₁ * d₂ < B := (Nat.mul_le_mul hd₁ hd₂).trans_lt (by nlinarith)
  have h1 : 1 < B := by nlinarith
  have hs₁B : s₁ < B := hs₁.trans_lt h1
  have hs₂B : s₂ < B := hs₂.trans_lt h1
  have hmul : fractionValue (if s₁ = s₂ then 0 else 1) (n₁ * n₂) (d₁ * d₂) =
      fractionValue s₁ n₁ d₁ * fractionValue s₂ n₂ d₂ := by
    have hs₁cases : s₁ = 0 ∨ s₁ = 1 := by omega
    have hs₂cases : s₂ = 0 ∨ s₂ = 1 := by omega
    rcases hs₁cases with rfl | rfl <;> rcases hs₂cases with rfl | rfl <;>
      norm_num [fractionValue, Nat.cast_mul] <;> ring
  have hn := normalizeFraction_output_spec B (if s₁ = s₂ then 0 else 1)
    (n₁ * n₂) (d₁ * d₂) (by split_ifs <;> omega) hnn hdd
    (Nat.mul_pos hd₁pos hd₂pos)
  rintro σ ⟨hσs₁, hσn₁, hσd₁, hσs₂, hσn₂, hσd₂⟩
  run_vcg [hn]
  all_goals simp_all

def sumNumerator (s₁ n₁ d₁ s₂ n₂ d₂ : ℕ) : ℕ :=
  if s₁ = s₂ then n₁ * d₂ + n₂ * d₁
  else if n₁ * d₂ < n₂ * d₁ then n₂ * d₁ - n₁ * d₂ else n₁ * d₂ - n₂ * d₁

def sumSign (s₁ n₁ d₁ s₂ n₂ d₂ : ℕ) : ℕ :=
  if s₁ = s₂ then s₁ else if n₁ * d₂ < n₂ * d₁ then s₂ else s₁

theorem fractionValue_sum (s₁ n₁ d₁ s₂ n₂ d₂ : ℕ) (hs₁ : s₁ ≤ 1) (hs₂ : s₂ ≤ 1)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    fractionValue (sumSign s₁ n₁ d₁ s₂ n₂ d₂) (sumNumerator s₁ n₁ d₁ s₂ n₂ d₂) (d₁ * d₂) =
      fractionValue s₁ n₁ d₁ + fractionValue s₂ n₂ d₂ := by
  have hd₁q : (d₁ : ℚ) ≠ 0 := by positivity
  have hd₂q : (d₂ : ℚ) ≠ 0 := by positivity
  have hs₁cases : s₁ = 0 ∨ s₁ = 1 := by omega
  have hs₂cases : s₂ = 0 ∨ s₂ = 1 := by omega
  rcases hs₁cases with rfl | rfl <;> rcases hs₂cases with rfl | rfl <;>
    by_cases h : n₁ * d₂ < n₂ * d₁
  all_goals first
    | (have hu : n₁ * d₂ ≤ n₂ * d₁ := by omega
       simp [sumSign, sumNumerator, fractionValue, h, Nat.cast_sub hu]
       field_simp <;> ring)
    | (have hv : n₂ * d₁ ≤ n₁ * d₂ := by omega
       simp [sumSign, sumNumerator, fractionValue, h, Nat.cast_sub hv]
       field_simp <;> ring)

def addFraction : Com :=
  .seq (.assign "sum.u" (.mul (.var "left.n") (.var "right.d")))
    (.seq (.assign "sum.v" (.mul (.var "right.n") (.var "left.d")))
      (.seq (.assign "rat.d" (.mul (.var "left.d") (.var "right.d")))
        (.seq (.ite (.eq (.var "left.s") (.var "right.s"))
          (.seq (.assign "rat.n" (.add (.var "sum.u") (.var "sum.v")))
            (.assign "rat.s" (.var "left.s")))
          (.ite (.lt (.var "sum.u") (.var "sum.v"))
            (.seq (.assign "rat.n" (.sub (.var "sum.v") (.var "sum.u")))
              (.assign "rat.s" (.var "right.s")))
            (.seq (.assign "rat.n" (.sub (.var "sum.u") (.var "sum.v")))
              (.assign "rat.s" (.var "left.s"))))) normalizeFraction)))

set_option maxHeartbeats 800000 in
theorem addFraction_spec (B M s₁ n₁ d₁ s₂ n₂ d₂ : ℕ)
    (hB : 2 * M ^ 2 + 3 < B) (hs₁ : s₁ ≤ 1) (hs₂ : s₂ ≤ 1)
    (hn₁ : n₁ ≤ M) (hd₁ : d₁ ≤ M) (hn₂ : n₂ ≤ M) (hd₂ : d₂ ≤ M)
    (hd₁pos : 0 < d₁) (hd₂pos : 0 < d₂) :
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) addFraction
      (fun _ σ' => FractionOutput (fractionValue s₁ n₁ d₁ + fractionValue s₂ n₂ d₂) σ')
      (36 * (d₁ * d₂).size + 96) := by
  have hM : M < B := by nlinarith
  have hn₁B := hn₁.trans_lt hM
  have hd₁B := hd₁.trans_lt hM
  have hn₂B := hn₂.trans_lt hM
  have hd₂B := hd₂.trans_lt hM
  have hu : n₁ * d₂ ≤ M * M := Nat.mul_le_mul hn₁ hd₂
  have hv : n₂ * d₁ ≤ M * M := Nat.mul_le_mul hn₂ hd₁
  have huB : n₁ * d₂ < B := hu.trans_lt (by nlinarith)
  have hvB : n₂ * d₁ < B := hv.trans_lt (by nlinarith)
  have huvB : n₁ * d₂ + n₂ * d₁ < B := by nlinarith
  have hdd : d₁ * d₂ < B := (Nat.mul_le_mul hd₁ hd₂).trans_lt (by nlinarith)
  have hnB : sumNumerator s₁ n₁ d₁ s₂ n₂ d₂ < B := by
    unfold sumNumerator
    split_ifs <;> omega
  have h1 : 1 < B := by nlinarith
  have hs₁B := hs₁.trans_lt h1
  have hs₂B := hs₂.trans_lt h1
  have hss : sumSign s₁ n₁ d₁ s₂ n₂ d₂ ≤ 1 := by unfold sumSign; split_ifs <;> omega
  have hn := normalizeFraction_output_spec B (sumSign s₁ n₁ d₁ s₂ n₂ d₂)
    (sumNumerator s₁ n₁ d₁ s₂ n₂ d₂) (d₁ * d₂) hss hnB hdd
    (Nat.mul_pos hd₁pos hd₂pos)
  have hsum := fractionValue_sum s₁ n₁ d₁ s₂ n₂ d₂ hs₁ hs₂ hd₁pos hd₂pos
  rintro σ ⟨hσs₁, hσn₁, hσd₁, hσs₂, hσn₂, hσd₂⟩
  run_vcg [hn]
  all_goals simp_all [sumNumerator, sumSign]
  all_goals try omega

end Lax455465Proofs.RamRational
