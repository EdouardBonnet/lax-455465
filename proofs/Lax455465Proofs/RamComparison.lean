/-
Generic RAM utilities reused from the registered LP development, Apache-2.0:
https://github.com/EdouardBonnet/lax-109476/tree/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864
Only namespaces and imports are adapted here. The LP solver itself is used
through its registered concept theorem, rather than its proof package.
-/
import Lax455465Proofs.RamRational

namespace Lax455465Proofs.RamComparison

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational

def leFlag (s₁ n₁ d₁ s₂ n₂ d₂ : ℕ) : ℕ :=
  if s₁ = s₂ then
    if s₁ = 1 then (if n₁ * d₂ < n₂ * d₁ then 0 else 1)
    else (if n₂ * d₁ < n₁ * d₂ then 0 else 1)
  else if s₁ = 1 then 1
  else if n₁ = 0 then (if n₂ = 0 then 1 else 0) else 0

theorem leFlag_le_one (s₁ n₁ d₁ s₂ n₂ d₂ : ℕ) : leFlag s₁ n₁ d₁ s₂ n₂ d₂ ≤ 1 := by
  unfold leFlag
  split_ifs <;> omega

/-- Comparison accepts either sign for zero, as the arithmetic routines do. -/
theorem leFlag_correct (s₁ n₁ d₁ s₂ n₂ d₂ : ℕ) (hs₁ : s₁ ≤ 1) (hs₂ : s₂ ≤ 1)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    leFlag s₁ n₁ d₁ s₂ n₂ d₂ = 1 ↔
      fractionValue s₁ n₁ d₁ ≤ fractionValue s₂ n₂ d₂ := by
  have hd₁q : (0 : ℚ) < d₁ := by exact_mod_cast hd₁
  have hd₂q : (0 : ℚ) < d₂ := by exact_mod_cast hd₂
  have hpos₁ : (0 : ℚ) ≤ (n₁ : ℚ) / d₁ := by positivity
  have hpos₂ : (0 : ℚ) ≤ (n₂ : ℚ) / d₂ := by positivity
  have hcross : (n₁ : ℚ) / d₁ ≤ (n₂ : ℚ) / d₂ ↔ n₁ * d₂ ≤ n₂ * d₁ := by
    rw [div_le_div_iff₀ hd₁q hd₂q]
    exact_mod_cast Iff.rfl
  have hcrossRev : (n₂ : ℚ) / d₂ ≤ (n₁ : ℚ) / d₁ ↔ n₂ * d₁ ≤ n₁ * d₂ := by
    rw [div_le_div_iff₀ hd₂q hd₁q]
    exact_mod_cast Iff.rfl
  have hzero : (n₁ : ℚ) / d₁ ≤ -((n₂ : ℚ) / d₂) ↔ n₁ = 0 ∧ n₂ = 0 := by
    constructor
    · intro h
      have hz₁ : (n₁ : ℚ) / d₁ = 0 := by linarith
      have hz₂ : (n₂ : ℚ) / d₂ = 0 := by linarith
      simpa [div_eq_zero_iff, ne_of_gt hd₁q, ne_of_gt hd₂q] using And.intro hz₁ hz₂
    · rintro ⟨rfl, rfl⟩; simp
  have hs₁cases : s₁ = 0 ∨ s₁ = 1 := by omega
  have hs₂cases : s₂ = 0 ∨ s₂ = 1 := by omega
  rcases hs₁cases with rfl | rfl <;> rcases hs₂cases with rfl | rfl
  · simp [leFlag, fractionValue, hcross]
  · simp [leFlag, fractionValue, neg_div, hzero]
    split_ifs <;> simp_all
  · simp [leFlag, fractionValue, neg_div]
    linarith
  · simp [leFlag, fractionValue, neg_div, hcrossRev]

def compareFraction : Com :=
  .seq (.assign "cmp.u" (.mul (.var "left.n") (.var "right.d")))
    (.seq (.assign "cmp.v" (.mul (.var "right.n") (.var "left.d")))
      (.ite (.eq (.var "left.s") (.var "right.s"))
        (.ite (.eq (.var "left.s") (.lit 1))
          (.ite (.lt (.var "cmp.u") (.var "cmp.v"))
            (.assign "cmp.le" (.lit 0)) (.assign "cmp.le" (.lit 1)))
          (.ite (.lt (.var "cmp.v") (.var "cmp.u"))
            (.assign "cmp.le" (.lit 0)) (.assign "cmp.le" (.lit 1))))
        (.ite (.eq (.var "left.s") (.lit 1)) (.assign "cmp.le" (.lit 1))
          (.ite (.eq (.var "left.n") (.lit 0))
            (.ite (.eq (.var "right.n") (.lit 0))
              (.assign "cmp.le" (.lit 1)) (.assign "cmp.le" (.lit 0)))
            (.assign "cmp.le" (.lit 0))))))

set_option maxHeartbeats 800000 in
theorem compareFraction_flag_spec (B M s₁ n₁ d₁ s₂ n₂ d₂ : ℕ)
    (hB : 2 * M ^ 2 + 3 < B) (hs₁ : s₁ ≤ 1) (hs₂ : s₂ ≤ 1)
    (hn₁ : n₁ ≤ M) (hd₁ : d₁ ≤ M) (hn₂ : n₂ ≤ M) (hd₂ : d₂ ≤ M) :
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) compareFraction
      (fun _ σ' => σ'.vars "cmp.le" = leFlag s₁ n₁ d₁ s₂ n₂ d₂) 40 := by
  have hM : M < B := by nlinarith
  have hn₁B := hn₁.trans_lt hM
  have hd₁B := hd₁.trans_lt hM
  have hn₂B := hn₂.trans_lt hM
  have hd₂B := hd₂.trans_lt hM
  have huB : n₁ * d₂ < B := (Nat.mul_le_mul hn₁ hd₂).trans_lt (by nlinarith)
  have hvB : n₂ * d₁ < B := (Nat.mul_le_mul hn₂ hd₁).trans_lt (by nlinarith)
  have h1 : 1 < B := by nlinarith
  have hs₁B := hs₁.trans_lt h1
  have hs₂B := hs₂.trans_lt h1
  rintro σ ⟨hσs₁, hσn₁, hσd₁, hσs₂, hσn₂, hσd₂⟩
  run_vcg
  all_goals simp_all [leFlag]

theorem compareFraction_spec (B M s₁ n₁ d₁ s₂ n₂ d₂ : ℕ)
    (hB : 2 * M ^ 2 + 3 < B) (hs₁ : s₁ ≤ 1) (hs₂ : s₂ ≤ 1)
    (hn₁ : n₁ ≤ M) (hd₁ : d₁ ≤ M) (hn₂ : n₂ ≤ M) (hd₂ : d₂ ≤ M)
    (hd₁pos : 0 < d₁) (hd₂pos : 0 < d₂) :
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) compareFraction
      (fun _ σ' => σ'.vars "cmp.le" ≤ 1 ∧
        (σ'.vars "cmp.le" = 1 ↔ fractionValue s₁ n₁ d₁ ≤ fractionValue s₂ n₂ d₂)) 40 := by
  apply (compareFraction_flag_spec B M s₁ n₁ d₁ s₂ n₂ d₂ hB hs₁ hs₂ hn₁ hd₁ hn₂ hd₂).post
  intro σ τ _ ht
  rw [ht]
  exact ⟨leFlag_le_one _ _ _ _ _ _, leFlag_correct _ _ _ _ _ _ hs₁ hs₂ hd₁pos hd₂pos⟩

end Lax455465Proofs.RamComparison
