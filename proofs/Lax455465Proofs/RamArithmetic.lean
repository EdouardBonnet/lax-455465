/-
Generic RAM utilities reused from the registered LP development, Apache-2.0:
https://github.com/EdouardBonnet/lax-109476/tree/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864
Only namespaces and imports are adapted here. The LP solver itself is used
through its registered concept theorem, rather than its proof package.
-/
import Lax808846Proofs.Tactic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.GCD.Basic

namespace Lax455465Proofs.RamArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- One Euclidean step uses only operations compiled to the registered RAM. -/
def gcdStep : Com :=
  .seq (.assign "gcd.t" (.sub (.var "gcd.a")
    (.mul (.div (.var "gcd.a") (.var "gcd.b")) (.var "gcd.b"))))
    (.seq (.assign "gcd.a" (.var "gcd.b")) (.assign "gcd.b" (.var "gcd.t")))

theorem gcdStep_spec (B a b : ℕ) (ha : a < B) (hb : b < B) :
    Spec B (fun σ => σ.vars "gcd.a" = a ∧ σ.vars "gcd.b" = b) gcdStep
      (fun _ σ' => σ'.vars "gcd.a" = b ∧ σ'.vars "gcd.b" = a % b) 12 := by
  rintro σ ⟨hsa, hsb⟩
  have hdiv : a / b < B := (Nat.div_le_self a b).trans_lt ha
  have hmul : a / b * b < B := (Nat.div_mul_le_self a b).trans_lt ha
  have hsub : a - a / b * b < B := (Nat.sub_le _ _).trans_lt ha
  run_vcg
  all_goals simp_all [Nat.mod_def, Nat.mul_comm]

def gcdDoubleStep : Com :=
  .seq gcdStep (.ite (.lt (.lit 0) (.var "gcd.b")) gcdStep .skip)

def gcdLoop : Com := .while (.lt (.lit 0) (.var "gcd.b")) gcdDoubleStep

/-- Two nonterminal Euclidean steps halve the divisor. -/
theorem remainder_half (d r : ℕ) (hr : 0 < r) (hrd : r < d) : d % r ≤ d / 2 := by
  by_cases h : r ≤ d / 2
  · exact (Nat.mod_lt d hr).le.trans h
  · rw [Nat.mod_eq_sub_mod hrd.le, Nat.mod_eq_of_lt (by omega)]
    omega

theorem size_half_lt (b : ℕ) (hb : 0 < b) : (b / 2).size < b.size := by
  have hs : 0 < b.size := Nat.size_pos.mpr hb
  have hp : b < 2 ^ b.size := Nat.lt_size_self b
  have he : 2 ^ b.size = 2 * 2 ^ (b.size - 1) := by
    calc
      _ = 2 ^ ((b.size - 1) + 1) := congrArg (fun k => 2 ^ k) (by omega)
      _ = _ := by rw [pow_succ]; omega
  have hhalf : b / 2 < 2 ^ (b.size - 1) := by omega
  have h := Nat.size_le.mpr hhalf
  omega

theorem gcd_swap_mod (a b : ℕ) : Nat.gcd b (a % b) = Nat.gcd a b := by
  rw [Nat.gcd_comm b _, ← Nat.gcd_rec, Nat.gcd_comm]

theorem gcdDoubleStep_spec (B M a b : ℕ) (hM : M < B)
    (ha : a ≤ M) (hb : b ≤ M) (hbpos : 0 < b) :
    Spec B (fun σ => σ.vars "gcd.a" = a ∧ σ.vars "gcd.b" = b) gcdDoubleStep
      (fun _ σ' => σ'.vars "gcd.a" ≤ M ∧ σ'.vars "gcd.b" ≤ M ∧
        Nat.gcd (σ'.vars "gcd.a") (σ'.vars "gcd.b") = Nat.gcd a b ∧
        (σ'.vars "gcd.b").size < b.size) 32 := by
  intro σ hσ
  obtain ⟨τ, hrun, hτa, hτb⟩ := (gcdStep_spec B a b (ha.trans_lt hM) (hb.trans_lt hM)) σ hσ
  have hrlt : a % b < b := Nat.mod_lt a hbpos
  have hrB : a % b < B := hrlt.trans (hb.trans_lt hM)
  have h0B : 0 < B := (Nat.zero_le M).trans_lt hM
  by_cases hr0 : a % b = 0
  · have hc : (Cond.lt (.lit 0) (.var "gcd.b")).evalB B τ = some false := by
      rw [evalB_condLt (evalB_lit h0B) (evalB_var (hτb ▸ hrB)), hτb, hr0]
      rfl
    refine ⟨τ, (hrun.seq (Run.ite_false hc Run.skip)).mono (by norm_num), ?_⟩
    dsimp only
    rw [hτa, hτb]
    refine ⟨hb, hrlt.le.trans hb, gcd_swap_mod a b, ?_⟩
    rw [hr0]
    exact Nat.size_pos.mpr hbpos
  · have hrpos : 0 < a % b := Nat.pos_of_ne_zero hr0
    have hc : (Cond.lt (.lit 0) (.var "gcd.b")).evalB B τ = some true := by
      rw [evalB_condLt (evalB_lit h0B) (evalB_var (hτb ▸ hrB)), hτb]
      simp [hrpos]
    obtain ⟨ν, hrν, hνa, hνb⟩ :=
      (gcdStep_spec B b (a % b) (hb.trans_lt hM) hrB) τ ⟨hτa, hτb⟩
    refine ⟨ν, (hrun.seq (Run.ite_true hc hrν)).mono (by norm_num), ?_⟩
    dsimp only
    rw [hνa, hνb]
    refine ⟨hrlt.le.trans hb, (Nat.mod_lt b hrpos).le.trans (hrlt.le.trans hb),
      (gcd_swap_mod b (a % b)).trans (gcd_swap_mod a b), ?_⟩
    exact (Nat.size_le_size (remainder_half b (a % b) hrpos hrlt)).trans_lt
      (size_half_lt b hbpos)

/-- Exact GCD in a number of structured instructions linear in the divisor's
bit size; every intermediate stays below the supplied word bound. -/
theorem gcdLoop_spec (B M a b : ℕ) (hM : M < B) (ha : a ≤ M) (hb : b ≤ M) :
    Spec B (fun σ => σ.vars "gcd.a" = a ∧ σ.vars "gcd.b" = b) gcdLoop
      (fun _ σ' => σ'.vars "gcd.a" = Nat.gcd a b ∧ σ'.vars "gcd.b" = 0)
      (36 * b.size + 4) := by
  let I := fun σ : Env => σ.vars "gcd.a" ≤ M ∧ σ.vars "gcd.b" ≤ M ∧
    Nat.gcd (σ.vars "gcd.a") (σ.vars "gcd.b") = Nat.gcd a b
  have hloop : Spec B (fun σ => σ.vars "gcd.a" = a ∧ σ.vars "gcd.b" = b) gcdLoop
      (fun _ σ' => I σ' ∧
        (Cond.lt (.lit 0) (.var "gcd.b")).evalB B σ' = some false)
      (36 * b.size + 4) := by
    apply Spec.while_count I (fun σ => (σ.vars "gcd.b").size) 32
    · intro σ hI
      exact ⟨_, evalB_condLt (evalB_lit ((Nat.zero_le M).trans_lt hM))
        (evalB_var (hI.2.1.trans_lt hM))⟩
    · rintro σ ⟨hI, hc⟩
      have hbpos : 0 < σ.vars "gcd.b" := by
        rw [evalB_condLt (evalB_lit ((Nat.zero_le M).trans_lt hM))
          (evalB_var (hI.2.1.trans_lt hM))] at hc
        simpa using hc
      obtain ⟨τ, hr, hτa, hτb, hτg, hτs⟩ :=
        gcdDoubleStep_spec B M _ _ hM hI.1 hI.2.1 hbpos σ ⟨rfl, rfl⟩
      exact ⟨τ, hr, ⟨hτa, hτb, hτg.trans hI.2.2⟩, hτs⟩
    · rintro σ ⟨hσa, hσb⟩
      exact ⟨hσa ▸ ha, hσb ▸ hb, by rw [hσa, hσb]⟩
    · rintro σ ⟨_, hσb⟩
      simp [hσb]
  apply hloop.post
  rintro σ τ _ ⟨hI, hc⟩
  have hb0 : τ.vars "gcd.b" = 0 := by
    rw [evalB_condLt (evalB_lit ((Nat.zero_le M).trans_lt hM))
      (evalB_var (hI.2.1.trans_lt hM))] at hc
    simpa using hc
  exact ⟨by simpa [hb0] using hI.2.2, hb0⟩

/-- Reduce an unsigned numerator and positive denominator in place. The sign
is held separately by the rational representation and is left untouched. -/
def normalizeFraction : Com :=
  .seq (.assign "gcd.a" (.var "rat.n"))
    (.seq (.assign "gcd.b" (.var "rat.d"))
      (.seq gcdLoop
        (.seq (.assign "rat.n" (.div (.var "rat.n") (.var "gcd.a")))
          (.assign "rat.d" (.div (.var "rat.d") (.var "gcd.a"))))))

theorem normalizeFraction_spec (B n d : ℕ) (hn : n < B) (hd : d < B) (hdpos : 0 < d) :
    Spec B (fun σ => σ.vars "rat.n" = n ∧ σ.vars "rat.d" = d) normalizeFraction
      (fun _ σ' => σ'.vars "rat.n" = n / Nat.gcd n d ∧
        σ'.vars "rat.d" = d / Nat.gcd n d) (36 * d.size + 16) := by
  have hM : max n d < B := max_lt hn hd
  have hg : Nat.gcd n d < B := (Nat.gcd_le_right n hdpos).trans_lt hd
  have hnDiv : n / Nat.gcd n d < B := (Nat.div_le_self _ _).trans_lt hn
  have hdDiv : d / Nat.gcd n d < B := (Nat.div_le_self _ _).trans_lt hd
  have hs := (gcdLoop_spec B (max n d) n d hM (le_max_left _ _) (le_max_right _ _)).frame
  rintro σ ⟨hσn, hσd⟩
  run_vcg [hs]
  all_goals simp_all [gcdLoop, gcdDoubleStep, gcdStep, Com.wvars]

end Lax455465Proofs.RamArithmetic
