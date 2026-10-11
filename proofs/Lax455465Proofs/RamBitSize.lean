import Lax455465Proofs.WordSize
import Lax455465Proofs.RamFrames
import Lax455465Proofs.RamVirtualState

namespace Lax455465Proofs.RamBitSize

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def wordStep : Com := .seq (.assign "size.value" (.div (.var "size.value") (.lit 2)))
  (.assign "size.count" (.add (.var "size.count") (.lit 1)))

def wordLoop : Com := .while (.lt (.lit 0) (.var "size.value")) wordStep

def word : Com := .seq (.assign "size.count" (.lit 0)) wordLoop

/-- Count the canonical bits of a word by exact integer halving. This is
independent of the host word width and has linear cost in the input bits. -/
theorem word_spec (B v : ℕ) (h2 : 2 < B) (hv : v < B) :
    Spec B (fun σ => σ.vars "size.value" = v) word
      (fun _ τ => τ.vars "size.value" = 0 ∧ τ.vars "size.count" = v.size) (12 * v.size + 6) := by
  let I := fun σ : Env => σ.vars "size.value" ≤ v ∧
    σ.vars "size.count" + (σ.vars "size.value").size = v.size
  have hs : v.size ≤ v := Nat.size_le.mpr (Nat.lt_two_pow_self)
  have hlo : Spec B (fun σ => σ.vars "size.value" = v ∧ σ.vars "size.count" = 0) wordLoop
      (fun _ τ => I τ ∧ (Cond.lt (.lit 0) (.var "size.value")).evalB B τ = some false)
      (12 * v.size + 4) := by
    apply Spec.while_count I (fun σ => (σ.vars "size.value").size) 8
    · intro σ hI
      exact ⟨_, evalB_condLt (evalB_lit (by omega)) (evalB_var (hI.1.trans_lt hv))⟩
    · rintro σ ⟨hI, hcond⟩
      have hval := hI.1.trans_lt hv
      have hp : 0 < σ.vars "size.value" := by
        rw [evalB_condLt (evalB_lit (by omega)) (evalB_var hval)] at hcond
        simpa using hcond
      have hhalf := WordSize.size_half (σ.vars "size.value") hp
      have hcounter : σ.vars "size.count" + 1 < B := by
        have hsz := Nat.size_pos.mpr hp
        have heq := hI.2
        omega
      have hdiv := (Nat.div_le_self (σ.vars "size.value") 2).trans_lt hval
      have hle := (Nat.div_le_self (σ.vars "size.value") 2).trans hI.1
      run_vcg
      all_goals simp_all [I]
      all_goals omega
    · rintro σ ⟨hvalue, hcount⟩
      simp [I, hvalue, hcount]
    · rintro σ ⟨hvalue, hcount⟩
      simp [hvalue]
  have hfinish : Spec B (fun σ => σ.vars "size.value" = v ∧ σ.vars "size.count" = 0) wordLoop
      (fun _ τ => τ.vars "size.value" = 0 ∧ τ.vars "size.count" = v.size) (12 * v.size + 4) := hlo.post (by
    rintro σ τ _ ⟨hI, hcond⟩
    have hzero : τ.vars "size.value" = 0 := by
      rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (hI.1.trans_lt hv))] at hcond
      simpa using hcond
    exact ⟨hzero, by simpa only [hzero, Nat.size_zero, Nat.add_zero] using hI.2⟩)
  rintro σ hvalue
  run_vcg [hfinish]
  all_goals simp_all

private theorem take_size_le (xs : List ℕ) (i : ℕ) :
    Lax759944.BinaryWordEncoding.bitSize (xs.take i) ≤ Lax759944.BinaryWordEncoding.bitSize xs := by
  have h := WordSize.bitSize_append (xs.take i) (xs.drop i)
  rw [List.take_append_drop] at h
  omega

private theorem take_size_step (xs : List ℕ) (i : ℕ) (hi : i < xs.length) :
    Lax759944.BinaryWordEncoding.bitSize (xs.take (i + 1)) =
      Lax759944.BinaryWordEncoding.bitSize (xs.take i) + xs[i].size + 1 := by
  rw [List.take_succ_eq_append_getElem hi, WordSize.bitSize_append, WordSize.bitSize_cons,
    WordSize.bitSize_nil]
  omega

open RamVirtualState Lax759944.BinaryWordEncoding

def ArrayInvariant (xs : List ℕ) (σ : Env) : Prop :=
  σ.vars "input.length" = xs.length ∧ σ.vars "size.i" ≤ xs.length ∧
  σ.vars "size.total" = bitSize (xs.take (σ.vars "size.i")) ∧ Prefix xs "input.data" σ

def arrayStep : Com := .seq (.assign "size.value" (.get "input.data" (.var "size.i")))
  (.seq word (.seq (.assign "size.total" (.add (.add (.var "size.total") (.var "size.count")) (.lit 1)))
    (.assign "size.i" (.add (.var "size.i") (.lit 1)))))

/-- A pass over the copied logical input counts exactly the separator and
canonical bits of each word, including zero words and an empty input. -/
theorem arrayStep_spec (B : ℕ) (xs : List ℕ) (h2 : 2 < B) (hlen : xs.length < B)
    (hsize : bitSize xs + 1 < B) (hwords : ∀ x ∈ xs, x < B) :
    Spec B (fun σ => ArrayInvariant xs σ ∧ σ.vars "size.i" < xs.length) arrayStep
      (fun σ τ => ArrayInvariant xs τ ∧ τ.vars "size.i" = σ.vars "size.i" + 1)
      (12 * bitSize xs + 19) := by
  rintro σ ⟨⟨hcount, hi, htotal, hp⟩, hpos⟩
  let i := σ.vars "size.i"
  let value := xs[i]
  have hvalue : value < B := hwords _ (List.getElem_mem hpos)
  have hget := hp i hpos
  have harray : i < (σ.arrs "input.data").length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hget
    cases hget
  have hiB : σ.vars "size.i" < B := hpos.trans hlen
  have hread : (Expr.get "input.data" (.var "size.i")).evalB B σ = some value := by
    rw [evalB_get_iff]
    exact ⟨i, evalB_var hiB, hget, hvalue⟩
  let ν := σ.setVar "size.value" value
  have hload : Run B (.assign "size.value" (.get "input.data" (.var "size.i"))) σ ν 3 :=
    Run.assign hread
  obtain ⟨μ, hword, hzero, hbits⟩ := word_spec B value h2 hvalue ν (by simp [ν])
  have hiμ : μ.vars "size.i" = i := (hword.frame_var _ (by simp [word, wordLoop, wordStep, Com.wvars])).trans
    (by simp [ν, i])
  have htotalμ : μ.vars "size.total" = bitSize (xs.take i) :=
    (hword.frame_var _ (by simp [word, wordLoop, wordStep, Com.wvars])).trans (by simpa [ν, i] using htotal)
  have hlenμ : μ.vars "input.length" = xs.length :=
    (hword.frame_var _ (by simp [word, wordLoop, wordStep, Com.wvars])).trans (by simpa [ν] using hcount)
  have hdataμ := hword.frame_arr "input.data" (by simp [word, wordLoop, wordStep, Com.warrs])
  have hpμ : Prefix xs "input.data" μ := by simpa only [Prefix, hdataμ, ν, arrs_setVar] using hp
  have hstep := take_size_step xs i hpos
  have hbound := take_size_le xs (i + 1)
  have hsum : bitSize (xs.take i) + value.size + 1 < B := by dsimp only [value]; omega
  have htotalB : bitSize (xs.take i) < B := (take_size_le xs i).trans_lt (by omega)
  have hcountB : value.size < B := by
    have hs := WordSize.member_size xs value (List.getElem_mem hpos)
    omega
  have hiNext : i + 1 < B := by omega
  have hfinish : Spec B (fun τ => τ.vars "size.i" = i ∧ τ.vars "size.total" = bitSize (xs.take i) ∧
      τ.vars "size.count" = value.size ∧ τ.vars "input.length" = xs.length ∧ Prefix xs "input.data" τ)
      (.seq (.assign "size.total" (.add (.add (.var "size.total") (.var "size.count")) (.lit 1)))
        (.assign "size.i" (.add (.var "size.i") (.lit 1))))
      (fun _ τ => ArrayInvariant xs τ ∧ τ.vars "size.i" = i + 1) 10 := by
    rintro τ ⟨hiτ, htτ, hcτ, hlτ, hpτ⟩
    run_vcg
    all_goals simp_all [ArrayInvariant, Prefix, value]
    all_goals omega
  obtain ⟨τ, hfinish, hpost⟩ := hfinish μ ⟨hiμ, htotalμ, hbits, hlenμ, hpμ⟩
  exact ⟨τ, (hload.seq (hword.seq hfinish)).mono (by
    have hs := WordSize.member_size xs value (List.getElem_mem hpos)
    omega), hpost⟩

def array : Com := .seq (.assign "size.total" (.lit 0))
  (.seq (.assign "size.i" (.lit 0)) (.while (.lt (.var "size.i") (.var "input.length")) arrayStep))

theorem array_spec (B : ℕ) (xs : List ℕ) (h2 : 2 < B) (hlen : xs.length < B)
    (hsize : bitSize xs + 1 < B) (hwords : ∀ x ∈ xs, x < B) :
    Spec B (fun σ => σ.vars "input.length" = xs.length ∧ Prefix xs "input.data" σ) array
      (fun _ τ => τ.vars "size.total" = bitSize xs)
      ((12 * bitSize xs + 23) * xs.length + 8) := by
  have hscan := Spec.forRangeZero "size.i" "input.length" (ArrayInvariant xs) xs.length
    (12 * bitSize xs + 19) hlen (fun _ h => h.2.1) (fun _ h => h.1)
    (arrayStep_spec B xs h2 hlen hsize hwords)
  have hfinish : Spec B (fun σ => ArrayInvariant xs (σ.setVar "size.i" 0))
      (.seq (.assign "size.i" (.lit 0)) (.while (.lt (.var "size.i") (.var "input.length")) arrayStep))
      (fun _ τ => τ.vars "size.total" = bitSize xs) ((12 * bitSize xs + 23) * xs.length + 6) :=
    hscan.post (fun _ τ _ h => by simpa only [h.2, List.take_length] using h.1.2.2.1)
  rintro σ ⟨hlenσ, hpσ⟩
  run_vcg [hfinish]
  all_goals simp_all [ArrayInvariant, Prefix, WordSize.bitSize_nil]

end Lax455465Proofs.RamBitSize
