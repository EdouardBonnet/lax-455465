import Lax455465Proofs.RamWordBuffer

namespace Lax455465Proofs.RamLpInputFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

def step : Com := .seq
  (RamWordBuffer.append "vm.input" "vm.inputLength" (.get "lp.word" (.var "frame.i")))
  (.assign "frame.i" (.add (.var "frame.i") (.lit 1)))

def Invariant (xs : List ℕ) (σ : Env) : Prop :=
  σ.vars "lp.position" = xs.length ∧ σ.vars "frame.i" ≤ xs.length ∧
  Prefix xs "lp.word" σ ∧ Prefix (xs.length :: xs.take (σ.vars "frame.i")) "vm.input" σ ∧
  σ.vars "vm.inputLength" = σ.vars "frame.i" + 1 ∧ xs.length < (σ.arrs "vm.input").length

theorem step_spec (B : ℕ) (xs : List ℕ) (h1 : 1 < B) (hlen : xs.length + 1 < B)
    (hwords : ∀ x ∈ xs, x < B) :
    Spec B (fun σ => Invariant xs σ ∧ σ.vars "frame.i" < xs.length) step
      (fun σ τ => Invariant xs τ ∧ τ.vars "frame.i" = σ.vars "frame.i" + 1) 12 := by
  rintro σ ⟨⟨hpos, hi, hsource, hp, hcursor, hroom⟩, hlt⟩
  let i := σ.vars "frame.i"
  let value := xs[i]
  have hi' : i ≤ xs.length := hi
  have hlt' : i < xs.length := hlt
  have hv := hwords xs[i] (List.getElem_mem hlt)
  have hget := hsource i hlt
  have hsourceRoom : i < (σ.arrs "lp.word").length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hget
    cases hget
  have he : (Expr.get "lp.word" (.var "frame.i")).evalB B σ = some value := by
    rw [evalB_get_iff]
    exact ⟨i, evalB_var (by omega), hget, hv⟩
  have hprefixlen : (xs.length :: xs.take i).length = i + 1 := by simp [List.length_take, Nat.min_eq_left hi']
  obtain ⟨ν, hwrite, hpost⟩ := RamWordBuffer.append_spec B "vm.input" "vm.inputLength"
    (xs.length :: xs.take i) value (.get "lp.word" (.var "frame.i")) h1
    (by rw [hprefixlen]; omega) σ ⟨hp, by rwa [hprefixlen], by rw [hprefixlen]; omega, he⟩
  have hiν : ν.vars "frame.i" = i := (hwrite.frame_var _ (by simp [RamWordBuffer.append, Com.wvars])).trans rfl
  have hposν := (hwrite.frame_var "lp.position" (by simp [RamWordBuffer.append, Com.wvars])).trans hpos
  have hsourceν : Prefix xs "lp.word" ν := by
    simpa only [Prefix, hwrite.frame_arr "lp.word" (by simp [RamWordBuffer.append, Com.warrs])] using hsource
  have hroomν : xs.length < (ν.arrs "vm.input").length := by
    rwa [RamFrames.run_array_length hwrite "vm.input"]
  have htake : xs.take (i + 1) = xs.take i ++ [value] := List.take_succ_eq_append_getElem hlt'
  have hpν : Prefix (xs.length :: xs.take (i + 1)) "vm.input" ν := by
    rw [htake]
    simpa only [List.cons_append] using hpost.1
  have hlenν : ν.vars "vm.inputLength" = i + 1 + 1 := by simpa only [hprefixlen] using hpost.2
  have hiNext : i + 1 < B := by omega
  have hinc : Run B (.assign "frame.i" (.add (.var "frame.i") (.lit 1))) ν (ν.setVar "frame.i" (i + 1)) 4 :=
    Run.assign (evalB_bin (op := .add) (by rw [evalB_var_iff]; exact ⟨hiν.symm, hiν ▸ (by omega : i < B)⟩)
      (evalB_lit h1) hiNext)
  refine ⟨ν.setVar "frame.i" (i + 1), (hwrite.seq hinc).mono (by simp [Expr.size]), ?_⟩
  constructor
  · simpa only [Invariant, Prefix, arrs_setVar, vars_setVar, String.reduceEq, if_true, if_false]
      using And.intro hposν (And.intro (by omega : i + 1 ≤ xs.length)
        (And.intro hsourceν (And.intro hpν (And.intro hlenν hroomν))))
  · simp [i]


/-- The virtual solver receives exactly the physical length-prefixed LP
word, copied from the constructed LP buffer without consuming host input. -/
def command : Com := .seq (.assign "vm.inputLength" (.lit 0))
  (.seq (RamWordBuffer.append "vm.input" "vm.inputLength" (.var "lp.position"))
    (.seq (.assign "frame.i" (.lit 0)) (.while (.lt (.var "frame.i") (.var "lp.position")) step)))

theorem command_spec (B : ℕ) (xs : List ℕ) (h1 : 1 < B) (hlen : xs.length + 1 < B)
    (hwords : ∀ x ∈ xs, x < B) :
    Spec B (fun σ => Prefix xs "lp.word" σ ∧ σ.vars "lp.position" = xs.length ∧
      xs.length < (σ.arrs "vm.input").length) command
      (fun _ τ => Prefix (xs.length :: xs) "vm.input" τ ∧ τ.vars "vm.inputLength" = xs.length + 1)
      (16 * xs.length + 15) := by
  have hscan := Spec.forRangeZero "frame.i" "lp.position" (Invariant xs) xs.length 12
    (by omega) (fun _ h => h.2.1) (fun _ h => h.1) (step_spec B xs h1 hlen hwords)
  have hfinish : Spec B (fun σ => Invariant xs (σ.setVar "frame.i" 0))
      (.seq (.assign "frame.i" (.lit 0)) (.while (.lt (.var "frame.i") (.var "lp.position")) step))
      (fun _ τ => Prefix (xs.length :: xs) "vm.input" τ ∧ τ.vars "vm.inputLength" = xs.length + 1)
      (16 * xs.length + 6) := hscan.post (fun _ τ _ h => by
        exact ⟨by simpa only [h.2, List.take_length] using h.1.2.2.2.1, by simpa only [h.2] using h.1.2.2.2.2.1⟩)
  have hprefix := RamWordBuffer.append_spec B "vm.input" "vm.inputLength" [] xs.length (.var "lp.position") h1
    (by simp; omega)
  rintro σ ⟨hp, hpos, hroom⟩
  let ν := σ.setVar "vm.inputLength" 0
  have hzero : Run B (.assign "vm.inputLength" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  obtain ⟨μ, hhead, hheadPost⟩ := hprefix ν ⟨by intro i hi; simp at hi, by simp [ν],
    by simp [ν]; omega, by rw [evalB_var_iff]; exact ⟨by simp [ν, hpos], by simp [ν, hpos]; omega⟩⟩
  have hposμ : μ.vars "lp.position" = xs.length :=
    (hhead.frame_var _ (by simp [RamWordBuffer.append, Com.wvars])).trans (by simp [ν, hpos])
  have hpμ : Prefix xs "lp.word" μ := by
    simpa only [Prefix, hhead.frame_arr "lp.word" (by simp [RamWordBuffer.append, Com.warrs]),
      ν, arrs_setVar] using hp
  have hroomμ : xs.length < (μ.arrs "vm.input").length := by
    rw [RamFrames.run_array_length hhead "vm.input"]
    simpa only [ν, arrs_setVar] using hroom
  have hpre : Invariant xs (μ.setVar "frame.i" 0) := by
    simpa only [Invariant, Prefix, vars_setVar, String.reduceEq, if_true, if_false,
      arrs_setVar, List.take_zero, List.length_nil, List.nil_append, Nat.zero_add]
      using And.intro hposμ (And.intro (Nat.zero_le xs.length)
        (And.intro hpμ (And.intro hheadPost.1 (And.intro hheadPost.2 hroomμ))))
  obtain ⟨τ, hscan, hpost⟩ := hfinish μ hpre
  exact ⟨τ, (hzero.seq (hhead.seq hscan)).mono (by simp [Expr.size]; omega), hpost⟩

end Lax455465Proofs.RamLpInputFrame
