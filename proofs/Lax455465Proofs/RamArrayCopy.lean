import Lax455465Proofs.RamVirtualState
import Lax455465Proofs.RamFrames

namespace Lax455465Proofs.RamArrayCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

def step (source target : String) : Com :=
  .seq (.store target (.var "copy.i") (.get source (.var "copy.i")))
    (.assign "copy.i" (.add (.var "copy.i") (.lit 1)))

def command (source target count : String) : Com := .seq (.assign "copy.i" (.lit 0))
  (.while (.lt (.var "copy.i") (.var count)) (step source target))

def Invariant (xs : List ℕ) (source target count : String) (σ : Env) : Prop :=
  Prefix xs source σ ∧ σ.vars count = xs.length ∧ σ.vars "copy.i" ≤ xs.length ∧
    xs.length ≤ (σ.arrs target).length ∧ Prefix (xs.take (σ.vars "copy.i")) target σ

theorem step_spec (B : ℕ) (xs : List ℕ) (source target count : String)
    (h1 : 1 < B) (hlen : xs.length < B) (hwords : ∀ x ∈ xs, x < B)
    (harray : source ≠ target) (hcount : count ≠ "copy.i") :
    Spec B (fun σ => Invariant xs source target count σ ∧ σ.vars "copy.i" < xs.length)
      (step source target) (fun σ τ => Invariant xs source target count τ ∧
        τ.vars "copy.i" = σ.vars "copy.i"+1) 8 := by
  rintro σ ⟨⟨hp,hc,hi,hroom,ht⟩,hlt⟩
  let i := σ.vars "copy.i"
  have hi' : i < xs.length := hlt
  have hget : (σ.arrs source)[i]? = some xs[i] := hp i hi'
  have hiB : i < B := hi'.trans hlen
  have hvB : xs[i] < B := hwords _ (List.getElem_mem hi')
  have rstore : Run B (.store target (.var "copy.i") (.get source (.var "copy.i"))) σ
      (σ.setArr target i xs[i]) 4 := Run.store (evalB_var hiB)
        (evalB_get (evalB_var hiB) hget hvB) (by omega)
  let ν := σ.setArr target i xs[i]
  have rinc : Run B (.assign "copy.i" (.add (.var "copy.i") (.lit 1))) ν
      (ν.setVar "copy.i" (i+1)) 4 := Run.assign
    (evalB_bin (op := .add) (evalB_var (by simpa [ν] using hiB)) (evalB_lit h1) (by dsimp [Bop.apply]; omega))
  have hprefix : Prefix (xs.take (i+1)) target ν := by
    intro j hj
    have hj' : j < i+1 := by simp only [List.length_take] at hj; omega
    have hxj : j < xs.length := by omega
    have htake : (xs.take (i+1))[j] = xs[j] := List.getElem_take
    simp only [ν,arrs_setArr,if_true]
    by_cases he : i = j
    · subst j
      rw [List.getElem?_set_self (by omega)]
      exact congrArg some htake.symm
    · rw [List.getElem?_set_ne he]
      have hji : j < i := by omega
      have hjtake : j < (xs.take i).length := by simp only [List.length_take]; omega
      exact (ht j hjtake).trans (congrArg some (by simp only [List.getElem_take,htake]))
  refine ⟨ν.setVar "copy.i" (i+1),rstore.seq rinc,?_,?_⟩
  · refine ⟨?_,?_,by simp; omega,?_,?_⟩
    · simpa only [Prefix,ν,arrs_setVar,arrs_setArr,if_neg harray] using hp
    · simpa only [ν,vars_setVar,vars_setArr,if_neg hcount] using hc
    · simpa only [ν,length_arrs_setArr,arrs_setVar] using hroom
    · simpa only [Prefix,arrs_setVar,vars_setVar,if_pos rfl,if_true] using hprefix
  · simp [i]

/-- Copy a bounded initialized prefix between reserved arrays, preserving
the source and reading exactly the runtime count. -/
theorem command_spec (B : ℕ) (xs : List ℕ) (source target count : String)
    (h1 : 1 < B) (hlen : xs.length < B) (hwords : ∀ x ∈ xs, x < B)
    (harray : source ≠ target) (hcount : count ≠ "copy.i") :
    Spec B (fun σ => Prefix xs source σ ∧ σ.vars count = xs.length ∧
      xs.length ≤ (σ.arrs target).length) (command source target count)
      (fun _ τ => Prefix xs source τ ∧ Prefix xs target τ) (12*xs.length+6) := by
  have hloop := Spec.forRangeZero "copy.i" count (Invariant xs source target count) xs.length 8 hlen
    (fun _ h => h.2.2.1) (fun _ h => h.2.1) (step_spec B xs source target count h1 hlen hwords harray hcount)
  rintro σ ⟨hp,hc,hroom⟩
  have hinit : Invariant xs source target count (σ.setVar "copy.i" 0) := by
    refine ⟨?_,?_,by simp,?_,?_⟩
    · simpa only [Prefix,arrs_setVar] using hp
    · simpa only [vars_setVar,if_neg hcount] using hc
    · simpa only [arrs_setVar] using hroom
    · intro i hi
      simp only [vars_setVar,if_true,List.take_zero,List.length_nil] at hi
      omega
  obtain ⟨τ,hr,hpost⟩ := hloop σ hinit
  exact ⟨τ,by simpa only [command] using hr,hpost.1.1,
    by simpa only [hpost.2,List.take_length] using hpost.1.2.2.2.2⟩

end Lax455465Proofs.RamArrayCopy
