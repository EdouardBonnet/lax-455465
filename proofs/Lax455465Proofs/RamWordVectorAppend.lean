import Lax455465Proofs.RamWordBuffer

namespace Lax455465Proofs.RamWordVectorAppend
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

/-- Append the actual simple-path vertex buffer to the certificate buffer. -/
def step : Com := .seq (RamWordBuffer.append "short.output" "short.outputLength"
  (.get "short.simple" (.var "record.i"))) (.assign "record.i" (.add (.var "record.i") (.lit 1)))

def command : Com := .seq (.assign "record.i" (.lit 0))
  (.while (.lt (.var "record.i") (.var "short.simpleLength")) step)

def Invariant (front xs : List ℕ) (σ : Env) : Prop :=
  Prefix xs "short.simple" σ ∧ σ.vars "short.simpleLength"=xs.length ∧ σ.vars "record.i"≤xs.length ∧
    Prefix (front++xs.take (σ.vars "record.i")) "short.output" σ ∧
    σ.vars "short.outputLength"=front.length+σ.vars "record.i" ∧
    front.length+xs.length<(σ.arrs "short.output").length

theorem step_spec (B : ℕ) (front xs : List ℕ) (h1 : 1<B) (hlen : front.length+xs.length+1<B)
    (hwords : ∀ x∈xs,x<B) :
    Spec B (fun σ => Invariant front xs σ ∧ σ.vars "record.i"<xs.length) step
      (fun σ τ => Invariant front xs τ ∧ τ.vars "record.i"=σ.vars "record.i"+1) 12 := by
  rintro σ ⟨⟨hsource,hcount,hi,houtput,hpos,hroom⟩,hlt⟩
  let i := σ.vars "record.i"
  have hi' : i<xs.length := hlt
  let words := front++xs.take i
  have hwordlen : words.length=front.length+i := by simp only [words,List.length_append,List.length_take,Nat.min_eq_left hi'.le]
  have hvalue := hwords xs[i] (List.getElem_mem hi')
  obtain ⟨ν,rr,pr⟩ := RamWordBuffer.append_spec B "short.output" "short.outputLength" words xs[i]
    (.get "short.simple" (.var "record.i")) h1 (by rw [hwordlen]; omega) σ
    ⟨houtput,by rwa [hwordlen],by rw [hwordlen]; omega,
      evalB_get (evalB_var (hi'.trans (by omega : xs.length<B))) (hsource i hi') hvalue⟩
  have hiν := rr.frame_var "record.i" (by decide)
  have hsourceν : Prefix xs "short.simple" ν := by
    simpa only [Prefix,rr.frame_arr "short.simple" (by decide)] using hsource
  have hcountν := (rr.frame_var "short.simpleLength" (by decide)).trans hcount
  have hroomν : front.length+xs.length<(ν.arrs "short.output").length := by
    simpa only [RamFrames.run_array_length rr "short.output"] using hroom
  have hnew : words++[xs[i]]=front++xs.take (i+1) := by
    rw [List.take_succ_eq_append_getElem hi']
    simp only [words,List.append_assoc]
  let τ := ν.setVar "record.i" (i+1)
  have rinc : Run B (.assign "record.i" (.add (.var "record.i") (.lit 1))) ν τ 4 :=
    Run.assign (evalB_bin (op := .add) (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ (hi'.trans (by omega))⟩)
      (evalB_lit h1) (by dsimp [Bop.apply]; omega))
  refine ⟨τ,rr.seq rinc,?_,by simp [τ,i]⟩
  refine ⟨hsourceν,?_,by simp [τ]; omega,?_,?_,hroomν⟩
  · simpa only [τ,vars_setVar,String.reduceEq,if_false] using hcountν
  · simpa only [τ,Prefix,arrs_setVar,vars_setVar,if_true,hnew] using pr.1
  · have hp : ν.vars "short.outputLength"=front.length+i+1 := by simpa only [hwordlen] using pr.2
    simpa only [τ,vars_setVar,String.reduceEq,if_false,if_true,Nat.add_assoc] using hp

theorem command_spec (B : ℕ) (front xs : List ℕ) (h1 : 1<B) (hlen : front.length+xs.length+1<B)
    (hwords : ∀ x∈xs,x<B) :
    Spec B (fun σ => Prefix xs "short.simple" σ ∧ σ.vars "short.simpleLength"=xs.length ∧
      Prefix front "short.output" σ ∧ σ.vars "short.outputLength"=front.length ∧
      front.length+xs.length<(σ.arrs "short.output").length) command
      (fun _ τ => Prefix (front++xs) "short.output" τ ∧ τ.vars "short.outputLength"=front.length+xs.length)
      (16*xs.length+6) := by
  have hscan := Spec.forRangeZero "record.i" "short.simpleLength" (Invariant front xs) xs.length 12
    (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.1) (step_spec B front xs h1 hlen hwords)
  rintro σ ⟨hp,hcount,ho,hpos,hroom⟩
  have hinit : Invariant front xs (σ.setVar "record.i" 0) := by
    refine ⟨hp,?_,by simp,?_,?_,hroom⟩
    · simpa only [vars_setVar,String.reduceEq,if_false] using hcount
    · simpa only [Prefix,arrs_setVar,vars_setVar,if_true,List.take_zero,List.append_nil] using ho
    · simpa only [vars_setVar,String.reduceEq,if_false,if_true,Nat.add_zero] using hpos
  obtain ⟨τ,rr,pr⟩ := hscan σ hinit
  exact ⟨τ,rr,by simpa only [pr.2,List.take_length] using pr.1.2.2.2.1,
    by simpa only [pr.2] using pr.1.2.2.2.2.1⟩

end Lax455465Proofs.RamWordVectorAppend
