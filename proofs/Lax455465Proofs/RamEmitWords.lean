import Lax455465Proofs.RamFrames
import Lax455465Proofs.RamVirtualState

namespace Lax455465Proofs.RamEmitWords
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

def step (array : String) (stride : ℕ) : Com := .seq (.write (.get array (.mul (.lit stride) (.var "emit.i"))))
  (.assign "emit.i" (.add (.var "emit.i") (.lit 1)))
def command (array : String) (stride : ℕ) : Com := .seq (.assign "emit.i" (.lit 0))
  (.while (.lt (.var "emit.i") (.var "emit.count")) (step array stride))
def Data (array : String) (stride : ℕ) (xs : List ℕ) (σ : Env) : Prop :=
  ∀ i,∀ hi : i < xs.length,(σ.arrs array)[stride*i]?=some xs[i]

def Invariant (array : String) (stride : ℕ) (xs front : List ℕ) (σ : Env) : Prop :=
  Data array stride xs σ ∧ σ.vars "emit.count"=xs.length ∧ σ.vars "emit.i"≤xs.length ∧
    σ.out=front++xs.take (σ.vars "emit.i")

/-- Emit an initialized word buffer in order, retaining the existing output
prefix. Output words are read from the actual runtime array. -/
theorem command_spec (B : ℕ) (array : String) (stride : ℕ) (xs front : List ℕ)
    (h1 : 1 < B) (hstride : stride < B) (hoffset : stride*xs.length < B) (hlen : xs.length < B) (hwords : ∀ x∈xs,x < B) :
    Spec B (fun σ => Data array stride xs σ ∧ σ.vars "emit.count"=xs.length ∧ σ.out=front)
      (command array stride) (fun _ τ => τ.out=front++xs) (13*xs.length+6) := by
  have hstep : Spec B (fun σ => Invariant array stride xs front σ ∧ σ.vars "emit.i" < xs.length)
      (step array stride) (fun σ τ => Invariant array stride xs front τ ∧ τ.vars "emit.i"=σ.vars "emit.i"+1) 9 := by
    rintro σ ⟨⟨hp,hcount,hle,hout⟩,hlt⟩
    let i := σ.vars "emit.i"
    have hi : i < xs.length := hlt
    have hval : xs[i] < B := hwords _ (List.getElem_mem hi)
    have he : (Expr.get array (.mul (.lit stride) (.var "emit.i"))).evalB B σ=some xs[i] :=
      evalB_get (evalB_bin (op := .mul) (evalB_lit hstride) (evalB_var (hi.trans hlen))
        ((Nat.mul_le_mul_left stride hi.le).trans_lt hoffset)) (hp i hi) hval
    let ν : Env := {σ with out := σ.out++[xs[i]]}
    have r1 : Run B (.write (.get array (.mul (.lit stride) (.var "emit.i")))) σ ν 5 := Run.write he
    have r2 : Run B (.assign "emit.i" (.add (.var "emit.i") (.lit 1))) ν (ν.setVar "emit.i" (i+1)) 4 :=
      Run.assign (evalB_bin (op := .add) (evalB_var (hi.trans hlen)) (evalB_lit h1) (by dsimp [Bop.apply]; omega))
    refine ⟨_,r1.seq r2,⟨hp,by simpa [ν] using hcount,by simp; omega,?_⟩,by simp [i,ν]⟩
    change σ.out++[xs[i]]=front++xs.take (i+1)
    rw [List.take_succ_eq_append_getElem hi,←List.append_assoc]
    exact congrArg (fun a => a++[xs[i]]) hout
  have hloop := Spec.forRangeZero "emit.i" "emit.count" (Invariant array stride xs front) xs.length 9 hlen
    (fun _ h => h.2.2.1) (fun _ h => h.2.1) hstep
  rintro σ ⟨hp,hcount,hout⟩
  obtain ⟨τ,rr,pr⟩ := hloop σ ⟨hp,by simpa using hcount,by simp,by simpa using hout⟩
  exact ⟨τ,by simpa [command] using rr,by simpa only [pr.2,List.take_length] using pr.1.2.2.2⟩

end Lax455465Proofs.RamEmitWords
