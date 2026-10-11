import Lax455465Proofs.RamUnsignedScalar
import Lax455465Proofs.RamComparison
import Lax455465Proofs.RamFractionPrimitives
import Lax455465Proofs.RamUnsignedBuffer
import Lax455465Proofs.RamUnsignedVector

namespace Lax455465Proofs.RamBallMask

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamUnsignedScalar
open scoped NNRat

def flag (q radius : ℚ≥0) : ℚ≥0 := if (q : ℚ) < (radius : ℚ) then 1 else 0

def Context (array : String) (qs : List ℚ≥0) (radius : ℚ≥0) (σ : Env) : Prop :=
  σ.vars "ball.count" = qs.length ∧ Stored "region.radius" radius σ ∧
    Prefix (RamUnsignedBuffer.encode qs) array σ

def entry (array : String) : Com := .seq (load "region.radius")
  (.seq (RamUnsignedArithmetic.copy "left") (.seq (RamUnsignedBuffer.read array "ball.i")
    (.seq (RamUnsignedArithmetic.copy "right") (.seq RamComparison.compareFraction
      (.ite (.eq (.var "cmp.le") (.lit 1)) RamFractionPrimitives.zero RamFractionPrimitives.one)))))

theorem entry_spec (B M : ℕ) (array : String) (qs : List ℚ≥0) (radius : ℚ≥0) (i : ℕ)
    (hi : i < qs.length) (hB : 2*M^2+3 < B) (hindex : 2*qs.length+2 < B)
    (hrn : radius.num ≤ M) (hrd : radius.den ≤ M) (hqn : qs[i].num ≤ M) (hqd : qs[i].den ≤ M) :
    Spec B (fun σ => Context array qs radius σ ∧ σ.vars "ball.i" = i) (entry array)
      (fun _ τ => Context array qs radius τ ∧ FractionOutput (flag qs[i] radius : ℚ) τ) 82 := by
  have hM : M < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  rintro σ ⟨hctx,hidx⟩
  obtain ⟨ν,rload,pload⟩ := load_spec B "region.radius" radius h1 (hrn.trans_lt hM) (hrd.trans_lt hM) (by decide) σ hctx.2.1
  obtain ⟨μ,rl,pl⟩ := RamUnsignedArithmetic.copy_spec B radius "left" h1
    (hrn.trans_lt hM) (hrd.trans_lt hM) (by decide) ν pload
  have hpμ : Prefix (RamUnsignedBuffer.encode qs) array μ := by
    have rr := rload.seq rl
    simpa only [Prefix,rr.frame_arr array (by change array ∉ ([] : List String); simp)] using hctx.2.2
  have hiμ : μ.vars "ball.i" = i := by
    have rr := rload.seq rl
    exact (rr.frame_var "ball.i" (by decide)).trans hidx
  obtain ⟨ξ,rq,pq⟩ := RamUnsignedBuffer.read_spec B array "ball.i" qs i hi (by nlinarith) (by omega)
    (hqn.trans_lt hM) (hqd.trans_lt hM) (by decide) μ ⟨hpμ,hiμ⟩
  obtain ⟨η,rr,pr⟩ := RamUnsignedArithmetic.copy_spec B qs[i] "right" h1
    (hqn.trans_lt hM) (hqd.trans_lt hM) (by decide) ξ pq.1
  have plη : η.vars "left.s" = 0 ∧ η.vars "left.n" = radius.num ∧ η.vars "left.d" = radius.den := by
    have r := rq.seq rr
    simpa only [r.frame_var "left.s" (by simp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]),
      r.frame_var "left.n" (by simp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]),
      r.frame_var "left.d" (by simp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]),String.reduceAppend] using pl
  obtain ⟨ζ,rc,pc⟩ := RamComparison.compareFraction_spec B M 0 radius.num radius.den 0 qs[i].num qs[i].den
    hB (by omega) (by omega) hrn hrd hqn hqd radius.den_pos qs[i].den_pos η
    ⟨plη.1,plη.2.1,plη.2.2,by simpa only [String.reduceAppend] using pr⟩
  have hflag : ζ.vars "cmp.le" = 1 ↔ (radius : ℚ) ≤ (qs[i] : ℚ) := by
    simpa only [RamUnsignedArithmetic.value] using pc.2
  have hc : (Cond.eq (.var "cmp.le") (.lit 1)).evalB B ζ = some (decide (ζ.vars "cmp.le" = 1)) := by
    rw [evalB_condEq (evalB_var (pc.1.trans_lt h1)) (evalB_lit h1)]
    congr 1
  have preserve : ∀ {τ : Env} {c : Com} {k : ℕ}, Run B c σ τ k →
      array ∉ c.warrs → (∀ x ∈ ["ball.count","region.radius.n","region.radius.d"], x ∉ c.wvars) → Context array qs radius τ := by
    intro τ c k r ha hv
    simpa only [Context,Stored,Prefix,r.frame_arr array ha,
      r.frame_var "ball.count" (hv _ (by simp)),r.frame_var "region.radius.n" (hv _ (by simp)),
      r.frame_var "region.radius.d" (hv _ (by simp)),String.reduceAppend] using hctx
  by_cases hq : (qs[i] : ℚ) < (radius : ℚ)
  · have hf : ¬ζ.vars "cmp.le" = 1 := fun h => (not_le_of_gt hq) (hflag.mp h)
    obtain ⟨τ,rone,pone⟩ := RamFractionPrimitives.one_spec B h1 ζ trivial
    have branchRun := Run.ite_false (c := RamFractionPrimitives.zero) (by simpa only [hf,decide_false] using hc) rone
    have r := rload.seq (rl.seq (rq.seq (rr.seq (rc.seq branchRun))))
    refine ⟨τ,r.mono (by dsimp [Cond.size,Expr.size]; omega),?_,?_⟩
    · exact preserve r (by change array ∉ ([] : List String); simp) (by
        dsimp [Com.wvars,load,RamUnsignedArithmetic.copy,RamUnsignedBuffer.read]; decide)
    · simpa only [flag,if_pos hq,NNRat.coe_one] using pone
  · have hf := hflag.mpr (le_of_not_gt hq)
    obtain ⟨τ,rzero,pzero⟩ := RamFractionPrimitives.zero_spec B h1 ζ trivial
    have branchRun := Run.ite_true (d := RamFractionPrimitives.one) (by simpa only [hf,decide_true] using hc) rzero
    have r := rload.seq (rl.seq (rq.seq (rr.seq (rc.seq branchRun))))
    refine ⟨τ,r.mono (by dsimp [Cond.size,Expr.size]; omega),?_,?_⟩
    · exact preserve r (by change array ∉ ([] : List String); simp) (by
        dsimp [Com.wvars,load,RamUnsignedArithmetic.copy,RamUnsignedBuffer.read]; decide)
    · simpa only [flag,if_neg hq,NNRat.coe_zero] using pzero

def command (source target : String) : Com := .seq (.assign "ball.pos" (.lit 0))
  (RamUnsignedVector.command "ball.i" "ball.count" target "ball.pos" (entry source))

/-- Emit the exact strict ball as canonical zero/one rational coordinates.
Threshold equality remains outside the ball. -/
theorem command_spec (B M : ℕ) (source target : String) (qs : List ℚ≥0) (radius : ℚ≥0)
    (hneq : source ≠ target) (hB : 2*M^2+3 < B) (hindex : 2*qs.length+2 < B)
    (hrn : radius.num ≤ M) (hrd : radius.den ≤ M)
    (hnum : ∀ q ∈ qs, q.num ≤ M) (hden : ∀ q ∈ qs, q.den ≤ M) :
    Spec B (fun σ => Context source qs radius σ ∧ 2*qs.length < (σ.arrs target).length)
      (command source target) (fun _ τ => Context source qs radius τ ∧
        Prefix (RamUnsignedBuffer.encode (qs.map (fun q => flag q radius))) target τ)
      (104*qs.length+8) := by
  have h1 : 1 < B := by nlinarith
  let flags := qs.map (fun q => flag q radius)
  have hlen : flags.length = qs.length := by simp [flags]
  have hvalues : ∀ i, ∀ hi : i < flags.length, flags[i].num < B ∧ flags[i].den < B := by
    intro i hi
    have hq : i < qs.length := by omega
    have he : flags[i] = flag qs[i] radius := by simp only [flags,List.getElem_map]
    rw [he]
    unfold flag
    split_ifs <;> norm_num <;> omega
  have hf := RamUnsignedVector.command_spec B 82 (Context source qs radius)
    "ball.i" "ball.count" target "ball.pos" flags [] (entry source) h1
    (by simp only [List.length_nil,hlen]; omega)
    (fun i hi => (hvalues i hi).1) (fun i hi => (hvalues i hi).2)
    (fun _ h => by simpa only [hlen] using h.1)
    (fun σ k h => by simpa only [Context,Stored,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false,String.reduceAppend] using h)
    (fun i hi => by
      have hq : i < qs.length := by omega
      have hm := List.getElem_mem hq
      simpa only [flags,List.getElem_map] using entry_spec B M source qs radius i hq hB hindex
        hrn hrd (hnum _ hm) (hden _ hm))
    (by dsimp [entry,Com.wvars,load,RamUnsignedArithmetic.copy,RamUnsignedBuffer.read]; decide)
    (by dsimp [entry,Com.wvars,load,RamUnsignedArithmetic.copy,RamUnsignedBuffer.read]; decide)
    (by change target ∉ ([] : List String); simp)
    (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide)
    (fun rr h => by
      simpa only [Context,Stored,Prefix,String.reduceAppend,
        rr.frame_var "ball.count" (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide),
        rr.frame_var "region.radius.n" (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide),
        rr.frame_var "region.radius.d" (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide),
        rr.frame_arr source (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.warrs,hneq])] using h)
    (by decide) (by decide)
  rintro σ ⟨hctx,hroom⟩
  let ν := σ.setVar "ball.pos" 0
  have rzero : Run B (.assign "ball.pos" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have hctxν : Context source qs radius ν := by
    simpa only [Context,Stored,Prefix,ν,vars_setVar,arrs_setVar,String.reduceEq,if_false,String.reduceAppend] using hctx
  obtain ⟨τ,rr,pr⟩ := hf ν ⟨hctxν,by intro i hi; simp at hi,by simp [ν],
    by simpa only [ν,arrs_setVar,List.length_nil,Nat.zero_add,hlen] using hroom⟩
  exact ⟨τ,(rzero.seq rr).mono (by rw [hlen]; omega),pr.1,by simpa only [flags,List.nil_append] using pr.2.1⟩

end Lax455465Proofs.RamBallMask
