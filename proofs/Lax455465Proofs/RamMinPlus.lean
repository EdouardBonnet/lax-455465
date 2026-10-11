import Lax455465Proofs.RamUnsignedArithmetic
import Lax455465Proofs.RamUnsignedBuffer
import Lax455465Proofs.RamMinimum

namespace Lax455465Proofs.RamMinPlus

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

def restore : Com := .seq (.assign "left.s" (.lit 0))
  (.seq (.assign "left.n" (.var "metric.base.n")) (.assign "left.d" (.var "metric.base.d")))

def command : Com := .seq (RamUnsignedBuffer.read "metric.old" "metric.a")
  (.seq (RamUnsignedArithmetic.copy "metric.base")
    (.seq (RamUnsignedBuffer.read "metric.old" "metric.b")
      (.seq (RamUnsignedArithmetic.copy "left")
        (.seq (RamUnsignedBuffer.read "metric.old" "metric.c")
          (.seq (RamUnsignedArithmetic.copy "right")
            (.seq addFraction (.seq (RamUnsignedArithmetic.copy "right")
              (.seq restore RamMinimum.command))))))))

def Context (qs : List ℚ≥0) (a b c : ℕ) (σ : Env) : Prop :=
  Prefix (RamUnsignedBuffer.encode qs) "metric.old" σ ∧
    σ.vars "metric.a" = a ∧ σ.vars "metric.b" = b ∧ σ.vars "metric.c" = c

theorem frame {B K : ℕ} {cmd : Com} {σ τ : Env} (hr : Run B cmd σ τ K)
    {qs : List ℚ≥0} {a b c : ℕ} (h : Context qs a b c σ)
    (ha : "metric.old" ∉ cmd.warrs)
    (hx : ∀ x ∈ ["metric.a","metric.b","metric.c"], x ∉ cmd.wvars) : Context qs a b c τ := by
  simpa only [Context,Prefix,hr.frame_arr "metric.old" ha,
    hr.frame_var "metric.a" (hx _ (by simp)),hr.frame_var "metric.b" (hx _ (by simp)),
    hr.frame_var "metric.c" (hx _ (by simp))] using h

theorem restore_spec (B : ℕ) (q : ℚ≥0) (h1 : 1 < B) (hn : q.num < B) (hd : q.den < B) :
    Spec B (fun σ => σ.vars "metric.base.n" = q.num ∧ σ.vars "metric.base.d" = q.den)
      restore (fun _ τ => τ.vars "left.s" = 0 ∧ τ.vars "left.n" = q.num ∧ τ.vars "left.d" = q.den) 6 := by
  rintro σ ⟨hnσ,hdσ⟩
  run_vcg
  all_goals simp_all

/-- One actual native min-plus update reads three initialized rational
coordinates, adds the two pivot legs, and returns their minimum with the
original distance. The normalized candidate bound is supplied by the
common-denominator invariant, rather than an iterated squaring estimate. -/
theorem command_spec (B H : ℕ) (qs : List ℚ≥0) (a b c : ℕ)
    (ha : a < qs.length) (hb : b < qs.length) (hc : c < qs.length)
    (hB : 2*(2*H)^2+3 < B)
    (hia : 2*a+1 < B) (hib : 2*b+1 < B) (hic : 2*c+1 < B)
    (han : qs[a].num ≤ H) (had : qs[a].den ≤ H)
    (hbn : qs[b].num ≤ H) (hbd : qs[b].den ≤ H)
    (hcn : qs[c].num ≤ H) (hcd : qs[c].den ≤ H)
    (hsn : (qs[b]+qs[c]).num ≤ 2*H) (hsd : (qs[b]+qs[c]).den ≤ 2*H) :
    Spec B (Context qs a b c) command
      (fun _ τ => FractionOutput (min (qs[a] : ℚ) ((qs[b]+qs[c] : ℚ≥0) : ℚ)) τ)
      (36*(qs[b].den*qs[c].den).size+218) := by
  have hH : H < B := by nlinarith
  have h2H : 2*H < B := by nlinarith
  have hB' : 2*H^2+3 < B := by nlinarith
  have h2 : 2 < B := by nlinarith
  rintro σ hctx
  obtain ⟨s1,r1,p1⟩ := RamUnsignedBuffer.read_spec B "metric.old" "metric.a" qs a ha h2 hia
    (han.trans_lt hH) (had.trans_lt hH) (by decide) σ ⟨hctx.1,hctx.2.1⟩
  obtain ⟨s2,r2,p2⟩ := RamUnsignedArithmetic.copy_spec B qs[a] "metric.base" (by omega)
    (han.trans_lt hH) (had.trans_lt hH) (by decide) s1 p1.1
  have ctx2 := frame (r1.seq r2) hctx (by decide) (by decide)
  obtain ⟨s3,r3,p3⟩ := RamUnsignedBuffer.read_spec B "metric.old" "metric.b" qs b hb h2 hib
    (hbn.trans_lt hH) (hbd.trans_lt hH) (by decide) s2 ⟨ctx2.1,ctx2.2.2.1⟩
  obtain ⟨s4,r4,p4⟩ := RamUnsignedArithmetic.copy_spec B qs[b] "left" (by omega)
    (hbn.trans_lt hH) (hbd.trans_lt hH) (by decide) s3 p3.1
  have ctx4 := frame (r3.seq r4) ctx2 (by decide) (by decide)
  obtain ⟨s5,r5,p5⟩ := RamUnsignedBuffer.read_spec B "metric.old" "metric.c" qs c hc h2 hic
    (hcn.trans_lt hH) (hcd.trans_lt hH) (by decide) s4 ⟨ctx4.1,ctx4.2.2.2⟩
  obtain ⟨s6,r6,p6⟩ := RamUnsignedArithmetic.copy_spec B qs[c] "right" (by omega)
    (hcn.trans_lt hH) (hcd.trans_lt hH) (by decide) s5 p5.1
  have pleft6 : s6.vars "left.s" = 0 ∧ s6.vars "left.n" = qs[b].num ∧ s6.vars "left.d" = qs[b].den := by
    simpa only [String.reduceAppend,(r5.seq r6).frame_var "left.s" (by decide),(r5.seq r6).frame_var "left.n" (by decide),
      (r5.seq r6).frame_var "left.d" (by decide)] using p4
  obtain ⟨s7,r7,p7⟩ := RamUnsignedArithmetic.add_spec B H qs[b] qs[c] hB' hbn hbd hcn hcd s6
    ⟨pleft6.1,pleft6.2.1,pleft6.2.2,p6⟩
  obtain ⟨s8,r8,p8⟩ := RamUnsignedArithmetic.copy_spec B (qs[b]+qs[c]) "right" (by omega)
    (hsn.trans_lt h2H) (hsd.trans_lt h2H) (by decide) s7 p7
  have rbase := r3.seq (r4.seq (r5.seq (r6.seq (r7.seq r8))))
  have pbase8 : s8.vars "metric.base.n" = qs[a].num ∧ s8.vars "metric.base.d" = qs[a].den := by
    simpa only [String.reduceAppend,rbase.frame_var "metric.base.n" (by decide),rbase.frame_var "metric.base.d" (by decide)] using p2.2
  obtain ⟨s9,r9,p9⟩ := restore_spec B qs[a] (by omega) (han.trans_lt hH) (had.trans_lt hH) s8 pbase8
  have pright9 : s9.vars "right.s" = 0 ∧ s9.vars "right.n" = (qs[b]+qs[c]).num ∧
      s9.vars "right.d" = (qs[b]+qs[c]).den := by
    simpa only [String.reduceAppend,r9.frame_var "right.s" (by decide),r9.frame_var "right.n" (by decide),
      r9.frame_var "right.d" (by decide)] using p8
  obtain ⟨τ,r10,p10⟩ := RamMinimum.command_spec B (2*H) qs[a] (qs[b]+qs[c]) hB
    (by omega) (by omega) hsn hsd s9 ⟨p9.1,p9.2.1,p9.2.2,pright9⟩
  exact ⟨τ,(r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq r10))))))))).mono
    (by omega),p10⟩

end Lax455465Proofs.RamMinPlus
