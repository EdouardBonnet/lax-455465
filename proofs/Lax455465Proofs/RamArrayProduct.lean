import Lax455465Proofs.RamUnsignedBuffer
import Lax455465Proofs.RamUnsignedArithmetic

namespace Lax455465Proofs.RamArrayProduct

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

def command (leftArray rightArray : String) : Com := .seq (RamUnsignedBuffer.read leftArray "sum.i")
  (.seq (RamUnsignedArithmetic.copy "left") (.seq (RamUnsignedBuffer.read rightArray "sum.i")
    (.seq (RamUnsignedArithmetic.copy "right") multiplyFraction)))

/-- Exact coordinatewise product from two canonical unsigned buffers. All
input coordinates and the runtime index remain available to the enclosing sum. -/
theorem command_spec (B M : ℕ) (leftArray rightArray : String) (xs ys : List ℚ≥0) (i : ℕ)
    (hxi : i < xs.length) (hyi : i < ys.length) (hB : 2*M^2+3 < B) (hindex : 2*i+1 < B)
    (hxn : xs[i].num ≤ M) (hxd : xs[i].den ≤ M) (hyn : ys[i].num ≤ M) (hyd : ys[i].den ≤ M) :
    Spec B (fun σ => Prefix (RamUnsignedBuffer.encode xs) leftArray σ ∧
      Prefix (RamUnsignedBuffer.encode ys) rightArray σ ∧ σ.vars "sum.i" = i)
      (command leftArray rightArray)
      (fun _ τ => FractionOutput ((xs[i]*ys[i] : ℚ≥0) : ℚ) τ)
      (36*(xs[i].den*ys[i].den).size+104) := by
  have hM : M < B := by nlinarith
  have h2 : 2 < B := by nlinarith
  rintro σ ⟨hxp,hyp,hi⟩
  obtain ⟨ν,rx,px⟩ := RamUnsignedBuffer.read_spec B leftArray "sum.i" xs i hxi h2 hindex
    (hxn.trans_lt hM) (hxd.trans_lt hM) (by decide) σ ⟨hxp,hi⟩
  obtain ⟨μ,rl,pl⟩ := RamUnsignedArithmetic.copy_spec B xs[i] "left" (by omega)
    (hxn.trans_lt hM) (hxd.trans_lt hM) (by decide) ν px.1
  have hypμ : Prefix (RamUnsignedBuffer.encode ys) rightArray μ := by
    have rr := rx.seq rl
    simpa only [Prefix,rr.frame_arr rightArray (by change rightArray ∉ ([] : List String); simp)] using hyp
  have hiμ : μ.vars "sum.i" = i := by
    have rr := rx.seq rl
    exact (rr.frame_var "sum.i" (by simp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars])).trans hi
  obtain ⟨ξ,ry,py⟩ := RamUnsignedBuffer.read_spec B rightArray "sum.i" ys i hyi h2 hindex
    (hyn.trans_lt hM) (hyd.trans_lt hM) (by decide) μ ⟨hypμ,hiμ⟩
  obtain ⟨η,rr,pr⟩ := RamUnsignedArithmetic.copy_spec B ys[i] "right" (by omega)
    (hyn.trans_lt hM) (hyd.trans_lt hM) (by decide) ξ py.1
  have plη : η.vars "left.s" = 0 ∧ η.vars "left.n" = xs[i].num ∧ η.vars "left.d" = xs[i].den := by
    have run := ry.seq rr
    simpa only [run.frame_var "left.s" (by simp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]),
      run.frame_var "left.n" (by simp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]),
      run.frame_var "left.d" (by simp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]),String.reduceAppend] using pl
  obtain ⟨τ,rm,pm⟩ := multiplyFraction_spec B M 0 xs[i].num xs[i].den 0 ys[i].num ys[i].den
    hB (by omega) (by omega) hxn hxd hyn hyd xs[i].den_pos ys[i].den_pos η
    ⟨plη.1,plη.2.1,plη.2.2,by simpa only [String.reduceAppend] using pr⟩
  refine ⟨τ,(rx.seq (rl.seq (ry.seq (rr.seq rm)))).mono (by omega),?_⟩
  simpa only [RamUnsignedArithmetic.value,NNRat.coe_mul] using pm

end Lax455465Proofs.RamArrayProduct
