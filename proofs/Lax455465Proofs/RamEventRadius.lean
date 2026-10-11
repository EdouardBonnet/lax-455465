import Lax455465Proofs.RamUnsignedScalar
import Lax455465Proofs.RamUnsignedBuffer
import Lax455465Proofs.RamRootDistances
import Lax455465Proofs.RamMinimum

namespace Lax455465Proofs.RamEventRadius

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRational RamVirtualState
open scoped NNRat

def command (outward : Bool) : Com := .seq (load "round.delta")
  (.seq (RamUnsignedArithmetic.copy "left") (.seq (RamUnsignedBuffer.read (RamRootDistances.array outward) "radius.v")
    (.seq (RamUnsignedArithmetic.copy "right") RamMinimum.command)))

/-- Clip an actual vertex-distance event to the stored radius budget. Both
source distances and the budget remain available for the next candidate. -/
theorem command_spec (B M : ℕ) {n : ℕ} (outward : Bool) (distance : Fin n → ℚ≥0)
    (delta : ℚ≥0) (v : Fin n) (hB : 2*M^2+3 < B) (hindex : 2*n+2 < B)
    (hdn : delta.num ≤ M) (hdd : delta.den ≤ M)
    (hvn : (distance v).num ≤ M) (hvd : (distance v).den ≤ M) :
    Spec B (fun σ => Stored "round.delta" delta σ ∧
      Prefix (RamUnsignedBuffer.encode (List.ofFn distance)) (RamRootDistances.array outward) σ ∧ σ.vars "radius.v"=v.val)
      (command outward) (fun _ τ => FractionOutput ((min delta (distance v) : ℚ≥0) : ℚ) τ) 82 := by
  have hM : M < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  let qs := List.ofFn distance
  have hi : v.val < qs.length := by simpa only [qs,List.length_ofFn] using v.isLt
  have hv : qs[v.val] = distance v := by simp only [qs,List.getElem_ofFn,Fin.eta]
  rintro σ ⟨hδ,hsource,hindexσ⟩
  obtain ⟨ν,rl,pl⟩ := load_spec B "round.delta" delta h1 (hdn.trans_lt hM) (hdd.trans_lt hM) (by decide) σ hδ
  obtain ⟨μ,rc,pc⟩ := RamUnsignedArithmetic.copy_spec B delta "left" h1 (hdn.trans_lt hM) (hdd.trans_lt hM) (by decide) ν pl
  have hsourceμ : Prefix (RamUnsignedBuffer.encode qs) (RamRootDistances.array outward) μ := by
    have rr := rl.seq rc
    simpa only [Prefix,qs,rr.frame_arr (RamRootDistances.array outward) (by change RamRootDistances.array outward ∉ ([] : List String); simp)] using hsource
  have hvμ : μ.vars "radius.v"=v.val := by
    have rr := rl.seq rc
    exact (rr.frame_var _ (by decide)).trans hindexσ
  obtain ⟨ξ,rv,pv⟩ := RamUnsignedBuffer.read_spec B (RamRootDistances.array outward) "radius.v" qs v.val hi (by omega) (by have := v.isLt; omega)
    (by rw [hv]; exact hvn.trans_lt hM) (by rw [hv]; exact hvd.trans_lt hM) (by decide) μ ⟨hsourceμ,hvμ⟩
  obtain ⟨η,rr,pr⟩ := RamUnsignedArithmetic.copy_spec B (distance v) "right" h1 (hvn.trans_lt hM) (hvd.trans_lt hM) (by decide) ξ (by simpa only [hv] using pv.1)
  have pleft : η.vars "left.s"=0 ∧ η.vars "left.n"=delta.num ∧ η.vars "left.d"=delta.den := by
    have r := rv.seq rr
    simpa only [r.frame_var "left.s" (by cases outward <;> decide),r.frame_var "left.n" (by cases outward <;> decide),
      r.frame_var "left.d" (by cases outward <;> decide),String.reduceAppend] using pc
  obtain ⟨τ,rm,pm⟩ := RamMinimum.command_spec B M delta (distance v) hB hdn hdd hvn hvd η
    ⟨pleft.1,pleft.2.1,pleft.2.2,by simpa only [String.reduceAppend] using pr⟩
  exact ⟨τ,rl.seq (rc.seq (rv.seq (rr.seq rm))),by simpa only [NNRat.coe_min] using pm⟩

end Lax455465Proofs.RamEventRadius
