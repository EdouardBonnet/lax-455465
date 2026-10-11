import Lax455465Proofs.RamUnsignedBuffer
import Lax455465Proofs.RamWordBuffer

namespace Lax455465Proofs.RamUnsignedEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

def command (array cursor : String) : Com := .seq (RamWordBuffer.append array cursor (.var "rat.n"))
  (RamWordBuffer.append array cursor (.var "rat.d"))

/-- Store a normalized nonnegative rational as its two canonical words. -/
theorem command_spec (B : ℕ) (array cursor : String) (q : ℚ≥0) (words : List ℕ) (h1 : 1 < B)
    (hn : q.num < B) (hd : q.den < B) (hlen : words.length+2 < B) (hfresh : cursor ≠ "rat.d") :
    Spec B (fun σ => FractionOutput (q : ℚ) σ ∧ Prefix words array σ ∧
      σ.vars cursor = words.length ∧ words.length+1 < (σ.arrs array).length) (command array cursor)
      (fun _ τ => Prefix (words ++ Lax455465.RationalEncoding.encodeRational q) array τ ∧
        τ.vars cursor = words.length+2) 14 := by
  rintro σ ⟨hf,hp,hpos,hroom⟩
  have hnum : σ.vars "rat.n" = q.num := by simpa only [NNRat.natAbs_num_coe] using hf.2.1
  have hden : σ.vars "rat.d" = q.den := by simpa only [NNRat.den_coe] using hf.2.2.1
  have hfirst := RamFrames.keep_scalar
    (RamWordBuffer.append_spec B array cursor words q.num (.var "rat.n") h1 (by omega))
    "rat.d" q.den (by simp [RamWordBuffer.append,Com.wvars,Ne.symm hfresh])
  obtain ⟨ν,hrn,hnPost⟩ := hfirst σ ⟨⟨hp,hpos,by omega,
    by rw [evalB_var_iff]; exact ⟨hnum.symm,hnum ▸ hn⟩⟩,hden⟩
  have hroomν : (words ++ [q.num]).length < (ν.arrs array).length := by
    rw [RamFrames.run_array_length hrn array,List.length_append,List.length_singleton]; exact hroom
  obtain ⟨τ,hrd,hdPost⟩ := RamWordBuffer.append_spec B array cursor (words ++ [q.num]) q.den (.var "rat.d") h1
    (by simp only [List.length_append,List.length_singleton]; omega) ν
      ⟨hnPost.1.1,by simpa only [List.length_append,List.length_singleton] using hnPost.1.2,hroomν,
        by rw [evalB_var_iff]; exact ⟨hnPost.2.symm,hnPost.2 ▸ hd⟩⟩
  refine ⟨τ,hrn.seq hrd,?_,?_⟩
  · simpa only [Lax455465.RationalEncoding.encodeRational,List.append_assoc,List.cons_append,List.nil_append] using hdPost.1
  · simpa only [List.length_append,List.length_singleton,Nat.add_assoc] using hdPost.2

end Lax455465Proofs.RamUnsignedEncoding
