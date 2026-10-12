import Lax455465Proofs.RamWordBuffer
import Lax455465Proofs.RamRoundingConstants
import Lax455465Proofs.RegionLoop

namespace Lax455465Proofs.RamRegionRecord
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open scoped NNRat

structure Entry (n : ℕ) where
  root : Fin n
  radius : ℚ≥0
  outward : Bool

def Entry.region {n : ℕ} (e : Entry n) : RegionLoop.Region n := ⟨e.root,e.radius,e.outward⟩
def Entry.words {n : ℕ} (e : Entry n) : List ℕ := [e.root.val,e.radius.num,e.radius.den,if e.outward then 1 else 0]
def words {n : ℕ} (history : List (Entry n)) : List ℕ := history.flatMap Entry.words
@[simp] theorem length_words {n : ℕ} (history : List (Entry n)) : (words history).length=4*history.length := by
  induction history with
  | nil => rfl
  | cons e history ih => simp [words,Entry.words] at *; omega

structure Input {n : ℕ} (history : List (Entry n)) (e : Entry n) (σ : Env) : Prop where
  data : Prefix (words history) "region.history" σ
  position : σ.vars "history.pos"=(words history).length
  root : σ.vars "region.root"=e.root.val
  radius : Stored "region.radius" e.radius σ
  outward : σ.vars "region.outward"=(if e.outward then 1 else 0)

def command : Com := .seq (RamWordBuffer.append "region.history" "history.pos" (.var "region.root"))
  (.seq (RamWordBuffer.append "region.history" "history.pos" (.var "region.radius.n"))
    (.seq (RamWordBuffer.append "region.history" "history.pos" (.var "region.radius.d"))
      (RamWordBuffer.append "region.history" "history.pos" (.var "region.outward"))))

/-- Append an actual selected region to the runtime history, preserving all
previous records and recording its exact canonical rational radius. -/
theorem command_spec (B : ℕ) {n : ℕ} (history : List (Entry n)) (e : Entry n)
    (hlen : 4*history.length+4<B) (hroot : n<B) (hnum : e.radius.num<B) (hden : e.radius.den<B) :
    Spec B (fun σ => Input history e σ ∧ 4*history.length+4≤(σ.arrs "region.history").length)
      command (fun _ τ => Prefix (words (history++[e])) "region.history" τ ∧
        τ.vars "history.pos"=4*(history.length+1)) 28 := by
  have h1 : 1<B := by omega
  let ws := words history
  rintro σ ⟨hσ,hroom⟩
  obtain ⟨σ1,r1,p1⟩ := RamWordBuffer.append_spec B "region.history" "history.pos" ws e.root.val (.var "region.root")
    h1 (by simp only [ws,length_words]; omega) σ
    ⟨hσ.data,hσ.position,by simp only [ws,length_words]; omega,
      by rw [evalB_var_iff]; exact ⟨hσ.root.symm,hσ.root ▸ e.root.isLt.trans hroot⟩⟩
  obtain ⟨σ2,r2,p2⟩ := RamWordBuffer.append_spec B "region.history" "history.pos" (ws++[e.root.val]) e.radius.num (.var "region.radius.n")
    h1 (by simp only [List.length_append,List.length_singleton,ws,length_words]; omega) σ1
    ⟨p1.1,by simpa only [List.length_append,List.length_singleton] using p1.2,
      by rw [RamFrames.run_array_length r1 "region.history"]; simp only [List.length_append,List.length_singleton,ws,length_words]; omega,
      by rw [evalB_var_iff]; exact ⟨((r1.frame_var _ (by decide)).trans hσ.radius.1).symm,
        ((r1.frame_var _ (by decide)).trans hσ.radius.1) ▸ hnum⟩⟩
  have r12 := r1.seq r2
  obtain ⟨σ3,r3,p3⟩ := RamWordBuffer.append_spec B "region.history" "history.pos" ((ws++[e.root.val])++[e.radius.num]) e.radius.den (.var "region.radius.d")
    h1 (by simp only [List.length_append,List.length_singleton,ws,length_words]; omega) σ2
    ⟨p2.1,by simpa only [List.length_append,List.length_singleton] using p2.2,
      by rw [RamFrames.run_array_length r12 "region.history"]; simp only [List.length_append,List.length_singleton,ws,length_words]; omega,
      by rw [evalB_var_iff]; exact ⟨((r12.frame_var _ (by decide)).trans hσ.radius.2).symm,
        ((r12.frame_var _ (by decide)).trans hσ.radius.2) ▸ hden⟩⟩
  have r123 := r1.seq (r2.seq r3)
  obtain ⟨τ,r4,p4⟩ := RamWordBuffer.append_spec B "region.history" "history.pos" (((ws++[e.root.val])++[e.radius.num])++[e.radius.den]) (if e.outward then 1 else 0) (.var "region.outward")
    h1 (by simp only [List.length_append,List.length_singleton,ws,length_words]; omega) σ3
    ⟨p3.1,by simpa only [List.length_append,List.length_singleton] using p3.2,
      by rw [RamFrames.run_array_length r123 "region.history"]; simp only [List.length_append,List.length_singleton,ws,length_words]; omega,
      by rw [evalB_var_iff]; refine ⟨((r123.frame_var _ (by decide)).trans hσ.outward).symm,?_⟩
         rw [(r123.frame_var _ (by decide)).trans hσ.outward]; split_ifs <;> omega⟩
  refine ⟨τ,r1.seq (r2.seq (r3.seq r4)),?_,?_⟩
  · simpa only [words,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,Entry.words,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,ws] using p4.1
  · simp only [List.length_append,List.length_singleton,ws,length_words] at p4
    omega

end Lax455465Proofs.RamRegionRecord
