import Lax455465Proofs.RamLpRationalRead
import Lax455465Proofs.RamUnsignedEncoding
import Lax455465Proofs.RamVectorEncoding

namespace Lax455465Proofs.RamCertificateVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

/-- Signed LP encoding of a nonnegative vector. -/
def source (qs : List ℚ≥0) : List ℕ :=
  qs.flatMap fun (q : ℚ≥0) => Lax109476.RationalEncoding.encodeRational (q : ℚ)

@[simp] theorem length_source (qs : List ℚ≥0) : (source qs).length = 3*qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [source,Lax109476.RationalEncoding.encodeRational] at *; omega

theorem source_split (qs : List ℚ≥0) (i : ℕ) (hi : i < qs.length) :
    source qs = source (qs.take i) ++
      (Lax109476.RationalEncoding.encodeRational (qs[i] : ℚ) ++ source (qs.drop (i+1))) := by
  have hsplit := congrArg source (List.take_append_drop (i+1) qs)
  rw [List.take_succ_eq_append_getElem hi] at hsplit
  simpa only [source,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.append_assoc] using hsplit.symm

def step (array : String) : Com := .seq RamLpRationalRead.command
  (.seq (RamUnsignedEncoding.command array "cert.position")
    (.assign "cert.i" (.add (.var "cert.i") (.lit 1))))

def command (array : String) : Com := .seq (.assign "cert.position" (.lit 0))
  (.seq (.assign "cert.i" (.lit 0))
    (.while (.lt (.var "cert.i") (.var "cert.count")) (step array)))

def Invariant (front tail : List ℕ) (qs : List ℚ≥0) (array : String) (σ : Env) : Prop :=
  Prefix (front ++ (source qs ++ tail)) "vm.output" σ ∧
    σ.vars "cert.count" = qs.length ∧ σ.vars "cert.i" ≤ qs.length ∧
    σ.vars "cert.cursor" = front.length+3*σ.vars "cert.i" ∧
    Prefix (RamUnsignedBuffer.encode (qs.take (σ.vars "cert.i"))) array σ ∧
    σ.vars "cert.position" = 2*σ.vars "cert.i" ∧ 2*qs.length < (σ.arrs array).length

theorem step_spec (B : ℕ) (front tail : List ℕ) (qs : List ℚ≥0) (array : String)
    (h3 : 3 < B) (hlen : front.length+3*qs.length+3 < B)
    (hnum : ∀ q ∈ qs, q.num < B) (hden : ∀ q ∈ qs, q.den < B)
    (harray : array ≠ "vm.output") :
    Spec B (fun σ => Invariant front tail qs array σ ∧ σ.vars "cert.i" < qs.length)
      (step array) (fun σ τ => Invariant front tail qs array τ ∧
        τ.vars "cert.i" = σ.vars "cert.i"+1) 35 := by
  rintro σ ⟨⟨hp,hcount,hi,hcursor,htarget,hpos,hroom⟩,hlt⟩
  let i := σ.vars "cert.i"
  have hi' : i < qs.length := hlt
  have hi0 : i ≤ qs.length := hi
  let front' := front ++ source (qs.take i)
  let tail' := source (qs.drop (i+1)) ++ tail
  have hfront : front'.length = front.length+3*i := by
    simp only [front',List.length_append,length_source,List.length_take,Nat.min_eq_left hi0]
  have hsource : front ++ (source qs ++ tail) =
      front' ++ (Lax109476.RationalEncoding.encodeRational (qs[i] : ℚ) ++ tail') := by
    rw [source_split qs i hi']; simp only [front',tail',List.append_assoc]
  have hnB := hnum qs[i] (List.getElem_mem hi')
  have hdB := hden qs[i] (List.getElem_mem hi')
  have hlength : (RamUnsignedBuffer.encode (qs.take i)).length = 2*i := by
    simp only [RamUnsignedBuffer.length_encode,List.length_take,Nat.min_eq_left hi0]
  obtain ⟨ν,hread,hreadPost⟩ := RamLpRationalRead.command_spec B (qs[i] : ℚ) front' tail' h3
    (by rw [hfront]; omega) (by simpa only [NNRat.natAbs_num_coe] using hnB)
    (by simpa only [NNRat.den_coe] using hdB) σ ⟨by rwa [←hsource],by rwa [hfront]⟩
  have htν : Prefix (RamUnsignedBuffer.encode (qs.take i)) array ν := by
    simpa only [Prefix,hread.frame_arr array (by simp [RamLpRationalRead.command,Com.warrs])] using htarget
  have hposν : ν.vars "cert.position" = 2*i := (hread.frame_var "cert.position" (by decide)).trans hpos
  have hiν : ν.vars "cert.i" = i := (hread.frame_var "cert.i" (by decide)).trans rfl
  have hcν : ν.vars "cert.count" = qs.length := (hread.frame_var "cert.count" (by decide)).trans hcount
  have hroomν : 2*qs.length < (ν.arrs array).length := by rwa [RamFrames.run_array_length hread array]
  obtain ⟨μ,hemit,hemitPost⟩ := RamUnsignedEncoding.command_spec B array "cert.position" qs[i]
    (RamUnsignedBuffer.encode (qs.take i)) (by omega) hnB hdB
    (by rw [hlength]; omega) (by decide) ν ⟨hreadPost.1,htν,by rwa [hlength],by rw [hlength]; omega⟩
  have hpμ : Prefix (front ++ (source qs ++ tail)) "vm.output" μ := by
    simpa only [Prefix,hemit.frame_arr "vm.output" (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,
      Com.warrs,Ne.symm harray]),hread.frame_arr "vm.output" (by decide)] using hp
  have hcurμ : μ.vars "cert.cursor" = front.length+3*i+3 := by
    simpa only [hemit.frame_var "cert.cursor" (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]),hfront] using hreadPost.2
  have hcμ : μ.vars "cert.count" = qs.length := (hemit.frame_var "cert.count" (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars])).trans hcν
  have hiμ : μ.vars "cert.i" = i := (hemit.frame_var "cert.i" (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars])).trans hiν
  have htμ : Prefix (RamUnsignedBuffer.encode (qs.take (i+1))) array μ := by
    rw [List.take_succ_eq_append_getElem hi']
    simpa only [RamUnsignedBuffer.encode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil] using hemitPost.1
  have hposμ : μ.vars "cert.position" = 2*(i+1) := by rw [hlength] at hemitPost; omega
  have hroomμ : 2*qs.length < (μ.arrs array).length := by rwa [RamFrames.run_array_length hemit array]
  have hiNext : i+1 < B := by omega
  have hinc : Run B (.assign "cert.i" (.add (.var "cert.i") (.lit 1))) μ (μ.setVar "cert.i" (i+1)) 4 :=
    Run.assign (evalB_bin (op := .add) (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega : i < B)⟩)
      (evalB_lit (by omega)) hiNext)
  refine ⟨μ.setVar "cert.i" (i+1),hread.seq (hemit.seq hinc),?_,?_⟩
  · refine ⟨?_,?_,by simpa only [vars_setVar,String.reduceEq,if_true] using (Nat.succ_le_iff.mpr hi'),?_,?_,?_,?_⟩
    · simpa only [Prefix,arrs_setVar] using hpμ
    · simpa only [vars_setVar,String.reduceEq,if_false] using hcμ
    · simpa only [vars_setVar,String.reduceEq,if_false,if_true] using
        hcurμ.trans (by omega : front.length+3*i+3 = front.length+3*(i+1))
    · simpa only [Prefix,arrs_setVar,vars_setVar,String.reduceEq,if_true] using htμ
    · simpa only [vars_setVar,String.reduceEq,if_false,if_true] using hposμ
    · simpa only [arrs_setVar] using hroomμ
  · simp [i]

theorem command_spec (B : ℕ) (front tail : List ℕ) (qs : List ℚ≥0) (array : String)
    (h3 : 3 < B) (hlen : front.length+3*qs.length+3 < B)
    (hnum : ∀ q ∈ qs, q.num < B) (hden : ∀ q ∈ qs, q.den < B)
    (harray : array ≠ "vm.output") :
    Spec B (fun σ => Prefix (front ++ (source qs ++ tail)) "vm.output" σ ∧
      σ.vars "cert.count" = qs.length ∧ σ.vars "cert.cursor" = front.length ∧
      2*qs.length < (σ.arrs array).length) (command array)
      (fun _ τ => Prefix (front ++ (source qs ++ tail)) "vm.output" τ ∧
        τ.vars "cert.cursor" = front.length+3*qs.length ∧ Prefix (RamUnsignedBuffer.encode qs) array τ ∧
        τ.vars "cert.position" = 2*qs.length) (39*qs.length+8) := by
  have hcount : qs.length < B := by omega
  have hscan := Spec.forRangeZero "cert.i" "cert.count" (Invariant front tail qs array)
    qs.length 35 hcount (fun _ h => h.2.2.1) (fun _ h => h.2.1)
      (step_spec B front tail qs array h3 hlen hnum hden harray)
  rintro σ ⟨hp,hcountσ,hcursorσ,hroom⟩
  let ν := σ.setVar "cert.position" 0
  have hzero : Run B (.assign "cert.position" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have hinit : Invariant front tail qs array (ν.setVar "cert.i" 0) := by
    refine ⟨?_,?_,by simp,?_,?_,?_,?_⟩
    · simpa only [Prefix,ν,arrs_setVar] using hp
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hcountσ
    · simpa only [ν,vars_setVar,String.reduceEq,if_false,if_true,Nat.mul_zero,Nat.add_zero] using hcursorσ
    · intro i hi
      simp only [vars_setVar,if_true,List.take_zero,RamUnsignedBuffer.encode,List.flatMap_nil,List.length_nil] at hi
      omega
    · simp only [ν,vars_setVar,String.reduceEq,if_false,if_true,Nat.mul_zero]
    · simpa only [ν,arrs_setVar] using hroom
  obtain ⟨τ,hr,hpost⟩ := hscan ν hinit
  refine ⟨τ,(hzero.seq hr).mono (by omega),hpost.1.1,?_,?_,?_⟩
  · simpa only [hpost.2] using hpost.1.2.2.2.1
  · simpa only [hpost.2,List.take_length] using hpost.1.2.2.2.2.1
  · simpa only [hpost.2] using hpost.1.2.2.2.2.2.1

end Lax455465Proofs.RamCertificateVector
