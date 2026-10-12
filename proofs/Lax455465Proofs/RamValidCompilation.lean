import Lax455465Proofs.RamAutomaticLayout
import Lax455465Proofs.RamValidFlowCut

set_option maxRecDepth 16384
namespace Lax455465Proofs.RamValidCompilation
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding RamFlowData

/-- Logical zero-array extents are proof bookkeeping; the compiler starts
from the registered RAM's standard zero memory. -/
def extent {n : ℕ} (TB : Polynomial ℕ) (kind : EdgeKind) (I : RationalInstance n) : ℕ :=
  (encodeInput kind I).length+RamFlowLp.wordLength n+
    (Lax109476.RationalEncoding.encodeProgram (DirectedFlowLP.program I)).length+
    TB.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (DirectedFlowLP.program I)))+
    2*n+2*(n*n)+2*columns n+2*rows n+
    ((RamRegionInvariant.extents n (RamRoundingInit.support I.weight)).map Prod.snd).sum+1

theorem room {n : ℕ} (TB : Polynomial ℕ) (kind : EdgeKind) (I : RationalInstance n) :
    RamRegionInvariant.Room n (RamRoundingInit.support I.weight)
      (initEnv (fun _ => extent TB kind I) ((encodeInput kind I).length::encodeInput kind I)) := by
  intro a count hc
  have hmem : count ∈ (RamRegionInvariant.extents n (RamRoundingInit.support I.weight)).map Prod.snd :=
    List.mem_map.mpr ⟨(a,count),hc,rfl⟩
  have hs := List.single_le_sum (fun x hx => Nat.zero_le x) count hmem
  simp only [initEnv,List.length_replicate]
  dsimp [extent]
  omega

theorem input_fits (xs : List ℕ) (v : ℕ) (hv : bitSize xs+1 ≤ v) :
    ∀ a∈xs.length::xs,a < 2^v := by
  intro a ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl | ha
  · have hlen := WordSize.length_le xs
    exact (show xs.length < 2^(bitSize xs+1) from lt_of_le_of_lt hlen
      (by have := Nat.lt_two_pow_self (n := bitSize xs+1); omega)).trans_le
      (Nat.pow_le_pow_right (by decide) hv)
  · exact (WordSize.member_bound xs a ha).trans_le (Nat.pow_le_pow_right (by decide) (by omega))

set_option maxHeartbeats 3200000 in
/-- Compile the complete valid-input algorithm to one fixed program of the
registered word RAM, with polynomial resources at every sufficient word width.
The same certificate is returned at all those widths. -/
theorem exists_program :
    ∃ (p : Lax808846.Ram.Program) (WB TB : Polynomial ℕ),
      ∀ {n : ℕ} (kind : EdgeKind) (I : RationalInstance n),
        (kind=.undirected → I.network.IsUndirected) → 2 ≤ supportCount I.weights →
        ∃ certificate : Lax455465.FlowCutCertificate.Certificate n,
          Lax455465.FlowCutCertificate.IsValid kind I 512 certificate ∧
          ∀ W : ℕ, WB.eval (bitSize (encodeInput kind I)) ≤ W →
            ∃ t ≤ TB.eval (bitSize (encodeInput kind I)),
              Lax808846.Ram.RunsTo W p ((encodeInput kind I).length::encodeInput kind I)
                (Lax455465.FlowCutCertificate.encodeCertificate certificate) t := by
  obtain ⟨c,T,WB,sourceTime,hcorrect⟩ := RamValidFlowCut.exists_program
  let layout := RamAutomaticLayout.layout c
  refine ⟨compileProgram layout c,WB+Polynomial.X+Polynomial.C (2+RamTransfer.layoutAllowance layout),
    Polynomial.C layout.const*T+1,?_⟩
  intro n kind I hsym hp
  let L := bitSize (encodeInput kind I)
  let v := WB.eval L+L+2
  let σ := initEnv (fun _ => extent sourceTime kind I) ((encodeInput kind I).length::encodeInput kind I)
  have hE := room sourceTime kind I
  have hcut : RamRegionCut.Room n σ := by
    constructor
    · intro a ha
      simp only [σ,initEnv,List.length_replicate]
      dsimp [extent]
      omega
    · simp only [σ,initEnv,List.length_replicate]
      dsimp [extent]
      omega
    · simp only [σ,initEnv,List.length_replicate]
      dsimp [extent]
      omega
  have hrun := hcorrect kind I hsym hp v (by dsimp [v,L]; omega)
  obtain ⟨τ,rr,cert,hvalid,hout⟩ := hrun σ (by
    refine ⟨rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hE,hcut,?_,rfl⟩
    all_goals simp only [σ,initEnv,List.length_replicate]; dsimp [extent]; omega)
  refine ⟨cert,hvalid,?_⟩
  intro W hW
  have hv : 0 < v := by dsimp [v]; omega
  have hfit : v+RamTransfer.layoutAllowance layout ≤ W := by
    simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,v,L,Nat.add_assoc] using hW
  obtain ⟨k,hk,hbs⟩ := rr
  obtain ⟨t,ht,hr⟩ := Lax808846Proofs.Simulation.compileProgram_runsTo
    (RamTransfer.layout_fits hv hfit) (RamAutomaticLayout.layout_ok c)
    (input_fits (encodeInput kind I) v (by dsimp [v,L]; omega)) hbs
  refine ⟨t,?_,by simpa only [hout] using hr⟩
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_one] using
    ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_left layout.const hk) 1)

end Lax455465Proofs.RamValidCompilation
