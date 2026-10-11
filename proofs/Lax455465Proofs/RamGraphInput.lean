import Lax455465Proofs.RamGraphHeader
import Lax455465Proofs.RamDecodeVector

namespace Lax455465Proofs.RamGraphInput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamFlowData
open Lax455465.RationalEncoding Lax455465.ProductNetwork
open scoped NNRat

def weightsSetup : Com := .seq (.assign "decode.count" (.var "lp.n"))
  (.assign "decode.cursor" (.lit 2))

def capacitySetup : Com := .assign "decode.count" (.var "lp.n2")

def weights : Com := RamDecodeVector.command "flow.weights" "flow.weightPosition"
def capacity : Com := RamDecodeVector.command "flow.capacities" "flow.capacityPosition"

def command : Com := .seq RamGraphHeader.command
  (.seq weightsSetup (.seq weights (.seq capacitySetup capacity)))

theorem weightsSetup_spec (B n : ℕ) (h2 : 2 < B) (hn : n < B) :
    Spec B (fun σ => σ.vars "lp.n" = n) weightsSetup
      (fun _ τ => τ.vars "decode.count" = n ∧ τ.vars "decode.cursor" = 2) 4 := by
  rintro σ hN
  run_vcg
  all_goals simp_all

theorem capacitySetup_spec (B n : ℕ) (hn2 : n*n < B) :
    Spec B (fun σ => σ.vars "lp.n2" = n*n) capacitySetup
      (fun _ τ => τ.vars "decode.count" = n*n) 2 := by
  rintro σ hN
  run_vcg
  all_goals simp_all

/-- Recover the source weights and capacities in canonical initialized
buffers and compute every construction dimension from the source header. -/
theorem command_spec (B K : ℕ) {n : ℕ} (kind : EdgeKind) (I : RationalInstance n)
    (h2 : 2 < B) (hn : n < B) (hn2 : n*n < B) (hn3 : (n*n)*n < B)
    (hr : rows n < B) (hc : columns n < B) (hm : rows n*columns n < B)
    (hlen : (encodeInput kind I).length+2 < B)
    (hwords : ∀ x ∈ encodeInput kind I, x < B)
    (hweightSize : ∀ u, (I.weight u).den.size ≤ K)
    (hcapacitySize : ∀ u v, (I.capacity u v).den.size ≤ K) :
    Spec B (fun σ => Prefix (encodeInput kind I) "input.data" σ ∧
      2*n < (σ.arrs "flow.weights").length ∧ 2*(n*n) < (σ.arrs "flow.capacities").length) command
      (fun _ τ => Data I τ ∧ τ.vars "flow.kind" = RamGraphHeader.tag kind)
      ((36*K+56)*(n+n*n)+52) := by
  let ws := List.ofFn I.weight
  let cs := capacities I
  let front := [RamGraphHeader.tag kind,n]
  have hwl : ws.length = n := by simp [ws]
  have hcl : cs.length = n*n := by simp [cs,capacities]
  have hinput : encodeInput kind I = front ++ (RamUnsignedBuffer.encode ws ++ RamUnsignedBuffer.encode cs) :=
    FlowInputLists.input_eq kind I
  have hweightDen : ∀ q ∈ ws, q.den.size ≤ K := by
    intro q hq
    obtain ⟨u,rfl⟩ := List.mem_ofFn.mp hq
    exact hweightSize u
  have hcapacityDen : ∀ q ∈ cs, q.den.size ≤ K := by
    intro q hq
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hq
    exact hcapacitySize _ _
  have hwdecode := RamDecodeVector.command_spec B K front (RamUnsignedBuffer.encode cs) ws
    "flow.weights" "flow.weightPosition" h2 (by rwa [←hinput])
    (by rwa [←hinput]) hweightDen (by decide) (by decide) (by decide)
  let cfront := front ++ RamUnsignedBuffer.encode ws
  have hcinput : encodeInput kind I = cfront ++ (RamUnsignedBuffer.encode cs ++ []) := by
    simp only [hinput,cfront,List.append_nil,List.append_assoc]
  have hcdecode := RamDecodeVector.command_spec B K cfront [] cs
    "flow.capacities" "flow.capacityPosition" h2 (by rwa [←hcinput])
    (by rwa [←hcinput]) hcapacityDen (by decide) (by decide) (by decide)
  rintro σ ⟨hp,hwroom,hcroom⟩
  obtain ⟨ν,hheader,hheaderPost⟩ := RamGraphHeader.command_spec B kind I h2 hn hn2 hn3 hr hc hm σ hp
  obtain ⟨μ,hwsetup,hwsetupPost⟩ := weightsSetup_spec B n h2 hn ν hheaderPost.2.1.1
  have hdμ := RamGraphDimensions.frame hwsetup n hheaderPost.2.1 (by decide)
  have hpμ : Prefix (encodeInput kind I) "input.data" μ := by
    simpa only [Prefix,hwsetup.frame_arr "input.data" (by decide)] using hheaderPost.1
  have hwroomμ : 2*ws.length < (μ.arrs "flow.weights").length := by
    rw [hwl,RamFrames.run_array_length hwsetup "flow.weights",RamFrames.run_array_length hheader "flow.weights"]
    exact hwroom
  obtain ⟨ρ,hwrun,hwpost⟩ := hwdecode μ ⟨by rwa [←hinput],by simpa only [hwl] using hwsetupPost.1,by simpa [front] using hwsetupPost.2,hwroomμ⟩
  have hdρ := RamGraphDimensions.frame hwrun n hdμ (by decide)
  obtain ⟨κ,hcsetup,hcsetupPost⟩ := capacitySetup_spec B n hn2 ρ hdρ.2.1
  have hdκ := RamGraphDimensions.frame hcsetup n hdρ (by decide)
  have hpκ : Prefix (encodeInput kind I) "input.data" κ := by
    simpa only [Prefix,hcsetup.frame_arr "input.data" (by decide),hinput] using hwpost.1
  have hcurκ : κ.vars "decode.cursor" = cfront.length := by
    have hcur := (hcsetup.frame_var "decode.cursor" (by decide)).trans hwpost.2.1
    simpa only [cfront,List.length_append,RamUnsignedBuffer.length_encode,hwl,front,
      List.length_cons,List.length_nil] using hcur
  have hcroomκ : 2*cs.length < (κ.arrs "flow.capacities").length := by
    rw [hcl,RamFrames.run_array_length hcsetup "flow.capacities",RamFrames.run_array_length hwrun "flow.capacities",
      RamFrames.run_array_length hwsetup "flow.capacities",RamFrames.run_array_length hheader "flow.capacities"]
    exact hcroom
  obtain ⟨τ,hcrun,hcpost⟩ := hcdecode κ ⟨by rwa [←hcinput],by simpa only [hcl] using hcsetupPost,hcurκ,hcroomκ⟩
  have hdτ := RamGraphDimensions.frame hcrun n hdκ (by decide)
  have hwpτ : Prefix (RamUnsignedBuffer.encode ws) "flow.weights" τ := by
    simpa only [Prefix,hcrun.frame_arr "flow.weights" (by decide),hcsetup.frame_arr "flow.weights" (by decide)] using hwpost.2.2.1
  have hkτ : τ.vars "flow.kind" = RamGraphHeader.tag kind :=
    (hcrun.frame_var "flow.kind" (by decide)).trans ((hcsetup.frame_var "flow.kind" (by decide)).trans
      ((hwrun.frame_var "flow.kind" (by decide)).trans ((hwsetup.frame_var "flow.kind" (by decide)).trans hheaderPost.2.2)))
  refine ⟨τ,(hheader.seq (hwsetup.seq (hwrun.seq (hcsetup.seq hcrun)))).mono
    (by simp only [hwl,hcl]; ring_nf; omega),?_,hkτ⟩
  exact ⟨hdτ.1,hdτ.2.1,hdτ.2.2.1,hdτ.2.2.2.1,hdτ.2.2.2.2.1,hdτ.2.2.2.2.2,hwpτ,hcpost.2.2.1⟩

end Lax455465Proofs.RamGraphInput
