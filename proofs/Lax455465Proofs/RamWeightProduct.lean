import Lax455465Proofs.RamUnsignedBuffer
import Lax455465Proofs.RamFrames

namespace Lax455465Proofs.RamWeightProduct

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

def copyLeft : Com := .seq (.assign "left.s" (.var "rat.s"))
  (.seq (.assign "left.n" (.var "rat.n")) (.assign "left.d" (.var "rat.d")))
def copyRight : Com := .seq (.assign "right.s" (.var "rat.s"))
  (.seq (.assign "right.n" (.var "rat.n")) (.assign "right.d" (.var "rat.d")))

def command : Com := .seq (RamUnsignedBuffer.read "flow.weights" "lp.s")
  (.seq copyLeft (.seq (RamUnsignedBuffer.read "flow.weights" "lp.t")
    (.seq copyRight multiplyFraction)))

/-- The only nonconstant matrix coefficients are products of two runtime
weights. This command reads both weights and reduces their exact product. -/
theorem command_spec (B M : ℕ) (weights : List ℚ≥0) (s t : ℕ)
    (hs : s < weights.length) (ht : t < weights.length)
    (hB : 2*M^2+3 < B) (hsi : 2*s+1 < B) (hti : 2*t+1 < B)
    (hsn : weights[s].num ≤ M) (hsd : weights[s].den ≤ M)
    (htn : weights[t].num ≤ M) (htd : weights[t].den ≤ M) :
    Spec B (fun σ => Prefix (RamUnsignedBuffer.encode weights) "flow.weights" σ ∧
      σ.vars "lp.s" = s ∧ σ.vars "lp.t" = t) command
      (fun _ τ => FractionOutput ((weights[s] : ℚ) * (weights[t] : ℚ)) τ)
      (36*(weights[s].den*weights[t].den).size+104) := by
  have hM : M < B := by nlinarith
  have h2 : 2 < B := by nlinarith
  have hreadS := RamUnsignedBuffer.read_spec B "flow.weights" "lp.s" weights s hs h2 hsi
    (hsn.trans_lt hM) (hsd.trans_lt hM) (by decide)
  have hreadT := RamUnsignedBuffer.read_spec B "flow.weights" "lp.t" weights t ht h2 hti
    (htn.trans_lt hM) (htd.trans_lt hM) (by decide)
  have hleft : Spec B (fun σ => FractionOutput (weights[s] : ℚ) σ ∧ σ.vars "rat.s" = 0)
      copyLeft (fun _ τ => τ.vars "left.s" = 0 ∧ τ.vars "left.n" = weights[s].num ∧
        τ.vars "left.d" = weights[s].den) 6 := by
    rintro σ ⟨⟨hv,hn,hd,hsg⟩,hzero⟩
    have hns : σ.vars "rat.n" = weights[s].num := by simpa only [NNRat.natAbs_num_coe] using hn
    have hds : σ.vars "rat.d" = weights[s].den := by simpa only [NNRat.den_coe] using hd
    have hnB := hsn.trans_lt hM
    have hdB := hsd.trans_lt hM
    run_vcg
    all_goals simp_all
  have hright : Spec B (fun σ => FractionOutput (weights[t] : ℚ) σ ∧ σ.vars "rat.s" = 0)
      copyRight (fun _ τ => τ.vars "right.s" = 0 ∧ τ.vars "right.n" = weights[t].num ∧
        τ.vars "right.d" = weights[t].den) 6 := by
    rintro σ ⟨⟨hv,hn,hd,hsg⟩,hzero⟩
    have hns : σ.vars "rat.n" = weights[t].num := by simpa only [NNRat.natAbs_num_coe] using hn
    have hds : σ.vars "rat.d" = weights[t].den := by simpa only [NNRat.den_coe] using hd
    have hnB := htn.trans_lt hM
    have hdB := htd.trans_lt hM
    run_vcg
    all_goals simp_all
  have hmul := multiplyFraction_spec B M 0 weights[s].num weights[s].den
    0 weights[t].num weights[t].den hB (by omega) (by omega) hsn hsd htn htd
      weights[s].den_pos weights[t].den_pos
  have hvs : fractionValue 0 weights[s].num weights[s].den = (weights[s] : ℚ) := by
    simp only [fractionValue, show ¬(0:ℕ)=1 by decide,if_false]
    exact congrArg (fun q : ℚ≥0 => (q : ℚ)) (NNRat.num_div_den weights[s])
  have hvt : fractionValue 0 weights[t].num weights[t].den = (weights[t] : ℚ) := by
    simp only [fractionValue, show ¬(0:ℕ)=1 by decide,if_false]
    exact congrArg (fun q : ℚ≥0 => (q : ℚ)) (NNRat.num_div_den weights[t])
  rintro σ ⟨hp,hσs,hσt⟩
  obtain ⟨ν,hrS,hsPost⟩ := hreadS σ ⟨hp,hσs⟩
  obtain ⟨μ,hcpS,hleftPost⟩ := hleft ν hsPost
  have hpμ : Prefix (RamUnsignedBuffer.encode weights) "flow.weights" μ := by
    simpa only [Prefix,hcpS.frame_arr "flow.weights" (by simp [copyLeft,Com.warrs]),
      hrS.frame_arr "flow.weights" (by simp [RamUnsignedBuffer.read,Com.warrs])] using hp
  have htμ : μ.vars "lp.t" = t :=
    (hcpS.frame_var "lp.t" (by simp [copyLeft,Com.wvars])).trans
      ((hrS.frame_var "lp.t" (by simp [RamUnsignedBuffer.read,Com.wvars])).trans hσt)
  obtain ⟨ρ,hrT,htPost⟩ := hreadT μ ⟨hpμ,htμ⟩
  obtain ⟨κ,hcpT,hrightPost⟩ := hright ρ htPost
  have hls : κ.vars "left.s" = 0 :=
    (hcpT.frame_var "left.s" (by simp [copyRight,Com.wvars])).trans
      ((hrT.frame_var "left.s" (by simp [RamUnsignedBuffer.read,Com.wvars])).trans hleftPost.1)
  have hln : κ.vars "left.n" = weights[s].num :=
    (hcpT.frame_var "left.n" (by simp [copyRight,Com.wvars])).trans
      ((hrT.frame_var "left.n" (by simp [RamUnsignedBuffer.read,Com.wvars])).trans hleftPost.2.1)
  have hld : κ.vars "left.d" = weights[s].den :=
    (hcpT.frame_var "left.d" (by simp [copyRight,Com.wvars])).trans
      ((hrT.frame_var "left.d" (by simp [RamUnsignedBuffer.read,Com.wvars])).trans hleftPost.2.2)
  obtain ⟨τ,hrMul,hpost⟩ := hmul κ ⟨hls,hln,hld,hrightPost⟩
  exact ⟨τ,(hrS.seq (hcpS.seq (hrT.seq (hcpT.seq hrMul)))).mono (by omega),
    by simpa only [hvs,hvt] using hpost⟩

end Lax455465Proofs.RamWeightProduct
