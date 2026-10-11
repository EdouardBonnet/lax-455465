import Lax455465Proofs.RamScalarBinary
import Lax455465Proofs.RamTruncatedSubtract
import Lax455465Proofs.RegionVolume

namespace Lax455465Proofs.RamEdgePortion

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

/-- The unsigned part of an edge lying within a radius. -/
def value (length base radius : ℚ≥0) : ℚ≥0 := min length (RamTruncatedSubtract.value radius base)

theorem coe_value (length base radius : ℚ≥0) :
    (value length base radius : ℚ) = RegionVolume.edgePortion (length : ℚ) base radius := by
  rfl

def difference : Com := RamScalarBinary.command "portion.radius" "portion.base" RamTruncatedSubtract.command
def minimum : Com := RamScalarBinary.command "portion.length" "portion.diff" RamMinimum.command

def command : Com := .seq difference (.seq (save "portion.diff") minimum)

/-- Exact native clipped edge volume. Both saturation at the whole edge and
zero contribution before the tail event are computed by rational comparisons. -/
theorem command_spec (B M : ℕ) (length base radius : ℚ≥0) (hB : 2*M^2+3 < B)
    (hlN : length.num ≤ M) (hlD : length.den ≤ M)
    (hbN : base.num ≤ M) (hbD : base.den ≤ M)
    (hrN : radius.num ≤ M) (hrD : radius.den ≤ M)
    (hdN : (RamTruncatedSubtract.value radius base).num ≤ M)
    (hdD : (RamTruncatedSubtract.value radius base).den ≤ M) :
    Spec B (fun σ => Stored "portion.length" length σ ∧ Stored "portion.base" base σ ∧ Stored "portion.radius" radius σ)
      command (fun _ τ => FractionOutput (value length base radius : ℚ) τ)
      (36*(radius.den*base.den).size+244) := by
  have hM : M < B := by nlinarith
  rintro σ ⟨hl,hb,hr⟩
  obtain ⟨ν,rd,pd⟩ := RamScalarBinary.command_spec B M (36*(radius.den*base.den).size+142)
    radius base "portion.radius" "portion.base" RamTruncatedSubtract.command (RamTruncatedSubtract.value radius base : ℚ)
    hB hrN hrD hbN hbD (by decide) (by decide) (by decide)
    (RamTruncatedSubtract.command_spec B M radius base hB hrN hrD hbN hbD) σ ⟨hr,hb⟩
  obtain ⟨μ,rs,ps⟩ := save_spec B "portion.diff" (RamTruncatedSubtract.value radius base)
    (hdN.trans_lt hM) (hdD.trans_lt hM) (by decide) ν pd
  have hlμ : Stored "portion.length" length μ := by
    have rr := rd.seq rs
    simpa only [Stored,rr.frame_var "portion.length.n" (by decide),rr.frame_var "portion.length.d" (by decide),String.reduceAppend] using hl
  obtain ⟨τ,rm,pm⟩ := RamScalarBinary.command_spec B M 50 length (RamTruncatedSubtract.value radius base)
    "portion.length" "portion.diff" RamMinimum.command (min (length : ℚ) (RamTruncatedSubtract.value radius base : ℚ))
    hB hlN hlD hdN hdD (by decide) (by decide) (by decide)
    (RamMinimum.command_spec B M length (RamTruncatedSubtract.value radius base) hB hlN hlD hdN hdD) μ ⟨hlμ,ps⟩
  refine ⟨τ,(rd.seq (rs.seq rm)).mono (by omega),?_⟩
  exact pm

end Lax455465Proofs.RamEdgePortion
