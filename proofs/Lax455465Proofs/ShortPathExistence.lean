import Lax455465Proofs.PathCertificateInterpretation
import Lax455465Proofs.ShortLayerSelection
import Lax455465Proofs.ShortRationalParameters

open scoped BigOperators NNRat NNReal
namespace Lax455465Proofs.ShortPathExistence
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax455465.ConcurrentFlow
open Lax455465.ShortPathFlow LayeredFlowLP LayeredFlowFeasibility

/-- The mathematical short-path flow theorem, with explicit rational
certificates and a polynomial bound on the number of path records. -/
theorem certificate_exists {n : ℕ} (I : RationalInstance n)
    (hI : I.network.IsUndirected) (hw : ∀ v,I.weight v=1) (hn : 2 ≤ n)
    (hS : 0 < sparsestCut I.network (uniformWeight n)) :
    ∃ c : FlowCertificate n,
      IsConcurrentFlow .undirected I.network (uniformWeight n) (c.value : ℝ≥0) c.flow ∧
      (sparsestCut I.network (uniformWeight n) : ℝ) ≤ 32768*logFactor n*(c.value : ℝ) ∧
      HasPathLengthAtMost c.flow
        (8192*(maxIncidentCapacity I.network : ℝ)*logFactor n /
          ((n : ℝ)*(sparsestCut I.network (uniformWeight n) : ℝ))) ∧
      c.paths.length ≤ n*n*(n^4+1) := by
  have hweights : I.weights=uniformWeight n := by
    funext v
    simp [RationalInstance.weights,uniformWeight,hw]
  have hsym : ∀ u v,I.capacity u v=I.capacity v u := by
    intro u v
    have hh := hI u v
    change (I.capacity u v : ℝ≥0)=(I.capacity v u : ℝ≥0) at hh
    exact_mod_cast hh
  obtain ⟨s,hscast,hcut⟩ := ShortRationalParameters.exists_sparsest I hw hn
  rw [hweights] at hscast
  have hs : 0 < s := by
    have hh : (0 : ℝ) < s := by rw [hscast]; exact_mod_cast hS
    exact_mod_cast hh
  let R : ℚ := ShortRationalParameters.maximum I
  let q : ℚ := R/((n : ℚ)*s)
  obtain ⟨hR,hq,hqeq⟩ := ShortRationalParameters.normalized_expansion I hw hn s hs hcut
  change 1/2 ≤ q at hq
  change q*n*s=R at hqeq
  have hrows (v : Fin n) : (∑ u,(I.capacity v u : ℚ)) ≤ q*n*s := by
    rw [hqeq]
    exact ShortRationalParameters.row_le I v
  have hex (L : ℕ) := LayeredFlowBounds.exact_optimal_pair I hn L
  choose value x y hfeas hdual heq using hex
  have hv (L : ℕ) : 0 ≤ value L := (hfeas L).1
  have hlarge (L : ℕ) (hL : 1024*(RegionBudget.steps n : ℚ)*q ≤ L ∨ n-1 ≤ L) :
      s/(2048*(RegionBudget.steps n : ℚ)) < value L := by
    rw [heq L]
    exact LayeredDualBound.objective_lower I hw hn hsym s q hs hq hcut hrows hL (y L) (hdual L)
  obtain ⟨hmin,hmax,hsize,hvalue⟩ := ShortLayerSelection.guarantees n hn s q hs hq value hv hlarge
  let L := ShortLayerSelection.select n (q*n*s) value
  change 1 ≤ L at hmin
  change L ≤ n-1 at hmax
  change (L : ℚ) ≤ 1026*(RegionBudget.steps n : ℚ)*q at hsize
  change s/(4104*(RegionBudget.steps n : ℚ)) ≤ value L at hvalue
  obtain ⟨rs,hvalid,hcap,hdemand,hcount⟩ := LayeredFlowRecords.exists_records I (value L) (x L) (hfeas L)
  let c := PathCertificateInterpretation.certificate (value L) rs
  obtain ⟨hflow,hlen⟩ := PathCertificateInterpretation.correct I (value L) (hv L) rs
    (fun r hr => ⟨(hvalid r hr).1.le,(hvalid r hr).2⟩) hcap (fun s t hst => (hdemand s t hst).ge)
  have hcast : (c.value : ℝ)=(value L : ℝ) := by
    exact_mod_cast Rat.coe_toNNRat (value L) (hv L)
  have hsteps := RegionBudget.steps_le_log n hn
  change (RegionBudget.steps n : ℝ) ≤ 6*logFactor n at hsteps
  have hK : (0 : ℝ) < RegionBudget.steps n := by exact_mod_cast RegionBudget.steps_pos n
  have hlog : 0 ≤ logFactor n := by linarith
  have hvreal : (0 : ℝ) ≤ value L := by exact_mod_cast hv L
  have hqreal : (0 : ℝ) ≤ q := by exact_mod_cast (show (0 : ℚ) ≤ q by linarith)
  refine ⟨c,hflow,?_,?_,?_⟩
  · rw [hcast,←hscast]
    have hb : s ≤ 4104*(RegionBudget.steps n : ℚ)*value L := by
      have hKq : (0 : ℚ) < RegionBudget.steps n := by exact_mod_cast RegionBudget.steps_pos n
      have hh := (div_le_iff₀ (by positivity : (0 : ℚ) < 4104*(RegionBudget.steps n : ℚ))).mp hvalue
      nlinarith
    have hb' : (s : ℝ) ≤ 4104*(RegionBudget.steps n : ℝ)*(value L : ℝ) := by exact_mod_cast hb
    have hh := mul_le_mul_of_nonneg_right hsteps hvreal
    have hpos : 0 ≤ logFactor n*(value L : ℝ) := mul_nonneg hlog hvreal
    nlinarith
  · have hlenreal : (L : ℝ) ≤ 1026*(RegionBudget.steps n : ℝ)*(q : ℝ) := by exact_mod_cast hsize
    have hh := mul_le_mul_of_nonneg_right hsteps hqreal
    have hpos : 0 ≤ logFactor n*(q : ℝ) := mul_nonneg hlog hqreal
    have hbound : (L : ℝ) ≤ 8192*logFactor n*(q : ℝ) := by nlinarith
    have hRcast : (R : ℝ)=(maxIncidentCapacity I.network : ℝ) := by
      have hh := ShortRationalParameters.maximum_cast I (by omega)
      change (((ShortRationalParameters.maximum I : ℚ≥0) : ℚ) : ℝ)=_
      rw [Rat.cast_nnratCast]
      exact congrArg (fun z : ℝ≥0 => (z : ℝ)) hh
    have hqcast : (q : ℝ)*(n : ℝ)*(s : ℝ)=(R : ℝ) := by exact_mod_cast hqeq
    have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsreal : (0 : ℝ) < s := by exact_mod_cast hs
    have he : 8192*(maxIncidentCapacity I.network : ℝ)*logFactor n /
        ((n : ℝ)*(sparsestCut I.network (uniformWeight n) : ℝ))=8192*logFactor n*(q : ℝ) := by
      rw [←hRcast,←hscast,←hqcast]
      field_simp
    rw [he]
    intro p hp
    exact (hlen p hp).trans hbound
  · change (rs.map _).length ≤ _
    rw [List.length_map]
    have hLn : L+1 ≤ n := by omega
    have hh : ((L+1)*n)^2 ≤ n^4 := by
      calc
        _ ≤ (n*n)^2 := Nat.pow_le_pow_left (Nat.mul_le_mul_right n hLn) 2
        _ = _ := by ring
    exact hcount.trans (Nat.mul_le_mul_left (n*n) (by omega))

end Lax455465Proofs.ShortPathExistence
