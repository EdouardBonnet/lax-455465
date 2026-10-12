import Lax455465Proofs.ShortPathExistence

open scoped BigOperators NNRat NNReal
namespace Lax455465Proofs.ShortSelectedBounds
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax455465.ConcurrentFlow
open Lax455465.ShortPathFlow LayeredFlowLP LayeredFlowFeasibility LayeredFlowDual

/-- Quantitative bounds for the exact family of optimal LP solutions used
by the native stopping scan, rather than independently chosen optimizers. -/
theorem guarantees {n : ℕ} (I : RationalInstance n) (hI : I.network.IsUndirected)
    (hw : ∀ v,I.weight v=1) (hn : 2≤n) (hS : 0<sparsestCut I.network (uniformWeight n))
    (f : ℕ → ℚ≥0) (x : ∀ L,Arc n L → ℚ) (y : ∀ L,Dual n L)
    (hf : ∀ L,Feasible I (f L : ℚ) (x L))
    (hy : ∀ L,Lax109476.LinearProgram.DualFeasible (program I L) (y L))
    (heq : ∀ L,(f L : ℚ)=Lax109476.LinearProgram.dualValue (program I L) (y L)) :
    let L:=ShortLayerSelection.select n (ShortRationalParameters.maximum I : ℚ) (fun k => (f k : ℚ))
    1≤L ∧ L≤n-1 ∧
      (sparsestCut I.network (uniformWeight n) : ℝ)≤32768*logFactor n*(f L : ℝ) ∧
      (L : ℝ)≤8192*(maxIncidentCapacity I.network : ℝ)*logFactor n /
        ((n : ℝ)*(sparsestCut I.network (uniformWeight n) : ℝ)) := by
  dsimp only
  have hweights : I.weights=uniformWeight n := by
    funext v
    simp [RationalInstance.weights,uniformWeight,hw]
  have hsym : ∀ u v,I.capacity u v=I.capacity v u := by
    intro u v
    have hh:=hI u v
    change (I.capacity u v : ℝ≥0)=(I.capacity v u : ℝ≥0) at hh
    exact_mod_cast hh
  obtain ⟨s,hscast,hcut⟩:=ShortRationalParameters.exists_sparsest I hw hn
  rw [hweights] at hscast
  have hs : 0<s := by
    have hh : (0 : ℝ)<s := by rw [hscast]; exact_mod_cast hS
    exact_mod_cast hh
  let R : ℚ:=ShortRationalParameters.maximum I
  let q : ℚ:=R/((n : ℚ)*s)
  obtain ⟨hR,hq,hqeq⟩:=ShortRationalParameters.normalized_expansion I hw hn s hs hcut
  change 1/2≤q at hq
  change q*n*s=R at hqeq
  have hrows (v : Fin n) : (∑ u,(I.capacity v u : ℚ))≤q*n*s := by
    rw [hqeq]
    exact ShortRationalParameters.row_le I v
  have hlarge (L : ℕ) (hL : 1024*(RegionBudget.steps n : ℚ)*q≤L ∨ n-1≤L) :
      s/(2048*(RegionBudget.steps n : ℚ))<(f L : ℚ) := by
    rw [heq L]
    exact LayeredDualBound.objective_lower I hw hn hsym s q hs hq hcut hrows hL (y L) (hy L)
  obtain ⟨hmin,hmax,hsize,hvalue⟩:=ShortLayerSelection.guarantees n hn s q hs hq
    (fun L => (f L : ℚ)) (fun L => (f L).coe_nonneg) hlarge
  rw [hqeq] at hmin hmax hsize hvalue
  let L:=ShortLayerSelection.select n R (fun k => (f k : ℚ))
  change 1≤L at hmin
  change L≤n-1 at hmax
  change (L : ℚ)≤1026*(RegionBudget.steps n : ℚ)*q at hsize
  change s/(4104*(RegionBudget.steps n : ℚ))≤(f L : ℚ) at hvalue
  have hsteps:=RegionBudget.steps_le_log n hn
  change (RegionBudget.steps n : ℝ)≤6*logFactor n at hsteps
  have hK : (0 : ℝ)<RegionBudget.steps n := by exact_mod_cast RegionBudget.steps_pos n
  have hlog : 0≤logFactor n := by linarith
  have hvreal : (0 : ℝ)≤f L := by positivity
  have hqreal : (0 : ℝ)≤q := by exact_mod_cast (show (0 : ℚ)≤q by linarith)
  refine ⟨hmin,hmax,?_,?_⟩
  · rw [←hscast]
    have hb : s≤4104*(RegionBudget.steps n : ℚ)*(f L : ℚ) := by
      have hKq : (0 : ℚ)<RegionBudget.steps n := by exact_mod_cast RegionBudget.steps_pos n
      have hh := (div_le_iff₀ (by positivity : (0 : ℚ)<4104*(RegionBudget.steps n : ℚ))).mp hvalue
      nlinarith only [hh]
    have hb' : (s : ℝ)≤4104*(RegionBudget.steps n : ℝ)*(f L : ℝ) := by exact_mod_cast hb
    have hh:=mul_le_mul_of_nonneg_right hsteps hvreal
    have hpos:=mul_nonneg hlog hvreal
    nlinarith
  · have hlenreal : (L : ℝ)≤1026*(RegionBudget.steps n : ℝ)*(q : ℝ) := by exact_mod_cast hsize
    have hh:=mul_le_mul_of_nonneg_right hsteps hqreal
    have hpos:=mul_nonneg hlog hqreal
    have hbound : (L : ℝ)≤8192*logFactor n*(q : ℝ) := by nlinarith
    have hRcast : (R : ℝ)=(maxIncidentCapacity I.network : ℝ) := by
      have hh:=ShortRationalParameters.maximum_cast I (by omega)
      change (((ShortRationalParameters.maximum I : ℚ≥0) : ℚ) : ℝ)=_
      rw [Rat.cast_nnratCast]
      exact congrArg (fun z : ℝ≥0 => (z : ℝ)) hh
    have hqcast : (q : ℝ)*(n : ℝ)*(s : ℝ)=(R : ℝ) := by exact_mod_cast hqeq
    have hnreal : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have hsreal : (0 : ℝ)<s := by exact_mod_cast hs
    have he : 8192*(maxIncidentCapacity I.network : ℝ)*logFactor n /
        ((n : ℝ)*(sparsestCut I.network (uniformWeight n) : ℝ))=8192*logFactor n*(q : ℝ) := by
      rw [←hRcast,←hscast,←hqcast]
      field_simp
    rwa [he]

end Lax455465Proofs.ShortSelectedBounds
