import Lax455465Proofs.RamRegionSetup

set_option maxRecDepth 4096
namespace Lax455465Proofs.RamRegionChoice
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRegionSetup RegionQueryData
open scoped NNRat

/-- The first accepted buffer index returns exactly the mathematical
region-growing search radius, including the original candidate order. -/
theorem first_of_search {n : ℕ} (q : Query n) (delta : ℚ≥0) (p : ℕ)
    (hb : (q.beta : ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (r : ℚ) (hs : RegionSearch.search (MetricMatrix.rational q.capacity) (MetricMatrix.rational q.length)
      (fun v => (q.outDistance v : ℚ)) (fun v => (q.inDistance v : ℚ)) q.seed delta p (direction q)=some r) :
    ∃ i, RamFind.first (RadiusSearchData.predicate q
        (RadiusData.candidates q.outDistance q.inDistance (RegionBudget.steps p) delta))
        (RegionBudget.steps p+1+2*n)=some i ∧
      ((RadiusData.candidates q.outDistance q.inDistance (RegionBudget.steps p) delta).getD i 0 : ℚ)=r := by
  let radii := RadiusData.candidates q.outDistance q.inDistance (RegionBudget.steps p) delta
  have he := congrArg (fun o : Option ℚ≥0 => o.map (fun a : ℚ≥0 => (a : ℚ)))
    (RadiusSearchData.first_value q radii)
  rw [RadiusSearchData.search_value q delta p hb,hs] at he
  cases hi : RamFind.first (RadiusSearchData.predicate q radii) radii.length with
  | none => simp only [hi,Option.map_none] at he; cases he
  | some i =>
    refine ⟨i,?_,?_⟩
    · simpa only [radii,RadiusData.length_candidates] using hi
    · simpa only [hi,Option.map_some,Option.some.injEq] using he

set_option maxHeartbeats 2400000 in
/-- Execute the root's full native region search and recover the actual
successful query whose radius equals the mathematical search result. -/
theorem command_spec (B M H : ℕ) {n : ℕ} (weights : Fin n → ℚ≥0)
    (capacity length : MetricMatrix.Matrix n) (root : Fin n) (seed beta delta : ℚ≥0) (p : ℕ)
    (hk : RegionBudget.steps p≤M) (hB : 2*M^2+3<B) (hquery : 2*(2^H)^2+3<B)
    (hindex : 2*(n*n)+2<B) (hvertex : 2*n+2<B) (hradius : 2*(RegionBudget.steps p+1+2*n)+2<B)
    (hl : ∀ u v, LpInputSize.Height M (length u v : ℚ))
    (hd : LpInputSize.Height M (delta : ℚ))
    (hu : LpInputSize.Height M ((delta/(RegionBudget.steps p : ℚ≥0) : ℚ≥0) : ℚ))
    (hb : ∀ i, ∀ hi : i<(RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta).length,
      RegionQueryHeight.Bounds (RadiusSearchData.atRadius (query weights capacity length root seed beta)
        (RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta)[i]) H)
    (hbeta : (beta : ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (r : ℚ) (hs : RegionSearch.search (MetricMatrix.rational capacity) (MetricMatrix.rational length)
      (fun v => (length root v : ℚ)) (fun v => (length v root : ℚ)) seed delta p
      (RegionSelection.direction (fun v => (weights v : ℚ)) (fun v => (length root v : ℚ))
        (fun v => (length v root : ℚ)))=some r) :
    Spec B (fun σ => Input weights capacity length root seed beta delta (RegionBudget.steps p) σ ∧
      Room n (RegionBudget.steps p+1+2*n) σ) RamRegionSetup.command
      (fun _ τ => ∃ rn : ℚ≥0, (rn : ℚ)=r ∧ rn∈RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta ∧
        τ.vars "find.found"=1 ∧
        RamRadiusSearch.Answer (RadiusSearchData.atRadius (query weights capacity length root seed beta) rn) τ)
      (RamRegionSetup.cost n (RegionBudget.steps p) M H) := by
  let q := query weights capacity length root seed beta
  let radii := RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta
  obtain ⟨i,hi,hr⟩ := first_of_search q delta p hbeta r hs
  change RamFind.first (RadiusSearchData.predicate (query weights capacity length root seed beta) radii)
    (RegionBudget.steps p+1+2*n)=some i at hi
  have hlen : radii.length=RegionBudget.steps p+1+2*n := RadiusData.length_candidates _ _ _ _
  intro σ hσ
  obtain ⟨τ,rr,pr⟩ := RamRegionSetup.command_spec B M H weights capacity length root seed beta delta (RegionBudget.steps p)
    hk hB hquery hindex hvertex hradius hl hd hu hb σ hσ
  refine ⟨τ,rr,radii.getD i 0,hr,?_,?_,?_⟩
  · have hi' : i<radii.length := by
      apply (RamFind.first_some (RadiusSearchData.predicate (query weights capacity length root seed beta) radii) radii.length i (by rwa [hlen])).1
    rw [List.getD_eq_get radii 0 (⟨i,hi'⟩ : Fin radii.length),List.get_eq_getElem]
    exact List.getElem_mem hi'
  · have hm := pr.2.1
    change RamFind.Matches (RamFind.first (RadiusSearchData.predicate (query weights capacity length root seed beta) radii)
      (RegionBudget.steps p+1+2*n)) τ at hm
    simp only [RamFind.Matches,hi] at hm
    exact hm.1
  · have hp := pr.2.2
    change RamSelectedRegion.Selected (query weights capacity length root seed beta) radii τ at hp
    simpa only [RamSelectedRegion.Selected,hlen,hi] using hp

end Lax455465Proofs.RamRegionChoice
