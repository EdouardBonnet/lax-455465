import Lax455465Proofs.RamRegionContext
import Lax455465Proofs.RamScalarComparison

namespace Lax455465Proofs.RamRegionAcceptance

open RegionQueryData RamRegionContext Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState RamRational
open scoped NNRat

def product : Com := RamScalarBinary.command "round.slope" "region.volume" multiplyFraction
def compare : Com := RamScalarComparison.command "region.boundary" "query.bound"
def record : Com := .ite (.eq (.var "region.radius.n") (.lit 0)) (.assign "find.ok" (.lit 0))
  (.assign "find.ok" (.var "cmp.le"))
def command : Com := .seq product (.seq (save "query.bound") (.seq compare record))

set_option maxHeartbeats 1600000 in
/-- The acceptance word is the exact positive-radius/volume-growth
predicate of region search. Its arithmetic uses the computed boundary,
volume, and stored slope and preserves the masks needed by the next step. -/
theorem command_spec (B H : ℕ) {n : ℕ} (q : Query n) (hb : RegionQueryHeight.Bounds q H)
    (hB : 2*(2^H)^2+3 < B) :
    Spec B (fun σ => Masks q σ ∧ Stored "region.boundary" (boundary q) σ ∧ Stored "region.volume" (volume q) σ)
      command (fun _ τ => Masks q τ ∧ Stored "query.bound" (bound q) τ ∧
        τ.vars "find.ok" = if accepted q then 1 else 0) (72*H+198) := by
  have hM : 2^H < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  have hv : LpInputSize.Height (2^H) (volume q : ℚ) := (hb.volumeBounds (direction q q.radius)).valueBound
  have hbc : LpInputSize.Height (2^H) (boundary q : ℚ) := by
    have hh := hb.boundaryPrefixBound (direction q q.radius)
      (RamMaskedSum.coefficients (MetricMatrix.values q.capacity) (MetricMatrix.values (BoundaryData.arcs (direction q q.radius) (distance q (direction q q.radius)) q.radius))).length
    simpa only [boundary,boundaryAt,BoundaryData.value,List.take_length] using hh
  have hp := hb.boundBound
  rintro σ ⟨hctx,hboundary,hvolume⟩
  obtain ⟨ν,rp,pp⟩ := RamScalarBinary.command_spec B (2^H) (36*((2^H)^2).size+64)
    q.beta (volume q) "round.slope" "region.volume" multiplyFraction (bound q : ℚ) hB
    (num_bound hb.betaBound) (den_bound hb.betaBound) (num_bound hv) (den_bound hv) (by decide) (by decide) (by decide)
    (fun σ h => by
      obtain ⟨τ,rr,pr⟩ := multiplyFraction_spec B (2^H) 0 q.beta.num q.beta.den 0 (volume q).num (volume q).den hB
        (by omega) (by omega) (num_bound hb.betaBound) (den_bound hb.betaBound) (num_bound hv) (den_bound hv)
        q.beta.den_pos (volume q).den_pos σ h
      have hsize : (q.beta.den*(volume q).den).size ≤ ((2^H)^2).size := Nat.size_le_size (by nlinarith [Nat.mul_le_mul (den_bound hb.betaBound) (den_bound hv)])
      exact ⟨τ,rr.mono (by omega),by simpa only [bound,NNRat.coe_mul,RamUnsignedArithmetic.value] using pr⟩) σ ⟨hctx.input.betaData,hvolume⟩
  obtain ⟨μ,rs,ps⟩ := save_spec B "query.bound" (bound q) ((num_bound hp).trans_lt hM) ((den_bound hp).trans_lt hM) (by decide) ν pp
  have hboundaryμ : Stored "region.boundary" (boundary q) μ := by
    have rr := rp.seq rs
    simpa only [Stored,String.reduceAppend,rr.frame_var "region.boundary.n" (by decide),rr.frame_var "region.boundary.d" (by decide)] using hboundary
  obtain ⟨ξ,rc,pc⟩ := RamScalarComparison.command_spec B (2^H) (boundary q) (bound q) "region.boundary" "query.bound" hB
    (num_bound hbc) (den_bound hbc) (num_bound hp) (den_bound hp) (by decide) (by decide) (by decide) μ ⟨hboundaryμ,ps⟩
  have rprior := rp.seq (rs.seq rc)
  have hradius : ξ.vars "region.radius.n"=q.radius.num :=
    (rprior.frame_var _ (by decide)).trans hctx.input.radiusData.1
  have hc : (Cond.eq (.var "region.radius.n") (.lit 0)).evalB B ξ = some (decide (q.radius.num=0)) := by
    rw [evalB_condEq (evalB_var (hradius ▸ (num_bound hb.radiusBound).trans_lt hM)) (evalB_lit (by omega)),hradius]
    rfl
  have preserve {τ : Env} {c : Com} {k : ℕ} (rr : Run B c σ τ k)
      (hx : ∀ x ∈ sourceVariables, x ∉ c.wvars) (hd : "region.outward" ∉ c.wvars)
      (ha : ∀ a ∈ arrays, a ∉ c.warrs) (ho : "region.outMask" ∉ c.warrs) (hi : "region.inMask" ∉ c.warrs) : Masks q τ := by
    exact ⟨Input.frame rr hctx.input hx ha,
      by simpa only [Prefix,rr.frame_arr "region.outMask" ho] using hctx.outMask,
      by simpa only [Prefix,rr.frame_arr "region.inMask" hi] using hctx.inMask,
      (rr.frame_var _ hd).trans hctx.directionValue⟩
  by_cases hz : q.radius.num=0
  · have rb : Run B (.assign "find.ok" (.lit 0)) ξ (ξ.setVar "find.ok" 0) 2 := Run.assign (evalB_lit (by omega))
    have rrecord := Run.ite_true (d := .assign "find.ok" (.var "cmp.le")) (by simpa only [hz,decide_true] using hc) rb
    have rr := rp.seq (rs.seq (rc.seq rrecord))
    refine ⟨ξ.setVar "find.ok" 0,rr.mono ?_,preserve rr (by dsimp [sourceVariables]; decide) (by decide)
      (by intro a ha; change a ∉ ([] : List String); simp) (by decide) (by decide),?_,?_⟩
    · dsimp only [Cond.size,Expr.size]
      rw [←Nat.pow_mul,Nat.size_pow]
      ring_nf; omega
    · have ra := rc.seq rrecord
      simpa only [Stored,String.reduceAppend,ra.frame_var "query.bound.n" (by decide),ra.frame_var "query.bound.d" (by decide)] using ps
    · simp [accepted_eq,hz]
  · let flag : ℕ := if (boundary q : ℚ)≤(bound q : ℚ) then 1 else 0
    have hflag : ξ.vars "cmp.le" < B := by rw [pc]; split_ifs <;> omega
    have rb : Run B (.assign "find.ok" (.var "cmp.le")) ξ (ξ.setVar "find.ok" flag) 2 :=
      Run.assign (by rw [evalB_var_iff]; exact ⟨pc.symm,hflag⟩)
    have rrecord := Run.ite_false (c := .assign "find.ok" (.lit 0)) (by simpa only [hz,decide_false] using hc) rb
    have rr := rp.seq (rs.seq (rc.seq rrecord))
    refine ⟨ξ.setVar "find.ok" flag,rr.mono ?_,preserve rr (by dsimp [sourceVariables]; decide) (by decide)
      (by intro a ha; change a ∉ ([] : List String); simp) (by decide) (by decide),?_,?_⟩
    · dsimp only [Cond.size,Expr.size]
      rw [←Nat.pow_mul,Nat.size_pow]
      ring_nf; omega
    · have ra := rc.seq rrecord
      simpa only [Stored,String.reduceAppend,ra.frame_var "query.bound.n" (by decide),ra.frame_var "query.bound.d" (by decide)] using ps
    · simp [accepted_eq,flag,Nat.pos_of_ne_zero hz]

end Lax455465Proofs.RamRegionAcceptance
