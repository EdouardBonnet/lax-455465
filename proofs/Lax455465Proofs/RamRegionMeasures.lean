import Lax455465Proofs.RamRegionContext

namespace Lax455465Proofs.RamRegionMeasures

open RegionQueryData RamRegionContext Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState
open scoped NNRat

def oriented (outward : Bool) : Com := .seq (RamBoundary.command outward) (RamVolume.command outward)
def command : Com := .ite (.eq (.var "region.outward") (.lit 1)) (oriented true) (oriented false)

theorem masks_frame {B K : ℕ} {cmd : Com} {σ τ : Env} (hr : Run B cmd σ τ K)
    {n : ℕ} {q : Query n} (h : Masks q σ)
    (hx : ∀ x ∈ sourceVariables, x ∉ cmd.wvars) (ha : ∀ a ∈ arrays, a ∉ cmd.warrs)
    (hout : "region.outMask" ∉ cmd.warrs) (hin : "region.inMask" ∉ cmd.warrs)
    (hdir : "region.outward" ∉ cmd.wvars) : Masks q τ := by
  refine ⟨Input.frame hr h.input hx ha,?_,?_,(hr.frame_var _ hdir).trans h.directionValue⟩
  · simpa only [Prefix,hr.frame_arr "region.outMask" hout] using h.outMask
  · simpa only [Prefix,hr.frame_arr "region.inMask" hin] using h.inMask

set_option maxHeartbeats 1600000 in
/-- Compute the boundary and seeded volume in the selected runtime
orientation, preserving both masks for subsequent removal or cut rounding. -/
theorem command_spec (B H : ℕ) {n : ℕ} (q : Query n) (hb : RegionQueryHeight.Bounds q H)
    (hB : 2*(2^H)^2+3 < B) (hindex : 2*(n*n)+2 < B) (hvertex : 2*n+2 < B) :
    Spec B (fun σ => Masks q σ ∧ 2*(n*n) < (σ.arrs "region.crossing").length) command
      (fun _ τ => Masks q τ ∧ Stored "region.boundary" (boundary q) τ ∧ Stored "region.volume" (volume q) τ)
      ((288*H+880)*(n*n)+72*H+226) := by
  have hM1 : 1 ≤ 2^H := by have := Nat.two_pow_pos H; omega
  have hM : 2^H < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  have horiented (b : Bool) : Spec B (fun σ => Masks q σ ∧ 2*(n*n) < (σ.arrs "region.crossing").length)
      (oriented b) (fun _ τ => Masks q τ ∧ Stored "region.boundary" (boundaryAt q b) τ ∧ Stored "region.volume" (volumeAt q b) τ)
      ((144*((2^H)^2).size+736)*(n*n)+36*((2^H)^2).size+186) := by
    rintro σ ⟨hctx,hroom⟩
    obtain ⟨ν,rb,pb⟩ := RamBoundary.command_spec B (2^H) b q.capacity (distance q b) q.radius hM1 hB hindex hvertex
      (fun u v => num_bound (hb.capacityBound u v)) (fun u v => den_bound (hb.capacityBound u v))
      (fun i => num_bound (hb.boundaryPrefixBound b i)) (fun i => den_bound (hb.boundaryPrefixBound b i)) σ ⟨hctx.boundaryContext b,hroom⟩
    have hmν := masks_frame rb hctx (by cases b <;> dsimp [sourceVariables] <;> decide)
      (by cases b <;> dsimp [arrays] <;> decide) (by cases b <;> decide) (by cases b <;> decide) (by cases b <;> decide)
    have hvb := hb.volumeBounds b
    obtain ⟨τ,rv,pv⟩ := RamVolume.command_spec B (2^H) b q.capacity q.length (distance q b) q.seed q.radius hB hindex hvertex
      (fun u v => num_bound (hvb.capacityBound u v)) (fun u v => den_bound (hvb.capacityBound u v))
      (fun u v => num_bound (hvb.lengthBound u v)) (fun u v => den_bound (hvb.lengthBound u v))
      (fun v => num_bound (hvb.distanceBound v)) (fun v => den_bound (hvb.distanceBound v))
      (num_bound hvb.seedBound) (den_bound hvb.seedBound) (num_bound hvb.radiusBound) (den_bound hvb.radiusBound)
      (fun v => num_bound (hvb.differenceBound v)) (fun v => den_bound (hvb.differenceBound v))
      (fun u v => num_bound (hvb.portionBound u v)) (fun u v => den_bound (hvb.portionBound u v))
      (fun a ha => num_bound (hvb.coefficientBound a ha)) (fun a ha => den_bound (hvb.coefficientBound a ha))
      (fun i => num_bound (hvb.prefixBound i)) (fun i => den_bound (hvb.prefixBound i))
      (num_bound hvb.valueBound) (den_bound hvb.valueBound) ν (hmν.input.volumeContext b)
    refine ⟨τ,(rb.seq rv).mono (by ring_nf; omega),masks_frame rv hmν
      (by cases b <;> dsimp [sourceVariables] <;> decide) (by cases b <;> dsimp [arrays] <;> decide)
      (by cases b <;> decide) (by cases b <;> decide) (by cases b <;> decide),?_,pv.2⟩
    simpa only [boundaryAt,Stored,String.reduceAppend,rv.frame_var "region.boundary.n" (by cases b <;> decide),
      rv.frame_var "region.boundary.d" (by cases b <;> decide)] using pb.2.2
  rintro σ ⟨hctx,hroom⟩
  have hdir : σ.vars "region.outward" < B := by rw [hctx.directionValue]; split_ifs <;> omega
  have hc : (Cond.eq (.var "region.outward") (.lit 1)).evalB B σ = some (direction q q.radius) := by
    rw [evalB_condEq (evalB_var hdir) (evalB_lit h1),hctx.directionValue]
    cases direction q q.radius <;> rfl
  cases hd : direction q q.radius with
  | true =>
    obtain ⟨τ,rr,pr⟩ := horiented true σ ⟨hctx,hroom⟩
    have rb := Run.ite_true (d := oriented false) (by simpa only [hd] using hc) rr
    refine ⟨τ,rb.mono ?_,pr.1,?_,?_⟩
    · dsimp only [Cond.size,Expr.size]
      rw [←Nat.pow_mul,Nat.size_pow]
      ring_nf; omega
    · simpa only [boundary,hd] using pr.2.1
    · simpa only [volume,hd] using pr.2.2
  | false =>
    obtain ⟨τ,rr,pr⟩ := horiented false σ ⟨hctx,hroom⟩
    have rb := Run.ite_false (c := oriented true) (by simpa only [hd] using hc) rr
    refine ⟨τ,rb.mono ?_,pr.1,?_,?_⟩
    · dsimp only [Cond.size,Expr.size]
      rw [←Nat.pow_mul,Nat.size_pow]
      ring_nf; omega
    · simpa only [boundary,hd] using pr.2.1
    · simpa only [volume,hd] using pr.2.2

end Lax455465Proofs.RamRegionMeasures
