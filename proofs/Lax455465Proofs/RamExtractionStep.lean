import Lax455465Proofs.RamPositivePath
import Lax455465Proofs.RamPathSubtract
import Lax455465Proofs.RamPathRecord
import Lax455465Proofs.RamRemainingSubtract
import Lax455465Proofs.LayeredExtractionStep

namespace Lax455465Proofs.RamExtractionStep
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open LayeredFlowLP LayeredGraphFlow LayeredWalkState LayeredPathSweep RamPathState
open scoped NNRat

def command : Com := .seq RamPositivePath.command (.seq RamBottleneck.command
  (.seq RamPathRecord.command (.seq RamPathSubtract.command RamRemainingSubtract.command)))

/-- The growing buffer is related to its exact encoded prefix and record counter. -/
structure Output (front : List ℕ) (count : ℕ) (σ : Env) : Prop where
  buffer : Prefix front "short.output" σ
  cursor : σ.vars "short.outputLength"=front.length
  count : σ.vars "short.recordCount"=count

theorem output_frame {B K : ℕ} {c : Com} {σ τ : Env} (rr : Run B c σ τ K)
    {front : List ℕ} {count : ℕ} (h : Output front count σ)
    (hcursor : "short.outputLength"∉c.wvars) (hcount : "short.recordCount"∉c.wvars)
    (hbuffer : "short.output"∉c.warrs) : Output front count τ :=
  ⟨by simpa only [Prefix,rr.frame_arr "short.output" hbuffer] using h.buffer,
    (rr.frame_var "short.outputLength" hcursor).trans h.cursor,
    (rr.frame_var "short.recordCount" hcount).trans h.count⟩

def cost (n L M : ℕ) : ℕ :=
  (100*n+100*L+204)*L+122*L+16*(L+1)+(36*(M^2).size+256)*L+36*(M^2).size+340

/-- A complete native extraction iteration: traverse, cap the bottleneck,
emit the simple path, subtract its raw layered flow, and reduce demand. -/
theorem command_spec (B D H : ℕ) {n L : ℕ} (q : Coordinate n L → ℚ≥0)
    (a : ℚ≥0) (st : Edge n) (front : List ℕ) (count : ℕ)
    (hD : 0<D) (hH : 1≤H) (hB : 2*(H*D)^2+3<B) (hL : 1≤L) (ha : 0<a)
    (hsize : n+n*n+L*(n*n)+2*(1+(n*n)*(L*(n*n)))+2*L+20<B)
    (hlen : front.length+L+5<B) (hcount : count+1<B)
    (hq : ∀ j,ResidualLattice.Bounded D H (q j)) (haheight : ResidualLattice.Bounded D H a)
    (hb : AcyclicFlowPath.Balance (graph (arc q) st) (0,st.1) (Fin.last L,st.2) (a : ℚ)) :
    Spec B (fun σ => Data q st σ ∧ RamUnsignedScalar.Stored "short.remaining" a σ ∧
      Output front count σ ∧ front.length+L+4<(σ.arrs "short.output").length) command
      (fun _ τ => ∃ path : Fin (L+1) → Fin n, ∃ ys : List (Fin n),
        LayeredExtractionStep.Valid q a st path ys ∧
        Data (after q (LayeredExtractionStep.amount q a st path) st path L) st τ ∧
        RamUnsignedScalar.Stored "short.remaining"
          (RamTruncatedSubtract.value a (LayeredExtractionStep.amount q a st path)) τ ∧
        Output (front++RamPathRecord.encode (simple ys) (LayeredExtractionStep.amount q a st path)) (count+1) τ)
      (cost n L (H*D)) := by
  let M := H*D
  have hMB : M<B := by dsimp [M]; nlinarith only [hB]
  have hqn (j) : (q j).num≤M := by
    simpa only [NNRat.natAbs_num_coe] using (ResidualLattice.height (hq j) hD hH).1
  have hqd (j) : (q j).den≤M := (ResidualLattice.height (hq j) hD hH).2
  have han : a.num≤M := by simpa only [NNRat.natAbs_num_coe] using (ResidualLattice.height haheight hD hH).1
  have had : a.den≤M := (ResidualLattice.height haheight hD hH).2
  rintro σ ⟨hd,has,hout,hroom⟩
  obtain ⟨s1,r1,hd1,xs,ys,hw,hbuf⟩ := RamPositivePath.command_spec B q st (a : ℚ)
    (by exact_mod_cast ha) hL hb hsize (fun j => (hqn j).trans_lt hMB) (fun j => (hqd j).trans_lt hMB) σ hd
  obtain ⟨path,hxs,hs,ht,hpos⟩ := LayeredWalkVector.completed q st hw
  subst xs
  have hv : LayeredExtractionStep.Valid q a st path ys := LayeredExtractionStep.of_walk hw hs ht hpos
  let w := LayeredExtractionStep.amount q a st path
  have hwh := LayeredExtractionStep.amount_lattice q a st path D H hq haheight
  have hwn : w.num≤M := by simpa only [NNRat.natAbs_num_coe] using (ResidualLattice.height hwh hD hH).1
  have hwd : w.den≤M := (ResidualLattice.height hwh hD hH).2
  have hp1 : Prefix (List.ofFn fun i => (path i).val) "short.raw" s1 := by
    simpa only [vertices,LayeredSweepGraph.raw,List.map_ofFn,Function.comp_def] using hbuf.raw
  have ha1 : RamUnsignedScalar.Stored "short.remaining" a s1 := by
    simpa only [RamUnsignedScalar.Stored,String.reduceAppend,r1.frame_var "short.remaining.n" (by decide),
      r1.frame_var "short.remaining.d" (by decide)] using has
  have ho1 := output_frame r1 hout (by decide) (by decide) (by decide)
  obtain ⟨s2,r2,p2⟩ := RamBottleneck.command_spec B M q st path a hB hsize hqn hqd ⟨han,had⟩ s1 ⟨⟨hd1,hp1⟩,ha1⟩
  change RamPathEdgeRead.Context q st path s2 ∧ RamUnsignedScalar.Stored "short.amount" w s2 at p2
  have hs2 : Prefix (simple ys) "short.simple" s2 := by
    simpa only [Prefix,r2.frame_arr "short.simple" (by decide)] using hbuf.stack
  have hlen2 := (r2.frame_var "short.simpleLength" (by decide)).trans hbuf.stackLength
  have ho2 := output_frame r2 ho1 (by decide) (by decide) (by decide)
  have hroom2 : front.length+(simple ys).length+3<(s2.arrs "short.output").length := by
    rw [RamFrames.run_array_length r2 "short.output",RamFrames.run_array_length r1 "short.output"]
    simp only [simple,List.length_map]
    have hh := hv.length
    omega
  obtain ⟨s3,r3,p3⟩ := RamPathRecord.command_spec B front (simple ys) w count (by omega)
    (by simp only [simple,List.length_map]; have hh:=hv.length; omega) hcount
    (hwn.trans_lt hMB) (hwd.trans_lt hMB)
    (by intro v hv; obtain ⟨u,hu,rfl⟩:=List.mem_map.mp hv; exact u.isLt.trans (by omega)) s2
    ⟨ho2.buffer,ho2.cursor,hs2,by simpa only [simple,List.length_map] using hlen2,p2.2,ho2.count,hroom2⟩
  have hd3 := data_frame r3 p2.1.1 (by decide) (by decide)
  have hp3 : Prefix (List.ofFn fun i => (path i).val) "short.raw" s3 := by
    simpa only [Prefix,r3.frame_arr "short.raw" (by decide)] using p2.1.2
  have hw3 : RamUnsignedScalar.Stored "short.amount" w s3 := by
    simpa only [RamUnsignedScalar.Stored,String.reduceAppend,r3.frame_var "short.amount.n" (by decide),
      r3.frame_var "short.amount.d" (by decide)] using p2.2
  have hafter (i : ℕ) (j : Coordinate n L) : ResidualLattice.Bounded D H (after q w st path i j) :=
    lattice q w st path D H i hq hwh j
  obtain ⟨s4,r4,p4⟩ := RamPathSubtract.command_spec B M q w st path hB hsize
    (fun i _ j => by simpa only [NNRat.natAbs_num_coe] using (ResidualLattice.height (hafter i j) hD hH).1)
    (fun i _ j => (ResidualLattice.height (hafter i j) hD hH).2) hwn hwd s3 ⟨⟨hd3,hp3⟩,hw3⟩
  have ha4 : RamUnsignedScalar.Stored "short.remaining" a s4 := by
    simpa only [RamUnsignedScalar.Stored,String.reduceAppend,
      (r2.seq (r3.seq r4)).frame_var "short.remaining.n" (by decide),
      (r2.seq (r3.seq r4)).frame_var "short.remaining.d" (by decide)] using ha1
  have hrh := ResidualLattice.height (ResidualLattice.subtract haheight hwh) hD hH
  obtain ⟨τ,r5,p5⟩ := RamRemainingSubtract.command_spec B M a w hB han had hwn hwd
    (by simpa only [NNRat.natAbs_num_coe] using hrh.1.trans_lt hMB) (hrh.2.trans_lt hMB) s4 ⟨ha4,p4.2⟩
  have hdτ := data_frame r5 p4.1.1 (by decide) (by decide)
  have ho3 : Output (front++RamPathRecord.encode (simple ys) w) (count+1) s3 := by
    refine ⟨p3.1,?_,p3.2.2⟩
    have hh:=p3.2.1
    simp only [RamPathRecord.encode,Lax455465.RationalEncoding.encodeRational,List.length_append,
      List.length_cons,List.length_nil]
    omega
  have hoτ := output_frame (r4.seq r5) ho3 (by decide) (by decide) (by decide)
  refine ⟨τ,(r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono ?_,path,ys,hv,hdτ,p5,hoτ⟩
  dsimp only [cost,M]
  simp only [simple,List.length_map]
  have hl := Nat.mul_le_mul_left 16 hv.length
  omega

end Lax455465Proofs.RamExtractionStep
