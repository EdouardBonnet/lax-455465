import Lax455465Proofs.RamExtractionStep
import Lax455465Proofs.LayeredCommodityState

set_option maxRecDepth 4096

namespace Lax455465Proofs.RamCommodityLoop
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open LayeredFlowLP LayeredGraphFlow LayeredWalkState LayeredPathSweep RamPathState
open LayeredCommodityState PathRecordBuffer RamExtractionStep
open scoped NNRat

def condition : Cond := .lt (.lit 0) (.var "short.remaining.n")
def iteration : Com := .ite condition RamExtractionStep.command .skip
def step : Com := .seq iteration
  (.assign "short.inner.i" (.add (.var "short.inner.i") (.lit 1)))
def scan : Com := .seq (.assign "short.inner.i" (.lit 0))
  (.while (.lt (.var "short.inner.i") (.var "short.inner.limit")) step)
def command : Com := .seq (.assign "short.inner.limit" (.add (.var "lp.columns") (.lit 1))) scan

def Context {n L : ℕ} (q₀ : Coordinate n L → ℚ≥0) (a₀ : ℚ≥0) (st : Edge n)
    (D H : ℕ) (front : List ℕ) (count i : ℕ) (σ : Env) : Prop :=
  i≤budget n L ∧ σ.vars "lp.columns"=1+(n*n)*(L*(n*n)) ∧
  σ.vars "short.inner.limit"=budget n L ∧
  front.length+budget n L*(L+4)+L+4<(σ.arrs "short.output").length ∧
  ∃ q a rs, State q₀ a₀ st D H i q a rs ∧ Data q st σ ∧
    RamUnsignedScalar.Stored "short.remaining" a σ ∧ Output (front++encode rs) (count+rs.length) σ

theorem set_index {n L : ℕ} {q₀ : Coordinate n L → ℚ≥0} {a₀ : ℚ≥0} {st : Edge n}
    {D H : ℕ} {front : List ℕ} {count i : ℕ} {σ : Env}
    (h : Context q₀ a₀ st D H front count i σ) (v : ℕ) :
    Context q₀ a₀ st D H front count i (σ.setVar "short.inner.i" v) := by
  obtain ⟨hi,hcols,hlimit,hroom,q,a,rs,hm,hd,ha,ho⟩:=h
  refine ⟨hi,by simpa using hcols,by simpa using hlimit,hroom,q,a,rs,hm,
    RamPathState.set_var hd "short.inner.i" v (by decide),?_,?_⟩
  · simpa only [RamUnsignedScalar.Stored,String.reduceAppend,vars_setVar,String.reduceEq,if_false] using ha
  · exact ⟨ho.buffer,by simpa using ho.cursor,by simpa using ho.count⟩

theorem iteration_spec (B D H : ℕ) {n L : ℕ} (q₀ : Coordinate n L → ℚ≥0)
    (a₀ : ℚ≥0) (st : Edge n) (front : List ℕ) (count i : ℕ)
    (hD : 0<D) (hH : 1≤H) (hB : 2*(H*D)^2+3<B) (hL : 1≤L)
    (hsize : n+n*n+L*(n*n)+2*(1+(n*n)*(L*(n*n)))+2*L+20<B)
    (hlen : front.length+budget n L*(L+4)+L+5<B) (hcount : count+budget n L+1<B) :
    Spec B (fun σ => Context q₀ a₀ st D H front count i σ ∧ i<budget n L) iteration
      (fun _ τ => Context q₀ a₀ st D H front count (i+1) τ)
      (RamExtractionStep.cost n L (H*D)+4) := by
  rintro σ ⟨⟨hi,hcols,hlimit,hroom,q,a,rs,hm,hd,has,hout⟩,hlt⟩
  have hab : a.num<B := by
    have hh:= (ResidualLattice.height hm.remainder hD hH).1
    have hmb : H*D<B := by nlinarith only [hB]
    simpa only [NNRat.natAbs_num_coe] using hh.trans_lt hmb
  have hc : condition.evalB B σ=some (decide (0<a.num)) := by
    exact evalB_condLt (evalB_lit (by omega)) (by rw [evalB_var_iff]; exact ⟨has.1.symm,has.1 ▸ hab⟩)
  by_cases ha : 0<a
  · have hap : 0<a.num := by exact_mod_cast (NNRat.num_pos.mpr ha)
    have hen := length_bound rs hm.lengths
    have hrsl : rs.length≤budget n L := hm.count.trans hi
    have henc : (encode rs).length≤budget n L*(L+4) := hen.trans (Nat.mul_le_mul_right _ hrsl)
    obtain ⟨ν,rr,path,ys,hv,hdν,haν,hoν⟩ := RamExtractionStep.command_spec B D H q a st (front++encode rs)
      (count+rs.length) hD hH hB hL ha hsize
      (by simp only [List.length_append]; omega) (by omega) hm.lattice hm.remainder hm.balance σ
      ⟨hd,has,hout,by simp only [List.length_append]; omega⟩
    let w := LayeredExtractionStep.amount q a st path
    let rs' := rs++[(ys,w)]
    have hm' := LayeredCommodityState.step hm ha hv
    have ho' : Output (front++encode rs') (count+rs'.length) ν := by
      simpa only [rs',encode_append,encode_singleton,List.append_assoc,List.length_append,
        List.length_singleton,Nat.add_assoc] using hoν
    refine ⟨ν,(Run.ite_true (d := .skip) (by simpa only [hap,decide_true] using hc) rr).mono
      (by simp only [condition,Cond.size,Expr.size]; omega),?_,?_,?_,?_,_,_,_,hm',hdν,haν,ho'⟩
    · omega
    · exact (rr.frame_var "lp.columns" (by decide)).trans hcols
    · exact (rr.frame_var "short.inner.limit" (by decide)).trans hlimit
    · simpa only [RamFrames.run_array_length rr "short.output"] using hroom
  · have haz : a=0 := le_antisymm (le_of_not_gt ha) (by exact_mod_cast a.coe_nonneg)
    have hn : a.num=0 := by simp [haz]
    refine ⟨σ,(Run.ite_false (c := RamExtractionStep.command)
      (by simpa only [hn,lt_self_iff_false,decide_false] using hc) (Run.skip (σ := σ) (B := B))).mono
      (by simp only [condition,Cond.size,Expr.size,RamExtractionStep.cost]; omega),?_,hcols,hlimit,hroom,q,a,rs,LayeredCommodityState.idle hm haz,hd,has,hout⟩
    omega

theorem step_spec (B D H : ℕ) {n L : ℕ} (q₀ : Coordinate n L → ℚ≥0)
    (a₀ : ℚ≥0) (st : Edge n) (front : List ℕ) (count : ℕ)
    (hD : 0<D) (hH : 1≤H) (hB : 2*(H*D)^2+3<B) (hL : 1≤L)
    (hsize : n+n*n+L*(n*n)+2*(1+(n*n)*(L*(n*n)))+2*L+20<B)
    (hlen : front.length+budget n L*(L+4)+L+5<B) (hcount : count+budget n L+1<B) :
    Spec B (fun σ => Context q₀ a₀ st D H front count (σ.vars "short.inner.i") σ ∧
      σ.vars "short.inner.i"<budget n L) step
      (fun σ τ => Context q₀ a₀ st D H front count (τ.vars "short.inner.i") τ ∧
        τ.vars "short.inner.i"=σ.vars "short.inner.i"+1)
      (RamExtractionStep.cost n L (H*D)+8) := by
  rintro σ ⟨hσ,hlt⟩
  let i := σ.vars "short.inner.i"
  have hQB : budget n L<B := by
    have hh : 1≤L+4 := by omega
    have hm := Nat.mul_le_mul_left (budget n L) hh
    omega
  obtain ⟨ν,rr,pr⟩ := iteration_spec B D H q₀ a₀ st front count i hD hH hB hL hsize hlen hcount σ ⟨hσ,hlt⟩
  have hiν : ν.vars "short.inner.i"=i := rr.frame_var "short.inner.i" (by decide)
  let τ := ν.setVar "short.inner.i" (i+1)
  have ra : Run B (.assign "short.inner.i" (.add (.var "short.inner.i") (.lit 1))) ν τ 4 :=
    Run.assign (evalB_bin (op := .add)
      (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ (by omega : i<B)⟩)
      (evalB_lit (by omega)) (by dsimp [Bop.apply]; omega))
  refine ⟨τ,(rr.seq ra).mono (by omega),?_,by simp [τ,i]⟩
  simpa only [τ,vars_setVar,if_true] using set_index pr (i+1)

/-- The fixed loop runs the support budget, skipping iterations once the
remaining demand reaches zero. The invariant forces completion by its end. -/
theorem scan_spec (B D H : ℕ) {n L : ℕ} (q₀ : Coordinate n L → ℚ≥0)
    (a₀ : ℚ≥0) (st : Edge n) (front : List ℕ) (count : ℕ)
    (hD : 0<D) (hH : 1≤H) (hB : 2*(H*D)^2+3<B) (hL : 1≤L)
    (hsize : n+n*n+L*(n*n)+2*(1+(n*n)*(L*(n*n)))+2*L+20<B)
    (hlen : front.length+budget n L*(L+4)+L+5<B) (hcount : count+budget n L+1<B) :
    Spec B (Context q₀ a₀ st D H front count 0) scan
      (fun _ τ => ∃ q rs,
        State q₀ a₀ st D H (budget n L) q 0 rs ∧ Data q st τ ∧
        RamUnsignedScalar.Stored "short.remaining" 0 τ ∧ Output (front++encode rs) (count+rs.length) τ)
      ((RamExtractionStep.cost n L (H*D)+12)*budget n L+6) := by
  have hQB : budget n L<B := by
    have hm := Nat.mul_le_mul_left (budget n L) (by omega : 1≤L+4)
    omega
  have hr := Spec.forRangeZero "short.inner.i" "short.inner.limit"
    (fun σ => Context q₀ a₀ st D H front count (σ.vars "short.inner.i") σ) (budget n L)
    (RamExtractionStep.cost n L (H*D)+8) hQB (fun _ h => h.1) (fun _ h => h.2.2.1)
    (step_spec B D H q₀ a₀ st front count hD hH hB hL hsize hlen hcount)
  intro σ hσ
  have hinit : Context q₀ a₀ st D H front count
      ((σ.setVar "short.inner.i" 0).vars "short.inner.i") (σ.setVar "short.inner.i" 0) := by
    simpa only [vars_setVar,if_true] using set_index hσ 0
  obtain ⟨τ,rr,pr⟩ := hr σ hinit
  obtain ⟨hi,hcols,hlimit,hroom,q,a,rs,hm,hd,ha,ho⟩ := pr.1
  have haz : a=0 := LayeredCommodityState.finished (by simpa only [pr.2] using hm)
  subst a
  exact ⟨τ,rr,q,rs,by simpa only [pr.2] using hm,hd,ha,ho⟩

theorem command_spec (B D H : ℕ) {n L : ℕ} (q₀ : Coordinate n L → ℚ≥0)
    (a₀ : ℚ≥0) (st : Edge n) (front : List ℕ) (count : ℕ)
    (hD : 0<D) (hH : 1≤H) (hB : 2*(H*D)^2+3<B) (hL : 1≤L)
    (hsize : n+n*n+L*(n*n)+2*(1+(n*n)*(L*(n*n)))+2*L+20<B)
    (hlen : front.length+budget n L*(L+4)+L+5<B) (hcount : count+budget n L+1<B)
    (hq : ∀ j,ResidualLattice.Bounded D H (q₀ j)) (ha : ResidualLattice.Bounded D H a₀)
    (hb : AcyclicFlowPath.Balance (graph (arc q₀) st) (0,st.1) (Fin.last L,st.2) (a₀ : ℚ)) :
    Spec B (fun σ => Data q₀ st σ ∧ RamUnsignedScalar.Stored "short.remaining" a₀ σ ∧
      Output front count σ ∧ σ.vars "lp.columns"=1+(n*n)*(L*(n*n)) ∧
      front.length+budget n L*(L+4)+L+4<(σ.arrs "short.output").length) command
      (fun _ τ => ∃ q rs,
        State q₀ a₀ st D H (budget n L) q 0 rs ∧ Data q st τ ∧
        RamUnsignedScalar.Stored "short.remaining" 0 τ ∧ Output (front++encode rs) (count+rs.length) τ)
      ((RamExtractionStep.cost n L (H*D)+12)*budget n L+10) := by
  rintro σ ⟨hd,has,ho,hcols,hroom⟩
  let ν:=σ.setVar "short.inner.limit" (budget n L)
  have ri : Run B (.assign "short.inner.limit" (.add (.var "lp.columns") (.lit 1))) σ ν 4 :=
    Run.assign (evalB_bin (op := .add)
      (by rw [evalB_var_iff]; exact ⟨hcols.symm,hcols ▸ (by omega : 1+(n*n)*(L*(n*n))<B)⟩)
      (evalB_lit (by omega)) (by dsimp only [Bop.apply,budget]; omega))
  have hctx : Context q₀ a₀ st D H front count 0 ν := by
    refine ⟨Nat.zero_le _,by simpa [ν] using hcols,by simp [ν],hroom,q₀,a₀,[],
      LayeredCommodityState.initial q₀ a₀ st D H hq ha hb,
      RamPathState.set_var hd "short.inner.limit" (budget n L) (by decide),?_,?_⟩
    · simpa only [ν,RamUnsignedScalar.Stored,String.reduceAppend,vars_setVar,String.reduceEq,if_false] using has
    · simpa only [encode,List.flatMap_nil,List.append_nil,List.length_nil,Nat.add_zero] using
        output_frame ri ho (by decide) (by decide) (by decide)
  obtain ⟨τ,rr,pr⟩ := scan_spec B D H q₀ a₀ st front count hD hH hB hL hsize hlen hcount ν hctx
  exact ⟨τ,(ri.seq rr).mono (by omega),pr⟩

end Lax455465Proofs.RamCommodityLoop
