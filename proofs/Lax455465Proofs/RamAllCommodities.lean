import Lax455465Proofs.RamExtractionData
import Lax455465Proofs.LayeredExtractionState

set_option maxRecDepth 8192
namespace Lax455465Proofs.RamAllCommodities
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open LayeredFlowLP LayeredGraphFlow LayeredWalkState LayeredPathSweep
open PathRecordBuffer RamExtractionStep RamExtractionData
open scoped NNRat

def start : Com := .seq (.assign "short.remaining.n" (.var "short.initial.n"))
  (.assign "short.remaining.d" (.var "short.initial.d"))
def branch : Com := .ite (.eq (.var "short.source") (.var "short.target")) .skip
  (.seq start RamCommodityLoop.command)
def iteration : Com := .seq RamExtractionData.endpoints branch
def step : Com := .seq iteration
  (.assign "short.commodity" (.add (.var "short.commodity") (.lit 1)))
def command : Com := .seq (.assign "short.commodity" (.lit 0))
  (.while (.lt (.var "short.commodity") (.var "lp.n2")) step)

def innerCost (n L M : ℕ) : ℕ :=
  (RamExtractionStep.cost n L M+12)*LayeredCommodityState.budget n L+10

def Context {n L : ℕ} (q₀ : Coordinate n L → ℚ≥0) (a₀ : ℚ≥0) (D H : ℕ)
    (front : List ℕ) (count i : ℕ) (σ : Env) : Prop :=
  i≤n*n ∧ RamUnsignedScalar.Stored "short.initial" a₀ σ ∧
  front.length+(n*n+1)*LayeredCommodityState.budget n L*(L+4)+L+4<(σ.arrs "short.output").length ∧
  ∃ q rs,LayeredExtractionState.State q₀ a₀ D H i q rs ∧ Data q σ ∧
    Output (front++encode rs) (count+rs.length) σ

theorem set_index {n L : ℕ} {q₀ : Coordinate n L → ℚ≥0} {a₀ : ℚ≥0} {D H : ℕ}
    {front : List ℕ} {count i : ℕ} {σ : Env} (h : Context q₀ a₀ D H front count i σ) (v : ℕ) :
    Context q₀ a₀ D H front count i (σ.setVar "short.commodity" v) := by
  obtain ⟨hi,ha,hr,q,rs,hm,hd,ho⟩:=h
  refine ⟨hi,?_,hr,q,rs,hm,RamExtractionData.set_index hd v,ho.buffer,?_,?_⟩
  · simpa only [RamUnsignedScalar.Stored,String.reduceAppend,vars_setVar,String.reduceEq,if_false] using ha
  · simpa using ho.cursor
  · simpa using ho.count

theorem iteration_spec (B D H : ℕ) {n L : ℕ} (q₀ : Coordinate n L → ℚ≥0) (a₀ : ℚ≥0)
    (front : List ℕ) (count i : ℕ) (hn : 0<n) (hL : 1≤L) (hD : 0<D) (hH : 1≤H)
    (hB : 2*(H*D)^2+3<B)
    (hsize : n+n*n+L*(n*n)+2*(1+(n*n)*(L*(n*n)))+2*L+20<B)
    (hlen : front.length+(n*n+1)*LayeredCommodityState.budget n L*(L+4)+L+5<B)
    (hcount : count+(n*n+1)*LayeredCommodityState.budget n L+1<B)
    (ha : ResidualLattice.Bounded D H a₀) :
    Spec B (fun σ => Context q₀ a₀ D H front count i σ ∧ σ.vars "short.commodity"=i ∧ i<n*n)
      iteration (fun _ τ => Context q₀ a₀ D H front count (i+1) τ)
      (innerCost n L (H*D)+18) := by
  rintro σ ⟨⟨hi,has,hroom,q,rs,hm,hd,ho⟩,hidx,hlt⟩
  let st : Edge n := (DirectedFlowLP.edgeIndex n).symm ⟨i,hlt⟩
  have hst : LayeredExtractionState.index st=i := congrArg Fin.val ((DirectedFlowLP.edgeIndex n).apply_symm_apply ⟨i,hlt⟩)
  have hstidx : σ.vars "short.commodity"=(DirectedFlowLP.edgeIndex n st).val := hidx.trans hst.symm
  obtain ⟨ν,r1,p1⟩ := endpoints_spec B q st hn (by omega) σ ⟨hd,hstidx⟩
  have hasν : RamUnsignedScalar.Stored "short.initial" a₀ ν := by
    simpa only [RamUnsignedScalar.Stored,String.reduceAppend,r1.frame_var "short.initial.n" (by decide),
      r1.frame_var "short.initial.d" (by decide)] using has
  have hoν := output_frame r1 ho (by decide) (by decide) (by decide)
  have hroomν : front.length+(n*n+1)*LayeredCommodityState.budget n L*(L+4)+L+4<(ν.arrs "short.output").length := by
    simpa only [RamFrames.run_array_length r1 "short.output"] using hroom
  have hcond : (Cond.eq (.var "short.source") (.var "short.target")).evalB B ν=some (decide (st.1=st.2)) := by
    have hs : (Expr.var "short.source").evalB B ν=some st.1.val := by
      rw [evalB_var_iff]; exact ⟨p1.2.2.1.symm,p1.2.2.1 ▸ st.1.isLt.trans (by omega)⟩
    have ht : (Expr.var "short.target").evalB B ν=some st.2.val := by
      rw [evalB_var_iff]; exact ⟨p1.2.2.2.symm,p1.2.2.2 ▸ st.2.isLt.trans (by omega)⟩
    have hh:=evalB_condEq hs ht
    by_cases he : st.1=st.2
    · simpa [he] using hh
    · have hv : st.1.val≠st.2.val := fun hh => he (Fin.ext hh)
      simpa [he,hv] using hh
  by_cases he : st.1=st.2
  · have rb : Run B branch ν ν 5 := Run.ite_true (by simpa only [he,decide_true] using hcond) Run.skip
    refine ⟨ν,(r1.seq rb).mono (by dsimp only [innerCost,RamExtractionStep.cost]; omega),by omega,hasν,hroomν,
      q,rs,LayeredExtractionState.diagonal hm hst he,p1.1,hoν⟩
  · have han : a₀.num<B := by
      have hh:=(ResidualLattice.height ha hD hH).1
      have hmb : H*D<B := by nlinarith only [hB]
      simpa only [NNRat.natAbs_num_coe] using hh.trans_lt hmb
    have had : a₀.den<B := (ResidualLattice.height ha hD hH).2.trans_lt (by nlinarith only [hB])
    let μ := (ν.setVar "short.remaining.n" a₀.num).setVar "short.remaining.d" a₀.den
    have r2 : Run B start ν μ 4 := by
      suffices ∃ τ,Run B start ν τ 4 ∧ τ=μ by obtain ⟨τ,rr,rfl⟩:=this; exact rr
      unfold start
      run_vcg
      all_goals simp_all [μ,RamUnsignedScalar.Stored]
    have hdμ := frame r2 p1.1 (by decide) (by decide)
    have hoμ := output_frame r2 hoν (by decide) (by decide) (by decide)
    have hcμ : μ.vars "short.commodity"=(DirectedFlowLP.edgeIndex n st).val :=
      (r2.frame_var "short.commodity" (by decide)).trans p1.2.1
    have hsμ : μ.vars "short.source"=st.1.val := (r2.frame_var "short.source" (by decide)).trans p1.2.2.1
    have hrsl : rs.length≤n*n*LayeredCommodityState.budget n L :=
      hm.count.trans (Nat.mul_le_mul_right _ hi)
    have henc := (length_bound rs (fun r hr => (hm.good r hr).2.2.2)).trans (Nat.mul_le_mul_right (L+4) hrsl)
    have hbudget : (n*n+1)*LayeredCommodityState.budget n L*(L+4)=
      n*n*LayeredCommodityState.budget n L*(L+4)+LayeredCommodityState.budget n L*(L+4) := by ring
    have hbudget' : (n*n+1)*LayeredCommodityState.budget n L=
      n*n*LayeredCommodityState.budget n L+LayeredCommodityState.budget n L := by ring
    obtain ⟨τ,r3,q',ts,hmath,hpath,hrem,hout⟩ := RamCommodityLoop.command_spec B D H q a₀ st
      (front++encode rs) (count+rs.length) hD hH hB hL hsize
      (by simp only [List.length_append]; rw [hbudget] at hlen; omega)
      (by rw [hbudget'] at hcount; omega) hm.lattice ha (hm.balances st (by omega) he) μ
      ⟨to_path hdμ st hcμ hsμ,by simp [μ,RamUnsignedScalar.Stored],hoμ,hdμ.columns,
        by simp only [List.length_append]; rw [RamFrames.run_array_length r2 "short.output"];
           rw [hbudget] at hroomν; omega⟩
    have rb := Run.ite_false (c := .skip) (by simpa only [he,decide_false] using hcond) (r2.seq r3)
    have rd := r1.seq rb
    have hdτ : Data q' τ := of_path hpath ((r3.frame_var "lp.columns" (by decide)).trans hdμ.columns)
    have hasτ : RamUnsignedScalar.Stored "short.initial" a₀ τ := by
      simpa only [RamUnsignedScalar.Stored,String.reduceAppend,rd.frame_var "short.initial.n" (by decide),
        rd.frame_var "short.initial.d" (by decide)] using has
    refine ⟨τ,rd.mono (by dsimp only [innerCost]; simp only [Cond.size,Expr.size]; omega),by omega,hasτ,?_,q',rs++ts,
      LayeredExtractionState.next hm hst he hmath,hdτ,?_⟩
    · simpa only [RamFrames.run_array_length rd "short.output"] using hroom
    · simpa only [encode_append,List.append_assoc,List.length_append,Nat.add_assoc] using hout

theorem step_spec (B D H : ℕ) {n L : ℕ} (q₀ : Coordinate n L → ℚ≥0) (a₀ : ℚ≥0)
    (front : List ℕ) (count : ℕ) (hn : 0<n) (hL : 1≤L) (hD : 0<D) (hH : 1≤H)
    (hB : 2*(H*D)^2+3<B)
    (hsize : n+n*n+L*(n*n)+2*(1+(n*n)*(L*(n*n)))+2*L+20<B)
    (hlen : front.length+(n*n+1)*LayeredCommodityState.budget n L*(L+4)+L+5<B)
    (hcount : count+(n*n+1)*LayeredCommodityState.budget n L+1<B)
    (ha : ResidualLattice.Bounded D H a₀) :
    Spec B (fun σ => Context q₀ a₀ D H front count (σ.vars "short.commodity") σ ∧
      σ.vars "short.commodity"<n*n) step
      (fun σ τ => Context q₀ a₀ D H front count (τ.vars "short.commodity") τ ∧
        τ.vars "short.commodity"=σ.vars "short.commodity"+1) (innerCost n L (H*D)+22) := by
  rintro σ ⟨hσ,hlt⟩
  let i:=σ.vars "short.commodity"
  obtain ⟨ν,rr,pr⟩ := iteration_spec B D H q₀ a₀ front count i hn hL hD hH hB hsize hlen hcount ha σ ⟨hσ,rfl,hlt⟩
  have hiν : ν.vars "short.commodity"=i := rr.frame_var "short.commodity" (by decide)
  let τ:=ν.setVar "short.commodity" (i+1)
  have ri : Run B (.assign "short.commodity" (.add (.var "short.commodity") (.lit 1))) ν τ 4 :=
    Run.assign (evalB_bin (op := .add)
      (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ (by omega : i<B)⟩)
      (evalB_lit (by omega)) (by dsimp only [Bop.apply]; omega))
  refine ⟨τ,(rr.seq ri).mono (by omega),?_,by simp [τ,i]⟩
  simpa only [τ,vars_setVar,if_true] using set_index pr (i+1)

/-- One uniform native command decomposes all distinct ordered commodities,
using only the runtime dimensions and the decoded primal coordinate buffer. -/
theorem command_spec (B D H : ℕ) {n L : ℕ} (q₀ : Coordinate n L → ℚ≥0) (a₀ : ℚ≥0)
    (front : List ℕ) (count : ℕ) (hn : 0<n) (hL : 1≤L) (hD : 0<D) (hH : 1≤H)
    (hB : 2*(H*D)^2+3<B)
    (hsize : n+n*n+L*(n*n)+2*(1+(n*n)*(L*(n*n)))+2*L+20<B)
    (hlen : front.length+(n*n+1)*LayeredCommodityState.budget n L*(L+4)+L+5<B)
    (hcount : count+(n*n+1)*LayeredCommodityState.budget n L+1<B)
    (ha : ResidualLattice.Bounded D H a₀) :
    Spec B (Context q₀ a₀ D H front count 0) command
      (fun _ τ => ∃ q rs,LayeredExtractionState.State q₀ a₀ D H (n*n) q rs ∧ Data q τ ∧
        Output (front++encode rs) (count+rs.length) τ)
      ((innerCost n L (H*D)+26)*(n*n)+6) := by
  have hs := Spec.forRangeZero "short.commodity" "lp.n2"
    (fun σ => Context q₀ a₀ D H front count (σ.vars "short.commodity") σ) (n*n)
    (innerCost n L (H*D)+22) (by omega) (fun _ h => h.1)
    (fun _ h => by obtain ⟨_,_,_,q,rs,_,hd,_⟩:=h; exact hd.square)
    (step_spec B D H q₀ a₀ front count hn hL hD hH hB hsize hlen hcount ha)
  intro σ hσ
  have hinit : Context q₀ a₀ D H front count
      ((σ.setVar "short.commodity" 0).vars "short.commodity") (σ.setVar "short.commodity" 0) := by
    simpa only [vars_setVar,if_true] using set_index hσ 0
  obtain ⟨τ,rr,pr⟩ := hs σ hinit
  obtain ⟨_,_,_,q,rs,hm,hd,ho⟩:=pr.1
  exact ⟨τ,rr,q,rs,by simpa only [pr.2] using hm,hd,ho⟩

end Lax455465Proofs.RamAllCommodities
