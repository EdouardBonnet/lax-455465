import Lax455465Proofs.RamFind
import Lax455465Proofs.RamArrayScalar
import Lax455465Proofs.CutScoreData

set_option maxRecDepth 8192
namespace Lax455465Proofs.RamPositivePair
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding DirectedFlowLP FlowLpIndices
open scoped NNRat

def predicate {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n) (i : ℕ) : Bool :=
  if hi : i<n*n then
    let uv := (edgeIndex n).symm ⟨i,hi⟩
    decide (0<(I.weight uv.1).num ∧ 0<(I.weight uv.2).num ∧ 0<(d uv.1 uv.2).num)
  else false

def Context {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n) (σ : Env) : Prop :=
  σ.vars "metric.n"=n ∧ σ.vars "metric.n2"=n*n ∧ σ.vars "find.count"=n*n ∧
    Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ ∧
    Prefix (RamUnsignedBuffer.encode (MetricMatrix.values d)) "metric.old" σ

theorem frame {B K : ℕ} {cmd : Com} {σ τ : Env} (rr : Run B cmd σ τ K)
    {n : ℕ} {I : RationalInstance n} {d : MetricMatrix.Matrix n} (h : Context I d σ)
    (hx : ∀ x∈["metric.n","metric.n2","find.count"],x∉cmd.wvars)
    (ha : ∀ a∈["flow.weights","metric.old"],a∉cmd.warrs) : Context I d τ := by
  simpa only [Context,Prefix,rr.frame_var "metric.n" (hx _ (by simp)),rr.frame_var "metric.n2" (hx _ (by simp)),
    rr.frame_var "find.count" (hx _ (by simp)),rr.frame_arr "flow.weights" (ha _ (by simp)),
    rr.frame_arr "metric.old" (ha _ (by simp))] using h

def indices : Com := .seq (.assign "pair.u" (.div (.var "find.i") (.var "metric.n")))
  (.assign "pair.v" (.sub (.var "find.i") (.mul (.var "pair.u") (.var "metric.n"))))
def flags : Com := .ite (.eq (.var "pair.left.n") (.lit 0)) (.assign "find.ok" (.lit 0))
  (.ite (.eq (.var "pair.right.n") (.lit 0)) (.assign "find.ok" (.lit 0))
    (.ite (.eq (.var "pair.distance.n") (.lit 0)) (.assign "find.ok" (.lit 0)) (.assign "find.ok" (.lit 1))))
def test : Com := .seq indices (.seq (RamArrayScalar.command "flow.weights" "pair.u" "pair.left")
  (.seq (RamArrayScalar.command "flow.weights" "pair.v" "pair.right")
    (.seq (RamArrayScalar.command "metric.old" "find.i" "pair.distance") flags)))
def command : Com := .seq (.assign "find.count" (.var "metric.n2")) (RamFind.command test)

theorem indices_spec (B : ℕ) {n : ℕ} (u v : Fin n) (hn : n<B) (hn2 : n*n<B) :
    Spec B (fun σ => σ.vars "metric.n"=n ∧ σ.vars "find.i"=(edgeIndex n (u,v)).val) indices
      (fun _ τ => τ.vars "pair.u"=u.val ∧ τ.vars "pair.v"=v.val) 10 := by
  have hidx : (edgeIndex n (u,v)).val<B := (edgeIndex n (u,v)).isLt.trans hn2
  have hu : u.val<B := u.isLt.trans hn
  have hv : v.val<B := v.isLt.trans hn
  have hprod : u.val*n<B := by rw [edge_value] at hidx; omega
  have hdiv := edge_div u v
  have hmod := edge_mod u v
  rw [Nat.mod_def] at hmod
  rintro σ ⟨hnσ,hiσ⟩
  run_vcg
  all_goals simp_all [edge_value]

theorem flags_spec (B a b c : ℕ) (h1 : 1<B) (ha : a<B) (hb : b<B) (hc : c<B) :
    Spec B (fun σ => σ.vars "pair.left.n"=a ∧ σ.vars "pair.right.n"=b ∧ σ.vars "pair.distance.n"=c) flags
      (fun _ τ => τ.vars "find.ok"=(if 0<a ∧ 0<b ∧ 0<c then 1 else 0)) 14 := by
  rintro σ ⟨haσ,hbσ,hcσ⟩
  run_vcg
  all_goals simp_all

theorem test_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (i : ℕ) (hi : i<n*n) (hMB : M<B) (h2 : 2<B) (hindex : 2*(n*n)+2<B) (hvertex : 2*n+2<B)
    (hw : ∀ v,LpInputSize.Height M (I.weight v : ℚ)) (hd : ∀ u v,LpInputSize.Height M (d u v : ℚ)) :
    Spec B (fun σ => Context I d σ ∧ σ.vars "find.i"=i) test
      (fun _ τ => Context I d τ ∧ τ.vars "find.ok"=(if predicate I d i then 1 else 0)) 78 := by
  let uv := (edgeIndex n).symm ⟨i,hi⟩
  have he : (edgeIndex n uv).val=i := congrArg Fin.val ((edgeIndex n).apply_symm_apply ⟨i,hi⟩)
  have hdist : (MetricMatrix.values d)[i]'(by simpa only [MetricMatrix.length_values] using hi)=d uv.1 uv.2 := by
    simpa only [he] using MetricMatrix.value_at d uv.1 uv.2
  rintro σ ⟨hσ,hidx⟩
  obtain ⟨σ1,r1,p1⟩ := indices_spec B uv.1 uv.2 (by omega) (by omega) σ ⟨hσ.1,by simpa only [he] using hidx⟩
  have h1 := frame r1 hσ (by decide) (by decide)
  obtain ⟨σ2,r2,p2⟩ := RamArrayScalar.command_spec B "flow.weights" "pair.u" "pair.left" (List.ofFn I.weight) uv.1.val
    (by simpa using uv.1.isLt) h2 (by have := uv.1.isLt; omega)
    (by simpa only [List.getElem_ofFn] using (num_bound (hw uv.1)).trans_lt hMB)
    (by simpa only [List.getElem_ofFn] using (den_bound (hw uv.1)).trans_lt hMB) (by decide) (by decide) σ1 ⟨h1.2.2.2.1,p1.1⟩
  have h2σ := frame r2 h1 (by decide) (by decide)
  have hv : σ2.vars "pair.v"=uv.2.val := (r2.frame_var _ (by decide)).trans p1.2
  obtain ⟨σ3,r3,p3⟩ := RamArrayScalar.command_spec B "flow.weights" "pair.v" "pair.right" (List.ofFn I.weight) uv.2.val
    (by simpa using uv.2.isLt) h2 (by have := uv.2.isLt; omega)
    (by simpa only [List.getElem_ofFn] using (num_bound (hw uv.2)).trans_lt hMB)
    (by simpa only [List.getElem_ofFn] using (den_bound (hw uv.2)).trans_lt hMB) (by decide) (by decide) σ2 ⟨h2σ.2.2.2.1,hv⟩
  have h3 := frame r3 h2σ (by decide) (by decide)
  have hidx3 : σ3.vars "find.i"=i := ((r1.seq (r2.seq r3)).frame_var _ (by decide)).trans hidx
  obtain ⟨σ4,r4,p4⟩ := RamArrayScalar.command_spec B "metric.old" "find.i" "pair.distance" (MetricMatrix.values d) i
    (by simpa only [MetricMatrix.length_values] using hi) h2 (by omega)
    (by rw [hdist]; exact (num_bound (hd uv.1 uv.2)).trans_lt hMB)
    (by rw [hdist]; exact (den_bound (hd uv.1 uv.2)).trans_lt hMB) (by decide) (by decide) σ3 ⟨h3.2.2.2.2,hidx3⟩
  have hleft := RamRoundingConstants.storedFrame (r3.seq r4) p2 (by decide) (by decide)
  have hright := RamRoundingConstants.storedFrame r4 p3 (by decide) (by decide)
  obtain ⟨τ,r5,p5⟩ := flags_spec B (I.weight uv.1).num (I.weight uv.2).num (d uv.1 uv.2).num (by omega)
    ((num_bound (hw uv.1)).trans_lt hMB) ((num_bound (hw uv.2)).trans_lt hMB)
    ((num_bound (hd uv.1 uv.2)).trans_lt hMB) σ4
    ⟨by simpa only [Stored,List.getElem_ofFn,Fin.eta,String.reduceAppend] using hleft.1,
      by simpa only [Stored,List.getElem_ofFn,Fin.eta,String.reduceAppend] using hright.1,
      by simpa only [hdist,String.reduceAppend] using p4.1⟩
  have rr := r1.seq (r2.seq (r3.seq (r4.seq r5)))
  exact ⟨τ,rr,frame rr hσ (by decide) (by decide),by simpa only [predicate,dif_pos hi,decide_eq_true_eq,uv] using p5⟩

theorem command_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (hMB : M<B) (h2 : 2<B) (hindex : 2*(n*n)+2<B) (hvertex : 2*n+2<B)
    (hw : ∀ v,LpInputSize.Height M (I.weight v : ℚ)) (hd : ∀ u v,LpInputSize.Height M (d u v : ℚ)) :
    Spec B (fun σ => σ.vars "metric.n"=n ∧ σ.vars "metric.n2"=n*n ∧
      Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ ∧
      Prefix (RamUnsignedBuffer.encode (MetricMatrix.values d)) "metric.old" σ) command
      (fun _ τ => Context I d τ ∧ RamFind.Matches (RamFind.first (predicate I d) (n*n)) τ) (98*(n*n)+12) := by
  have hscan := RamFind.command_spec B (n*n) 78 (Context I d) (predicate I d) test (by omega) (by omega)
    (fun _ h => h.2.2.1)
    (fun σ k name h hn => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl | rfl | rfl <;> simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (fun i hi => test_spec B M I d i hi hMB h2 hindex hvertex hw hd) (by decide)
  rintro σ ⟨hn,hn2,hwσ,hdσ⟩
  let ν := σ.setVar "find.count" (n*n)
  have rc : Run B (.assign "find.count" (.var "metric.n2")) σ ν 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hn2.symm,hn2 ▸ (by omega : n*n<B)⟩)
  obtain ⟨τ,rs,ps⟩ := hscan ν ⟨by simpa [ν] using hn,by simpa [ν] using hn2,by simp [ν],hwσ,hdσ⟩
  exact ⟨τ,(rc.seq rs).mono (by omega),ps⟩

end Lax455465Proofs.RamPositivePair
