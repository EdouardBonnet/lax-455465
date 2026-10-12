import Lax455465Proofs.RamHalfFraction
import Lax455465Proofs.PrimalEncoding
import Lax455465Proofs.RamUnsignedVector
import Lax455465Proofs.RamGraphHeader

namespace Lax455465Proofs.RamFlowConvert
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational RamRegionContext
open Lax455465.RationalEncoding Lax455465.ProductNetwork
open scoped NNRat

def values (kind : EdgeKind) (qs : List ℚ≥0) : List ℚ≥0 :=
  List.ofFn fun i : Fin qs.length => if kind=.undirected ∧ i.val≠0 then qs[i.val]/2 else qs[i.val]

def Context (kind : EdgeKind) (qs : List ℚ≥0) (σ : Env) : Prop :=
  σ.vars "flow.kind"=RamGraphHeader.tag kind ∧ σ.vars "lp.columns"=qs.length ∧
    Prefix (RamUnsignedBuffer.encode qs) "flow.primal" σ

theorem frame {B K : ℕ} {cmd : Com} {σ τ : Env} (rr : Run B cmd σ τ K)
    {kind : EdgeKind} {qs : List ℚ≥0} (h : Context kind qs σ)
    (hx : ∀ x∈["flow.kind","lp.columns"],x∉cmd.wvars) (ha : "flow.primal"∉cmd.warrs) : Context kind qs τ := by
  simpa only [Context,Prefix,rr.frame_var "flow.kind" (hx _ (by simp)),
    rr.frame_var "lp.columns" (hx _ (by simp)),rr.frame_arr "flow.primal" ha] using h

def choose : Com := .ite (.eq (.var "flow.kind") (.lit 0))
  (.ite (.eq (.var "emit.coordinate") (.lit 0)) .skip RamHalfFraction.command) .skip

def body : Com := .seq (RamUnsignedBuffer.read "flow.primal" "emit.coordinate") choose

def command : Com := .seq (.assign "emit.convertedPos" (.lit 0))
  (RamUnsignedVector.command "emit.coordinate" "lp.columns" "flow.converted" "emit.convertedPos" body)

def bodyCost (M : ℕ) : ℕ := 36*(2*M).size+42

def cost (k M : ℕ) : ℕ := (bodyCost M+22)*k+8

theorem choose_spec (B M : ℕ) (kind : EdgeKind) (q : ℚ≥0) (i : ℕ)
    (h2 : 2 < B) (hB : 2*M < B) (hi : i < B) (hq : LpInputSize.Height M (q : ℚ)) :
    Spec B (fun σ => σ.vars "flow.kind"=RamGraphHeader.tag kind ∧ σ.vars "emit.coordinate"=i ∧
      FractionOutput (q : ℚ) σ ∧ σ.vars "rat.s"=0) choose
      (fun _ τ => FractionOutput ((if kind=.undirected ∧ i≠0 then q/2 else q : ℚ≥0) : ℚ) τ)
      (36*(2*M).size+28) := by
  rintro σ ⟨hk,hiσ,hqσ,hs⟩
  have ht : RamGraphHeader.tag kind < B := by cases kind <;> simp only [RamGraphHeader.tag] <;> omega
  have hc := evalB_condEq (evalB_var (hk ▸ ht)) (evalB_lit (by omega : 0 < B))
  rw [hk] at hc
  cases kind with
  | directed =>
    have hc' : (Cond.eq (.var "flow.kind") (.lit 0)).evalB B σ=some false := hc
    exact ⟨σ,(Run.ite_false (c := .ite (.eq (.var "emit.coordinate") (.lit 0)) .skip RamHalfFraction.command) hc' Run.skip).mono
      (by dsimp [Cond.size,Expr.size]; omega),by simpa using hqσ⟩
  | undirected =>
    have hc' : (Cond.eq (.var "flow.kind") (.lit 0)).evalB B σ=some true := hc
    have hci := evalB_condEq (evalB_var (hiσ ▸ hi)) (evalB_lit (by omega : 0 < B))
    rw [hiσ] at hci
    by_cases hz : i=0
    · have hci' : (Cond.eq (.var "emit.coordinate") (.lit 0)).evalB B σ=some true := by simpa [hz] using hci
      exact ⟨σ,(Run.ite_true (d := .skip) hc' (Run.ite_true (d := RamHalfFraction.command) hci' Run.skip)).mono
        (by dsimp [Cond.size,Expr.size]; omega),by simpa [hz] using hqσ⟩
    · have hci' : (Cond.eq (.var "emit.coordinate") (.lit 0)).evalB B σ=some false := by simpa [hz] using hci
      obtain ⟨τ,rr,pr⟩ := RamHalfFraction.command_spec B M q h2 hB hq σ ⟨hqσ,hs⟩
      exact ⟨τ,(Run.ite_true (d := .skip) hc' (Run.ite_false (c := .skip) hci' rr)).mono
        (by dsimp [Cond.size,Expr.size]; omega),by simpa [hz] using pr.1⟩

theorem value_height (M : ℕ) (kind : EdgeKind) (qs : List ℚ≥0)
    (hq : ∀ q∈qs,LpInputSize.Height M (q : ℚ)) (i : ℕ) (hi : i < (values kind qs).length) :
    LpInputSize.Height (2*M) ((values kind qs)[i] : ℚ) := by
  have hi' : i < qs.length := by simpa [values] using hi
  simp only [values,List.getElem_ofFn]
  split_ifs
  · have hh := LpInputSize.height_mul (hq qs[i] (List.getElem_mem hi'))
      (show LpInputSize.Height 2 (1/2 : ℚ) from by norm_num [LpInputSize.Height])
    change LpInputSize.Height (2*M) ((qs[i] : ℚ)/2)
    simpa only [div_eq_mul_inv,one_mul,Nat.mul_comm] using hh
  · exact LpInputSize.height_mono (hq qs[i] (List.getElem_mem hi')) (by omega)

theorem body_spec (B M : ℕ) (kind : EdgeKind) (qs : List ℚ≥0) (i : ℕ) (hi : i < qs.length)
    (h2 : 2 < B) (hB : 2*M < B) (hlen : 2*qs.length+2 < B)
    (hq : ∀ q∈qs,LpInputSize.Height M (q : ℚ)) :
    Spec B (fun σ => Context kind qs σ ∧ σ.vars "emit.coordinate"=i) body
      (fun _ τ => Context kind qs τ ∧
        FractionOutput ((if kind=.undirected ∧ i≠0 then qs[i]/2 else qs[i] : ℚ≥0) : ℚ) τ) (bodyCost M) := by
  rintro σ ⟨hc,hidx⟩
  have hh := hq qs[i] (List.getElem_mem hi)
  obtain ⟨ν,r1,p1⟩ := RamUnsignedBuffer.read_spec B "flow.primal" "emit.coordinate" qs i hi h2 (by omega)
    ((num_bound hh).trans_lt (by omega)) ((den_bound hh).trans_lt (by omega)) (by decide) σ ⟨hc.2.2,hidx⟩
  have hcν := frame r1 hc (by decide) (by decide)
  obtain ⟨τ,r2,p2⟩ := choose_spec B M kind qs[i] i h2 hB (by omega) hh ν
    ⟨hcν.1,(r1.frame_var "emit.coordinate" (by decide)).trans hidx,p1⟩
  exact ⟨τ,(r1.seq r2).mono (by dsimp [bodyCost]; omega),frame r2 hcν (by decide) (by decide),p2⟩

/-- Convert the actual primal buffer, preserving its value coordinate and
canonically halving only the undirected arc amounts. -/
theorem command_spec (B M : ℕ) (kind : EdgeKind) (qs : List ℚ≥0)
    (h2 : 2 < B) (hB : 2*M < B) (hlen : 2*qs.length+2 < B)
    (hq : ∀ q∈qs,LpInputSize.Height M (q : ℚ)) :
    Spec B (fun σ => Context kind qs σ ∧ 2*qs.length < (σ.arrs "flow.converted").length) command
      (fun _ τ => Context kind qs τ ∧ Prefix (RamUnsignedBuffer.encode (values kind qs)) "flow.converted" τ)
      (cost qs.length M) := by
  have hvalues : (values kind qs).length=qs.length := List.length_ofFn
  have hloop := RamUnsignedVector.command_spec B (bodyCost M) (Context kind qs)
    "emit.coordinate" "lp.columns" "flow.converted" "emit.convertedPos" (values kind qs) [] body (by omega)
    (by simpa only [List.length_nil,Nat.zero_add,hvalues] using hlen)
    (fun i hi => (num_bound (value_height M kind qs hq i hi)).trans_lt hB)
    (fun i hi => (den_bound (value_height M kind qs hq i hi)).trans_lt hB)
    (fun _ h => h.2.1.trans hvalues.symm)
    (fun σ k h => by simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (fun i hi σ hσ => by
      have hi' : i < qs.length := hvalues ▸ hi
      obtain ⟨τ,rr,pr⟩ := body_spec B M kind qs i hi' h2 hB hlen hq σ hσ
      exact ⟨τ,rr,pr.1,by simpa only [values,List.getElem_ofFn] using pr.2⟩)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr h => frame rr h (by decide) (by decide)) (by decide) (by decide)
  rintro σ ⟨hc,hroom⟩
  let ν := σ.setVar "emit.convertedPos" 0
  have rz : Run B (.assign "emit.convertedPos" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  obtain ⟨τ,rl,pl⟩ := hloop ν ⟨frame rz hc (by decide) (by decide),by intro i hi; simp at hi,
    by simp [ν],by simpa only [List.length_nil,Nat.zero_add,hvalues,ν,arrs_setVar] using hroom⟩
  exact ⟨τ,(rz.seq rl).mono (by simp only [cost,hvalues]; omega),pl.1,by simpa only [List.nil_append] using pl.2.1⟩

theorem primal_values {n : ℕ} (kind : EdgeKind) (z : Fin (1+(n*n)*(n*n)) → ℚ) (hz : ∀ i,0 ≤ z i) :
    values kind (RamOptimalDecode.vector z hz)=PrimalEncoding.converted kind z := by
  have hv : RamOptimalDecode.vector z hz=List.ofFn (fun i => (z i).toNNRat) := by
    change List.ofFn (fun i => (⟨z i,hz i⟩ : ℚ≥0))=_
    apply congrArg List.ofFn
    funext i
    apply NNRat.coe_injective
    simp [Rat.coe_toNNRat _ (hz i)]
  rw [hv]
  unfold values PrimalEncoding.converted
  simp only [List.length_ofFn,List.getElem_ofFn,Fin.val_cast,Fin.eta]

end Lax455465Proofs.RamFlowConvert
