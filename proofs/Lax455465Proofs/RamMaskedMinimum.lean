import Lax455465Proofs.RamBestFold
import Lax455465Proofs.RamArrayScalar

namespace Lax455465Proofs.RamMaskedMinimum
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open scoped NNRat

def valid (mask : List ℚ≥0) (i : ℕ) : Prop := (mask.getD i 0).num=1
instance (mask : List ℚ≥0) : DecidablePred (valid mask) := fun i => inferInstanceAs (Decidable ((_ : ℕ)=1))
def value (qs : List ℚ≥0) (i : ℕ) : ℚ≥0 := qs.getD i 0
def minimum (qs mask : List ℚ≥0) : ℚ≥0 :=
  match BestCutIndex.best (valid mask) (value qs) qs.length with
  | none => 0
  | some j => value qs j

def Context (source mask : String) (qs ms : List ℚ≥0) (σ : Env) : Prop :=
  σ.vars "cut.count"=qs.length ∧ Prefix (RamUnsignedBuffer.encode qs) source σ ∧
    Prefix (RamUnsignedBuffer.encode ms) mask σ

theorem frame {B K : ℕ} {cmd : Com} {σ τ : Env} (rr : Run B cmd σ τ K)
    {source mask : String} {qs ms : List ℚ≥0} (h : Context source mask qs ms σ)
    (hx : "cut.count"∉cmd.wvars) (hs : source∉cmd.warrs) (hm : mask∉cmd.warrs) : Context source mask qs ms τ := by
  simpa only [Context,Prefix,rr.frame_var "cut.count" hx,rr.frame_arr source hs,rr.frame_arr mask hm] using h

def entry (source mask : String) : Com := .seq (RamArrayScalar.command source "cut.candidate" "cut.ratio")
  (.seq (RamUnsignedBuffer.read mask "cut.candidate") (.assign "cut.valid" (.var "rat.n")))
def command (source mask : String) : Com :=
  .seq (RamBestFold.command (entry source mask)) (load "best.value")

theorem entry_spec (B M : ℕ) (source mask : String) (qs ms : List ℚ≥0) (i : ℕ)
    (hi : i<qs.length) (hlen : ms.length=qs.length) (hM : 1≤M) (hB : 2*M^2+3<B) (hindex : 2*i+1<B)
    (hq : LpInputSize.Height M (qs[i] : ℚ)) (hmn : (ms[i]'(by omega)).num≤1) (hmd : (ms[i]'(by omega)).den≤1) :
    Spec B (fun σ => Context source mask qs ms σ ∧ σ.vars "cut.candidate"=i) (entry source mask)
      (fun _ τ => Context source mask qs ms τ ∧ RamBestUpdate.Current (valid ms) (value qs) i τ) 34 := by
  have hMB : M<B := by nlinarith
  have h1 : 1<B := by nlinarith
  rintro σ ⟨hσ,hidx⟩
  obtain ⟨ν,rq,pq⟩ := RamArrayScalar.command_spec B source "cut.candidate" "cut.ratio" qs i hi
    (by nlinarith) hindex ((num_bound hq).trans_lt hMB) ((den_bound hq).trans_lt hMB) (by decide) (by decide) σ ⟨hσ.2.1,hidx⟩
  have hν := frame rq hσ (by simp [RamArrayScalar.command,RamUnsignedBuffer.read,save,Com.wvars])
    (by simp [RamArrayScalar.command,RamUnsignedBuffer.read,save,Com.warrs])
    (by simp [RamArrayScalar.command,RamUnsignedBuffer.read,save,Com.warrs])
  have hiν : ν.vars "cut.candidate"=i := (rq.frame_var _ (by simp [RamArrayScalar.command,RamUnsignedBuffer.read,save,Com.wvars])).trans hidx
  obtain ⟨μ,rm,pm⟩ := RamUnsignedBuffer.read_spec B mask "cut.candidate" ms i (by omega)
    (by nlinarith) hindex (hmn.trans_lt h1) (hmd.trans_lt h1) (by decide) ν ⟨hν.2.2,hiν⟩
  have hm : μ.vars "rat.n"=ms[i].num := by simpa only [NNRat.natAbs_num_coe] using pm.1.2.1
  let τ := μ.setVar "cut.valid" ms[i].num
  have ra : Run B (.assign "cut.valid" (.var "rat.n")) μ τ 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hm.symm,hm ▸ hmn.trans_lt h1⟩)
  have rr := rq.seq (rm.seq ra)
  refine ⟨τ,rr,frame rr hσ (by simp [RamArrayScalar.command,RamUnsignedBuffer.read,save,Com.wvars])
    (by simp [RamArrayScalar.command,RamUnsignedBuffer.read,save,Com.warrs])
    (by simp [RamArrayScalar.command,RamUnsignedBuffer.read,save,Com.warrs]),
    (rr.frame_var _ (by simp [RamArrayScalar.command,RamUnsignedBuffer.read,save,Com.wvars])).trans hidx,?_,?_⟩
  · simp only [τ,vars_setVar,if_true,valid,List.getD_eq_get ms 0 ⟨i,by omega⟩]
    change ms[i].num=(if ms[i].num=1 then 1 else 0)
    split_ifs <;> omega
  · have hp := RamRoundingConstants.storedFrame (rm.seq ra) pq
      (by simp [RamUnsignedBuffer.read,Com.wvars]) (by simp [RamUnsignedBuffer.read,Com.wvars])
    simpa only [value,List.getD_eq_get qs 0 ⟨i,hi⟩,List.get_eq_getElem] using hp

/-- Minimum of a nonempty mask, computed by the same fixed forward fold as
the cut selector. Its value is an input coordinate, so its height does not grow. -/
theorem command_spec (B M : ℕ) (source mask : String) (qs ms : List ℚ≥0)
    (hlen : ms.length=qs.length) (hM : 1≤M) (hB : 2*M^2+3<B) (hindex : 2*qs.length+2<B)
    (hq : ∀ i,∀ hi : i<qs.length,LpInputSize.Height M (qs[i] : ℚ))
    (hmn : ∀ q∈ms,q.num≤1) (hmd : ∀ q∈ms,q.den≤1)
    (hex : ∃ i<qs.length,valid ms i) :
    Spec B (Context source mask qs ms) (command source mask)
      (fun _ τ => Context source mask qs ms τ ∧ RamRational.FractionOutput (minimum qs ms : ℚ) τ)
      (126*qs.length+16) := by
  have hvalue (i : ℕ) (hi : i<qs.length) : LpInputSize.Height M (value qs i : ℚ) := by
    simpa only [value,List.getD_eq_get qs 0 ⟨i,hi⟩,List.get_eq_getElem] using hq i hi
  have hscan := RamBestFold.command_spec B M 34 (Context source mask qs ms) (valid ms) (value qs) qs.length
    (entry source mask) hB (by omega) hvalue (fun _ h => h.1)
    (fun σ k name hn h => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl | rfl | rfl <;> simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (fun i hi => entry_spec B M source mask qs ms i hi hlen hM hB (by omega) (hq i hi)
      (hmn _ (List.getElem_mem (by omega))) (hmd _ (List.getElem_mem (by omega))))
    (by dsimp [RamBestFold.bestNames,entry,RamArrayScalar.command,RamUnsignedBuffer.read,Com.wvars,save]; decide)
    (fun rr h => frame rr h (by decide) (by simp [RamBestUpdate.command,RamBestUpdate.choose,RamBestUpdate.compare,
      RamBestUpdate.update,RamScalarComparison.command,RamScalarBinary.command,RamComparison.compareFraction,Com.warrs,load,RamUnsignedArithmetic.copy])
      (by simp [RamBestUpdate.command,RamBestUpdate.choose,RamBestUpdate.compare,
      RamBestUpdate.update,RamScalarComparison.command,RamScalarBinary.command,RamComparison.compareFraction,Com.warrs,load,RamUnsignedArithmetic.copy]))
  have hexBest : ∃ j,BestCutIndex.best (valid ms) (value qs) qs.length=some j := by
    cases he : BestCutIndex.best (valid ms) (value qs) qs.length with
    | none => obtain ⟨i,hi,hv⟩ := hex; exact False.elim ((BestCutIndex.best_none _ _ _).mp he i hi hv)
    | some j => exact ⟨j,rfl⟩
  obtain ⟨j,hj⟩ := hexBest
  have hjlt := (BestCutIndex.best_sound _ _ _ j hj).1
  have hheight := hvalue j hjlt
  have hMB : M<B := by nlinarith
  rintro σ hσ
  obtain ⟨ν,rs,ps⟩ := hscan σ hσ
  have hm : RamBestUpdate.Matches (value qs) (some j) ν := by simpa only [hj] using ps.2
  obtain ⟨τ,rl,pl⟩ := load_spec B "best.value" (value qs j) (by nlinarith)
    ((num_bound hheight).trans_lt hMB) ((den_bound hheight).trans_lt hMB) (by decide) ν hm.2.2
  exact ⟨τ,(rs.seq rl).mono (by omega),frame rl ps.1 (by decide) (by simp [load,Com.warrs]) (by simp [load,Com.warrs]),
    by simpa only [minimum,hj] using pl⟩

end Lax455465Proofs.RamMaskedMinimum
