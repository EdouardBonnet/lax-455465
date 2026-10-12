import Lax455465Proofs.SetDistanceData

set_option maxRecDepth 8192
namespace Lax455465Proofs.RamSetDistances
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRegionContext
open scoped NNRat

def Context {n : ℕ} (d : MetricMatrix.Matrix n) (S : Finset (Fin n)) (σ : Env) : Prop :=
  σ.vars "metric.n"=n ∧ σ.vars "cut.count"=n ∧
    Prefix (RamUnsignedBuffer.encode (MetricMatrix.values d)) "metric.old" σ ∧
    Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "potential.set" σ

theorem frame {B K : ℕ} {cmd : Com} {σ τ : Env} (rr : Run B cmd σ τ K)
    {n : ℕ} {d : MetricMatrix.Matrix n} {S : Finset (Fin n)} (h : Context d S σ)
    (hx : ∀ x∈["metric.n","cut.count"],x∉cmd.wvars)
    (ha : ∀ a∈["metric.old","potential.set"],a∉cmd.warrs) : Context d S τ := by
  simpa only [Context,Prefix,rr.frame_var "metric.n" (hx _ (by simp)),rr.frame_var "cut.count" (hx _ (by simp)),
    rr.frame_arr "metric.old" (ha _ (by simp)),rr.frame_arr "potential.set" (ha _ (by simp))] using h

def entry (toSet : Bool) : Com := .seq (RamRootDistances.command toSet)
  (RamMaskedMinimum.command (RamRootDistances.array toSet) "potential.set")
def command (toSet : Bool) : Com := .seq (.assign "potential.pos" (.lit 0))
  (RamUnsignedVector.command "region.root" "metric.n" "potential.values" "potential.pos" (entry toSet))
def cost (n : ℕ) : ℕ := (168*n+46)*n+8

theorem entry_spec (B M : ℕ) {n : ℕ} (toSet : Bool) (d : MetricMatrix.Matrix n)
    (S : Finset (Fin n)) (hS : S.Nonempty) (v : Fin n) (hM : 1≤M) (hB : 2*M^2+3<B)
    (hindex : 2*(n*n)+2<B) (hvertex : 2*n+2<B) (hd : ∀ u v,LpInputSize.Height M (d u v : ℚ)) :
    Spec B (fun σ => Context d S σ ∧ σ.vars "region.root"=v.val ∧
        2*n<(σ.arrs (RamRootDistances.array toSet)).length) (entry toSet)
      (fun _ τ => Context d S τ ∧ RamRational.FractionOutput (SetDistanceData.distance toSet d S hS v : ℚ) τ)
      (168*n+24) := by
  have hMB : M<B := by nlinarith
  rintro σ ⟨hσ,hroot,hroom⟩
  obtain ⟨ν,rr,pr⟩ := RamRootDistances.command_spec B M toSet v d hMB (by omega) (by omega) hindex
    (fun u v => num_bound (hd u v)) (fun u v => den_bound (hd u v)) σ
      ⟨⟨hσ.1,hroot,hσ.2.2.1⟩,hroom⟩
  have hν := frame rr hσ (by cases toSet <;> decide) (by cases toSet <;> decide)
  have hqs : ∀ i,∀ hi : i<(RamRootDistances.vector toSet v d).length,
      LpInputSize.Height M ((RamRootDistances.vector toSet v d)[i] : ℚ) := by
    intro i hi
    have hi' : i<n := by simpa only [RamRootDistances.length_vector] using hi
    simp only [RamRootDistances.vector,List.getElem_ofFn]
    cases toSet <;> exact hd _ _
  have hflags : ∀ q∈CutScoreData.vertexFlags S,q.num≤1 ∧ q.den≤1 := by
    intro q hq
    obtain ⟨u,rfl⟩ := List.mem_ofFn.mp hq
    change (if ResidualData.mask S u then (1 : ℚ≥0) else 0).num≤1 ∧
      (if ResidualData.mask S u then (1 : ℚ≥0) else 0).den≤1
    split_ifs <;> norm_num
  obtain ⟨τ,rm,pm⟩ := RamMaskedMinimum.command_spec B M (RamRootDistances.array toSet) "potential.set"
    (RamRootDistances.vector toSet v d) (CutScoreData.vertexFlags S)
    (by simp [CutScoreData.vertexFlags,MaskedMassData.flags]) hM hB (by simpa using hvertex) hqs
    (fun q hq => (hflags q hq).1) (fun q hq => (hflags q hq).2)
    (by simpa only [RamRootDistances.length_vector] using SetDistanceData.mask_nonempty S hS) ν
    ⟨by simpa only [RamRootDistances.length_vector] using hν.2.1,pr.2,hν.2.2.2⟩
  exact ⟨τ,(rr.seq rm).mono (by simp only [RamRootDistances.length_vector]; omega),
    frame rm hν (by cases toSet <;> decide) (by cases toSet <;> decide),
    by simpa only [SetDistanceData.minimum_vector toSet d S hS v] using pm.2⟩

set_option maxHeartbeats 3200000 in
/-- Compute all distances to or from a nonempty runtime vertex set. The
matrix and set mask are read from RAM; the result contains exact canonical
minima, each equal to an original distance-matrix entry. -/
theorem command_spec (B M : ℕ) {n : ℕ} (toSet : Bool) (d : MetricMatrix.Matrix n)
    (S : Finset (Fin n)) (hS : S.Nonempty) (hM : 1≤M) (hB : 2*M^2+3<B)
    (hindex : 2*(n*n)+2<B) (hvertex : 2*n+2<B) (hd : ∀ u v,LpInputSize.Height M (d u v : ℚ)) :
    Spec B (fun σ => Context d S σ ∧ 2*n<(σ.arrs (RamRootDistances.array toSet)).length ∧
        2*n<(σ.arrs "potential.values").length) (command toSet)
      (fun _ τ => Context d S τ ∧ Prefix (RamUnsignedBuffer.encode
        (List.ofFn (SetDistanceData.distance toSet d S hS))) "potential.values" τ) (cost n) := by
  let qs := List.ofFn (SetDistanceData.distance toSet d S hS)
  let R := fun σ => Context d S σ ∧ 2*n<(σ.arrs (RamRootDistances.array toSet)).length
  have hMB : M<B := by nlinarith
  have hheight (i : ℕ) (hi : i<qs.length) : LpInputSize.Height M (qs[i] : ℚ) := by
    simp only [qs,List.getElem_ofFn]
    exact SetDistanceData.height toSet d S hS M hd _
  have hloop := RamUnsignedVector.command_spec B (168*n+24) R "region.root" "metric.n"
    "potential.values" "potential.pos" qs [] (entry toSet) (by nlinarith)
    (by simpa only [qs,List.length_nil,List.length_ofFn,Nat.zero_add] using hvertex)
    (fun i hi => (num_bound (hheight i hi)).trans_lt hMB)
    (fun i hi => (den_bound (hheight i hi)).trans_lt hMB)
    (fun σ h => by simpa only [qs,List.length_ofFn] using h.1.1)
    (fun σ k h => by simpa only [R,Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (fun i hi σ h => by
      have hi' : i<n := by simpa only [qs,List.length_ofFn] using hi
      obtain ⟨τ,rr,pr⟩ := entry_spec B M toSet d S hS ⟨i,hi'⟩ hM hB hindex hvertex hd σ ⟨h.1.1,h.2,h.1.2⟩
      exact ⟨τ,rr,⟨pr.1,by rw [RamFrames.run_array_length rr]; exact h.1.2⟩,
        by simpa only [qs,List.getElem_ofFn] using pr.2⟩)
    (by cases toSet <;> decide) (by cases toSet <;> decide) (by cases toSet <;> decide) (by decide)
    (fun rr h => ⟨frame rr h.1 (by decide) (by decide),by rw [RamFrames.run_array_length rr]; exact h.2⟩)
    (by decide) (by decide)
  rintro σ ⟨hσ,hroom,hout⟩
  let ν := σ.setVar "potential.pos" 0
  have rz : Run B (.assign "potential.pos" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have hν := frame rz hσ (by decide) (by decide)
  obtain ⟨τ,rl,pl⟩ := hloop ν ⟨⟨hν,hroom⟩,by intro i hi; simp at hi,by simp [ν],by simpa only [ν,arrs_setVar,qs,List.length_nil,List.length_ofFn,Nat.zero_add] using hout⟩
  exact ⟨τ,(rz.seq rl).mono (by simp only [qs,List.length_ofFn,cost,Nat.add_assoc,Nat.reduceAdd]; omega),pl.1.1,
    by simpa only [List.nil_append,qs] using pl.2.1⟩

end Lax455465Proofs.RamSetDistances
