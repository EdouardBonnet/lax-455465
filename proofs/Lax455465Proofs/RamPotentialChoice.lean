import Lax455465Proofs.RamPotentialAverage

set_option maxRecDepth 8192
namespace Lax455465Proofs.RamPotentialChoice
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding LargePotentialData
open scoped NNRat

def select (toSet : Bool) : Com := .seq (.assign "copy.count" (.mul (.lit 2) (.var "metric.n")))
  (.seq (RamArrayCopy.command (RamSetPotential.targetArray toSet) "cut.potential" "copy.count")
    (.assign "cut.reversed" (.lit (if toSet then 1 else 0))))
def command : Com := .seq (RamScalarComparison.command "potential.toAvg" "potential.fromAvg")
  (.ite (.eq (.var "cmp.le") (.lit 1)) (select false) (select true))

theorem select_spec (B M : ℕ) {n : ℕ} (toSet : Bool) (f : Fin n → ℚ≥0)
    (hMB : M<B) (h1 : 1<B) (hindex : 2*n+2<B) (hf : ∀ v,LpInputSize.Height M (f v : ℚ)) :
    Spec B (fun σ => σ.vars "metric.n"=n ∧ Prefix (RamUnsignedBuffer.encode (List.ofFn f))
        (RamSetPotential.targetArray toSet) σ ∧ 2*n<(σ.arrs "cut.potential").length) (select toSet)
      (fun _ τ => τ.vars "cut.reversed"=(if toSet then 1 else 0) ∧
        Prefix (RamUnsignedBuffer.encode (List.ofFn f)) "cut.potential" τ) (24*n+12) := by
  let xs := RamUnsignedBuffer.encode (List.ofFn f)
  have hlen : xs.length=2*n := by simp [xs]
  have hwords : ∀ x∈xs,x<B := RamSetPotential.encoded_bound B M (List.ofFn f) hMB
    (by intro q hq; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq; exact hf v)
  rintro σ ⟨hn,hp,hroom⟩
  let ν := σ.setVar "copy.count" (2*n)
  have rc : Run B (.assign "copy.count" (.mul (.lit 2) (.var "metric.n"))) σ ν 4 :=
    Run.assign (evalB_bin (op := .mul) (evalB_lit (by omega))
      (by rw [evalB_var_iff]; exact ⟨hn.symm,hn ▸ (by omega : n<B)⟩) (by dsimp [Bop.apply]; omega))
  obtain ⟨μ,rr,pr⟩ := RamArrayCopy.command_spec B xs (RamSetPotential.targetArray toSet) "cut.potential" "copy.count"
    h1 (by rw [hlen]; omega) hwords (by cases toSet <;> decide) (by decide) ν
    ⟨hp,by simp [ν,hlen],by rw [hlen]; exact hroom.le⟩
  let τ := μ.setVar "cut.reversed" (if toSet then 1 else 0)
  have rflag : Run B (.assign "cut.reversed" (.lit (if toSet then 1 else 0))) μ τ 2 :=
    Run.assign (evalB_lit (by split_ifs <;> omega))
  exact ⟨τ,(rc.seq (rr.seq rflag)).mono (by rw [hlen]; omega),by simp [τ],pr.2⟩

structure Input {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (Tin Tout : Finset (Fin n)) (hin : Tin.Nonempty) (hout : Tout.Nonempty) (σ : Env) : Prop where
  nValue : σ.vars "metric.n"=n
  fromAverage : Stored "potential.fromAvg" (average I false d Tout hout) σ
  toAverage : Stored "potential.toAvg" (average I true d Tin hin) σ
  fromData : Prefix (RamUnsignedBuffer.encode (vector false d Tout hout)) "potential.from" σ
  toData : Prefix (RamUnsignedBuffer.encode (vector true d Tin hin)) "potential.to" σ
  room : 2*n<(σ.arrs "cut.potential").length

theorem command_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n) (d : MetricMatrix.Matrix n)
    (Tin Tout : Finset (Fin n)) (hin : Tin.Nonempty) (hout : Tout.Nonempty)
    (hb : Bounds I d Tin Tout hin hout M) (hB : 2*M^2+3<B) (hindex : 2*n+2<B) :
    Spec B (Input I d Tin Tout hin hout) command
      (fun _ τ => τ.vars "cut.reversed"=(if reversed I d Tin Tout hin hout then 1 else 0) ∧
        Prefix (RamUnsignedBuffer.encode (List.ofFn (values I d Tin Tout hin hout))) "cut.potential" τ)
      (24*n+80) := by
  have hMB : M<B := by nlinarith
  have h1 : 1<B := by nlinarith
  have hfrom : LpInputSize.Height M (average I false d Tout hout : ℚ) := by
    simpa only [average,List.take_length] using hb.fromPrefix (products I false d Tout hout).length
  have hto : LpInputSize.Height M (average I true d Tin hin : ℚ) := by
    simpa only [average,List.take_length] using hb.toPrefix (products I true d Tin hin).length
  rintro σ hσ
  obtain ⟨ν,rc,pc⟩ := RamScalarComparison.command_spec B M (average I true d Tin hin) (average I false d Tout hout)
    "potential.toAvg" "potential.fromAvg" hB (num_bound hto) (den_bound hto) (num_bound hfrom) (den_bound hfrom)
    (by decide) (by decide) (by decide) σ ⟨hσ.toAverage,hσ.fromAverage⟩
  have hn : ν.vars "metric.n"=n := (rc.frame_var _ (by decide)).trans hσ.nValue
  have hroom : 2*n<(ν.arrs "cut.potential").length := by rw [RamFrames.run_array_length rc]; exact hσ.room
  by_cases h : average I true d Tin hin≤average I false d Tout hout
  · have hcmp : ν.vars "cmp.le"=1 := by simpa only [NNRat.coe_le_coe,if_pos h] using pc
    have hc : (Cond.eq (.var "cmp.le") (.lit 1)).evalB B ν=some true := by
      rw [evalB_condEq (evalB_var (hcmp ▸ h1)) (evalB_lit h1),hcmp]; rfl
    have hp : Prefix (RamUnsignedBuffer.encode (vector false d Tout hout)) "potential.from" ν := by
      simpa only [Prefix,rc.frame_arr "potential.from" (by decide)] using hσ.fromData
    obtain ⟨τ,rs,ps⟩ := select_spec B M false (SetDistanceData.distance false d Tout hout) hMB h1 hindex
      (SetDistanceData.height false d Tout hout M hb.distances) ν ⟨hn,hp,hroom⟩
    exact ⟨τ,(rc.seq (Run.ite_true (d := select true) hc rs)).mono (by dsimp [Cond.size,Expr.size]; omega),
      by simpa only [reversed,values,if_pos h,Bool.false_eq_true,if_false] using ps⟩
  · have hcmp : ν.vars "cmp.le"=0 := by simpa only [NNRat.coe_le_coe,if_neg h] using pc
    have hc : (Cond.eq (.var "cmp.le") (.lit 1)).evalB B ν=some false := by
      rw [evalB_condEq (evalB_var (hcmp ▸ (by omega : 0<B))) (evalB_lit h1),hcmp]; rfl
    have hp : Prefix (RamUnsignedBuffer.encode (vector true d Tin hin)) "potential.to" ν := by
      simpa only [Prefix,rc.frame_arr "potential.to" (by decide)] using hσ.toData
    obtain ⟨τ,rs,ps⟩ := select_spec B M true (SetDistanceData.distance true d Tin hin) hMB h1 hindex
      (SetDistanceData.height true d Tin hin M hb.distances) ν ⟨hn,hp,hroom⟩
    exact ⟨τ,(rc.seq (Run.ite_false (c := select false) hc rs)).mono (by dsimp [Cond.size,Expr.size]; omega),
      by simpa only [reversed,values,if_neg h,if_true] using ps⟩

end Lax455465Proofs.RamPotentialChoice
