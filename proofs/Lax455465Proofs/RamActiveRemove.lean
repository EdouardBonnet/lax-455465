import Lax455465Proofs.RamBooleanVector
import Lax455465Proofs.RamArrayCopy
import Lax455465Proofs.ResidualData

namespace Lax455465Proofs.RamActiveRemove
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open scoped NNRat

def Context {n : ℕ} (active outBall inBall : Finset (Fin n)) (outward : Bool) (σ : Env) : Prop :=
  σ.vars "metric.n"=n ∧ σ.vars "region.outward"=(if outward then 1 else 0) ∧
  Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask active))) "region.active" σ ∧
  Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask outBall))) "region.outMask" σ ∧
  Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask inBall))) "region.inMask" σ

def removed {n : ℕ} (active outBall inBall : Finset (Fin n)) (outward : Bool) : Finset (Fin n) :=
  active \ (if outward then outBall else inBall)

def select : Com := .ite (.eq (.var "region.outward") (.lit 1))
  (RamBooleanVector.command (some true) "region.active" "region.outMask" "region.nextActive")
  (RamBooleanVector.command (some true) "region.active" "region.inMask" "region.nextActive")

def command : Com := .seq select (.seq (.assign "copy.count" (.mul (.lit 2) (.var "metric.n")))
  (RamArrayCopy.command "region.nextActive" "region.active" "copy.count"))

theorem difference_mask {n : ℕ} (active ball : Finset (Fin n)) :
    (fun v => RamBooleanArithmetic.flag (some true) (ResidualData.mask active v) (ResidualData.mask ball v)) =
      ResidualData.mask (active \ ball) := by
  funext v
  simp [RamBooleanArithmetic.flag,ResidualData.mask,Finset.mem_sdiff]

set_option maxHeartbeats 1200000 in
/-- Remove the selected ball from the actual active-vertex buffer, keeping
zero-weight transit vertices active whenever they lie outside that ball. -/
theorem command_spec (B : ℕ) {n : ℕ} (active outBall inBall : Finset (Fin n)) (outward : Bool)
    (h2 : 2<B) (hindex : 2*n+2<B) :
    Spec B (fun σ => Context active outBall inBall outward σ ∧
      2*n<(σ.arrs "region.nextActive").length ∧ 2*n≤(σ.arrs "region.active").length)
      command (fun _ τ => τ.vars "metric.n"=n ∧
        Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags
          (ResidualData.mask (removed active outBall inBall outward)))) "region.active" τ)
      (96*n+22) := by
  let next := RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask (removed active outBall inBall outward)))
  have hlen : next.length=2*n := by simp [next,MaskedMassData.flags]
  have hwords : ∀ x∈next, x<B := by
    intro x hx
    simp only [next,RamUnsignedBuffer.encode,List.mem_flatMap] at hx
    obtain ⟨q,hq,hx⟩ := hx
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    by_cases hv : v∈removed active outBall inBall outward <;>
      simp [ResidualData.mask,hv,Lax455465.RationalEncoding.encodeRational] at hx <;> omega
  rintro σ ⟨hσ,hroom,hactive⟩
  have selected : ∃ ν, Run B select σ ν (72*n+12) ∧
      Prefix next "region.nextActive" ν := by
    cases ho : outward
    · have hc : (Cond.eq (.var "region.outward") (.lit 1)).evalB B σ=some false := by
        have hd : σ.vars "region.outward"=0 := by simpa only [ho,Bool.false_eq_true,if_false] using hσ.2.1
        rw [evalB_condEq (evalB_var (hd ▸ (by omega : 0<B))) (evalB_lit (by omega)),hd]
        rfl
      obtain ⟨ν,rr,pr⟩ := RamBooleanVector.command_spec B (some true) "region.active" "region.inMask" "region.nextActive"
        (ResidualData.mask active) (ResidualData.mask inBall) h2 hindex (by decide) σ
        ⟨⟨hσ.1,hσ.2.2.1,hσ.2.2.2.2⟩,hroom⟩
      refine ⟨ν,(Run.ite_false (c := RamBooleanVector.command (some true) "region.active" "region.outMask" "region.nextActive") hc rr).mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
      simpa only [next,removed,ho,Bool.false_eq_true,if_false,difference_mask] using pr.2
    · have hc : (Cond.eq (.var "region.outward") (.lit 1)).evalB B σ=some true := by
        have hd : σ.vars "region.outward"=1 := by simpa only [ho,if_true] using hσ.2.1
        rw [evalB_condEq (evalB_var (hd ▸ (by omega : 1<B))) (evalB_lit (by omega)),hd]
        rfl
      obtain ⟨ν,rr,pr⟩ := RamBooleanVector.command_spec B (some true) "region.active" "region.outMask" "region.nextActive"
        (ResidualData.mask active) (ResidualData.mask outBall) h2 hindex (by decide) σ
        ⟨⟨hσ.1,hσ.2.2.1,hσ.2.2.2.1⟩,hroom⟩
      refine ⟨ν,(Run.ite_true (d := RamBooleanVector.command (some true) "region.active" "region.inMask" "region.nextActive") hc rr).mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
      simpa only [next,removed,ho,if_true,difference_mask] using pr.2
  obtain ⟨ν,rs,ps⟩ := selected
  have hn : ν.vars "metric.n"=n := (rs.frame_var _ (by dsimp [select,RamBooleanVector.command,RamBooleanVector.entry,RamUnsignedVector.command,Com.wvars,RamUnsignedEncoding.command,RamWordBuffer.append]; decide)).trans hσ.1
  let μ := ν.setVar "copy.count" (2*n)
  have rc : Run B (.assign "copy.count" (.mul (.lit 2) (.var "metric.n"))) ν μ 4 :=
    Run.assign (evalB_bin (op := .mul) (evalB_lit h2) (by rw [evalB_var_iff]; exact ⟨hn.symm,hn ▸ (by omega : n<B)⟩) (by dsimp [Bop.apply]; omega))
  obtain ⟨τ,rr,pr⟩ := RamArrayCopy.command_spec B next "region.nextActive" "region.active" "copy.count"
    (by omega) (by rw [hlen]; omega) hwords (by decide) (by decide) μ
    ⟨by simpa only [Prefix,μ,arrs_setVar] using ps,by simp [μ,hlen],
      by simpa only [μ,arrs_setVar,hlen,RamFrames.run_array_length rs "region.active"] using hactive⟩
  have run := rs.seq (rc.seq rr)
  exact ⟨τ,run.mono (by rw [hlen]; omega),
    (run.frame_var _ (by dsimp [command,select,RamBooleanVector.command,RamBooleanVector.entry,RamUnsignedVector.command,RamArrayCopy.command,RamArrayCopy.step,Com.wvars,RamUnsignedEncoding.command,RamWordBuffer.append]; decide)).trans hσ.1,pr.2⟩

end Lax455465Proofs.RamActiveRemove
