import Lax455465Proofs.RamShortTrial
import Lax455465Proofs.RamLayeredHostWidth
import Lax455465Proofs.LayeredOptimalCertificate

namespace Lax455465Proofs.RamShortLpCalls
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open LayeredFlowLP LayeredLpFlat LayeredFlowDual LayeredFlowFeasibility RamShortContext
open Lax455465.RationalEncoding Lax109476.RationalCertificates
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open scoped NNRat

/-- One fixed registered solver supplies the whole family of layered
primal-dual pairs. The family is tied to its actual executions, so the
selection proof and the final extraction use the same emitted values. -/
theorem exists_program :
    ∃ (p : Lax808846.Ram.Program) (WB TB : Polynomial ℕ) (coefficients : List ℕ),
      ∀ {n : ℕ} (kind : Lax455465.ProductNetwork.EdgeKind) (I : RationalInstance n),2 ≤ n →
        ∃ (f : ℕ → ℚ≥0) (x : ∀ L,Arc n L → ℚ) (y : ∀ L,Dual n L),
          (∀ L,Feasible I (f L : ℚ) (x L) ∧
            Lax109476.LinearProgram.DualFeasible (program I L) (y L) ∧
            (f L : ℚ)=Lax109476.LinearProgram.dualValue (program I L) (y L)) ∧
          (∀ L,FitsInWords (WB.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I L))))
            (Lax109476.RationalEncoding.encodeCertificate (.optimal (vector (f L : ℚ) (x L)) (y L)))) ∧
          ∀ L,L ≤ n → ∀ W : ℕ,
            (RamLayeredHostWidth.wordBound p WB TB).eval (bitSize (encodeInput kind I)) ≤ W →
            ∀ R : ℚ≥0,
              let S := LayeredLpSize.sizeBound.eval (bitSize (encodeInput kind I))
              Spec (2^W) (fun σ => Context I R S (TB.eval S) σ ∧ RamLayeredData.Data I L σ)
                (RamLayeredLpSolver.command p coefficients)
                (fun _ τ => Context I R S (TB.eval S) τ ∧
                  Prefix (Lax109476.RationalEncoding.encodeCertificate (.optimal (vector (f L : ℚ) (x L)) (y L)))
                    "vm.output" τ)
                ((RamLayeredSolverBounds.timeBound p coefficients TB).eval (bitSize (encodeInput kind I))) := by
  classical
  obtain ⟨p,WB,TB,coefficients,hsolve⟩ := RamLayeredLpSolver.exists_program
  refine ⟨p,WB,TB,coefficients,?_⟩
  intro n kind I hn
  choose certificate hvalid hfit hexec using (fun L => hsolve I L)
  have hopt : ∀ L,∃ (f : ℚ≥0) (x : Arc n L → ℚ) (y : Dual n L),
      certificate L=.optimal (vector (f : ℚ) x) y ∧ Feasible I (f : ℚ) x ∧
      Lax109476.LinearProgram.DualFeasible (program I L) y ∧
      (f : ℚ)=Lax109476.LinearProgram.dualValue (program I L) y := by
    intro L
    obtain ⟨f,x,y,he,hf,hy,hv⟩ := LayeredOptimalCertificate.optimal I hn (certificate L) (hvalid L)
    exact ⟨⟨f,hf.1⟩,x,y,he,hf,hy,hv⟩
  choose f x y he hf hy hv using hopt
  refine ⟨f,x,y,fun L => ⟨hf L,hy L,hv L⟩,?_,?_⟩
  · intro L
    simpa only [he L] using hfit L
  · intro L hL W hW R
    dsimp only
    let s := bitSize (encodeInput kind I)
    let S := LayeredLpSize.sizeBound.eval s
    let M := 2^s
    have hsize : bitSize (Lax109476.RationalEncoding.encodeProgram (program I L)) ≤ S :=
      LayeredLpSize.polynomial_size kind I L hL
    have hlength : (Lax109476.RationalEncoding.encodeProgram (program I L)).length ≤ S :=
      (WordSize.length_le _).trans hsize
    have hword : LayeredLpSize.wordLength n L ≤ S := by
      rwa [LayeredLpSize.program_length] at hlength
    have htime := RamFlowSolverBounds.eval_mono TB hsize
    obtain ⟨hbuild,hinvoke⟩ := RamLayeredHostWidth.sufficient p WB TB kind I L hn hL W hW
    have hnum : ∀ u v,(I.capacity u v).num ≤ M := fun u v => by
      simpa only [NNRat.natAbs_num_coe] using (LpInputSize.capacity_height kind I u v).1
    have hden : ∀ u v,(I.capacity u v).den ≤ M := fun u v => by
      simpa only [NNRat.den_coe] using (LpInputSize.capacity_height kind I u v).2
    rintro σ ⟨hctx,hdata⟩
    obtain ⟨τ,rr,pr⟩ := hexec L (2^W) M hbuild hinvoke hnum hden σ
      ⟨hdata,hword.trans_lt hctx.lpRoom,hlength.trans_lt hctx.inputRoom,
        htime.trans_lt hctx.addressRoom,htime.trans_lt hctx.valueRoom,htime.trans_lt hctx.outputRoom⟩
    exact ⟨τ,rr.mono (RamLayeredSolverBounds.cost_bound p coefficients TB kind I L hL),
      RamShortTrial.solver_frame rr hctx,by simpa only [he L] using pr.1⟩

end Lax455465Proofs.RamShortLpCalls
