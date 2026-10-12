import Lax455465Proofs.RamShortLpCalls
import Lax455465Proofs.RamShortSelection
import Lax455465Proofs.ShortInputBounds

namespace Lax455465Proofs.RamShortScan
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open LayeredFlowLP LayeredFlowDual LayeredFlowFeasibility RamShortContext
open Lax455465.RationalEncoding Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open scoped NNRat

/-- Search the layer budgets, then solve the selected budget once more to
leave its entire primal certificate available for path extraction. -/
def command (p : Lax808846.Ram.Program) (coefficients : List ℕ) : Com :=
  .seq (RamShortSelection.command (RamShortTrial.command p coefficients))
    (.seq RamLayeredData.dimensions (RamLayeredLpSolver.command p coefficients))

noncomputable def wordBound (p : Lax808846.Ram.Program) (WB TB : Polynomial ℕ) : Polynomial ℕ :=
  RamLayeredHostWidth.wordBound p WB TB+
    Polynomial.C 2*((Polynomial.X+Polynomial.C 1)^2+WB.comp LayeredLpSize.sizeBound)+
    Polynomial.C 16*(Polynomial.X+Polynomial.C 1)^2+Polynomial.C 4

noncomputable def timeBound (p : Lax808846.Ram.Program) (coefficients : List ℕ) (TB : Polynomial ℕ) : Polynomial ℕ :=
  let T := RamLayeredSolverBounds.timeBound p coefficients TB
  (T+Polynomial.C 120)*(Polynomial.X+Polynomial.C 1)+T+Polynomial.C 60

/-- A single fixed native command returns the actual optimal certificate
at the first successful layer budget, with polynomial time and word bounds. -/
theorem exists_program :
    ∃ (p : Lax808846.Ram.Program) (WB TB : Polynomial ℕ) (coefficients : List ℕ),
      ∀ {n : ℕ} (kind : Lax455465.ProductNetwork.EdgeKind) (I : RationalInstance n),2 ≤ n →
        ∃ (f : ℕ → ℚ≥0) (x : ∀ L,Arc n L → ℚ) (y : ∀ L,Dual n L),
          (∀ L,Feasible I (f L : ℚ) (x L) ∧
            Lax109476.LinearProgram.DualFeasible (program I L) (y L) ∧
            (f L : ℚ)=Lax109476.LinearProgram.dualValue (program I L) (y L)) ∧
          (∀ L,FitsInWords (WB.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I L))))
            (Lax109476.RationalEncoding.encodeCertificate (.optimal (vector (f L : ℚ) (x L)) (y L)))) ∧
          ∀ W : ℕ,(wordBound p WB TB).eval (bitSize (encodeInput kind I)) ≤ W →
            let S := LayeredLpSize.sizeBound.eval (bitSize (encodeInput kind I))
            let R := ShortRationalParameters.maximum I
            let L := ShortLayerSelection.select n (R : ℚ) (fun k => (f k : ℚ))
            Spec (2^W) (Context I R S (TB.eval S)) (command p coefficients)
              (fun _ τ => Context I R S (TB.eval S) τ ∧ RamLayeredData.Data I L τ ∧
                Prefix (Lax109476.RationalEncoding.encodeCertificate (.optimal (vector (f L : ℚ) (x L)) (y L)))
                  "vm.output" τ)
              ((timeBound p coefficients TB).eval (bitSize (encodeInput kind I))) := by
  classical
  obtain ⟨p,WB,TB,coefficients,hcalls⟩ := RamShortLpCalls.exists_program
  refine ⟨p,WB,TB,coefficients,?_⟩
  intro n kind I hn
  obtain ⟨f,x,y,hmath,hfit,hcall⟩ := hcalls kind I hn
  refine ⟨f,x,y,hmath,hfit,?_⟩
  intro W hW
  dsimp only
  let b := bitSize (encodeInput kind I)
  let S := LayeredLpSize.sizeBound.eval b
  let T := (RamLayeredSolverBounds.timeBound p coefficients TB).eval b
  let R := ShortRationalParameters.maximum I
  let L := ShortLayerSelection.select n (R : ℚ) (fun k => (f k : ℚ))
  let w := (b+1)^2+WB.eval S
  let M := 2^w
  have hwidth : (RamLayeredHostWidth.wordBound p WB TB).eval b+2*w+16*(b+1)^2+4 ≤ W := by
    simpa only [wordBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_comp] using hW
  have hhost : (RamLayeredHostWidth.wordBound p WB TB).eval b ≤ W := by omega
  have hnbit : n≤b := LpInputSize.input_dimension kind I
  have hwW : w<W := by omega
  have hMB : M<2^W := Nat.pow_lt_pow_right (by decide) hwW
  have hshape (k : ℕ) (hk : k≤n) : RamLayeredData.shapeSize n k<2^W :=
    (RamLayeredHostWidth.sufficient p WB TB kind I k hn hk W hhost).1.2.2.1
  have hsmall : n<2^W ∧ 1<2^W := by
    have hh := hshape 0 (by omega)
    dsimp only [RamLayeredData.shapeSize] at hh
    omega
  have hfits (k : ℕ) (hk : k≤n) : ∀ a∈Lax109476.RationalEncoding.encodeCertificate
      (.optimal (vector (f k : ℚ) (x k)) (y k)),a<M := by
    intro a ha
    have he := RamFlowSolverBounds.eval_mono WB (LayeredLpSize.polynomial_size kind I k hk)
    have hw : WB.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I k)))≤w := by
      exact he.trans (Nat.le_add_left _ _)
    exact (hfit k a ha).trans_le (Nat.pow_le_pow_right (by decide) hw)
  have hfheight (k : ℕ) (hk : k≤n) : (f k).num≤M ∧ (f k).den≤M := by
    obtain ⟨tail,he⟩ := LayeredOptimalCertificate.encoding_head (f k : ℚ) (x k) (y k)
    have hnum := hfits k hk (f k).num (by
      rw [he]
      simp [Lax109476.RationalEncoding.encodeRational,NNRat.natAbs_num_coe])
    have hden := hfits k hk (f k).den (by
      rw [he]
      simp [Lax109476.RationalEncoding.encodeRational,NNRat.den_coe])
    exact ⟨hnum.le,hden.le⟩
  have hRheight : R.num≤M ∧ R.den≤M := by
    have hh := ShortInputBounds.maximum_height kind I
    have he : 2^((b+1)^2)≤M := Nat.pow_le_pow_right (by decide) (by dsimp [w]; omega)
    exact ⟨hh.1.trans he,hh.2.trans he⟩
  have htrial : ∀ i,i<n-1→Spec (2^W) (fun σ => Context I R S (TB.eval S) σ ∧ σ.vars "find.i"=i)
      (RamShortTrial.command p coefficients)
      (fun _ τ => Context I R S (TB.eval S) τ ∧ τ.vars "find.ok"=
        if ShortLayerScan.predicate n (R : ℚ) (fun k => (f k : ℚ)) i then 1 else 0) (T+100) := by
    intro i hi
    have hil : i+1≤n := by omega
    have hp := RamShortTrial.command_spec (2^W) M T n S (TB.eval S) i I R (f (i+1)) (x (i+1)) (y (i+1))
      p coefficients (hshape _ hil)
      (ShortInputBounds.test_space b n (i+1) w W hnbit (by omega) (by omega))
      hRheight.1 hRheight.2 (hfheight _ hil).1 (hfheight _ hil).2
      (fun a ha => (hfits _ hil a ha).trans hMB)
      (by
        intro σ hσ
        obtain ⟨τ,rr,pr⟩ := hcall (i+1) hil W hhost R σ hσ
        exact ⟨τ,rr,pr.2⟩)
    simpa only [ShortLayerScan.predicate,ShortLayerSelection.good,decide_eq_true_eq,
      Nat.cast_add,Nat.cast_one] using hp
  have hselect := RamShortSelection.command_spec (2^W) (T+100) n hn hsmall.1 (R : ℚ)
    (fun k => (f k : ℚ)) (Context I R S (TB.eval S)) (RamShortTrial.command p coefficients)
    (fun _ h => h.source.order)
    (by
      intro σ k name h hm
      apply RamShortContext.set_var h name k
      simp only [RamShortSelection.names,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl <;> decide)
    htrial (RamShortTrial.scan_frame p coefficients)
  rintro σ hσ
  obtain ⟨σ1,r1,p1⟩ := hselect σ hσ
  have hLrange := ShortLayerSelection.select_range n hn (R : ℚ) (fun k => (f k : ℚ))
  have hLn : L≤n := by dsimp only [L]; omega
  obtain ⟨σ2,r2,p2⟩ := RamLayeredSource.from_source (2^W) I L (hshape _ hLn) σ1 ⟨p1.1.source,p1.2⟩
  have hc2 := RamShortContext.frame r2 p1.1 (by decide) (by decide)
  obtain ⟨τ,r3,p3⟩ := hcall L hLn W hhost R σ2 ⟨hc2,p2⟩
  refine ⟨τ,(r1.seq (r2.seq r3)).mono ?_,p3.1,RamLayeredScope.solver_data r3 I p2,p3.2⟩
  have hmain : (T+120)*(n-1)≤(T+120)*(b+1) := Nat.mul_le_mul_left _ (by omega)
  simp only [timeBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  change (T+100+20)*(n-1)+18+(30+T)≤(T+120)*(b+1)+T+60
  rw [show T+100+20=T+120 by omega]
  omega

end Lax455465Proofs.RamShortScan
