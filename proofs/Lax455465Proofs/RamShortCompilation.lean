import Lax455465Proofs.RamShortValidInput
import Lax455465Proofs.RamValidCompilation

set_option maxRecDepth 16384
namespace Lax455465Proofs.RamShortCompilation
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile RamVirtualState
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax455465.ConcurrentFlow Lax455465.ShortPathFlow
open Lax759944.BinaryWordEncoding
open scoped NNReal

noncomputable def extent {n : ℕ} (TB : Polynomial ℕ) (I : RationalInstance n) : ℕ :=
  let S:=LayeredLpSize.sizeBound.eval (bitSize (encodeInput .undirected I))
  (encodeInput .undirected I).length+2*n+2*(n*n)+4*S+TB.eval S+RamShortExtractionBounds.space S+10

theorem initial_input {n : ℕ} (TB : Polynomial ℕ) (I : RationalInstance n) :
    RamShortValidInput.Input I TB
      (initEnv (fun _ => extent TB I) ((encodeInput .undirected I).length::encodeInput .undirected I)) := by
  constructor
  all_goals simp only [initEnv,List.length_replicate] <;> dsimp only [extent] <;> omega

/-- Compile the full valid-input short-path algorithm from standard zero
memory. Array extents provide address-space bookkeeping, with no preloaded advice. -/
theorem exists_program : ∃ (p : Lax808846.Ram.Program) (WB TB : Polynomial ℕ),
    ∀ {n : ℕ} (I : RationalInstance n),I.network.IsUndirected → (∀ v,I.weight v=1) → 2≤n →
      0<sparsestCut I.network (uniformWeight n) → ∃ cert : FlowCertificate n,
        IsConcurrentFlow .undirected I.network (uniformWeight n) (cert.value : ℝ≥0) cert.flow ∧
        (sparsestCut I.network (uniformWeight n) : ℝ)≤32768*logFactor n*(cert.value : ℝ) ∧
        HasPathLengthAtMost cert.flow (8192*(maxIncidentCapacity I.network : ℝ)*logFactor n /
          ((n : ℝ)*(sparsestCut I.network (uniformWeight n) : ℝ))) ∧
        ∀ W : ℕ,WB.eval (bitSize (encodeInput .undirected I))≤W → ∃ t≤TB.eval (bitSize (encodeInput .undirected I)),
          Lax808846.Ram.RunsTo W p ((encodeInput .undirected I).length::encodeInput .undirected I) (encodeFlow cert) t := by
  obtain ⟨c,T,WB,sourceTime,hcorrect⟩:=RamShortValidInput.exists_program
  let layout:=RamAutomaticLayout.layout c
  refine ⟨compileProgram layout c,WB+Polynomial.X+Polynomial.C (2+RamTransfer.layoutAllowance layout),
    Polynomial.C layout.const*T+1,?_⟩
  intro n I hsym hw hn hS
  let b:=bitSize (encodeInput .undirected I)
  let v:=WB.eval b+b+2
  let σ:=initEnv (fun _ => extent sourceTime I) ((encodeInput .undirected I).length::encodeInput .undirected I)
  obtain ⟨τ,rr,cert,hout,hflow,hvalue,hlength⟩:=hcorrect I hsym hw hn hS v (by dsimp only [v,b]; omega) σ
    (initial_input sourceTime I)
  refine ⟨cert,hflow,hvalue,hlength,?_⟩
  intro W hW
  have hv : 0<v := by dsimp only [v]; omega
  have hfit : v+RamTransfer.layoutAllowance layout≤W := by
    simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,v,b,Nat.add_assoc] using hW
  obtain ⟨k,hk,hbs⟩:=rr
  obtain ⟨t,ht,hr⟩:=Lax808846Proofs.Simulation.compileProgram_runsTo
    (RamTransfer.layout_fits hv hfit) (RamAutomaticLayout.layout_ok c)
    (RamValidCompilation.input_fits (encodeInput .undirected I) v (by dsimp only [v,b]; omega)) hbs
  refine ⟨t,?_,by simpa only [hout] using hr⟩
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_one] using
    ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_left layout.const hk) 1)

end Lax455465Proofs.RamShortCompilation
