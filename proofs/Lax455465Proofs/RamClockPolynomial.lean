import Lax455465Proofs.RamClockTotal
import Lax455465Proofs.RamTransfer
import Lax455465Proofs.RamHostBounds

namespace Lax455465Proofs.RamClockPolynomial
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Polynomial

/-- A fixed-width, bounded-time simulation, defined for every input word. -/
def solve (p : Lax808846.Ram.Program) (WB TB : Polynomial ℕ) (xs : List ℕ) : List ℕ :=
  (SparseClock.run (WB.eval (bitSize xs)) p (TB.eval (bitSize xs))
    (SparseRam.init (xs.length::xs))).out

noncomputable def wordBound (p : Lax808846.Ram.Program) (WB TB : Polynomial ℕ) : Polynomial ℕ :=
  2*WB+TB+C (RamVirtualConstants.allowance p)+2*X+WB.comp (X+1)+TB.comp (X+1)+16

noncomputable def timeBound (p : Lax808846.Ram.Program) (TB : Polynomial ℕ) (wc tc : List ℕ) : Polynomial ℕ :=
  (12*X+63)*X+C (6*wc.length+6*tc.length+74)+(C (4*p.length)+32*TB+123)*TB

@[simp] theorem wordBound_eval (p : Lax808846.Ram.Program) (WB TB : Polynomial ℕ) (L : ℕ) :
    (wordBound p WB TB).eval L =
      2*WB.eval L+TB.eval L+RamVirtualConstants.allowance p+2*L+WB.eval (L+1)+TB.eval (L+1)+16 := by
  simp [wordBound]

@[simp] theorem timeBound_eval (p : Lax808846.Ram.Program) (TB : Polynomial ℕ) (wc tc : List ℕ) (L : ℕ) :
    (timeBound p TB wc tc).eval L =
      (12*L+63)*L+(6*wc.length+6*tc.length+74)+(4*p.length+32*TB.eval L+123)*TB.eval L := by
  simp [timeBound]

/-- The interpreter is uniformly polynomial time even if the interpreted
program fails to halt. Its virtual word width and clock are polynomials
computed from the actual binary input size. -/
theorem polynomial_time (p : Lax808846.Ram.Program) (WB TB : Polynomial ℕ) :
    RamPolytime (solve p WB TB) := by
  obtain ⟨wc,hwc⟩ := RamPolynomial.exists_coefficients WB
  obtain ⟨tc,htc⟩ := RamPolynomial.exists_coefficients TB
  let c := RamClockTotal.command p wc tc
  let W := wordBound p WB TB
  let T := timeBound p TB wc tc
  have hbounds (xs : List ℕ) := RamHostBounds.sufficient_bounds
    (WB.eval (bitSize xs)) (TB.eval (bitSize xs)) (RamVirtualConstants.allowance p)
    (2*bitSize xs+WB.eval (bitSize xs+1)+TB.eval (bitSize xs+1)+8)
    (W.eval (bitSize xs)) (by dsimp [W]; rw [wordBound_eval]; unfold RamHostBounds.sufficient; omega)
  have hwidth (xs : List ℕ) : WB.eval (bitSize xs) ≤ W.eval (bitSize xs) := by
    dsimp [W]; rw [wordBound_eval]; omega
  have hsize (xs : List ℕ) : bitSize xs ≤ W.eval (bitSize xs) := by
    dsimp [W]; rw [wordBound_eval]; omega
  have hinput (xs : List ℕ) : ∀ a∈xs.length::xs,a < 2^(W.eval (bitSize xs)) := by
    intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · have := (hbounds xs).2.2.2
      have := WordSize.length_le xs
      omega
    · exact (WordSize.member_bound xs a ha).trans_le (Nat.pow_le_pow_right (by decide) (hsize xs))
  apply RamTransfer.ramPolytime_of_solves (RamAutomaticLayout.layout c) c (solve p WB TB) W T
  · intro xs
    dsimp [W]; rw [wordBound_eval]; omega
  · intro xs a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hinput xs a ha
    · have hw := SparseClock.run_output_words (WB.eval (bitSize xs)) p (TB.eval (bitSize xs))
        (SparseRam.init (xs.length::xs)) (by intro a ha; cases ha)
      exact (hw a ha).trans_le (Nat.pow_le_pow_right (by decide) (hwidth xs))
  · refine ⟨RamAutomaticLayout.layout_ok c,?_,?_⟩
    · rintro tape ⟨xs,rfl⟩
      exact hinput xs
    · rintro tape ⟨xs,rfl⟩
      let ext : String → ℕ := fun _ => xs.length+TB.eval (bitSize xs)+1
      let σ := initEnv ext (xs.length::xs)
      have hh := hbounds xs
      have hlen := WordSize.length_le xs
      obtain ⟨τ,rr,hout⟩ := RamClockTotal.command_spec (2^(W.eval (bitSize xs))) p wc tc xs
        (by simpa only [hwc] using hh.1) (by simpa only [htc] using hh.2.1) hh.2.2.1
        (by omega) (by omega) (fun a ha => hinput xs a (List.mem_cons_of_mem xs.length ha))
        (by rw [hwc]; omega) (by rw [htc]; omega) σ (by
          refine ⟨rfl,?_,rfl⟩
          simp only [RamClockTotal.Room,RamClockedLoop.Room,σ,initEnv,ext,List.length_replicate,htc]
          omega)
      refine ⟨ext,τ,rr.mono ?_,?_⟩
      · simp only [List.tail_cons]
        dsimp [RamClockTotal.cost,T]
        rw [timeBound_eval,htc]
        nlinarith
      · simpa only [List.tail_cons,solve,hwc,htc] using hout

end Lax455465Proofs.RamClockPolynomial
