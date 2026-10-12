import Lax455465Proofs.RamIncidentSum
import Lax455465Proofs.RamUnsignedMaximum
import Lax455465Proofs.RamUnsignedScalar
import Lax455465Proofs.ShortRationalParameters

namespace Lax455465Proofs.RamIncidentMaximum
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamLayeredSource
open Lax455465.RationalEncoding RamUnsignedMaximum
open scoped NNRat BigOperators

def sums {n : ℕ} (I : RationalInstance n) : List ℚ≥0 :=
  List.ofFn fun v => (RamIncidentSum.row I v).sum

theorem maximum_le (qs : List ℚ≥0) (a : ℚ≥0) (h : ∀ q∈qs,q ≤ a) : maximum qs ≤ a := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    rw [maximum_cons,max_le_iff]
    exact ⟨h q (by simp),ih (fun x hx => h x (by simp [hx]))⟩

theorem le_maximum (qs : List ℚ≥0) (q : ℚ≥0) (h : q∈qs) : q ≤ maximum qs := by
  induction qs with
  | nil => simp at h
  | cons a qs ih =>
    rcases List.mem_cons.mp h with rfl | hmem
    · exact le_max_left _ _
    · exact (ih hmem).trans (le_max_right _ _)

theorem maximum_sums {n : ℕ} (I : RationalInstance n) :
    maximum (sums I)=ShortRationalParameters.maximum I := by
  simp only [sums,RamIncidentSum.row,List.sum_ofFn,ShortRationalParameters.maximum]
  apply le_antisymm
  · apply maximum_le
    intro q hq
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    exact Finset.le_sup (s := Finset.univ) (f := fun v : Fin n => ∑ u,I.capacity v u) (Finset.mem_univ v)
  · apply Finset.sup_le
    intro v _
    exact le_maximum _ _ (List.mem_ofFn.mpr ⟨v,rfl⟩)

def scan : Com := RamUnsignedMaximum.command "short.row" "lp.n" RamIncidentSum.command

def command : Com := .seq scan (RamUnsignedScalar.save "short.maximum")

/-- Compute the maximum incident capacity from the original capacity
matrix, including exact row sums and a deterministic maximum scan. -/
theorem command_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n)
    (hM : 1 ≤ M) (hB : 2*M^2+3 < B) (hindex : 2*(n*n)+3 < B)
    (hnum : ∀ v w,(I.capacity v w).num ≤ M) (hden : ∀ v w,(I.capacity v w).den ≤ M)
    (hprefixNum : ∀ v i,((RamIncidentSum.row I v).take i).sum.num ≤ M)
    (hprefixDen : ∀ v i,((RamIncidentSum.row I v).take i).sum.den ≤ M) :
    Spec B (Source I) command
      (fun _ τ => Source I τ ∧ RamUnsignedScalar.Stored "short.maximum" (ShortRationalParameters.maximum I) τ)
      ((((36*(M^2).size+140)*n+16)+74)*n+20) := by
  have hMB : M<B := by nlinarith only [hB]
  have hn : n<B := by nlinarith only [hindex]
  have hsums (q : ℚ≥0) (hq : q∈sums I) : q.num ≤ M ∧ q.den ≤ M := by
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    have hN := hprefixNum v n
    have hD := hprefixDen v n
    have he : (RamIncidentSum.row I v).length=n := by simp [RamIncidentSum.row]
    simpa only [List.take_of_length_le he.le] using And.intro hN hD
  have hprefix (i : ℕ) : (maximum ((sums I).take i)).num ≤ M ∧ (maximum ((sums I).take i)).den ≤ M :=
    maximum_height M _ hM (fun q hq => (hsums q (List.mem_of_mem_take hq)).1)
      (fun q hq => (hsums q (List.mem_of_mem_take hq)).2)
  have hbody : ∀ i,∀ hi : i<(sums I).length,
      Spec B (fun σ => Source I σ ∧ σ.vars "short.row"=i) RamIncidentSum.command
        (fun _ τ => Source I τ ∧ FractionOutput ((sums I)[i] : ℚ) τ)
        ((36*(M^2).size+140)*n+16) := by
    intro i hi σ hσ
    have hin : i<n := by simpa [sums] using hi
    obtain ⟨τ,rr,pr⟩ := RamIncidentSum.command_spec B M I ⟨i,hin⟩ hB hindex
      (hnum _) (hden _) (hprefixNum _) (hprefixDen _) σ hσ
    exact ⟨τ,rr,pr.1.1,by simpa only [sums,List.getElem_ofFn] using pr.2⟩
  have hscan := RamUnsignedMaximum.command_spec B M ((36*(M^2).size+140)*n+16)
    (Source I) "short.row" "lp.n" (sums I) RamIncidentSum.command hB (by simpa [sums] using hn)
    (fun q hq => (hsums q hq).1) (fun q hq => (hsums q hq).2)
    (fun i => (hprefix i).1) (fun i => (hprefix i).2)
    (fun σ h => by simpa [sums] using h.order)
    (by
      intro σ k name h hh
      rcases hh with rfl | rfl | rfl
      all_goals refine ⟨?_,?_,?_⟩
      all_goals first
        | simpa only [vars_setVar,String.reduceEq,if_false] using h.order
        | simpa only [vars_setVar,String.reduceEq,if_false] using h.square
        | simpa only [Prefix,arrs_setVar] using h.capacities)
    hbody (by decide) (by decide) (by decide)
    (fun rr h => RamLayeredSource.frame rr h (by decide) (by decide) (by decide))
    (fun rr h => RamLayeredSource.frame rr h (by decide) (by decide) (by decide))
  have hmax := maximum_height M (sums I) hM (fun q hq => (hsums q hq).1) (fun q hq => (hsums q hq).2)
  intro σ hσ
  obtain ⟨ν,rr,pr⟩ := hscan σ hσ
  obtain ⟨τ,rs,ps⟩ := RamUnsignedScalar.save_spec B "short.maximum" (maximum (sums I))
    (hmax.1.trans_lt hMB) (hmax.2.trans_lt hMB) (by decide) ν pr.2
  refine ⟨τ,(rr.seq rs).mono ?_,RamLayeredSource.frame rs pr.1 (by decide) (by decide) (by decide),?_⟩
  · simp only [sums,List.length_ofFn]
    omega
  · simpa only [maximum_sums] using ps

end Lax455465Proofs.RamIncidentMaximum
