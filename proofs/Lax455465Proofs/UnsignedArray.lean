import Lax455465Proofs.RamUnsignedBuffer

namespace Lax455465Proofs.UnsignedArray
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open scoped NNRat

/-- A typed view of each initialized numerator-denominator pair. -/
def Initialized {N : ℕ} (q : Fin N → ℚ≥0) (array : String) (σ : Env) : Prop :=
  ∀ i : Fin N,(σ.arrs array)[2*i.val]?=some (q i).num ∧
    (σ.arrs array)[2*i.val+1]?=some (q i).den

theorem of_prefix {N : ℕ} (q : Fin N → ℚ≥0) (array : String) (σ : Env)
    (h : Prefix (RamUnsignedBuffer.encode (List.ofFn q)) array σ) : Initialized q array σ := by
  intro i
  have hn := RamUnsignedBuffer.numerator_at (List.ofFn q) i.val (by simpa using i.isLt)
  have hd := RamUnsignedBuffer.denominator_at (List.ofFn q) i.val (by simpa using i.isLt)
  have hni : 2*i.val<(RamUnsignedBuffer.encode (List.ofFn q)).length := by simp <;> omega
  have hdi : 2*i.val+1<(RamUnsignedBuffer.encode (List.ofFn q)).length := by simp <;> omega
  refine ⟨?_,?_⟩
  · have he := (h _ hni).trans ((List.getElem?_eq_getElem hni).symm.trans hn)
    simpa only [List.getElem_ofFn,Fin.eta] using he
  · have he := (h _ hdi).trans ((List.getElem?_eq_getElem hdi).symm.trans hd)
    simpa only [List.getElem_ofFn,Fin.eta] using he

theorem to_prefix {N : ℕ} (q : Fin N → ℚ≥0) (array : String) (σ : Env)
    (h : Initialized q array σ) : Prefix (RamUnsignedBuffer.encode (List.ofFn q)) array σ := by
  intro k hk
  have hkN : k<2*N := by simpa only [RamUnsignedBuffer.length_encode,List.length_ofFn] using hk
  let i : Fin N := ⟨k/2,by omega⟩
  have hcases : k=2*i.val ∨ k=2*i.val+1 := by dsimp only [i]; omega
  rcases hcases with he | he
  · have hki : 2*i.val<(RamUnsignedBuffer.encode (List.ofFn q)).length := by simp only [RamUnsignedBuffer.length_encode,List.length_ofFn]; omega
    have hencoded := RamUnsignedBuffer.numerator_at (List.ofFn q) i.val (by simpa using i.isLt)
    have hv : (RamUnsignedBuffer.encode (List.ofFn q))[2*i.val]=(q i).num := by
      simpa only [List.getElem?_eq_getElem hki,List.getElem_ofFn,Fin.eta,Option.some.injEq] using hencoded
    simpa only [he] using (h i).1.trans (congrArg some hv.symm)
  · have hki : 2*i.val+1<(RamUnsignedBuffer.encode (List.ofFn q)).length := by simp only [RamUnsignedBuffer.length_encode,List.length_ofFn]; omega
    have hencoded := RamUnsignedBuffer.denominator_at (List.ofFn q) i.val (by simpa using i.isLt)
    have hv : (RamUnsignedBuffer.encode (List.ofFn q))[2*i.val+1]=(q i).den := by
      simpa only [List.getElem?_eq_getElem hki,List.getElem_ofFn,Fin.eta,Option.some.injEq] using hencoded
    simpa only [he] using (h i).2.trans (congrArg some hv.symm)

theorem prefix_iff {N : ℕ} (q : Fin N → ℚ≥0) (array : String) (σ : Env) :
    Prefix (RamUnsignedBuffer.encode (List.ofFn q)) array σ ↔ Initialized q array σ :=
  ⟨of_prefix q array σ,to_prefix q array σ⟩

end Lax455465Proofs.UnsignedArray
