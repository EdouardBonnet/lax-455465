import Lax455465Proofs.RamLayeredSource
import Lax455465Proofs.RamUnsignedScalar

namespace Lax455465Proofs.RamShortContext
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamLayeredSource RamUnsignedScalar
open Lax455465.RationalEncoding
open scoped NNRat

/-- Only source graph data, the computed maximum, and buffer extents are
shared between calls. Layer-specific LP dimensions may be overwritten. -/
structure Context {n : ℕ} (I : RationalInstance n) (R : ℚ≥0) (words time : ℕ) (σ : Env) : Prop where
  source : Source I σ
  maximum : Stored "short.maximum" R σ
  lpRoom : words < (σ.arrs "lp.word").length
  inputRoom : words < (σ.arrs "vm.input").length
  addressRoom : time < (σ.arrs "vm.addresses").length
  valueRoom : time < (σ.arrs "vm.values").length
  outputRoom : time < (σ.arrs "vm.output").length

def names : List String := ["lp.n","lp.n2","short.maximum.n","short.maximum.d"]

theorem frame {B K : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ K)
    {n words time : ℕ} {I : RationalInstance n} {R : ℚ≥0} (h : Context I R words time σ)
    (hx : ∀ x∈names,x∉c.wvars) (ha : "flow.capacities"∉c.warrs) : Context I R words time τ := by
  refine ⟨RamLayeredSource.frame hr h.source (hx _ (by simp [names])) (hx _ (by simp [names])) ha,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Stored,String.reduceAppend,hr.frame_var "short.maximum.n" (hx _ (by simp [names])),
      hr.frame_var "short.maximum.d" (hx _ (by simp [names]))] using h.maximum
  · simpa only [RamFrames.run_array_length hr "lp.word"] using h.lpRoom
  · simpa only [RamFrames.run_array_length hr "vm.input"] using h.inputRoom
  · simpa only [RamFrames.run_array_length hr "vm.addresses"] using h.addressRoom
  · simpa only [RamFrames.run_array_length hr "vm.values"] using h.valueRoom
  · simpa only [RamFrames.run_array_length hr "vm.output"] using h.outputRoom

theorem set_var {n words time : ℕ} {I : RationalInstance n} {R : ℚ≥0} {σ : Env}
    (h : Context I R words time σ) (x : String) (k : ℕ) (hx : x∉names) :
    Context I R words time (σ.setVar x k) := by
  have hn : "lp.n" ≠ x := by intro he; exact hx (he ▸ (by simp [names]))
  have hn2 : "lp.n2" ≠ x := by intro he; exact hx (he ▸ (by simp [names]))
  have hRn : "short.maximum.n" ≠ x := by intro he; exact hx (he ▸ (by simp [names]))
  have hRd : "short.maximum.d" ≠ x := by intro he; exact hx (he ▸ (by simp [names]))
  refine ⟨⟨?_,?_,?_⟩,?_,h.lpRoom,h.inputRoom,h.addressRoom,h.valueRoom,h.outputRoom⟩
  · simpa only [vars_setVar,if_neg hn] using h.source.order
  · simpa only [vars_setVar,if_neg hn2] using h.source.square
  · exact h.source.capacities
  · simpa only [Stored,vars_setVar,String.reduceAppend,if_neg hRn,if_neg hRd] using h.maximum

end Lax455465Proofs.RamShortContext
