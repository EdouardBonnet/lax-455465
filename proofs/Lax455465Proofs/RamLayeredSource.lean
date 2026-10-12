import Lax455465Proofs.RamLayeredData

namespace Lax455465Proofs.RamLayeredSource
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamLayeredData
open Lax455465.RationalEncoding

/-- Graph data shared by every iteration of the layer-budget scan. -/
structure Source {n : ℕ} (I : RationalInstance n) (σ : Env) : Prop where
  order : σ.vars "lp.n"=n
  square : σ.vars "lp.n2"=n*n
  capacities : Prefix (RamUnsignedBuffer.encode (RamFlowData.capacities I)) "flow.capacities" σ

theorem of_data {n L : ℕ} {I : RationalInstance n} {σ : Env} (h : Data I L σ) : Source I σ :=
  ⟨h.order,h.square,h.capacities⟩

theorem frame {B K : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ K)
    {n : ℕ} {I : RationalInstance n} (h : Source I σ)
    (hn : "lp.n"∉c.wvars) (hn2 : "lp.n2"∉c.wvars) (ha : "flow.capacities"∉c.warrs) : Source I τ :=
  ⟨(hr.frame_var _ hn).trans h.order,(hr.frame_var _ hn2).trans h.square,
    by simpa only [Prefix,hr.frame_arr _ ha] using h.capacities⟩

theorem from_source (B : ℕ) {n : ℕ} (I : RationalInstance n) (L : ℕ)
    (hB : shapeSize n L < B) :
    Spec B (fun σ => Source I σ ∧ σ.vars "short.layer"=L) dimensions
      (fun _ τ => Data I L τ) 30 := by
  rintro σ ⟨hsource,hL⟩
  obtain ⟨τ,hr,hp⟩ := dimensions_spec B n L hB σ ⟨hsource.order,hsource.square,hL⟩
  have hsτ := frame hr hsource (by decide) (by decide) (by decide)
  exact ⟨τ,hr,hsτ.order,hsτ.square,(hr.frame_var "short.layer" (by decide)).trans hL,
    hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2.1,hp.2.2.2.2.2,hsτ.capacities⟩

end Lax455465Proofs.RamLayeredSource
