import Lax455465Proofs.ResidualData
import Lax455465Proofs.RamProductVector

namespace Lax455465Proofs.RamResidual

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational MetricMatrix
open Lax455465.RationalEncoding
open scoped NNRat

def Context {n : ℕ} (I : RationalInstance n) (active : Finset (Fin n)) (σ : Env) : Prop :=
  σ.vars "metric.n" = n ∧ σ.vars "metric.n2" = n*n ∧
    Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ ∧
    Prefix (RamUnsignedBuffer.encode (values I.capacity)) "flow.capacities" σ ∧
    Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask active))) "region.active" σ

def command : Com := .seq (RamArcMask.command none "region.active" "region.arcActive")
  (.seq (.assign "product.count" (.var "metric.n2"))
    (.seq (RamProductVector.command "flow.capacities" "region.arcActive" "region.capacities")
      (.seq (.assign "product.count" (.var "metric.n"))
        (RamProductVector.command "flow.weights" "region.active" "region.weights"))))

set_option maxHeartbeats 1600000 in
/-- Recompute both residual arrays from the original graph. Active arcs
require both endpoints; zero-weight transit vertices retain their flags. -/
theorem command_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n) (active : Finset (Fin n))
    (hM1 : 1 ≤ M) (hB : 2*M^2+3 < B) (hindex : 2*(n*n)+2 < B) (hvertex : 2*n+2 < B)
    (hwn : ∀ v, (I.weight v).num ≤ M) (hwd : ∀ v, (I.weight v).den ≤ M)
    (hcn : ∀ u v, (I.capacity u v).num ≤ M) (hcd : ∀ u v, (I.capacity u v).den ≤ M) :
    Spec B (fun σ => Context I active σ ∧
      2*(n*n) < (σ.arrs "region.arcActive").length ∧
      2*(n*n) < (σ.arrs "region.capacities").length ∧
      2*n < (σ.arrs "region.weights").length) command
      (fun _ τ => Context I active τ ∧
        Prefix (RamUnsignedBuffer.encode (values (ResidualData.capacity I active))) "region.capacities" τ ∧
        Prefix (RamUnsignedBuffer.encode (List.ofFn (ResidualData.weights I active))) "region.weights" τ)
      ((36*(M^2).size+208)*(n*n)+(36*(M^2).size+126)*n+28) := by
  have h2 : 2 < B := by nlinarith
  let ws := List.ofFn I.weight
  let cs := values I.capacity
  let vs := MaskedMassData.flags (ResidualData.mask active)
  let es := values (RamArcMask.matrix none (ResidualData.mask active))
  have hwLen : ws.length = n := List.length_ofFn
  have hcLen : cs.length = n*n := length_values _
  have hvLen : vs.length = n := List.length_ofFn
  have heLen : es.length = n*n := length_values _
  have hwN : ∀ q ∈ ws, q.num ≤ M := by
    intro q hq; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq; exact hwn v
  have hwD : ∀ q ∈ ws, q.den ≤ M := by
    intro q hq; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq; exact hwd v
  have hcN : ∀ q ∈ cs, q.num ≤ M := by
    intro q hq; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq; exact hcn _ _
  have hcD : ∀ q ∈ cs, q.den ≤ M := by
    intro q hq; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq; exact hcd _ _
  have hvN : ∀ q ∈ vs, q.num ≤ M := by
    intro q hq; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    by_cases hv : v ∈ active <;> simp [ResidualData.mask,hv] <;> omega
  have hvD : ∀ q ∈ vs, q.den ≤ M := by
    intro q hq; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    by_cases hv : v ∈ active <;> simp [ResidualData.mask,hv] <;> omega
  have heN : ∀ q ∈ es, q.num ≤ M := by
    intro q hq; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    dsimp only [RamArcMask.matrix]
    cases RamBooleanArithmetic.flag none (ResidualData.mask active _) (ResidualData.mask active _) <;>
      simp [RamBooleanArithmetic.bit] <;> omega
  have heD : ∀ q ∈ es, q.den ≤ M := by
    intro q hq; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    dsimp only [RamArcMask.matrix]
    cases RamBooleanArithmetic.flag none (ResidualData.mask active _) (ResidualData.mask active _) <;>
      simp [RamBooleanArithmetic.bit] <;> omega
  rintro σ ⟨hctx,heRoom,hcRoom,hwRoom⟩
  obtain ⟨ν,re,pe⟩ := RamArcMask.command_spec B none "region.active" "region.arcActive" (ResidualData.mask active)
    (by decide) h2 (by omega) (by omega) hindex hvertex σ ⟨⟨hctx.1,hctx.2.1,hctx.2.2.2.2⟩,heRoom⟩
  let ξ := ν.setVar "product.count" (n*n)
  have rcCount : Run B (.assign "product.count" (.var "metric.n2")) ν ξ 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨pe.1.2.1.symm,pe.1.2.1 ▸ (by omega : n*n < B)⟩)
  have hcCtx : RamProductVector.Context "flow.capacities" "region.arcActive" cs es ξ := by
    refine ⟨by simp [ξ,hcLen],?_,?_⟩
    · simpa only [cs,Prefix,ξ,arrs_setVar,re.frame_arr "flow.capacities" (by decide)] using hctx.2.2.2.1
    · simpa only [es,Prefix,ξ,arrs_setVar] using pe.2
  obtain ⟨μ,rc,pc⟩ := RamProductVector.command_spec B M "flow.capacities" "region.arcActive" "region.capacities" cs es
    (by rw [heLen,hcLen]) (by decide) hB (by rwa [hcLen]) hcN hcD heN heD ξ
    ⟨hcCtx,by simpa only [ξ,arrs_setVar,hcLen,re.frame_arr "region.capacities" (by decide)] using hcRoom⟩
  have hnμ : μ.vars "metric.n" = n :=
    (rc.frame_var _ (by decide)).trans ((rcCount.frame_var _ (by decide)).trans pe.1.1)
  let ρ := μ.setVar "product.count" n
  have rwCount : Run B (.assign "product.count" (.var "metric.n")) μ ρ 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hnμ.symm,hnμ ▸ (by omega : n < B)⟩)
  have rprior := re.seq (rcCount.seq (rc.seq rwCount))
  have hwCtx : RamProductVector.Context "flow.weights" "region.active" ws vs ρ := by
    refine ⟨by simp [ρ,hwLen],?_,?_⟩
    · simpa only [ws,Prefix,rprior.frame_arr "flow.weights" (by decide)] using hctx.2.2.1
    · simpa only [vs,Prefix,rprior.frame_arr "region.active" (by decide)] using hctx.2.2.2.2
  obtain ⟨τ,rw,pw⟩ := RamProductVector.command_spec B M "flow.weights" "region.active" "region.weights" ws vs
    (by rw [hvLen,hwLen]) (by decide) hB (by rwa [hwLen]) hwN hwD hvN hvD ρ
    ⟨hwCtx,by simpa only [hwLen,rprior.frame_arr "region.weights" (by decide)] using hwRoom⟩
  have rr := re.seq (rcCount.seq (rc.seq (rwCount.seq rw)))
  refine ⟨τ,rr.mono ?_,?_,?_,?_⟩
  · simp only [hcLen,hwLen,Nat.add_assoc,Nat.reduceAdd]
    ring_nf; omega
  · simpa only [Context,Prefix,
      rr.frame_var "metric.n" (by decide),rr.frame_var "metric.n2" (by decide),
      rr.frame_arr "flow.weights" (by decide),rr.frame_arr "flow.capacities" (by decide),
      rr.frame_arr "region.active" (by decide)] using hctx
  · have rafter := rwCount.seq rw
    simpa only [cs,es,ResidualData.capacity_products,Prefix,rafter.frame_arr "region.capacities" (by decide)] using pc.2
  · simpa only [ws,vs,ResidualData.weight_products] using pw.2

end Lax455465Proofs.RamResidual
