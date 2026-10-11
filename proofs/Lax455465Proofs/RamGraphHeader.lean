import Lax455465Proofs.RamGraphDimensions
import Lax455465Proofs.FlowInputLists

namespace Lax455465Proofs.RamGraphHeader

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamFlowData
open Lax455465.RationalEncoding Lax455465.ProductNetwork

def tag (kind : EdgeKind) : ℕ := match kind with | .undirected => 0 | .directed => 1

def command : Com := .seq (.assign "flow.kind" (.get "input.data" (.lit 0)))
  (.seq (.assign "lp.n" (.get "input.data" (.lit 1))) RamGraphDimensions.command)

/-- Read the actual edge-model and order from the copied input and compute
all flow-LP dimensions. No dimension is initialized from a typed witness. -/
theorem command_spec (B : ℕ) {n : ℕ} (kind : EdgeKind) (I : RationalInstance n)
    (h2 : 2 < B) (hn : n < B) (hn2 : n*n < B) (hn3 : (n*n)*n < B)
    (hr : rows n < B) (hc : columns n < B) (hm : rows n*columns n < B) :
    Spec B (Prefix (encodeInput kind I) "input.data") command
      (fun _ τ => Prefix (encodeInput kind I) "input.data" τ ∧
        RamGraphDimensions.Dimensions n τ ∧ τ.vars "flow.kind" = tag kind) 30 := by
  intro σ hp
  have hlen : 2 ≤ (encodeInput kind I).length := by
    simp only [encodeInput,List.length_append,List.length_cons,List.length_nil]; omega
  have ht : tag kind < B := by cases kind <;> simp only [tag] <;> omega
  have hget0 : (σ.arrs "input.data")[0]? = some (tag kind) := by
    have := hp 0 (by omega)
    cases kind <;> simpa only [encodeInput,List.cons_append,List.nil_append,List.getElem_cons_zero,tag] using this
  have hget1 : (σ.arrs "input.data")[1]? = some n := by
    have := hp 1 (by omega)
    simpa only [encodeInput,List.cons_append,List.nil_append,List.getElem_cons_succ,List.getElem_cons_zero] using this
  let ν := σ.setVar "flow.kind" (tag kind)
  have hkind : Run B (.assign "flow.kind" (.get "input.data" (.lit 0))) σ ν 3 :=
    Run.assign (evalB_get (evalB_lit (by omega)) hget0 ht)
  let μ := ν.setVar "lp.n" n
  have hget1ν : (ν.arrs "input.data")[1]? = some n := by simpa only [ν,arrs_setVar] using hget1
  have horder : Run B (.assign "lp.n" (.get "input.data" (.lit 1))) ν μ 3 :=
    Run.assign (evalB_get (evalB_lit (by omega)) hget1ν hn)
  obtain ⟨τ,hdims,hpost⟩ := RamGraphDimensions.command_spec B n h2 hn hn2 hn3 hr hc hm μ (by simp [μ])
  have hpτ : Prefix (encodeInput kind I) "input.data" τ := by
    simpa only [Prefix,hdims.frame_arr "input.data" (by decide),μ,ν,arrs_setVar] using hp
  have hkτ : τ.vars "flow.kind" = tag kind :=
    (hdims.frame_var "flow.kind" (by decide)).trans (by simp [μ,ν])
  exact ⟨τ,hkind.seq (horder.seq hdims),hpτ,hpost,hkτ⟩

end Lax455465Proofs.RamGraphHeader
