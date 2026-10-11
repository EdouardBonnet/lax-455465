import Lax455465Proofs.RamArithmetic
import Lax455465Proofs.FlowLpIndices

namespace Lax455465Proofs.RamMetricIndices

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning DirectedFlowLP FlowLpIndices

def command : Com := .seq (.assign "metric.a" (.var "metric.entry"))
  (.seq (.assign "metric.u" (.div (.var "metric.entry") (.var "metric.n")))
    (.seq (.assign "metric.v" (.sub (.var "metric.entry") (.mul (.var "metric.u") (.var "metric.n"))))
      (.seq (.assign "metric.b" (.add (.mul (.var "metric.u") (.var "metric.n")) (.var "metric.p")))
        (.assign "metric.c" (.add (.mul (.var "metric.p") (.var "metric.n")) (.var "metric.v"))))))

/-- Compute all three actual row-major addresses for one min-plus update. -/
theorem command_spec (B : ℕ) {n : ℕ} (u v p : Fin n) (hn : n < B) (hn2 : n*n < B) :
    Spec B (fun σ => σ.vars "metric.n" = n ∧ σ.vars "metric.p" = p.val ∧
      σ.vars "metric.entry" = (edgeIndex n (u,v)).val) command
      (fun _ τ => τ.vars "metric.a" = (edgeIndex n (u,v)).val ∧
        τ.vars "metric.b" = (edgeIndex n (u,p)).val ∧
        τ.vars "metric.c" = (edgeIndex n (p,v)).val) 24 := by
  have hidx : (edgeIndex n (u,v)).val < B := (edgeIndex n (u,v)).isLt.trans hn2
  have hidxb : (edgeIndex n (u,p)).val < B := (edgeIndex n (u,p)).isLt.trans hn2
  have hidxc : (edgeIndex n (p,v)).val < B := (edgeIndex n (p,v)).isLt.trans hn2
  have hu : u.val < B := u.isLt.trans hn
  have hv : v.val < B := v.isLt.trans hn
  have hp : p.val < B := p.isLt.trans hn
  have hup : u.val*n < B := by rw [edge_value] at hidx; omega
  have hpp : p.val*n < B := by rw [edge_value] at hidxc; omega
  have hdiv := edge_div u v
  have hmod := edge_mod u v
  rw [Nat.mod_def] at hmod
  have hb : u.val*n+p.val < B := by simpa only [edge_value] using hidxb
  have hc : p.val*n+v.val < B := by simpa only [edge_value] using hidxc
  rintro σ ⟨hnσ,hpσ,heσ⟩
  run_vcg
  all_goals simp_all [edge_value]

end Lax455465Proofs.RamMetricIndices
