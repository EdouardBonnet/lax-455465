import Lax455465Proofs.RamArithmetic

namespace Lax455465Proofs.RamFlowDimensions

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- All dense LP dimensions are computed from the runtime graph order. -/
def command : Com :=
  .seq (.assign "lp.n2" (.mul (.var "lp.n") (.var "lp.n")))
    (.seq (.assign "lp.n3" (.mul (.var "lp.n2") (.var "lp.n")))
      (.seq (.assign "lp.rows" (.add (.var "lp.n2") (.mul (.lit 2) (.var "lp.n3"))))
        (.assign "lp.columns" (.add (.lit 1) (.mul (.var "lp.n2") (.var "lp.n2"))))))

theorem command_spec (B n : ℕ) (h2 : 2 < B) (hn : n < B)
    (hn2 : n*n < B) (hn3 : (n*n)*n < B) (hrows : n*n+2*((n*n)*n) < B)
    (hcols : 1+(n*n)*(n*n) < B) :
    Spec B (fun σ => σ.vars "lp.n" = n) command
      (fun _ τ => τ.vars "lp.n" = n ∧ τ.vars "lp.n2" = n*n ∧
        τ.vars "lp.n3" = (n*n)*n ∧ τ.vars "lp.rows" = n*n+2*((n*n)*n) ∧
        τ.vars "lp.columns" = 1+(n*n)*(n*n)) 20 := by
  have htwice : 2*((n*n)*n) < B := by omega
  have hn4 : (n*n)*(n*n) < B := by omega
  rintro σ hσ
  run_vcg
  all_goals simp_all

end Lax455465Proofs.RamFlowDimensions
