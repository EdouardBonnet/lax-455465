import Lax455465Proofs.LayeredExtractionLoad
import Lax455465Proofs.PathRecordBuffer

namespace Lax455465Proofs.LayeredCommodityState
open LayeredFlowLP LayeredGraphFlow LayeredWalkState LayeredPathSweep
open LayeredExtractionStep LayeredExtractionLoad PathRecordBuffer AcyclicFlowDecomposition
open scoped NNRat

def budget (n L : ℕ) : ℕ := 1+(n*n)*(L*(n*n))+1

/-- Conservation, capacity accounting, and the decreasing support budget
for one commodity's actual emitted records. -/
structure State {n L : ℕ} (q₀ : Coordinate n L → ℚ≥0) (a₀ : ℚ≥0) (st : Edge n)
    (D H i : ℕ) (q : Coordinate n L → ℚ≥0) (a : ℚ≥0) (rs : PathRecordBuffer.Records n) : Prop where
  lattice : ∀ j,ResidualLattice.Bounded D H (q j)
  remainder : ResidualLattice.Bounded D H a
  balance : AcyclicFlowPath.Balance (graph (arc q) st) (0,st.1) (Fin.last L,st.2) (a : ℚ)
  valid : AcyclicFlowDecomposition.Valid st.1 st.2 (rational rs)
  lengths : ∀ r∈rs,r.1.length≤L+1
  weights : ∀ r∈rs,ResidualLattice.Bounded D H r.2
  count : rs.length≤ i
  progress : a≠0 → (support q).card+i+1≤budget n L
  mass : AcyclicFlowDecomposition.mass (rational rs)+(a : ℚ)=(a₀ : ℚ)
  load : ∀ u v,AcyclicFlowDecomposition.load (rational rs) u v+totalLoad q u v≤totalLoad q₀ u v
  others : ∀ other : Edge n,other≠st → graph (arc q) other=graph (arc q₀) other
  value : q (variableIndex n L (.inl 0))=q₀ (variableIndex n L (.inl 0))

theorem initial {n L : ℕ} (q₀ : Coordinate n L → ℚ≥0) (a₀ : ℚ≥0) (st : Edge n) (D H : ℕ)
    (hq : ∀ j,ResidualLattice.Bounded D H (q₀ j)) (ha : ResidualLattice.Bounded D H a₀)
    (hb : AcyclicFlowPath.Balance (graph (arc q₀) st) (0,st.1) (Fin.last L,st.2) (a₀ : ℚ)) :
    State q₀ a₀ st D H 0 q₀ a₀ [] := by
  refine ⟨hq,ha,hb,by simp [AcyclicFlowDecomposition.Valid,rational],by simp,by simp,by simp,?_,by simp [rational],?_,by simp,rfl⟩
  · intro _
    have hh := Finset.card_le_univ (support q₀)
    simpa only [Fintype.card_fin,Nat.add_zero,budget] using Nat.add_le_add_right hh 1
  · intro u v
    simp [rational]

theorem step {n L : ℕ} {q₀ : Coordinate n L → ℚ≥0} {a₀ : ℚ≥0} {st : Edge n} {D H i : ℕ}
    {q : Coordinate n L → ℚ≥0} {a : ℚ≥0} {rs : PathRecordBuffer.Records n}
    (h : State q₀ a₀ st D H i q a rs) (ha : 0<a)
    {path : Fin (L+1) → Fin n} {ys : List (Fin n)} (hv : LayeredExtractionStep.Valid q a st path ys) :
    State q₀ a₀ st D H (i+1) (after q (amount q a st path) st path L)
      (RamTruncatedSubtract.value a (amount q a st path)) (rs++[(ys,amount q a st path)]) := by
  let w := amount q a st path
  have hw := amount_lattice q a st path D H h.lattice h.remainder
  refine ⟨LayeredPathSweep.lattice q w st path D H L h.lattice hw,
    ResidualLattice.subtract h.remainder hw,LayeredExtractionStep.balance hv h.balance,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro r hr
    rw [rational_append,rational_singleton] at hr
    rcases List.mem_append.mp hr with hr | hr
    · exact h.valid r hr
    · have he : r=(ys,(w : ℚ)) := List.mem_singleton.mp hr
      subst r
      exact ⟨by exact_mod_cast amount_positive hv ha,hv.head,hv.last,hv.simple⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact h.lengths r hr
    · have he : r=(ys,w) := List.mem_singleton.mp hr
      subst r
      exact hv.length
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact h.weights r hr
    · have he : r=(ys,w) := List.mem_singleton.mp hr
      subst r
      exact hw
  · simp only [List.length_append,List.length_singleton]
    have hh:=h.count
    omega
  · intro hne
    have hbefore := h.progress (ne_of_gt ha)
    have hd := (LayeredExtractionStep.progress hv ha).resolve_left hne
    omega
  · rw [mass_append,rational_singleton,mass_cons,mass_nil,add_zero,remaining_coe]
    have hh := h.mass
    dsimp only [w]
    linarith only [hh]
  · intro u v
    rw [rational_append,rational_singleton,PathRecordArithmetic.load_append,load_cons,load_nil,add_zero]
    have hs := LayeredExtractionLoad.step_le hv u v
    have hh := h.load u v
    dsimp only [w]
    linarith only [hs,hh]
  · intro other hother
    exact (LayeredSweepGraph.other_graph q w st other path hother L).trans (h.others other hother)
  · exact (LayeredSweepGraph.value_unchanged q w st path L).trans h.value

theorem idle {n L : ℕ} {q₀ : Coordinate n L → ℚ≥0} {a₀ : ℚ≥0} {st : Edge n} {D H i : ℕ}
    {q : Coordinate n L → ℚ≥0} {a : ℚ≥0} {rs : PathRecordBuffer.Records n}
    (h : State q₀ a₀ st D H i q a rs) (ha : a=0) : State q₀ a₀ st D H (i+1) q a rs := by
  exact { h with count := h.count.trans (Nat.le_succ i), progress := fun hne => (hne ha).elim }

theorem finished {n L : ℕ} {q₀ : Coordinate n L → ℚ≥0} {a₀ : ℚ≥0} {st : Edge n} {D H : ℕ}
    {q : Coordinate n L → ℚ≥0} {a : ℚ≥0} {rs : PathRecordBuffer.Records n}
    (h : State q₀ a₀ st D H (budget n L) q a rs) : a=0 := by
  by_contra hne
  have hh:=h.progress hne
  omega

end Lax455465Proofs.LayeredCommodityState
