import Lax455465Proofs.LayeredWalkVector
import Lax455465Proofs.LayeredPathProjection

namespace Lax455465Proofs.LayeredExtractionStep
open LayeredFlowLP LayeredGraphFlow LayeredWalkState LayeredPathSweep
open scoped NNRat BigOperators

/-- Properties retained from one actual native extraction step. -/
structure Valid {n L : ℕ} (q : Coordinate n L → ℚ≥0) (a : ℚ≥0) (st : Edge n)
    (path : Fin (L+1) → Fin n) (ys : List (Fin n)) : Prop where
  source : path 0=st.1
  target : path (Fin.last L)=st.2
  positive : ∀ k,0<q (edge st path k)
  simple : ys.Nodup
  head : ys.head?=some st.1
  last : ys.getLast?=some st.2
  length : ys.length≤L+1
  sublist : List.Sublist (PathSimplification.arcs ys)
    (PathSimplification.arcs ((LayeredSweepGraph.raw path).map Prod.snd))

def amount {n L : ℕ} (q : Coordinate n L → ℚ≥0) (a : ℚ≥0)
    (st : Edge n) (path : Fin (L+1) → Fin n) : ℚ≥0 :=
  Bottleneck.minimum a (RamBottleneck.edges q st path)

theorem of_walk {n L : ℕ} {q : Coordinate n L → ℚ≥0} {a : ℚ≥0} {st : Edge n}
    {path : Fin (L+1) → Fin n} {ys : List (Fin n)}
    (h : Walk q st (LayeredSweepGraph.raw path) (Fin.last L,st.2) ys)
    (hs : path 0=st.1) (ht : path (Fin.last L)=st.2)
    (hp : ∀ k,0<q (edge st path k)) : Valid q a st path ys := by
  refine ⟨hs,ht,hp,h.simple,h.simpleHead,h.simpleLast,?_,h.simpleArcs⟩
  simpa only [LayeredSweepGraph.raw,List.length_ofFn] using h.simpleLength

theorem amount_positive {n L : ℕ} {q : Coordinate n L → ℚ≥0} {a : ℚ≥0} {st : Edge n}
    {path : Fin (L+1) → Fin n} {ys : List (Fin n)} (h : Valid q a st path ys)
    (ha : 0<a) : 0<amount q a st path := by
  apply Bottleneck.positive _ _ ha
  intro r hr
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hr
  exact h.positive k

theorem amount_le {n L : ℕ} (q : Coordinate n L → ℚ≥0) (a : ℚ≥0)
    (st : Edge n) (path : Fin (L+1) → Fin n) :
    amount q a st path≤a ∧ ∀ k,amount q a st path≤q (edge st path k) :=
  ⟨Bottleneck.le_start _ _,fun k => Bottleneck.le_entry _ _ _ (List.mem_ofFn.mpr ⟨k,rfl⟩)⟩

theorem amount_lattice {n L : ℕ} (q : Coordinate n L → ℚ≥0) (a : ℚ≥0)
    (st : Edge n) (path : Fin (L+1) → Fin n) (D H : ℕ)
    (hq : ∀ j,ResidualLattice.Bounded D H (q j)) (ha : ResidualLattice.Bounded D H a) :
    ResidualLattice.Bounded D H (amount q a st path) := by
  apply Bottleneck.lattice _ _ _ _ ha
  intro r hr
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hr
  exact hq _

theorem remaining_coe {n L : ℕ} (q : Coordinate n L → ℚ≥0) (a : ℚ≥0)
    (st : Edge n) (path : Fin (L+1) → Fin n) :
    (RamTruncatedSubtract.value a (amount q a st path) : ℚ)=
      (a : ℚ)-(amount q a st path : ℚ) := by
  change max ((a : ℚ)-(amount q a st path : ℚ)) 0=_
  exact max_eq_left (sub_nonneg.mpr (by exact_mod_cast (amount_le q a st path).1))

theorem progress {n L : ℕ} {q : Coordinate n L → ℚ≥0} {a : ℚ≥0} {st : Edge n}
    {path : Fin (L+1) → Fin n} {ys : List (Fin n)} (h : Valid q a st path ys) (ha : 0<a) :
    RamTruncatedSubtract.value a (amount q a st path)=0 ∨
      (support (after q (amount q a st path) st path L)).card<(support q).card := by
  by_cases he : amount q a st path=a
  · left
    apply Subtype.ext
    simp [RamTruncatedSubtract.value,he]
  · exact Or.inr (support_decreases q a st path ha h.positive he)

theorem balance {n L : ℕ} {q : Coordinate n L → ℚ≥0} {a : ℚ≥0} {st : Edge n}
    {path : Fin (L+1) → Fin n} {ys : List (Fin n)} (h : Valid q a st path ys)
    (hb : AcyclicFlowPath.Balance (graph (arc q) st) (0,st.1) (Fin.last L,st.2) (a : ℚ)) :
    AcyclicFlowPath.Balance (graph (arc (after q (amount q a st path) st path L)) st)
      (0,st.1) (Fin.last L,st.2) (RamTruncatedSubtract.value a (amount q a st path) : ℚ) := by
  rw [remaining_coe]
  exact LayeredSweepGraph.balance_after _ _ _ _ (amount_le q a st path).2 h.source h.target _ hb

/-- Cycle erasure can only reduce the physical load of the extracted raw path. -/
theorem count_le {n L : ℕ} {q : Coordinate n L → ℚ≥0} {a : ℚ≥0} {st : Edge n}
    {path : Fin (L+1) → Fin n} {ys : List (Fin n)} (h : Valid q a st path ys) (u v : Fin n) :
    PathCounting.count ys u v≤∑ i : Fin (L+1),∑ j : Fin (L+1),
      PathCounting.count (LayeredSweepGraph.raw path) (i,u) (j,v) := by
  rw [←LayeredPathProjection.count_map]
  unfold PathCounting.count
  exact_mod_cast h.sublist.count_le (u,v)

end Lax455465Proofs.LayeredExtractionStep
