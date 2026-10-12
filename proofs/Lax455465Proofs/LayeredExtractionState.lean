import Lax455465Proofs.LayeredCommodityState

namespace Lax455465Proofs.LayeredExtractionState
open LayeredFlowLP LayeredGraphFlow LayeredWalkState LayeredPathSweep
open LayeredExtractionLoad PathRecordBuffer AcyclicFlowDecomposition
open scoped NNRat

def index {n : ℕ} (st : Edge n) : ℕ := (DirectedFlowLP.edgeIndex n st).val

def Good {n L : ℕ} (rs : PathRecordBuffer.Records n) : Prop :=
  ∀ r∈rs,0<r.2 ∧ 2≤r.1.length ∧ r.1.Nodup ∧ r.1.length≤L+1

structure State {n L : ℕ} (q₀ : Coordinate n L → ℚ≥0) (a₀ : ℚ≥0)
    (D H i : ℕ) (q : Coordinate n L → ℚ≥0) (rs : PathRecordBuffer.Records n) : Prop where
  lattice : ∀ j,ResidualLattice.Bounded D H (q j)
  balances : ∀ st : Edge n,i≤ index st → st.1≠st.2 →
    AcyclicFlowPath.Balance (graph (arc q) st) (0,st.1) (Fin.last L,st.2) (a₀ : ℚ)
  good : Good (L := L) rs
  weights : ∀ r∈rs,ResidualLattice.Bounded D H r.2
  count : rs.length≤ i*LayeredCommodityState.budget n L
  routed : ∀ st : Edge n,index st< i → st.1≠st.2 → PathRecordArithmetic.routed (rational rs) st.1 st.2=(a₀ : ℚ)
  pending : ∀ st : Edge n,i≤ index st → PathRecordArithmetic.routed (rational rs) st.1 st.2=0
  load : ∀ u v,AcyclicFlowDecomposition.load (rational rs) u v+totalLoad q u v≤totalLoad q₀ u v
  value : q (variableIndex n L (.inl 0))=q₀ (variableIndex n L (.inl 0))

theorem initial {n L : ℕ} (q₀ : Coordinate n L → ℚ≥0) (a₀ : ℚ≥0) (D H : ℕ)
    (hq : ∀ j,ResidualLattice.Bounded D H (q₀ j))
    (hb : ∀ st : Edge n,st.1≠st.2 →
      AcyclicFlowPath.Balance (graph (arc q₀) st) (0,st.1) (Fin.last L,st.2) (a₀ : ℚ)) :
    State q₀ a₀ D H 0 q₀ [] := by
  refine ⟨hq,fun st _ hst => hb st hst,by simp [Good],by simp,by simp,?_,?_,?_,rfl⟩
  · intro st hi
    omega
  · simp [rational]
  · simp [rational]

theorem path_length {n : ℕ} (s t : Fin n) (hne : s≠t) (xs : List (Fin n))
    (hs : xs.head?=some s) (ht : xs.getLast?=some t) : 2≤xs.length := by
  cases xs with
  | nil => simp at hs
  | cons u xs =>
    cases xs with
    | nil =>
      have h1 : u=s := by simpa using hs
      have h2 : u=t := by simpa using ht
      exact (hne (h1.symm.trans h2)).elim
    | cons v xs => simp

theorem append_good {n L : ℕ} {rs ts : PathRecordBuffer.Records n} (h : Good (L := L) rs)
    {st : Edge n} (hne : st.1≠st.2) (ht : AcyclicFlowDecomposition.Valid st.1 st.2 (rational ts))
    (hlen : ∀ r∈ts,r.1.length≤L+1) : Good (L := L) (rs++ts) := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h r hr
  · have hh := ht (r.1,(r.2 : ℚ)) (List.mem_map.mpr ⟨r,hr,rfl⟩)
    exact ⟨by exact_mod_cast hh.1,path_length _ _ hne r.1 hh.2.1 hh.2.2.1,hh.2.2.2,hlen r hr⟩

theorem next {n L : ℕ} {q₀ : Coordinate n L → ℚ≥0} {a₀ : ℚ≥0} {D H i : ℕ}
    {q q' : Coordinate n L → ℚ≥0} {rs ts : PathRecordBuffer.Records n} {st : Edge n}
    (h : State q₀ a₀ D H i q rs) (hst : index st=i) (hne : st.1≠st.2)
    (hc : LayeredCommodityState.State q a₀ st D H (LayeredCommodityState.budget n L) q' 0 ts) :
    State q₀ a₀ D H (i+1) q' (rs++ts) := by
  have hm : AcyclicFlowDecomposition.mass (rational ts)=(a₀ : ℚ) := by simpa using hc.mass
  have hr (other : Edge n) : PathRecordArithmetic.routed (rational ts) other.1 other.2=
      if other=st then (a₀ : ℚ) else 0 := by
    rw [PathRecordArithmetic.routed_valid hc.valid,hm]
    simp only [Prod.ext_iff]
    split_ifs <;> grind
  have hi (other : Edge n) (hh : other≠st) : graph (arc q') other=graph (arc q) other := hc.others other hh
  refine ⟨hc.lattice,?_,append_good h.good hne hc.valid hc.lengths,?_,?_,?_,?_,?_,hc.value.trans h.value⟩
  · intro other hidx ho
    have hh : other≠st := by intro he; subst other; omega
    rw [hi other hh]
    exact h.balances other (by omega) ho
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact h.weights r hr
    · exact hc.weights r hr
  · simp only [List.length_append]
    have hh := h.count
    have ht := hc.count
    nlinarith only [hh,ht]
  · intro other hidx ho
    rw [rational_append,PathRecordArithmetic.routed_append,hr]
    by_cases he : other=st
    · subst other
      rw [if_pos rfl,h.pending st (by omega),zero_add]
    · rw [if_neg he,add_zero]
      have hnidx : index other≠i := by
        intro heidx
        have heval : (DirectedFlowLP.edgeIndex n other).val=(DirectedFlowLP.edgeIndex n st).val := heidx.trans hst.symm
        exact he ((DirectedFlowLP.edgeIndex n).injective (Fin.ext heval))
      exact h.routed other (by omega) ho
  · intro other hidx
    have hh : other≠st := by intro he; subst other; omega
    rw [rational_append,PathRecordArithmetic.routed_append,hr,if_neg hh,h.pending other (by omega),zero_add]
  · intro u v
    rw [rational_append,PathRecordArithmetic.load_append]
    have h1 := h.load u v
    have h2 := hc.load u v
    linarith only [h1,h2]

theorem diagonal {n L : ℕ} {q₀ : Coordinate n L → ℚ≥0} {a₀ : ℚ≥0} {D H i : ℕ}
    {q : Coordinate n L → ℚ≥0} {rs : PathRecordBuffer.Records n} {st : Edge n}
    (h : State q₀ a₀ D H i q rs) (hst : index st=i) (he : st.1=st.2) :
    State q₀ a₀ D H (i+1) q rs := by
  refine { h with
    balances := fun other hi hn => h.balances other (by omega) hn
    count := h.count.trans (Nat.mul_le_mul_right _ (Nat.le_succ i))
    pending := fun other hi => h.pending other (by omega)
    routed := ?_ }
  intro other hi hne
  have hnidx : index other≠i := by
    intro heidx
    have heval : (DirectedFlowLP.edgeIndex n other).val=(DirectedFlowLP.edgeIndex n st).val := heidx.trans hst.symm
    have hh := (DirectedFlowLP.edgeIndex n).injective (Fin.ext heval)
    subst other
    exact hne he
  exact h.routed other (by omega) hne

end Lax455465Proofs.LayeredExtractionState
