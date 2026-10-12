import Lax455465Proofs.RamBottleneck
import Lax455465Proofs.ResidualLattice

namespace Lax455465Proofs.LayeredPathSweep
open LayeredFlowLP
open scoped NNRat

abbrev Coordinate (n L : ℕ) := Fin (1+(n*n)*(L*(n*n)))

def edge {n L : ℕ} (st : Edge n) (path : Fin (L+1) → Fin n) (k : Fin L) : Coordinate n L :=
  variableIndex n L (.inr (st,(k,(path k.castSucc,path k.succ))))

theorem edge_injective {n L : ℕ} (st : Edge n) (path : Fin (L+1) → Fin n) :
    Function.Injective (edge st path) := by
  intro k l he
  have hh := (variableIndex n L).injective he
  exact congrArg (fun a : Variable n L => match a with | .inl _ => k | .inr a => a.2.1) hh

def Processed {n L : ℕ} (st : Edge n) (path : Fin (L+1) → Fin n) (i : ℕ) (j : Coordinate n L) : Prop :=
  ∃ k : Fin L,k.val < i ∧ j=edge st path k

instance {n L : ℕ} (st : Edge n) (path : Fin (L+1) → Fin n) (i : ℕ) (j : Coordinate n L) :
    Decidable (Processed st path i j) := inferInstanceAs (Decidable (∃ k : Fin L,k.val < i ∧ j=edge st path k))

/-- Residual vector after the first i raw-path edges have been updated. -/
def after {n L : ℕ} (q : Coordinate n L → ℚ≥0) (w : ℚ≥0) (st : Edge n)
    (path : Fin (L+1) → Fin n) (i : ℕ) (j : Coordinate n L) : ℚ≥0 :=
  if Processed st path i j then RamTruncatedSubtract.value (q j) w else q j

@[simp] theorem after_zero {n L : ℕ} (q : Coordinate n L → ℚ≥0) (w : ℚ≥0)
    (st : Edge n) (path : Fin (L+1) → Fin n) : after q w st path 0=q := by
  funext j
  simp [after,Processed]

theorem unprocessed {n L : ℕ} (st : Edge n) (path : Fin (L+1) → Fin n) (k : Fin L) :
    ¬Processed st path k.val (edge st path k) := by
  rintro ⟨l,hl,he⟩
  have hh := edge_injective st path he
  subst l
  omega

theorem current {n L : ℕ} (q : Coordinate n L → ℚ≥0) (w : ℚ≥0)
    (st : Edge n) (path : Fin (L+1) → Fin n) (k : Fin L) :
    after q w st path k.val (edge st path k)=q (edge st path k) := by
  simp only [after,if_neg (unprocessed st path k)]

theorem processed_succ {n L : ℕ} (st : Edge n) (path : Fin (L+1) → Fin n) (k : Fin L) (j : Coordinate n L) :
    Processed st path (k.val+1) j ↔ Processed st path k.val j ∨ j=edge st path k := by
  constructor
  · rintro ⟨l,hl,he⟩
    by_cases hh : l.val<k.val
    · exact Or.inl ⟨l,hh,he⟩
    · have hle : l=k := Fin.ext (by omega)
      subst l
      exact Or.inr he
  · rintro (⟨l,hl,he⟩ | he)
    · exact ⟨l,by omega,he⟩
    · exact ⟨k,by omega,he⟩

/-- Each native update touches a distinct layered coordinate, even when
the raw physical walk contains a cycle or waiting step. -/
theorem after_succ {n L : ℕ} (q : Coordinate n L → ℚ≥0) (w : ℚ≥0)
    (st : Edge n) (path : Fin (L+1) → Fin n) (k : Fin L) :
    after q w st path (k.val+1)=Function.update (after q w st path k.val) (edge st path k)
      (RamTruncatedSubtract.value (q (edge st path k)) w) := by
  funext j
  by_cases he : j=edge st path k
  · subst j
    rw [Function.update_self]
    simp only [after,processed_succ,or_true,if_true]
  · rw [Function.update_of_ne he]
    simp only [after,processed_succ,he,or_false]

theorem full {n L : ℕ} (q : Coordinate n L → ℚ≥0) (w : ℚ≥0)
    (st : Edge n) (path : Fin (L+1) → Fin n) (k : Fin L) :
    after q w st path L (edge st path k)=RamTruncatedSubtract.value (q (edge st path k)) w := by
  simp only [after,if_pos (show Processed st path L (edge st path k) from ⟨k,k.isLt,rfl⟩)]

theorem lattice {n L : ℕ} (q : Coordinate n L → ℚ≥0) (w : ℚ≥0)
    (st : Edge n) (path : Fin (L+1) → Fin n) (D H i : ℕ)
    (hq : ∀ j,ResidualLattice.Bounded D H (q j)) (hw : ResidualLattice.Bounded D H w) :
    ∀ j,ResidualLattice.Bounded D H (after q w st path i j) := by
  intro j
  unfold after
  split_ifs
  · exact ResidualLattice.subtract (hq j) hw
  · exact hq j

theorem subtract_le (a b : ℚ≥0) : RamTruncatedSubtract.value a b≤a := by
  change max ((a : ℚ)-(b : ℚ)) 0≤(a : ℚ)
  exact max_le (sub_le_self _ b.coe_nonneg) a.coe_nonneg

def support {n L : ℕ} (q : Coordinate n L → ℚ≥0) : Finset (Coordinate n L) :=
  Finset.univ.filter fun j => 0<q j

theorem support_subset {n L : ℕ} (q : Coordinate n L → ℚ≥0) (w : ℚ≥0)
    (st : Edge n) (path : Fin (L+1) → Fin n) (i : ℕ) : support (after q w st path i)⊆support q := by
  intro j hj
  simp only [support,Finset.mem_filter,Finset.mem_univ,true_and] at hj ⊢
  unfold after at hj
  split_ifs at hj
  · exact hj.trans_le (subtract_le _ _)
  · exact hj

/-- Unless the capped bottleneck finishes the demand, it annihilates an
actual positive residual coordinate and strictly decreases the support. -/
theorem support_decreases {n L : ℕ} (q : Coordinate n L → ℚ≥0) (a : ℚ≥0)
    (st : Edge n) (path : Fin (L+1) → Fin n)
    (ha : 0<a) (hpos : ∀ k : Fin L,0<q (edge st path k))
    (hne : Bottleneck.minimum a (RamBottleneck.edges q st path)≠a) :
    (support (after q (Bottleneck.minimum a (RamBottleneck.edges q st path)) st path L)).card<(support q).card := by
  let w := Bottleneck.minimum a (RamBottleneck.edges q st path)
  have hw : 0<w := Bottleneck.positive a _ ha (by
    intro r hr
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hr
    exact hpos k)
  have hmem : w∈RamBottleneck.edges q st path := (Bottleneck.selected a _).resolve_left hne
  obtain ⟨k,hk⟩ := List.mem_ofFn.mp hmem
  have he : q (edge st path k)=w := hk
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨support_subset q w st path L,?_⟩
  intro hsame
  have hbefore : edge st path k∈support q := by simp [support,hpos k]
  rw [←hsame] at hbefore
  have hzero : after q w st path L (edge st path k)=0 := by
    rw [full,he]
    apply Subtype.ext
    simp [RamTruncatedSubtract.value]
  simp only [support,Finset.mem_filter,Finset.mem_univ,true_and] at hbefore
  change 0<after q w st path L (edge st path k) at hbefore
  rw [hzero] at hbefore
  exact (lt_irrefl _ hbefore)

end Lax455465Proofs.LayeredPathSweep
