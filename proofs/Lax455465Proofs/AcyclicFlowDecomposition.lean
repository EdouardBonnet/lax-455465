import Lax455465Proofs.PathSubtraction

open scoped BigOperators
namespace Lax455465Proofs.AcyclicFlowDecomposition
open PathSimplification AcyclicFlowPath PathSubtraction
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev Records (α : Type*) := List (List α × ℚ)

def mass (rs : Records α) : ℚ := (rs.map Prod.snd).sum
def load (rs : Records α) (u v : α) : ℚ :=
  (rs.map fun r => r.2*PathCounting.count r.1 u v).sum
def Valid (s t : α) (rs : Records α) : Prop :=
  ∀ r∈rs,0 < r.2 ∧ r.1.head?=some s ∧ r.1.getLast?=some t ∧ r.1.Nodup

@[simp] theorem mass_nil : mass ([] : Records α)=0 := rfl
@[simp] theorem mass_cons (r : List α×ℚ) (rs : Records α) : mass (r::rs)=r.2+mass rs := rfl
@[simp] theorem load_nil (u v : α) : load ([] : Records α) u v=0 := rfl
@[simp] theorem load_cons (r : List α×ℚ) (rs : Records α) (u v : α) :
    load (r::rs) u v=r.2*PathCounting.count r.1 u v+load rs u v := rfl

/-- Repeated bottleneck subtraction yields at most one more path than the
number of positive arcs. Every record has positive rational weight. -/
theorem exists_records (g : α → α → ℚ) (hg : ∀ u v,0 ≤ g u v)
    (rank : α → ℕ) (N : ℕ) (hrank : ∀ u,rank u ≤ N)
    (hstep : ∀ u v,0 < g u v → rank u < rank v)
    (s t : α) (hst : s ≠ t) (a : ℚ) (ha : 0 ≤ a) (hbal : Balance g s t a) :
    ∃ rs : Records α,Valid s t rs ∧ mass rs=a ∧
      (∀ u v,load rs u v ≤ g u v) ∧ rs.length ≤ (support g).card+1 := by
  have aux : ∀ m (g : α → α → ℚ) (a : ℚ),
      (support g).card=m → (∀ u v,0 ≤ g u v) → 0 ≤ a →
      (∀ u v,0 < g u v → rank u < rank v) → Balance g s t a →
      ∃ rs : Records α,Valid s t rs ∧ mass rs=a ∧
        (∀ u v,load rs u v ≤ g u v) ∧ rs.length ≤ (support g).card+1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro g a hcard hg ha hstep hbal
      by_cases haz : a=0
      · subst a
        exact ⟨[],by simp [Valid],rfl,hg,by simp⟩
      have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
      obtain ⟨xs,hs,ht,hn,hsize,hpos⟩ := exists_path g hg rank N hrank hstep s t hst a hapos hbal
      obtain ⟨w,hw,hwa,hwg,hstop⟩ := exists_amount g xs hsize hpos a hapos
      have hres := residual_nonnegative g hg xs hn w hwg
      have hvalid : 0 < w ∧ xs.head?=some s ∧ xs.getLast?=some t ∧ xs.Nodup := ⟨hw,hs,ht,hn⟩
      rcases hstop with hwaeq | ⟨e,he,hew⟩
      · refine ⟨[(xs,w)],?_,by simpa using hwaeq,?_,by simp⟩
        · intro r hr
          have he : r=(xs,w) := by simpa using hr
          subst r
          exact hvalid
        · intro u v
          have hh := hres u v
          simp only [load_cons,load_nil,add_zero]
          unfold PathSubtraction.residual at hh
          linarith
      · have hdec := support_decreases g xs hn w hw e he hew
        have hresstep : ∀ u v,0 < residual g xs w u v → rank u < rank v := by
          intro u v huv
          exact hstep u v (huv.trans_le (residual_le g xs w hw.le u v))
        obtain ⟨rs,hvalidrs,hmass,hload,hlen⟩ :=
          ih (support (residual g xs w)).card (by omega) (residual g xs w) (a-w) rfl
            hres (sub_nonneg.mpr hwa) hresstep (residual_balance g s t a hbal xs hs ht w)
        refine ⟨(xs,w)::rs,?_,?_,?_,?_⟩
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact hvalid
          · exact hvalidrs r hr
        · simp only [mass_cons,hmass]
          ring
        · intro u v
          have hh := hload u v
          simp only [load_cons]
          unfold PathSubtraction.residual at hh
          linarith
        · simp only [List.length_cons]
          omega
  exact aux (support g).card g a rfl hg ha hstep hbal

theorem load_nonnegative {s t : α} {rs : Records α} (h : Valid s t rs) (u v : α) :
    0 ≤ load rs u v := by
  apply List.sum_nonneg
  intro z hz
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hz
  exact mul_nonneg (h r hr).1.le (PathCounting.nonnegative r.1 u v)

/-- Every edge in a positive path record was already positive in the input flow. -/
theorem record_supported (g : α → α → ℚ) {s t : α} {rs : Records α}
    (hvalid : Valid s t rs) (hload : ∀ u v,load rs u v ≤ g u v)
    (r : List α×ℚ) (hr : r∈rs) (e : α×α) (he : e∈arcs r.1) : 0 < g e.1 e.2 := by
  have hh : r.2*PathCounting.count r.1 e.1 e.2 ≤ load rs e.1 e.2 := by
    apply List.single_le_sum
    · intro z hz
      obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hz
      exact mul_nonneg (hvalid r' hr').1.le (PathCounting.nonnegative r'.1 e.1 e.2)
    · exact List.mem_map.mpr ⟨r,hr,rfl⟩
  rw [PathCounting.count_eq (hvalid r hr).2.2.2,if_pos he,mul_one] at hh
  exact (hvalid r hr).1.trans_le (hh.trans (hload e.1 e.2))

end Lax455465Proofs.AcyclicFlowDecomposition
