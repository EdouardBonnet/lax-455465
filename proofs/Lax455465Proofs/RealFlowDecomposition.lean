import Lax455465Proofs.RealPathSubtraction

open scoped BigOperators
namespace Lax455465Proofs.RealFlowDecomposition
open PathSimplification RealPositivePath RealPathSubtraction
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev Records (α : Type*) := List (List α × ℝ)

def mass (rs : Records α) : ℝ := (rs.map Prod.snd).sum
def load (rs : Records α) (u v : α) : ℝ :=
  (rs.map fun r => r.2*RealPathCounting.count r.1 u v).sum
def Valid (s t : α) (rs : Records α) : Prop :=
  ∀ r∈rs,0 < r.2 ∧ r.1.head?=some s ∧ r.1.getLast?=some t ∧ r.1.Nodup

@[simp] theorem mass_nil : mass ([] : Records α)=0 := rfl
@[simp] theorem mass_cons (r : List α×ℝ) (rs : Records α) : mass (r::rs)=r.2+mass rs := rfl
@[simp] theorem load_nil (u v : α) : load ([] : Records α) u v=0 := rfl
@[simp] theorem load_cons (r : List α×ℝ) (rs : Records α) (u v : α) :
    load (r::rs) u v=r.2*RealPathCounting.count r.1 u v+load rs u v := rfl

/-- Repeated bottleneck subtraction yields at most one more path than the
number of positive arcs. Every record has positive real weight. -/
theorem exists_records (g : α → α → ℝ) (hg : ∀ u v,0 ≤ g u v)
    (s t : α) (hst : s ≠ t) (a : ℝ) (ha : 0 ≤ a) (hbal : Balance g s t a) :
    ∃ rs : Records α,Valid s t rs ∧ mass rs=a ∧
      (∀ u v,load rs u v ≤ g u v) ∧ rs.length ≤ (support g).card+1 := by
  have aux : ∀ m (g : α → α → ℝ) (a : ℝ),
      (support g).card=m → (∀ u v,0 ≤ g u v) → 0 ≤ a →
      Balance g s t a →
      ∃ rs : Records α,Valid s t rs ∧ mass rs=a ∧
        (∀ u v,load rs u v ≤ g u v) ∧ rs.length ≤ (support g).card+1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro g a hcard hg ha hbal
      by_cases haz : a=0
      · subst a
        exact ⟨[],by simp [Valid],rfl,hg,by simp⟩
      have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
      obtain ⟨xs,hs,ht,hn,hsize,hpos⟩ := exists_path g hg s t hst a hapos hbal
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
          unfold RealPathSubtraction.residual at hh
          linarith
      · have hdec := support_decreases g xs hn w hw e he hew
        obtain ⟨rs,hvalidrs,hmass,hload,hlen⟩ :=
          ih (support (residual g xs w)).card (by omega) (residual g xs w) (a-w) rfl
            hres (sub_nonneg.mpr hwa) (residual_balance g s t a hbal xs hs ht w)
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
          unfold RealPathSubtraction.residual at hh
          linarith
        · simp only [List.length_cons]
          omega
  exact aux (support g).card g a rfl hg ha hbal

end Lax455465Proofs.RealFlowDecomposition
