import Lax455465Proofs.LayeredDualBound
import Lax455465Proofs.LayeredFlowBounds

open scoped BigOperators
namespace Lax455465Proofs.ShortLayerSelection
open Lax455465.RationalEncoding LayeredFlowLP LayeredFlowDual LayeredFlowFeasibility
open Lax109476.LinearProgram

/-- The inexpensive stopping condition uses only the LP value and maximum
incident capacity; it does not require knowing the sparsest cut. -/
def good (n : ℕ) (R : ℚ) (value : ℕ → ℚ) (L : ℕ) : Prop :=
  R ≤ 4*(n : ℚ)*L*value L

instance (n : ℕ) (R : ℚ) (value : ℕ → ℚ) (L : ℕ) : Decidable (good n R value L) :=
  inferInstanceAs (Decidable (R ≤ 4*(n : ℚ)*L*value L))

def candidates (n : ℕ) (R : ℚ) (value : ℕ → ℚ) : Finset ℕ :=
  (Finset.Icc 1 (n-1)).filter (good n R value)

/-- First successful layer budget, with the full simple-path budget as fallback. -/
def select (n : ℕ) (R : ℚ) (value : ℕ → ℚ) : ℕ :=
  if h : (candidates n R value).Nonempty then (candidates n R value).min' h else n-1

theorem select_range (n : ℕ) (hn : 2 ≤ n) (R : ℚ) (value : ℕ → ℚ) :
    1 ≤ select n R value ∧ select n R value ≤ n-1 := by
  unfold select
  split_ifs with h
  · exact Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.min'_mem _ h)).1
  · omega

theorem select_good_or_full (n : ℕ) (R : ℚ) (value : ℕ → ℚ) :
    good n R value (select n R value) ∨ select n R value=n-1 := by
  unfold select
  split_ifs with h
  · exact Or.inl (Finset.mem_filter.mp (Finset.min'_mem _ h)).2
  · exact Or.inr rfl

theorem select_le (n : ℕ) (R : ℚ) (value : ℕ → ℚ) (L : ℕ)
    (hL : 1 ≤ L) (hgood : L ≤ n-1 → good n R value L) : select n R value ≤ L := by
  by_cases hmax : L ≤ n-1
  · have hmem : L ∈ candidates n R value :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hL,hmax⟩,hgood hmax⟩
    have hne : (candidates n R value).Nonempty := ⟨L,hmem⟩
    simp only [select,dif_pos hne]
    exact Finset.min'_le _ _ hmem
  · unfold select
    split_ifs with h
    · have hh := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.min'_mem _ h)).1).2
      omega
    · omega

/-- Quantitative scan bounds. Even when no stopping test succeeds, the
full-length LP has the needed value by the cycle-erased dual argument. -/
theorem guarantees (n : ℕ) (hn : 2 ≤ n) (s q : ℚ) (hs : 0 < s) (hq : 1/2 ≤ q)
    (value : ℕ → ℚ) (hv : ∀ L,0 ≤ value L)
    (hlarge : ∀ L : ℕ, 1024*(RegionBudget.steps n : ℚ)*q ≤ L ∨ n-1 ≤ L →
      s/(2048*(RegionBudget.steps n : ℚ)) < value L) :
    let L := select n (q*n*s) value
    1 ≤ L ∧ L ≤ n-1 ∧
      (L : ℚ) ≤ 1026*(RegionBudget.steps n : ℚ)*q ∧
      s/(4104*(RegionBudget.steps n : ℚ)) ≤ value L := by
  let K : ℚ := RegionBudget.steps n
  have hK : 1 ≤ K := by
    change (1 : ℚ) ≤ (RegionBudget.steps n : ℚ)
    exact_mod_cast RegionBudget.steps_pos n
  have hKpos : 0 < K := by linarith
  have hqpos : 0 < q := by linarith
  have hnpos : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  let T : ℕ := ⌈1024*K*q⌉₊
  have hTlo : 1024*K*q ≤ (T : ℚ) := Nat.le_ceil _
  have hTpos : 1 ≤ T := by
    have hp : (0 : ℚ) < T := lt_of_lt_of_le (by positivity) hTlo
    have : 0 < T := by exact_mod_cast hp
    omega
  have hTup : (T : ℚ) ≤ 1026*K*q := by
    have ht : (T : ℚ) < 1024*K*q+1 := Nat.ceil_lt_add_one (by positivity)
    have hkq : 1 ≤ 2*K*q := by nlinarith
    nlinarith
  have htest : good n (q*n*s) value T := by
    have hf := hlarge T (Or.inl hTlo)
    have hprod := mul_le_mul hTlo hf.le (by positivity : (0 : ℚ) ≤ s/(2048*K)) (by positivity : (0 : ℚ) ≤ T)
    have he : (1024*K*q)*(s/(2048*K))=q*s/2 := by field_simp; ring
    rw [he] at hprod
    have hh := mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℚ) ≤ 4*n)
    unfold good
    have hnonneg : 0 ≤ q*n*s := by positivity
    nlinarith
  have hselect : select n (q*n*s) value ≤ T := select_le n _ value T hTpos (fun _ => htest)
  have hsize : (select n (q*n*s) value : ℚ) ≤ 1026*K*q :=
    (by exact_mod_cast hselect : (select n (q*n*s) value : ℚ) ≤ T).trans hTup
  obtain ⟨hmin,hmax⟩ := select_range n hn (q*n*s) value
  refine ⟨hmin,hmax,hsize,?_⟩
  rcases select_good_or_full n (q*n*s) value with hg | he
  · have hh := mul_le_mul_of_nonneg_right hsize (hv (select n (q*n*s) value))
    have hh' := mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℚ) ≤ 4*n)
    have hb : s ≤ 4104*K*value (select n (q*n*s) value) := by
      apply (mul_le_mul_iff_right₀ (mul_pos hqpos hnpos)).mp
      unfold good at hg
      nlinarith
    exact (div_le_iff₀ (by positivity : (0 : ℚ) < 4104*K)).mpr (by nlinarith)
  · have hf := hlarge (select n (q*n*s) value) (Or.inr he.ge)
    have hd : s/(4104*K) ≤ s/(2048*K) := by
      apply div_le_div_of_nonneg_left hs.le (by positivity)
      nlinarith
    exact hd.trans hf.le

end Lax455465Proofs.ShortLayerSelection
