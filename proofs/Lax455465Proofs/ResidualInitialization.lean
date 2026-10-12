import Lax455465Proofs.RamShortHeader
import Lax455465Proofs.RationalSumHeight

namespace Lax455465Proofs.ResidualInitialization
open scoped NNRat

def initial {N : ℕ} (q : Fin (1+N) → ℚ≥0) : List ℚ≥0 := (q 0/2)::List.ofFn q
def denominator {N : ℕ} (q : Fin (1+N) → ℚ≥0) : ℕ := RationalSumHeight.denominator (initial q)
def height (w : ℕ) : ℕ := 2^(w+1)

theorem initial_height {N : ℕ} (q : Fin (1+N) → ℚ≥0) (w : ℕ)
    (hn : ∀ j,(q j).num≤2^w) (hd : ∀ j,(q j).den≤2^w) :
    ∀ r∈initial q,r.num≤height w ∧ r.den≤height w := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · have hh:=RamShortHeader.half_height (2^w) (q 0)
      ⟨by simpa only [NNRat.natAbs_num_coe] using hn 0,hd 0⟩
    have he : 2*2^w=height w := by simp [height,pow_succ,Nat.mul_comm]
    exact ⟨by simpa only [NNRat.natAbs_num_coe,he] using hh.1,by simpa only [NNRat.den_coe,he] using hh.2⟩
  · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hr
    have hpow : 2^w≤height w := Nat.pow_le_pow_right (by decide) (Nat.le_succ w)
    exact ⟨(hn j).trans hpow,(hd j).trans hpow⟩

theorem bounded {N : ℕ} (q : Fin (1+N) → ℚ≥0) (w : ℕ)
    (hn : ∀ j,(q j).num≤2^w) (hd : ∀ j,(q j).den≤2^w) :
    (∀ j,ResidualLattice.Bounded (denominator q) (height w) (q j)) ∧
      ResidualLattice.Bounded (denominator q) (height w) (q 0/2) := by
  have hi:=initial_height q w hn hd
  constructor
  · intro j
    exact ResidualLattice.initial (initial q) (height w) (fun r hr => (hi r hr).1) (q j)
      (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨j,rfl⟩))
  · exact ResidualLattice.initial (initial q) (height w) (fun r hr => (hi r hr).1) (q 0/2) List.mem_cons_self

theorem denominator_pos {N : ℕ} (q : Fin (1+N) → ℚ≥0) : 0<denominator q :=
  RationalSumHeight.denominator_pos (initial q)

theorem residual_height {N : ℕ} (q : Fin (1+N) → ℚ≥0) (w S : ℕ) (hN : 1+N≤S)
    (hn : ∀ j,(q j).num≤2^w) (hd : ∀ j,(q j).den≤2^w) :
    height w*denominator q≤2^((w+1)*(S+2)) := by
  have hi:=initial_height q w hn hd
  have hden:=RationalSumHeight.denominator_bound (initial q) (w+1) (fun r hr => (hi r hr).2)
  have hlen : (initial q).length=N+2 := by simp [initial]; omega
  have hp : (w+1)+(w+1)*(N+2)≤(w+1)*(S+2) := by nlinarith only [hN]
  calc height w*denominator q≤2^(w+1)*2^((w+1)*(N+2)) := by
         dsimp only [height,denominator]
         exact Nat.mul_le_mul_left _ (by simpa only [hlen] using hden)
       _=2^((w+1)+(w+1)*(N+2)) := (pow_add _ _ _).symm
       _≤2^((w+1)*(S+2)) := Nat.pow_le_pow_right (by decide) hp

end Lax455465Proofs.ResidualInitialization
