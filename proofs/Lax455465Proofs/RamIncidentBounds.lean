import Lax455465Proofs.ShortInputBounds
import Lax455465Proofs.RamHostBounds

namespace Lax455465Proofs.RamIncidentBounds
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding
open scoped NNRat

theorem fits (b n W : ℕ) (hn : n≤b) (hW : 18*(b+1)^2+4≤W) :
    2*(2^((b+1)^2))^2+3<2^W ∧ 2*(n*n)+3<2^W := by
  have hn2 : n*n≤b*b := Nat.mul_le_mul hn hn
  have hs : RamHostBounds.sufficient ((b+1)^2) 0 0 (2*b*b+3) ≤ W := by
    dsimp only [RamHostBounds.sufficient]
    nlinarith only [hW]
  obtain ⟨hA,_,_,hI⟩ := RamHostBounds.sufficient_bounds ((b+1)^2) 0 0 (2*b*b+3) W hs
  exact ⟨hA,by nlinarith only [hn2,hI]⟩

theorem capacity_height {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) (u v : Fin n) :
    let b := bitSize (encodeInput kind I)
    (I.capacity u v).num ≤ 2^((b+1)^2) ∧ (I.capacity u v).den ≤ 2^((b+1)^2) := by
  have hh := LpInputSize.capacity_height kind I u v
  have he : 2^(bitSize (encodeInput kind I))≤2^((bitSize (encodeInput kind I)+1)^2) :=
    Nat.pow_le_pow_right (by decide) (by nlinarith)
  exact ⟨(by simpa only [NNRat.natAbs_num_coe] using hh.1.trans he),
    by simpa only [NNRat.den_coe] using hh.2.trans he⟩

theorem cost (n b : ℕ) (hn : n≤b) :
    ((((36*((2^((b+1)^2))^2).size+140)*n+16)+74)*n+20)≤512*(b+1)^4 := by
  let a := b+1
  have ha : 1≤a := by omega
  have hnA : n≤a := by omega
  have hs : ((2^(a^2))^2).size=2*a^2+1 := by
    rw [pow_two,←pow_add,Nat.size_pow]
    omega
  have hn2 : n*n≤a*a := Nat.mul_le_mul hnA hnA
  have ha2 : 1≤a^2 := one_le_pow₀ ha
  have ha4 : 1≤a^4 := one_le_pow₀ ha
  have han4 : n≤a^4 := hnA.trans (by simpa only [pow_one] using Nat.pow_le_pow_right ha (show 1≤4 by decide))
  have hf : 36*(2*a^2+1)+140≤248*a^2 := by omega
  have hmain := Nat.mul_le_mul hf hn2
  have he : (248*a^2)*(a*a)=248*a^4 := by ring
  rw [he] at hmain
  change ((36*((2^(a^2))^2).size+140)*n+16+74)*n+20≤512*a^4
  rw [hs]
  nlinarith only [hmain,han4,ha4]

end Lax455465Proofs.RamIncidentBounds
