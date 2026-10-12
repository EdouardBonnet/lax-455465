import Lax455465Proofs.RamShortExtraction
import Lax455465Proofs.RamHostBounds

set_option maxRecDepth 32768

namespace Lax455465Proofs.RamShortExtractionBounds
open LayeredCommodityState

def space (S : ℕ) : ℕ := 64*(S+1)^4
def time (S r : ℕ) : ℕ := 4096*(r+1)*(S+1)^6

theorem space_bounds (n L S : ℕ) (hn : n≤S) (hL : L≤S) (hn2 : n*n≤S)
    (hLA : L*(n*n)≤S) (hc : 1+(n*n)*(L*(n*n))≤S) :
    n+n*n+L*(n*n)+2*(1+(n*n)*(L*(n*n)))+2*L+20≤space S ∧
      RamShortExtraction.reserve n L≤space S ∧
      (n*n+1)*budget n L+1≤space S ∧ RamShortExtraction.outputLength n L≤space S := by
  have hQ : budget n L≤S+1 := by dsimp only [budget]; omega
  have hp := Nat.mul_le_mul (by omega : n*n+1≤S+1) hQ
  have hpL := Nat.mul_le_mul hp (by omega : L+4≤S+4)
  have ht := Nat.mul_le_mul (Nat.mul_le_mul hn2 hQ) (by omega : L+4≤S+4)
  have hpow : (S+1)^3≤(S+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  dsimp only [space,RamShortExtraction.reserve,RamShortExtraction.outputLength]
  constructor
  · nlinarith only [hn,hL,hn2,hLA,hc,hpow,Nat.zero_le (S^3),Nat.zero_le (S^2)]
  constructor
  · nlinarith only [hpL,hL,hpow,Nat.zero_le (S^3),Nat.zero_le (S^2)]
  constructor
  · nlinarith only [hp,hpow]
  · nlinarith only [ht,hpow,Nat.zero_le (S^3),Nat.zero_le (S^2)]

theorem size_bounds (M r : ℕ) (hM : M≤2^r) :
    (M^2).size≤2*r+1 ∧ (2*M).size≤r+2 := by
  have hsq : M^2≤2^(2*r) := by
    calc M^2≤(2^r)^2 := Nat.pow_le_pow_left hM 2
         _=2^(2*r) := by rw [←pow_mul]; congr 1; omega
  have htw : 2*M≤2^(r+1) := by
    calc 2*M≤2*2^r := Nat.mul_le_mul_left 2 hM
         _=2^(r+1) := by rw [pow_succ]; omega
  exact ⟨(Nat.size_le_size hsq).trans (by rw [Nat.size_pow]),(Nat.size_le_size htw).trans (by rw [Nat.size_pow])⟩

theorem iteration_cost (n L S M r : ℕ) (hn : n≤S) (hL : L≤S) (hM : M≤2^r) :
    RamExtractionStep.cost n L M≤1024*(r+1)*(S+1)^2 := by
  have hs := (size_bounds M r hM).1
  have hlarge : RamExtractionStep.cost n L M≤
      (200*S+204)*S+122*S+16*(S+1)+(36*(2*r+1)+256)*S+36*(2*r+1)+340 := by
    dsimp only [RamExtractionStep.cost]
    gcongr <;> omega
  have hp : 0≤r*S^2 := Nat.zero_le _
  nlinarith only [hlarge,hp,Nat.zero_le (r*S)]

/-- Every extraction loop and the complete certificate writer admit one
polynomial time bound in the LP size and initial rational bit height. -/
theorem cost_bound (n L S M r : ℕ) (hn : n≤S) (hL : L≤S) (hn2 : n*n≤S)
    (hc : 1+(n*n)*(L*(n*n))≤S) (hM : M≤2^r) :
    RamShortExtraction.cost n L M≤time S r := by
  have hi := iteration_cost n L S M r hn hL hM
  have hQ : budget n L≤S+1 := by dsimp only [budget]; omega
  have hs := (size_bounds M r hM).2
  have hinner : RamAllCommodities.innerCost n L M≤
      (1024*(r+1)*(S+1)^2+12)*(S+1)+10 := by
    dsimp only [RamAllCommodities.innerCost]
    exact Nat.add_le_add_right (Nat.mul_le_mul (by omega) hQ) 10
  have hout : RamShortExtraction.outputLength n L≤3+S*(S+1)*(S+4) := by
    dsimp only [RamShortExtraction.outputLength]
    exact Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul hn2 hQ) (by omega)) 3
  have houter := Nat.mul_le_mul (Nat.add_le_add_right hinner 26) hn2
  have hupper : RamShortExtraction.cost n L M≤16+36*(r+2)+53+
      (((1024*(r+1)*(S+1)^2+12)*(S+1)+10+26)*S+6)+13*(3+S*(S+1)*(S+4))+11 := by
    dsimp only [RamShortExtraction.cost]
    omega
  have hp : (S+1)^4≤(S+1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hm := Nat.mul_le_mul_left (r+1) hp
  have hc' : RamShortExtraction.cost n L M≤4096*(r+1)*(S+1)^4 := by
    nlinarith only [hupper,Nat.zero_le (r*S^4),Nat.zero_le (r*S^3),Nat.zero_le (r*S^2),
      Nat.zero_le (r*S),Nat.zero_le (S^4),Nat.zero_le (S^3),Nat.zero_le (S^2)]
  exact hc'.trans (by simpa only [time,Nat.mul_assoc] using Nat.mul_le_mul_left 4096 hm)

end Lax455465Proofs.RamShortExtractionBounds
