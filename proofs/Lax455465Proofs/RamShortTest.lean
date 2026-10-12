import Lax455465Proofs.RamLpRationalRead
import Lax455465Proofs.RamUnsignedScalar
import Lax455465Proofs.ShortLayerSelection

namespace Lax455465Proofs.RamShortTest
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamUnsignedScalar
open scoped NNRat

/-- Compare by integer cross-products, without introducing a new rational
normalization or any approximation to the stopping threshold. -/
def command : Com :=
  .seq (.assign "short.scale" (.mul (.mul (.lit 4) (.var "lp.n")) (.var "short.layer")))
  (.seq (.assign "short.left" (.mul (.var "short.maximum.n") (.var "rat.d")))
  (.seq (.assign "short.right" (.mul (.mul (.var "short.scale") (.var "rat.n")) (.var "short.maximum.d")))
    (.ite (.lt (.var "short.right") (.var "short.left"))
      (.assign "find.ok" (.lit 0)) (.assign "find.ok" (.lit 1)))))

theorem cross_products (n L : ℕ) (R f : ℚ≥0) :
    (R : ℚ) ≤ 4*n*L*(f : ℚ) ↔ R.num*f.den ≤ 4*n*L*f.num*R.den := by
  have hR : (R : ℚ)=(R.num : ℚ)/R.den := by
    exact (congrArg (fun q : ℚ≥0 => (q : ℚ)) (NNRat.num_div_den R)).symm
  have hf : (f : ℚ)=(f.num : ℚ)/f.den := by
    exact (congrArg (fun q : ℚ≥0 => (q : ℚ)) (NNRat.num_div_den f)).symm
  have hdR : (0 : ℚ)<R.den := by exact_mod_cast R.den_pos
  have hdf : (0 : ℚ)<f.den := by exact_mod_cast f.den_pos
  rw [hR,hf,←mul_div_assoc,div_le_div_iff₀ hdR hdf]
  norm_cast

def space (n L M : ℕ) : ℕ := n+L+4*n+(4*n*L+1)*(M+1)^2+10

theorem command_spec (B M n L : ℕ) (R f : ℚ≥0)
    (hB : space n L M < B)
    (hRn : R.num ≤ M) (hRd : R.den ≤ M) (hfn : f.num ≤ M) (hfd : f.den ≤ M) :
    Spec B (fun σ => σ.vars "lp.n"=n ∧ σ.vars "short.layer"=L ∧
      Stored "short.maximum" R σ ∧ FractionOutput (f : ℚ) σ) command
      (fun _ τ => τ.vars "find.ok"=if (R : ℚ) ≤ 4*n*L*(f : ℚ) then 1 else 0) 24 := by
  have hM : M ≤ (M+1)^2 := by nlinarith
  have hRfd : R.num*f.den ≤ (M+1)^2 := by
    have hh := Nat.mul_le_mul hRn hfd
    nlinarith only [hh]
  have hff : f.num*R.den ≤ (M+1)^2 := by
    have hh := Nat.mul_le_mul hfn hRd
    nlinarith only [hh]
  have hproduct : 4*n*L*f.num*R.den ≤ (4*n*L+1)*(M+1)^2 := by
    have hh := Nat.mul_le_mul_left (4*n*L) hff
    nlinarith only [hh]
  have hprefix : 4*n*L*f.num ≤ (4*n*L+1)*(M+1)^2 := by
    have hh := Nat.mul_le_mul_left (4*n*L) (hfn.trans hM)
    nlinarith only [hh]
  have hscale : 4*n*L ≤ (4*n*L+1)*(M+1)^2 := by
    have hh := Nat.mul_le_mul_left (4*n*L+1) (show 1 ≤ (M+1)^2 by nlinarith)
    omega
  have hunit : (M+1)^2 ≤ (4*n*L+1)*(M+1)^2 := by
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hsmall : 4<B ∧ n<B ∧ L<B ∧ 4*n<B ∧ 4*n*L<B ∧
      R.num<B ∧ R.den<B ∧ f.num<B ∧ f.den<B ∧ R.num*f.den<B ∧
      4*n*L*f.num<B ∧ 4*n*L*f.num*R.den<B := by
    dsimp only [space] at hB
    omega
  rcases hsmall with ⟨h4,hn,hL,h4n,h4nL,hRnB,hRdB,hfnB,hfdB,hleft,hrightPart,hright⟩
  have hcmp := cross_products n L R f
  rintro σ ⟨hnσ,hLσ,hRσ,hfσ⟩
  rcases hRσ with ⟨hRnσ,hRdσ⟩
  have hfnσ : σ.vars "rat.n"=f.num := by simpa only [NNRat.natAbs_num_coe] using hfσ.2.1
  have hfdσ : σ.vars "rat.d"=f.den := by simpa only [NNRat.den_coe] using hfσ.2.2.1
  run_vcg
  all_goals simp_all [Stored]
  all_goals split_ifs <;> omega

end Lax455465Proofs.RamShortTest
