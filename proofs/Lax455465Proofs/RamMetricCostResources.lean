import Lax455465Proofs.RamMetricCost
import Lax455465Proofs.RamHostBounds

namespace Lax455465Proofs.RamMetricCostResources

open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding

noncomputable def heightBound (metricWord : Polynomial ℕ) : Polynomial ℕ :=
  (Polynomial.X+metricWord+Polynomial.C 1)*(Polynomial.X^2+Polynomial.C 1)

noncomputable def timeBound (metricWord : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 1000*heightBound metricWord*(Polynomial.X+Polynomial.C 1)^2+Polynomial.C 24

noncomputable def wordBound (metricWord : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 2*heightBound metricWord+Polynomial.C 2*Polynomial.X^2+Polynomial.C 20

theorem height_bound (metricWord : Polynomial ℕ) {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) :
    MetricCostHeight.exponent n (bitSize (encodeInput kind I)) (metricWord.eval (bitSize (encodeInput kind I))) ≤
      (heightBound metricWord).eval (bitSize (encodeInput kind I)) := by
  let L := bitSize (encodeInput kind I)
  have hn : n ≤ L := LpInputSize.input_dimension kind I
  have hnn : n*n+1 ≤ L^2+1 := by nlinarith
  simp only [heightBound,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_pow]
  dsimp only [MetricCostHeight.exponent]
  have hh := Nat.mul_le_mul_left (L+metricWord.eval L+1) hnn
  dsimp only [L] at hh
  nlinarith

theorem time_bound (metricWord : Polynomial ℕ) {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) :
    (144*MetricCostHeight.exponent n (bitSize (encodeInput kind I))
      (metricWord.eval (bitSize (encodeInput kind I)))+296)*(n*n)+22 ≤
      (timeBound metricWord).eval (bitSize (encodeInput kind I)) := by
  let L := bitSize (encodeInput kind I)
  let H := (heightBound metricWord).eval L
  have hn : n ≤ L := LpInputSize.input_dimension kind I
  have hv := height_bound metricWord kind I
  have hpos : 1 ≤ H := by
    simp only [H,heightBound,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_pow]
    nlinarith
  have hcoefficient : 144*MetricCostHeight.exponent n L (metricWord.eval L)+296 ≤ 1000*H := by
    dsimp only [L,H] at hv ⊢
    nlinarith
  have hnn : n*n ≤ (L+1)^2 := by nlinarith
  have hh := Nat.mul_le_mul hcoefficient hnn
  simp only [timeBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  dsimp only [L,H] at hh ⊢
  omega

theorem host_bound (metricWord : Polynomial ℕ) {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) (W : ℕ)
    (hW : (wordBound metricWord).eval (bitSize (encodeInput kind I)) ≤ W) :
    2*(2^(MetricCostHeight.exponent n (bitSize (encodeInput kind I))
      (metricWord.eval (bitSize (encodeInput kind I)))))^2+3 < 2^W ∧ 2*(n*n)+2 < 2^W := by
  let L := bitSize (encodeInput kind I)
  let V := MetricCostHeight.exponent n L (metricWord.eval L)
  have hn : n ≤ L := LpInputSize.input_dimension kind I
  have hv := height_bound metricWord kind I
  have hwidth : RamHostBounds.sufficient V 0 0 (2*(n*n)+3) ≤ W := by
    simp only [wordBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X] at hW
    dsimp only [RamHostBounds.sufficient,V,L]
    have hnn : n*n ≤ L^2 := by nlinarith
    dsimp only [L] at hnn hv
    omega
  obtain ⟨hB,hT,hC,hL⟩ := RamHostBounds.sufficient_bounds V 0 0 (2*(n*n)+3) W hwidth
  exact ⟨hB,by omega⟩

end Lax455465Proofs.RamMetricCostResources
