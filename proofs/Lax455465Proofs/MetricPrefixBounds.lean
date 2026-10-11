import Lax455465Proofs.MetricHeight
import Lax455465Proofs.MetricMatrix

namespace Lax455465Proofs.MetricPrefixBounds

open MetricMatrix
open scoped NNRat

theorem coordinate_height {n : ℕ} (d : Matrix n) (w k : ℕ)
    (hnum : ∀ u v, (d u v).num ≤ 2^w) (hden : ∀ u v, (d u v).den ≤ 2^w) :
    ∀ u v, LpInputSize.Height (2^(w*(n*n+1))) ((afterPivots d k u v : ℚ≥0) : ℚ) := by
  have hcoenum : ∀ u v, (rational d u v).num.natAbs ≤ 2^w := by
    simpa only [rational,NNRat.natAbs_num_coe] using hnum
  have hcoeden : ∀ u v, (rational d u v).den ≤ 2^w := by
    simpa only [rational,NNRat.den_coe] using hden
  have hh := MetricHeight.iterate_word_height (rational d) ((List.finRange n).take k) w
    (fun u v => (d u v).property) hcoenum hcoeden
  intro u v
  have heq := congrFun (congrFun (rational_iterate d ((List.finRange n).take k)) u) v
  simpa only [←heq,afterPivots,rational] using hh u v

theorem candidate_height {n : ℕ} (d : Matrix n) (w k : ℕ)
    (hnum : ∀ u v, (d u v).num ≤ 2^w) (hden : ∀ u v, (d u v).den ≤ 2^w)
    (u p v : Fin n) :
    LpInputSize.Height (2*2^(w*(n*n+1)))
      ((afterPivots d k u p+afterPivots d k p v : ℚ≥0) : ℚ) := by
  have hcoenum : ∀ u v, (rational d u v).num.natAbs ≤ 2^w := by
    simpa only [rational,NNRat.natAbs_num_coe] using hnum
  have hcoeden : ∀ u v, (rational d u v).den ≤ 2^w := by
    simpa only [rational,NNRat.den_coe] using hden
  have hh := MetricHeight.candidate_word_height (rational d) ((List.finRange n).take k) w
    (fun u v => (d u v).property) hcoenum hcoeden u p v
  have heq := rational_iterate d ((List.finRange n).take k)
  have hleft := congrFun (congrFun heq u) p
  have hright := congrFun (congrFun heq p) v
  simpa only [←hleft,←hright,afterPivots,rational,NNRat.coe_add] using hh

end Lax455465Proofs.MetricPrefixBounds
