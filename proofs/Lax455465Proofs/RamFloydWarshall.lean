import Lax455465Proofs.RamMetricPivot
import Lax455465Proofs.RamArrayCopy

namespace Lax455465Proofs.RamFloydWarshall

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState MetricMatrix
open scoped NNRat

def step : Com := .seq RamMetricPivot.command
  (.seq (RamArrayCopy.command "metric.new" "metric.old" "metric.words")
    (.assign "metric.p" (.add (.var "metric.p") (.lit 1))))

def command : Com := .seq (.assign "metric.words" (.mul (.lit 2) (.var "metric.n2")))
  (.seq (.assign "metric.p" (.lit 0))
    (.while (.lt (.var "metric.p") (.var "metric.n")) step))

def Invariant {n : ℕ} (d : Matrix n) (σ : Env) : Prop :=
  σ.vars "metric.n" = n ∧ σ.vars "metric.n2" = n*n ∧ σ.vars "metric.words" = 2*(n*n) ∧
    σ.vars "metric.p" ≤ n ∧ Prefix (RamUnsignedBuffer.encode (values (afterPivots d (σ.vars "metric.p")))) "metric.old" σ ∧
    2*(n*n) ≤ (σ.arrs "metric.old").length ∧ 2*(n*n) < (σ.arrs "metric.new").length

theorem step_spec (B H : ℕ) {n : ℕ} (d : Matrix n)
    (hB : 2*(2*H)^2+3 < B) (hn : n < B) (hn2 : n*n < B) (hindex : 2*(n*n)+2 < B)
    (hnum : ∀ k ≤ n, ∀ u v, (afterPivots d k u v).num ≤ H)
    (hden : ∀ k ≤ n, ∀ u v, (afterPivots d k u v).den ≤ H)
    (hsnum : ∀ k, ∀ hk : k < n, ∀ u v,
      (afterPivots d k u ⟨k,hk⟩+afterPivots d k ⟨k,hk⟩ v).num ≤ 2*H)
    (hsden : ∀ k, ∀ hk : k < n, ∀ u v,
      (afterPivots d k u ⟨k,hk⟩+afterPivots d k ⟨k,hk⟩ v).den ≤ 2*H) :
    Spec B (fun σ => Invariant d σ ∧ σ.vars "metric.p" < n) step
      (fun σ τ => Invariant d τ ∧ τ.vars "metric.p" = σ.vars "metric.p"+1)
      ((36*(H*H).size+288)*(n*n)+18) := by
  rintro σ ⟨⟨hN,hN2,hwords,hp,hsource,hOldRoom,hNewRoom⟩,hlt⟩
  let k := σ.vars "metric.p"
  have hk : k < n := hlt
  let p : Fin n := ⟨k,hk⟩
  let current := afterPivots d k
  let next := MetricMatrix.step current p
  have hnext : next = afterPivots d (k+1) := (prefix_succ d k hk).symm
  obtain ⟨ν,rpivot,ppivot⟩ := RamMetricPivot.command_spec B H current p hB hn hn2 hindex
    (hnum k hp) (hden k hp) (hsnum k hk) (hsden k hk)
    (by intro u v; change (next u v).num ≤ H; rw [hnext]; exact hnum (k+1) (by omega) u v)
    (by intro u v; change (next u v).den ≤ H; rw [hnext]; exact hden (k+1) (by omega) u v) σ
      ⟨⟨hN,hN2,rfl,hsource⟩,hNewRoom⟩
  let xs := RamUnsignedBuffer.encode (values next)
  have hxs : xs.length = 2*(n*n) := by simp [xs]
  have hH : H < B := by nlinarith
  have hxwords : ∀ x ∈ xs, x < B := by
    intro x hx
    obtain ⟨q,hq,hxq⟩ := List.mem_flatMap.mp hx
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hq
    have hv : next ((DirectedFlowLP.edgeIndex n).symm e).1 ((DirectedFlowLP.edgeIndex n).symm e).2 =
      afterPivots d (k+1) ((DirectedFlowLP.edgeIndex n).symm e).1 ((DirectedFlowLP.edgeIndex n).symm e).2 := by rw [hnext]
    simp only [Lax455465.RationalEncoding.encodeRational,List.mem_cons,List.not_mem_nil,or_false] at hxq
    rcases hxq with rfl | rfl
    · have hbnd : (next ((DirectedFlowLP.edgeIndex n).symm e).1 ((DirectedFlowLP.edgeIndex n).symm e).2).num ≤ H := by
        rw [hv]; exact hnum (k+1) (by omega) _ _
      exact hbnd.trans_lt hH
    · have hbnd : (next ((DirectedFlowLP.edgeIndex n).symm e).1 ((DirectedFlowLP.edgeIndex n).symm e).2).den ≤ H := by
        rw [hv]; exact hden (k+1) (by omega) _ _
      exact hbnd.trans_lt hH
  have hwordsν : ν.vars "metric.words" = xs.length := by
    simpa only [hxs] using (rpivot.frame_var "metric.words" (by decide)).trans hwords
  have hOldRoomν : xs.length ≤ (ν.arrs "metric.old").length := by
    rw [hxs,RamFrames.run_array_length rpivot "metric.old"]; exact hOldRoom
  obtain ⟨μ,rcopy,pcopy⟩ := RamArrayCopy.command_spec B xs "metric.new" "metric.old" "metric.words"
    (by nlinarith) (by rw [hxs]; omega) hxwords (by decide) (by decide) ν
      ⟨ppivot.2.1,hwordsν,hOldRoomν⟩
  have rp := rpivot.seq rcopy
  have hpμ : μ.vars "metric.p" = k := (rp.frame_var "metric.p" (by decide)).trans rfl
  have rnext : Run B (.assign "metric.p" (.add (.var "metric.p") (.lit 1))) μ
      (μ.setVar "metric.p" (k+1)) 4 := Run.assign
    (evalB_bin (op := .add) (by rw [evalB_var_iff]; exact ⟨hpμ.symm,hpμ ▸ (by omega : k < B)⟩)
      (evalB_lit (by nlinarith)) (by dsimp [Bop.apply]; omega))
  have hNμ : μ.vars "metric.n" = n := (rp.frame_var "metric.n" (by decide)).trans hN
  have hN2μ : μ.vars "metric.n2" = n*n := (rp.frame_var "metric.n2" (by decide)).trans hN2
  have hwordsμ : μ.vars "metric.words" = 2*(n*n) := (rp.frame_var "metric.words" (by decide)).trans hwords
  have hOldRoomμ : 2*(n*n) ≤ (μ.arrs "metric.old").length := by rwa [RamFrames.run_array_length rp "metric.old"]
  have hNewRoomμ : 2*(n*n) < (μ.arrs "metric.new").length := by rwa [RamFrames.run_array_length rp "metric.new"]
  refine ⟨μ.setVar "metric.p" (k+1),(rpivot.seq (rcopy.seq rnext)).mono
    (by simp only [hxs]; ring_nf; omega),?_,?_⟩
  · refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [vars_setVar,String.reduceEq,if_false] using hNμ
    · simpa only [vars_setVar,String.reduceEq,if_false] using hN2μ
    · simpa only [vars_setVar,String.reduceEq,if_false] using hwordsμ
    · simp only [vars_setVar,if_true]; omega
    · simpa only [xs,Prefix,vars_setVar,if_true,arrs_setVar,hnext] using pcopy.2
    · simpa only [arrs_setVar] using hOldRoomμ
    · simpa only [arrs_setVar] using hNewRoomμ
  · simp [k]

/-- The full fixed Floyd–Warshall command processes the n runtime pivots;
it executes n² exact native min-plus updates per pivot and returns the
same distance matrix as the proved mathematical algorithm. -/
theorem command_spec (B H : ℕ) {n : ℕ} (d : Matrix n)
    (hB : 2*(2*H)^2+3 < B) (hn : n < B) (hn2 : n*n < B) (hindex : 2*(n*n)+2 < B)
    (hnum : ∀ k ≤ n, ∀ u v, (afterPivots d k u v).num ≤ H)
    (hden : ∀ k ≤ n, ∀ u v, (afterPivots d k u v).den ≤ H)
    (hsnum : ∀ k, ∀ hk : k < n, ∀ u v,
      (afterPivots d k u ⟨k,hk⟩+afterPivots d k ⟨k,hk⟩ v).num ≤ 2*H)
    (hsden : ∀ k, ∀ hk : k < n, ∀ u v,
      (afterPivots d k u ⟨k,hk⟩+afterPivots d k ⟨k,hk⟩ v).den ≤ 2*H) :
    Spec B (fun σ => σ.vars "metric.n" = n ∧ σ.vars "metric.n2" = n*n ∧
      Prefix (RamUnsignedBuffer.encode (values d)) "metric.old" σ ∧
      2*(n*n) ≤ (σ.arrs "metric.old").length ∧ 2*(n*n) < (σ.arrs "metric.new").length) command
      (fun _ τ => τ.vars "metric.n" = n ∧ τ.vars "metric.n2" = n*n ∧
        Prefix (RamUnsignedBuffer.encode (values (iterate d (List.finRange n)))) "metric.old" τ)
      (n*((36*(H*H).size+288)*(n*n)+22)+10) := by
  have hloop := Spec.forRangeZero "metric.p" "metric.n" (Invariant d) n
    ((36*(H*H).size+288)*(n*n)+18) hn (fun _ h => h.2.2.2.1) (fun _ h => h.1)
    (step_spec B H d hB hn hn2 hindex hnum hden hsnum hsden)
  rintro σ ⟨hN,hN2,hprefix,hOldRoom,hNewRoom⟩
  let ν := σ.setVar "metric.words" (2*(n*n))
  have rwords : Run B (.assign "metric.words" (.mul (.lit 2) (.var "metric.n2"))) σ ν 4 := Run.assign
    (evalB_bin (op := .mul) (evalB_lit (by nlinarith))
      (by rw [evalB_var_iff]; exact ⟨hN2.symm,hN2 ▸ hn2⟩) (by dsimp [Bop.apply]; omega))
  have hinit : Invariant d (ν.setVar "metric.p" 0) := by
    refine ⟨?_,?_,?_,by simp,?_,?_,?_⟩
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hN
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hN2
    · simp [ν]
    · simpa only [Prefix,vars_setVar,if_true,prefix_zero,ν,arrs_setVar] using hprefix
    · simpa only [ν,arrs_setVar] using hOldRoom
    · simpa only [ν,arrs_setVar] using hNewRoom
  obtain ⟨τ,hr,hpost⟩ := hloop ν hinit
  refine ⟨τ,(rwords.seq hr).mono (by ring_nf; omega),hpost.1.1,hpost.1.2.1,?_⟩
  have htake : (List.finRange n).take n = List.finRange n := by
    simpa only [List.length_finRange] using (show (List.finRange n).take (List.finRange n).length = List.finRange n from List.take_length)
  simpa only [hpost.2,afterPivots,htake] using hpost.1.2.2.2.2.1

end Lax455465Proofs.RamFloydWarshall
