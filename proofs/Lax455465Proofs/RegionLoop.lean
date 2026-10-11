import Lax455465Proofs.RegionSelection
import Lax455465Proofs.RegionFrontier
import Lax455465Proofs.LargeBallRounding

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lax455465Proofs.RegionLoop

open Lax455465.RationalEncoding RegionVolume RegionCharging RegionSelection RationalDistances

/-- Residual arrays are determined by the active vertex set. -/
def weights {n : ℕ} (I : RationalInstance n) (active : Finset (Fin n)) : Fin n → ℚ :=
  fun v => if v ∈ active then (I.weight v : ℚ) else 0

def capacity {n : ℕ} (I : RationalInstance n) (active : Finset (Fin n)) : Matrix n :=
  fun u v => if u ∈ active ∧ v ∈ active then (I.capacity u v : ℚ) else 0

structure Region (n : ℕ) where
  root : Fin n
  radius : ℚ
  outward : Bool

def Region.ball {n : ℕ} (R : Region n) (d : Distance n) : Finset (Fin n) :=
  if R.outward then RegionCharging.ball (d R.root) R.radius
  else RegionCharging.ball (fun v => d v R.root) R.radius

def chooseDirection {n : ℕ} (I : RationalInstance n) (d : Distance n)
    (active : Finset (Fin n)) (root : Fin n) : ℚ → Bool :=
  direction (weights I active) (d root) (fun v => d v root)

inductive Result (n : ℕ) where
  | large : Region n → Result n
  | regions : List (Region n) → Result n

/-- A bounded deterministic loop. The fuel bound will be discharged by the
strict decrease of the positive-weight support, rather than by an oracle. -/
def run {n : ℕ} (I : RationalInstance n) (d : Distance n) (seed delta : ℚ) (p : ℕ) :
    ℕ → Finset (Fin n) → Option (Result n)
  | 0, active =>
    if chooseRoot (weights I active) = none then some (.regions []) else none
  | fuel + 1, active =>
    match chooseRoot (weights I active) with
    | none => some (.regions [])
    | some root =>
      match RegionSearch.search (capacity I active) d (d root) (fun v => d v root)
        seed delta p (chooseDirection I d active root) with
      | none => none
      | some r =>
        let R : Region n := ⟨root, r, chooseDirection I d active root r⟩
        if (2 / 3 : ℚ) * LargeBallRounding.total I ≤ ∑ v ∈ R.ball d, weights I active v then
          some (.large R)
        else
          (run I d seed delta p fuel (active \ R.ball d)).map fun result =>
            match result with
            | .large T => .large T
            | .regions rest => .regions (R :: rest)

/-- A removed small ball has the actual search guarantee at its selected orientation. -/
def StepGood {n : ℕ} (I : RationalInstance n) (d : Distance n) (seed delta : ℚ) (p : ℕ)
    (active : Finset (Fin n)) (R : Region n) : Prop :=
  0 < weights I active R.root ∧ 0 < R.radius ∧ R.radius ≤ delta ∧
  R.outward = chooseDirection I d active R.root R.radius ∧
  RegionSearch.Good (capacity I active) d (d R.root) (fun v => d v R.root)
    seed (RegionSearch.slope (RegionBudget.steps p) delta) (chooseDirection I d active R.root) R.radius ∧
  (∑ v ∈ R.ball d, weights I active v) < (2 / 3 : ℚ) * LargeBallRounding.total I

def ValidHistory {n : ℕ} (I : RationalInstance n) (d : Distance n) (seed delta : ℚ) (p : ℕ) :
    Finset (Fin n) → List (Region n) → Prop
  | active, [] => (support (weights I active)).card = 0
  | active, R :: rest => StepGood I d seed delta p active R ∧
      ValidHistory I d seed delta p (active \ R.ball d) rest

def LargeGood {n : ℕ} (I : RationalInstance n) (d : Distance n) (delta : ℚ) (R : Region n) : Prop :=
  0 < R.radius ∧ R.radius ≤ delta ∧
  (2 / 3 : ℚ) * LargeBallRounding.total I ≤ LargeBallRounding.mass I (RegionCharging.ball (d R.root) R.radius) ∧
  (2 / 3 : ℚ) * LargeBallRounding.total I ≤ LargeBallRounding.mass I (RegionCharging.ball (fun v => d v R.root) R.radius)

theorem weights_nonnegative {n : ℕ} (I : RationalInstance n) (active : Finset (Fin n)) (v : Fin n) :
    0 ≤ weights I active v := by unfold weights; split_ifs <;> positivity

theorem weights_le {n : ℕ} (I : RationalInstance n) (active : Finset (Fin n)) (v : Fin n) :
    weights I active v ≤ (I.weight v : ℚ) := by
  unfold weights
  split_ifs
  · exact le_rfl
  · exact NNRat.coe_nonneg _

theorem capacity_nonnegative {n : ℕ} (I : RationalInstance n) (active : Finset (Fin n)) :
    ∀ u v, 0 ≤ capacity I active u v := by
  intro u v
  unfold capacity
  split_ifs <;> positivity

theorem residual_cost_le {n : ℕ} (I : RationalInstance n) (d : Distance n)
    (active : Finset (Fin n)) (hd : Nonnegative d) :
    weight (capacity I active) d ≤ weight (fun u v => (I.capacity u v : ℚ)) d := by
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  apply mul_le_mul_of_nonneg_right _ (hd u v)
  unfold capacity
  split_ifs
  · exact le_rfl
  · exact NNRat.coe_nonneg _

theorem weights_remove {n : ℕ} (I : RationalInstance n) (active S : Finset (Fin n)) :
    weights I (active \ S) = eraseWeights (weights I active) S := by
  funext v
  simp only [weights, eraseWeights, Finset.mem_sdiff]
  split_ifs <;> (try simp_all)

theorem capacity_remove {n : ℕ} (I : RationalInstance n) (active S : Finset (Fin n)) :
    capacity I (active \ S) = erase (capacity I active) S := by
  funext u v
  simp only [capacity, erase, Finset.mem_sdiff]
  split_ifs <;> (try simp_all)

theorem root_none_iff {n : ℕ} (w : Fin n → ℚ) :
    chooseRoot w = none ↔ (support w).card = 0 := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨root, hr, _⟩ := root_correct w (by omega)
    rw [h] at hr
    cases hr
  · intro h
    unfold chooseRoot
    apply List.find?_eq_none.mpr
    intro v _
    simp only [decide_eq_true_eq]
    intro hv
    have hmem : v ∈ support w := by simp [support, hv]
    have hpos := Finset.card_pos.mpr ⟨v, hmem⟩
    omega

/-- The deterministic loop terminates within its support budget. Every
returned history consists of successful small-ball steps and exhausts all
positive-weight vertices; the alternative is an actual large-ball witness. -/
theorem run_correct {n : ℕ} (I : RationalInstance n) (d : Distance n)
    (seed delta : ℚ) (p fuel : ℕ)
    (hd : Nonnegative d) (hdiag : ∀ v, d v v = 0)
    (htri : ∀ u v w, d u w ≤ d u v + d v w)
    (hseed : 0 < seed) (hdelta : 0 < delta) (hp : 0 < p)
    (hcost : weight (fun u v => (I.capacity u v : ℚ)) d ≤ (p : ℚ) * seed)
    (active : Finset (Fin n)) (hfuel : (support (weights I active)).card ≤ fuel) :
    ∃ result, run I d seed delta p fuel active = some result ∧
      match result with
      | .large R => LargeGood I d delta R
      | .regions history => ValidHistory I d seed delta p active history ∧
          history.length ≤ (support (weights I active)).card := by
  induction fuel generalizing active with
  | zero =>
    have hz : (support (weights I active)).card = 0 := by omega
    have hn := (root_none_iff _).mpr hz
    refine ⟨.regions [], ?_, hz, ?_⟩
    · simp only [run, hn, ↓reduceIte]
    · simp
  | succ fuel ih =>
    cases hr : chooseRoot (weights I active) with
    | none =>
      refine ⟨.regions [], ?_, (root_none_iff _).mp hr, ?_⟩
      · simp only [run, hr]
      · simp
    | some root =>
      have hroot : 0 < weights I active root := by
        simpa only [decide_eq_true_eq] using List.find?_some hr
      obtain ⟨r, hs, _, _, hgood⟩ := RegionSearch.search_correct (capacity I active) d
        (d root) (fun v => d v root) seed delta p (chooseDirection I d active root)
        (capacity_nonnegative I active) hd hseed hdelta hp
        ((residual_cost_le I d active hd).trans hcost)
        (fun u v => by linarith [htri root u v])
        (fun u v => by linarith [htri v u root])
      let R : Region n := ⟨root, r, chooseDirection I d active root r⟩
      have hball : R.ball d = chosenBall (d root) (fun v => d v root)
          (chooseDirection I d active root) r := rfl
      have hrad := RegionSearch.search_radius (capacity I active) d (d root) (fun v => d v root)
        seed delta p (chooseDirection I d active root) r hdelta.le hs
      by_cases hlarge : (2 / 3 : ℚ) * LargeBallRounding.total I ≤ ∑ v ∈ R.ball d, weights I active v
      · have hmin : (2 / 3 : ℚ) * LargeBallRounding.total I ≤
            min (ballMass (weights I active) (d root) r)
              (ballMass (weights I active) (fun v => d v root) r) := by
          rw [← chosen_mass]
          simpa only [chooseDirection, hball] using hlarge
        have hout := (le_min_iff.mp hmin).1
        have hin := (le_min_iff.mp hmin).2
        have hmassOut : ballMass (weights I active) (d root) r ≤
            LargeBallRounding.mass I (RegionCharging.ball (d root) r) :=
          Finset.sum_le_sum fun v _ => weights_le I active v
        have hmassIn : ballMass (weights I active) (fun v => d v root) r ≤
            LargeBallRounding.mass I (RegionCharging.ball (fun v => d v root) r) :=
          Finset.sum_le_sum fun v _ => weights_le I active v
        refine ⟨.large R, ?_, hrad.1, hrad.2, hout.trans hmassOut, hin.trans hmassIn⟩
        dsimp only [R] at hlarge ⊢
        simp only [run, hr, hs, if_pos hlarge]
      · have hmem : root ∈ R.ball d := by
          rw [hball]
          exact root_mem_chosen _ _ _ r root (hdiag root) (hdiag root) hrad.1
        have hprogress : (support (weights I (active \ R.ball d))).card <
            (support (weights I active)).card := by
          rw [weights_remove]
          exact support_decreases _ _ root hroot hmem
        have hstep : StepGood I d seed delta p active R :=
          ⟨hroot, hrad.1, hrad.2, rfl, hgood, lt_of_not_ge hlarge⟩
        obtain ⟨result, hrun, hvalid⟩ := ih (active \ R.ball d) (by omega)
        cases result with
        | large T =>
          refine ⟨.large T, ?_, hvalid⟩
          dsimp only [R] at hlarge hrun ⊢
          simp only [run, hr, hs, if_neg hlarge, hrun, Option.map_some]
        | regions rest =>
          refine ⟨.regions (R :: rest), ?_, ⟨hstep, hvalid.1⟩, ?_⟩
          · dsimp only [R] at hlarge hrun ⊢
            simp only [run, hr, hs, if_neg hlarge, hrun, Option.map_some]
          · have hlen := hvalid.2
            simp only [List.length_cons]
            omega

end Lax455465Proofs.RegionLoop
