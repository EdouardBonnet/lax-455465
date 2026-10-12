import Lax455465Proofs.HopContraction

open scoped BigOperators
namespace Lax455465Proofs.BoundedDistances

abbrev Length (n : ℕ) := Fin n → Fin n → ℚ

/-- A finite walk with an exact hop count and length. Reflexive segments
have no hops; genuine edges have distinct endpoints. -/
inductive Route {n : ℕ} (ell : Length n) : Fin n → Fin n → ℕ → ℚ → Prop
  | refl (v : Fin n) : Route ell v v 0 0
  | edge {u v : Fin n} (hne : u ≠ v) : Route ell u v 1 (ell u v)
  | trans {u v w : Fin n} {a b : ℕ} {x y : ℚ} :
      Route ell u v a x → Route ell v w b y → Route ell u w (a+b) (x+y)

theorem Route.nonnegative {n : ℕ} {ell : Length n} (hell : ∀ u v,0 ≤ ell u v)
    {u v : Fin n} {k : ℕ} {c : ℚ} (h : Route ell u v k c) : 0 ≤ c := by
  induction h with
  | refl => rfl
  | edge => exact hell _ _
  | trans _ _ ih1 ih2 => exact add_nonneg ih1 ih2

theorem Route.reverse {n : ℕ} {ell : Length n} (hsym : ∀ u v,ell u v=ell v u)
    {u v : Fin n} {k : ℕ} {c : ℚ} (h : Route ell u v k c) : Route ell v u k c := by
  induction h with
  | refl v => exact .refl v
  | @edge u v hne => simpa only [hsym v u] using (Route.edge (ell := ell) (Ne.symm hne))
  | trans _ _ ih1 ih2 => simpa only [Nat.add_comm,add_comm] using ih2.trans ih1

/-- Positive per-edge regularization bounds the number of genuine hops. -/
theorem Route.hops_bound {n : ℕ} {ell : Length n} (delta : ℚ)
    (hdelta : ∀ u v,u ≠ v → delta ≤ ell u v)
    {u v : Fin n} {k : ℕ} {c : ℚ} (h : Route ell u v k c) : delta*k ≤ c := by
  induction h with
  | refl => simp
  | edge hne => simpa using hdelta _ _ hne
  | trans _ _ ih1 ih2 => push_cast; nlinarith

/-- Changing to smaller nonnegative edge lengths preserves every route and
can only decrease its exact cost. -/
theorem Route.smaller {n : ℕ} {ell ell' : Length n} (hle : ∀ u v,ell' u v ≤ ell u v)
    {u v : Fin n} {k : ℕ} {c : ℚ} (h : Route ell u v k c) :
    ∃ c' ≤ c,Route ell' u v k c' := by
  induction h with
  | refl v => exact ⟨0,le_rfl,.refl v⟩
  | @edge u v hne => exact ⟨ell' u v,hle u v,.edge hne⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨x,hx,rx⟩ := ih1
    obtain ⟨y,hy,ry⟩ := ih2
    exact ⟨x+y,add_le_add hx hy,rx.trans ry⟩

def candidate {n : ℕ} (ell : Length n) (a : Fin n → ℚ) (v : Fin n) : Option (Fin n) → ℚ
  | none => a v
  | some u => a u+ell u v

def step {n : ℕ} (ell : Length n) (a : Fin n → ℚ) (v : Fin n) : ℚ :=
  Finset.univ.inf' ⟨none,Finset.mem_univ _⟩ (candidate ell a v)

theorem step_le {n : ℕ} (ell : Length n) (a : Fin n → ℚ) (v : Fin n) : step ell a v ≤ a v :=
  Finset.inf'_le (candidate ell a v) (Finset.mem_univ none)

theorem step_edge {n : ℕ} (ell : Length n) (a : Fin n → ℚ) (u v : Fin n) :
    step ell a v ≤ a u+ell u v :=
  Finset.inf'_le (candidate ell a v) (Finset.mem_univ (some u))

theorem step_choice {n : ℕ} (ell : Length n) (a : Fin n → ℚ) (v : Fin n) :
    step ell a v=a v ∨ ∃ u,step ell a v=a u+ell u v := by
  obtain ⟨o,_,ho⟩ := Finset.exists_mem_eq_inf' (show (Finset.univ : Finset (Option (Fin n))).Nonempty from ⟨none,Finset.mem_univ _⟩)
    (candidate ell a v)
  cases o with
  | none => exact Or.inl ho
  | some u => exact Or.inr ⟨u,ho⟩

theorem step_nonnegative {n : ℕ} (ell : Length n) (a : Fin n → ℚ)
    (hell : ∀ u v,0 ≤ ell u v) (ha : ∀ v,0 ≤ a v) (v : Fin n) : 0 ≤ step ell a v := by
  apply Finset.le_inf'
  intro o _
  cases o with
  | none => exact ha v
  | some u => exact add_nonneg (ha u) (hell u v)

def initial {n : ℕ} (T : Finset (Fin n)) (M : ℚ) (v : Fin n) : ℚ := if v∈T then 0 else M

def run {n : ℕ} (ell : Length n) (T : Finset (Fin n)) (M : ℚ) : ℕ → Fin n → ℚ
  | 0 => initial T M
  | k+1 => step ell (run ell T M k)

theorem nonnegative {n : ℕ} (ell : Length n) (T : Finset (Fin n)) (M : ℚ)
    (hell : ∀ u v,0 ≤ ell u v) (hM : 0 ≤ M) (k : ℕ) : ∀ v,0 ≤ run ell T M k v := by
  induction k with
  | zero => intro v; simp only [run,initial]; split_ifs <;> positivity
  | succ k ih => exact step_nonnegative ell _ hell ih

theorem zero_on_set {n : ℕ} (ell : Length n) (T : Finset (Fin n)) (M : ℚ)
    (hell : ∀ u v,0 ≤ ell u v) (hM : 0 ≤ M) (k : ℕ) : ∀ v∈T,run ell T M k v=0 := by
  induction k with
  | zero => intro v hv; simp [run,initial,hv]
  | succ k ih =>
    intro v hv
    apply le_antisymm
    · change step ell (run ell T M k) v ≤ 0
      exact (step_le ell (run ell T M k) v).trans_eq (ih v hv)
    · exact nonnegative ell T M hell hM _ v

/-- Any value strictly below the cap has an actual route from T with no
more hops than the relaxation budget. The cap supplies no fictitious path. -/
theorem route_of_lt {n : ℕ} (ell : Length n) (T : Finset (Fin n)) (M : ℚ)
    (hell : ∀ u v,0 ≤ ell u v) (k : ℕ) (v : Fin n) (hv : run ell T M k v < M) :
    ∃ s∈T,∃ h ≤ k,∃ c ≤ run ell T M k v,Route ell s v h c := by
  induction k generalizing v with
  | zero =>
    have hmem : v∈T := by by_contra hn; simp [run,initial,hn] at hv
    exact ⟨v,hmem,0,le_rfl,0,by simp [run,initial,hmem],.refl v⟩
  | succ k ih =>
    rcases step_choice ell (run ell T M k) v with he | ⟨u,he⟩
    · have he' : run ell T M (k+1) v=run ell T M k v := he
      obtain ⟨s,hs,h,hh,c,hc,hr⟩ := ih v (by rwa [←he'])
      exact ⟨s,hs,h,by omega,c,by simpa only [he'] using hc,hr⟩
    · have he' : run ell T M (k+1) v=run ell T M k u+ell u v := he
      obtain ⟨s,hs,h,hh,c,hc,hr⟩ := ih u (by rw [he'] at hv; linarith [hell u v])
      by_cases huv : u=v
      · subst u
        exact ⟨s,hs,h,by omega,c,by rw [he']; linarith [hell v v],hr⟩
      · exact ⟨s,hs,h+1,by omega,c+ell u v,by rw [he']; linarith,hr.trans (.edge huv)⟩

end Lax455465Proofs.BoundedDistances
