import Lax759944.RamPolytime
import Mathlib.Tactic

namespace Lax455465Proofs.SparseRam

open Lax808846.Ram

/-- A chronological stack of virtual memory writes, newest first. -/
abbrev Memory := List (ℕ × ℕ)

def lookup : Memory → ℕ → ℕ
  | [], _ => 0
  | (a, v) :: rest, b => if b = a then v else lookup rest b

def write (w : ℕ) (m : Memory) (a v : ℕ) : Memory := (a % 2 ^ w, v % 2 ^ w) :: m

/-- Sparse updates preserve the registered machine's exact modulo-address
and modulo-value semantics, including overwriting earlier writes. -/
theorem lookup_write (w : ℕ) (m : Memory) (a v : ℕ) :
    lookup (write w m a v) = setCell w (lookup m) a v := by
  funext b
  rfl

structure SparseState where
  pc : ℕ
  memory : Memory
  input : List ℕ
  inp : List ℕ
  out : List ℕ

def expand (s : SparseState) : State := ⟨s.pc, lookup s.memory, s.input, s.inp, s.out⟩

def assign (w : ℕ) (s : SparseState) (a v : ℕ) : SparseState :=
  { s with pc := s.pc + 1, memory := write w s.memory a v }

def effect (w : ℕ) : Instr → SparseState → Option SparseState
  | .set a n, s => some (assign w s a n)
  | .load a b, s => some (assign w s a (lookup s.memory (lookup s.memory (b % 2 ^ w) % 2 ^ w)))
  | .store a b, s => some (assign w s (lookup s.memory (a % 2 ^ w)) (lookup s.memory (b % 2 ^ w)))
  | .add a b c, s => some (assign w s a (lookup s.memory (b % 2 ^ w) + lookup s.memory (c % 2 ^ w)))
  | .sub a b c, s => some (assign w s a (lookup s.memory (b % 2 ^ w) - lookup s.memory (c % 2 ^ w)))
  | .mul a b c, s => some (assign w s a (lookup s.memory (b % 2 ^ w) * lookup s.memory (c % 2 ^ w)))
  | .div a b c, s => some (assign w s a (lookup s.memory (b % 2 ^ w) / lookup s.memory (c % 2 ^ w)))
  | .and a b c, s => some (assign w s a (Nat.land (lookup s.memory (b % 2 ^ w)) (lookup s.memory (c % 2 ^ w))))
  | .shiftl a b c, s => some (assign w s a (lookup s.memory (b % 2 ^ w) * 2 ^ lookup s.memory (c % 2 ^ w)))
  | .not a b, s => some (assign w s a (2 ^ w - 1 - lookup s.memory (b % 2 ^ w)))
  | .jump l, s => some { s with pc := l }
  | .jzero a l, s => some { s with pc := if lookup s.memory (a % 2 ^ w) = 0 then l else s.pc + 1 }
  | .jeof l, s => some { s with pc := if s.inp.isEmpty then l else s.pc + 1 }
  | .inputLength a, s => some (assign w s a s.input.length)
  | .inputLoad a b, s => some (assign w s a (s.input[lookup s.memory (b % 2 ^ w) % 2 ^ w]?.getD 0))
  | .halt, _ => none
  | .read a, s => s.inp.head?.map fun v => { assign w s a v with inp := s.inp.tail }
  | .write a, s => some { s with pc := s.pc + 1, out := s.out ++ [lookup s.memory (a % 2 ^ w) % 2 ^ w] }

/-- One sparse virtual instruction exactly simulates one registered RAM
instruction. Virtual memory is initialized independently of the host. -/
theorem effect_expand (w : ℕ) (i : Instr) (s : SparseState) :
    (effect w i s).map expand = i.effect w (expand s) := by
  cases i <;> simp only [effect, Instr.effect, assign, expand, lookup_write, Option.map_some, Option.map_none] <;> try rfl
  rename_i a
  cases s.inp.head? <;> simp only [Option.map_some, Option.map_none, expand, lookup_write]

def step (w : ℕ) (p : Program) (s : SparseState) : Option SparseState :=
  p[s.pc]?.bind fun i => effect w i s

theorem step_expand (w : ℕ) (p : Program) (s : SparseState) :
    (step w p s).map expand = Lax808846.Ram.step w p (expand s) := by
  change (p[s.pc]?.bind fun i => effect w i s).map expand =
    p[s.pc]?.bind fun i => i.effect w (expand s)
  cases hi : p[s.pc]? with
  | none => rfl
  | some i => exact effect_expand w i s

def run (w : ℕ) (p : Program) : ℕ → SparseState → Option SparseState
  | 0, s => some s
  | t + 1, s => (step w p s).bind (run w p t)

def init (x : List ℕ) : SparseState := ⟨0, [], x, x, []⟩

theorem init_expand (x : List ℕ) : expand (init x) = initState x := rfl

theorem run_expand (w : ℕ) (p : Program) (t : ℕ) (s : SparseState) :
    (run w p t s).map expand = Lax808846.Ram.run w p t (expand s) := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
    rw [run, Lax808846.Ram.run]
    have he := step_expand w p s
    cases hs : step w p s with
    | none =>
      have hn : Lax808846.Ram.step w p (expand s) = none := by
        simpa only [hs, Option.map_none] using he.symm
      simp only [hn, Option.bind_none, Option.map_none]
    | some τ =>
      have hn : Lax808846.Ram.step w p (expand s) = some (expand τ) := by
        simpa only [hs, Option.map_some] using he.symm
      simp only [hn, Option.bind_some]
      exact ih τ

theorem effect_memory_le (w : ℕ) (i : Instr) (s τ : SparseState)
    (hs : effect w i s = some τ) : τ.memory.length ≤ s.memory.length + 1 := by
  cases i <;> simp only [effect] at hs
  all_goals first
    | solve | (cases hs; simp [assign, write])
    | solve | (cases hi : s.inp.head? <;> (try simp only [hi, Option.map_some, Option.map_none] at hs) <;> cases hs <;> simp [assign, write])

theorem step_memory_le (w : ℕ) (p : Program) (s τ : SparseState)
    (hs : step w p s = some τ) : τ.memory.length ≤ s.memory.length + 1 := by
  unfold step at hs
  cases hi : p[s.pc]? with
  | none => simp only [hi, Option.bind_none] at hs; cases hs
  | some i =>
    simp only [hi, Option.bind_some] at hs
    exact effect_memory_le w i s τ hs

theorem run_memory_le (w : ℕ) (p : Program) (t : ℕ) (s τ : SparseState)
    (hs : run w p t s = some τ) : τ.memory.length ≤ s.memory.length + t := by
  induction t generalizing s τ with
  | zero =>
    simp only [run, Option.some.injEq] at hs
    subst τ
    omega
  | succ t ih =>
    obtain ⟨ν, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hs
    have hfirst := step_memory_le w p s ν hstep
    have hlast := ih ν τ hrest
    omega

/-- Every bounded execution of a black-box RAM program has a sparse
execution with the same exact output and at most one stored write per
successful virtual instruction. No address-range scan is needed. -/
theorem exists_execution (w : ℕ) (p : Program) (x y : List ℕ) (t : ℕ)
    (h : RunsTo w p x y t) :
    ∃ k ≤ t, ∃ s : SparseState,
      run w p k (init x) = some s ∧ step w p s = none ∧ s.out = y ∧
      s.memory.length ≤ k ∧ t = k + terminalCost p (expand s) := by
  obtain ⟨k, τ, hrun, hhalt, hout, htime⟩ := h
  have hexpand := run_expand w p k (init x)
  rw [init_expand, hrun] at hexpand
  cases hs : run w p k (init x) with
  | none => simp only [hs, Option.map_none] at hexpand; cases hexpand
  | some s =>
    have heq : expand s = τ := by simpa only [hs, Option.map_some, Option.some.injEq] using hexpand
    have hstop : step w p s = none := by
      have he := step_expand w p s
      rw [heq, hhalt] at he
      exact Option.map_eq_none_iff.mp he
    have hm := run_memory_le w p k (init x) s hs
    have htime' : t = k + terminalCost p (expand s) := by rw [heq]; exact htime
    refine ⟨k, by omega, s, hs, hstop, ?_, ?_, htime'⟩
    · change (expand s).out = y
      rw [heq]
      exact hout
    · simpa only [init, List.length_nil, Nat.zero_add] using hm

/-- Large virtual shifts can be handled by one comparison, without
constructing an exponentially long unbounded intermediate. -/
def shiftValue (w value count : ℕ) : ℕ :=
  if count < w then (value * 2 ^ count) % 2 ^ w else 0

theorem shiftValue_eq (w value count : ℕ) :
    shiftValue w value count = (value * 2 ^ count) % 2 ^ w := by
  unfold shiftValue
  split_ifs with h
  · rfl
  · have hc : count = w + (count - w) := by omega
    rw [hc, pow_add]
    simp only [Nat.mul_mod, Nat.mod_self, zero_mul, mul_zero, Nat.zero_mod]

/-- A registered polynomial-time solver supplies a fixed virtual program
and polynomial bounds for sparse execution. Only its public computation
predicate is used; no implementation-specific program is imported. -/
theorem polynomial_execution (solve : List ℕ → List ℕ)
    (hsolve : Lax759944.RamPolytime.RamPolytime solve) :
    ∃ (p : Program) (wordBound timeBound : Polynomial ℕ), ∀ x : List ℕ,
      Lax759944.RamPolytime.FitsInWords (wordBound.eval (Lax759944.BinaryWordEncoding.bitSize x))
        ((x.length :: x) ++ solve x) ∧
      ∃ k ≤ timeBound.eval (Lax759944.BinaryWordEncoding.bitSize x), ∃ s : SparseState,
        run (wordBound.eval (Lax759944.BinaryWordEncoding.bitSize x)) p k (init (x.length :: x)) = some s ∧
        step (wordBound.eval (Lax759944.BinaryWordEncoding.bitSize x)) p s = none ∧
        s.out = solve x ∧ s.memory.length ≤ k := by
  obtain ⟨p, wordBound, timeBound, hprogram⟩ := hsolve
  refine ⟨p, wordBound, timeBound, ?_⟩
  intro x
  obtain ⟨hfit, hwidth⟩ := hprogram x
  obtain ⟨t, ht, hrun⟩ := hwidth _ le_rfl
  obtain ⟨k, hkt, s, hs, hhalt, hout, hmemory, _⟩ := exists_execution _ p _ _ t hrun
  exact ⟨hfit, k, hkt.trans ht, s, hs, hhalt, hout, hmemory⟩

end Lax455465Proofs.SparseRam
