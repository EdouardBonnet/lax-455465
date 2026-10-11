import Lax455465Proofs.SparseRam
import Lax808846Proofs.Tactic
import Mathlib.Data.List.TakeDrop

namespace Lax455465Proofs.RamSparseMemory

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- Process writes in chronological order, retaining the latest match. -/
def update (address old : ℕ) (record : ℕ × ℕ) : ℕ := if record.1 = address then record.2 else old

def seen (records : List (ℕ × ℕ)) (address count : ℕ) : ℕ :=
  (records.take count).foldl (update address) 0

theorem seen_zero (records : List (ℕ × ℕ)) (address : ℕ) : seen records address 0 = 0 := rfl

theorem seen_step (records : List (ℕ × ℕ)) (address i : ℕ) (hi : i < records.length) :
    seen records address (i + 1) = update address (seen records address i) records[i] := by
  unfold seen
  rw [← List.take_concat_get' records i hi, List.foldl_append]
  rfl

theorem seen_reverse (m : SparseRam.Memory) (address : ℕ) :
    seen m.reverse address m.length = SparseRam.lookup m address := by
  unfold seen
  rw [← List.length_reverse, List.take_length]
  induction m with
  | nil => rfl
  | cons r rest ih =>
    rw [List.reverse_cons, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, ih, update, SparseRam.lookup]
    by_cases he : r.1 = address
    · rw [if_pos he, if_pos he.symm]
    · have hn : address ≠ r.1 := fun h => he h.symm
      rw [if_neg he, if_neg hn]

private theorem fold_bounded (records : List (ℕ × ℕ)) (address start B : ℕ)
    (hs : start < B) (hwords : ∀ r ∈ records, r.2 < B) :
    records.foldl (update address) start < B := by
  induction records generalizing start with
  | nil => exact hs
  | cons r rest ih =>
    apply ih
    · unfold update
      split_ifs
      · exact hwords r (List.mem_cons_self)
      · exact hs
    · exact fun r hr => hwords r (List.mem_cons_of_mem _ hr)

theorem seen_bounded (records : List (ℕ × ℕ)) (address i B : ℕ) (hB : 0 < B)
    (hwords : ∀ r ∈ records, r.2 < B) : seen records address i < B := by
  exact fold_bounded _ address 0 B hB (fun r hr => hwords r (List.mem_of_mem_take hr))

def Inputs (records : List (ℕ × ℕ)) (address : ℕ) (σ : Env) : Prop :=
  (∀ i (hi : i < records.length), (σ.arrs "vm.addresses")[i]? = some records[i].1 ∧
    (σ.arrs "vm.values")[i]? = some records[i].2) ∧
    σ.vars "vm.count" = records.length ∧ σ.vars "lookup.address" = address

def scanStep : Com :=
  .seq (.ite (.eq (.get "vm.addresses" (.var "lookup.i")) (.var "lookup.address"))
    (.assign "lookup.result" (.get "vm.values" (.var "lookup.i"))) .skip)
    (.assign "lookup.i" (.add (.var "lookup.i") (.lit 1)))

theorem scanStep_spec (B : ℕ) (records : List (ℕ × ℕ)) (address i : ℕ)
    (h1 : 1 < B) (haddress : address < B) (hlen : records.length < B) (hi : i < records.length)
    (hwords : ∀ r ∈ records, r.1 < B ∧ r.2 < B) :
    Spec B (fun σ => Inputs records address σ ∧ σ.vars "lookup.i" = i ∧
        σ.vars "lookup.result" = seen records address i) scanStep
      (fun _ τ => Inputs records address τ ∧ τ.vars "lookup.i" = i + 1 ∧
        τ.vars "lookup.result" = seen records address (i + 1)) 12 := by
  rintro σ ⟨⟨harrays, hcount, haddr⟩, hindex, hresult⟩
  have ha := (hwords records[i] (List.getElem_mem hi)).1
  have hv := (hwords records[i] (List.getElem_mem hi)).2
  have hgetA := (harrays i hi).1
  have hgetV := (harrays i hi).2
  have hlenA : i < (σ.arrs "vm.addresses").length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hgetA
    cases hgetA
  have hlenV : i < (σ.arrs "vm.values").length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hgetV
    cases hgetV
  run_vcg
  all_goals simp_all [Inputs, seen_step, update]

def Invariant (records : List (ℕ × ℕ)) (address : ℕ) (σ : Env) : Prop :=
  Inputs records address σ ∧ σ.vars "lookup.i" ≤ records.length ∧
    σ.vars "lookup.result" = seen records address (σ.vars "lookup.i")

def lookup : Com := .seq (.assign "lookup.result" (.lit 0))
  (.seq (.assign "lookup.i" (.lit 0))
    (.while (.lt (.var "lookup.i") (.var "vm.count")) scanStep))

/-- A host-memory lookup costs at most a constant times the number of
virtual writes, even when virtual addresses are much larger than that
number. The address and value arrays are preserved. -/
theorem lookup_spec (B : ℕ) (records : List (ℕ × ℕ)) (address : ℕ)
    (h1 : 1 < B) (haddress : address < B) (hlen : records.length < B)
    (hwords : ∀ r ∈ records, r.1 < B ∧ r.2 < B) :
    Spec B (Inputs records address) lookup
      (fun _ τ => Inputs records address τ ∧ τ.vars "lookup.result" = seen records address records.length)
      (16 * records.length + 8) := by
  have hbody : Spec B (fun σ => Invariant records address σ ∧ σ.vars "lookup.i" < records.length)
      scanStep (fun σ τ => Invariant records address τ ∧ τ.vars "lookup.i" = σ.vars "lookup.i" + 1) 12 := by
    rintro σ ⟨⟨hinputs, hindex, hresult⟩, hi⟩
    obtain ⟨τ, hr, ht⟩ := scanStep_spec B records address (σ.vars "lookup.i") h1 haddress hlen hi hwords
      σ ⟨hinputs, rfl, hresult⟩
    refine ⟨τ, hr, ⟨ht.1, ?_, ?_⟩, ht.2.1⟩
    · rw [ht.2.1]
      omega
    · rw [ht.2.1]
      exact ht.2.2
  have hlo := Spec.forRangeZero "lookup.i" "vm.count" (Invariant records address) records.length 12 hlen
    (fun _ h => h.2.1) (fun _ h => h.1.2.1) hbody
  have hfinal := hlo.post (fun _ τ _ h =>
    (show Inputs records address τ ∧ τ.vars "lookup.result" = seen records address records.length from
      ⟨h.1.1, by simpa only [h.2] using h.1.2.2⟩))
  intro σ hσ
  run_vcg [hfinal]
  all_goals simp_all [Invariant, Inputs, seen_zero]

/-- The reserved buffers represent exactly their initialized prefix. -/
theorem prefix_append (records : List (ℕ × ℕ)) (a v : ℕ) (σ : Env)
    (h : ∀ i (hi : i < records.length),
      (σ.arrs "vm.addresses")[i]? = some records[i].1 ∧
      (σ.arrs "vm.values")[i]? = some records[i].2)
    (hA : records.length < (σ.arrs "vm.addresses").length)
    (hV : records.length < (σ.arrs "vm.values").length) :
    ∀ i (hi : i < (records ++ [(a, v)]).length),
      ((σ.arrs "vm.addresses").set records.length a)[i]? = some (records ++ [(a, v)])[i].1 ∧
      ((σ.arrs "vm.values").set records.length v)[i]? = some (records ++ [(a, v)])[i].2 := by
  intro i hi
  by_cases hlt : i < records.length
  · rw [← List.getElem_append_left' hlt]
    have hne : records.length ≠ i := by omega
    simpa only [List.getElem?_set_ne hne] using h i hlt
  · have he : i = records.length := by
      simp only [List.length_append, List.length_singleton] at hi
      omega
    subst i
    simp only [List.getElem?_set_self hA, List.getElem?_set_self hV]
    simp

def put : Com := .seq
  (.store "vm.addresses" (.var "vm.count") (.var "put.address"))
  (.seq (.store "vm.values" (.var "vm.count") (.var "put.value"))
    (.assign "vm.count" (.add (.var "vm.count") (.lit 1))))

/-- Appending a virtual write touches two reserved host cells and costs
 ten structured instructions, independent of the virtual address. -/
theorem put_spec (B : ℕ) (records : List (ℕ × ℕ)) (lookupAddress a v : ℕ)
    (h1 : 1 < B) (ha : a < B) (hv : v < B) (hlen : records.length + 1 < B) :
    Spec B (fun σ => Inputs records lookupAddress σ ∧ σ.vars "put.address" = a ∧
      σ.vars "put.value" = v ∧ records.length < (σ.arrs "vm.addresses").length ∧
      records.length < (σ.arrs "vm.values").length) put
      (fun _ τ => Inputs (records ++ [(a, v)]) lookupAddress τ) 10 := by
  rintro σ ⟨⟨harrays, hcount, haddr⟩, hputA, hputV, hA, hV⟩
  have happend := prefix_append records a v σ harrays hA hV
  run_vcg
  all_goals simp_all [Inputs]

end Lax455465Proofs.RamSparseMemory
