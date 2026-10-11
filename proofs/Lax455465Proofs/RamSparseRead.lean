import Lax455465Proofs.RamSparseMemory

namespace Lax455465Proofs.RamSparseRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamSparseMemory

def Representation (records : List (ℕ × ℕ)) (σ : Env) : Prop :=
  (∀ i (hi : i < records.length), (σ.arrs "vm.addresses")[i]? = some records[i].1 ∧
    (σ.arrs "vm.values")[i]? = some records[i].2) ∧ σ.vars "vm.count" = records.length

def read (target : String) (address : Expr) : Com :=
  .seq (.assign "lookup.address" address)
    (.seq lookup (.assign target (.var "lookup.result")))

/-- Read a virtual cell into any host register other than the memory
counter. The buffer representation and all unrelated host data are framed. -/
theorem read_spec (B : ℕ) (records : List (ℕ × ℕ)) (a : ℕ) (target : String) (e : Expr)
    (h1 : 1 < B) (ha : a < B) (hlen : records.length < B)
    (hwords : ∀ r ∈ records, r.1 < B ∧ r.2 < B) (htarget : target ≠ "vm.count") :
    Spec B (fun σ => Representation records σ ∧ e.evalB B σ = some a) (read target e)
      (fun _ τ => Representation records τ ∧ τ.vars target = seen records a records.length)
      (16 * records.length + e.size + 11) := by
  rintro σ ⟨⟨harrays, hcount⟩, he⟩
  have hstart : Run B (.assign "lookup.address" e) σ (σ.setVar "lookup.address" a)
      (1 + e.size) := Run.assign he
  have hinputs : Inputs records a (σ.setVar "lookup.address" a) := by
    simp only [Inputs, arrs_setVar, vars_setVar]
    exact ⟨harrays, by simpa using hcount, by simp⟩
  obtain ⟨ν, hlookup, hpost⟩ := lookup_spec B records a h1 ha hlen hwords _ hinputs
  have hbound : ν.vars "lookup.result" < B := by
    rw [hpost.2]
    exact seen_bounded records a records.length B (by omega) (fun r hr => (hwords r hr).2)
  have hfinish : Run B (.assign target (.var "lookup.result")) ν
      (ν.setVar target (ν.vars "lookup.result")) 2 := Run.assign (evalB_var hbound)
  refine ⟨ν.setVar target (ν.vars "lookup.result"), (hstart.seq (hlookup.seq hfinish)).mono ?_, ?_⟩
  · omega
  · rcases hpost.1 with ⟨harrays', hcount', _⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa only [arrs_setVar] using harrays'
    · simpa only [vars_setVar, if_neg (Ne.symm htarget)] using hcount'
    · simp only [vars_setVar]
      exact hpost.2

/-- Reading chronological writes recovers the registered virtual memory. -/
theorem read_sparse_spec (B : ℕ) (m : SparseRam.Memory) (a : ℕ) (target : String) (e : Expr)
    (h1 : 1 < B) (ha : a < B) (hlen : m.length < B)
    (hwords : ∀ r ∈ m, r.1 < B ∧ r.2 < B) (htarget : target ≠ "vm.count") :
    Spec B (fun σ => Representation m.reverse σ ∧ e.evalB B σ = some a) (read target e)
      (fun _ τ => Representation m.reverse τ ∧ τ.vars target = SparseRam.lookup m a)
      (16 * m.length + e.size + 11) := by
  have h := read_spec B m.reverse a target e h1 ha (by simpa using hlen)
    (fun r hr => hwords r (List.mem_reverse.mp hr)) htarget
  simpa only [List.length_reverse, seen_reverse] using h

def write : Com := .seq (.assign "put.address" (.var "vm.target"))
  (.seq (.assign "put.value" (.var "vm.result")) put)

theorem write_spec (B : ℕ) (records : List (ℕ × ℕ)) (a v : ℕ)
    (h1 : 1 < B) (ha : a < B) (hv : v < B) (hlen : records.length + 1 < B) :
    Spec B (fun σ => Representation records σ ∧ σ.vars "vm.target" = a ∧
      σ.vars "vm.result" = v ∧ records.length < (σ.arrs "vm.addresses").length ∧
      records.length < (σ.arrs "vm.values").length) write
      (fun _ τ => Representation (records ++ [(a, v)]) τ) 14 := by
  have hput : Spec B (fun σ => Representation records σ ∧ σ.vars "put.address" = a ∧
      σ.vars "put.value" = v ∧ records.length < (σ.arrs "vm.addresses").length ∧
      records.length < (σ.arrs "vm.values").length) put
      (fun _ τ => Representation (records ++ [(a, v)]) τ) 10 := by
    rintro σ ⟨⟨harrays, hcount⟩, hsa, hsv, hA, hV⟩
    obtain ⟨τ, hrun, hpost⟩ := put_spec B records (σ.vars "lookup.address") a v h1 ha hv hlen
      σ ⟨⟨harrays, hcount, rfl⟩, hsa, hsv, hA, hV⟩
    exact ⟨τ, hrun, hpost.1, hpost.2.1⟩
  rintro σ ⟨⟨harrays, hcount⟩, hsa, hsv, hA, hV⟩
  run_vcg [hput]
  all_goals simp_all [Representation]

/-- The native append operation realizes a virtual modulo-address and
modulo-value write, when its two operands have already been reduced. -/
theorem write_sparse_spec (B w : ℕ) (m : SparseRam.Memory) (a v : ℕ)
    (h1 : 1 < B) (hM : 2 ^ w < B) (ha : a < 2 ^ w) (hv : v < 2 ^ w)
    (hlen : m.length + 1 < B) :
    Spec B (fun σ => Representation m.reverse σ ∧ σ.vars "vm.target" = a ∧
      σ.vars "vm.result" = v ∧ m.length < (σ.arrs "vm.addresses").length ∧
      m.length < (σ.arrs "vm.values").length) write
      (fun _ τ => Representation (SparseRam.write w m a v).reverse τ) 14 := by
  have h := write_spec B m.reverse a v h1 (ha.trans hM) (hv.trans hM) (by simpa using hlen)
  simpa only [List.length_reverse, SparseRam.write, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hv,
    List.reverse_cons] using h

end Lax455465Proofs.RamSparseRead
