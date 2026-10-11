import Lax455465Proofs.RamVirtualProgram
import Lax455465Proofs.SparseBounds

namespace Lax455465Proofs.RamVirtualCore

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualProgram RamSparseRead

/-- The virtual machine owns only its reserved buffers and registers. -/
def Core (w pc : ℕ) (m : SparseRam.Memory) (σ : Env) : Prop :=
  Representation m.reverse σ ∧ σ.vars "vm.pc" = pc ∧
  σ.vars "vm.modulus" = 2 ^ w ∧ σ.vars "vm.width" = w

theorem read_expression_spec (B w pc : ℕ) (m : SparseRam.Memory) (a : ℕ) (target : String) (e : Expr)
    (h1 : 1 < B) (hM : 2 ^ w < B) (ha : a < B) (hlen : m.length < B)
    (hwords : SparseBounds.MemoryWords w m)
    (htarget : target ≠ "vm.count") (hpc : target ≠ "vm.pc")
    (hmodulus : target ≠ "vm.modulus") (hwidth : target ≠ "vm.width") :
    Spec B (fun σ => Core w pc m σ ∧ e.evalB B σ = some a) (RamSparseRead.read target e)
      (fun _ τ => Core w pc m τ ∧ τ.vars target = SparseRam.lookup m a)
      (16 * m.length + e.size + 11) := by
  rintro σ ⟨⟨hrep, hσpc, hσmod, hσwidth⟩, he⟩
  obtain ⟨τ, hrun, hpost⟩ := read_sparse_spec B m a target e h1 ha hlen
    (fun r hr => ⟨(hwords r hr).1.trans hM, (hwords r hr).2.trans hM⟩) htarget σ ⟨hrep, he⟩
  have hpc' := hrun.frame_var "vm.pc" (by simp [RamSparseRead.read, RamSparseMemory.lookup,
    RamSparseMemory.scanStep, Com.wvars, Ne.symm hpc])
  have hmod' := hrun.frame_var "vm.modulus" (by simp [RamSparseRead.read, RamSparseMemory.lookup,
    RamSparseMemory.scanStep, Com.wvars, Ne.symm hmodulus])
  have hwidth' := hrun.frame_var "vm.width" (by simp [RamSparseRead.read, RamSparseMemory.lookup,
    RamSparseMemory.scanStep, Com.wvars, Ne.symm hwidth])
  exact ⟨τ, hrun, ⟨hpost.1, hpc'.trans hσpc, hmod'.trans hσmod, hwidth'.trans hσwidth⟩, hpost.2⟩

theorem read_literal_spec (B w pc : ℕ) (m : SparseRam.Memory) (a : ℕ) (target : String)
    (h1 : 1 < B) (hM : 2 ^ w < B) (ha : a < B) (hlen : m.length < B)
    (hwords : SparseBounds.MemoryWords w m)
    (htarget : target ≠ "vm.count") (hpc : target ≠ "vm.pc")
    (hmodulus : target ≠ "vm.modulus") (hwidth : target ≠ "vm.width") :
    Spec B (Core w pc m) (RamSparseRead.read target (remainder (.lit a)))
      (fun _ τ => Core w pc m τ ∧ τ.vars target = SparseRam.lookup m (a % 2 ^ w))
      (16 * m.length + 18) := by
  rintro σ ⟨hrep, hσpc, hσmod, hσwidth⟩
  have he := evalB_remainder (evalB_lit ha) hσmod hM ha
  obtain ⟨τ, hrun, hpost⟩ := read_sparse_spec B m (a % 2 ^ w) target (remainder (.lit a)) h1
    ((Nat.mod_lt _ (Nat.two_pow_pos w)).trans hM) hlen
    (fun r hr => ⟨(hwords r hr).1.trans hM, (hwords r hr).2.trans hM⟩) htarget σ ⟨hrep, he⟩
  have hpc' := hrun.frame_var "vm.pc" (by simp [RamSparseRead.read, RamSparseMemory.lookup,
    RamSparseMemory.scanStep, Com.wvars, Ne.symm hpc])
  have hmod' := hrun.frame_var "vm.modulus" (by simp [RamSparseRead.read, RamSparseMemory.lookup,
    RamSparseMemory.scanStep, Com.wvars, Ne.symm hmodulus])
  have hwidth' := hrun.frame_var "vm.width" (by simp [RamSparseRead.read, RamSparseMemory.lookup,
    RamSparseMemory.scanStep, Com.wvars, Ne.symm hwidth])
  exact ⟨τ, hrun, ⟨hpost.1, hpc'.trans hσpc, hmod'.trans hσmod, hwidth'.trans hσwidth⟩, hpost.2⟩

theorem write_core_spec (B w pc : ℕ) (m : SparseRam.Memory) (a value : ℕ)
    (h1 : 1 < B) (hM : 2 ^ w < B) (ha : a < 2 ^ w) (hv : value < 2 ^ w)
    (hlen : m.length + 1 < B) :
    Spec B (fun σ => Core w pc m σ ∧ σ.vars "vm.target" = a ∧
      σ.vars "vm.result" = value ∧ m.length < (σ.arrs "vm.addresses").length ∧
      m.length < (σ.arrs "vm.values").length) RamSparseRead.write
      (fun _ τ => Core w pc (SparseRam.write w m a value) τ) 14 := by
  rintro σ ⟨⟨hrep, hspc, hsmod, hsw⟩, htarget, hvalue, hA, hV⟩
  obtain ⟨τ, hr, ht⟩ := write_sparse_spec B w m a value h1 hM ha hv hlen
    σ ⟨hrep, htarget, hvalue, hA, hV⟩
  exact ⟨τ, hr, ht, (hr.frame_var "vm.pc" (by decide)).trans hspc,
    (hr.frame_var "vm.modulus" (by decide)).trans hsmod,
    (hr.frame_var "vm.width" (by decide)).trans hsw⟩

theorem writeBack_general_spec (B w pc : ℕ) (m : SparseRam.Memory) (a value : ℕ)
    (targetExpr valueExpr : Expr) (h1 : 1 < B) (hM : 2 ^ w < B) (ha : a < B) (hv : value < B)
    (hpc : pc + 1 < B) (hlen : m.length + 1 < B) :
    Spec B (fun σ => Core w pc m σ ∧ m.length < (σ.arrs "vm.addresses").length ∧
      m.length < (σ.arrs "vm.values").length ∧ targetExpr.evalB B σ = some a ∧
      valueExpr.evalB B (σ.setVar "vm.target" (a % 2 ^ w)) = some value)
      (writeBack targetExpr valueExpr)
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m a value) τ)
      (2 * targetExpr.size + 2 * valueExpr.size + 30) := by
  rintro σ ⟨hcore, hA, hV, htarget, hvalue⟩
  have hmσ := hcore.2.2.1
  have ht := evalB_remainder htarget hmσ hM ha
  have hmν : (σ.setVar "vm.target" (a % 2 ^ w)).vars "vm.modulus" = 2 ^ w := by simpa using hmσ
  have hv' := evalB_remainder hvalue hmν hM hv
  have hfirst := Run.assign (x := "vm.target") ht
  have hsecond := Run.assign (x := "vm.result") hv'
  have hpre : Core w pc m ((σ.setVar "vm.target" (a % 2 ^ w)).setVar "vm.result" (value % 2 ^ w)) ∧
      ((σ.setVar "vm.target" (a % 2 ^ w)).setVar "vm.result" (value % 2 ^ w)).vars "vm.target" = a % 2 ^ w ∧
      ((σ.setVar "vm.target" (a % 2 ^ w)).setVar "vm.result" (value % 2 ^ w)).vars "vm.result" = value % 2 ^ w ∧
      m.length < (((σ.setVar "vm.target" (a % 2 ^ w)).setVar "vm.result" (value % 2 ^ w)).arrs "vm.addresses").length ∧
      m.length < (((σ.setVar "vm.target" (a % 2 ^ w)).setVar "vm.result" (value % 2 ^ w)).arrs "vm.values").length := by
    simpa only [Core, RamSparseRead.Representation, arrs_setVar, vars_setVar,
      String.reduceEq, if_true, if_false, true_and] using And.intro hcore (And.intro hA hV)
  obtain ⟨τ, hwrite, hpost⟩ := write_core_spec B w pc m (a % 2 ^ w) (value % 2 ^ w)
    h1 hM (Nat.mod_lt _ (Nat.two_pow_pos w)) (Nat.mod_lt _ (Nat.two_pow_pos w)) hlen _ hpre
  have hwrites : SparseRam.write w m (a % 2 ^ w) (value % 2 ^ w) = SparseRam.write w m a value := by
    simp only [SparseRam.write, Nat.mod_mod]
  rw [hwrites] at hpost
  have hinc : Run B increment τ (τ.setVar "vm.pc" (pc + 1)) 4 :=
    Run.assign (evalB_bin (op := .add)
      (by rw [evalB_var_iff]; exact ⟨hpost.2.1.symm, by rw [hpost.2.1]; omega⟩)
      (evalB_lit h1) hpc)
  refine ⟨τ.setVar "vm.pc" (pc + 1), (hfirst.seq (hsecond.seq (hwrite.seq hinc))).mono ?_, ?_⟩
  · simp only [remainder, Expr.size]
    omega
  · simpa only [Core, RamSparseRead.Representation, arrs_setVar, vars_setVar,
      String.reduceEq, if_true, if_false, true_and] using And.intro hpost.1 hpost.2.2

theorem set_spec (B w pc : ℕ) (m : SparseRam.Memory) (a value : ℕ)
    (h1 : 1 < B) (hM : 2 ^ w < B) (ha : a < B) (hv : value < B)
    (hpc : pc + 1 < B) (hlen : m.length + 1 < B) :
    Spec B (fun σ => Core w pc m σ ∧ m.length < (σ.arrs "vm.addresses").length ∧
      m.length < (σ.arrs "vm.values").length) (instruction (.set a value))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m a value) τ) 40 := by
  have ham := Nat.mod_lt a (Nat.two_pow_pos w)
  have hvm := Nat.mod_lt value (Nat.two_pow_pos w)
  have hwrite := write_core_spec B w pc m (a % 2 ^ w) (value % 2 ^ w) h1 hM ham hvm hlen
  have hwrites : SparseRam.write w m (a % 2 ^ w) (value % 2 ^ w) = SparseRam.write w m a value := by
    simp only [SparseRam.write, Nat.mod_mod]
  rw [hwrites] at hwrite
  rintro σ ⟨⟨hrep, hσpc, hσmod, hσwidth⟩, hA, hV⟩
  have had : a / 2 ^ w < B := (Nat.div_le_self _ _).trans_lt ha
  have hap : a / 2 ^ w * 2 ^ w < B := (Nat.div_mul_le_self _ _).trans_lt ha
  have has : a - a / 2 ^ w * 2 ^ w < B := (Nat.sub_le _ _).trans_lt ha
  have hvd : value / 2 ^ w < B := (Nat.div_le_self _ _).trans_lt hv
  have hvp : value / 2 ^ w * 2 ^ w < B := (Nat.div_mul_le_self _ _).trans_lt hv
  have hvs : value - value / 2 ^ w * 2 ^ w < B := (Nat.sub_le _ _).trans_lt hv
  simp only [instruction, writeBack, remainder, increment]
  run_vcg [hwrite]
  all_goals simp_all [Core, Representation, Nat.mod_def, Nat.mul_comm]
  all_goals omega

theorem writeBack_register_spec (B w pc : ℕ) (m : SparseRam.Memory) (a value : ℕ)
    (h1 : 1 < B) (hM : 2 ^ w < B) (ha : a < B) (hv : value < B)
    (hpc : pc + 1 < B) (hlen : m.length + 1 < B) :
    Spec B (fun σ => Core w pc m σ ∧ σ.vars "vm.result" = value ∧
      m.length < (σ.arrs "vm.addresses").length ∧ m.length < (σ.arrs "vm.values").length)
      (writeBack (.lit a) (.var "vm.result"))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m a value) τ) 40 := by
  have ham := Nat.mod_lt a (Nat.two_pow_pos w)
  have hvm := Nat.mod_lt value (Nat.two_pow_pos w)
  have hwrite := write_core_spec B w pc m (a % 2 ^ w) (value % 2 ^ w) h1 hM ham hvm hlen
  have hwrites : SparseRam.write w m (a % 2 ^ w) (value % 2 ^ w) = SparseRam.write w m a value := by
    simp only [SparseRam.write, Nat.mod_mod]
  rw [hwrites] at hwrite
  rintro σ ⟨⟨hrep, hσpc, hσmod, hσwidth⟩, hσvalue, hA, hV⟩
  have had : a / 2 ^ w < B := (Nat.div_le_self _ _).trans_lt ha
  have hap : a / 2 ^ w * 2 ^ w < B := (Nat.div_mul_le_self _ _).trans_lt ha
  have has : a - a / 2 ^ w * 2 ^ w < B := (Nat.sub_le _ _).trans_lt ha
  have hvd : value / 2 ^ w < B := (Nat.div_le_self _ _).trans_lt hv
  have hvp : value / 2 ^ w * 2 ^ w < B := (Nat.div_mul_le_self _ _).trans_lt hv
  have hvs : value - value / 2 ^ w * 2 ^ w < B := (Nat.sub_le _ _).trans_lt hv
  simp only [writeBack, remainder, increment]
  run_vcg [hwrite]
  all_goals simp_all [Core, Representation, Nat.mod_def, Nat.mul_comm]
  all_goals omega

theorem jump_spec (B w pc : ℕ) (m : SparseRam.Memory) (label : ℕ) (hlabel : label < B) :
    Spec B (Core w pc m) (instruction (.jump label))
      (fun _ τ => Core w label m τ) 2 := by
  rintro σ ⟨hrep, hσpc, hσmod, hσwidth⟩
  run_vcg
  all_goals simp_all [Core, Representation]

end Lax455465Proofs.RamVirtualCore
