import Lax455465Proofs.RamBooleanArithmetic
import Lax455465Proofs.RamDualDistancesInit
import Lax455465Proofs.MaskedMassData

namespace Lax455465Proofs.RamArcMask

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational MetricMatrix DirectedFlowLP
open scoped NNRat

def matrix {n : ℕ} (mode : Option Bool) (mask : Fin n → Bool) : Matrix n :=
  fun u v => RamBooleanArithmetic.bit (RamBooleanArithmetic.flag mode (mask u) (mask v))

def Context {n : ℕ} (source : String) (mask : Fin n → Bool) (σ : Env) : Prop :=
  σ.vars "metric.n" = n ∧ σ.vars "metric.n2" = n*n ∧
    Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags mask)) source σ

theorem frame {B K : ℕ} {cmd : Com} {σ τ : Env} (hr : Run B cmd σ τ K)
    {n : ℕ} {source : String} {mask : Fin n → Bool} (h : Context source mask σ)
    (ha : source ∉ cmd.warrs) (hx : ∀ x ∈ ["metric.n","metric.n2"], x ∉ cmd.wvars) :
    Context source mask τ := by
  simpa only [Context,Prefix,hr.frame_arr source ha,
    hr.frame_var "metric.n" (hx _ (by simp)),hr.frame_var "metric.n2" (hx _ (by simp))] using h

def coefficient (mode : Option Bool) (source : String) : Com :=
  .seq RamDualDistancesInit.indices
    (.seq (RamUnsignedBuffer.read source "metric.u")
      (.seq (RamUnsignedArithmetic.copy "left")
        (.seq (RamUnsignedBuffer.read source "metric.v")
          (.seq (RamUnsignedArithmetic.copy "right") (RamBooleanArithmetic.command mode)))))

/-- Read both endpoint flags from the current vertex mask. The mode selects
active arcs, outward crossing arcs, or inward crossing arcs. -/
theorem coefficient_spec (B : ℕ) {n : ℕ} (mode : Option Bool) (source : String)
    (mask : Fin n → Bool) (u v : Fin n) (h2 : 2 < B) (hn : n < B) (hn2 : n*n < B)
    (hindex : 2*n+2 < B) :
    Spec B (fun σ => Context source mask σ ∧ σ.vars "metric.entry" = (edgeIndex n (u,v)).val)
      (coefficient mode source)
      (fun _ τ => Context source mask τ ∧ FractionOutput ((matrix mode mask u v : ℚ≥0) : ℚ) τ) 60 := by
  let qs := MaskedMassData.flags mask
  have hlen : qs.length = n := List.length_ofFn
  have hvalue (t : Fin n) : qs[t.val] = RamBooleanArithmetic.bit (mask t) := by
    simp only [qs,MaskedMassData.flags,List.getElem_ofFn,RamBooleanArithmetic.bit]
  have hnum (t : Fin n) : qs[t.val].num < B := by
    rw [hvalue]; cases mask t <;> simp [RamBooleanArithmetic.bit] <;> omega
  have hden (t : Fin n) : qs[t.val].den < B := by
    rw [hvalue]; cases mask t <;> simp [RamBooleanArithmetic.bit] <;> omega
  rintro σ ⟨hctx,hentry⟩
  obtain ⟨σ₁,r₁,p₁⟩ := RamDualDistancesInit.indices_spec B u v hn hn2 σ ⟨hctx.1,hentry⟩
  have hctx₁ := frame r₁ hctx (by simp [RamDualDistancesInit.indices,Com.warrs]) (by decide)
  obtain ⟨σ₂,r₂,p₂⟩ := RamUnsignedBuffer.read_spec B source "metric.u" qs u.val
    (by simpa only [hlen] using u.isLt) h2 (by omega) (hnum u) (hden u) (by decide) σ₁ ⟨hctx₁.2.2,p₁.1⟩
  obtain ⟨σ₃,r₃,p₃⟩ := RamUnsignedArithmetic.copy_spec B qs[u.val] "left" (by omega)
    (hnum u) (hden u) (by decide) σ₂ p₂.1
  have hctx₃ := frame r₃ (frame r₂ hctx₁ (by simp [RamUnsignedBuffer.read,Com.warrs]) (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide))
    (by simp [RamUnsignedArithmetic.copy,Com.warrs]) (by decide)
  have hv₃ : σ₃.vars "metric.v" = v.val :=
    (r₃.frame_var _ (by decide)).trans ((r₂.frame_var _ (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide)).trans p₁.2)
  obtain ⟨σ₄,r₄,p₄⟩ := RamUnsignedBuffer.read_spec B source "metric.v" qs v.val
    (by simpa only [hlen] using v.isLt) h2 (by omega) (hnum v) (hden v) (by decide) σ₃ ⟨hctx₃.2.2,hv₃⟩
  obtain ⟨σ₅,r₅,p₅⟩ := RamUnsignedArithmetic.copy_spec B qs[v.val] "right" (by omega)
    (hnum v) (hden v) (by decide) σ₄ p₄.1
  have hctx₅ := frame r₅ (frame r₄ hctx₃ (by simp [RamUnsignedBuffer.read,Com.warrs]) (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide))
    (by simp [RamUnsignedArithmetic.copy,Com.warrs]) (by decide)
  have hleft : σ₅.vars "left.s" = 0 ∧ σ₅.vars "left.n" = (RamBooleanArithmetic.bit (mask u)).num ∧ σ₅.vars "left.d" = 1 := by
    rw [r₅.frame_var "left.s" (by decide),r₅.frame_var "left.n" (by decide),r₅.frame_var "left.d" (by decide),
      r₄.frame_var "left.s" (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide),r₄.frame_var "left.n" (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide),r₄.frame_var "left.d" (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide)]
    have hp := p₃
    rw [hvalue u] at hp
    cases hu : mask u <;> simpa [RamBooleanArithmetic.bit,hu] using hp
  have hright : σ₅.vars "right.s" = 0 ∧ σ₅.vars "right.n" = (RamBooleanArithmetic.bit (mask v)).num ∧ σ₅.vars "right.d" = 1 := by
    have hp := p₅
    rw [hvalue v] at hp
    cases hv : mask v <;> simpa [RamBooleanArithmetic.bit,hv] using hp
  obtain ⟨τ,r₆,p₆⟩ := RamBooleanArithmetic.command_spec B mode (mask u) (mask v) (by omega) σ₅
    ⟨hleft.1,hleft.2.1,hleft.2.2,hright.1,hright.2.1,hright.2.2⟩
  refine ⟨τ,r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq r₆)))),
    frame r₆ hctx₅ (by cases mode with | none => simp [RamBooleanArithmetic.command,Com.warrs] | some b => cases b <;> simp [RamBooleanArithmetic.command,Com.warrs])
      (by cases mode with | none => decide | some b => cases b <;> decide),p₆⟩

def command (mode : Option Bool) (source target : String) : Com :=
  .seq (.assign "mask.position" (.lit 0))
    (RamUnsignedVector.command "metric.entry" "metric.n2" target "mask.position" (coefficient mode source))

/-- Produce the row-major arc mask using one bounded pass over all ordered
vertex pairs. No sorted list or externally supplied arc mask is required. -/
theorem command_spec (B : ℕ) {n : ℕ} (mode : Option Bool) (source target : String)
    (mask : Fin n → Bool) (hneq : source ≠ target) (h2 : 2 < B) (hn : n < B)
    (hn2 : n*n < B) (hindex : 2*(n*n)+2 < B) (hvertex : 2*n+2 < B) :
    Spec B (fun σ => Context source mask σ ∧ 2*(n*n) < (σ.arrs target).length)
      (command mode source target)
      (fun _ τ => Context source mask τ ∧ Prefix (RamUnsignedBuffer.encode (values (matrix mode mask))) target τ)
      (82*(n*n)+8) := by
  let qs := values (matrix mode mask)
  have hlen : qs.length = n*n := length_values _
  have hwords : ∀ i, ∀ hi : i < qs.length, qs[i].num < B ∧ qs[i].den < B := by
    intro i hi
    simp only [qs,values,matrix,List.getElem_ofFn]
    cases RamBooleanArithmetic.flag mode (mask _) (mask _) <;> simp [RamBooleanArithmetic.bit] <;> omega
  have hbody : ∀ i, ∀ hi : i < qs.length,
      Spec B (fun σ => Context source mask σ ∧ σ.vars "metric.entry" = i)
        (coefficient mode source) (fun _ τ => Context source mask τ ∧ FractionOutput (qs[i] : ℚ) τ) 60 := by
    intro i hi
    have he : i < n*n := by rwa [hlen] at hi
    let uv := (edgeIndex n).symm (⟨i,he⟩ : Fin (n*n))
    have hidx : edgeIndex n uv = (⟨i,he⟩ : Fin (n*n)) := (edgeIndex n).apply_symm_apply _
    simpa only [hidx,qs,values,List.getElem_ofFn,uv,Fin.eta] using
      coefficient_spec B mode source mask uv.1 uv.2 h2 hn hn2 hvertex
  have hfresh (x : String) (h : x ∈ ["metric.entry","mask.position"]) :
      x ∉ (coefficient mode source).wvars := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h|h
    · subst x; cases mode with
      | none => dsimp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.wvars]; decide
      | some b => cases b <;> dsimp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.wvars] <;> decide
    · subst x; cases mode with
      | none => dsimp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.wvars]; decide
      | some b => cases b <;> dsimp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.wvars] <;> decide
  have hloop := RamUnsignedVector.command_spec B 60 (Context source mask)
    "metric.entry" "metric.n2" target "mask.position" qs [] (coefficient mode source) (by omega)
    (by simp only [List.length_nil,hlen]; omega)
    (fun i hi => (hwords i hi).1) (fun i hi => (hwords i hi).2)
    (fun _ h => by simpa only [hlen] using h.2.1)
    (fun σ k h => by simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    hbody (hfresh _ (by simp)) (hfresh _ (by simp))
    (by cases mode with
      | none => simp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.warrs]
      | some b => cases b <;> simp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.warrs])
    (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide)
    (fun rr h => frame rr h (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.warrs,hneq])
      (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide))
    (by decide) (by decide)
  rintro σ ⟨hctx,hroom⟩
  let ν := σ.setVar "mask.position" 0
  have rzero : Run B (.assign "mask.position" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have hctxν := frame rzero hctx (by simp [Com.warrs]) (by decide)
  obtain ⟨τ,rr,pr⟩ := hloop ν ⟨hctxν,by intro i hi; simp at hi,by simp [ν],
    by simpa only [ν,arrs_setVar,hlen,List.length_nil,Nat.zero_add] using hroom⟩
  exact ⟨τ,(rzero.seq rr).mono (by simp only [hlen]; omega),pr.1,by simpa only [List.nil_append,qs] using pr.2.1⟩

end Lax455465Proofs.RamArcMask
