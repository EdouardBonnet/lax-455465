import Lax455465Proofs.RamArraySum
import Lax455465Proofs.RamFractionPrimitives
import Mathlib.Data.List.GetD

namespace Lax455465Proofs.RamMaskedSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

def coefficients (qs mask : List ℚ≥0) : List ℚ≥0 :=
  List.ofFn fun i : Fin qs.length => if (mask.getD i.val 0).num = 1 then qs[i.val] else 0

@[simp] theorem length_coefficients (qs ms : List ℚ≥0) : (coefficients qs ms).length = qs.length := List.length_ofFn

def entry (source mask : String) : Com := .seq (RamUnsignedBuffer.read mask "sum.i")
  (.ite (.eq (.var "rat.n") (.lit 1)) (RamUnsignedBuffer.read source "sum.i") RamFractionPrimitives.zero)

def command (source mask : String) : Com := RamUnsignedSum.command "sum.i" "sum.count" (entry source mask)

def Context (source mask : String) (qs ms : List ℚ≥0) (σ : Env) : Prop :=
  σ.vars "sum.count" = qs.length ∧ Prefix (RamUnsignedBuffer.encode qs) source σ ∧
    Prefix (RamUnsignedBuffer.encode ms) mask σ

theorem coefficient_at (qs ms : List ℚ≥0) (hlen : ms.length = qs.length) (i : ℕ) (hi : i < qs.length) :
    (coefficients qs ms)[i]'(by simpa only [coefficients,List.length_ofFn] using hi) =
      if (ms[i]'(by omega)).num = 1 then qs[i] else 0 := by
  simp only [coefficients,List.getElem_ofFn,List.getD_eq_get ms 0 (⟨i,by omega⟩ : Fin ms.length)]
  rfl

theorem entry_spec (B M : ℕ) (source mask : String) (qs ms : List ℚ≥0)
    (hlen : ms.length = qs.length) (i : ℕ) (hi : i < qs.length) (hB : 2*M^2+3 < B)
    (hindex : 2*i+1 < B) (hqn : qs[i].num ≤ M) (hqd : qs[i].den ≤ M)
    (hmn : (ms[i]'(by omega)).num ≤ M) (hmd : (ms[i]'(by omega)).den ≤ M) :
    Spec B (fun σ => Context source mask qs ms σ ∧ σ.vars "sum.i" = i) (entry source mask)
      (fun _ τ => Context source mask qs ms τ ∧ FractionOutput ((coefficients qs ms)[i]'(by simpa only [length_coefficients] using hi) : ℚ) τ) 32 := by
  have hM : M < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  have hmi : i < ms.length := by omega
  rintro σ ⟨hctx,hidx⟩
  obtain ⟨ν,rm,pm⟩ := RamUnsignedBuffer.read_spec B mask "sum.i" ms i hmi (by nlinarith) hindex
    (hmn.trans_lt hM) (hmd.trans_lt hM) (by decide) σ ⟨hctx.2.2,hidx⟩
  have hnum : ν.vars "rat.n" = ms[i].num := by simpa only [NNRat.natAbs_num_coe] using pm.1.2.1
  have hctxν : Context source mask qs ms ν := by
    simpa only [Context,Prefix,rm.frame_var "sum.count" (by simp [RamUnsignedBuffer.read,Com.wvars]),
      rm.frame_arr source (by simp [RamUnsignedBuffer.read,Com.warrs]),
      rm.frame_arr mask (by simp [RamUnsignedBuffer.read,Com.warrs])] using hctx
  have hidxν : ν.vars "sum.i" = i := (rm.frame_var "sum.i" (by simp [RamUnsignedBuffer.read,Com.wvars])).trans hidx
  have hc : (Cond.eq (.var "rat.n") (.lit 1)).evalB B ν = some (decide (ms[i].num = 1)) := by
    rw [evalB_condEq (evalB_var (hnum ▸ hmn.trans_lt hM)) (evalB_lit h1),hnum]
    congr 1
  by_cases hm : ms[i].num = 1
  · obtain ⟨τ,rq,pq⟩ := RamUnsignedBuffer.read_spec B source "sum.i" qs i hi (by nlinarith) hindex
      (hqn.trans_lt hM) (hqd.trans_lt hM) (by decide) ν ⟨hctxν.2.1,hidxν⟩
    have rr := rm.seq (Run.ite_true (d := RamFractionPrimitives.zero) (by simpa only [hm,decide_true] using hc) rq)
    refine ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),?_,?_⟩
    · simpa only [Context,Prefix,rq.frame_var "sum.count" (by simp [RamUnsignedBuffer.read,Com.wvars]),
        rq.frame_arr source (by simp [RamUnsignedBuffer.read,Com.warrs]),
        rq.frame_arr mask (by simp [RamUnsignedBuffer.read,Com.warrs])] using hctxν
    · simpa only [coefficient_at qs ms hlen i hi,if_pos hm] using pq.1
  · obtain ⟨τ,rz,pz⟩ := RamFractionPrimitives.zero_spec B h1 ν trivial
    have rr := rm.seq (Run.ite_false (c := RamUnsignedBuffer.read source "sum.i") (by simpa only [hm,decide_false] using hc) rz)
    refine ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),?_,?_⟩
    · simpa only [Context,Prefix,rz.frame_var "sum.count" (by decide),rz.frame_arr source (by change source ∉ ([] : List String); simp),
        rz.frame_arr mask (by change mask ∉ ([] : List String); simp)] using hctxν
    · simpa only [coefficient_at qs ms hlen i hi,if_neg hm,NNRat.coe_zero] using pz

/-- Exact native masked mass or capacity sum. Canonical zero/one masks
select precisely the supported coordinates, without division or host tests. -/
theorem command_spec (B M : ℕ) (source mask : String) (qs ms : List ℚ≥0)
    (hlen : ms.length = qs.length) (hB : 2*M^2+3 < B) (hindex : 2*qs.length+2 < B)
    (hqn : ∀ q ∈ qs, q.num ≤ M) (hqd : ∀ q ∈ qs, q.den ≤ M)
    (hmn : ∀ q ∈ ms, q.num ≤ M) (hmd : ∀ q ∈ ms, q.den ≤ M)
    (hprefixNum : ∀ i, ((coefficients qs ms).take i).sum.num ≤ M)
    (hprefixDen : ∀ i, ((coefficients qs ms).take i).sum.den ≤ M) :
    Spec B (Context source mask qs ms) (command source mask)
      (fun _ τ => Context source mask qs ms τ ∧ FractionOutput (((coefficients qs ms).sum : ℚ≥0) : ℚ) τ)
      ((36*(M^2).size+152)*qs.length+16) := by
  have hM1 : 1 ≤ M := by simpa only [List.take_zero,List.sum_nil,NNRat.den_zero] using hprefixDen 0
  have hnum : ∀ q ∈ coefficients qs ms, q.num ≤ M := by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    split_ifs
    · exact hqn _ (List.getElem_mem i.isLt)
    · simpa only [NNRat.num_zero] using Nat.zero_le M
  have hden : ∀ q ∈ coefficients qs ms, q.den ≤ M := by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    split_ifs
    · exact hqd _ (List.getElem_mem i.isLt)
    · simpa only [NNRat.den_zero] using hM1
  have hbody : ∀ i, ∀ hi : i < (coefficients qs ms).length,
      Spec B (fun σ => Context source mask qs ms σ ∧ σ.vars "sum.i" = i) (entry source mask)
        (fun _ τ => Context source mask qs ms τ ∧ FractionOutput ((coefficients qs ms)[i] : ℚ) τ) 32 := by
    intro i hi
    have hq : i < qs.length := by simpa only [length_coefficients] using hi
    have hm : i < ms.length := by omega
    exact entry_spec B M source mask qs ms hlen i hq hB (by omega)
      (hqn _ (List.getElem_mem hq)) (hqd _ (List.getElem_mem hq))
      (hmn _ (List.getElem_mem hm)) (hmd _ (List.getElem_mem hm))
  have hf := RamUnsignedSum.command_spec B M 32 (Context source mask qs ms)
    "sum.i" "sum.count" (coefficients qs ms) (entry source mask) hB
    (by rw [length_coefficients]; omega) hnum hden hprefixNum hprefixDen
    (fun _ h => by simpa only [length_coefficients] using h.1)
    (fun σ k name h hn => by
      rcases hn with rfl | rfl | rfl <;>
        simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    hbody (by decide)
    (by dsimp [entry,RamUnsignedBuffer.read,Com.wvars]; decide)
    (by dsimp [entry,RamUnsignedBuffer.read,Com.wvars]; decide)
    (fun rr h => by
      simpa only [Context,Prefix,rr.frame_var "sum.count" (by decide),
        rr.frame_arr source (by change source ∉ ([] : List String); simp),
        rr.frame_arr mask (by change mask ∉ ([] : List String); simp)] using h)
    (fun rr h => by
      simpa only [Context,Prefix,rr.frame_var "sum.count" (by decide),
        rr.frame_arr source (by change source ∉ ([] : List String); simp),
        rr.frame_arr mask (by change mask ∉ ([] : List String); simp)] using h)
  unfold command
  rw [length_coefficients] at hf
  convert hf using 1 <;> ring

end Lax455465Proofs.RamMaskedSum
