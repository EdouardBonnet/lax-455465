import Lax455465Proofs.RamLayeredContext

namespace Lax455465Proofs.RamLayeredCoefficient
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open RamLayeredContext LayeredLpFlat

def balance : Com := .ite (.eq (.var "lp.j") (.lit 0)) RamLayeredUnits.demand RamLayeredUnits.arc

theorem balance_spec (B n L i j : ℕ) (h2 : 2 < B) (hL : L < B) (hi : i < B) (hj : j+1 < B) :
    Spec B (Prepared n L i j) balance
      (fun _ τ => FractionOutput (balanceValue n L i j) τ) 34 := by
  obtain ⟨hac,hak,hau,hav⟩ := arc_bounds n L j
  obtain ⟨hf,hrc,hrk,hru,hs,ht⟩ := row_bounds n L i
  have h1 : 1 < B := by omega
  have hj' : j < B := by omega
  have hD := RamLayeredUnits.demand_spec B L (rowCommodity n L i/n) (rowCommodity n L i%n)
    (rowLayer n L i) (rowVertex n L i) h2 hL (hs.trans_lt hi) (ht.trans_lt hi) (hrk.trans_lt hi) (hru.trans_lt hi)
  have hA := RamLayeredUnits.arc_spec B (arcCommodity n L j) (rowCommodity n L i)
    (arcLayer n L j) (rowLayer n L i) (arcSource n L j) (arcTarget n L j) (rowVertex n L i)
    h1 (hac.trans_lt hj') (hrc.trans_lt hi) (by omega) (hrk.trans_lt hi) (hau.trans_lt hj') (hav.trans_lt hj') (hru.trans_lt hi)
  rintro σ ⟨hctx,hacσ,hakσ,hauσ,havσ,hfσ,hrcσ,hrkσ,hruσ,hsσ,htσ,hcsσ,hctσ⟩
  rcases hctx with ⟨hnσ,hn2σ,hLσ,hAσ,hVσ,hMσ,hiσ,hjσ⟩
  run_vcg [hD,hA]
  all_goals simp_all [balanceValue,divergenceValue,RamLayeredUnits.demandValue,
    neg_ite,←neg_div,neg_sub]

def signedBalance : Com := .seq balance RamLayeredUnits.rowSign

theorem signedBalance_spec (B n L i j : ℕ) (h2 : 2 < B) (hL : L < B) (hi : i < B) (hj : j+1 < B) :
    Spec B (Prepared n L i j) signedBalance
      (fun _ τ => FractionOutput (if rowSign n L i=0 then balanceValue n L i j else -balanceValue n L i j) τ) 42 := by
  intro σ h
  obtain ⟨ν,hbal,hpost⟩ := balance_spec B n L i j h2 hL hi hj σ h
  have hflag : ν.vars "short.rowSign"=rowSign n L i :=
    (hbal.frame_var "short.rowSign" (by decide)).trans h.2.2.2.2.2.1
  obtain ⟨τ,hsign,hpost'⟩ := RamLayeredUnits.rowSign_spec B (rowSign n L i) (balanceValue n L i j)
    (by omega) ((row_bounds n L i).1.trans_lt hi) ν ⟨hpost,hflag⟩
  exact ⟨τ,hbal.seq hsign,hpost'⟩

def body : Com := .ite (.lt (.var "lp.i") (.var "lp.n2")) RamLayeredUnits.capacity signedBalance

theorem body_spec (B n L i j : ℕ) (h2 : 2 < B) (hn2 : n*n < B) (hL : L < B) (hi : i < B) (hj : j+1 < B) :
    Spec B (Prepared n L i j) body (fun _ τ => FractionOutput (coefficient n L i j) τ) 46 := by
  have hj' : j < B := by omega
  have ha := (arc_bounds n L j).2.2.1.trans_lt hj'
  have hb := (arc_bounds n L j).2.2.2.trans_lt hj'
  have hC := RamLayeredUnits.capacity_spec B j (i/n) (i%n) (arcSource n L j) (arcTarget n L j)
    (by omega) hj' ((Nat.div_le_self _ _).trans_lt hi) ((Nat.mod_le _ _).trans_lt hi) ha hb
  have hS := signedBalance_spec B n L i j h2 hL hi hj
  intro σ h
  rcases h with ⟨hctx,hacσ,hakσ,hauσ,havσ,hfσ,hrcσ,hrkσ,hruσ,hsσ,htσ,hcsσ,hctσ⟩
  rcases hctx with ⟨hnσ,hn2σ,hLσ,hAσ,hVσ,hMσ,hiσ,hjσ⟩
  run_vcg [hC,hS]
  all_goals simp_all [Prepared,Context,coefficient,capacityValue,RamLayeredUnits.capacityValue]
  all_goals
    have hnot : ¬i<n*n := by omega
    simp_all only [if_neg hnot,if_false]

/-- The complete fixed native coefficient evaluator. No dimensions or row
indices occur as program parameters. -/
def command : Com := .seq prepare body

theorem command_spec (B n L i j : ℕ) (h2 : 2 < B) (hn : n < B) (hn2 : n*n < B)
    (hL : L < B) (hA : L*(n*n) < B) (hV : (L+1)*n < B) (hM : (n*n)*((L+1)*n) < B)
    (hi : i < B) (hj : j+1 < B) :
    Spec B (Context n L i j) command (fun _ τ => FractionOutput (coefficient n L i j) τ) 134 := by
  intro σ h
  obtain ⟨ν,hprep,hpost⟩ := prepare_spec B n L i j (by omega) hn hn2 hA hV hM hi (by omega) σ h
  obtain ⟨τ,hbody,hpost'⟩ := body_spec B n L i j h2 hn2 hL hi hj ν hpost
  exact ⟨τ,hprep.seq hbody,hpost'⟩

end Lax455465Proofs.RamLayeredCoefficient
