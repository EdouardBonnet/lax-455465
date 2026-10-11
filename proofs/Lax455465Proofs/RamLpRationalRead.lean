import Lax455465Proofs.RamRational
import Lax455465Proofs.RamVirtualState
import Lax109476.RationalEncoding

namespace Lax455465Proofs.RamLpRationalRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open Lax109476.RationalEncoding

def sign (q : ℚ) : ℕ := if q.num < 0 then 1 else 0

theorem value_eq (q : ℚ) : fractionValue (sign q) q.num.natAbs q.den = q := by
  have hnum : (if q.num < 0 then -((q.num.natAbs : ℕ) : ℚ) else ((q.num.natAbs : ℕ) : ℚ)) = (q.num : ℚ) := by
    generalize q.num = z
    cases z <;> simp
  by_cases h : q.num < 0
  · simp only [if_pos h] at hnum
    simpa only [fractionValue,sign,if_pos h,if_true,hnum] using q.num_div_den
  · simp only [if_neg h] at hnum
    simpa only [fractionValue,sign,if_neg h,show ¬(0:ℕ)=1 by decide,if_false,hnum] using q.num_div_den

/-- Read a canonical signed LP rational from the interpreter's private
output buffer and advance by exactly its three encoded words. -/
def command : Com := .seq (.assign "rat.s" (.get "vm.output" (.var "cert.cursor")))
  (.seq (.assign "rat.n" (.get "vm.output" (.add (.var "cert.cursor") (.lit 1))))
    (.seq (.assign "rat.d" (.get "vm.output" (.add (.var "cert.cursor") (.lit 2))))
      (.assign "cert.cursor" (.add (.var "cert.cursor") (.lit 3)))))

theorem command_spec (B : ℕ) (q : ℚ) (front tail : List ℕ) (h3 : 3 < B)
    (hlen : front.length+3 < B) (hn : q.num.natAbs < B) (hd : q.den < B) :
    Spec B (fun σ => Prefix (front ++ (encodeRational q ++ tail)) "vm.output" σ ∧
      σ.vars "cert.cursor" = front.length) command
      (fun _ τ => FractionOutput q τ ∧ τ.vars "cert.cursor" = front.length+3) 17 := by
  have hsign : sign q < B := by unfold sign; split_ifs <;> omega
  have hsign1 : sign q ≤ 1 := by unfold sign; split_ifs <;> omega
  have hvalue := value_eq q
  rintro σ ⟨hp,hcursor⟩
  let words := front ++ (encodeRational q ++ tail)
  have hiS : front.length < words.length := by simp [words,encodeRational]
  have hiN : front.length+1 < words.length := by simp [words,encodeRational]
  have hiD : front.length+2 < words.length := by simp [words,encodeRational]
  have hoS : words[front.length]? = some (sign q) := by
    rw [List.getElem?_append_right (by omega),Nat.sub_self]
    simp [encodeRational,sign]
  have hoN : words[front.length+1]? = some q.num.natAbs := by
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    simp [encodeRational]
  have hoD : words[front.length+2]? = some q.den := by
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    simp [encodeRational]
  rw [List.getElem?_eq_getElem hiS] at hoS
  rw [List.getElem?_eq_getElem hiN] at hoN
  rw [List.getElem?_eq_getElem hiD] at hoD
  have hgetS := (hp front.length hiS).trans hoS
  have hgetN := (hp (front.length+1) hiN).trans hoN
  have hgetD := (hp (front.length+2) hiD).trans hoD
  have hroom : front.length+2 < (σ.arrs "vm.output").length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hgetD
    cases hgetD
  run_vcg
  all_goals simp_all [FractionOutput]

end Lax455465Proofs.RamLpRationalRead
