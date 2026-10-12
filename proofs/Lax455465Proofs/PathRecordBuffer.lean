import Lax455465Proofs.RamPathRecord
import Lax455465Proofs.RamPathState
import Lax455465Proofs.PathRecordArithmetic

namespace Lax455465Proofs.PathRecordBuffer
open scoped NNRat

abbrev Records (n : ℕ) := List (List (Fin n)×ℚ≥0)

def rational {n : ℕ} (rs : Records n) : AcyclicFlowDecomposition.Records (Fin n) :=
  rs.map fun r => (r.1,(r.2 : ℚ))

def encode {n : ℕ} (rs : Records n) : List ℕ :=
  rs.flatMap fun r => RamPathRecord.encode (RamPathState.simple r.1) r.2

@[simp] theorem rational_append {n : ℕ} (rs ts : Records n) :
    rational (rs++ts)=rational rs++rational ts := List.map_append

@[simp] theorem encode_append {n : ℕ} (rs ts : Records n) :
    encode (rs++ts)=encode rs++encode ts := List.flatMap_append

@[simp] theorem encode_singleton {n : ℕ} (ys : List (Fin n)) (w : ℚ≥0) :
    encode [(ys,w)]=RamPathRecord.encode (RamPathState.simple ys) w := by simp [encode]

theorem length_bound {n L : ℕ} (rs : Records n) (h : ∀ r∈rs,r.1.length≤L+1) :
    (encode rs).length≤rs.length*(L+4) := by
  induction rs with
  | nil => simp [encode]
  | cons r rs ih =>
    have hh := h r List.mem_cons_self
    have ht := ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
    simp only [encode,List.flatMap_cons,List.length_append,RamPathRecord.encode,
      RamPathState.simple,List.length_map,Lax455465.RationalEncoding.encodeRational,
      List.length_cons,List.length_nil] at ht ⊢
    nlinarith only [ht,hh]

theorem mass_append {n : ℕ} (rs ts : Records n) :
    AcyclicFlowDecomposition.mass (rational (rs++ts))=
      AcyclicFlowDecomposition.mass (rational rs)+AcyclicFlowDecomposition.mass (rational ts) := by
  simp [AcyclicFlowDecomposition.mass]

@[simp] theorem rational_singleton {n : ℕ} (ys : List (Fin n)) (w : ℚ≥0) :
    rational [(ys,w)]=[(ys,(w : ℚ))] := rfl

end Lax455465Proofs.PathRecordBuffer
