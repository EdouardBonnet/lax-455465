import Lax455465Proofs.LoopErasure

namespace Lax455465Proofs.LoopErasureMap
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem index (f : α → β) (hf : Function.Injective f) (xs : List α) (v : α) :
    (xs.map f).idxOf (f v)=xs.idxOf v := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases he : a=v
    · subst a
      simp
    · have hfe : f a≠f v := fun h => he (hf h)
      simpa [List.idxOf_cons,he,hfe] using congrArg (fun n : ℕ => n+1) ih

theorem append (f : α → β) (hf : Function.Injective f) (xs : List α) (v : α) :
    (LoopErasure.append xs v).map f=LoopErasure.append (xs.map f) (f v) := by
  have hm : f v∈xs.map f ↔ v∈xs := by
    simp only [List.mem_map]
    constructor
    · rintro ⟨a,ha,he⟩
      exact (hf he) ▸ ha
    · intro h
      exact ⟨v,h,rfl⟩
  simp only [LoopErasure.append,hm]
  split_ifs <;> simp only [List.map_take,index f hf,List.map_append,List.map_cons,List.map_nil]

end Lax455465Proofs.LoopErasureMap
