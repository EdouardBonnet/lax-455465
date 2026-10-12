import Lax455465Proofs.LayeredGraphFlow

namespace Lax455465Proofs.LayeredPositivePath
open LayeredFlowLP LayeredGraphFlow AcyclicFlowPath
open scoped BigOperators

/-- At every nontarget vertex reached by positive flow, conservation
supplies a positive outgoing edge. -/
theorem next {α : Type*} [Fintype α] [DecidableEq α]
    (g : α → α → ℚ) (hg : ∀ u v,0≤g u v) (s t u : α) (a : ℚ)
    (ha : 0<a) (hb : Balance g s t a) (hut : u≠t)
    (hreach : u=s ∨ ∃ v,0<g v u) : ∃ v,0<g u v := by
  have hout : 0<∑ v,g u v := by
    have hh := hb u
    rw [if_neg hut] at hh
    rcases hreach with rfl | ⟨v,hv⟩
    · have hin : 0≤∑ v,g v u := Finset.sum_nonneg fun v _ => hg v u
      simp only [if_true,sub_zero] at hh
      linarith
    · have hin : 0<∑ v,g v u := hv.trans_le
        (Finset.single_le_sum (fun v _ => hg v u) (Finset.mem_univ v))
      split_ifs at hh <;> linarith
  by_contra! hh
  have hnonpos : (∑ v,g u v)≤0 := Finset.sum_nonpos fun v _ => hh v
  linarith

theorem edge_eq {n L : ℕ} (x : Arc n L → ℚ) (st : Edge n) (k : Fin L) (u v : Fin n) :
    graph x st (k.castSucc,u) (k.succ,v)=x (st,(k,(u,v))) := by
  have he (j : Fin L) : j.castSucc=k.castSucc ∧ j.succ=k.succ ↔ j=k := by
    constructor
    · intro h
      exact Fin.ext (congrArg (fun i : Fin (L+1) => i.val) h.1)
    · rintro rfl
      exact ⟨rfl,rfl⟩
  simp only [graph,he]
  simp

theorem exists_successor {n L : ℕ} (x : Arc n L → ℚ) (hx : ∀ a,0≤x a)
    (s t : Fin n) (a : ℚ) (ha : 0<a)
    (hb : Balance (graph x (s,t)) (0,s) (Fin.last L,t) a)
    (k : Fin L) (u : Fin n)
    (hreach : ((k.castSucc,u) : Vertex n L)=(0,s) ∨
      ∃ p : Vertex n L,0<graph x (s,t) p (k.castSucc,u)) :
    ∃ v : Fin n,0<x ((s,t),(k,(u,v))) := by
  have hnot : ((k.castSucc,u) : Vertex n L)≠(Fin.last L,t) := by
    intro hh
    have he := congrArg (fun p : Vertex n L => p.1.val) hh
    simp only [Fin.val_castSucc,Fin.val_last] at he
    omega
  obtain ⟨q,hq⟩ := next (graph x (s,t)) (nonnegative x hx (s,t)) (0,s) (Fin.last L,t)
    (k.castSucc,u) a ha hb hnot hreach
  have hl := advances x hx (s,t) (k.castSucc,u) q hq
  have he : q.1=k.succ := Fin.ext (by simpa using hl)
  rcases q with ⟨l,v⟩
  simp only at he
  subst l
  exact ⟨v,by simpa only [edge_eq] using hq⟩

theorem outgoing_last {n L : ℕ} (x : Arc n L → ℚ) (st : Edge n) (v : Fin n) :
    (∑ q,graph x st (Fin.last L,v) q)=0 := by
  rw [outgoing]
  have he (k : Fin L) : k.castSucc≠Fin.last L := by
    intro hh
    have hval := congrArg Fin.val hh
    simp only [Fin.val_castSucc,Fin.val_last] at hval
    omega
  simp [he]

/-- A positive incoming edge at the final layer must end at the target. -/
theorem target {n L : ℕ} (x : Arc n L → ℚ) (hx : ∀ a,0≤x a)
    (s t v : Fin n) (a : ℚ) (ha : 0≤a)
    (hb : Balance (graph x (s,t)) (0,s) (Fin.last L,t) a)
    (hin : ∃ p : Vertex n L,0<graph x (s,t) p (Fin.last L,v)) : v=t := by
  by_contra hv
  have hut : ((Fin.last L,v) : Vertex n L)≠(Fin.last L,t) := by
    intro he
    exact hv (congrArg Prod.snd he)
  obtain ⟨p,hp⟩ := hin
  have hsum : 0<∑ p,graph x (s,t) p (Fin.last L,v) := hp.trans_le
    (Finset.single_le_sum (fun p _ => nonnegative x hx (s,t) p _) (Finset.mem_univ p))
  have hh := hb (Fin.last L,v)
  rw [outgoing_last,if_neg hut] at hh
  split_ifs at hh <;> linarith

end Lax455465Proofs.LayeredPositivePath
