import BinaryHeap.CompleteTree.Basic
import BinaryHeap.CompleteTree.NatLemmas

namespace BinaryHeap

----------------------------------------------------------------------------------------------
-- indexOf

/--Helper function for CompleteTree.indexOf.-/
private def CompleteTree.indexOfAux {α : Type u} (heap : CompleteTree α o) (pred : α → Bool) (currentIndex : Nat) : Option (Fin (o+currentIndex)) :=
  match o, heap with
  | 0, .leaf => none
  | (n+m+1), .branch a left right _ _ _ =>
    have sum_n_m_succ_curr : n + m.succ + currentIndex > 0 := Nat.add_pos_left (Nat.add_pos_right n (Nat.succ_pos m)) currentIndex
    if pred a then
      let result := Fin.ofNat' currentIndex sum_n_m_succ_curr
      some result
    else
      let found_left := left.indexOfAux pred (currentIndex + 1)
      let found_left : Option (Fin (n+m+1+currentIndex)) := found_left.map λ a ↦ Fin.ofNat' a sum_n_m_succ_curr
      let found_right :=
        found_left
        <|>
        (right.indexOfAux pred (currentIndex + n + 1)).map ((λ a ↦ Fin.ofNat' a sum_n_m_succ_curr) : _ → Fin (n+m+1+currentIndex))
      found_right

/--Finds the first occurance of a given element in the heap and returns its index. Indices are depth first.-/
def CompleteTree.indexOf {α : Type u} (heap : CompleteTree α o) (pred : α → Bool) : Option (Fin o) :=
  indexOfAux heap pred 0


----------------------------------------------------------------------------------------------
-- get

/--Returns the lement at the given index. Indices are depth first.-/
def CompleteTree.get {α : Type u} {n : Nat} (index : Fin (n+1)) (heap : CompleteTree α (n+1)) : α :=
  match h₁ : index, h₂ : n, heap with
  | 0, (_+_), .branch v _ _ _ _ _ => v
  | ⟨j+1,h₃⟩, (o+p), .branch _ l r _ _ _ =>
    if h₄ : j < o then
      match o with
      | (oo+1) => get ⟨j, h₄⟩ l
    else
      have h₅ : n - o = p := Nat.sub_eq_of_eq_add $ (Nat.add_comm o p).subst h₂
      have : p ≠ 0 :=
        have h₆ : o < n := Nat.lt_of_le_of_lt (Nat.ge_of_not_lt h₄) (Nat.lt_of_succ_lt_succ h₃)
        h₅.symm.substr $ Nat.sub_ne_zero_of_lt h₆
      have h₆ : j - o < p := h₅.subst $ Nat.sub_lt_sub_right (Nat.ge_of_not_lt h₄) $ Nat.lt_of_succ_lt_succ h₃
      have _termination : j - o < index.val := (Fin.val_inj.mpr h₁).substr (Nat.sub_lt_succ j o)
      match p with
      | (pp + 1) => get ⟨j - o, h₆⟩ r