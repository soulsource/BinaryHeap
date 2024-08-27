import BinaryHeap.CompleteTree.Basic
import BinaryHeap.CompleteTree.NatLemmas

namespace BinaryHeap.CompleteTree

----------------------------------------------------------------------------------------------
-- indexOf

/--Helper function for CompleteTree.indexOf.-/
protected def Internal.indexOfAux {α : Type u} (heap : CompleteTree α o) (pred : α → Bool) (currentIndex : Nat) : Option (Fin (o+currentIndex)) :=
  match o, heap with
  | 0, .leaf => none
  | (n+m+1), .branch a left right _ _ _ =>
    have sum_n_m_succ_curr : n + m.succ + currentIndex > 0 := Nat.add_pos_left (Nat.add_pos_right n (Nat.succ_pos m)) currentIndex
    if pred a then
      let result := Fin.ofNat' currentIndex sum_n_m_succ_curr
      some result
    else
      let found_left := CompleteTree.Internal.indexOfAux left pred (currentIndex + 1)
      let found_left : Option (Fin (n+m+1+currentIndex)) := found_left.map λ a ↦ Fin.ofNat' a sum_n_m_succ_curr
      let found_right :=
        found_left
        <|>
        (CompleteTree.Internal.indexOfAux right pred (currentIndex + n + 1)).map ((λ a ↦ Fin.ofNat' a sum_n_m_succ_curr) : _ → Fin (n+m+1+currentIndex))
      found_right

/--Finds the first occurance of a given element in the heap and returns its index. Indices are depth first.-/
def indexOf {α : Type u} (heap : CompleteTree α o) (pred : α → Bool) : Option (Fin o) :=
  CompleteTree.Internal.indexOfAux heap pred 0


----------------------------------------------------------------------------------------------
-- get

/--Returns the element at the given index. Indices are depth first.-/
def get {α : Type u} {n : Nat} (index : Fin n) (heap : CompleteTree α n) : α :=
  match n, index, heap with
  | (_+_+1), 0, .branch v _ _ _ _ _ => v
  | (o+p+1), ⟨j+1,h₃⟩, .branch _ l r _ _ _ =>
    if h₄ : j < o then
      get ⟨j, h₄⟩ l
    else
      have h₄ : j - o < p := Nat.sub_lt_left_of_lt_add (Nat.ge_of_not_lt h₄) $ Nat.lt_of_succ_lt_succ h₃
      get ⟨j - o, h₄⟩ r

----------------------------------------------------------------------------------------------
-- contains - implemented as decidable proposition

def contains {α : Type u} {n : Nat} (tree : CompleteTree α n) (element : α) : Prop :=
  match n, tree with
  | 0, .leaf => False
  | (_+_+1), .branch v l r _ _ _ => v = element ∨ (l.contains element) ∨ (r.contains element)

instance {α : Type u} [DecidableEq α] {tree : CompleteTree α n} {element : α} : Decidable (tree.contains element) :=
  let rec go : [DecidableEq α] → (o :Nat) → (tree : CompleteTree α o) → Decidable (tree.contains element) := λ o tree ↦
    match o, tree with
    | 0, .leaf => Decidable.isFalse $ not_false_eq_true.mpr $ (eq_self 0).mp (rfl (a := 0))
    | p+q+1, .branch v l r _ _ _ =>
      if t : v = element then
        Decidable.isTrue $ Or.inl t
      else
        have hl := go p l
        if h₁ : hl.decide then
          Decidable.isTrue $ Or.inr $ Or.inl $ decide_eq_true_eq.mp h₁
        else
          have hr := go q r
          if h₂ : hr.decide then
            Decidable.isTrue $ Or.inr $ Or.inr $ decide_eq_true_eq.mp h₂
          else
            have h₁ : ¬l.contains element := decide_eq_true_eq.subst h₁
            have h₂ : ¬r.contains element := decide_eq_true_eq.subst h₂
            Decidable.isFalse $ not_or_intro t $ not_or_intro h₁ h₂
  go n tree
