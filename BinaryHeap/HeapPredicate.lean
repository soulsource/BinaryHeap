import BinaryHeap.CompleteTree.Basic

namespace BinaryHeap

def transitive_le {α : Type u} (le : α → α → Bool) : Prop := ∀(a b c : α), (le a b) ∧ (le b c) → le a c
def total_le {α : Type u} (le : α → α → Bool) : Prop := ∀(a b : α), le a b ∨ le b a

def HeapPredicate {α : Type u} {n : Nat} (heap : CompleteTree α n) (le : α → α → Bool) : Prop :=
  match heap with
  | .leaf => True
  | .branch a left right _ _ _ =>
    HeapPredicate left le ∧ HeapPredicate right le ∧ leOrLeaf a left ∧ leOrLeaf a right
    where leOrLeaf := λ {m : Nat} (v : α) (h : CompleteTree α m) ↦ match m with
                              | .zero => true
                              | .succ o => le v (h.root (Nat.succ_pos o))
