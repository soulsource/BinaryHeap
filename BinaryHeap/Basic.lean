namespace BinaryHeap

def transitive_le {α : Type u} (le : α → α → Bool) : Prop := ∀(a b c : α), (le a b) ∧ (le b c) → le a c
def total_le {α : Type u} (le : α → α → Bool) : Prop := ∀(a b : α), le a b ∨ le b a

inductive CompleteTree (α : Type u) : Nat → Type u
  | leaf : CompleteTree α 0
  | branch :
    (val : α)
    → (left : CompleteTree α n)
    → (right : CompleteTree α m)
    → m ≤ n
    → n < 2*(m+1)
    → (n+1).isPowerOfTwo ∨ (m+1).isPowerOfTwo
    → CompleteTree α (n+m+1)
deriving Repr

/-- Returns the element stored in the root node. -/
def CompleteTree.root (tree : CompleteTree α n) (_ : 0 < n) : α := match tree with
| .branch a _ _ _ _ _ => a

def HeapPredicate {α : Type u} {n : Nat} (heap : CompleteTree α n) (le : α → α → Bool) : Prop :=
  match heap with
  | .leaf => True
  | .branch a left right _ _ _ =>
    HeapPredicate left le ∧ HeapPredicate right le ∧ leOrLeaf a left ∧ leOrLeaf a right
    where leOrLeaf := λ {m : Nat} (v : α) (h : CompleteTree α m) ↦ match m with
                              | .zero => true
                              | .succ o => le v (h.root (Nat.succ_pos o))
