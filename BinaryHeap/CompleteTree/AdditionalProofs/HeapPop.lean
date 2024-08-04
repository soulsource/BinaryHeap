import BinaryHeap.CompleteTree.HeapOperations
import BinaryHeap.CompleteTree.AdditionalProofs.HeapRemoveLast
import BinaryHeap.CompleteTree.AdditionalProofs.HeapUpdateRoot

namespace BinaryHeap.CompleteTree.AdditionalProofs

theorem heapPopReturnsRoot {α : Type u} {n : Nat} (tree : CompleteTree α (n+1)) (le : α → α → Bool) : (tree.heapPop le).snd = tree.root (Nat.succ_pos n) := by
  unfold heapPop
  split
  <;> simp only
  case isFalse h₁ =>
    unfold Internal.heapRemoveLast Internal.heapRemoveLastAux
    split
    rename_i n m v l r _ _ _
    have h₂ : 0 = n + m := Eq.symm $  Nat.eq_zero_of_le_zero $ Nat.le_of_not_gt h₁
    simp only [h₂, ↓reduceDite, id_eq, root_unfold]
    have : n = 0 := And.left $ Nat.add_eq_zero.mp h₂.symm
    subst n
    have : m = 0 := And.right $ Nat.add_eq_zero.mp h₂.symm
    subst m
    rfl
  case isTrue h₁ =>
    have h₂ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexLeavesRoot tree h₁
    have h₃ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexHeapRemoveLastSameTree tree
    simp only [h₃, heapUpdateRootReturnsRoot, h₂]
