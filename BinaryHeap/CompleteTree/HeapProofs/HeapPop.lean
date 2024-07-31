import BinaryHeap.CompleteTree.HeapProofs.HeapRemoveLast
import BinaryHeap.CompleteTree.HeapProofs.HeapUpdateRoot

namespace BinaryHeap.CompleteTree

theorem heapPopIsHeap {α : Type u} {n : Nat} (le : α → α → Bool) (heap : CompleteTree α (n+1)) (h₁ : HeapPredicate heap le) (wellDefinedLe : transitive_le le ∧ total_le le) : HeapPredicate (heap.heapPop le).fst le := by
  have h₂ : HeapPredicate (Internal.heapRemoveLast heap).fst le := CompleteTree.heapRemoveLastIsHeap h₁ wellDefinedLe.left wellDefinedLe.right
  unfold heapPop
  cases n <;> simp[h₂, heapUpdateRootIsHeap, wellDefinedLe]
