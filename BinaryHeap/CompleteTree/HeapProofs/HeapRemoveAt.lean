import BinaryHeap.CompleteTree.HeapProofs.HeapPop
import BinaryHeap.CompleteTree.HeapProofs.HeapUpdateAt

namespace BinaryHeap.CompleteTree

theorem heapRemoveAtIsHeap {α : Type u} {n : Nat} (le : α → α → Bool) (index : Fin (n+1)) (heap : CompleteTree α (n+1)) (h₁ : HeapPredicate heap le) (wellDefinedLe : transitive_le le ∧ total_le le) : HeapPredicate (heap.heapRemoveAt le index).fst le := by
  have h₂ : HeapPredicate (Internal.heapRemoveLastWithIndex heap).fst le := CompleteTree.heapRemoveLastWithIndexIsHeap h₁ wellDefinedLe.left wellDefinedLe.right
  unfold heapRemoveAt
  split
  case isTrue => exact heapPopIsHeap le heap h₁ wellDefinedLe
  case isFalse h₃ =>
    cases h: (index = (Internal.heapRemoveLastWithIndex heap).snd.snd : Bool)
    <;> simp_all
    split
    <;> apply heapUpdateAtIsHeap <;> simp_all
