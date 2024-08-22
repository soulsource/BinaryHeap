import BinaryHeap.CompleteTree.HeapOperations
import BinaryHeap.CompleteTree.AdditionalOperations
import BinaryHeap.CompleteTree.AdditionalProofs.Contains

namespace BinaryHeap.CompleteTree.AdditionalProofs

private theorem containsSeesThroughCast {α : Type u} {o p : Nat} (heap : CompleteTree α (o + 1 + p + 1)) (h₁ : o + 1 + p + 1 = o + p + 2) : heap.contains = (h₁▸heap).contains := by
  induction p generalizing o
  case zero => rfl
  case succ pp hp =>
    have hp := hp (o := o + 1)
    have : o + 1 + 1 + pp + 1 = o + 1 + (pp + 1) + 1 := by omega
    rw[this] at hp
    have : o + 1 + pp + 2 = o + (pp + 1) + 2 := by omega
    rw[this] at hp
    have hp := hp heap h₁
    assumption

theorem heapPushContainsValue {α : Type u} {n : Nat} (le : α → α → Bool) (heap : CompleteTree α n) (val : α) : (heap.heapPush le val).contains val := by
  unfold heapPush
  split
  case h_1 =>
    rw[contains_as_root_left_right _ _ (Nat.succ_pos _),root_unfold]
    left
    rfl
  case h_2 =>
    rename_i o p v l r p_le_o max_height_difference subtree_complete
    cases le val v
    <;> dsimp
    <;> split
    case' true.isFalse | false.isFalse =>
      rw[←containsSeesThroughCast]
    case true.isTrue | true.isFalse =>
      rw[contains_as_root_left_right _ _ (Nat.succ_pos _), root_unfold]
      left
      rfl
    case' false.isTrue | false.isFalse =>
      rw[contains_as_root_left_right _ _ (Nat.succ_pos _)]
      right
    case false.isTrue =>
      right
      rw[right_unfold]
      exact heapPushContainsValue le r val
    case false.isFalse =>
      left
      rw[left_unfold]
      exact heapPushContainsValue le l val
