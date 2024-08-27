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

theorem heapPushRetainsHeapValues {α : Type u} {n: Nat} (le : α → α → Bool) (heap : CompleteTree α n) (val : α) (index : Fin n) : (heap.heapPush le val).contains (heap.get index) := by
  unfold heapPush
  split
  case h_1 =>
    have := index.isLt
    contradiction
  case h_2 =>
    rename_i o p v l r p_le_o max_height_difference subtree_complete
    have h₁ : o+p+1 > 0 := Nat.succ_pos _
    if h₂ : index = ⟨0, h₁⟩ then
      subst h₂
      cases le val v
      <;> dsimp
      <;> rw[←Fin.zero_eta]
      <;> split
      case' true.isFalse | false.isFalse => rw[←containsSeesThroughCast]
      case false.isFalse | false.isTrue =>
        rw[←get_zero_eq_root _ (Nat.succ_pos _), contains_as_root_left_right _ _ (Nat.succ_pos _)]
        left
        rw[root_unfold]
        rw[root_unfold]
      case' true.isFalse | true.isTrue =>
        rw[←get_zero_eq_root _ (Nat.succ_pos _), root_unfold]
        rw[contains_as_root_left_right _ _ (Nat.succ_pos _)]
      case true.isFalse =>
        right; left
        rw[left_unfold]
        exact heapPushContainsValue _ _ _
      case true.isTrue =>
        right;right
        rw[right_unfold]
        exact heapPushContainsValue _ _ _
    else
      cases le val v
      <;> dsimp
      case false | true =>
        have h₂₂ : index > ⟨0, h₁⟩ := Fin.pos_iff_ne_zero.mpr h₂
        if h₃ : index.val ≤ o then
          split
          case' isFalse => rw[←containsSeesThroughCast]
          case' isTrue | isFalse =>
            rw[get_left (.branch v l r p_le_o max_height_difference subtree_complete) index h₂₂ h₃]
            rw[contains_as_root_left_right _ _ (Nat.succ_pos _)]
            right; left
            rw[left_unfold]
            rw[left_unfold]
          case isTrue =>
            rw[contains_iff_index_exists _ _ (Nat.lt_of_lt_of_le (Fin.lt_iff_val_lt_val.mp h₂₂) h₃)]
            have : index.val - 1 < o := Nat.sub_one_lt_of_le h₂₂ h₃
            exists ⟨index.val - 1, this⟩
          case isFalse =>
            exact heapPushRetainsHeapValues le l _ ⟨index.val - 1, _⟩
        else
          split
          case' isFalse => rw[←containsSeesThroughCast]
          case' isTrue | isFalse =>
            rw[get_right (.branch v l r p_le_o max_height_difference subtree_complete) index (Nat.gt_of_not_le h₃)]
            rw[contains_as_root_left_right _ _ (Nat.succ_pos _)]
            right; right
            rw[right_unfold]
            rw[right_unfold]
            simp only [Nat.succ_eq_add_one, leftLen_unfold]
          case isTrue =>
            exact heapPushRetainsHeapValues le r _ ⟨index.val - o - 1, _⟩
          case isFalse =>
            have : (o.add p).succ = p + (o + 1) := (Nat.add_assoc p o 1).substr $ (Nat.add_comm o p).subst (motive := λx ↦ (o+p)+1 = x + 1) rfl
            have : p > 0 := by omega
            rw[contains_iff_index_exists _ _ this]
            exists ⟨index.val - o - 1, by omega⟩
