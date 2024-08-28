import BinaryHeap.CompleteTree.AdditionalOperations
import BinaryHeap.CompleteTree.AdditionalProofs.Get

namespace BinaryHeap.CompleteTree.AdditionalProofs

private theorem if_get_eq_contains {α : Type u} {n : Nat} (tree : CompleteTree α n) (element : α) (index : Fin n) : tree.get index = element → tree.contains element := by
    rw[get_unfold]
    rw[contains_as_root_left_right]
    intro h₁
    split at h₁
    case isTrue =>
      left
      assumption
    case isFalse h =>
      have _termination : index.val ≠ 0 := Fin.val_ne_iff.mpr h
      right
      simp only at h₁
      split at h₁
      case' isTrue => left
      case' isFalse => right
      all_goals
        revert h₁
        apply if_get_eq_contains
termination_by index.val

private theorem if_contains_get_eq_auxl {α : Type u} {n : Nat} (tree : CompleteTree α n) (element : α) (h₁ : n > 0):
  ∀(indexl : Fin (tree.leftLen h₁)), (tree.left _).get indexl = element → ∃(index : Fin n), tree.get index = element
:= by
  intro indexl
  let index : Fin n := indexl.succ.castLT (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt indexl.isLt) (leftLenLtN tree h₁))
  intro prereq
  exists index
  have h₂ : index > ⟨0,h₁⟩ := Nat.zero_lt_of_ne_zero $ Fin.val_ne_iff.mpr $ Fin.succ_ne_zero _
  have h₃ : index.val ≤ tree.leftLen h₁ := Nat.succ_le_of_lt indexl.isLt
  rw[get_left _ _ h₂ h₃]
  exact prereq

private theorem if_contains_get_eq_auxr {α : Type u} {n : Nat} (tree : CompleteTree α n) (element : α) (h₁ : n > 0):
  ∀(indexr : Fin (tree.rightLen h₁)), (tree.right _).get indexr = element → ∃(index : Fin n), tree.get index = element
:= by
  intro indexr
  let index : Fin n := ⟨(tree.leftLen h₁ + indexr.val + 1), by
    have h₂ : tree.leftLen h₁ + tree.rightLen _ + 1 = tree.length := Eq.symm $ lengthEqLeftRightLenSucc tree _
    rw[length] at h₂
    have h₃ : tree.leftLen h₁ + indexr.val + 1 < tree.leftLen h₁ + tree.rightLen h₁ + 1 := by
      apply Nat.succ_lt_succ
      apply Nat.add_lt_add_left
      exact indexr.isLt
    exact Nat.lt_of_lt_of_eq h₃ h₂
  ⟩
  intro prereq
  exists index
  have h₂ : tree.leftLen h₁ < tree.leftLen h₁ + indexr.val + 1 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (Nat.lt_succ_self _)
  rw[get_right _ index h₂]
  have : index.val - tree.leftLen h₁ - 1 = indexr.val :=
    have : index.val = tree.leftLen h₁ + indexr.val + 1 := rfl
    have : index.val = indexr.val + tree.leftLen h₁ + 1 := (Nat.add_comm indexr.val (tree.leftLen h₁)).substr this
    have : index.val - (tree.leftLen h₁ + 1) = indexr.val := Nat.sub_eq_of_eq_add this
    (Nat.sub_sub _ _ _).substr this
  simp only[this]
  assumption

private theorem if_contains_get_eq {α : Type u} {n : Nat} (tree : CompleteTree α n) (element : α) (h₁ : tree.contains element) : ∃(index : Fin n), tree.get index = element := by
    unfold contains at h₁
    match n, tree with
    | 0, .leaf => contradiction
    | (o+p+1), .branch v l r o_le_p max_height_diff subtree_complete =>
    cases h₁
    case inl h₂ =>
      exists 0
    case inr h₂ =>
      cases h₂
      case inl h₂ =>
        have h₄ := if_contains_get_eq l element h₂
        have h₅ := if_contains_get_eq_auxl (.branch v l r o_le_p max_height_diff subtree_complete) element (Nat.succ_pos _)
        apply h₄.elim
        assumption
      case inr h₂ =>
        have h₄ := if_contains_get_eq r element h₂
        have h₅ := if_contains_get_eq_auxr (.branch v l r o_le_p max_height_diff subtree_complete) element (Nat.succ_pos _)
        apply h₄.elim
        assumption


theorem contains_iff_index_exists {α : Type u} {n : Nat} (tree : CompleteTree α n) (element : α) : tree.contains element ↔ ∃ (index : Fin n), tree.get index = element := by
  constructor
  case mpr =>
    simp only [forall_exists_index]
    exact if_get_eq_contains tree element
  case mp =>
    exact if_contains_get_eq tree element
