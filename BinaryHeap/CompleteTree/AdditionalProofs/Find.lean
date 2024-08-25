import BinaryHeap.CompleteTree.AdditionalOperations
import BinaryHeap.CompleteTree.AdditionalProofs.Get

namespace BinaryHeap.CompleteTree.AdditionalProofs

private theorem Option.orElse_result_none_both_none : Option.orElse a (λ_↦y) = none → a = none ∧ y = none := by
  intro h₁
  cases a
  case some => contradiction
  case none =>
    simp
    cases y
    case some => contradiction
    case none => rfl

private theorem Option.bind_some_eq_map {α β : Type u} (f : α → β) (a : Option α) : Option.bind a (λy ↦ some (f y)) = Option.map f a := by
  unfold Option.bind Option.map
  cases a
  case none => rfl
  case some => rfl

private theorem indexOfNoneImpPredFalseAux {α : Type u} {n : Nat} (tree : CompleteTree α n) (pred : α → Bool) (currentIndex : Nat) : (CompleteTree.Internal.indexOfAux tree pred currentIndex).isNone → ∀(index : Fin n), ¬pred (tree.get index) := by
  if h₁ : n > 0 then
    intro h₂
    intro index
    simp only [Option.isNone_iff_eq_none] at h₂
    simp only [Bool.not_eq_true]
    unfold CompleteTree.Internal.indexOfAux at h₂
    split at h₂ ; contradiction
    rename_i o p v l r p_le_o max_height_difference subtree_complete
    split at h₂; contradiction
    unfold HOrElse.hOrElse instHOrElseOfOrElse at h₂
    unfold OrElse.orElse Option.instOrElse at h₂
    simp only [Nat.add_zero, Nat.reduceAdd, Option.pure_def, Option.bind_eq_bind] at h₂
    have h₂₂ := Option.orElse_result_none_both_none h₂
    repeat rw[Option.bind_some_eq_map] at h₂₂
    simp only [Option.map_eq_none'] at h₂₂
    if h₃ : index = ⟨0,h₁⟩ then
      subst index
      rw[←get_zero_eq_root, root_unfold]
      rename_i solution
      simp only [Bool.not_eq_true] at solution
      exact solution
    else
      have h₃₂ : index > ⟨0,h₁⟩ := Fin.pos_iff_ne_zero.mpr h₃
      if h₄ : index ≤ o then
        rw[get_left (.branch v l r p_le_o max_height_difference subtree_complete) _ h₁ h₃₂ h₄]
        rw[left_unfold]
        have := indexOfNoneImpPredFalseAux l pred (currentIndex + 1)
        simp only [Option.isNone_iff_eq_none, Bool.not_eq_true] at this
        exact this h₂₂.left _
      else
        have h₄₂ : index > o := Nat.gt_of_not_le h₄
        rw[get_right (.branch v l r p_le_o max_height_difference subtree_complete) _ (Nat.succ_pos _) h₄₂]
        rw[right_unfold]
        have := indexOfNoneImpPredFalseAux r pred (currentIndex + o + 1)
        simp only [Option.isNone_iff_eq_none, Bool.not_eq_true] at this
        exact this h₂₂.right _
  else
    simp at h₁
    intro h₂
    intro hx
    subst h₁
    cases hx
    contradiction

theorem indexOfNoneImpPredFalse {α : Type u} {n : Nat} (tree : CompleteTree α n) (pred : α → Bool) : (tree.indexOf pred).isNone → ∀(index : Fin n), ¬pred (tree.get index) :=
  indexOfNoneImpPredFalseAux tree pred 0

theorem indexOfSomeImpPredTrue {α : Type u} {n : Nat} (tree : CompleteTree α n) (pred : α → Bool) : (h₁ : (tree.indexOf pred).isSome) → pred (tree.get ((tree.indexOf pred).get h₁)) := by
  sorry
