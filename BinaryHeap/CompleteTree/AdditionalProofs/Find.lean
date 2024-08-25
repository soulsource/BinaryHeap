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

private theorem indexOfNoneImpPredFalseAux {α : Type u} {n : Nat} (tree : CompleteTree α n) (h₁ : n > 0) (pred : α → Bool) (currentIndex : Nat) : (CompleteTree.Internal.indexOfAux tree pred currentIndex).isNone → ∀(index : Fin n), ¬pred (tree.get index h₁) := by
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
      have : o > 0 := by omega
      have := indexOfNoneImpPredFalseAux l this pred (currentIndex + 1)
      simp only [Option.isNone_iff_eq_none, Bool.not_eq_true] at this
      exact this h₂₂.left _
    else
      have h₄₂ : index > o := Nat.gt_of_not_le h₄
      rw[get_right (.branch v l r p_le_o max_height_difference subtree_complete) _ (Nat.succ_pos _) h₄₂]
      rw[right_unfold]
      -- if you are wondering: this is needed to make omega work below.
      have : (o.add p).succ = p + (o + 1) := (Nat.add_assoc p o 1).substr $ (Nat.add_comm o p).subst (motive := λx ↦ (o+p)+1 = x + 1) rfl
      have : p > 0 := by omega
      have := indexOfNoneImpPredFalseAux r this pred (currentIndex + o + 1)
      simp only [Option.isNone_iff_eq_none, Bool.not_eq_true] at this
      exact this h₂₂.right _

theorem indexOfNoneImpPredFalse {α : Type u} {n : Nat} (tree : CompleteTree α n) (h₁ : n > 0) (pred : α → Bool) : (tree.indexOf pred).isNone → ∀(index : Fin n), ¬pred (tree.get index h₁) :=
  indexOfNoneImpPredFalseAux tree h₁ pred 0
