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

private theorem Option.is_some_map {α : Type u} {β : Type v} (f : α → β) (a : Option α) : (Option.map f a).isSome = a.isSome := by
  cases a
  case none => simp only [Option.map_none', Option.isSome_none]
  case some => simp only [Option.map_some', Option.isSome_some]

private theorem Option.orElse_is_some {α : Type u} (a b : Option α) : (HOrElse.hOrElse a λ_ ↦ b).isSome = (a.isSome || b.isSome) := by
  cases a
  case none => simp only [Option.none_orElse, Option.isSome_none, Bool.false_or]
  case some _ => simp only [Option.some_orElse, Option.isSome_some, Bool.true_or]

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
        rw[get_left (.branch v l r p_le_o max_height_difference subtree_complete) _ h₃₂ h₄]
        rw[left_unfold]
        have := indexOfNoneImpPredFalseAux l pred (currentIndex + 1)
        simp only [Option.isNone_iff_eq_none, Bool.not_eq_true] at this
        exact this h₂₂.left _
      else
        have h₄₂ : index > o := Nat.gt_of_not_le h₄
        rw[get_right (.branch v l r p_le_o max_height_difference subtree_complete) _ h₄₂]
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

private theorem indexOfSomeImpPredTrueAux2 {α : Type u} {p : Nat} {r : CompleteTree α p} {pred : α → Bool} (o q : Nat) : (Internal.indexOfAux r pred o).isSome → (Internal.indexOfAux r pred q).isSome := by
  unfold Internal.indexOfAux
  split
  case h_1 => intro hx; contradiction
  case h_2 p q v l r _ _ _ =>
    simp
    split
    case isTrue =>
      simp only [Option.isSome_some, imp_self]
    case isFalse =>
      repeat rw[Option.bind_some_eq_map]
      simp only [Option.map_map]
      simp only [Option.orElse_is_some, Bool.or_eq_true, Option.is_some_map]
      intro h₁
      cases h₁
      case inl h₁ =>
        left
        exact indexOfSomeImpPredTrueAux2 _ _ h₁
      case inr h₁ =>
        right
        exact indexOfSomeImpPredTrueAux2 _ _ h₁

private theorem indexOfSomeImpPredTrueAuxR {α : Type u} {p : Nat} (r : CompleteTree α p) (pred : α → Bool) {o : Nat} (index : Fin ((o+p)+1)) (h₁ : o + p + 1 > 0) (h₂ : (Internal.indexOfAux r pred 0).isSome) : ∀(a : Fin (p + (o + 1))), (Internal.indexOfAux r pred (o + 1) = some a ∧ Fin.ofNat' ↑a h₁ = index) → (Internal.indexOfAux r pred 0).get h₂ + o + 1 = index.val := by
  sorry

private theorem indexOfSomeImpPredTrueAuxL {α : Type u} {o : Nat} (l : CompleteTree α o) (pred : α → Bool) {p : Nat} (index : Fin ((o+p)+1)) (h₁ : o + p + 1 > 0) (h₂ : (Internal.indexOfAux l pred 0).isSome) : ∀(a : Fin ((o + 1))), (Internal.indexOfAux l pred 1 = some a ∧ Fin.ofNat' ↑a h₁ = index) → (Internal.indexOfAux l pred 0).get h₂ + 1 = index.val := by
  sorry

theorem indexOfSomeImpPredTrue {α : Type u} {n : Nat} (tree : CompleteTree α n) (pred : α → Bool) : (h₁ : (tree.indexOf pred).isSome) → pred (tree.get ((tree.indexOf pred).get h₁)) := by
  intro h₁
  generalize h₂ : (get ((tree.indexOf pred).get h₁) tree) = value
  unfold Option.get at h₂
  split at h₂
  rename_i d1 d2 index _ he₁ he₂
  clear d1 d2
  unfold indexOf CompleteTree.Internal.indexOfAux at he₁
  split at he₁
  case h_1 => contradiction
  case h_2 o p v l r _ _ _ _ =>
    simp at he₁
    cases h₃ : pred v
    case true =>
      simp only [h₃, ↓reduceIte, Option.some.injEq] at he₁
      subst index
      simp[Fin.ofNat'] at h₂
      rw[←Fin.zero_eta, ←get_zero_eq_root, root_unfold] at h₂
      subst v
      assumption
    case false =>
      --unfold HOrElse.hOrElse instHOrElseOfOrElse at he₁
      simp only [h₃, Bool.false_eq_true, ↓reduceIte, Option.bind_some_eq_map ] at he₁
      cases h₄ : (Option.map (fun a => Fin.ofNat' a _) (Option.map Fin.val (Internal.indexOfAux l pred 1)))
      case none =>
        rw[h₄, Option.none_orElse] at he₁
        simp only [Option.map_map, Option.map_eq_some', Function.comp_apply] at he₁
        rw[Nat.zero_add] at he₁
        have h₅ : (Internal.indexOfAux r pred (o + 1)).isSome := Option.isSome_iff_exists.mpr (Exists.imp (λx ↦ And.left) he₁)
        have h₆ := indexOfSomeImpPredTrueAux2 _ 0 h₅
        have h₇ := indexOfSomeImpPredTrueAuxR r pred index (Nat.succ_pos _) h₆
        have h₈ := he₁.elim h₇
        have h₉ := indexOfSomeImpPredTrue r pred h₆
        rw[get_right' _ (Nat.lt_of_add_right $ Nat.lt_of_succ_le $ Nat.le_of_eq h₈)] at h₂
        simp[←h₈] at h₂
        rw[←h₂]
        have : ↑((Internal.indexOfAux r pred 0).get h₆) + o + 1 - o - 1 = ↑((Internal.indexOfAux r pred 0).get h₆) := by omega
        simp[this]
        exact h₉
      case some lindex =>
        rw[h₄, Option.some_orElse, Option.some_inj] at he₁
        simp only [Option.map_map, Option.map_eq_some', Function.comp_apply] at h₄
        subst lindex
        have h₅ : (Internal.indexOfAux l pred 1).isSome := Option.isSome_iff_exists.mpr (Exists.imp (λx ↦ And.left) h₄)
        have h₆ := indexOfSomeImpPredTrueAux2 _ 0 h₅
        have h₇ := indexOfSomeImpPredTrueAuxL l pred index (Nat.succ_pos _) h₆
        have h₈ := h₄.elim h₇
        have h₉ := indexOfSomeImpPredTrue l pred h₆
        have h₁₀ : index.val ≤ o := Nat.le_trans (Nat.le_of_eq h₈.symm) (((Internal.indexOfAux l pred 0).get h₆).isLt)
        rw[get_left' _ (by simp[Fin.lt_iff_val_lt_val, ←h₈]) h₁₀] at h₂
        simp[←h₈] at h₂
        rw[←h₂]
        exact h₉
