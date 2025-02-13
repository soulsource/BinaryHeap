import BinaryHeap.CompleteTree.AdditionalOperations
import BinaryHeap.CompleteTree.Lemmas

namespace BinaryHeap.CompleteTree.AdditionalProofs

theorem get_zero_eq_root {α : Type u} {n : Nat} (tree : CompleteTree α n) (h₁ : n > 0): tree.root h₁ = tree.get ⟨0,h₁⟩ :=
  match h₂ : n, h₃ : (⟨0,h₁⟩ : Fin n), tree with
  | (_+_+1), 0, .branch v _ _ _ _ _ => rfl
  | nn+1, ⟨j+1,h₄⟩, _ => by
    subst h₂
    simp only [Nat.succ_eq_add_one, Fin.zero_eta, heq_eq_eq, Fin.ext_iff, Fin.val_zero,
      Nat.self_eq_add_left, Nat.add_one_ne_zero] at h₃

theorem get_right {α : Type u} {n : Nat} (tree : CompleteTree α n) (index : Fin n) (h₂ : index > tree.leftLen (Nat.zero_lt_of_lt index.isLt))
  : have h₁ : n > 0 := Nat.zero_lt_of_lt index.isLt
    have h₃ : ↑index - tree.leftLen h₁ - 1 < tree.rightLen h₁ := by
      revert h₂
      unfold leftLen rightLen length
      split
      intro h₂
      rename_i o p v l r _ _ _
      have h₃ := index.isLt
      apply Nat.sub_lt_right_of_lt_add
      omega
      apply Nat.sub_lt_right_of_lt_add
      omega
      have : p+1+o = (o.add p).succ := by simp_arith
      rw[this]
      assumption
    tree.get index = (tree.right h₁).get ⟨index.val - (tree.leftLen h₁) - 1, h₃⟩
  :=
  match n, index, tree with
  | (o+p+1), ⟨j+1,h₃⟩, .branch _ _ r _ _ _ =>
    if h₄ : j < o then
      absurd h₄ $ Nat.not_lt_of_ge (Nat.le_of_lt_succ h₂)
    else by
      simp only[right_unfold, leftLen_unfold]
      have : j + 1 - o - 1 = j - o := by omega
      simp only [get, reduceDIte, this, h₄]

theorem get_right' {α : Type u} {n m : Nat} {v : α} {l : CompleteTree α n} {r : CompleteTree α m} {m_le_n : m ≤ n} {max_height_diff : n < 2 * (m + 1)} {subtree_complete : (n + 1).isPowerOfTwo ∨ (m + 1).isPowerOfTwo} (index : Fin (n + m + 1)) (h₁ : index > n) :
  have h₂ : ↑index - n - 1 < m := by
    have h₃ := index.isLt
    apply Nat.sub_lt_right_of_lt_add
    omega
    apply Nat.sub_lt_right_of_lt_add
    omega
    have : m + 1 + n = n + m + 1 := by simp_arith
    rw[this]
    assumption
  (branch v l r m_le_n max_height_diff subtree_complete).get index = r.get ⟨index.val - n - 1, h₂⟩
:=
  get_right (branch v l r m_le_n max_height_diff subtree_complete) index h₁

theorem get_left {α : Type u} {n : Nat} (tree : CompleteTree α n) (index : Fin n) (h₂ : index > ⟨0, (Nat.zero_lt_of_lt index.isLt)⟩) (h₃ : index ≤ tree.leftLen (Nat.zero_lt_of_lt index.isLt)) :
  have h₁ : n > 0 := Nat.zero_lt_of_lt index.isLt
  have h₃ : ↑index - 1 < tree.leftLen h₁ := Nat.lt_of_lt_of_le (Nat.pred_lt_self h₂) h₃
  tree.get index = (tree.left h₁).get ⟨index.val - 1, h₃⟩
:=
    match n, index, tree with
  | (o+p+1), ⟨j+1,h₅⟩, .branch _ l _ _ _ _ =>
    if h₄ : j < o then by
      simp only[left_unfold, leftLen_unfold]
      have : j + 1 - o - 1 = j - o := by omega
      simp only [get, h₄, reduceDIte, Nat.add_one_sub_one]
    else
      absurd (Nat.lt_of_succ_le h₃) h₄

theorem get_left' {α : Type u} {n m : Nat} {v : α} {l : CompleteTree α n} {r : CompleteTree α m} {m_le_n : m ≤ n} {max_height_diff : n < 2 * (m + 1)} {subtree_complete : (n + 1).isPowerOfTwo ∨ (m + 1).isPowerOfTwo} (index : Fin (n + m + 1)) (h₁ : index > ⟨0, Nat.succ_pos _⟩) (h₂ : index ≤ n) :
  have h₃ : ↑index - 1 < n := Nat.lt_of_lt_of_le (Nat.pred_lt_self h₁) h₂
  (branch v l r m_le_n max_height_diff subtree_complete).get index = l.get ⟨index.val - 1, h₃⟩
:=
  get_left (branch v l r m_le_n max_height_diff subtree_complete) index h₁ h₂

theorem get_unfold {α : Type u} {n : Nat} (tree : CompleteTree α n) (index : Fin n)
  :
  have h₁ : n > 0 := (Nat.zero_lt_of_lt index.isLt)
  tree.get index =
    if h₂ : index = ⟨0, h₁⟩ then
      tree.root h₁
    else if h₃ : index ≤ tree.leftLen h₁ then
      have h₃ : ↑index - 1 < tree.leftLen h₁ := Nat.lt_of_lt_of_le (Nat.pred_lt_self $ Nat.zero_lt_of_ne_zero $ Fin.val_ne_iff.mpr h₂) h₃
      (tree.left h₁).get ⟨index.val - 1, h₃⟩
    else
      have h₃ : ↑index - tree.leftLen h₁ - 1 < tree.rightLen h₁ := by
        revert h₃
        unfold leftLen rightLen length
        split
        intro h₂
        rename_i o p v l r _ _ _ _ _
        have h₃ := index.isLt
        apply Nat.sub_lt_right_of_lt_add
        omega
        apply Nat.sub_lt_right_of_lt_add
        omega
        have : p+1+o = (o.add p).succ := by simp_arith
        rw[this]
        assumption
      (tree.right h₁).get ⟨index.val - (tree.leftLen h₁) - 1, h₃⟩
  :=
  have h₁ : n > 0 := (Nat.zero_lt_of_lt index.isLt)
  if h₂ : index = ⟨0, h₁⟩ then by
    simp only [h₂]
    exact Eq.symm $ get_zero_eq_root _ _
  else if h₃ : index ≤ tree.leftLen h₁ then by
    simp [h₂, h₃]
    exact get_left tree index (Nat.zero_lt_of_ne_zero $ Fin.val_ne_iff.mpr h₂) h₃
  else by
    simp [h₂, h₃]
    exact get_right tree index (Nat.gt_of_not_le h₃)

theorem get_unfold' {α : Type u} {n m : Nat} {v : α} {l : CompleteTree α n} {r : CompleteTree α m} {m_le_n : m ≤ n} {max_height_diff : n < 2 * (m + 1)} {subtree_complete : (n + 1).isPowerOfTwo ∨ (m + 1).isPowerOfTwo} (index : Fin (n + m + 1)) :
  (branch v l r m_le_n max_height_diff subtree_complete).get index = if h₂ : index = ⟨0, Nat.zero_lt_of_lt index.isLt⟩ then
      v
    else if h₃ : index ≤ n then
      have h₃ : ↑index - 1 < n := Nat.lt_of_lt_of_le (Nat.pred_lt_self $ Nat.zero_lt_of_ne_zero $ Fin.val_ne_iff.mpr h₂) h₃
      l.get ⟨index.val - 1, h₃⟩
    else
      have h₃ : ↑index - n - 1 < m := by omega
      r.get ⟨index.val - n - 1, h₃⟩
  :=
    get_unfold _ _
