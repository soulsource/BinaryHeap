import BinaryHeap.CompleteTree.AdditionalOperations
import BinaryHeap.CompleteTree.Lemmas

namespace BinaryHeap.CompleteTree.AdditionalProofs

theorem get_right {α : Type u} {n : Nat} (tree : CompleteTree α n) (index : Fin n) (h₁ : n > 0) (h₂ : index > tree.leftLen h₁) :
  have h₃ : ↑index - tree.leftLen h₁ - 1 < tree.rightLen h₁ := by
    revert h₂
    unfold leftLen rightLen length
    split
    intro h₂
    rename_i o p v l r _ _ _ _
    have h₃ := index.isLt
    apply Nat.sub_lt_right_of_lt_add
    omega
    apply Nat.sub_lt_right_of_lt_add
    omega
    have : p+1+o = (o.add p).succ := by simp_arith
    rw[this]
    assumption
  have h₄ : tree.rightLen h₁ > 0 := Nat.zero_lt_of_lt h₃
  tree.get index h₁ = (tree.right h₁).get ⟨index.val - (tree.leftLen h₁) - 1, h₃⟩ h₄
:=
  match n, tree with
  | (o+p+1), .branch v l r _ _ _ => by
    simp[right_unfold, leftLen_unfold]
    rw[leftLen_unfold] at h₂
    generalize hnew : get ⟨↑index - o - 1, _⟩ r _ = new
    unfold get get'
    split
    case h_1 =>
      contradiction
    case h_2 j h₃ o2 p2 v2 l2 r2 _ _ _ d1 he₁ he₂ _ =>
      clear d1
      have : o = o2 := heqSameLeftLen (congrArg Nat.succ he₁) (Nat.succ_pos _) he₂
      have : p = p2 := heqSameRightLen (congrArg Nat.succ he₁) (Nat.succ_pos _) he₂
      subst o2 p2
      simp at he₂
      have : v = v2 := he₂.left
      have : l = l2 := he₂.right.left
      have : r = r2 := he₂.right.right
      subst r2 l2 v2
      simp_all
      have : ¬j < o := by simp_arith[h₂]
      simp[this]
      cases p <;> simp
      case zero =>
        omega
      case succ pp _ _ _ _ _ _ =>
        have : j + 1 - o - 1 = j - o := by omega
        simp[this] at hnew
        rw[get_eq_get']
        assumption

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
  (branch v l r m_le_n max_height_diff subtree_complete).get index (Nat.succ_pos _) = r.get ⟨index.val - n - 1, h₂⟩  (Nat.zero_lt_of_lt h₂)
:=
  get_right (branch v l r m_le_n max_height_diff subtree_complete) index (Nat.succ_pos _) h₁
