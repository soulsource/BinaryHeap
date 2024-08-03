import BinaryHeap.CompleteTree.HeapOperations
import BinaryHeap.CompleteTree.HeapProofs.HeapUpdateRoot
import BinaryHeap.CompleteTree.Lemmas

namespace BinaryHeap.CompleteTree.AdditionalProofs

-- That heapUpdateRootReturnsRoot is already proven in HeapProofs.HeapUpdateRoot

theorem HeapUpdateRootOnlyUpdatesRoot {α : Type u} {n : Nat} (le : α → α → Bool) (tree : CompleteTree α n) (h₁ : n > 0) (index : Fin n) (h₂ : index ≠ ⟨0, h₁⟩) (value : α) : (tree.heapUpdateRoot le value h₁).fst.contains $ tree.get index h₁ := by
  generalize h₃ : (get index tree h₁) = oldVal
  unfold get at h₃
  unfold heapUpdateRoot
  split
  simp at h₃
  rename_i o p v l r p_le_o _ _ _
  cases o
  case zero =>
    have : p = 0 := Nat.eq_zero_of_le_zero p_le_o
    subst p
    exact absurd (Fin.fin_one_eq_zero index) h₂
  case succ oo _ _ _ =>
    simp
    unfold get' at h₃
    split at h₃
    case h_1 => omega
    case h_2 j _ o2 p2 v2 l2 r2 _ _ _ _ he1 he2 =>
      have : oo+1 = o2 := heqSameLeftLen (congrArg Nat.succ he1) (by simp_arith) he2
      have : p = p2 := heqSameRightLen (congrArg Nat.succ he1) (by simp_arith) he2
      subst o2
      subst p2
      simp at he2
      have := he2.left
      have := he2.right.left
      have := he2.right.right
      subst v2 l2 r2
      simp at h₃
      cases p
      case zero =>
        have : j < oo + 1 := by omega
        simp[this] at h₃ ⊢
        cases le value (l.root _) <;> simp
        case false =>

          sorry
        case true =>
          --rewrite h₃ into l.contains oldVal somehow.
          sorry
      case succ pp => sorry
