import BinaryHeap.CompleteTree.HeapOperations
import BinaryHeap.CompleteTree.HeapProofs.HeapUpdateRoot
import BinaryHeap.CompleteTree.Lemmas
import BinaryHeap.CompleteTree.AdditionalProofs.Get
import BinaryHeap.CompleteTree.AdditionalProofs.Contains

namespace BinaryHeap.CompleteTree.AdditionalProofs

-- That heapUpdateRootReturnsRoot is already proven in HeapProofs.HeapUpdateRoot
-- but still, re-export it.

abbrev heapUpdateRootReturnsRoot {α : Type u} {n : Nat} (le : α → α → Bool) (value : α) (heap : CompleteTree α n) (h₁ : n > 0)  := CompleteTree.heapUpdateRootReturnsRoot le value heap h₁

/--
  Shows that each element contained before updating the root that is not the root is still contained after updating the root.
  This is not a rigorous proof that the rest of the tree remained unchanged. See comment on heapPopOnlyRemovesRoot.
  Imho it is still a good indication that there are no obvious bugs.
  -/
theorem heapUpdateRootOnlyUpdatesRoot {α : Type u} {n : Nat} (le : α → α → Bool) (tree : CompleteTree α n) (h₁ : n > 0) (index : Fin n) (h₂ : index ≠ ⟨0, h₁⟩) (value : α) : (tree.heapUpdateRoot le value h₁).fst.contains $ tree.get index h₁ := by
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
          cases j
          case zero =>
            rw[heapUpdateRootReturnsRoot]
            rw[get_zero_eq_root]
            unfold get; simp only
            rw[h₃, contains_as_root_left_right _ _ (Nat.succ_pos _)]
            left
            rw[root_unfold]
          case succ jj h₄ =>
            have h₅ : oo = 0 := by omega
            have h₆ : jj < oo := Nat.lt_of_succ_lt_succ this
            have h₆ : jj < 0 := h₅.subst h₆
            exact absurd h₆ $ Nat.not_lt_zero jj
        case true h₄ _ _ _ _ _=>
          rw[contains_as_root_left_right _ _ h₄]
          right
          left
          rewrite[contains_iff_index_exists']
          exists ⟨j,this⟩
      case succ pp _ _ _ _ _ _ _ _ =>
        simp
        if h : j < oo + 1 then
          -- index was in l
          simp only [h, ↓reduceDIte] at h₃
          split
          case isTrue =>
            simp
            rw[contains_as_root_left_right _ _ (Nat.succ_pos _)]
            right
            left
            rw[←h₃, contains_iff_index_exists', left_unfold]
            exists ⟨j,h⟩
          case isFalse =>
            split
            <;> rw[heapUpdateRootReturnsRoot]
            case isTrue =>
              -- l.root gets moved up
              simp only
              cases j
              case zero =>
                rw[get_zero_eq_root]
                unfold get
                simp only
                rw[h₃, contains_as_root_left_right _ _ (Nat.succ_pos _)]
                left
                rw[root_unfold]
              case succ jj _ =>
                --recursion
                rw[contains_as_root_left_right _ _ (Nat.succ_pos _)]
                right
                left
                rw[←h₃, left_unfold]
                have : oo + 1 < oo + 1 + pp + 1 + 1 := by simp_arith --termination
                apply heapUpdateRootOnlyUpdatesRoot
                apply Fin.ne_of_val_ne
                simp only [Nat.add_one_ne_zero, not_false_eq_true]
            case isFalse =>
              -- r.root gets moved up
              rw[contains_as_root_left_right _ _ (Nat.succ_pos _)]
              right
              left
              simp only [left_unfold]
              rw[←h₃, contains_iff_index_exists']
              exists ⟨j, h⟩
        else
          -- index was in r
          simp only [h, ↓reduceDIte] at h₃
          rename_i h₄ _ _ _ _
          have h₄ : j - (oo + 1) < pp + 1 := Nat.sub_lt_left_of_lt_add (Nat.le_of_not_gt h) (Nat.lt_of_succ_lt_succ h₄)
          split
          case isTrue h₄ _ _ _ _ _ =>
            simp
            rw[contains_as_root_left_right _ _ (Nat.succ_pos _)]
            right
            right
            rw[←h₃, contains_iff_index_exists', right_unfold]
            exists ⟨j-(oo+1), h₄⟩
          case isFalse =>
            split
            <;> rw[heapUpdateRootReturnsRoot]
            case isTrue =>
              --l.root gets moved up
              rw[contains_as_root_left_right _ _ (Nat.succ_pos _)]
              right
              right
              simp only [right_unfold]
              rw[←h₃, contains_iff_index_exists']
              exists ⟨j- (oo + 1), h₄⟩
            case isFalse =>
              --r.root gets moved up
              simp only
              generalize h₅ : j - (oo + 1) = jr
              simp only [h₅] at h₃
              have h₄ : jr < pp+1 := h₅.subst (motive := λx ↦ x < pp+1) h₄
              cases jr
              case zero =>
                rw[get_zero_eq_root]
                unfold get
                simp only
                rw[h₃, contains_as_root_left_right _ _ (Nat.succ_pos _)]
                left
                rw[root_unfold]
              case succ jjr =>
                rw[contains_as_root_left_right _ _ (Nat.succ_pos _)]
                right
                right
                rw[←h₃, right_unfold]
                have : pp + 1 < oo + 1 + pp + 1 + 1 := by simp_arith --termination
                apply heapUpdateRootOnlyUpdatesRoot
                apply Fin.ne_of_val_ne
                simp only [Nat.add_one_ne_zero, not_false_eq_true]
termination_by n

theorem heapUpdateRootContainsUpdatedElement {α : Type u} {n : Nat} (tree : CompleteTree α n) (le : α → α → Bool) (value : α) (h₁ : n > 0): (tree.heapUpdateRoot le value h₁).fst.contains value := by
  unfold heapUpdateRoot
  split
  rename_i o p v l r _ _ _ h₁
  cases o <;> simp only [Nat.add_eq, Nat.succ_eq_add_one, Nat.add_one_ne_zero, ↓reduceDIte]
  case zero => simp only [contains, true_or]
  case succ oo _ _ _ =>
    cases p <;> simp only [Nat.add_one_ne_zero, ↓reduceDIte]
    case zero =>
      split
      case isTrue => simp only [contains, true_or]
      case isFalse =>
        rw[contains_as_root_left_right _ _ (Nat.succ_pos _)]
        right
        left
        rw[left_unfold]
        exact heapUpdateRootContainsUpdatedElement l le value _
    case succ pp _ _ _ =>
      split
      case isTrue => simp only [contains, true_or]
      case isFalse =>
        split
        case isTrue =>
          rw[contains_as_root_left_right _ _ (Nat.succ_pos _)]
          right
          left
          rw[left_unfold]
          exact heapUpdateRootContainsUpdatedElement l le value _
        case isFalse =>
          rw[contains_as_root_left_right _ _ (Nat.succ_pos _)]
          right
          right
          rw[right_unfold]
          exact heapUpdateRootContainsUpdatedElement r le value _
