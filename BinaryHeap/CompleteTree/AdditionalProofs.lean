import BinaryHeap.CompleteTree.Lemmas
import BinaryHeap.CompleteTree.HeapOperations

namespace BinaryHeap

/--Shows that the index and value returned by heapRemoveLastWithIndex are consistent.-/
private theorem CompleteTree.heapRemoveLastWithIndexReturnsItemAtIndex {α : Type u} {o : Nat} (heap : CompleteTree α (o+1)) : heap.get heap.heapRemoveLastWithIndex.snd.snd = heap.heapRemoveLastWithIndex.snd.fst := by
  unfold CompleteTree.heapRemoveLastWithIndex CompleteTree.Internal.heapRemoveLastAux
  split
  rename_i n m v l r m_le_n max_height_difference subtree_full
  simp only [Nat.add_eq, Fin.zero_eta, Fin.isValue, decide_eq_true_eq, Fin.castLE_succ]
  split
  case isTrue n_m_zero =>
    unfold get
    split
    case h_1 nn mm vv ll rr mm_le_nn _ _ _ _ he₁ he₂ =>
      have h₁ : n = 0 := And.left $ Nat.add_eq_zero.mp n_m_zero.symm
      have h₂ : m = 0 := And.right $ Nat.add_eq_zero.mp n_m_zero.symm
      have h₃ : nn = 0 := And.left (Nat.add_eq_zero.mp $ Eq.symm $ (Nat.zero_add 0).subst (motive := λx ↦ x = nn + mm) $ h₂.subst (motive := λx ↦ 0 + x = nn + mm) (h₁.subst (motive := λx ↦ x + m = nn + mm) he₁))
      have h₄ : mm = 0 := And.right (Nat.add_eq_zero.mp $ Eq.symm $ (Nat.zero_add 0).subst (motive := λx ↦ x = nn + mm) $ h₂.subst (motive := λx ↦ 0 + x = nn + mm) (h₁.subst (motive := λx ↦ x + m = nn + mm) he₁))
      subst n m nn mm
      exact And.left $ CompleteTree.branch.inj (eq_of_heq he₂.symm)
    case h_2 =>
      omega -- to annoying to deal with Fin.ofNat... There's a hypothesis that says 0 = ⟨1,_⟩.
  case isFalse n_m_not_zero =>
    unfold get
    split
    case h_1 nn mm vv ll rr mm_le_nn max_height_difference_2 subtree_full2 _ he₁ he₂ he₃ =>
      --aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
      --okay, I know that he₁ is False.
      --but reducing this wall of text to something the computer understands - I am frightened.
      exfalso
      revert he₁
      split
      case' isTrue => cases l; case leaf hx => exact absurd hx.left $ Nat.not_lt_zero m
      all_goals
        apply Fin.ne_of_val_ne
        simp only [Fin.isValue, Fin.val_succ, Fin.coe_castLE, Fin.coe_addNat, Nat.add_one_ne_zero, not_false_eq_true]
      --okay, this wasn't that bad
    case h_2 j j_lt_n_add_m nn mm vv ll rr mm_le_nn max_height_difference_2 subtree_full2 heap he₁ he₂ he₃ =>
      --he₁ relates j to the other indices. This is the important thing here.
      --it should be reducible to j = (l or r).heap.heapRemoveLastWithIndex.snd.snd
      --or something like it.

      --but first, let's get rid of mm and nn, and vv while at it.
      -- which are equal to m, n, v, but we need to deduce this from he₃...
      have : n = nn := heqSameLeftLen (congrArg (·+1) he₂) (by simp_arith) he₃
      have : m = mm := heqSameRightLen (congrArg (·+1) he₂) (by simp_arith) he₃
      subst nn mm
      simp only [heq_eq_eq, branch.injEq] at he₃
      -- yeah, no more HEq fuglyness!
      have : v = vv := he₃.left
      have : l = ll := he₃.right.left
      have : r = rr := he₃.right.right
      subst vv ll rr
      split at he₁
      <;> rename_i goLeft
      <;> simp only [goLeft, and_self, ↓reduceDite, Fin.isValue]
      case' isTrue =>
        cases l;
        case leaf => exact absurd goLeft.left $ Nat.not_lt_zero m
        rename_i o p _ _ _ _ _ _ _
      case' isFalse =>
        cases r;
        case leaf => simp (config := { ground := true }) only [and_true, Nat.not_lt, Nat.le_zero_eq] at goLeft;
                     exact absurd ((Nat.add_zero n).substr goLeft.symm) n_m_not_zero
      all_goals
        have he₁ := Fin.val_eq_of_eq he₁
        simp only [Fin.isValue, Fin.val_succ, Fin.coe_castLE, Fin.coe_addNat, Nat.reduceEqDiff] at he₁
        have : max_height_difference_2 = max_height_difference := rfl
        have : subtree_full2 = subtree_full := rfl
        subst max_height_difference_2 subtree_full2
        rename_i del1 del2
        clear del1 del2
      case' isTrue =>
        have : j < o + p + 1 := by omega --from he₁. It has j = (blah : Fin (o+p+1)).val
      case' isFalse =>
        have : ¬j<n := by omega --from he₁. It has j = something + n.
      all_goals
        simp only [this, ↓reduceDite, Nat.pred_succ, Fin.isValue]
        subst j -- overkill, but unlike rw it works
        simp only [Nat.pred_succ, Fin.isValue, Nat.add_sub_cancel, Fin.eta]
        apply heapRemoveLastWithIndexReturnsItemAtIndex
        done
