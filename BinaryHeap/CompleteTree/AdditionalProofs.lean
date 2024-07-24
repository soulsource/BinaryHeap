import BinaryHeap.CompleteTree.Lemmas
import BinaryHeap.CompleteTree.AdditionalOperations
import BinaryHeap.CompleteTree.HeapOperations

namespace BinaryHeap.CompleteTree.AdditionalProofs

private theorem if_get_eq_contains {α : Type u} {o : Nat} (tree : CompleteTree α (o+1)) (element : α) (index : Fin (o+1)) : tree.get' index = element → tree.contains element := by
    unfold get' contains
    simp only [Nat.succ_eq_add_one, Fin.zero_eta, Nat.add_eq, ne_eq]
    split
    case h_1 p q v l r _ _ _ _ =>
      intro h₁
      split; omega
      rename α => vv
      rename_i hsum heq
      have h₂ := heqSameRoot (hsum) (Nat.succ_pos (p+q)) heq
      rw[root_unfold] at h₂
      rw[root_unfold] at h₂
      simp only [←h₂, h₁, true_or]
    case h_2 index p q v l r _ _ _ _ h₃ =>
      intro h₄
      split ; rename_i hx _; exact absurd hx (Nat.succ_ne_zero _)
      case h_2 pp qq vv ll rr _ _  _ h₅ heq =>
      have : p = pp := heqSameLeftLen h₅ (Nat.succ_pos _) heq
      have : q = qq := heqSameRightLen h₅ (Nat.succ_pos _) heq
      subst pp qq
      simp only [Nat.add_eq, Nat.succ_eq_add_one, heq_eq_eq, branch.injEq] at heq
      have : v = vv := heq.left
      have : l = ll := heq.right.left
      have : r = rr := heq.right.right
      subst vv ll rr
      revert h₄
      split
      all_goals
        split
        intro h₄
        right
      case' isTrue => left
      case' isFalse => right
      all_goals
        revert h₄
        apply if_get_eq_contains
        done

private theorem if_contains_get_eq_auxl {α : Type u} {o : Nat} (tree : CompleteTree α (o+1)) (element : α) (h₁ : o > 0) :
  have : tree.leftLen (Nat.lt_succ_of_lt h₁) > 0 := by
    unfold leftLen;
    split
    unfold length
    rename_i hx _ _
    simp only [Nat.add_eq, Nat.succ_eq_add_one, Nat.reduceEqDiff] at hx
    omega
  ∀(indexl : Fin (tree.leftLen (Nat.succ_pos o))), (tree.left _).get indexl this = element → ∃(index : Fin (o+1)), tree.get index (Nat.lt_succ_of_lt h₁) = element
:= by
  simp
  intro indexl
  let index : Fin (o+1) := indexl.succ.castLT (by
    simp only [Nat.succ_eq_add_one, Fin.val_succ, Nat.succ_lt_succ_iff, gt_iff_lt]
    exact Nat.lt_of_lt_of_le indexl.isLt $ Nat.le_of_lt_succ $ leftLenLtN tree (Nat.succ_pos o)
  )
  intro prereq
  exists index
  unfold get
  simp
  unfold get'
  generalize hindex : index = i
  split
  case h_1 =>
    have : index.val = 0 := Fin.val_eq_of_eq hindex
    contradiction
  case h_2 j p q v l r ht1 ht2 ht3 _ _ =>
    have h₂ : index.val = indexl.val + 1 := rfl
    have h₃ : index.val = j.succ := Fin.val_eq_of_eq hindex
    have h₄ : j = indexl.val := Nat.succ.inj $ h₃.subst (motive := λx↦ x = indexl.val + 1) h₂
    have : p = (branch v l r ht1 ht2 ht3).leftLen (Nat.succ_pos _) := rfl
    have h₅ : j < p := by simp only [this, indexl.isLt, h₄]
    simp only [h₅, ↓reduceDite, Nat.add_eq]
    unfold get at prereq
    split at prereq
    rename_i pp ii ll _ hel hei heq _
    split
    rename_i ppp lll _ _ _ _ _ _ _
    have : pp = ppp := by omega
    subst pp
    simp only [gt_iff_lt, Nat.succ_eq_add_one, Nat.add_eq, heq_eq_eq, Nat.zero_lt_succ] at *
    have : j = ii.val := by omega
    subst j
    simp
    rw[←hei] at prereq
    rw[left_unfold] at heq
    rw[heq]
    assumption

private theorem if_contains_get_eq {α : Type u} {o : Nat} (tree : CompleteTree α (o+1)) (element : α) (h₁ : tree.contains element) : ∃(index : Fin (o+1)), tree.get' index = element := by
    revert h₁
    unfold contains
    split ; rename_i hx _; exact absurd hx (Nat.succ_ne_zero o)
    rename_i n m v l r _ _ _ he heq
    intro h₁
    cases h₁
    case h_2.inl h₂ =>
      unfold get'
      exists 0
      split
      case h_2 hx => have hx := Fin.val_eq_of_eq hx; simp at hx;
      case h_1 vv _ _ _ _ _ _ _ =>
        have h₃ := heqSameRoot he (Nat.succ_pos _) heq
        simp only[root_unfold] at h₃
        simp only[h₃, h₂]
    rename_i h
    cases h
    case h_2.inr.inl h₂ => exact
      match hn : n, hl: l with
      | 0, .leaf => by contradiction
      | (nn+1), l => by
        have nn_lt_o : nn < o := by have : o = nn + 1 + m := Nat.succ.inj he; omega
        have blah := if_contains_get_eq l element h₂
        have blupp := if_contains_get_eq_auxl tree element $ Nat.zero_lt_of_lt nn_lt_o
        simp at blupp
        simp[get_eq_get'] at blah ⊢
        apply blah.elim
        match o, tree with
        | (yy+_), .branch _ ll _ _ _ _ =>
          simp_all[left_unfold, leftLen_unfold]
          have : yy = nn+1 := heqSameLeftLen (by omega) (Nat.succ_pos _) heq
          subst yy
          have : _ = m := heqSameRightLen (by omega) (Nat.succ_pos _) heq
          subst m
          simp_all
          exact blupp
    case h_2.inr.inr h₂ => sorry
  termination_by o


theorem contains_iff_index_exists {α : Type u} {o : Nat} (tree : CompleteTree α (o+1)) (element : α) : tree.contains element ↔ ∃ (index : Fin (o+1)), tree.get' index = element := by
  constructor
  case mpr =>
    simp only [forall_exists_index]
    exact if_get_eq_contains tree element
  case mp =>
    exact if_contains_get_eq tree element

/--Shows that the index and value returned by heapRemoveLastWithIndex are consistent.-/
protected theorem heapRemoveLastWithIndexReturnsItemAtIndex {α : Type u} {o : Nat} (heap : CompleteTree α (o+1)) : heap.get' heap.heapRemoveLastWithIndex.snd.snd = heap.heapRemoveLastWithIndex.snd.fst := by
  unfold CompleteTree.heapRemoveLastWithIndex CompleteTree.Internal.heapRemoveLastAux
  split
  rename_i n m v l r m_le_n max_height_difference subtree_full
  simp only [Nat.add_eq, Fin.zero_eta, Fin.isValue, decide_eq_true_eq, Fin.castLE_succ]
  split
  case isTrue n_m_zero =>
    unfold get'
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
    unfold get'
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
        apply AdditionalProofs.heapRemoveLastWithIndexReturnsItemAtIndex
        done
