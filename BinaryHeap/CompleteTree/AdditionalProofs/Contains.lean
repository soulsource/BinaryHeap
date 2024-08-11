import BinaryHeap.CompleteTree.AdditionalOperations
import BinaryHeap.CompleteTree.AdditionalProofs.Get

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

private theorem if_contains_get_eq_auxr {α : Type u} {o : Nat} (tree : CompleteTree α (o+1)) (element : α) (h₁ : tree.rightLen (Nat.succ_pos o) > 0) :
  ∀(indexl : Fin (tree.rightLen (Nat.succ_pos o))), (tree.right _).get indexl h₁ = element → ∃(index : Fin (o+1)), tree.get index (Nat.succ_pos o) = element
:= by
  intro indexr
  let index : Fin (o+1) := ⟨(tree.leftLen (Nat.succ_pos o) + indexr.val + 1), by
    have h₂ : tree.leftLen (Nat.succ_pos _) + tree.rightLen _ + 1 = tree.length := Eq.symm $ lengthEqLeftRightLenSucc tree _
    rw[length] at h₂
    have h₃ : tree.leftLen (Nat.succ_pos o) + indexr.val + 1 < tree.leftLen (Nat.succ_pos o) + tree.rightLen (Nat.succ_pos o) + 1 := by
      apply Nat.succ_lt_succ
      apply Nat.add_lt_add_left
      exact indexr.isLt
    exact Nat.lt_of_lt_of_eq h₃ h₂
  ⟩
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
    have h₂ : index.val = (branch v l r ht1 ht2 ht3).leftLen (Nat.succ_pos _) + indexr.val + 1 := rfl
    have h₃ : index.val = j.succ := Fin.val_eq_of_eq hindex
    have h₄ : j = (branch v l r ht1 ht2 ht3).leftLen (Nat.succ_pos _) + indexr.val := by
      rw[h₃] at h₂
      exact Nat.succ.inj h₂
    have : p = (branch v l r ht1 ht2 ht3).leftLen (Nat.succ_pos _) := rfl
    have h₅ : ¬(j < p) := by simp_arith [this, h₄]
    simp only [h₅, ↓reduceDite, Nat.add_eq]
    unfold get at prereq
    split at prereq
    rename_i pp ii rr _ hel hei heq _
    split
    rename_i ppp rrr _ _ _ _ _ _ _ _
    have : pp = ppp := by rw[rightLen_unfold] at hel; exact Nat.succ.inj hel.symm
    subst pp
    simp only [gt_iff_lt, ne_eq, Nat.succ_eq_add_one, Nat.add_eq, Nat.reduceEqDiff, heq_eq_eq, Nat.zero_lt_succ] at *
    have : j = ii.val + p := by omega
    subst this
    simp
    rw[right_unfold] at heq
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
        have nn_lt_o : nn < o := by have : o = nn + 1 + m := Nat.succ.inj he; omega --also for termination
        have h₃ := if_contains_get_eq l element h₂
        have h₄ := if_contains_get_eq_auxl tree element $ Nat.zero_lt_of_lt nn_lt_o
        simp only at h₄
        simp[get_eq_get'] at h₃ ⊢
        apply h₃.elim
        match o, tree with
        | (yy+_), .branch _ ll _ _ _ _ =>
          simp_all[left_unfold, leftLen_unfold]
          have : yy = nn+1 := heqSameLeftLen (by omega) (Nat.succ_pos _) heq
          have : _ = m := heqSameRightLen (by omega) (Nat.succ_pos _) heq
          subst yy m
          simp_all
          exact h₄
    case h_2.inr.inr h₂ => exact
      match hm : m, hr: r with
      | 0, .leaf => by contradiction
      | (mm+1), r => by
        have mm_lt_o : mm < o := by have : o = n + (mm + 1) := Nat.succ.inj he; omega --termination
        have h₃ := if_contains_get_eq r element h₂
        have : tree.rightLen (Nat.succ_pos o) > 0 := by
          have := heqSameRightLen (he) (Nat.succ_pos o) heq
          simp[rightLen_unfold] at this
          rw[this]
          exact Nat.succ_pos mm
        have h₄ := if_contains_get_eq_auxr tree element this
        simp[get_eq_get'] at h₃ ⊢
        apply h₃.elim
        match o, tree with
        | (_+zz), .branch _ _ rr _ _ _ =>
          simp_all[right_unfold, rightLen_unfold]
          have : _ = n := heqSameLeftLen (by omega) (Nat.succ_pos _) heq
          have : zz = mm+1 := heqSameRightLen (by omega) (Nat.succ_pos _) heq
          subst n zz
          simp_all
          exact h₄
  termination_by o


theorem contains_iff_index_exists' {α : Type u} {o : Nat} (tree : CompleteTree α (o+1)) (element : α) : tree.contains element ↔ ∃ (index : Fin (o+1)), tree.get' index = element := by
  constructor
  case mpr =>
    simp only [forall_exists_index]
    exact if_get_eq_contains tree element
  case mp =>
    exact if_contains_get_eq tree element

theorem contains_iff_index_exists {α : Type u} {n : Nat} (tree : CompleteTree α n) (element : α) (h₁ : n > 0): tree.contains element ↔ ∃ (index : Fin n), tree.get index h₁ = element :=
  match n, tree with
  | _+1, tree => contains_iff_index_exists' tree element
