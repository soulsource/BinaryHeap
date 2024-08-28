import BinaryHeap.CompleteTree.HeapOperations
import BinaryHeap.CompleteTree.HeapProofs.HeapRemoveLast
import BinaryHeap.CompleteTree.AdditionalProofs.Contains
import BinaryHeap.CompleteTree.AdditionalProofs.Get
import BinaryHeap.CompleteTree.NatLemmas

namespace BinaryHeap.CompleteTree.AdditionalProofs

/--Shows that the index and value returned by heapRemoveLastWithIndex are consistent.-/
protected theorem heapRemoveLastWithIndexReturnsItemAtIndex {α : Type u} {o : Nat} (heap : CompleteTree α (o+1)) : heap.get (Internal.heapRemoveLastWithIndex heap).snd.snd = (Internal.heapRemoveLastWithIndex heap).snd.fst := by
  unfold CompleteTree.Internal.heapRemoveLastWithIndex CompleteTree.Internal.heapRemoveLastAux
  split
  rename_i n m v l r m_le_n max_height_difference subtree_full
  simp only [Nat.add_eq, Fin.zero_eta, Fin.isValue, decide_eq_true_eq, Fin.castLE_succ]
  split
  case isTrue n_m_zero =>
    have h₁ : n = 0 := And.left $ Nat.add_eq_zero.mp n_m_zero.symm
    have h₂ : m = 0 := And.right $ Nat.add_eq_zero.mp n_m_zero.symm
    subst n m
    rfl
  case isFalse n_m_not_zero =>
    split
    case isTrue goLeft =>
      match _term : n, l, m_le_n, max_height_difference, subtree_full with
      | (nn+1), l ,m_le_n, max_height_difference, subtree_full =>
      dsimp only [Fin.isValue, Nat.succ_eq_add_one]
      rw[get_left, left_unfold]
      case h₂ => exact Nat.succ_pos _
      case h₃ => exact (Internal.heapRemoveLastAux (β := λ n ↦ α × Fin n) l _ _ _).2.snd.isLt
      apply AdditionalProofs.heapRemoveLastWithIndexReturnsItemAtIndex
    case isFalse goRight =>
      dsimp only [Nat.pred_eq_sub_one, Nat.succ_eq_add_one, Fin.isValue]
      cases r -- to work around cast
      case leaf => simp (config:={ground:=true}) at goRight; exact absurd goRight.symm n_m_not_zero
      case branch rv rl rr rm_le_n rmax_height_difference rsubtree_full =>
        rw[get_right, right_unfold]
        case h₂ => simp_arith[leftLen_unfold]
        simp only [Fin.isValue, Fin.val_succ, Fin.coe_castLE, Fin.coe_addNat, leftLen_unfold]
        have : ∀(a : Nat), a + n + 1 - n - 1 = a := λa↦(Nat.add_sub_cancel _ _).subst $ (Nat.add_assoc a n 1).subst (motive := λx↦a+n+1-n-1 = x-(n+1)) $ (Nat.sub_sub (a+n+1) n 1).subst rfl
        simp only[this]
        apply AdditionalProofs.heapRemoveLastWithIndexReturnsItemAtIndex


protected theorem heapRemoveLastWithIndexLeavesRoot {α : Type u} {n: Nat} (heap : CompleteTree α (n+1)) (h₁ : n > 0) : heap.root (Nat.succ_pos n) = (CompleteTree.Internal.heapRemoveLastWithIndex heap).fst.root h₁ :=
  CompleteTree.heapRemoveLastAuxLeavesRoot heap _ _ _ h₁

private theorem lens_see_through_cast {α : Type u} {p q : Nat} (h₁ : q+p+1 = q+1+p) (len : {n : Nat} → CompleteTree α n → (n > 0) → Nat) (heap : CompleteTree α (q+p+1)) (ha : q+p+1 > 0) (hb : q+1+p > 0): len heap ha = len (h₁▸heap) hb:= by
  induction p generalizing q
  case zero => simp only [Nat.add_zero]
  case succ pp hp =>
    have h₂ := hp (q := q+1)
    have h₃ : (q + 1 + pp + 1) = q + (pp + 1) + 1 := Nat.add_comm_right q 1 (pp + 1)
    have h₄ : (q + 1 + 1 + pp) = q + 1 + (pp + 1) := (Nat.add_comm_right (q+1) 1 pp).substr $ Nat.add_assoc (q+1) pp 1
    rw[h₃, h₄] at h₂
    revert hb ha heap h₁
    assumption

protected theorem heapRemoveLastWithIndexHeapRemoveLastSameTree {α : Type u} {n : Nat} (tree : CompleteTree α (n+1)) : (CompleteTree.Internal.heapRemoveLast tree).fst = (CompleteTree.Internal.heapRemoveLastWithIndex tree).fst := by
  unfold Internal.heapRemoveLast Internal.heapRemoveLastWithIndex Internal.heapRemoveLastAux
  split
  rename_i o p v l r _ _ _
  split
  case isTrue h₁ => trivial
  case isFalse h₁ =>
    simp only
    split
    case isTrue h₂ =>
      cases o;
      case zero => exact absurd h₂.left $ Nat.not_lt_zero p
      case succ oo =>
        simp only
        have h₃ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexHeapRemoveLastSameTree l
        unfold Internal.heapRemoveLast Internal.heapRemoveLastWithIndex at h₃
        rw[h₃]
    case isFalse h₂ =>
      simp only
      cases p
      case zero =>
        simp (config := { ground := true }) only [Nat.zero_add, decide_True, and_true, Nat.not_lt, Nat.le_zero_eq] at h₂
        simp only [Nat.add_zero] at h₁
        exact absurd h₂.symm h₁
      case succ pp =>
        simp only
        have h₃ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexHeapRemoveLastSameTree r
        unfold Internal.heapRemoveLast Internal.heapRemoveLastWithIndex at h₃
        rw[h₃]

protected theorem heapRemoveLastWithIndexHeapRemoveLastSameElement {α : Type u} {n : Nat} (tree : CompleteTree α (n+1)) : (CompleteTree.Internal.heapRemoveLast tree).snd = (CompleteTree.Internal.heapRemoveLastWithIndex tree).snd.fst := by
  unfold Internal.heapRemoveLast Internal.heapRemoveLastWithIndex Internal.heapRemoveLastAux
  split
  rename_i o p v l r _ _ _
  split
  case isTrue h₁ =>
    simp only [id_eq, Nat.add_eq, Fin.zero_eta, Fin.isValue]
    have h₂ : o = 0 := And.left $ Nat.add_eq_zero.mp h₁.symm
    have h₃ : p = 0 := And.right $ Nat.add_eq_zero.mp h₁.symm
    subst o p
    rfl
  case isFalse h₁ =>
    simp only
    split
    case isTrue h₂ =>
      cases o;
      case zero => exact absurd h₂.left $ Nat.not_lt_zero p
      case succ oo =>
        simp only
        have h₃ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexHeapRemoveLastSameElement l
        unfold Internal.heapRemoveLast Internal.heapRemoveLastWithIndex at h₃
        rw[h₃]
    case isFalse h₂ =>
      simp only
      cases p
      case zero =>
        simp (config := { ground := true }) only [Nat.zero_add, decide_True, and_true, Nat.not_lt, Nat.le_zero_eq] at h₂
        simp only [Nat.add_zero] at h₁
        exact absurd h₂.symm h₁
      case succ pp =>
        simp only
        have h₃ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexHeapRemoveLastSameElement r
        unfold Internal.heapRemoveLast Internal.heapRemoveLastWithIndex at h₃
        rw[h₃]

protected theorem heapRemoveLastLeavesRoot {α : Type u} {n: Nat} (heap : CompleteTree α (n+1)) (h₁ : n > 0) : heap.root (Nat.succ_pos n) = (CompleteTree.Internal.heapRemoveLast heap).fst.root h₁ :=
  CompleteTree.heapRemoveLastAuxLeavesRoot heap _ _ _ h₁

protected theorem heapRemoveLastWithIndexIndexNeZeroForNGt1 {α : Type u} {n : Nat} (heap : CompleteTree α (n+1)) : (CompleteTree.Internal.heapRemoveLastWithIndex heap).snd.snd = 0 ↔ n = 0 := by
  constructor
  case mp =>
    unfold Internal.heapRemoveLastWithIndex Internal.heapRemoveLastAux
    split
    rename_i o p v l r _ _ _
    split
    case isTrue =>
      intro
      rename 0 = o + p => h₁
      exact h₁.symm
    case isFalse =>
      intro h₁
      simp at h₁
      split at h₁
      case isTrue =>
        cases o; omega
        case succ oo _ _ _ _ _ =>
          simp at h₁
          exact absurd h₁ $ Fin.succ_ne_zero _
      case isFalse =>
        simp at h₁
        exact absurd h₁ $ Fin.succ_ne_zero _
  case mpr =>
    intro h₁
    unfold Internal.heapRemoveLastWithIndex Internal.heapRemoveLastAux
    split
    rename_i o p v l r _ _ _
    simp at h₁
    simp[h₁]
    have : o = 0 := And.left $ Nat.add_eq_zero_iff.mp h₁
    subst o
    have : p = 0 := And.right $ Nat.add_eq_zero_iff.mp h₁
    subst p
    rfl

private theorem Fin.ne_zero_of_gt {n : Nat} {i j : Fin (n+1)} (h₁ : i > j) : i ≠ 0 :=
  have : 0 ≤ j := Fin.zero_le _
  by omega

private theorem heapRemoveLastWithIndexRelationGt_Aux {α : Type u} {o p q : Nat} (index : Fin (((o + 1).add p + 1))) (h₁ : o + 1 + p = o + p + 1) (tree : CompleteTree α (o+p+1)) (h₂ : o + 1 + p > 0) (h₄ : ↑index - 1 - q - 1 < (h₁ ▸ tree).rightLen h₂) (h₅ : o + p + 1 > 0) (h₇ : ↑index - (q + 1) - 1 < tree.rightLen h₅)
:
  get ⟨↑index - 1 - q - 1, h₄⟩
    ((h₁ ▸ tree).right h₂) =
  get ⟨↑index - (q + 1) - 1, h₇⟩ (tree.right h₅)
:= by
  induction p generalizing o
  case zero =>
    simp
    have : ⟨↑index - 1 - q - 1, h₄⟩ = (⟨↑index - (q + 1) - 1, h₇⟩ : Fin (tree.rightLen h₅)) := by simp; omega
    rw[this]
  case succ pp hp =>
    have hp₂ := hp (o := o+1)
    have hp₃ : (o + 1 + pp + 1) = o + (pp + 1) + 1 := Nat.add_comm_right o 1 (pp + 1)
    have hp₄ : (o + 1 + 1 + pp) = o + 1 + (pp + 1) := (Nat.add_comm_right (o+1) 1 pp).substr $ Nat.add_assoc (o+1) pp 1
    rw[hp₃, hp₄] at hp₂
    have : o + 1 + (pp + 1) + 1 = o + 1 + 1 + pp + 1 := Nat.add_comm_right (o + 1) (pp + 1) 1
    exact hp₂ (index.cast this) h₁ tree h₂ h₄ h₅ h₇

private theorem heapRemoveLastWithIndexRelationGt_Aux2 {α : Type u} {o p : Nat} (index : Fin (o + 1 + p)) (tree : CompleteTree α (o + p + 1)) (h₁ :  o + p + 1 = o + 1 + p) (h₄ : index.val < o + p + 1) : get index (h₁▸tree) = get ⟨index.val,h₄⟩ tree := by
  induction p generalizing o
  case zero =>
    simp
  case succ pp hp =>
    have hp₂ := hp (o := o+1)
    have hp₃ : (o + 1 + pp + 1) = o + (pp + 1) + 1 := Nat.add_comm_right o 1 (pp + 1)
    have hp₄ : (o + 1 + 1 + pp) = o + 1 + (pp + 1) := (Nat.add_comm_right (o+1) 1 pp).substr $ Nat.add_assoc (o+1) pp 1
    rw[hp₃, hp₄] at hp₂
    exact hp₂ index tree h₁ h₄

protected theorem heapRemoveLastWithIndexRelationGt {α : Type u} {n : Nat} (heap : CompleteTree α (n+1)) (index : Fin (n+1)) (h₁ : index > (CompleteTree.Internal.heapRemoveLastWithIndex heap).snd.snd) :
  (CompleteTree.Internal.heapRemoveLastWithIndex heap).fst.get (index.pred $ Fin.ne_zero_of_gt h₁) = heap.get index
:= by
have h₂ : 0 ≠ n := Ne.symm $ Nat.ne_zero_iff_zero_lt.mpr $ Nat.lt_of_lt_of_le (Fin.pos_iff_ne_zero.mpr $ Fin.ne_zero_of_gt h₁) (Nat.le_of_lt_succ index.isLt)
revert h₁
unfold Internal.heapRemoveLastWithIndex Internal.heapRemoveLastAux
intro h₁
split at h₁
rename_i o p v l r _ _ _
simp only [Nat.add_eq, ne_eq] at h₂
simp only [Nat.add_eq, h₂, ↓reduceDIte, decide_eq_true_eq, Fin.zero_eta, Fin.isValue,
  Nat.succ_eq_add_one, Fin.castLE_succ, Nat.pred_eq_sub_one, gt_iff_lt] at h₁ ⊢
if h₃ : p < o ∧ (p + 1).nextPowerOfTwo = p + 1 then
  --removed left
  simp only [h₃, and_self, ↓reduceDIte, Fin.isValue] at h₁ ⊢
  cases o
  case zero => exact absurd h₃.left $ Nat.not_lt_zero p
  case succ oo _ _ _ _ =>
    simp only [Fin.isValue] at h₁ ⊢
    if h₄ : index > oo + 1 then
      -- get goes into the right branch
      rewrite[get_right' _ h₄]
      have h₅ : index ≠ 0 := Fin.ne_zero_of_gt h₁
      have h₆ : index.pred h₅ > oo := Nat.lt_pred_iff_succ_lt.mpr h₄
      rewrite[get_right]
      case h₂ =>
        rewrite[←lens_see_through_cast _ leftLen _ (Nat.succ_pos _) _]
        rewrite[leftLen_unfold]
        assumption
      simp only [Nat.add_eq, ne_eq, Fin.zero_eta, Nat.succ_eq_add_one, Nat.pred_eq_sub_one,
        Fin.coe_pred, Fin.isValue, ← lens_see_through_cast _ leftLen _ (Nat.succ_pos _) _]
      simp only[leftLen_unfold]
      apply heapRemoveLastWithIndexRelationGt_Aux
      case h₁ => exact Nat.add_comm_right oo 1 p
      case h₅ => exact Nat.succ_pos _
    else
      -- get goes into the left branch
      have h₅ : index ≠ 0 := Fin.ne_zero_of_gt h₁
      rewrite[heapRemoveLastWithIndexRelationGt_Aux2]
      case h₄ => exact
        Nat.le_of_not_gt h₄
        |> (Nat.succ_pred (Fin.val_ne_of_ne h₅)).substr
        |> Nat.succ_le.mp
        |> Nat.lt_add_right p
        |> (Nat.add_comm_right oo 1 p).subst
      generalize hold :  get index (branch v l r _ _ _) = old
      have h₆ : index.pred h₅ ≤ oo := Nat.pred_le_iff_le_succ.mpr $ Nat.le_of_not_gt h₄
      have h₇ : ↑index - 1 ≤ oo := (Fin.coe_pred index h₅).subst (motive := λx↦x ≤ oo) h₆
      have h₈ : ↑index ≤ oo + 1 := Nat.le_succ_of_pred_le h₇
      rewrite[get_left']
      case h₁ => exact Nat.zero_lt_of_lt $ Nat.lt_sub_of_add_lt h₁
      case h₂ => exact h₆
      simp only [Fin.coe_pred, Fin.isValue]
      rewrite[get_left'] at hold
      case h₁ => exact Fin.pos_iff_ne_zero.mpr h₅
      case h₂ => exact h₈
      subst hold
      have h₈ : ⟨↑index - 1, Nat.lt_succ.mpr h₇⟩ > (Internal.heapRemoveLastWithIndex l).snd.snd :=
        Nat.lt_sub_of_add_lt h₁
      exact CompleteTree.AdditionalProofs.heapRemoveLastWithIndexRelationGt l ⟨↑index - 1, Nat.lt_succ.mpr h₇⟩ h₈
else
  --removed right
  simp only [h₃, ↓reduceDIte, Fin.isValue] at h₁ ⊢
  cases p <;> simp only [Nat.add_zero, Nat.reduceSub, Nat.reduceAdd, Fin.isValue] at h₁ ⊢
  case zero =>
    simp (config := { ground := true }) only [Nat.zero_add, and_true, Nat.not_lt, Nat.le_zero_eq] at h₃
    subst o
    contradiction
  case succ pp _ _ _ _ =>
    generalize hold : get index (branch v l r _ _ _) = oldValue
    have h₄ : index ≠ 0 := Fin.ne_zero_of_gt h₁
    have h₅ : index.pred h₄ > o := by
      simp only [Nat.add_eq, Fin.coe_pred, gt_iff_lt]
      rewrite[Fin.lt_iff_val_lt_val] at h₁
      simp only [Nat.succ_eq_add_one, Fin.isValue, Fin.val_succ, Fin.coe_castLE, Fin.coe_addNat] at h₁
      exact Nat.lt_of_add_right $ Nat.lt_pred_of_succ_lt h₁
    have h₆ : index > o :=  Nat.lt_of_add_left $ Nat.succ_lt_of_lt_pred h₅
    have h₇ : ↑index - o - 1 < pp + 1 :=
      have : ↑index < (o + 1) + (pp + 1) := (Nat.add_comm_right o (pp+1) 1).subst index.isLt
      have : ↑index < (pp + 1) + (o + 1) := (Nat.add_comm (o+1) (pp+1)).subst this
      (Nat.sub_lt_of_lt_add this (Nat.succ_le_of_lt h₆) : ↑index - (o + 1) < pp + 1)
    have h₈ : ⟨↑index - o - 1, h₇⟩ > (Internal.heapRemoveLastWithIndex r).snd.snd :=
      Nat.lt_sub_of_add_lt (b := o+1) h₁
    rewrite[get_right' _ h₅]
    rewrite[get_right' _ h₆] at hold
    rewrite[←hold]
    have h₉ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexRelationGt r ⟨↑index - o - 1, h₇⟩ h₈
    unfold Internal.heapRemoveLastWithIndex at h₉
    unfold Fin.pred Fin.subNat at h₉
    simp only [Nat.add_eq, Fin.zero_eta, Fin.isValue, Nat.succ_eq_add_one] at h₉
    simp only [Nat.add_eq, Fin.coe_pred, Fin.isValue]
    have : ↑index - 1 - o - 1 = ↑index - o - 1 - 1 :=
      (rfl : ↑index - (o + 1 + 1) = ↑index - (o + 1 + 1))
      |> (Nat.add_comm o 1).subst (motive := λx ↦ ↑index - (x + 1) = ↑index - (o + 1 + 1))
      |> (Nat.sub_sub ↑index 1 (o+1)).substr
    --exact this.substr h₉ --seems to run into a Lean 4.10 bug when proving termination
    simp only [this, Nat.add_eq, Fin.isValue, h₉] --no idea why simp avoids the same issue...

protected theorem heapRemoveLastWithIndexRelationLt {α : Type u} {n : Nat} (heap : CompleteTree α (n+1)) (index : Fin (n+1)) (h₁ : index < (CompleteTree.Internal.heapRemoveLastWithIndex heap).snd.snd) :
  have : index.val < n := Nat.lt_of_lt_of_le h₁ $ Nat.lt_succ.mp (CompleteTree.Internal.heapRemoveLastWithIndex heap).snd.snd.isLt
  (CompleteTree.Internal.heapRemoveLastWithIndex heap).fst.get ⟨index.val, this⟩ = heap.get index
:=
  have hn : n > 0 := Nat.lt_of_lt_of_le (Fin.pos_iff_ne_zero.mpr $ Fin.ne_zero_of_gt h₁) (Nat.le_of_lt_succ (CompleteTree.Internal.heapRemoveLastWithIndex heap).snd.snd.isLt)
  have hi : index.val < n := Nat.lt_of_lt_of_le h₁ $ Nat.lt_succ.mp (CompleteTree.Internal.heapRemoveLastWithIndex heap).snd.snd.isLt
  if h₂ : index = 0 then by
    subst index
    simp only [Fin.val_zero]
    have := Fin.zero_eta.subst (motive := λx ↦ heap.root _ = get x heap) $ get_zero_eq_root heap (Nat.succ_pos _)
    rewrite[←this]
    have :=  get_zero_eq_root (Internal.heapRemoveLastWithIndex heap).fst hn
    rewrite[←this]
    apply Eq.symm
    apply CompleteTree.AdditionalProofs.heapRemoveLastWithIndexLeavesRoot
  else by
    have h₃ : 0 ≠ n := Ne.symm $ Nat.ne_zero_iff_zero_lt.mpr $ Nat.lt_of_lt_of_le (Fin.pos_iff_ne_zero.mpr $ Fin.ne_zero_of_gt h₁) (Nat.le_of_lt_succ (CompleteTree.Internal.heapRemoveLastWithIndex heap).snd.snd.isLt)
    revert h₁
    unfold Internal.heapRemoveLastWithIndex Internal.heapRemoveLastAux
    intro h₁
    split at h₁
    rename_i o p v l r _ _ _
    simp only [Nat.add_eq, ne_eq] at h₃
    simp only [h₃, Nat.add_eq, Fin.zero_eta, Fin.isValue, decide_eq_true_eq, Nat.succ_eq_add_one,
      Fin.castLE_succ, Nat.pred_eq_sub_one, reduceDIte] at h₁ ⊢
    if h₄ : p < o ∧ (p + 1).nextPowerOfTwo = p + 1 then
      --removed left
      --get has to go into the square hole - erm, left branch too
      cases o
      case zero =>
        exact absurd h₄.left $ Nat.not_lt_zero _
      case succ oo _ _ _ _ =>
        rewrite[Fin.lt_iff_val_lt_val] at h₁
        simp only [Nat.add_eq, h₄, and_self, ↓reduceDIte, Fin.isValue, Fin.val_succ,
          Fin.coe_castLE] at h₁ ⊢
        have h₂₂ : index > 0 := Nat.zero_lt_of_ne_zero $ Fin.val_ne_iff.mpr h₂
        have h₆ := (Nat.add_comm_right oo 1 p).subst hi
        have h₈ : (⟨index.val, h₆⟩ : Fin (oo + p + 1)) > ⟨0,Nat.succ_pos _⟩ := h₂₂
        have h₇ : (⟨index.val, h₆⟩ : Fin (oo + p + 1)) ≤ oo := by
          generalize (Internal.heapRemoveLastAux l (β := λn ↦ α × Fin n) _ _ _).2.snd = i at h₁
          have a : i.val ≤ oo := Nat.le_of_lt_succ i.isLt
          have b : index.val ≤ i.val := Nat.le_of_lt_succ h₁
          exact Nat.le_trans b a
        have h₅ : index ≤ oo+1 := Nat.le_succ_of_le h₇
        rewrite[get_left' _ h₂₂ h₅]
        rewrite[heapRemoveLastWithIndexRelationGt_Aux2]
        case h₄ => exact h₆
        rewrite[get_left' _ h₈ h₇]
        have : index.val - 1 < oo + 1 := Nat.sub_one_lt_of_le h₂₂ h₅
        have h₉ : ⟨↑index - 1, this⟩ < (Internal.heapRemoveLastWithIndex l).snd.snd :=
            Nat.sub_lt_of_lt_add h₁ h₂₂
        exact CompleteTree.AdditionalProofs.heapRemoveLastWithIndexRelationLt l ⟨↑index - 1, _⟩ h₉
    else
      --removed right
      simp only [h₄, ↓reduceDIte, Fin.isValue] at h₁ ⊢
      cases p
      case zero =>
        simp (config := { ground := true }) only [Nat.zero_add, and_true, Nat.not_lt, Nat.le_zero_eq] at h₄
        subst o
        contradiction
      case succ pp _ _ _ _ =>
        if h₄ : index > o then
          --get goes into right branch -> recursion
          rewrite[get_right' _ h₄]
          have h₅ : (⟨index.val, hi⟩ : Fin (o + (pp+1))) > o := h₄
          rewrite[get_right' _ h₅]
          simp only [Nat.add_eq, Fin.isValue]
          rewrite[Fin.lt_iff_val_lt_val] at h₁
          have : ↑index - o - 1 < pp + 1 :=
            hi
            |> Nat.sub_lt_left_of_lt_add (n := o) (Nat.le_of_lt h₄)
            |> (flip (Nat.sub_lt_of_lt_add)) (Nat.zero_lt_sub_of_lt h₄)
            |> Nat.lt_succ_of_lt
          have h₈ : ⟨↑index - o - 1, this⟩ < (Internal.heapRemoveLastWithIndex r).snd.snd :=
            Nat.sub_lt_of_lt_add (b := o+1) h₁ h₅
          exact CompleteTree.AdditionalProofs.heapRemoveLastWithIndexRelationLt r  ⟨↑index - o - 1, this⟩ h₈
        else
          --get goes into left branch
          have h₄₂ : index ≤ o := Nat.le_of_not_gt h₄
          have h₂₂ : index > 0 := Nat.zero_lt_of_ne_zero $ Fin.val_ne_iff.mpr h₂
          rewrite[get_left' _ h₂₂ h₄₂]
          have h₅ : (⟨index.val, hi⟩ : Fin (o + (pp+1))) ≤ o := h₄₂
          have h₆ : (⟨index.val, hi⟩ : Fin (o + (pp+1))) > ⟨0,Nat.succ_pos _⟩ := h₂₂
          rw[get_left' _ h₆ h₅]

/--
  Shows that for each index in the original tree there is a corresponding index in the resulting tree of heapRemoveLast,
  except for the element returned by heapRemoveLast (WithIndex).
  This is a rigourous proof that heapRemoveLast does not modify the tree in any other ways than removing
  the last element.
 -/
protected theorem heapRemoveLastWithIndexRelation {α : Type u} {n : Nat} (heap : CompleteTree α (n+1)) (index : Fin (n+1)):
  let (result, removedElement, oldIndex) := CompleteTree.Internal.heapRemoveLastWithIndex heap
  if h₁ : index > oldIndex then
    have : oldIndex ≥ 0 := Fin.zero_le oldIndex
    have : index > 0 := by omega
    result.get (index.pred $ Fin.ne_of_gt this) = heap.get index
  else if h₂ : index < oldIndex then
    result.get (index.castLT (by omega)) = heap.get index
  else
    removedElement = heap.get index
:= by
  simp
  split
  case isTrue h₁ =>
    apply CompleteTree.AdditionalProofs.heapRemoveLastWithIndexRelationGt
    assumption
  case isFalse h₁ =>
    have h₁ : (Internal.heapRemoveLastWithIndex heap).2.snd ≥ index := Fin.not_lt.mp h₁
    split
    case isTrue h₂ =>
      apply CompleteTree.AdditionalProofs.heapRemoveLastWithIndexRelationLt
      assumption
    case isFalse h₂ =>
      --have h₂ : (Internal.heapRemoveLastWithIndex heap).2.snd ≤ index := Fin.not_lt.mp h₂
      have : (index.val < (Internal.heapRemoveLastWithIndex heap).2.snd.val) = False := Fin.lt_iff_val_lt_val.subst (p := λx ↦ x = False) $ eq_false  h₂
      have h₃ : index = (Internal.heapRemoveLastWithIndex heap).2.snd :=
        Nat.lt_or_eq_of_le h₁
        |> this.subst (motive := λx ↦ x ∨ index.val = (Internal.heapRemoveLastWithIndex heap).snd.snd.val)
        |> (false_or _).mp
        |> Fin.eq_of_val_eq
      exact
        CompleteTree.AdditionalProofs.heapRemoveLastWithIndexReturnsItemAtIndex heap
        |> h₃.substr
        |> Eq.symm


/--
  Shows that each element contained before removing the last that is not the last is still contained after removing the last.
  This is not a rigorous proof that the rest of the tree remained unchanged. Such a proof exists in heapRemoveLastWithIndexRelation
  -/
protected theorem heapRemoveLastWithIndexOnlyRemovesOneElement {α : Type u} {n : Nat} (heap : CompleteTree α (n+1)) (index : Fin (n+1)) :
  let (newHeap, _, removedIndex) := Internal.heapRemoveLastWithIndex heap
  (h₁ : index ≠ removedIndex) → newHeap.contains (heap.get index)
:= by
  simp only [ne_eq]
  intro h₁
  rw[contains_iff_index_exists _ _]
  have h₃ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexRelation heap index
  simp at h₃
  split at h₃
  case isTrue h₄ =>
    exists (index.pred (Fin.ne_zero_of_gt h₄))
  case isFalse h₄ =>
    split at h₃
    case isTrue h₅ =>
      exists (index.castLT (by omega : ↑index < n))
    case isFalse h₅ =>
      omega --contradiction

/--
  Shows that each element contained before removing the last that is not the last is still contained after removing the last.
  This is not a rigorous proof that the rest of the tree remained unchanged. Such a proof exists in heapRemoveLastWithIndexRelation
  -/
protected theorem heapRemoveLastWithIndexEitherContainsOrReturnsElement {α : Type u} {n : Nat} (heap : CompleteTree α (n+1)) (index : Fin (n+1)) :
  let (newHeap, removedElement, _) := Internal.heapRemoveLastWithIndex heap
  newHeap.contains (heap.get index) ∨ removedElement = heap.get index
:=
  let removedIndex := (Internal.heapRemoveLastWithIndex heap).snd.snd
  if h₁ : index ≠ removedIndex then
    Or.inl $ CompleteTree.AdditionalProofs.heapRemoveLastWithIndexOnlyRemovesOneElement heap index h₁
  else by
    right
    have h₂ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexReturnsItemAtIndex heap
    simp at h₁
    subst index
    rw[h₂]
    rfl

/--
  Shows that each element contained before removing the last that is not the last is still contained after removing the last.
  This is not a rigorous proof that the rest of the tree remained unchanged. Such a proof exists in heapRemoveLastWithIndexRelation
  -/
protected theorem heapRemoveLastEitherContainsOrReturnsElement {α : Type u} {n : Nat} (heap : CompleteTree α (n+1)) (index : Fin (n+1)) :
  let (newHeap, removedElement) := Internal.heapRemoveLast heap
  newHeap.contains (heap.get index) ∨ removedElement = heap.get index
:= by
  have h₁ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexEitherContainsOrReturnsElement heap index
  simp at h₁ ⊢
  rewrite[CompleteTree.AdditionalProofs.heapRemoveLastWithIndexHeapRemoveLastSameElement]
  rewrite[CompleteTree.AdditionalProofs.heapRemoveLastWithIndexHeapRemoveLastSameTree]
  assumption
