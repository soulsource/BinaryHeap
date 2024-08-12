import BinaryHeap.CompleteTree.HeapOperations
import BinaryHeap.CompleteTree.HeapProofs.HeapRemoveLast
import BinaryHeap.CompleteTree.AdditionalProofs.Contains
import BinaryHeap.CompleteTree.AdditionalProofs.Get
import BinaryHeap.CompleteTree.NatLemmas

namespace BinaryHeap.CompleteTree.AdditionalProofs

/--Shows that the index and value returned by heapRemoveLastWithIndex are consistent.-/
protected theorem heapRemoveLastWithIndexReturnsItemAtIndex {α : Type u} {o : Nat} (heap : CompleteTree α (o+1)) : heap.get' (Internal.heapRemoveLastWithIndex heap).snd.snd = (Internal.heapRemoveLastWithIndex heap).snd.fst := by
  unfold CompleteTree.Internal.heapRemoveLastWithIndex CompleteTree.Internal.heapRemoveLastAux
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
      have : n = nn := heqSameLeftLen (congrArg (·+1) he₂) (Nat.succ_pos _) he₃
      have : m = mm := heqSameRightLen (congrArg (·+1) he₂) (Nat.succ_pos _) he₃
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

private theorem left_sees_through_cast {α : Type u} {p q : Nat} (h₁ : q+p+1 = q+1+p) (heap : CompleteTree α (q+p+1)) (ha : q+p+1 > 0) (hb : q+1+p > 0): HEq (heap.left ha) ((h₁▸heap).left hb) := by
  induction p generalizing q
  case zero => simp only [Nat.add_zero, heq_eq_eq]
  case succ pp hp =>
    have h₂ := hp (q := q+1)
    have h₃ : (q + 1 + pp + 1) = q + (pp + 1) + 1 := Nat.add_comm_right q 1 (pp + 1)
    have h₄ : (q + 1 + 1 + pp) = q + 1 + (pp + 1) := (Nat.add_comm_right (q+1) 1 pp).substr $ Nat.add_assoc (q+1) pp 1
    rw[h₃, h₄] at h₂
    revert hb ha heap h₁
    assumption

private theorem right_sees_through_cast {α : Type u} {p q : Nat} (h₁ : q+p+1 = q+1+p) (heap : CompleteTree α (q+p+1)) (ha : q+p+1 > 0) (hb : q+1+p > 0): HEq (heap.right ha) ((h₁▸heap).right hb) := by
  induction p generalizing q
  case zero => simp only [Nat.add_zero, heq_eq_eq]
  case succ pp hp =>
    have h₂ := hp (q := q+1)
    have h₃ : (q + 1 + pp + 1) = q + (pp + 1) + 1 := Nat.add_comm_right q 1 (pp + 1)
    have h₄ : (q + 1 + 1 + pp) = q + 1 + (pp + 1) := (Nat.add_comm_right (q+1) 1 pp).substr $ Nat.add_assoc (q+1) pp 1
    rw[h₃, h₄] at h₂
    revert hb ha heap h₁
    assumption

/--Helper for heapRemoveLastWithIndexOnlyRemovesOneElement_Auxllength to allow splitting the goal-/
private theorem heapRemoveLastWithIndexOnlyRemovesOneElement_AuxLLengthAux {α : Type u} {n : Nat} (tree : CompleteTree α (n+1)) (h₁ : n > 0)
:
  let o := tree.leftLen'
  let p := tree.rightLen'
  (h₂ : p < o ∧ (p+1).nextPowerOfTwo = p+1) → (Internal.heapRemoveLastWithIndex tree).fst.leftLen h₁ = o.pred
:= by
  simp only
  intro h₂
  unfold Internal.heapRemoveLastWithIndex Internal.heapRemoveLastAux
  split --finally
  rename_i del1 del2 o p v l r o_le_p max_height_difference subtree_complete
  clear del2 del1
  unfold rightLen' leftLen' at h₂
  simp only [leftLen_unfold, rightLen_unfold] at h₂
  have : 0 ≠ o + p := Nat.ne_of_lt h₁
  simp only [this, ↓reduceDite, h₂, decide_True, and_self]
  match o, l, o_le_p, max_height_difference, subtree_complete, this, h₂ with
  | (q+1), l, o_le_p, max_height_difference, subtree_complete, this, h₂ =>
    simp only [Nat.add_eq, Fin.zero_eta, Fin.isValue, Nat.succ_eq_add_one, Nat.pred_eq_sub_one]
    rw[←lens_see_through_cast _ leftLen _ (Nat.succ_pos (q+p))]
    unfold leftLen'
    rw[leftLen_unfold]
    rw[leftLen_unfold]
    rfl

private theorem heapRemoveLastWithIndexOnlyRemovesOneElement_AuxLLength {α : Type u} {o p : Nat} (v : α) (l : CompleteTree α (o+1)) (r : CompleteTree α p) (h₁ : p ≤ (o+1)) (h₂ : (o+1) < 2 * (p + 1)) (h₃ : (o + 1 + 1).isPowerOfTwo ∨ (p + 1).isPowerOfTwo) (h₄ : p < (o+1) ∧ ((p+1).nextPowerOfTwo = p+1 : Bool))
:
  (Internal.heapRemoveLastWithIndex (branch v l r h₁ h₂ h₃)).fst.leftLen (Nat.lt_add_right p $ Nat.succ_pos o) = o
:= by
  apply heapRemoveLastWithIndexOnlyRemovesOneElement_AuxLLengthAux (branch v l r h₁ h₂ h₃) (Nat.lt_add_right p $ Nat.succ_pos o)
  unfold leftLen' rightLen'
  simp only [leftLen_unfold, rightLen_unfold]
  simp only [decide_eq_true_eq] at h₄
  assumption

/--Helper for heapRemoveLastWithIndexOnlyRemovesOneElement_Auxllength to allow splitting the goal-/
private theorem heapRemoveLastWithIndexOnlyRemovesOneElement_AuxRLengthAux {α : Type u} {n : Nat} (tree : CompleteTree α (n+1)) (h₁ : n > 0)
:
  let o := tree.leftLen'
  let p := tree.rightLen'
  (h₂ : ¬(p < o ∧ ((p+1).nextPowerOfTwo = p+1 : Bool))) → (Internal.heapRemoveLastWithIndex tree).fst.rightLen h₁ = p.pred
:= by
  simp only
  intro h₂
  unfold Internal.heapRemoveLastWithIndex Internal.heapRemoveLastAux
  split --finally
  rename_i del1 del2 o p v l r o_le_p max_height_difference subtree_complete
  clear del2 del1
  unfold rightLen' leftLen' at h₂
  simp only [leftLen_unfold, rightLen_unfold] at h₂
  have : 0 ≠ o + p := Nat.ne_of_lt h₁
  simp only [this, ↓reduceDite, h₂, decide_True, and_self]
  cases p
  case zero =>
    simp at h₂ h₁
    simp (config := {ground:=true})[h₁] at h₂
  case succ pp =>
    simp[rightLen', rightLen_unfold]

private theorem heapRemoveLastWithIndexOnlyRemovesOneElement_AuxRLength {α : Type u} {o p : Nat} (v : α) (l : CompleteTree α o) (r : CompleteTree α (p+1)) (h₁ : p+1 ≤ o) (h₂ : o < 2 * (p + 1 + 1)) (h₃ : (o + 1).isPowerOfTwo ∨ (p + 1 + 1).isPowerOfTwo) (h₄ : ¬(p + 1 < o ∧ ((p+1+1).nextPowerOfTwo = p+1+1 : Bool)))
:
  (Internal.heapRemoveLastWithIndex (branch v l r h₁ h₂ h₃)).fst.rightLen (Nat.lt_add_left o $ Nat.succ_pos p) = p
:= by
  apply heapRemoveLastWithIndexOnlyRemovesOneElement_AuxRLengthAux (branch v l r h₁ h₂ h₃) (Nat.lt_add_left o $ Nat.succ_pos p)
  unfold leftLen' rightLen'
  simp only [leftLen_unfold, rightLen_unfold]
  assumption

private def heapRemoveLastWithIndex' {α : Type u} {o : Nat} (heap : CompleteTree α o) (_ : o > 0) : (CompleteTree α o.pred × α × Fin o) :=
  match o, heap with
  | _+1, heap => Internal.heapRemoveLastWithIndex heap

private theorem heapRemoveLastWithIndex'_unfold {α : Type u} {o : Nat} (heap : CompleteTree α o) (h₁ : o > 0)
:
  match o, heap with
  | (oo+1), heap => (heapRemoveLastWithIndex' heap h₁) = (Internal.heapRemoveLastWithIndex heap)
:= by
  split
  rfl

/--Helper for heapRemoveLastWithIndexOnlyRemovesOneElement_Auxl to allow splitting the goal-/
private theorem heapRemoveLastWithIndexOnlyRemovesOneElement_AuxLAux {α : Type u} {n : Nat} (tree : CompleteTree α (n+1)) (h₁ : n > 0)
:
  let o := tree.leftLen'
  let p := tree.rightLen'
  (h₂ : o > 0) →
  (h₃ : p < o ∧ ((p+1).nextPowerOfTwo = p+1 : Bool)) →
  HEq ((Internal.heapRemoveLastWithIndex tree).fst.left h₁) (heapRemoveLastWithIndex' (tree.left') h₂).fst
:= by
  simp only
  intro h₂ h₃
  --sorry for this wild mixture of working on the LHS and RHS of the goal.
  --this function is trial and error, I'm fighting an uphill battle agains tactics mode here,
  --which keeps randomly failing on me if I do steps in what the tactics
  --percieve to be the "wrong" order.
  have h₄ := heapRemoveLastWithIndex'_unfold tree.left' h₂
  split at h₄
  rename_i d3 d2 d1 oo l o_gt_0 he1 he2 he3
  clear d1 d2 d3
  --okay, I have no clue why generalizing here is needed.
  --I mean, why does unfolding and simplifying work if it's a separate hypothesis,
  --but not within the goal?
  generalize hi : (Internal.heapRemoveLastWithIndex tree).fst = input
  unfold Internal.heapRemoveLastWithIndex Internal.heapRemoveLastAux at hi
  split at hi
  rename_i o2 p vv ll rr _ _ _
  unfold left' leftLen' rightLen' at *
  rw[left_unfold] at *
  rw[leftLen_unfold, rightLen_unfold] at *
  subst o2
  simp at he2
  subst ll
  rw[h₄]
  have : (0 ≠ oo.succ + p) := by simp_arith
  simp[this, h₃] at hi
  have : (p+1).isPowerOfTwo := by
    have h₃ := h₃.right
    simp at h₃
    exact (Nat.power_of_two_iff_next_power_eq (p+1)).mpr h₃
  have := left_sees_through_cast (by simp_arith) (branch vv
      (Internal.heapRemoveLastAux (β := λn ↦ α × Fin n) l (fun a => (a, 0))
          (fun {prev_size curr_size} x h₁ => (x.fst, Fin.castLE (Nat.succ_le_of_lt h₁) x.snd.succ))
          fun {prev_size curr_size} x left_size h₁ => (x.fst, Fin.castLE (by omega) (x.snd.addNat left_size).succ)).fst
      rr (by omega) (by omega) (Or.inr this))
  rw[hi] at this
  clear hi
  have := this (by simp) (by simp_arith)
  simp only [left_unfold] at this
  unfold Internal.heapRemoveLastWithIndex
  simp
  exact this.symm

/--Shows that if the removal happens in the left tree, the new left-tree is the old left-tree with the last element removed.-/
private theorem heapRemoveLastWithIndexOnlyRemovesOneElement_AuxL {α : Type u} {o p : Nat} (v : α) (l : CompleteTree α (o+1)) (r : CompleteTree α p) (h₁ : p ≤ (o+1)) (h₂ : (o+1) < 2 * (p + 1)) (h₃ : (o + 1 + 1).isPowerOfTwo ∨ (p + 1).isPowerOfTwo) (h₄ : p < (o+1) ∧ ((p+1).nextPowerOfTwo = p+1 : Bool))
:
  HEq ((Internal.heapRemoveLastWithIndex (branch v l r h₁ h₂ h₃)).fst.left (Nat.lt_add_right p $ Nat.succ_pos o)) (Internal.heapRemoveLastWithIndex l).fst
:=
  --okay, let me be frank here: I have absolutely no clue why I need heapRemoveLastWithIndexOnlyRemovesOneElement_Auxl2.
  --from the looks of it, I should just be able to generalize the LHS, and unfold things and be happy.
  --However, tactic unfold fails. So, let's just forward this to the helper.
  have h₅ : (branch v l r h₁ h₂ h₃).leftLen' > 0 := Nat.succ_pos o
  heapRemoveLastWithIndexOnlyRemovesOneElement_AuxLAux _ _ h₅ h₄

/--Helper for heapRemoveLastWithIndexOnlyRemovesOneElement_AuxR to allow splitting the goal-/
private theorem heapRemoveLastWithIndexOnlyRemovesOneElement_AuxRAux {α : Type u} {n : Nat} (tree : CompleteTree α (n+1)) (h₁ : n > 0)
:
  let o := tree.leftLen'
  let p := tree.rightLen'
  (h₂ : p > 0) →
  (h₃ : ¬(p < o ∧ ((p+1).nextPowerOfTwo = p+1 : Bool))) →
  HEq ((Internal.heapRemoveLastWithIndex tree).fst.right h₁) (heapRemoveLastWithIndex' (tree.right') h₂).fst
:= by
  simp only
  intro h₂ h₃
  --sorry for this wild mixture of working on the LHS and RHS of the goal.
  --this function is trial and error, I'm fighting an uphill battle agains tactics mode here,
  --which keeps randomly failing on me if I do steps in what the tactics
  --percieve to be the "wrong" order.
  have h₄ := heapRemoveLastWithIndex'_unfold tree.right' h₂
  split at h₄
  rename_i d3 d2 d1 pp l o_gt_0 he1 he2 he3
  clear d1 d2 d3
  --okay, I have no clue why generalizing here is needed.
  --I mean, why does unfolding and simplifying work if it's a separate hypothesis,
  --but not within the goal?
  generalize hi : (Internal.heapRemoveLastWithIndex tree).fst = input
  unfold Internal.heapRemoveLastWithIndex Internal.heapRemoveLastAux at hi
  split at hi
  rename_i o p2 vv ll rr m_le_n max_height_difference subtree_complete
  unfold right' leftLen' rightLen' at *
  rw[right_unfold] at *
  rw[leftLen_unfold, rightLen_unfold] at *
  subst p2
  simp at he2
  subst rr
  rw[h₄]
  have : (0 ≠ o + pp.succ) := by simp_arith
  simp[this] at hi
  have : ¬(pp + 1 < o ∧ (pp + 1 + 1).nextPowerOfTwo = pp + 1 + 1) := by simp; simp at h₃; assumption
  simp[this] at hi
  subst input
  simp[right_unfold, Internal.heapRemoveLastWithIndex]
  done

/--Shows that if the removal happens in the left tree, the new left-tree is the old left-tree with the last element removed.-/
private theorem heapRemoveLastWithIndexOnlyRemovesOneElement_AuxR {α : Type u} {o p : Nat} (v : α) (l : CompleteTree α o) (r : CompleteTree α (p+1)) (h₁ : (p+1) ≤ o) (h₂ : o < 2 * (p + 1 + 1)) (h₃ : (o + 1).isPowerOfTwo ∨ (p + 1 + 1).isPowerOfTwo) (h₄ : ¬(p + 1 < o ∧ ((p + 1 + 1).nextPowerOfTwo = p + 1 + 1 : Bool)))
:
  HEq ((Internal.heapRemoveLastWithIndex (branch v l r h₁ h₂ h₃)).fst.right (Nat.lt_add_left o $ Nat.succ_pos p)) (Internal.heapRemoveLastWithIndex r).fst
:=
  --okay, let me be frank here: I have absolutely no clue why I need heapRemoveLastWithIndexOnlyRemovesOneElement_Auxl2.
  --from the looks of it, I should just be able to generalize the LHS, and unfold things and be happy.
  --However, tactic unfold fails. So, let's just forward this to the helper.
  have h₅ : (branch v l r h₁ h₂ h₃).rightLen' > 0 := Nat.succ_pos p
  heapRemoveLastWithIndexOnlyRemovesOneElement_AuxRAux _ _ h₅ h₄

/--Helper for heapRemoveLastWithIndexOnlyRemovesOneElement_Auxllength to allow splitting the goal-/
private theorem heapRemoveLastWithIndexOnlyRemovesOneElement_AuxLLength2Aux {α : Type u} {n : Nat} (tree : CompleteTree α (n+1)) (h₁ : n > 0)
:
  let o := tree.leftLen'
  let p := tree.rightLen'
  (h₂ : ¬(p < o ∧ ((p+1).nextPowerOfTwo = p+1 : Bool))) → (Internal.heapRemoveLastWithIndex tree).fst.leftLen h₁ = o
:= by
  simp only
  intro h₂
  unfold Internal.heapRemoveLastWithIndex Internal.heapRemoveLastAux
  split --finally
  rename_i del1 del2 o p v l r o_le_p max_height_difference subtree_complete
  clear del2 del1
  unfold rightLen' leftLen' at h₂
  simp only [leftLen_unfold, rightLen_unfold] at h₂
  have h₄ : 0 ≠ o + p := Nat.ne_of_lt h₁
  simp only [h₄, ↓reduceDite, h₂, decide_True, and_self]
  cases p
  case zero =>
    have : decide ((0 + 1).nextPowerOfTwo = 0 + 1) = true := by simp (config := { ground := true }) only [decide_True, Nat.zero_add]
    simp only [this, and_true, Nat.not_lt, Nat.le_zero_eq] at h₂
    exact absurd h₂.symm h₄
  case succ pp =>
    unfold leftLen'
    simp[leftLen_unfold]
    done

private theorem heapRemoveLastWithIndexOnlyRemovesOneElement_AuxLLength2 {α : Type u} {o p : Nat} (v : α) (l : CompleteTree α (o+1)) (r : CompleteTree α p) (h₁ : p ≤ (o+1)) (h₂ : (o+1) < 2 * (p + 1)) (h₃ : (o + 1 + 1).isPowerOfTwo ∨ (p + 1).isPowerOfTwo) (h₄ : ¬(p < (o+1) ∧ ((p+1).nextPowerOfTwo = p+1 : Bool)))
:
  (Internal.heapRemoveLastWithIndex (branch v l r h₁ h₂ h₃)).fst.leftLen (Nat.lt_add_right p $ Nat.succ_pos o) = o + 1
:= by
  apply heapRemoveLastWithIndexOnlyRemovesOneElement_AuxLLength2Aux (branch v l r h₁ h₂ h₃) (Nat.lt_add_right p $ Nat.succ_pos o)
  unfold leftLen' rightLen'
  simp only [leftLen_unfold, rightLen_unfold]
  assumption


private theorem heapRemoveLastWithIndexOnlyRemovesOneElement_AuxL2Aux {α : Type u} {n : Nat} (tree : CompleteTree α (n+1)) (h₁ : n > 0)
:
  let o := tree.leftLen'
  let p := tree.rightLen'
  (h₂ : o > 0) →
  (h₃ : ¬(p < o ∧ ((p+1).nextPowerOfTwo = p+1 : Bool))) →
  HEq ((Internal.heapRemoveLastWithIndex tree).fst.left h₁) tree.left'
:= by
  simp only
  intro h₂ h₃
  generalize hi : (Internal.heapRemoveLastWithIndex tree).fst = input
  unfold Internal.heapRemoveLastWithIndex Internal.heapRemoveLastAux at hi
  split at hi
  rename_i d1 d2 o2 p vv ll rr m_le_n max_height_difference subtree_complete
  clear d1 d2
  unfold leftLen' rightLen' at*
  rw[leftLen_unfold, rightLen_unfold] at *
  have h₄ : 0 ≠ o2+p := Nat.ne_of_lt h₁
  simp only [h₄, h₃, reduceDite] at hi
  -- okay, dealing with p.pred.succ is a guarantee for pain. "Stuck at solving universe constraint"
  cases p
  case zero =>
    have : decide ((0 + 1).nextPowerOfTwo = 0 + 1) = true := by simp (config := { ground := true }) only [decide_True, Nat.zero_add]
    simp only [this, and_true, Nat.not_lt, Nat.le_zero_eq] at h₃
    exact absurd h₃.symm h₄
  case succ pp =>
    simp at hi --whoa, how easy this gets if one just does cases p...
    unfold left'
    rewrite[←hi, left_unfold]
    rewrite[left_unfold]
    exact heq_of_eq rfl

/--Shows that if the removal happens in the right subtree, the left subtree remains unchanged.-/
private theorem heapRemoveLastWithIndexOnlyRemovesOneElement_AuxL2 {α : Type u} {o p : Nat} (v : α) (l : CompleteTree α (o+1)) (r : CompleteTree α p) (h₁ : p ≤ (o+1)) (h₂ : (o+1) < 2 * (p + 1)) (h₃ : (o + 1 + 1).isPowerOfTwo ∨ (p + 1).isPowerOfTwo) (h₄ : ¬ (p < (o+1) ∧ ((p+1).nextPowerOfTwo = p+1 : Bool)))
:
  HEq ((Internal.heapRemoveLastWithIndex (branch v l r h₁ h₂ h₃)).fst.left (Nat.lt_add_right p $ Nat.succ_pos o)) l
:=
  heapRemoveLastWithIndexOnlyRemovesOneElement_AuxL2Aux (branch v l r h₁ h₂ h₃) (by omega) (Nat.succ_pos _) h₄

private theorem heapRemoveLastWithIndexOnlyRemovesOneElement_AuxRLength2Aux {α : Type u} {n : Nat} (tree : CompleteTree α (n+1)) (h₁ : n > 0)
:
  let o := tree.leftLen'
  let p := tree.rightLen'
  (h₂ : (p < o ∧ ((p+1).nextPowerOfTwo = p+1 : Bool))) → (Internal.heapRemoveLastWithIndex tree).fst.rightLen h₁ = p
:= by
  simp only
  intro h₂
  unfold Internal.heapRemoveLastWithIndex Internal.heapRemoveLastAux
  split --finally
  rename_i del1 del2 o p v l r o_le_p max_height_difference subtree_complete
  clear del2 del1
  unfold rightLen' leftLen' at h₂
  simp only [leftLen_unfold, rightLen_unfold] at h₂
  have h₄ : 0 ≠ o + p := Nat.ne_of_lt h₁
  simp only [h₄, ↓reduceDite, h₂, decide_True, and_self]
  cases o
  case zero => exact absurd h₂.left $ Nat.not_lt_zero p
  case succ oo =>
    simp at h₂ ⊢
    have : (p+1).isPowerOfTwo := by simp[Nat.power_of_two_iff_next_power_eq, h₂.right]
    have := lens_see_through_cast ( by simp_arith : oo + p + 1 = oo + 1 + p) rightLen (branch v
          (Internal.heapRemoveLastAux (β := λn ↦ α × Fin n) l (fun a => (a, 0))
              (fun {prev_size curr_size} x h₁ => (x.fst, Fin.castLE (by omega) x.snd.succ))
              fun {prev_size curr_size} x left_size h₁ => (x.fst, Fin.castLE (by omega) (x.snd.addNat left_size).succ)).fst
          r (Nat.le_of_lt_succ h₂.left) (Nat.lt_of_succ_lt max_height_difference) (Or.inr this)) (Nat.succ_pos _) h₁
    rw[←this]
    simp[rightLen', rightLen_unfold]
    done

private theorem heapRemoveLastWithIndexOnlyRemovesOneElement_AuxRLength2 {α : Type u} {o p : Nat} (v : α) (l : CompleteTree α o) (r : CompleteTree α (p + 1)) (h₁ : (p + 1) ≤ o) (h₂ : o < 2 * (p + 1 + 1)) (h₃ : (o + 1).isPowerOfTwo ∨ (p + 1 + 1).isPowerOfTwo) (h₄ : ((p + 1) < o ∧ ((p+1+1).nextPowerOfTwo = p+1+1 : Bool)))
:
  (Internal.heapRemoveLastWithIndex (branch v l r h₁ h₂ h₃)).fst.rightLen (Nat.lt_add_left o $ Nat.succ_pos p) = p + 1
:= by
  apply heapRemoveLastWithIndexOnlyRemovesOneElement_AuxRLength2Aux (branch v l r h₁ h₂ h₃) (Nat.lt_add_left o $ Nat.succ_pos p)
  unfold leftLen' rightLen'
  simp only [leftLen_unfold, rightLen_unfold]
  assumption

private theorem heapRemoveLastWithIndexOnlyRemovesOneElement_AuxR2Aux {α : Type u} {n : Nat} (tree : CompleteTree α (n+1)) (h₁ : n > 0)
:
  let o := tree.leftLen'
  let p := tree.rightLen'
  (h₂ : p > 0) →
  (h₃ : (p < o ∧ ((p+1).nextPowerOfTwo = p+1 : Bool))) →
  HEq ((Internal.heapRemoveLastWithIndex tree).fst.right h₁) tree.right'
:= by
  simp only
  intro h₂ h₃
  generalize hi : (Internal.heapRemoveLastWithIndex tree).fst = input
  unfold Internal.heapRemoveLastWithIndex Internal.heapRemoveLastAux at hi
  split at hi
  rename_i d1 d2 o2 p vv ll rr m_le_n max_height_difference subtree_complete
  clear d1 d2
  unfold leftLen' rightLen' at*
  rw[leftLen_unfold, rightLen_unfold] at *
  have h₄ : 0 ≠ o2+p := Nat.ne_of_lt h₁
  simp only [h₄, h₃, and_true, reduceDite] at hi
  -- okay, dealing with p.pred.succ is a guarantee for pain. "Stuck at solving universe constraint"
  cases o2
  case zero =>
    exact absurd h₂ $ Nat.not_lt_of_le m_le_n
  case succ oo =>
    simp at hi --whoa, how easy this gets if one just does cases o2...
    unfold right'
    rewrite[right_unfold]
    simp at h₃
    have : (p+1).isPowerOfTwo := by simp[Nat.power_of_two_iff_next_power_eq, h₃.right]
    have h₅ := right_sees_through_cast (by simp_arith: oo + p + 1 = oo + 1 + p) (branch vv
      (Internal.heapRemoveLastAux (β := λn ↦ α × Fin n) ll (fun a => (a, 0))
          (fun {prev_size curr_size} x h₁ => (x.fst, Fin.castLE (by omega) x.snd.succ))
          fun {prev_size curr_size} x left_size h₁ => (x.fst, Fin.castLE (by omega) (x.snd.addNat left_size).succ)).fst
      rr (Nat.le_of_lt_succ h₃.left) (Nat.lt_of_succ_lt max_height_difference) (Or.inr this)) (Nat.succ_pos _) h₁
    rw[right_unfold, hi] at h₅
    exact h₅.symm

private theorem heapRemoveLastWithIndexOnlyRemovesOneElement_AuxR2 {α : Type u} {o p : Nat} (v : α) (l : CompleteTree α o) (r : CompleteTree α (p+1)) (h₁ : (p+1) ≤ o) (h₂ :o < 2 * (p + 1 + 1)) (h₃ : (o + 1).isPowerOfTwo ∨ (p + 1 + 1).isPowerOfTwo) (h₄ : ((p+1) < o ∧ ((p+1+1).nextPowerOfTwo = p+1+1 : Bool)))
:
  HEq ((Internal.heapRemoveLastWithIndex (branch v l r h₁ h₂ h₃)).fst.right (Nat.lt_add_left o $ Nat.succ_pos p)) r
:=
  heapRemoveLastWithIndexOnlyRemovesOneElement_AuxR2Aux (branch v l r h₁ h₂ h₃) (by omega) (Nat.succ_pos _) h₄


/--Helper for heapRemoveLastWithIndexOnlyRemovesOneElement_AuxlIndexNe-/
private theorem heapRemoveLastWithIndexOnlyRemovesOneElement_AuxLIndexNeAux {α : Type u} {n j : Nat} (tree : CompleteTree α (n+1)) (h₁ : (n+1) > 0) (h₂ : j < tree.leftLen h₁) (h₃ : j.succ < (n+1)) (h₄ : tree.rightLen' < tree.leftLen' ∧ ((tree.rightLen'+1).nextPowerOfTwo = tree.rightLen'+1 : Bool)) (h₅ : ⟨j.succ, h₃⟩ ≠ (Internal.heapRemoveLastWithIndex tree).2.snd) : ⟨j, h₂⟩ ≠ (heapRemoveLastWithIndex' (tree.left h₁) (Nat.zero_lt_of_lt h₂)).snd.snd := by
  have h₆ := heapRemoveLastWithIndex'_unfold tree.left' $ Nat.zero_lt_of_lt h₂
  split at h₆
  rename_i d3 d2 d1 oo l o_gt_0 he1 he2 he3
  clear d1 d2 d3
  unfold Internal.heapRemoveLastWithIndex Internal.heapRemoveLastAux at h₅
  split at h₅
  rename_i o2 p vv ll rr _ _ _
  unfold left' rightLen' leftLen' at *
  rw[left_unfold] at *
  rw[leftLen_unfold, rightLen_unfold] at *
  subst he1
  simp at he2
  subst he2
  rw[h₆]
  have : ¬ 0 = oo.succ + p := by omega
  simp only [this, h₄, and_true, reduceDite] at h₅
  rw[←Fin.val_ne_iff] at h₅ ⊢
  simp at h₅
  unfold Internal.heapRemoveLastWithIndex
  assumption

private theorem heapRemoveLastWithIndexOnlyRemovesOneElement_AuxLIndexNe {α : Type u} {o p j : Nat} (v : α) (l : CompleteTree α (o+1)) (r : CompleteTree α p) (h₁ : p ≤ (o+1)) (h₂ : (o+1) < 2 * (p + 1)) (h₃ : (o + 1 + 1).isPowerOfTwo ∨ (p + 1).isPowerOfTwo) (h₄ : j < o+1) (h₅ : p < (o+1) ∧ ((p+1).nextPowerOfTwo = p+1 : Bool)) (h₆ : ⟨j.succ, (by omega)⟩ ≠ (Internal.heapRemoveLastWithIndex (branch v l r h₁ h₂ h₃)).2.snd) : ⟨j,h₄⟩ ≠ (Internal.heapRemoveLastWithIndex l).snd.snd :=
  --splitting at h₅ does not work. Probably because we have o+1...
  --helper function it is...
  heapRemoveLastWithIndexOnlyRemovesOneElement_AuxLIndexNeAux (branch v l r h₁ h₂ h₃) (Nat.succ_pos _) _ (by omega) h₅ h₆

/--Helper for heapRemoveLastWithIndexOnlyRemovesOneElement_AuxlIndexNe-/
private theorem heapRemoveLastWithIndexOnlyRemovesOneElement_AuxRIndexNeAux {α : Type u} {n j : Nat} (tree : CompleteTree α (n+1)) (h₁ : (n+1) > 0) (h₂ : j - tree.leftLen h₁ < tree.rightLen h₁) (h₃ : j.succ < (n+1)) (h₄ : tree.leftLen' ≤ j) (h₅ : ¬(tree.rightLen' < tree.leftLen' ∧ ((tree.rightLen'+1).nextPowerOfTwo = tree.rightLen'+1 : Bool))) (h₆ : ⟨j.succ, h₃⟩ ≠ (Internal.heapRemoveLastWithIndex tree).2.snd) : ⟨j - tree.leftLen h₁, h₂⟩ ≠ (heapRemoveLastWithIndex' (tree.right h₁) (Nat.zero_lt_of_lt h₂)).snd.snd := by
  have h₇ := heapRemoveLastWithIndex'_unfold tree.right' (Nat.zero_lt_of_lt h₂)
  split at h₇
  rename_i d3 d2 d1 pp r o_gt_0 he1 he2 he3
  clear d1 d2 d3
  unfold Internal.heapRemoveLastWithIndex Internal.heapRemoveLastAux at h₆
  split at h₆
  rename_i o p2 vv ll rr _ _ _
  unfold right' rightLen' leftLen' at *
  rw[right_unfold] at *
  rw[leftLen_unfold, rightLen_unfold] at *
  subst he1
  simp at he2
  subst he2
  rw[h₇]
  have : ¬0 = o + pp.succ := by omega
  simp only [this, h₅, and_true, reduceDite] at h₆
  rw[←Fin.val_ne_iff] at h₆ ⊢
  simp at h₆
  unfold Internal.heapRemoveLastWithIndex
  simp[leftLen_unfold]
  rw[Nat.sub_eq_iff_eq_add h₄]
  assumption


private theorem heapRemoveLastWithIndexOnlyRemovesOneElement_AuxRIndexNe {α : Type u} {o p j : Nat} (v : α) (l : CompleteTree α o) (r : CompleteTree α (p+1)) (h₁ : p+1 ≤ o) (h₂ : o < 2 * (p + 1 + 1)) (h₃ : (o + 1).isPowerOfTwo ∨ (p + 1 + 1).isPowerOfTwo) (h₄ : j - o < p + 1) (h₅ : o ≤ j) (h₆ : ¬(p + 1 < o ∧ ((p+1+1).nextPowerOfTwo = p+1+1 : Bool))) (h₇ : ⟨j.succ, (by omega)⟩ ≠ (Internal.heapRemoveLastWithIndex (branch v l r h₁ h₂ h₃)).2.snd) : ⟨j-o,h₄⟩ ≠ (Internal.heapRemoveLastWithIndex r).snd.snd :=
  --splitting at h₅ does not work. Probably because we have o+1...
  --helper function it is...
  heapRemoveLastWithIndexOnlyRemovesOneElement_AuxRIndexNeAux (branch v l r h₁ h₂ h₃) (Nat.succ_pos _) _ _ h₅ h₆ h₇

/--If the resulting tree contains all elements except the removed one, and contains one less than the original, well, you get the idea.-/
protected theorem heapRemoveLastWithIndexOnlyRemovesOneElement {α : Type u} {n : Nat} (heap : CompleteTree α (n+1)) (index : Fin (n+1)) :
  let (newHeap, _, removedIndex) := Internal.heapRemoveLastWithIndex heap
  (h₁ : index ≠ removedIndex) → newHeap.contains (heap.get index (Nat.succ_pos n)) := by
  simp only
  intro h₁
  have h₂ : n > 0 := by omega --cases on n, zero -> h₁ = False as Fin 1 only has one value.
  unfold get get'
  split
  case h_1 o p v l r m_le_n max_height_difference subtree_complete del =>
    -- this should be reducible to heapRemoveLastWithIndexLeavesRoot
    clear del
    unfold contains
    split
    case h_1 _ hx _ => exact absurd hx (Nat.ne_of_gt h₂)
    case h_2 del2 del1 oo pp vv ll rr _ _ _ he heq =>
      clear del1 del2
      left
      have h₃ := heqSameRoot he h₂ heq
      have h₄ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexLeavesRoot ((branch v l r m_le_n max_height_difference subtree_complete)) h₂
      rw[←h₄] at h₃
      rw[root_unfold] at h₃
      rw[root_unfold] at h₃
      exact h₃.symm
  case h_2 j o p v l r m_le_n max_height_difference subtree_complete del h₃ =>
    -- this should be solvable by recursion
    clear del
    simp
    let rightIsFull : Bool := ((p + 1).nextPowerOfTwo = p + 1)
    split
    case isTrue j_lt_o =>
      split
      rename_i o d1 d2 d3 d4 d5 oo l ht1 ht2 ht3 _
      clear d1 d2 d3 d4 d5
      rw[contains_as_root_left_right _ _ (Nat.lt_add_right p $ Nat.succ_pos oo)]
      right
      left
      --unfold Internal.heapRemoveLastWithIndex Internal.heapRemoveLastAux
      --unfolding fails. Need a helper, it seems.
      if h₅ : p < oo + 1 ∧ rightIsFull then
        have h₆ := heapRemoveLastWithIndexOnlyRemovesOneElement_AuxL v l r ht1 ht2 ht3 h₅
        have h₇ := heapRemoveLastWithIndexOnlyRemovesOneElement_AuxLLength v l r ht1 ht2 ht3 h₅
        have h₈ := heqContains h₇ h₆
        rw[h₈]
        have h₉ : ⟨j,j_lt_o⟩ ≠ (Internal.heapRemoveLastWithIndex l).snd.snd := heapRemoveLastWithIndexOnlyRemovesOneElement_AuxLIndexNe v l r ht1 ht2 ht3 j_lt_o h₅ h₁
        exact CompleteTree.AdditionalProofs.heapRemoveLastWithIndexOnlyRemovesOneElement _ _ h₉
      else
        have h₆ := heapRemoveLastWithIndexOnlyRemovesOneElement_AuxL2 v l r ht1 ht2 ht3 h₅
        have h₇ := heapRemoveLastWithIndexOnlyRemovesOneElement_AuxLLength2 v l r ht1 ht2 ht3 h₅
        have h₈ := heqContains h₇ h₆
        rw[h₈]
        rw[contains_iff_index_exists _ _ (Nat.succ_pos oo)]
        exists ⟨j, j_lt_o⟩
    case isFalse j_ge_o =>
      split
      rename_i p d1 d2 d3 d4 d5 h₆ pp r ht1 ht2 ht3 _ h₅
      clear d1 d2 d3 d4 d5
      rw[contains_as_root_left_right _ _ (Nat.lt_add_left o $ Nat.succ_pos pp)]
      right
      right
      -- this should be the same as the left side, with minor adaptations... Let's see.
      if h₇ : pp + 1 < o ∧ rightIsFull then
        have h₈ := heapRemoveLastWithIndexOnlyRemovesOneElement_AuxR2 v l r ht1 ht2 ht3 h₇
        have h₉ := heapRemoveLastWithIndexOnlyRemovesOneElement_AuxRLength2 v l r ht1 ht2 ht3 h₇
        have h₁₀ := heqContains h₉ h₈
        rw[h₁₀]
        rw[contains_iff_index_exists _ _ (Nat.succ_pos pp)]
        have : p = pp.succ := (Nat.add_sub_cancel pp.succ o).subst $ (Nat.add_comm o (pp.succ)).subst (motive := λx ↦ p = x-o ) h₅.symm
        exists ⟨j-o,this.subst h₆⟩
      else
        have h₈ := heapRemoveLastWithIndexOnlyRemovesOneElement_AuxR v l r ht1 ht2 ht3 h₇
        have h₉ := heapRemoveLastWithIndexOnlyRemovesOneElement_AuxRLength v l r ht1 ht2 ht3 h₇
        have h₁₀ := heqContains h₉ h₈
        rw[h₁₀]
        have : p = pp.succ := (Nat.add_sub_cancel pp.succ o).subst $ (Nat.add_comm o (pp.succ)).subst (motive := λx ↦ p = x-o ) h₅.symm
        have h₉ : ⟨j-o,this.subst h₆⟩ ≠ (Internal.heapRemoveLastWithIndex r).snd.snd := heapRemoveLastWithIndexOnlyRemovesOneElement_AuxRIndexNe v l r ht1 ht2 ht3 (this.subst h₆) (by omega) h₇ h₁
        exact CompleteTree.AdditionalProofs.heapRemoveLastWithIndexOnlyRemovesOneElement _ _ h₉

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

protected theorem heapRemoveLastWithIndexEitherContainsOrReturnsElement {α : Type u} {n : Nat} (heap : CompleteTree α (n+1)) (index : Fin (n+1)) :
  let (newHeap, removedElement, _) := Internal.heapRemoveLastWithIndex heap
  newHeap.contains (heap.get index (Nat.succ_pos n)) ∨ removedElement = heap.get index (Nat.succ_pos n)
:=
  let removedIndex := (Internal.heapRemoveLastWithIndex heap).snd.snd
  if h₁ : index ≠ removedIndex then
    Or.inl $ CompleteTree.AdditionalProofs.heapRemoveLastWithIndexOnlyRemovesOneElement heap index h₁
  else by
    right
    have h₂ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexReturnsItemAtIndex heap
    unfold get
    simp at h₁
    subst index
    exact h₂.symm

protected theorem heapRemoveLastEitherContainsOrReturnsElement {α : Type u} {n : Nat} (heap : CompleteTree α (n+1)) (index : Fin (n+1)) :
  let (newHeap, removedElement) := Internal.heapRemoveLast heap
  newHeap.contains (heap.get index (Nat.succ_pos n)) ∨ removedElement = heap.get index (Nat.succ_pos n)
:= by
  have h₁ := CompleteTree.AdditionalProofs.heapRemoveLastWithIndexEitherContainsOrReturnsElement heap index
  simp at h₁ ⊢
  rewrite[CompleteTree.AdditionalProofs.heapRemoveLastWithIndexHeapRemoveLastSameElement]
  rewrite[CompleteTree.AdditionalProofs.heapRemoveLastWithIndexHeapRemoveLastSameTree]
  assumption

protected theorem heapRemoveLastLeavesRoot {α : Type u} {n: Nat} (heap : CompleteTree α (n+1)) (h₁ : n > 0) : heap.root (Nat.succ_pos n) = (CompleteTree.Internal.heapRemoveLast heap).fst.root h₁ :=
  CompleteTree.heapRemoveLastAuxLeavesRoot heap _ _ _ h₁

private theorem heapRemoveLastWithIndexIndexNeZeroForNGt1 {α : Type u} {n : Nat} (heap : CompleteTree α (n+1)) : (CompleteTree.Internal.heapRemoveLastWithIndex heap).snd.snd = 0 ↔ n = 0 := by
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

private theorem heapRemoveLastWithIndexRelationGt_Aux {α : Type u} {o p q : Nat} (index : Fin (((o + 1).add p + 1))) (h₁ : o + 1 + p = o + p + 1) (tree : CompleteTree α (o+p+1)) (h₂ : o + 1 + p > 0) (h₃ : (h₁ ▸ tree).rightLen h₂ > 0) (h₄ : ↑index - 1 - q - 1 < (h₁ ▸ tree).rightLen h₂) (h₅ : o + p + 1 > 0) (h₆ : tree.rightLen h₅ > 0) (h₇ : ↑index - (q + 1) - 1 < tree.rightLen h₅)
:
  get ⟨↑index - 1 - q - 1, h₄⟩
    ((h₁ ▸ tree).right h₂) h₃ =
  get ⟨↑index - (q + 1) - 1, h₇⟩ (tree.right h₅) h₆
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
    exact hp₂ (index.cast this) h₁ tree h₂ h₃ h₄ h₅ h₆ h₇

private theorem heapRemoveLastWithIndexRelationGt_Aux2 {α : Type u} {o p : Nat} (index : Fin (o + 1 + p)) (tree : CompleteTree α (o + p + 1)) (h₁ :  o + p + 1 = o + 1 + p) (h₂ : o + 1 + p > 0) (h₃ : o + p + 1 > 0) (h₄ : index.val < o + p + 1) : get index (h₁▸tree) h₂ = get ⟨index.val,h₄⟩ tree h₃ := by
  induction p generalizing o
  case zero =>
    simp
  case succ pp hp =>
    have hp₂ := hp (o := o+1)
    have hp₃ : (o + 1 + pp + 1) = o + (pp + 1) + 1 := Nat.add_comm_right o 1 (pp + 1)
    have hp₄ : (o + 1 + 1 + pp) = o + 1 + (pp + 1) := (Nat.add_comm_right (o+1) 1 pp).substr $ Nat.add_assoc (o+1) pp 1
    rw[hp₃, hp₄] at hp₂
    exact hp₂ index tree h₁ h₂ h₃ h₄

protected theorem heapRemoveLastWithIndexRelationGt {α : Type u} {n : Nat} (heap : CompleteTree α (n+1)) (index : Fin (n+1)) (h₁ : index > (CompleteTree.Internal.heapRemoveLastWithIndex heap).snd.snd) :
  have : n > 0 := Nat.lt_of_lt_of_le (Fin.pos_iff_ne_zero.mpr $ Fin.ne_zero_of_gt h₁) (Nat.le_of_lt_succ index.isLt)
  (CompleteTree.Internal.heapRemoveLastWithIndex heap).fst.get (index.pred $ Fin.ne_zero_of_gt h₁) this = heap.get index (Nat.succ_pos _)
:= by
have h₂ : 0 ≠ n := Ne.symm $ Nat.ne_zero_iff_zero_lt.mpr $ Nat.lt_of_lt_of_le (Fin.pos_iff_ne_zero.mpr $ Fin.ne_zero_of_gt h₁) (Nat.le_of_lt_succ index.isLt)
revert h₁
unfold Internal.heapRemoveLastWithIndex Internal.heapRemoveLastAux
intro h₁
split at h₁
rename_i o p v l r _ _ _ _
simp only [Nat.add_eq, ne_eq] at h₂
simp only [Nat.add_eq, h₂, ↓reduceDite, decide_eq_true_eq, Fin.zero_eta, Fin.isValue,
  Nat.succ_eq_add_one, Fin.castLE_succ, Nat.pred_eq_sub_one, gt_iff_lt] at h₁ ⊢
split
case isFalse h₃ =>
  --removed right
  simp only [h₃, ↓reduceDite, Fin.isValue] at h₁ ⊢
  cases p <;> simp only [Nat.add_zero, Nat.reduceSub, Nat.reduceAdd, Fin.isValue] at h₁ ⊢
  case zero =>
    simp (config := { ground := true }) only [Nat.zero_add, and_true, Nat.not_lt, Nat.le_zero_eq] at h₃
    subst o
    contradiction
  case succ pp _ _ _ _ =>
    generalize hold : get index (branch v l r _ _ _) _ = oldValue
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
    --exact this.substr h₉ --seems to run into a Lean 4.9 bug when proving termination
    simp only [this, Nat.add_eq, Fin.isValue, h₉] --no idea why simp avoids the same issue...
case isTrue h₃ =>
  --removed left
  simp only [h₃, and_self, ↓reduceDite, Fin.isValue] at h₁ ⊢
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
      case h₃ => exact Nat.succ_pos _
      case h₄ => exact
        Nat.le_of_not_gt h₄
        |> (Nat.succ_pred (Fin.val_ne_of_ne h₅)).substr
        |> Nat.succ_le.mp
        |> Nat.lt_add_right p
        |> (Nat.add_comm_right oo 1 p).subst
      generalize hold :  get index (branch v l r _ _ _) _ = old
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

protected theorem heapRemoveLastWithIndexRelationLt {α : Type u} {n : Nat} (heap : CompleteTree α (n+1)) (index : Fin (n+1)) (h₁ : index < (CompleteTree.Internal.heapRemoveLastWithIndex heap).snd.snd) :
  have hn : n > 0 := Nat.lt_of_lt_of_le (Fin.pos_iff_ne_zero.mpr $ Fin.ne_zero_of_gt h₁) (Nat.le_of_lt_succ (CompleteTree.Internal.heapRemoveLastWithIndex heap).snd.snd.isLt)
  have : index.val < n := Nat.lt_of_lt_of_le h₁ $ Nat.lt_succ.mp (CompleteTree.Internal.heapRemoveLastWithIndex heap).snd.snd.isLt
  (CompleteTree.Internal.heapRemoveLastWithIndex heap).fst.get ⟨index.val, this⟩ hn = heap.get index (Nat.succ_pos _)
:=
  have hn : n > 0 := Nat.lt_of_lt_of_le (Fin.pos_iff_ne_zero.mpr $ Fin.ne_zero_of_gt h₁) (Nat.le_of_lt_succ (CompleteTree.Internal.heapRemoveLastWithIndex heap).snd.snd.isLt)
  have hi : index.val < n := Nat.lt_of_lt_of_le h₁ $ Nat.lt_succ.mp (CompleteTree.Internal.heapRemoveLastWithIndex heap).snd.snd.isLt
  if h₂ : index = 0 then by
    subst index
    simp only [Fin.val_zero]
    have := Fin.zero_eta.subst (motive := λx ↦ heap.root _ = get x heap _) $ get_zero_eq_root heap (Nat.succ_pos _)
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
    rename_i o p v l r _ _ _ _
    simp only [Nat.add_eq, ne_eq] at h₃
    simp only [h₃, Nat.add_eq, Fin.zero_eta, Fin.isValue, decide_eq_true_eq, Nat.succ_eq_add_one,
      Fin.castLE_succ, Nat.pred_eq_sub_one, reduceDite] at h₁ ⊢
    split
    case isFalse h₄ =>
      --removed right
      simp only [h₄, ↓reduceDite, Fin.isValue] at h₁ ⊢
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
    case isTrue h₄ =>
      --removed left
      --get has to go into the square hole - erm, left branch too
      cases o
      case zero =>
        exact absurd h₄.left $ Nat.not_lt_zero _
      case succ oo _ _ _ _ =>
        rewrite[Fin.lt_iff_val_lt_val] at h₁
        simp only [Nat.add_eq, h₄, and_self, ↓reduceDite, Fin.isValue, Fin.val_succ,
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
        case h₃ => exact Nat.succ_pos _
        case h₄ => exact h₆
        rewrite[get_left' _ h₈ h₇]
        have : index.val - 1 < oo + 1 := Nat.sub_one_lt_of_le h₂₂ h₅
        have h₉ : ⟨↑index - 1, this⟩ < (Internal.heapRemoveLastWithIndex l).snd.snd :=
            Nat.sub_lt_of_lt_add h₁ h₂₂
        exact CompleteTree.AdditionalProofs.heapRemoveLastWithIndexRelationLt l ⟨↑index - 1, _⟩ h₉

protected theorem heapRemoveLastWithIndexRelation {α : Type u} {n : Nat} (heap : CompleteTree α (n+1)) (index : Fin (n+1)):
  let (result, removedElement, oldIndex) := CompleteTree.Internal.heapRemoveLastWithIndex heap
  if h₁ : index > oldIndex then
    have : oldIndex ≥ 0 := Fin.zero_le oldIndex
    have : index > 0 := by omega
    result.get (index.pred $ Fin.ne_of_gt this) (by omega) = heap.get index (by omega)
  else if h₂ : index < oldIndex then
    result.get (index.castLT (by omega)) (by omega) = heap.get index (by omega)
  else
    removedElement = heap.get index (Nat.succ_pos _)
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
