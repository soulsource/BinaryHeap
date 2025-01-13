import BinaryHeap.CompleteTree.Basic
import BinaryHeap.CompleteTree.NatLemmas

namespace BinaryHeap.CompleteTree

----------------------------------------------------------------------------------------------
-- heapPush

/-Lemma needed to show completeness of tree in heapPush.-/
private theorem power_of_two_mul_two_lt {n m : Nat} (h₁ : m.isPowerOfTwo) (h₂ : n < 2*m) (h₃ : ¬(n+1).isPowerOfTwo) : n+1 < 2*m :=
  if h₄ : n+1 > 2*m then
    absurd h₄ ((Nat.not_lt_eq (2*m) (n+1)).substr $ Nat.succ_le_of_lt h₂)
  else if h₅ : n+1 = 2*m then
    have h₆ : (2*m).isPowerOfTwo := (Nat.mul_comm 2 m).substr $ Nat.mul2_isPowerOfTwo_of_isPowerOfTwo h₁
    have h₇ : (n+1).isPowerOfTwo := h₅.substr h₆
    absurd h₇ h₃
  else
    Nat.lt_of_le_of_ne ((Nat.not_lt_eq _ _).mp h₄) h₅

/--Adds a new element to a given CompleteTree.-/
def heapPush (le : α → α → Bool) (elem : α) (heap : CompleteTree α o) : CompleteTree α (o+1) :=
  match o, heap with
  | 0, .leaf => .branch elem (.leaf) (.leaf) (Nat.le_refl 0) (by decide) (Or.inl Nat.one_isPowerOfTwo)
  | (n+m+1), .branch a left right p max_height_difference subtree_complete =>
    let (elem, a) := if le elem a then (a, elem) else (elem, a)
    -- okay, based on n and m we know if we want to add left or right.
    -- the left tree is full, if (n+1) is a power of two AND n != m
    let leftIsFull := (n+1).nextPowerOfTwo = n+1
    if r : m < n ∧ leftIsFull  then
      have s : (m + 1 < n + 1) = (m < n) := by simp_arith
      have q : m + 1 ≤ n := by apply Nat.le_of_lt_succ
                               rewrite[Nat.succ_eq_add_one]
                               rewrite[s]
                               simp[r]
      have difference_decreased := Nat.le_succ_of_le $ Nat.le_succ_of_le max_height_difference
      let result := branch a left (right.heapPush le elem) (q) difference_decreased (Or.inl $ (Nat.power_of_two_iff_next_power_eq (n+1)).mpr r.right)
      result
    else
      have q : m ≤ n+1 := by apply (Nat.le_of_succ_le)
                             simp_arith[p]
      have right_is_power_of_two : (m+1).isPowerOfTwo :=
        if s : n = m then
          s.subst (motive := λx ↦ (x+1).isPowerOfTwo ∨ (m+1).isPowerOfTwo) subtree_complete
          |> (or_self _).mp
        else if h₁ : leftIsFull then by
          rewrite[Decidable.not_and_iff_or_not (p := m<n) (q := leftIsFull)] at r
          cases r
          case inl h₂ => rewrite[Nat.not_lt_eq] at h₂
                         have h₃ := Nat.not_le_of_gt $ Nat.lt_of_le_of_ne h₂ s
                         contradiction
          case inr h₂ => simp at h₂
                         contradiction
        else
          have : leftIsFull = ((n + 1).nextPowerOfTwo = n + 1) := rfl
          have h₁ := h₁ ∘ this.mp ∘ (Nat.power_of_two_iff_next_power_eq (n+1)).mp
          match subtree_complete with
          | .inl h₂ => absurd h₂ h₁
          | .inr h₂ => h₂
      have still_in_range : n + 1 < 2 * (m + 1) := by
        rewrite[Decidable.not_and_iff_or_not (p := m<n) (q := leftIsFull)] at r
        cases r
        case inl h₁ => rewrite[Nat.not_gt_eq n m] at h₁
                       simp_arith[Nat.le_antisymm h₁ p]
        case inr h₁ => simp[←Nat.power_of_two_iff_next_power_eq, leftIsFull] at h₁
                       simp[h₁] at subtree_complete
                       exact power_of_two_mul_two_lt subtree_complete max_height_difference h₁
      let result := branch a (left.heapPush le elem) right q still_in_range (Or.inr right_is_power_of_two)
      have letMeSpellItOutForYou : n + 1 + m + 1 = n + m + 1 + 1 := by simp_arith
      letMeSpellItOutForYou ▸ result

----------------------------------------------------------------------------------------------
-- heapRemoveLast (with Index)

/-- Helper for heapRemoveLastAux -/
private theorem power_of_two_mul_two_le {n m : Nat} (h₁ : (n+1).isPowerOfTwo) (h₂ : n < 2*(m+1)) (h₃ : ¬(m+1).isPowerOfTwo) (h₄ : m > 0): n < 2*m :=
  if h₅ : n > 2*m then
    have h₆ : n + 1 = 2*(m+1) := congrArg Nat.succ $ Nat.eq_of_le_of_lt_succ h₅ h₂
    have h₇ : (2*(m+1)).isPowerOfTwo := h₆.subst h₁
    have h₈ : (m+1).isPowerOfTwo := (Nat.mul2_ispowerOfTwo_iff_isPowerOfTwo (m+1)).mpr h₇
    absurd h₈ h₃
  else if h₆ : n = 2*m then
    -- since (n+1) is a power of 2, n cannot be an even number, but n = 2*m means it's even
    -- ha, thought I wouldn't see that, didn't you? Thought you're smarter than I, computer?
    have h₇ : n > 0 := h₆.substr $ (Nat.mul_lt_mul_left (Nat.succ_pos 1 : 2 > 0)).mpr h₄
    have h₈ : n ≠ 0 := Ne.symm $ Nat.ne_of_lt h₇
    have h₉ : (n+1).isEven := (Nat.isPowerOfTwo_even_or_one h₁).resolve_left
      $ if h : n+1=1 then absurd (Nat.succ.inj h) h₈ else h
    have h₉ : n.isOdd := Nat.pred_even_odd h₉ (by simp_arith[h₇])
    have h₁₀ : ¬n.isOdd := Nat.even_not_odd_even.mp $ Nat.mul_2_is_even h₆
    absurd h₉ h₁₀
  else
    have h₅ : n ≤ 2*m := (Nat.not_gt_eq _ _).mp h₅
    have h₅ : n=2*m ∨ n < 2*m := Nat.eq_or_lt_of_le h₅
    h₅.resolve_left h₆

/-- Helper for heapRemoveLastAux -/
private theorem removeRightRightNotEmpty {n m : Nat} (m_gt_0_or_rightIsFull : m > 0 ∨ ((m+1).nextPowerOfTwo = m+1 : Bool)) (h₁ : 0 ≠ n + m) (h₂ : ¬(m < n ∧ ((m+1).nextPowerOfTwo = m+1 : Bool))) : m > 0 :=
  match m_gt_0_or_rightIsFull with
  | Or.inl h => h
  | Or.inr h => by
    simp only [h, and_true, Nat.not_lt] at h₂
    cases n
    case zero => exact Nat.zero_lt_of_ne_zero $ (Nat.zero_add m).subst (motive := (·≠0)) h₁.symm
    case succ q =>
      cases m
      . exact absurd h₂ $ Nat.not_succ_le_zero q
      . exact Nat.succ_pos _

/-- Helper for heapRemoveLastAux -/
private theorem removeRightLeftIsFull {n m : Nat} (r : ¬(m < n ∧ ((m+1).nextPowerOfTwo = m+1 : Bool))) (m_le_n : m ≤ n) (subtree_complete : (n + 1).isPowerOfTwo ∨ (m + 1).isPowerOfTwo) : (n+1).isPowerOfTwo := by
  rewrite[Decidable.not_and_iff_or_not] at r
  cases r
  case inl h₁ => rewrite[Nat.not_lt_eq] at h₁
                 have h₂ := Nat.le_antisymm h₁ m_le_n
                 rewrite[←h₂] at subtree_complete
                 simp at subtree_complete
                 assumption
  case inr h₁ => simp(config := {zetaDelta := true })[←Nat.power_of_two_iff_next_power_eq] at h₁
                 simp[h₁] at subtree_complete
                 assumption

/-- Helper for heapRemoveLastAux -/
private theorem stillInRange {n m : Nat} (r : ¬(m < n ∧ ((m+1).nextPowerOfTwo = m+1 : Bool))) (m_le_n : m ≤ n) (m_gt_0 : m > 0) (leftIsFull : (n+1).isPowerOfTwo) (max_height_difference: n < 2 * (m + 1)) : n < 2*m := by
  rewrite[Decidable.not_and_iff_or_not] at r
  cases r with
  | inl h₁ => have m_eq_n : m = n := Nat.le_antisymm m_le_n (Nat.not_lt.mp h₁)
              have m_lt_2_m : m < 2 * m := (Nat.one_mul m).subst (motive := λ x ↦ x < 2 * m) $ Nat.mul_lt_mul_of_pos_right Nat.one_lt_two m_gt_0
              exact m_eq_n.subst (motive := λx ↦ x < 2 * m) m_lt_2_m
  | inr h₁ => simp (config := { zetaDelta := true }) only [← Nat.power_of_two_iff_next_power_eq, decide_eq_true_eq] at h₁
              apply power_of_two_mul_two_le <;> assumption

/--
  Removes the last element, and computes additional values via the supplied lambdas.

  **BEWARE** that "last" here means the underlying complete tree. It is *not* the elemenent
  at the largest index, nor is it the largest element in the heap.
-/
protected def Internal.heapRemoveLastAux
{α : Type u}
{β : Nat → Type u}
{o : Nat}
(heap : CompleteTree α (o+1))
(aux0 : α → (β 1))
(auxl : {prev_size curr_size : Nat} → β prev_size → (h₁ : prev_size < curr_size) → β curr_size)
(auxr : {prev_size curr_size : Nat} → β prev_size → (left_size : Nat) → (h₁ : prev_size + left_size < curr_size) → β curr_size)
: (CompleteTree α o × (β (o+1)))
:=
  match o, heap with
  | (n+m), .branch a (left : CompleteTree α n) (right : CompleteTree α m) m_le_n max_height_difference subtree_complete =>
    if p : 0 = (n+m) then
      (p▸CompleteTree.leaf, p▸aux0 a)
    else
      let rightIsFull : Bool := (m+1).nextPowerOfTwo = m+1
      have m_gt_0_or_rightIsFull : m > 0 ∨ rightIsFull := by cases m <;> simp (config := { ground:=true })[rightIsFull]
      if r : m < n ∧ rightIsFull then
        --remove left
        match n, left with
        | (l+1), left =>
          let ((newLeft : CompleteTree α l), res) := Internal.heapRemoveLastAux left aux0 auxl auxr
          have q : l + m + 1 = l + 1 + m := Nat.add_right_comm l m 1
          have s : m ≤ l := Nat.le_of_lt_succ r.left
          have rightIsFull : (m+1).isPowerOfTwo := (Nat.power_of_two_iff_next_power_eq (m+1)).mpr $ decide_eq_true_eq.mp r.right
          have l_lt_2_m_succ : l < 2 * (m+1) := Nat.lt_of_succ_lt max_height_difference
          let res := auxl res (by simp_arith)
          (q▸CompleteTree.branch a newLeft right s l_lt_2_m_succ (Or.inr rightIsFull), res)
      else
        --remove right
        have m_gt_0 : m > 0 := removeRightRightNotEmpty m_gt_0_or_rightIsFull p r
        let l := m.pred
        have h₂ : l.succ = m := (Nat.succ_pred $ Nat.not_eq_zero_of_lt (Nat.gt_of_not_le $ Nat.not_le_of_gt m_gt_0))
        let ((newRight : CompleteTree α l), res) := Internal.heapRemoveLastAux (h₂.symm▸right : CompleteTree α l.succ) aux0 auxl auxr
        have leftIsFull : (n+1).isPowerOfTwo := removeRightLeftIsFull r m_le_n subtree_complete
        have still_in_range : n < 2 * (l+1) := h₂.substr (p := λx ↦ n < 2 * x) $ stillInRange r m_le_n m_gt_0 leftIsFull max_height_difference
        let res := auxr res n (by omega)
        (h₂▸CompleteTree.branch a left newRight (Nat.le_of_succ_le (h₂▸m_le_n)) still_in_range (Or.inl leftIsFull), res)

/--
  Removes the last element in the complete Tree. This is **NOT** the element with the
  largest index, nor is it the largest element in the heap.
-/
protected def Internal.heapRemoveLast {α : Type u} {o : Nat} (heap : CompleteTree α (o+1)) : (CompleteTree α o × α) :=
  Internal.heapRemoveLastAux heap id (λ(a : α) _ ↦ a) (λa _ _ ↦ a)

/--
  Removes the last element in the complete Tree. This is **NOT** the element with the
  largest index, nor is it the largest element in the heap.

  Also returns the index of the removed element.
-/
protected def Internal.heapRemoveLastWithIndex {α : Type u} {o : Nat} (heap : CompleteTree α (o+1)) : (CompleteTree α o × α × Fin (o+1)) :=
  Internal.heapRemoveLastAux heap (β := λn ↦ α × Fin n)
  (λ(a : α) ↦ (a, Fin.mk 0 (Nat.succ_pos 0)))
  (λ(a, prev_idx) h₁ ↦ (a, prev_idx.succ.castLE $ Nat.succ_le_of_lt h₁) )
  (λ(a, prev_idx) left_size h₁ ↦ (a, (prev_idx.addNat left_size).succ.castLE $ Nat.succ_le_of_lt h₁))

----------------------------------------------------------------------------------------------
-- heapUpdateRoot

/--
  Helper for heapUpdateAt. Makes proofing heap predicate work in Lean 4.9
  -/
def heapUpdateRoot  {α : Type u} {n : Nat} (_ : n > 0) (le : α → α → Bool) (value : α) (heap : CompleteTree α n) : CompleteTree α n × α :=
match n, heap with
  | (o+p+1), .branch v l r h₃ h₄ h₅ =>
    if h₆ : o = 0 then
      -- have : p = 0 := (Nat.le_zero_eq p).mp $ h₇.subst h₃ --not needed, left here for reference
      (.branch value l r h₃ h₄ h₅, v)
    else
      have h₇ : o > 0 := Nat.zero_lt_of_ne_zero h₆
      let lr := l.root h₇
      if h₈ : p = 0 then
        if le value lr then
          (.branch value l r h₃ h₄ h₅, v)
        else
          -- We would not need to recurse further, because we know o = 1.
          -- However, that would introduce type casts, what makes proving harder...
          -- have h₉: o = 1 := Nat.le_antisymm (by simp_arith[h₈] at h₄; exact h₄) (Nat.succ_le_of_lt h₇)
          let ln := heapUpdateRoot h₇ le value l
          (.branch ln.snd ln.fst r h₃ h₄ h₅, v)
      else
        have h₉ : p > 0 := Nat.zero_lt_of_ne_zero h₈
        let rr := r.root h₉
        if le value lr ∧ le value rr then
          (.branch value l r h₃ h₄ h₅, v)
        else if le lr rr then -- value is gt either left or right root. Move it down accordingly
          let ln := heapUpdateRoot h₇ le value l
          (.branch ln.snd ln.fst r h₃ h₄ h₅, v)
        else
          let rn := heapUpdateRoot h₉ le value r
          (.branch rn.snd l rn.fst h₃ h₄ h₅, v)

----------------------------------------------------------------------------------------------
-- heapRemoveAt

def heapUpdateAtAux {α : Type u} {n : Nat} (le : α → α → Bool) (index : Fin n) (value : α) (heap : CompleteTree α n) (h₁ : n > 0) : CompleteTree α n × α :=
  if h₂ : index == ⟨0,h₁⟩ then
    heapUpdateRoot h₁ le value heap
  else
    match n, heap with
    | (o+p+1), .branch v l r h₃ h₄ h₅ =>
      let (v, value) := if le v value then (v, value) else (value, v)
      if h₆ : index ≤ o then
        have h₇ : Nat.pred index.val < o := Nat.lt_of_lt_of_le (Nat.pred_lt $ Fin.val_ne_of_ne (ne_of_beq_false $ Bool.of_not_eq_true h₂)) h₆
        let index_in_left : Fin o := ⟨index.val.pred, h₇⟩
        have h₈ : 0 < o := Nat.zero_lt_of_lt h₇
        let result := heapUpdateAtAux le index_in_left value l h₈
        (.branch v result.fst r h₃ h₄ h₅, result.snd)
      else
        have h₇ : index.val - (o + 1) < p :=
          -- tactic rewrite failed, result is not type correct.
          have h₈ : index.val < p + o + 1 := index.isLt
            |> (Nat.add_assoc o p 1).subst
            |> (Nat.add_comm p 1).subst (motive := λx ↦ index.val < o + x)
            |> (Nat.add_assoc o 1 p).symm.subst
            |> (Nat.add_comm (o+1) p).subst
          Nat.sub_lt_of_lt_add h₈ $ (Nat.not_le_eq index.val o).mp h₆
        let index_in_right : Fin p := ⟨index.val - o - 1, h₇⟩
        have h₈ : 0 < p := Nat.zero_lt_of_lt h₇
        let result := heapUpdateAtAux le index_in_right value r h₈
        (.branch v l result.fst h₃ h₄ h₅, result.snd)

/--
  Helper for heapRemoveAt.
  Removes the element at index, and instead inserts the given value.
  Returns the element at index, and the resulting tree.
  -/
def heapUpdateAt {α : Type u} {n : Nat} (le : α → α → Bool) (index : Fin n) (value : α) (heap : CompleteTree α n) : CompleteTree α n × α :=
  heapUpdateAtAux le index value heap (Nat.zero_lt_of_lt index.isLt)

----------------------------------------------------------------------------------------------
-- heapPop

def heapPop {α : Type u} {n : Nat} (le : α → α → Bool) (heap : CompleteTree α (n+1)) : α × CompleteTree α n :=
  let l := Internal.heapRemoveLast heap
  if p : n > 0 then
    Prod.swap $ heapUpdateRoot p le l.snd l.fst
  else
    Prod.swap l
where Prod.swap := λ(a,b)↦(b,a)

----------------------------------------------------------------------------------------------
-- heapRemoveAt

/--Removes the element at a given index. Use `indexOf` to find the respective index.-/
def heapRemoveAt {α : Type u} {n : Nat} (le : α → α → Bool) (index : Fin (n+1)) (heap : CompleteTree α (n+1)) : α × CompleteTree α n :=
  --Since we cannot even temporarily break the completeness property, we go with the
  --version from Wikipedia: We first remove the last element, and then update values in the tree
  --indices are depth first, but "last" means last element of the complete tree.
  --sooo:
  if index_ne_zero : index = 0 then
    heapPop le heap
  else
    let (remaining_tree, removed_element, removed_index) := Internal.heapRemoveLastWithIndex heap
    if index = removed_index then
      (removed_element, remaining_tree)
    else
      if index_lt_lastIndex : index ≥ removed_index then
        let index := index.pred index_ne_zero
        Prod.swap $ heapUpdateAt le index removed_element remaining_tree
      else
        let h₁ : index < n := by omega
        let index : Fin n := ⟨index, h₁⟩
        Prod.swap $ heapUpdateAt le index removed_element remaining_tree
where Prod.swap := λ(a,b)↦(b,a)
