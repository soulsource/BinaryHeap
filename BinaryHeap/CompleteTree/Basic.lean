namespace BinaryHeap

inductive CompleteTree (α : Type u) : Nat → Type u
  | leaf : CompleteTree α 0
  | branch :
    (val : α)
    → (left : CompleteTree α n)
    → (right : CompleteTree α m)
    → m ≤ n
    → n < 2*(m+1)
    → (n+1).isPowerOfTwo ∨ (m+1).isPowerOfTwo
    → CompleteTree α (n+m+1)
deriving Repr

/--Creates an empty CompleteTree.-/
abbrev CompleteTree.empty {α : Type u} := CompleteTree.leaf (α := α)

/-- Returns the element stored in the root node. -/
def CompleteTree.root (tree : CompleteTree α n) (_ : 0 < n) : α := match tree with
| .branch a _ _ _ _ _ => a

/-- Same as CompleteTree.root, but a bit more ergonomic to use. However, CompleteTree.root is better suited for proofs-/
def CompleteTree.root' (tree : CompleteTree α (n+1)) : α := tree.root (Nat.zero_lt_succ n)

/-- Extracts the element count. For when pattern matching is too much work. -/
def CompleteTree.length : CompleteTree α n → Nat := λ_ ↦ n

/-- Returns the lenght of the left sub-tree. Mostly exists as a helper for expressing the return type of CompleteTree.left -/
def CompleteTree.leftLen (tree : CompleteTree α n) (_ : n > 0) : Nat := match n, tree with
| (_+_), .branch _ l _ _ _ _ => l.length

def CompleteTree.leftLen' (tree : CompleteTree α (n+1)) : Nat := tree.leftLen (Nat.zero_lt_succ n)

/-- Returns the lenght of the right sub-tree. Mostly exists as a helper for expressing the return type of CompleteTree.right -/
def CompleteTree.rightLen (tree : CompleteTree α n) (_ : n > 0) : Nat := match n, tree with
| (_+_), .branch _ _ r _ _ _ => r.length

def CompleteTree.rightLen' (tree : CompleteTree α (n+1)) : Nat := tree.rightLen (Nat.zero_lt_succ n)

def CompleteTree.left (tree : CompleteTree α n) (h₁ : n > 0) : CompleteTree α (tree.leftLen h₁) := match n, tree with
| (_+_), .branch _ l _ _ _ _ => l

def CompleteTree.left' (tree : CompleteTree α (n+1)) : CompleteTree α (tree.leftLen (Nat.zero_lt_succ n)) := tree.left (Nat.zero_lt_succ n)

def CompleteTree.right (tree : CompleteTree α n) (h₁ : n > 0) : CompleteTree α (tree.rightLen h₁) := match n, tree with
| (_+_), .branch _ _ r _ _ _ => r

def CompleteTree.right' (tree : CompleteTree α (n+1)) : CompleteTree α (tree.rightLen (Nat.zero_lt_succ n)) := tree.right (Nat.zero_lt_succ n)
