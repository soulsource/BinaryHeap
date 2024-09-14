/-
  This file contains proofs for relations that might be helpful for creating heaps.
 -/
import BinaryHeap.HeapPredicate

namespace BinaryHeap

/--Helper for the common case of using natural numbers for sorting.-/
theorem nat_ble_to_heap_le_total : total_le Nat.ble :=
  λa b ↦ Nat.ble_eq.substr $ Nat.ble_eq.substr (Nat.le_total a b)

/--Helper for the common case of using natural numbers for sorting.-/
theorem nat_ble_to_heap_transitive_le : transitive_le Nat.ble :=
  λ a b c ↦
    Nat.le_trans (n := a) (m := b) (k := c)
    |> Nat.ble_eq.substr
    |> Nat.ble_eq.substr
    |> Nat.ble_eq.substr
    |> and_imp.mpr
