import Mathlib.Tactic.Linarith

-- TactusTutorialHelpers.lean
--
-- Unconditional simp lemmas for the toNat shapes that come out of
-- Tactus rendering Verus's `(n - 1) as nat` style casts.

@[simp] theorem TactusTut.toNat_succ_sub_one (k : ℕ) :
    ((↑(k + 1) : Int) - 1).toNat = k := by omega

@[simp] theorem TactusTut.toNat_succ_succ_sub_one (k : ℕ) :
    ((↑(k + 1 + 1) : Int) - 1).toNat = k + 1 := by omega

@[simp] theorem TactusTut.toNat_succ_succ_sub_two (k : ℕ) :
    ((↑(k + 1 + 1) : Int) - 2).toNat = k := by omega

@[simp] theorem TactusTut.toNat_add_one_sub_one (k : ℕ) :
    ((↑k + 1 : Int) - 1).toNat = k := by omega

@[simp] theorem TactusTut.toNat_add_one_add_one_sub_two (k : ℕ) :
    ((↑k + 1 + 1 : Int) - 2).toNat = k := by omega
