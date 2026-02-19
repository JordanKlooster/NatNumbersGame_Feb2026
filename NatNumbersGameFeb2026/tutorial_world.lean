-- import Mathlib.lemma
-- import lemma.olean -- local file?
-- import MyNat.lemma
import NatNumbersGameFeb2026.MyNat

/- For all natural numbers x, y, z, we have
x * y + z = x * y + z
-/
open MyNat -- allows use of succ, zero and such without MyNat.succ


-- example 1
-- example (x y z : MyNat) : x * y + z = x * y + z := by
-- sorry

-- ALLOWED TO USE rfl
example (x y z : MyNat) : x * y + z = x * y + z := by
  rfl

-- example 2        https://youtu.be/bo95_OtujxY?list=PLCaPonEDDnrkDQVfxWiYdF0tYOYRyLI3N&t=562
-- example (x y : MyNat) (h: y = x + 7): 2 * y = 2 * (x + 7) := by
-- sorry

-- ALLOWED TO USE rewrite[] or rw[]
example (x y : MyNat) (h: y = x + 7): 2 * y = 2 * (x + 7) := by
  rewrite [<- h]
  rfl



-- example 3        https://youtu.be/bo95_OtujxY?list=PLCaPonEDDnrkDQVfxWiYdF0tYOYRyLI3N&t=562
-- theorem add_zero (a : MyNat): a + 0 = a := by
-- sorry
theorem add_zero (a : MyNat): a + 0 = a := by
rfl


theorem add_succ (a d : MyNat): a + succ d = succ (a + d) := by
rfl


-- https://youtu.be/bo95_OtujxY?list=PLCaPonEDDnrkDQVfxWiYdF0tYOYRyLI3N&t=1119
-- theorem zero_add (a : MyNat): 0 + a = a := by
-- sorry

theorem zero_succ_add1 (a : MyNat): a + succ 0 = succ a := by
rfl
theorem zero_succ_add (a : MyNat): a + succ 0 = succ a := by
  rewrite [add_succ, add_zero]
  rfl
theorem zero_succ_add2 (a : MyNat): a + succ 0 = succ a := by
  rw [add_succ, add_zero]
  -- rfl



--FROM WEBSITE
-- NOTE Website has rewrite shortened to rw but here rw checks rfl after

-- example tut1_8
example (x q : MyNat) : 37 * x + q = 37 * x + q := by rfl

-- example tut1_8
example (x q : MyNat) : 37 * x + q = 37 * x + q := by rfl



-- example tut2_8
example (x y : MyNat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw[h]
  -- rfl
example (x y : MyNat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rewrite[h]
  rfl


-- New Theorems
theorem one_eq_succ_zero : 1 = succ 0 := by
  rfl
theorem two_eq_succ_one : 2 = succ 1 := by
  rfl
theorem three_eq_succ_two : 3 = succ 2 := by
  rfl
theorem four_eq_succ_three : 4 = succ 3 := by
  rfl

-- example tut3_8
example : 2 = succ (succ 0) := by
  rw [two_eq_succ_one]
  rw [one_eq_succ_zero]
  -- rfl
example : 2 = succ (succ 0) := by
  -- rw [two_eq_succ_one]
  -- rw [one_eq_succ_zero]
  rewrite [two_eq_succ_one]
  rewrite [one_eq_succ_zero]
  rfl
--

-- example tut4_8
-- do it with <- rewrites
example : 2 = succ (succ 0) := by
  rw [<-one_eq_succ_zero]
  rw [<- two_eq_succ_one]
example : 2 = succ (succ 0) := by
  rewrite [<-one_eq_succ_zero]
  rewrite [<- two_eq_succ_one]
  rfl

-- example tut5_8
example (a b c : MyNat) : a + (b + 0) + (c + 0) = a + b + c := by
  rw[add_zero]
  rw[add_zero]
example (a b c : MyNat) : a + (b + 0) + (c + 0) = a + b + c := by
  rewrite [add_zero]
  rewrite [add_zero]
  rfl
