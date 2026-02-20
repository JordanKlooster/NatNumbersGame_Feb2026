import NatNumbersGameFeb2026.MyNat
import NatNumbersGameFeb2026.Lemma
import NatNumbersGameFeb2026.NthRewrite


-- for these ones I downloaded the files from the mathlib github and put them in the folder
-- lets you write "lemma" instead of "theorem"
-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Lemma.lean
-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/NthRewrite.lean



-- import Mathlib.Tactic.nth_rw

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
example (a b c : MyNat) : a + (b + 0) + (c + 0) = a + b + c := by
    repeat rw[add_zero] -- repeat makes it do thing multiple times
  -- rw[add_zero]
  -- rfl

-- example tut6_8 -- change the +0 with c first
example (a b c : MyNat) : a + (b + 0) + (c + 0) = a + b + c := by
rw [add_zero c]
rw [add_zero]


-- another way to show the first part
example (a b c : MyNat) : a + (b + 0) + (c + 0) = a + (b + 0) + c := by
rw [add_zero c]

--add_zero c is a proof of c + 0 = c so that was what got rewritten. You can
--now change b + 0 to b with rw [add_zero] or rw [add_zero b].
--You can usually stick to rw [add_zero] unless you need real precision.


-- add_succ is now allowed    a + MyNat.succ d = MyNat.succ (a + d)

-- example tut7_8
theorem succ_eq_add_one (n : MyNat)  : succ n = n + 1 := by
  rw [one_eq_succ_zero]
  rw [add_succ]
  rw [add_zero]

lemma succ_eq_add_one2 (n : MyNat)  : succ n = n + 1 := by
  rw [one_eq_succ_zero]
  rw [add_succ]
  rw [add_zero]



--example tut8_8 -- change the +0 with c first
example : (2 : MyNat) + 2 = 4 := by
  nth_rewrite 2 [two_eq_succ_one]
  nth_rewrite 1 [one_eq_succ_zero]
  nth_rw 1 [add_succ]
  nth_rw 1 [add_succ]
  rw [add_zero]
  rw [<- three_eq_succ_two]
  rw [<- four_eq_succ_three]

example : (2 : MyNat) + 2 = 4 := by
  nth_rewrite 2 [two_eq_succ_one] -- only change the second `2` to `succ 1`.
  rw [add_succ]
  rw [one_eq_succ_zero]
  rw [add_succ, add_zero] -- two rewrites at once
  rw [← three_eq_succ_two] -- change `succ 2` to `3`
  rw [← four_eq_succ_three]
