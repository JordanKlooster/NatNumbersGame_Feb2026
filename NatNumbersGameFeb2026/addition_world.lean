import NatNumbersGameFeb2026.MyNat
import NatNumbersGameFeb2026.Lemma
import NatNumbersGameFeb2026.NthRewrite
import NatNumbersGameFeb2026.tutorial_world




-- new tactic: induction
-- open MyNat
-- open tutorial_world

theorem zero_add (n : MyNat) : 0 + n = n :=
by
  induction n with
  -- | rw [add_zero]
  -- |
