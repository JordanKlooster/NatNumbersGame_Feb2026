

-- explain all these keywords
inductive MyNat where
  | zero : MyNat
  | succ : MyNat -> MyNat
  deriving Repr

#check MyNat.zero   -- just zero
#check MyNat.succ   -- a function

#check MyNat.succ (MyNat.zero) --type is MyNat
#check MyNat.succ MyNat.zero -- same thing as above

#eval MyNat.succ (MyNat.zero) -- MyNat.succ (MyNat.zero)
#eval MyNat.succ MyNat.zero --also MyNat.succ (MyNat.zero)


-- open is like opening namespace,
-- so I can just type "zero" instead of "MyNat.zero"
open MyNat
#eval succ zero -- shorter version of "#eval MyNat.succ MyNat.zero"


-- add m and n
def add (m: MyNat) (n: MyNat) : MyNat :=
  match n with
  | zero => m
  | succ n' => succ (add m n') -- n' is n-1

-- add 2 1 -- should be 3
#eval add (succ (succ zero)) (succ zero)
-- this works

--allows converting Nat to MyNat
def nat_to_mynat (n : Nat): MyNat :=
  match n with
  | Nat.zero => MyNat.zero
  | Nat.succ n' => MyNat.succ (nat_to_mynat n')

#eval add (nat_to_mynat 7) (nat_to_mynat 8)

-- auto converts to my nat
instance : OfNat MyNat n where
ofNat := nat_to_mynat n

#eval add 7 8 -- automatic with the instance thing

-- allow converting back for nice displaying of numbers
def mynat_to_nat (n : MyNat): Nat :=
  match n with
  | MyNat.zero => Nat.zero
  | MyNat.succ n' => Nat.succ (mynat_to_nat n')

#eval mynat_to_nat (add 7 8)  -- can display nicely as 15 instead of succ succ succ...
example : add 7 8 = 15 := rfl -- proof (via reflexivity) that 7+8=15 with our function


def mul (m n : MyNat) : MyNat :=
  match n with
  | zero => zero
  | succ (zero) => m
  | succ n' => add m (mul m n') -- n' is n - 1

example : mul 4 3 = 12 := rfl
#eval mynat_to_nat (mul 4 3)
example : mul 1 3 = 3 := rfl
#eval mynat_to_nat (mul 1 3)
example : mul 4 1 = 4 := rfl
#eval mynat_to_nat (mul 4 1)
example : mul 0 3 = 0 := rfl
#eval mynat_to_nat (mul 0 3)
example : mul 4 0 = 0 := rfl
#eval mynat_to_nat (mul 4 0)


-- maps Nat add to MyNat add, allows "+"
instance : Add MyNat where
  add := add
#eval mynat_to_nat (4 + 3)

-- maps Nat mul to MyNat mul, allows "*"
instance : Mul MyNat where
  mul := mul
#eval mynat_to_nat (4 * 3)
