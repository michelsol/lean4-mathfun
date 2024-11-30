import Mathlib


open Finset BigOperators

/- exercise 1 -/
example {a r : ℝ} (n : ℕ) (h : r ≠ 1) : ∑ i ∈ range (n+1), a * r^i = (a * r^(n+1) - a) / (r-1) := by
  rw [←mul_sum] -- pull the a * out of the ∑
  rw [←Nat.Ico_zero_eq_range] -- rewrite the range as an interval
  rw [geom_sum_Ico h (by simp)] -- use the standard geometric sum result
  ring




/- exercise 2 -/

/-
Let $n$ and $k$ be nonnegative integers with $k \leqslant n$. Then
(i ) $\binom{n}{0}=\binom{n}{n}=1$
(ii) $\binom{n}{k}=\binom{n}{n-k}$.
-/

section
-- these results already exist in mathlib
variable (n k : ℕ) (h : k ≤ n)
example : n.choose 0 = 1 := n.choose_zero_right
example : n.choose n = 1 := n.choose_self
example : n.choose k = n.choose (n - k) := (Nat.choose_symm h).symm
end

namespace Nat
-- here is another custom implementation using the traditional math definition
def choose' (n : ℕ) (k : ℕ) : ℕ := n ! / (k ! * (n - k) !)

theorem choose'_zero (n : ℕ) : n.choose' 0 = 1 := by
  induction n
  case zero => simp [choose']
  case succ n ih =>
    have : n + 1 ≠ 0 := n.zero_ne_add_one.symm
    rify at ih this ⊢ -- more lemmas are in ℝ, as div is not well behaved in ℕ
    simp [choose'] at ih
    simp [choose', factorial, mul_div_mul_comm, this, ih]

theorem choose'_sym {n k : ℕ} (h : k ≤ n) : n.choose' k = n.choose' (n - k) := by
  simp [choose', Nat.sub_sub_self h, mul_comm]

theorem choose'_self (n : ℕ) : n.choose' n = 1 := by
  simp [choose'_sym n.le_refl, choose'_zero]

end Nat



/- exercise 3 -/

/-
We define a function recursively for all positive integers $n$ by
$f(1)=1$, $f(2)=5$, and for $n>2, f(n+1)=f(n)+2 f(n-1)$.
Show that $f(n)=$ $2^{n}+(-1)^{n}$, using the second principle of mathematical induction.
-/

-- a solution using pattern matching
def f : (n : ℕ) → ℕ
  | 0 => 0 -- just like mathlib's style, we prefer avoiding an extra n > 0 assumption
  | 1 => 1
  | 2 => 5
  | k + 3 =>
    let n := k + 2
    f n + 2 * f (n - 1)

example {n : ℕ} (h : n ≠ 0) : f n = 2 ^ n + (-1 : ℤ) ^n := by
  induction n using f.induct with -- functional induction is available thanks to defining f by pattern matching
  | case1 => contradiction
  | case2 => rfl
  | case3 => rfl
  | case4 n ih2 ih1 =>
    simp [f, ih1, ih2]
    ring


-- another more mathematically traditional solution
def g (k : ℕ) : ℕ :=
  if k = 0 then 0 else
  if k = 1 then 1 else
  if k = 2 then 5 else
    let n := k - 1
    g n + 2 * g (n - 1)

example {n : ℕ} (h : n ≠ 0) : g n = 2 ^ n + (-1 : ℤ) ^n := by
  induction n using Nat.twoStepInduction
  . contradiction
  . simp [g]
  case _ n ih1 ih2 =>
    rw [g]
    split_ifs <;> try contradiction
    . simp [*]
    . simp [*]
    . simp_all [ih1, ih2]
      ring




-- lazier proof of the initial example using heavy duty tactics
example (n : ℕ) : ∑ i in (range (n + 1)), i = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; ring; omega
