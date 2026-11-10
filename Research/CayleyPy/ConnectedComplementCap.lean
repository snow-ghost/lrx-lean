module

public import Mathlib.Algebra.Ring.Fin
public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic

@[expose] public section

/-!
Phase80: the complement-of-a-gap estimate from the submitted proof.
This file proves the unbounded arithmetic implications. The finite
footrule inequality, source-packet geometry, exact service construction,
and quadratic gap-service lemma are explicit mathematical inputs.
-/
namespace CayleyPy.ConnectedComplementCap

theorem dominant_square_upper
    (p eta t b c e s G H squares : ℤ)
    (heta : eta=0 ∨ eta=1) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hb : b=t+c+e) (hs : s=b+c+e)
    (hG : 4*G=(s+eta)^2-p) (hsquares : squares ≤ b^2+c^2) :
    2*(squares-2*G-2*H) ≤ (t-eta)^2+p-2*eta-4*H := by
  subst b
  subst s
  have hce := mul_nonneg hc he
  rcases heta with rfl | rfl <;> nlinarith [sq_nonneg e]

theorem complement_square_cap
    (l u p eta H T : ℤ)
    (_hl : 0 ≤ l) (hu : 0 ≤ u) (hutop : u ≤ 2*l)
    (hp : p ≤ 1) (heta : 0 ≤ eta)
    (hH : 0 ≤ H) (hcomp : l*(u-l) ≤ H)
    (hT : 2*T ≤ u^2+p-2*eta-4*H) :
    2*T ≤ l^2+1 := by
  by_cases hside : u ≤ l
  · have hs := mul_nonneg (show 0 ≤ l-u by omega)
        (show 0 ≤ l+u by omega)
    nlinarith
  · have hs := mul_nonneg (show 0 ≤ u-l by omega)
        (show 0 ≤ 3*l-u by omega)
    nlinarith

theorem nondominant_square_cap
    (s eta p G H squares : ℤ)
    (hs : 0 ≤ s) (heta : eta=0 ∨ eta=1) (hp : p ≤ 1)
    (hG : 4*G=(s+eta)^2-p) (hH : 0 ≤ H)
    (hsquares : 2*squares ≤ s^2) :
    2*(squares-2*G-2*H) ≤ 1 := by
  rcases heta with rfl | rfl <;> nlinarith

theorem all_internal_gaps_paid
    (l delta epsilon K w T : ℤ)
    (hl : 0 ≤ l) (hdelta : l-1 ≤ delta)
    (hepsilon : 0 ≤ epsilon) (hw : 2 ≤ w)
    (henergy : K^2 ≤ T+2*epsilon)
    (hcap : 2*T ≤ l^2+1) :
    K-w ≤ delta+epsilon := by
  by_contra h
  have hK : l+epsilon+2 ≤ K := by omega
  have hp := mul_nonneg (show 0 ≤ K-(l+epsilon+2) by omega)
      (show 0 ≤ K+(l+epsilon+2) by omega)
  have he := mul_nonneg hepsilon
      (show 0 ≤ epsilon+2*l+2 by omega)
  nlinarith [sq_nonneg l]

#print axioms dominant_square_upper
#print axioms complement_square_cap
#print axioms nondominant_square_cap
#print axioms all_internal_gaps_paid

end CayleyPy.ConnectedComplementCap
