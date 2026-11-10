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

/-! A computable necessary scalar profile for the remaining M4 peak.
Admissibility is only a necessary condition, not a sharp-routing theorem. -/
namespace LRX.FinitePeak

structure Profile where
  t : ℤ
  m : ℤ
  parity : ℤ
  fixed : ℤ
  eps : ℤ
  isolated : ℤ
  peak : ℤ
  exterior : ℤ
  holes : ℤ
  deriving DecidableEq, Repr

namespace Profile

def n (r : Profile) : ℤ := 2*r.m+r.parity
def L (r : Profile) : ℤ := r.n-r.isolated-r.exterior
def B (r : Profile) : ℤ := if r.isolated=0 then r.t else r.isolated+r.t-1
def M (r : Profile) : ℤ := 2*(r.t-1)*(r.exterior-r.t)+r.isolated*r.exterior+
  (r.isolated.toNat.choose 2 : ℤ)
def T (r : Profile) : ℤ := 2*r.B+r.m-r.peak-3-r.M-r.eps
def A (r : Profile) : ℤ := 2*r.eps+r.parity-r.fixed
def cap (r : Profile) : ℤ := r.m+r.parity-2
def J (r : Profile) : ℤ := if r.holes ≤ r.cap then r.holes^2 else r.cap^2+(r.holes-r.cap)^2
def E2 (r : Profile) : ℤ := (r.exterior-2*r.t+2)^2+4*(r.t-1)
def B0 (r : Profile) : ℤ := 4*r.T^2+2*r.T
def energy (r : Profile) : ℤ := r.m*(r.m+r.parity)-r.eps
def need (r : Profile) : ℤ := 2*r.energy-4*r.peak*(r.L-r.peak)
def correction (r : Profile) : ℤ := if r.isolated<r.fixed then 1 else 0

def Domain (r : Profile) : Prop :=
  2 ≤ r.t ∧ r.t ≤ 7 ∧ 0 ≤ r.parity ∧ r.parity ≤ 1 ∧
  0 ≤ r.fixed ∧ r.fixed ≤ r.t+5 ∧ 0 ≤ r.eps ∧ r.eps ≤ 3*r.t+6 ∧
  0 ≤ r.isolated ∧ r.isolated ≤ r.fixed ∧ 1 ≤ r.peak ∧ r.peak ≤ 3*r.t+1 ∧
  2*r.t+r.isolated+1 ≤ r.m ∧ r.m ≤ 288 ∧
  2*r.t ≤ r.exterior ∧ r.exterior ≤ r.m-r.isolated-1 ∧
  (3 ≤ r.t → r.t^3-3*r.t^2+3*r.t+1 ≤ r.m) ∧
  r.energy % 2=0 ∧ 2*r.peak ≤ r.L ∧ 0 ≤ r.holes ∧ r.holes ≤ r.L-4

def Reserves (r : Profile) : Prop :=
  r.fixed^2 ≤ 4*r.eps+r.parity ∧ 0 ≤ r.A ∧
  1 ≤ 2*r.B+r.t-r.peak-r.A ∧
  2*r.fixed+r.t^2-2*(r.exterior-r.t) ≤ r.eps ∧
  0 ≤ r.T ∧ r.holes ≤ 2*r.T+r.fixed-r.isolated ∧
  0 ≤ r.cap ∧ r.holes < 2*r.cap

def Filters (r : Profile) : Prop :=
  r.need ≤ r.E2+r.J ∧ r.need ≤ r.E2+r.holes+r.B0 ∧
  r.need ≤ r.E2-r.exterior%2+4*r.T*(r.T+r.correction) ∧
  (r.holes+r.exterior+r.isolated-1)^2+2*r.exterior-1+r.parity-2*(r.B0+r.E2) ≤ 2*r.A ∧
  (r.holes+r.exterior+r.isolated)^2 ≤ 4*r.eps+r.parity+
    8*r.T*(r.T+r.correction)+2*(r.E2-r.exterior%2) ∧
  (r.holes+r.exterior)^2-2*(r.J+r.E2)+2*(r.holes+r.exterior-1)*r.isolated+
    r.isolated^2+r.parity ≤ 2*r.A

def Admissible (r : Profile) : Prop := r.Domain ∧ r.Reserves ∧ r.Filters

instance (r : Profile) : Decidable r.Domain := by unfold Domain; infer_instance
instance (r : Profile) : Decidable r.Reserves := by unfold Reserves; infer_instance
instance (r : Profile) : Decidable r.Filters := by unfold Filters; infer_instance
instance (r : Profile) : Decidable r.Admissible := by unfold Admissible; infer_instance

end Profile
end LRX.FinitePeak
