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

/-! M4: reject an entire scalar x-interval using a constant-size certificate.
The final density is concave on each side of h, but not globally concave.
Its minimum on an interval is attained at an endpoint or at h.
The verifier checks endpoint guards; no square-root implementation is trusted.
-/
namespace ScalarIntervalCertificate

def squareBound (h x : ℤ) : ℤ := if x ≤ h then x^2 else h^2+(x-h)^2

def density (h offset tail x : ℤ) : ℤ := (x+offset)^2-2*squareBound h x+tail

theorem concave_endpoint (B C lo hi x : ℤ) (hl : lo ≤ x) (hh : x ≤ hi) :
    C+B*lo-lo^2 ≤ C+B*x-x^2 ∨ C+B*hi-hi^2 ≤ C+B*x-x^2 := by
  by_cases hs : x+lo ≤ B
  · left
    have hp := mul_nonneg (show 0 ≤ x-lo by omega) (show 0 ≤ B-x-lo by omega)
    nlinarith
  · right
    have hp := mul_nonneg (show 0 ≤ hi-x by omega) (show 0 ≤ hi+x-B by omega)
    nlinarith

theorem density_left (h offset tail x : ℤ) (hx : x ≤ h) :
    density h offset tail x = offset^2+tail+2*offset*x-x^2 := by
  simp only [density,squareBound,ite_eq_left hx]
  ring

theorem density_right (h offset tail x : ℤ) (hx : h ≤ x) :
    density h offset tail x = offset^2-4*h^2+tail+(2*offset+4*h)*x-x^2 := by
  unfold density squareBound
  split_ifs with hh
  · have : x=h := by omega
    subst x
    ring
  · ring

theorem density_left_endpoint (h offset tail lo hi x : ℤ)
    (hl : lo ≤ x) (hh : x ≤ hi) (hhi : hi ≤ h) :
    density h offset tail lo ≤ density h offset tail x ∨
    density h offset tail hi ≤ density h offset tail x := by
  rw [density_left _ _ _ lo (by omega),density_left _ _ _ hi hhi,
    density_left _ _ _ x (by omega)]
  exact concave_endpoint (2*offset) (offset^2+tail) lo hi x hl hh

theorem density_right_endpoint (h offset tail lo hi x : ℤ)
    (hl : lo ≤ x) (hh : x ≤ hi) (hlo : h ≤ lo) :
    density h offset tail lo ≤ density h offset tail x ∨
    density h offset tail hi ≤ density h offset tail x := by
  rw [density_right _ _ _ lo hlo,density_right _ _ _ hi (by omega),
    density_right _ _ _ x (by omega)]
  exact concave_endpoint (2*offset+4*h) (offset^2-4*h^2+tail) lo hi x hl hh

/-- Three points suffice across both branches; testing just the two endpoints
is in general unsound if the interval straddles h. -/
theorem density_three_points (h offset tail lo hi x : ℤ) (hl : lo ≤ x) (hh : x ≤ hi) :
    density h offset tail lo ≤ density h offset tail x ∨
    density h offset tail hi ≤ density h offset tail x ∨
    (lo ≤ h ∧ h ≤ hi ∧ density h offset tail h ≤ density h offset tail x) := by
  by_cases hleft : hi ≤ h
  · rcases density_left_endpoint h offset tail lo hi x hl hh hleft with ha | hb
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)
  by_cases hright : h ≤ lo
  · rcases density_right_endpoint h offset tail lo hi x hl hh hright with ha | hb
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)
  by_cases hx : x ≤ h
  · rcases density_left_endpoint h offset tail lo h x hl hx le_rfl with ha | hb
    · exact Or.inl ha
    · exact Or.inr (Or.inr ⟨by omega,by omega,hb⟩)
  · rcases density_right_endpoint h offset tail h hi x (by omega) hh le_rfl with ha | hb
    · exact Or.inr (Or.inr ⟨by omega,by omega,ha⟩)
    · exact Or.inr (Or.inl hb)

theorem squareBound_mono (h x y : ℤ) (hh : 0 ≤ h) (hx : 0 ≤ x) (hxy : x ≤ y) :
    squareBound h x ≤ squareBound h y := by
  unfold squareBound
  split_ifs with hxh hyh hyh
  · nlinarith [mul_nonneg (show 0 ≤ y-x by omega) (show 0 ≤ y+x by omega)]
  · have hp := mul_nonneg (show 0 ≤ h-x by omega) (show 0 ≤ h+x by omega)
    nlinarith [sq_nonneg (y-h)]
  · omega
  · have hp := mul_nonneg (show 0 ≤ y-x by omega) (show 0 ≤ y+x-2*h by omega)
    nlinarith

structure Data where
  h : ℤ
  offset : ℤ
  cap : ℤ
  need : ℤ
  credit : ℤ
  areaCeiling : ℤ
  energyCeiling : ℤ
  tail : ℤ
  deriving DecidableEq, Repr

def Data.lower (d : Data) (x : ℤ) : Prop :=
  d.need ≤ x+d.credit ∧ d.need ≤ squareBound d.h x

def Data.upper (d : Data) (x : ℤ) : Prop :=
  (x+d.offset-1)^2 ≤ d.areaCeiling ∧ (x+d.offset)^2 ≤ d.energyCeiling

def Data.feasible (d : Data) (x : ℤ) : Prop :=
  0 ≤ x ∧ x ≤ d.cap ∧ d.lower x ∧ d.upper x ∧ density d.h d.offset d.tail x ≤ 0

instance (d : Data) (x : ℤ) : Decidable (d.lower x) := by unfold Data.lower; infer_instance
instance (d : Data) (x : ℤ) : Decidable (d.upper x) := by unfold Data.upper; infer_instance

theorem lower_mono (d : Data) (hh : 0 ≤ d.h) {x y : ℤ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hp : d.lower x) : d.lower y := by
  exact ⟨by have := hp.1; omega, hp.2.trans (squareBound_mono d.h x y hh hx hxy)⟩

theorem upper_antitone (d : Data) (ho : 1 ≤ d.offset) {x y : ℤ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hp : d.upper y) : d.upper x := by
  obtain ⟨h1,h2⟩ := hp
  constructor
  · have hprod := mul_nonneg (show 0 ≤ y-x by omega)
      (show 0 ≤ y+x+2*d.offset-2 by omega)
    nlinarith
  · have hprod := mul_nonneg (show 0 ≤ y-x by omega)
      (show 0 ≤ y+x+2*d.offset by omega)
    nlinarith

/-- Untrusted generators may propose lo and hi. Local checks at lo-1 and
hi+1 prove coverage. Empty intervals need no density tests. -/
def Certificate (d : Data) (lo hi : ℤ) : Prop :=
  0 ≤ d.h ∧ 1 ≤ d.offset ∧ 0 ≤ lo ∧ -1 ≤ hi ∧
  (lo=0 ∨ ¬d.lower (lo-1)) ∧ (hi=d.cap ∨ ¬d.upper (hi+1)) ∧
  (hi<lo ∨ (0 < density d.h d.offset d.tail lo ∧
    0 < density d.h d.offset d.tail hi ∧
    (lo ≤ d.h ∧ d.h ≤ hi → 0 < density d.h d.offset d.tail d.h)))

instance (d : Data) (lo hi : ℤ) : Decidable (Certificate d lo hi) := by
  unfold Certificate
  infer_instance

def verify (d : Data) (lo hi : ℤ) : Bool := decide (Certificate d lo hi)

theorem certificate_sound (d : Data) (lo hi : ℤ) (hc : Certificate d lo hi) :
    ∀ x, ¬d.feasible x := by
  obtain ⟨hh,ho,hlo,hhi,hfirst,hlast,hreject⟩ := hc
  intro x hx
  obtain ⟨hx0,hxcap,hxl,hxu,hxd⟩ := hx
  have hlx : lo ≤ x := by
    by_contra h
    rcases hfirst with hz | hn
    · omega
    · exact hn (lower_mono d hh hx0 (by omega) hxl)
  have hxh : x ≤ hi := by
    by_contra h
    rcases hlast with he | hn
    · omega
    · exact hn (upper_antitone d ho (by omega) (by omega) hxu)
  rcases hreject with he | ⟨hl,hr,hm⟩
  · omega
  · rcases density_three_points d.h d.offset d.tail lo hi x hlx hxh with h | h | ⟨hlh,hhh,h⟩
    · omega
    · omega
    · have := hm ⟨hlh,hhh⟩
      omega

theorem verify_sound (d : Data) (lo hi : ℤ) (hv : verify d lo hi=true) :
    ∀ x, ¬d.feasible x :=
  certificate_sound d lo hi (of_decide_eq_true hv)

/-- Direct transcription of the actual M4 scalar filters. These are integer
parameters; only x is being eliminated by the interval certificate. -/
def fromScalars (L h v a f parity eps U T mass E : ℤ) : Data where
  h := h
  offset := v+a
  cap := min (L-4) (min (2*T+f-a) (2*h-1))
  need := 2*mass-4*U*(L-U)-E
  credit := 4*T^2+2*T
  areaCeiling := 2*(2*eps+parity-f)-2*v+1-parity+2*(4*T^2+2*T+E)
  energyCeiling := 4*eps+parity+8*T*(T+if a<f then 1 else 0)+2*(E-v%2)
  tail := -2*a+parity-2*E-2*(2*eps+parity-f)

theorem feasible_of_scalar_filters (L h v a f parity eps U T mass E x : ℤ)
    (hx0 : 0 ≤ x) (hxL : x ≤ L-4) (hxT : x ≤ 2*T+f-a) (hxh : x < 2*h)
    (hlinear : 2*mass-4*U*(L-U) ≤ x+4*T^2+2*T+E)
    (hJ : 2*mass-4*U*(L-U) ≤ squareBound h x+E)
    (harea : (x+v+a-1)^2+2*v-1+parity-2*(4*T^2+2*T+E) ≤
      2*(2*eps+parity-f))
    (henergy : (x+v+a)^2 ≤ 4*eps+parity+8*T*(T+if a<f then 1 else 0)+2*(E-v%2))
    (hdensity : (x+v)^2-2*(squareBound h x+E)+2*(x+v-1)*a+a^2+parity ≤
      2*(2*eps+parity-f)) :
    (fromScalars L h v a f parity eps U T mass E).feasible x := by
  unfold Data.feasible Data.lower Data.upper fromScalars
  dsimp only
  refine ⟨hx0,le_min hxL (le_min hxT (by omega)),⟨by omega,by omega⟩,?_,?_⟩
  · constructor
    · have heq : x+(v+a)-1=x+v+a-1 := by ring
      rw [heq]
      omega
    · simpa only [add_assoc] using henergy
  · unfold density
    nlinarith only [hdensity]

#print axioms verify_sound
#print axioms feasible_of_scalar_filters
end ScalarIntervalCertificate
