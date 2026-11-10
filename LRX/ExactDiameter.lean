import LRX.ListBridge
import LRX.Small
import LRX.Graph
import GraphLower
import LRX.Cycle11WordSymmetry
import LRX.LowerBoundNativeComplete
import LRX.ReducedPrice

namespace LRX

private theorem hom_edist_le {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (a b : V) : H.edist (f a) (f b) ≤ G.edist a b := by
  change _ ≤ ⨅ p : G.Walk a b, (p.length : ℕ∞)
  apply le_iInf
  intro p
  simpa only [SimpleGraph.Walk.length_map] using (p.map f).edist_le

private theorem iso_edist_eq {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (a b : V) : H.edist (f a) (f b) = G.edist a b := by
  apply le_antisymm (hom_edist_le f.toHom a b)
  simpa using hom_edist_le f.symm.toHom (f a) (f b)

private theorem iso_ediam_eq {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) : H.ediam = G.ediam := by
  apply le_antisymm
  · apply SimpleGraph.ediam_le_of_edist_le
    intro a b
    obtain ⟨a, rfl⟩ := f.surjective a
    obtain ⟨b, rfl⟩ := f.surjective b
    rw [iso_edist_eq]
    exact SimpleGraph.edist_le_ediam
  · apply SimpleGraph.ediam_le_of_edist_le
    intro a b
    rw [← iso_edist_eq f]
    exact SimpleGraph.edist_le_ediam

theorem list_ediam_eq (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    (GraphBridge.graph n).ediam = (graph n).ediam :=
  iso_ediam_eq (ListBridge.graphIso n hn)

theorem list_diam_eq (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    (GraphBridge.graph n).diam = (graph n).diam :=
  congrArg ENat.toNat (list_ediam_eq n hn)

/-- The archived all-size lower bound, now on our permutation Cayley graph. -/
theorem diam_lower (n : ℕ) [NeZero n] (hn : 4 ≤ n) :
    n * (n - 1) / 2 ≤ (graph n).diam := by
  rw [← list_diam_eq n (by omega)]
  exact GraphBridge.diam_lower hn

/-- Equality from the universal upper bound. The premise is discharged by
`LRX.sharp_diameter_all` in `LRX.exact_diameter_all`. -/
theorem exact_diameter_of_upper (hupper : SharpDiameterTheorem)
    (n : ℕ) [NeZero n] (hn : 4 ≤ n) : (graph n).diam = n * (n - 1) / 2 := by
  apply le_antisymm _ (diam_lower n hn)
  have h := ENat.toNat_le_of_le_natCast (hupper n hn)
  simpa only [SimpleGraph.diam, Nat.choose_two_right] using h

#print axioms diam_lower
#print axioms exact_diameter_of_upper
end LRX
