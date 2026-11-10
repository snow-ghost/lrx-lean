module

public import LRX.CycleLeafInsertion
public import LRX.PrefixRootPacketSupport

@[expose] public section

namespace LRX.ZeroGap
variable {n : ℕ}

theorem cycle_right_leaf_insertion (p : State n) (hp : p.IsCycle) (a b : Fin n)
    (ha : a ∉ p.support) (hb : b ∈ p.support) :
    (p*Equiv.swap a b).IsCycle ∧ (p*Equiv.swap a b).support=insert a p.support := by
  classical
  have hh := cycle_leaf_insertion p⁻¹ hp.inv a b
    (by simpa only [Equiv.Perm.support_inv] using ha)
    (by simpa only [Equiv.Perm.support_inv] using hb)
  constructor
  · simpa using hh.1.inv
  · have he : (p*Equiv.swap a b)⁻¹=Equiv.swap a b*p⁻¹ := by simp
    calc
      _ = ((p*Equiv.swap a b)⁻¹).support := (Equiv.Perm.support_inv _).symm
      _ = _ := by rw [he,hh.2,Equiv.Perm.support_inv]

/-- An exterior transposition joins a real cyclic packet through a boundary
exchange, producing one cycle on the exact enlarged support. -/
theorem cycle_external_pair_join (p : State n) (hp : p.IsCycle) (u v z : Fin n)
    (hu : u ∈ p.support) (hv : v ∉ p.support) (hz : z ∉ p.support) (hvz : v ≠ z) :
    (p*Equiv.swap v z*Equiv.swap u v).IsCycle ∧
      (p*Equiv.swap v z*Equiv.swap u v).support=insert z (insert v p.support) := by
  classical
  obtain ⟨hc,hs⟩ := cycle_right_leaf_insertion p hp v u hv hu
  have hz' : z ∉ (p*Equiv.swap v u).support := by rw [hs]; simp [hz,Ne.symm hvz]
  have hv' : v ∈ (p*Equiv.swap v u).support := by rw [hs]; simp
  have hh := cycle_leaf_insertion (p*Equiv.swap v u) hc z v hz' hv'
  have hd : p.Disjoint (Equiv.swap v z) := by
    intro i
    by_cases hi : i=v
    · subst i; exact Or.inl (Equiv.Perm.notMem_support.mp hv)
    · by_cases hj : i=z
      · subst i; exact Or.inl (Equiv.Perm.notMem_support.mp hz)
      · exact Or.inr (Equiv.swap_apply_of_ne_of_ne hi hj)
  have he : Equiv.swap z v*(p*Equiv.swap v u)=p*Equiv.swap v z*Equiv.swap u v := by
    rw [Equiv.swap_comm z v,← mul_assoc,hd.commute.eq.symm,Equiv.swap_comm v u]
  rw [he,hs] at hh
  exact hh

/-- A larger upper map with the same root arrows and exterior pair agrees
with the joined cycle on its entire support. -/
theorem external_pair_join_agrees (p Q : State n) (u v z : Fin n)
    (hu : u ∈ p.support) (hv : v ∉ p.support) (hz : z ∉ p.support) (hvz : v ≠ z)
    (hQ : ∀ i ∈ p.support, Q i=p i) (hQv : Q v=z) (hQz : Q z=v) :
    ∀ i ∈ insert z (insert v p.support),
      (Q*Equiv.swap u v) i=(p*Equiv.swap v z*Equiv.swap u v) i := by
  classical
  have hvfix := Equiv.Perm.notMem_support.mp hv
  have hzfix := Equiv.Perm.notMem_support.mp hz
  have hpoint (j : Fin n) (hj : j ∈ insert z (insert v p.support)) :
      Q j=(p*Equiv.swap v z) j := by
    simp only [Finset.mem_insert] at hj
    rcases hj with rfl | rfl | hj
    · simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_right,hvfix] using hQz
    · simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_left,hzfix] using hQv
    · have hjv : j ≠ v := fun hh => hv (hh ▸ hj)
      have hjz : j ≠ z := fun hh => hz (hh ▸ hj)
      simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hjv hjz] using hQ j hj
  intro i hi
  have hmem : Equiv.swap u v i ∈ insert z (insert v p.support) := by
    by_cases hiu : i=u
    · subst i; simp
    · by_cases hiv : i=v
      · subst i; simpa only [Equiv.swap_apply_right,Finset.mem_insert] using (Or.inr (Or.inr hu))
      · simpa only [Equiv.swap_apply_of_ne_of_ne hiu hiv] using hi
  exact hpoint _ hmem

#print axioms cycle_right_leaf_insertion
#print axioms cycle_external_pair_join
#print axioms external_pair_join_agrees
end LRX.ZeroGap
