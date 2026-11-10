module

public import LRX.ZeroEnergyUnitCapacity
public import LRX.ExteriorUnitPairRigidity

@[expose] public section

namespace LRX.FiniteWindow
open scoped BigOperators
open FiniteCuts
variable {n : ℕ} [NeZero n]

theorem unit_window_arrow_positions (A : FillingWindow n) (p : State n)
    (hm : A.Matches p) (hu : (⟨A.size,A.filling⟩ : SmallExteriorMap)=unitExteriorMap) :
    ∃ a b : Fin n, Contains A.window a ∧ Contains A.window b ∧
      displacement p a=1 ∧ displacement p b= -1 := by
  rcases A with ⟨b,W,σ⟩
  change (⟨b,σ⟩ : SmallExteriorMap)=⟨2,Equiv.swap (0 : Fin 2) 1⟩ at hu
  cases hu
  refine ⟨embed W 0,embed W 1,contains_embed W 0,contains_embed W 1,?_,?_⟩
  · rw [matching_window_displacement W p _ hm]
    norm_num [displacement]
  · rw [matching_window_displacement W p _ hm]
    norm_num [displacement]

theorem two_unit_windows_no_unit_outside (A B : FillingWindow n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (he : canonicalEnergyDeficit p=0) (hp : n%2=0)
    (ha : A.Matches p.symm) (hb : B.Matches p.symm) (hab : A.Apart B)
    (hA : (⟨A.size,A.filling⟩ : SmallExteriorMap)=unitExteriorMap)
    (hB : (⟨B.size,B.filling⟩ : SmallExteriorMap)=unitExteriorMap)
    (i : Fin n) (hia : ¬Contains A.window i) (hib : ¬Contains B.window i) :
    |displacement p.symm i| ≠ 1 := by
  obtain ⟨ap,am,hap,ham,hapd,hamd⟩ := unit_window_arrow_positions A p.symm ha hA
  obtain ⟨bp,bm,hbp,hbm,hbpd,hbmd⟩ := unit_window_arrow_positions B p.symm hb hB
  have hpne : ap ≠ bp := by intro h; apply hab ap hap; rwa [h]
  have hmne : am ≠ bm := by intro h; apply hab am ham; rwa [h]
  intro hi
  have hsign : displacement p.symm i=1 ∨ displacement p.symm i= -1 := by
    by_cases h : 0 ≤ displacement p.symm i
    · left; rwa [abs_of_nonneg h] at hi
    · right; rw [abs_of_neg (by omega)] at hi; omega
  rcases hsign with hi | hi
  · rcases zero_energy_unit_pair_exhausts p hmaj he hp ap bp hpne 1 (Or.inl rfl) hapd hbpd i hi with h | h
    · subst i; exact hia hap
    · subst i; exact hib hbp
  · rcases zero_energy_unit_pair_exhausts p hmaj he hp am bm hmne (-1) (Or.inr rfl) hamd hbmd i hi with h | h
    · subst i; exact hia ham
    · subst i; exact hib hbm

#print axioms unit_window_arrow_positions
#print axioms two_unit_windows_no_unit_outside
end LRX.FiniteWindow
