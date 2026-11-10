import LRX.OddWidthFiveCatalogue
import LRX.OddZeroSmallArrows
import LRX.ExternalUnitPairsNoUnit

namespace LRX.FiniteWindow
open FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The span-two transposition has two double arrows and its fixed centre. -/
theorem span_two_window_positions (A : FillingWindow n) (p : State n)
    (hm : A.Matches p) (hu : (⟨A.size,A.filling⟩ : SmallExteriorMap)=spanTwoExteriorMap) :
    ∃ a b c : Fin n, Contains A.window a ∧ Contains A.window b ∧ Contains A.window c ∧
      displacement p a=2 ∧ displacement p b= -2 ∧ p c=c := by
  rcases A with ⟨b,W,σ⟩
  change (⟨b,σ⟩ : SmallExteriorMap)=⟨3,Equiv.swap (0 : Fin 3) 2⟩ at hu
  cases hu
  refine ⟨embed W 0,embed W 2,embed W 1,contains_embed W 0,contains_embed W 2,
    contains_embed W 1,?_,?_,?_⟩
  · rw [matching_window_displacement W p _ hm]
    norm_num [displacement]
  · rw [matching_window_displacement W p _ hm]
    norm_num [displacement]
  · have h := hm (1 : Fin 3)
    have hs : Equiv.swap (0 : Fin 3) 2 1=1 := by decide
    exact h.trans (congrArg (embed W) hs)

/-- The original fixed count excludes all further fixed positions. -/
theorem one_fixed_position_unique (p : State n) (hf : n-p.support.card=1)
    (c i : Fin n) (hc : p.symm c=c) (hi : p.symm i=i) : i=c := by
  classical
  let F := Finset.univ \ p.support
  have hcard : F.card ≤ 1 := by
    dsimp only [F]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simpa using (le_of_eq hf)
  have hcF : c ∈ F := by
    apply Finset.mem_sdiff.mpr
    exact ⟨Finset.mem_univ _,fun h => (mem_support_inverse p c).mp h hc⟩
  have hiF : i ∈ F := by
    apply Finset.mem_sdiff.mpr
    exact ⟨Finset.mem_univ _,fun h => (mem_support_inverse p i).mp h hi⟩
  exact Finset.card_le_one.mp hcard i hiF c hcF

/-- Outside these genuine windows every arrow has length at least three. -/
theorem odd_unit_span_windows_min_arrow (A B : FillingWindow n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (he : canonicalEnergyDeficit p=0) (hp : n%2=1) (hf : n-p.support.card=1)
    (ha : A.Matches p.symm) (hb : B.Matches p.symm)
    (hA : (⟨A.size,A.filling⟩ : SmallExteriorMap)=unitExteriorMap)
    (hB : (⟨B.size,B.filling⟩ : SmallExteriorMap)=spanTwoExteriorMap)
    (i : Fin n) (hia : ¬Contains A.window i) (hib : ¬Contains B.window i) :
    3 ≤ |displacement p.symm i| := by
  obtain ⟨ap,am,hap,ham,hapd,hamd⟩ := unit_window_arrow_positions A p.symm ha hA
  obtain ⟨bp,bm,c,hbp,hbm,hc,hbpd,hbmd,hcf⟩ := span_two_window_positions B p.symm hb hB
  have hzero : displacement p.symm i ≠ 0 := by
    intro hz
    have hif : p.symm i=i := by apply Fin.ext; unfold displacement at hz; omega
    have hh := one_fixed_position_unique p hf c i hcf hif
    subst i
    exact hib hc
  have hone : |displacement p.symm i| ≠ 1 := by
    intro hu
    by_cases hs : 0 ≤ displacement p.symm i
    · rw [abs_of_nonneg hs] at hu
      have hh := odd_zero_unit_unique p hmaj he hp hf ap i 1 (Or.inl rfl) hapd hu
      subst i
      exact hia hap
    · rw [abs_of_neg (by omega)] at hu
      have hh := odd_zero_unit_unique p hmaj he hp hf am i (-1) (Or.inr rfl) hamd (by omega)
      subst i
      exact hia ham
  have htwo : |displacement p.symm i| ≠ 2 := by
    intro hu
    by_cases hs : 0 ≤ displacement p.symm i
    · rw [abs_of_nonneg hs] at hu
      have hh := odd_zero_double_unique p hmaj he hp hf ap bp i 1 (Or.inl rfl)
        hapd (by simpa using hbpd) (by simpa using hu)
      subst i
      exact hib hbp
    · rw [abs_of_neg (by omega)] at hu
      have hh := odd_zero_double_unique p hmaj he hp hf am bm i (-1) (Or.inr rfl)
        hamd (by simpa using hbmd) (by omega)
      subst i
      exact hib hbm
  have hnon := abs_nonneg (displacement p.symm i)
  have hz := abs_ne_zero.mpr hzero
  omega

#print axioms span_two_window_positions
#print axioms one_fixed_position_unique
#print axioms odd_unit_span_windows_min_arrow
end LRX.FiniteWindow
