import LRX.ShellReservePayment

namespace LRX.FiniteCuts
open ContractionBlocks.System
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- All geometric inputs of the shortened exterior calculation are derived
from the actual prefix. The remaining input is the prospective shell price. -/
theorem prefix_even_exterior_shell_paid_or_small (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0)
    (heven : (prefixSourceCore p).card%2=0) (hU : sourceHalfPeak p=2)
    (hdom : (componentSet p 0).card-(prefixSourceCore p).card < n-(componentSet p 0).card)
    (E variance : ℤ) (hv : 0 ≤ variance)
    (hprice : let L := (componentSet p 0).card
      let R := (prefixSourceCore p).card
      let l := R/2
      let H := (l : ℤ)*((n : ℤ)-l)-(∑ i ∈ prefixSourceCore p, |displacement p.symm i|)
      let t := (n : ℤ)-2*(L : ℤ)+(R : ℤ)
      E ≤ 1-2*(H-t^2/4)-variance)
    : E ≤ 0 ∨ n=8 ∨ n=9 := by
  classical
  by_cases hpaid : E ≤ 0
  · exact Or.inl hpaid
  let L := (componentSet p 0).card
  let R := (prefixSourceCore p).card
  let l : ℤ := (R/2 : ℕ)
  let c : ℤ := (L : ℤ)-R
  let e : ℤ := (n : ℤ)-L
  let t : ℤ := e-c
  let H : ℤ := l*((n : ℤ)-l)-(∑ i ∈ prefixSourceCore p, |displacement p.symm i|)
  have hRL : R ≤ L := by
    apply Finset.card_le_card
    intro i hi
    exact (zero_component_prefix p i).mpr (Finset.mem_filter.mp hi).2
  have hLn : L ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ (componentSet p 0)
  have hR : (R : ℤ)=2*l := by dsimp only [R,l]; omega
  have hL : (L : ℤ)=2*l+c := by dsimp only [c]; omega
  have hN : (n : ℤ)=2*l+2*c+t := by dsimp only [c,e,t]; omega
  have hc : 0 ≤ c := by dsimp only [c]; omega
  have ht : 1 ≤ t := by dsimp only [t,e,c,R,L]; omega
  have htop : t ≤ 2*l-2 := by dsimp only [t,e,c,L] at *; omega
  have hsize : 2 ≤ (componentSet p 0).card := by omega
  have he2 := prefix_multiple_components_exterior_size p hsize hm
  have he : 2 ≤ c+t := by dsimp only [c,t,e,L] at *; omega
  have hlin := prefix_even_zero_defect_linear_reserve p hmaj hm hlarge hz heven
  have hlinear : c+t-1 ≤ H := by
    change ((n-L : ℕ) : ℤ)-1 ≤ H at hlin
    dsimp only [t,e]
    omega
  have hquad := prefix_zero_defect_exterior_deficit p hmaj hm hlarge hz
  have hquadratic : t^2/4 ≤ H := by
    change (max 0 ((n : ℤ)-2*(L : ℤ)+2*l))^2/4 ≤ H at hquad
    have ht' : (n : ℤ)-2*(L : ℤ)+2*l=t := by dsimp only [t,e,c]; omega
    rw [ht',max_eq_right (by omega)] at hquad
    exact hquad
  have henergy := prefix_core_energy_bound p (by rw [hU]; omega)
  rw [hU] at henergy
  have harea : l*(l+2*c+t)-4*(2*l+c-2) ≤ H := by
    change (∑ i ∈ prefixSourceCore p, |displacement p.symm i|) ≤ 2*(2 : ℕ)*((L : ℤ)-(2 : ℕ)) at henergy
    dsimp only [H]
    push_cast at henergy
    rw [hL] at henergy
    rw [hN]
    nlinarith
  have hmassEven : (∑ i ∈ prefixSourceCore p, |displacement p.symm i|)%2=0 := by
    obtain ⟨r,P,emb,_,_,_,_,_,_,_,_,_,hmass,_⟩ :=
      prefix_zero_defect_physical_model p hmaj hm hlarge hz
    rw [← hmass]
    exact physical_mass_mod_two P _
  have hparity : (l*(l+2*c+t)-H)%2=0 := by
    have heq : l*(l+2*c+t)-H=∑ i ∈ prefixSourceCore p, |displacement p.symm i| := by
      dsimp only [H]
      rw [hN]
      ring
    rwa [heq]
  have hprice' : E ≤ 1-2*(H-t^2/4)-variance := by
    change E ≤ 1-2*(H-((n : ℤ)-2*(L : ℤ)+(R : ℤ))^2/4)-variance at hprice
    have heq : (n : ℤ)-2*(L : ℤ)+(R : ℤ)=t := by dsimp only [t,e,c]; omega
    rwa [heq] at hprice
  have hcases := ShellReservePayment.even_exterior_unpaid_cases l c t H E variance hc ht htop he
    hlinear hquadratic harea hparity hv hprice' (by omega)
  rcases hcases with hh | hh
  · right; left; dsimp only [l,c,t,e,L,R] at *; omega
  · right; right; dsimp only [l,c,t,e,L,R] at *; omega


#print axioms prefix_even_exterior_shell_paid_or_small
end LRX.FiniteCuts
