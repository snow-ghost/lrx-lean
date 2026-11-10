import LRX.ShallowShellWindowFamily
import LRX.AdjacentBoundaryPrice

namespace LRX.FiniteCuts
open FiniteWindow FiniteRankOrder
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The actual external reversal pair can be joined at the adjacent packet
boundary by a rank-raising exchange. This supplies the precise upper target;
the special route and its price are separate obligations. -/
theorem exists_shell_boundary_upper_data (p : State n)
    (hc : 2 ≤ (componentSet p 0).card) (hout : 2 ≤ n-(componentSet p 0).card) :
    let L := (componentSet p 0).card
    let u := componentRight p 0
    let v : Fin n := ⟨L,by have hs := Finset.card_le_univ (componentSet p 0); simp only [Fintype.card_fin] at hs; omega⟩
    let z : Fin n := ⟨n-1,by have := NeZero.pos n; omega⟩
    ∃ (A : FillingWindow n) (Q : State n),
      A.window.offset=L ∧ A.size=n-L ∧
      (∀ B ∈ positiveSourceFamily p L++[A], ∀ i,
        Q (embed B.window i)=embed B.window (Fin.revPerm i)) ∧
      (positiveSourceFamily p L++[A]).Pairwise FillingWindow.Apart ∧
      familyPositions (positiveSourceFamily p L++[A])=(prefixSourceCore p)ᶜ ∧
      Below p.symm Q ∧
      (∀ i ∈ prefixSourceCore p, Q i=p.symm i) ∧ Q v=z ∧ Q z=v ∧
      Below p.symm (Q*Equiv.swap u v) ∧
      (Q*Equiv.swap u v) u=z ∧ (Q*Equiv.swap u v) v=p.symm u ∧
      inversionNumber (Q*Equiv.swap u v)=inversionNumber Q+1 ∧
      (∑ i, |displacement (Q*Equiv.swap u v) i|)=(∑ i, |displacement Q i|)+2 := by
  classical
  have hs : (componentSet p 0).card ≤ n := by simpa using Finset.card_le_univ (componentSet p 0)
  have hproper : (componentSet p 0).card < n := by omega
  let L := (componentSet p 0).card
  let u := componentRight p 0
  let v : Fin n := ⟨L,hproper⟩
  let z : Fin n := ⟨n-1,by have := NeZero.pos n; omega⟩
  obtain ⟨A,Q,hAo,hAs,hbelow,hkeep,hrev,hapart,hcover⟩ := exists_shell_upper_map p hc hproper
  have hA : A ∈ positiveSourceFamily p L++[A] := List.mem_append_right _ (by simp)
  have ha2 : 2 ≤ A.size := by omega
  let i0 : Fin A.size := ⟨0,by omega⟩
  have he0 : embed A.window i0=v := by
    apply Fin.ext
    dsimp only [embed,i0,v,L]
    omega
  have hez : embed A.window (Fin.revPerm i0)=z := by
    apply Fin.ext
    simp only [embed,Fin.revPerm_apply,Fin.val_rev]
    dsimp only [i0,z]
    omega
  have hQv : Q v=z := by
    have hh := hrev A hA i0
    rwa [he0,hez] at hh
  have hQz : Q z=v := by
    have hh := hrev A hA (Fin.revPerm i0)
    have hinv : Fin.revPerm (Fin.revPerm i0)=i0 := by simp
    rwa [hinv,he0,hez] at hh
  obtain ⟨_,hu,hwidth⟩ := prefix_component_source_ends p hc hproper
  have huCore : u ∈ prefixSourceCore p := Finset.mem_filter.mpr ⟨hu,by dsimp only [u]; omega⟩
  have hback := prefix_source_core_invariant p (p.symm u)
  simp only [Equiv.apply_symm_apply] at hback
  have hinvCore := hback.mp huCore
  have hvalue : (Q u).val < L := by
    rw [hkeep u huCore]
    exact (Finset.mem_filter.mp hinvCore).2
  have huv : u.val < v.val := by dsimp only [u,v,L]; omega
  have hraise : Below Q (Q*Equiv.swap u v) := below_raising_swap Q u v huv (by
    rw [hQv]
    dsimp only [z,L] at *
    omega)
  refine ⟨A,Q,hAo,hAs,hrev,hapart,hcover,hbelow,hkeep,hQv,hQz,below_trans hbelow hraise,?_,?_,?_,?_⟩
  · simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_left] using hQv
  · simp only [Equiv.Perm.mul_apply,Equiv.swap_apply_right]
    exact hkeep u huCore
  · apply adjacent_raising_inversion_price Q u v (by dsimp only [u,v,L]; omega)
    rw [hQv]
    dsimp only [z,L] at *
    omega
  · apply adjacent_boundary_mass_price Q u v (by dsimp only [u,v,L]; omega)
    · dsimp only [u,L] at *
      omega
    · rw [hQv]
      dsimp only [z,v,L]
      omega

#print axioms exists_shell_boundary_upper_data
end LRX.FiniteCuts
