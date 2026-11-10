module

public import LRX.EnclosingWindowRightRoute
public import LRX.CanonicalWindowBoundaryLoad
public import LRX.ReversalCombinedPrice
public import LRX.EnclosingCycleLoads

@[expose] public section

namespace LRX.FiniteWindow
open scoped BigOperators Fin.CommRing
open FiniteCuts RotationWords
variable {n b : ℕ} [NeZero n]

/-- Both boundary routes are compiled for the original lower map. Their
minimum is paid by the finite window profile, without majorizing the upper
map and without a supplied service or word certificate. -/
theorem enclosing_gap_word (hn : 2 ≤ n) (p G C : State n)
    (hbelow : FiniteRankOrder.Below p.symm G)
    (hC : C ∈ G.cycleFactorsFinset)
    (hzero : (0 : Fin n) ∈ C.support)
    (hlast : (⟨n-1,by have := NeZero.pos n; omega⟩ : Fin n) ∈ C.support)
    (W : Window n b) (f : State b)
    (hmatch : ∀ i, G (embed W i)=embed W (f i))
    (havoid : ∀ i ∈ C.support, ¬Contains W i)
    (u v : Fin n) (hu : u ∈ C.support) (hv : v ∈ C.support)
    (hoff : W.offset=u.val+1) (hedge : W.offset+b=v.val)
    (start finish : Fin n) (hlower : u.val ≤ min start.val finish.val)
    (hupper : max start.val finish.val < v.val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement G i|)-
        (∑ i, |displacement f i|)+(b*b/2 : ℕ)+(b%2 : ℕ)-
        portLoad (displacement C) u := by
  have hv0 : v ≠ 0 := by intro h; have := congrArg Fin.val h; simp only [Fin.val_zero] at this; omega
  have hvval : (v-1 : Fin n).val=v.val-1 := Fin.val_sub_one_of_ne_zero hv0
  let x := min start.val finish.val-u.val
  let y := max start.val finish.val-u.val
  have hx : x ≤ b := by dsimp [x]; omega
  have hy : y ≤ b := by dsimp [y]; omega
  have hxy' : x ≤ y := by dsimp [x,y]; omega
  have hsumcast : (x : ℤ)+(y : ℤ)=(start.val : ℤ)+(finish.val : ℤ)-2*(u.val : ℤ) := by
    dsimp [x,y]
    omega
  have hfix (i : Fin b) : C (embed W i)=embed W i := by
    apply Equiv.Perm.notMem_support.mp
    intro hi
    exact havoid _ hi (contains_embed W i)
  have hload : portLoad (displacement C) u=portLoad (displacement C) (v-1) := by
    simpa only [Equiv.symm_symm,Equiv.Perm.one_apply] using
      canonical_window_boundary_load C.symm W (1 : State b)
        (by intro i; simpa only [Equiv.symm_symm,Equiv.Perm.one_apply] using hfix i)
        u v hoff hedge
  obtain ⟨wl,hewl,hl⟩ := enclosing_window_left_route hn p G C hbelow hC hzero hlast
    W f hmatch havoid u hu hoff start finish (by omega) (by omega) y hy (by dsimp [y]; omega)
  obtain ⟨wr,hewr,hr⟩ := enclosing_window_right_route hn p G C hbelow hC hzero hlast
    W f hmatch havoid v hv hv0 hedge start finish (by omega) (by omega) x hx (by dsimp [x]; omega)
  rw [← hload] at hr
  have hnum := finite_cycle_charge_bound f x y hxy' hy
  change (∑ i, |displacement f i|)+
    min ((x : ℤ)+y-cycleLeftLoad f y) (2*(b : ℤ)-x-y-cycleRightLoad f x) ≤ _ at hnum
  have hwidth : ((v-1 : Fin n).val : ℤ)=(u.val : ℤ)+(b : ℤ) := by omega
  by_cases hc : (x : ℤ)+y-cycleLeftLoad f y ≤ 2*(b : ℤ)-x-y-cycleRightLoad f x
  · rw [min_eq_left hc] at hnum
    exact ⟨wl,hewl,by linarith⟩
  · rw [min_eq_right (by omega)] at hnum
    exact ⟨wr,hewr,by linarith⟩

#print axioms enclosing_gap_word

/-- In a reversed gap the quadratic window mass cancels exactly, leaving
only its parity and the genuine root-boundary discount. -/
theorem enclosing_reversed_gap_word (hn : 2 ≤ n) (p G C : State n)
    (hbelow : FiniteRankOrder.Below p.symm G)
    (hC : C ∈ G.cycleFactorsFinset)
    (hzero : (0 : Fin n) ∈ C.support)
    (hlast : (⟨n-1,by have := NeZero.pos n; omega⟩ : Fin n) ∈ C.support)
    (W : Window n b)
    (hmatch : ∀ i, G (embed W i)=embed W (Fin.revPerm i))
    (havoid : ∀ i ∈ C.support, ¬Contains W i)
    (u v : Fin n) (hu : u ∈ C.support) (hv : v ∈ C.support)
    (hoff : W.offset=u.val+1) (hedge : W.offset+b=v.val)
    (start finish : Fin n) (hlower : u.val ≤ min start.val finish.val)
    (hupper : max start.val finish.val < v.val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement G i|)+
        (b%2 : ℕ)-portLoad (displacement C) u := by
  obtain ⟨w,hw,hl⟩ := enclosing_gap_word hn p G C hbelow hC hzero hlast W Fin.revPerm
    hmatch havoid u v hu hv hoff hedge start finish hlower hupper
  rw [reversal_mass_half_square] at hl
  exact ⟨w,hw,by linarith⟩

#print axioms enclosing_reversed_gap_word

theorem enclosing_reversed_gap_discount_word (hn : 2 ≤ n) (p G C : State n)
    (hbelow : FiniteRankOrder.Below p.symm G)
    (hC : C ∈ G.cycleFactorsFinset)
    (hzero : (0 : Fin n) ∈ C.support)
    (hlast : (⟨n-1,by have := NeZero.pos n; omega⟩ : Fin n) ∈ C.support)
    (W : Window n b)
    (hmatch : ∀ i, G (embed W i)=embed W (Fin.revPerm i))
    (havoid : ∀ i ∈ C.support, ¬Contains W i)
    (u v : Fin n) (hu : u ∈ C.support) (hv : v ∈ C.support)
    (hoff : W.offset=u.val+1) (hedge : W.offset+b=v.val)
    (start finish : Fin n) (hlower : u.val ≤ min start.val finish.val)
    (hupper : max start.val finish.val < v.val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement G i|)-1 := by
  obtain ⟨w,hw,hl⟩ := enclosing_reversed_gap_word hn p G C hbelow hC hzero hlast
    W hmatch havoid u v hu hv hoff hedge start finish hlower hupper
  have hload := enclosing_cycle_port_load_ge_two C
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hC).1 hzero hlast u
    (by have := v.isLt; omega)
  have hpar : b%2 ≤ 1 := by omega
  exact ⟨w,hw,by omega⟩

#print axioms enclosing_reversed_gap_discount_word
end LRX.FiniteWindow
