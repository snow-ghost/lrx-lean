import LRX.ShellInternalWindowData

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Deleting the exterior reversal's joined endpoints leaves a smaller
literal reversal. Its physical coordinates and enclosing-root avoidance
are derived from the original exterior window. -/
theorem shell_exterior_inner_window_data (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (hc : 2 ≤ (componentSet p 0).card)
    (Q C : State n) (E : FillingWindow n)
    (hEo : E.window.offset=(componentSet p 0).card)
    (hEs : E.size=n-(componentSet p 0).card)
    (hrev : ∀ i, Q (embed E.window i)=embed E.window (Fin.revPerm i))
    (hCs : C.support=insert (⟨n-1,by have := NeZero.pos n; omega⟩ : Fin n)
      (insert (⟨(componentSet p 0).card,component_card_lt_of_multiple_roots p hm 0⟩ : Fin n)
        (prefixSourceCore p))) :
    let v : Fin n := ⟨(componentSet p 0).card,component_card_lt_of_multiple_roots p hm 0⟩
    ∃ W : Window n (n-(componentSet p 0).card-2),
      W.offset=(componentSet p 0).card+1 ∧
      W.offset+(n-(componentSet p 0).card-2)=n-1 ∧
      (∀ i, (Q*Equiv.swap (componentRight p 0) v) (embed W i)=embed W (Fin.revPerm i)) ∧
      (∀ i ∈ C.support, ¬Contains W i) := by
  classical
  let L := (componentSet p 0).card
  let v : Fin n := ⟨L,component_card_lt_of_multiple_roots p hm 0⟩
  have hout := prefix_multiple_components_exterior_size p hc hm
  have hproper := component_card_lt_of_multiple_roots p hm 0
  obtain ⟨_,_,hwidth⟩ := prefix_component_source_ends p hc hproper
  let W : Window n (n-L-2) := ⟨L+1,by dsimp only [L]; omega⟩
  refine ⟨W,rfl,by dsimp [W,L]; omega,?_,?_⟩
  · intro i
    let j : Fin E.size := ⟨i.val+1,by have := i.isLt; omega⟩
    have hj : embed E.window j=embed W i := by
      apply Fin.ext
      dsimp only [embed,j,W]
      dsimp only [L]
      omega
    have hjrev : embed E.window (Fin.revPerm j)=embed W (Fin.revPerm i) := by
      apply Fin.ext
      simp only [embed,Fin.revPerm_apply,Fin.val_rev]
      dsimp only [j,W,L]
      have := i.isLt
      omega
    have hiu : embed W i ≠ componentRight p 0 := by
      intro he
      have he' := congrArg Fin.val he
      dsimp only [embed,W,L] at he'
      omega
    have hiv : embed W i ≠ v := by
      intro he
      have he' := congrArg Fin.val he
      dsimp only [embed,W,v] at he'
      omega
    change (Q*Equiv.swap (componentRight p 0) v) (embed W i)=_
    rw [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hiu hiv,← hj,hrev,hjrev]
  · intro i hi hinside
    have hlo : L+1 ≤ i.val := hinside.1
    have hhi : i.val < L+1+(n-L-2) := hinside.2
    rw [hCs] at hi
    simp only [Finset.mem_insert] at hi
    rcases hi with rfl | rfl | hi
    · dsimp only [L] at *; omega
    · dsimp only [L] at *; omega
    · have hh := (Finset.mem_filter.mp hi).2
      dsimp only [L] at *
      omega

#print axioms shell_exterior_inner_window_data

def ExteriorShellGapWords (p Q C : State n) (hm : 2 ≤ (componentRoots p).card)
    (start finish : Fin n) : Prop :=
  let L := (componentSet p 0).card
  let v : Fin n := ⟨L,component_card_lt_of_multiple_roots p hm 0⟩
  L ≤ min start.val finish.val → max start.val finish.val < n-1 →
    ∃ w : List Letter,
      eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+
        (∑ i, |displacement (Q*Equiv.swap (componentRight p 0) v) i|)-1

theorem shell_exterior_gap_words (hn : 2 ≤ n) (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (hc : 2 ≤ (componentSet p 0).card)
    (Q C : State n) (E : FillingWindow n)
    (hEo : E.window.offset=(componentSet p 0).card)
    (hEs : E.size=n-(componentSet p 0).card)
    (hrev : ∀ i, Q (embed E.window i)=embed E.window (Fin.revPerm i))
    (hCs : C.support=insert (⟨n-1,by have := NeZero.pos n; omega⟩ : Fin n)
      (insert (⟨(componentSet p 0).card,component_card_lt_of_multiple_roots p hm 0⟩ : Fin n)
        (prefixSourceCore p)))
    (hbelow : FiniteRankOrder.Below p.symm
      (Q*Equiv.swap (componentRight p 0) ⟨(componentSet p 0).card,component_card_lt_of_multiple_roots p hm 0⟩))
    (hC : C ∈ (Q*Equiv.swap (componentRight p 0)
      ⟨(componentSet p 0).card,component_card_lt_of_multiple_roots p hm 0⟩).cycleFactorsFinset)
    (start finish : Fin n) : ExteriorShellGapWords p Q C hm start finish := by
  classical
  let v : Fin n := ⟨(componentSet p 0).card,component_card_lt_of_multiple_roots p hm 0⟩
  let z : Fin n := ⟨n-1,by omega⟩
  have hproper := component_card_lt_of_multiple_roots p hm 0
  obtain ⟨hzero,_,_⟩ := prefix_component_source_ends p hc hproper
  have h0 : (0 : Fin n) ∈ C.support := by
    rw [hCs]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_filter.mpr ⟨hzero,by change 0 < (componentSet p 0).card; omega⟩))
  have hv : v ∈ C.support := by rw [hCs]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hz : z ∈ C.support := by rw [hCs]; exact Finset.mem_insert_self _ _
  obtain ⟨W,hWo,hWe,hmatch,havoid⟩ := shell_exterior_inner_window_data p hm hc Q C E hEo hEs hrev hCs
  intro hlo hhi
  exact enclosing_reversed_gap_discount_word hn p _ C hbelow hC h0 hz W hmatch havoid
    v z hv hz hWo hWe start finish hlo hhi

#print axioms shell_exterior_gap_words
end LRX.FiniteCuts
