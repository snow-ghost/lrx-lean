module

public import LRX.ShallowShellBoundaryJoin
public import LRX.EnclosingGapWord

@[expose] public section

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem positive_source_window_ends (p : State n) (L : ℕ)
    (B : FillingWindow n) (hB : B ∈ positiveSourceFamily p L) :
    ∃ a b : Fin n, a ∈ sourcePackets p ∧ b ∈ sourcePackets p ∧
      a.val+1=B.window.offset ∧ B.window.offset+B.size=b.val ∧ b.val ≤ L := by
  classical
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hB
  have hu := (mem_positive_source_gap_starts p L u.val).mp u.property
  obtain ⟨v,hv,hvval⟩ := FiniteGaps.next_is_member (sourcePackets p) u.val hu.2.1
  have hnext := FiniteGaps.lt_next (sourcePackets p) u.val
  refine ⟨u.val,v,hu.1,hv,rfl,?_,by omega⟩
  change u.val.val+1+(FiniteGaps.next (sourcePackets p) u.val-u.val.val-1)=v.val
  omega

/-- Every original internal window survives the boundary join as a reversed
gap of the new enclosing cycle. Its actual endpoints belong to that cycle. -/
theorem shell_internal_window_data (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (hc : 2 ≤ (componentSet p 0).card)
    (Q C : State n)
    (hCs : C.support=insert (⟨n-1,by have := NeZero.pos n; omega⟩ : Fin n)
      (insert (⟨(componentSet p 0).card,component_card_lt_of_multiple_roots p hm 0⟩ : Fin n)
        (prefixSourceCore p)))
    (hrev : ∀ B ∈ positiveSourceFamily p (componentSet p 0).card, ∀ i,
      Q (embed B.window i)=embed B.window (Fin.revPerm i))
    (B : FillingWindow n) (hB : B ∈ positiveSourceFamily p (componentSet p 0).card) :
    let v : Fin n := ⟨(componentSet p 0).card,component_card_lt_of_multiple_roots p hm 0⟩
    (∀ i, (Q*Equiv.swap (componentRight p 0) v) (embed B.window i)=
      embed B.window (Fin.revPerm i)) ∧
    (∀ i ∈ C.support, ¬Contains B.window i) ∧
    ∃ a b : Fin n, a ∈ C.support ∧ b ∈ C.support ∧
      a.val+1=B.window.offset ∧ B.window.offset+B.size=b.val := by
  classical
  let L := (componentSet p 0).card
  let v : Fin n := ⟨L,component_card_lt_of_multiple_roots p hm 0⟩
  have hproper := component_card_lt_of_multiple_roots p hm 0
  have hbsize := (positive_source_family_spec p L).2.2.1 B hB
  obtain ⟨_,hright,_⟩ := prefix_component_source_ends p hc hproper
  have hinside (i : Fin n) (hi : Contains B.window i) : i.val < L := by
    have hh := hi.2
    omega
  have hav (i : Fin n) (hi : i ∈ C.support) : ¬Contains B.window i := by
    rw [hCs] at hi
    simp only [Finset.mem_insert] at hi
    rcases hi with rfl | rfl | hi
    · intro hb; have := hinside _ hb; dsimp only [L] at this; omega
    · intro hb; have := hinside _ hb; dsimp only [L] at this; omega
    · exact positive_family_avoids_source p L B hB i (Finset.mem_filter.mp hi).1
  refine ⟨?_,hav,?_⟩
  · intro i
    have hmem := contains_embed B.window i
    have hne : embed B.window i ≠ componentRight p 0 := by
      intro he
      have hh := positive_family_avoids_source p L B hB (componentRight p 0) hright
      exact hh (he ▸ hmem)
    have hnv : embed B.window i ≠ v := by
      intro he
      have hh := hinside _ hmem
      rw [he] at hh
      change L < L at hh
      omega
    change (Q*Equiv.swap (componentRight p 0) v) (embed B.window i)=_
    rw [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hne hnv]
    exact hrev B hB i
  · obtain ⟨a,b,ha,hb,hao,hbe,hbL⟩ := positive_source_window_ends p L B hB
    have hmem (i : Fin n) (hi : i ∈ sourcePackets p) (hvL : i.val ≤ L) : i ∈ C.support := by
      rw [hCs]
      by_cases he : i.val=L
      · have hiv : i=v := Fin.ext he
        rw [hiv]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hi,by omega⟩))
    exact ⟨a,b,hmem a ha (by omega),hmem b hb hbL,hao,hbe⟩

#print axioms shell_internal_window_data

def InternalShellGapWords (p Q C : State n) (hm : 2 ≤ (componentRoots p).card)
    (start finish : Fin n) : Prop :=
  let v : Fin n := ⟨(componentSet p 0).card,component_card_lt_of_multiple_roots p hm 0⟩
  ∀ B ∈ positiveSourceFamily p (componentSet p 0).card, ∃ a b : Fin n,
    a.val+1=B.window.offset ∧ B.window.offset+B.size=b.val ∧
    (a.val ≤ min start.val finish.val → max start.val finish.val < b.val →
      ∃ w : List Letter,
        eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
        (w.length : ℤ) ≤ (inversionNumber p : ℤ)+
          (∑ i, |displacement (Q*Equiv.swap (componentRight p 0) v) i|)-1)

theorem shell_internal_gap_words (hn : 2 ≤ n) (p : State n)
    (hm : 2 ≤ (componentRoots p).card) (hc : 2 ≤ (componentSet p 0).card)
    (Q C : State n)
    (hCs : C.support=insert (⟨n-1,by have := NeZero.pos n; omega⟩ : Fin n)
      (insert (⟨(componentSet p 0).card,component_card_lt_of_multiple_roots p hm 0⟩ : Fin n)
        (prefixSourceCore p)))
    (hrev : ∀ B ∈ positiveSourceFamily p (componentSet p 0).card, ∀ i,
      Q (embed B.window i)=embed B.window (Fin.revPerm i))
    (hbelow : FiniteRankOrder.Below p.symm
      (Q*Equiv.swap (componentRight p 0) ⟨(componentSet p 0).card,component_card_lt_of_multiple_roots p hm 0⟩))
    (hC : C ∈ (Q*Equiv.swap (componentRight p 0)
      ⟨(componentSet p 0).card,component_card_lt_of_multiple_roots p hm 0⟩).cycleFactorsFinset)
    (start finish : Fin n) : InternalShellGapWords p Q C hm start finish := by
  classical
  have hproper := component_card_lt_of_multiple_roots p hm 0
  obtain ⟨hzero,_,_⟩ := prefix_component_source_ends p hc hproper
  have h0 : (0 : Fin n) ∈ C.support := by
    rw [hCs]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_filter.mpr ⟨hzero,by change 0 < (componentSet p 0).card; omega⟩))
  have hz : (⟨n-1,by omega⟩ : Fin n) ∈ C.support := by rw [hCs]; simp
  intro B hB
  obtain ⟨hmatch,havoid,a,b,ha,hb,hao,hbe⟩ := shell_internal_window_data p hm hc Q C hCs hrev B hB
  refine ⟨a,b,hao,hbe,?_⟩
  intro hlo hhi
  exact enclosing_reversed_gap_discount_word hn p _ C hbelow hC h0 hz B.window hmatch havoid
    a b ha hb hao.symm hbe start finish hlo hhi

#print axioms shell_internal_gap_words
end LRX.FiniteCuts
