module

public import LRX.EnclosingCycleLoads
public import LRX.FiniteMarkedGap

@[expose] public section

namespace LRX.FiniteCuts
open scoped Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

def EnclosingPositiveArcs (C : State n) (s t : Fin n) : Prop :=
  ∀ dir : Bool, ∃ r ∈ C.support, ∃ port : Fin n,
    (port=r ∨ port+1=r) ∧
    (arcCoordinate dir s port).val ≤ (arcCoordinate dir s t).val ∧
    0 < portLoad (displacement C) port

def EnclosingCursorGap (C : State n) (s t : Fin n) : Prop :=
  ∃ u ∈ C.support, ∃ v ∈ C.support, u.val < v.val ∧
    (∀ z : Fin n, u.val < z.val → z.val < v.val → z ∉ C.support) ∧
    u.val ≤ s.val ∧ s.val < v.val ∧ u.val ≤ t.val ∧ t.val < v.val

theorem enclosing_arcs_between_outside (C : State n)
    (s t : Fin n) (hst : s.val < t.val) (ri pi ro po : Fin n)
    (hri : ri ∈ C.support) (hro : ro ∈ C.support)
    (hpi : pi=ri ∨ pi+1=ri) (hpo : po=ro ∨ po+1=ro)
    (hi : s.val ≤ pi.val ∧ pi.val ≤ t.val) (ho : po.val ≤ s.val ∨ t.val ≤ po.val)
    (hloadi : 0 < portLoad (displacement C) pi)
    (hloado : 0 < portLoad (displacement C) po) :
    EnclosingPositiveArcs C s t ∧ EnclosingPositiveArcs C t s := by
  have hb := ordered_arc_between s t pi hi.1 hi.2
  have ho' := ordered_arc_outside s t po hst ho
  constructor
  · intro dir; cases dir
    · exact ⟨ro,hro,po,hpo,ho'.1,hloado⟩
    · exact ⟨ri,hri,pi,hpi,hb.1,hloadi⟩
  · intro dir; cases dir
    · exact ⟨ri,hri,pi,hpi,hb.2,hloadi⟩
    · exact ⟨ro,hro,po,hpo,ho'.2,hloado⟩

theorem ordered_enclosing_cursor_cases (hn : 2 ≤ n) (C : State n) (hC : C.IsCycle)
    (hzero : (0 : Fin n) ∈ C.support)
    (hlast : (⟨n-1,by omega⟩ : Fin n) ∈ C.support)
    (s t : Fin n) (hst : s.val ≤ t.val) :
    (s.val < t.val ∧ EnclosingPositiveArcs C s t ∧ EnclosingPositiveArcs C t s) ∨
      EnclosingCursorGap C s t ∨ (s.val=n-1 ∧ t.val=n-1) := by
  classical
  let z : Fin n := ⟨n-1,by omega⟩
  have hp0 : 0 < portLoad (displacement C) 0 := by
    have hh := enclosing_cycle_port_load_ge_two C hC hzero hlast 0 (by simp; omega)
    omega
  by_cases ht : t.val < n-1
  · by_cases hm : ∃ r ∈ C.support, s.val < r.val ∧ r.val ≤ t.val
    · obtain ⟨r,hr,hsr,hrt⟩ := hm
      have hp : 0 < portLoad (displacement C) r := by
        have hh := enclosing_cycle_port_load_ge_two C hC hzero hlast r (by omega)
        omega
      exact Or.inl ⟨by omega,enclosing_arcs_between_outside C s t (by omega)
        r r 0 0 hr hzero (Or.inl rfl) (Or.inl rfl) ⟨by omega,hrt⟩
        (Or.inl (by simp)) hp hp0⟩
    · right; left
      exact finite_marked_gap C.support 0 z s t hzero hlast (by simp) (by dsimp [z]; omega)
        hst (fun r hr hh => hm ⟨r,hr,hh⟩)
  · have htlast : t.val=n-1 := by have := t.isLt; omega
    by_cases hs : s.val < n-1
    · have hz0 : z ≠ 0 := by intro he; have hh := congrArg Fin.val he; dsimp [z] at hh; omega
      have hzpred : (z-1 : Fin n).val=n-2 := by
        rw [Fin.val_sub_one_of_ne_zero hz0]
        dsimp [z]
        omega
      have hpz : 0 < portLoad (displacement C) (z-1) := by
        have hh := enclosing_cycle_port_load_ge_two C hC hzero hlast (z-1) (by rw [hzpred]; omega)
        omega
      exact Or.inl ⟨by omega,enclosing_arcs_between_outside C s t (by omega)
        z (z-1) 0 0 hlast hzero (Or.inr (by ring)) (Or.inl rfl)
        (by rw [hzpred]; constructor <;> omega) (Or.inl (by simp)) hpz hp0⟩
    · exact Or.inr (Or.inr ⟨by omega,htlast⟩)

/-- Complete cursor split for the new enclosing root itself. -/
theorem enclosing_cursor_cases (hn : 2 ≤ n) (C : State n) (hC : C.IsCycle)
    (hzero : (0 : Fin n) ∈ C.support)
    (hlast : (⟨n-1,by omega⟩ : Fin n) ∈ C.support) (start finish : Fin n) :
    (start ≠ finish ∧ EnclosingPositiveArcs C start finish) ∨
      EnclosingCursorGap C start finish ∨ (start.val=n-1 ∧ finish.val=n-1) := by
  by_cases h : start.val ≤ finish.val
  · rcases ordered_enclosing_cursor_cases hn C hC hzero hlast start finish h with h | h
    · exact Or.inl ⟨fun he => by have hh := congrArg Fin.val he; omega,h.2.1⟩
    · exact Or.inr h
  · rcases ordered_enclosing_cursor_cases hn C hC hzero hlast finish start (by omega) with h | h | h
    · exact Or.inl ⟨fun he => by have hh := congrArg Fin.val he; omega,h.2.2⟩
    · obtain ⟨u,hu,v,hv,huv,hgap,huf,hfv,hus,hsv⟩ := h
      exact Or.inr (Or.inl ⟨u,hu,v,hv,huv,hgap,hus,hsv,huf,hfv⟩)
    · exact Or.inr (Or.inr ⟨h.2,h.1⟩)

#print axioms enclosing_cursor_cases
end LRX.FiniteCuts
