import LRX.EnclosingCycleIncidentService
import LRX.WeightedPacketAssembly

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n : ℕ} [NeZero n]

/-- Exact retained-root and child family, before choosing a cursor route. -/
theorem enclosing_selected_family (hn : 2 ≤ n) (G C : State n)
    (hC : C ∈ G.cycleFactorsFinset)
    (hzero : (0 : Fin n) ∈ C.support)
    (hlast : (⟨n-1,by have := NeZero.pos n; omega⟩ : Fin n) ∈ C.support)
    (ss : List (ExactService n))
    (hdis : ss.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hcan : CanonicalFamily ss)
    (hpart : CyclePart.IsPart (ss.map (fun a => a.service.target)).prod G.symm)
    (houtside : C.Disjoint (ss.map (fun a => a.service.target)).prod)
    (saving : ExactService n → ℤ)
    (hprice : ∀ a ∈ ss, (BufferProgram.rotations a.service.word : ℤ) ≤
      (∑ i, |a.displacement i|)-saving a)
    (r port : Fin n) (hr : r ∈ C.support) (hp : port=r ∨ port+1=r) :
    ∃ a : ExactService n, a.service.port=port ∧ CanonicalFamily (a::ss) ∧
      (a::ss).Pairwise (fun a b => a.service.target.Disjoint b.service.target) ∧
      ((a::ss).map (fun a => a.service.target)).prod=G.symm ∧
      (((a::ss).map (fun a => BufferProgram.rotations a.service.word)).sum : ℤ) ≤
        (∑ i, |displacement G i|)-portLoad (displacement C) port-(ss.map saving).sum := by
  let selected := (ss.map (fun a => a.service.target)).prod
  let R := CyclePart.remaining selected G.symm hpart
  have hretained : C ∈ Equiv.Perm.cycleFactorsFinset R.symm :=
    retained_enclosing_cycle G C selected hpart hC houtside
  obtain ⟨a,ha,hat,had,har⟩ := enclosing_cycle_incident_service hn R C
    hretained hzero hlast r port hr hp
  have hpair : (a::ss).Pairwise (fun a b => a.service.target.Disjoint b.service.target) := by
    apply List.pairwise_cons.mpr
    refine ⟨?_,hdis⟩
    intro b hb
    have hs := Equiv.Perm.support_le_prod_of_mem (List.mem_map.mpr ⟨b,hb,rfl⟩)
      (List.pairwise_map.mpr hdis)
    rw [hat]
    exact (CyclePart.remaining_disjoint selected G.symm hpart).mono le_rfl hs
  have hcanonical : CanonicalFamily (a::ss) := by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · rw [had,hat]
      rfl
    · exact hcan b hb
  have hprod : ((a::ss).map (fun b => b.service.target)).prod=G.symm := by
    simp only [List.map_cons,List.prod_cons,hat]
    exact CyclePart.remaining_product selected G.symm hpart
  have hmass := canonical_family_mass (a::ss) hpair hcanonical
  rw [hprod] at hmass
  change ((a::ss).map (fun b => ∑ i, |b.displacement i|)).sum=
    ∑ i, |displacement G i| at hmass
  simp only [List.map_cons,List.sum_cons,had] at hmass
  have hchild := canonical_family_weighted_bound ss hdis hcan saving hprice
  rw [← canonical_family_mass ss hdis hcan] at hchild
  have hrot : (((a::ss).map (fun b => BufferProgram.rotations b.service.word)).sum : ℤ) ≤
      (∑ i, |displacement G i|)-portLoad (displacement C) port-(ss.map saving).sum := by
    have hcast : (((a::ss).map (fun b => BufferProgram.rotations b.service.word)).sum : ℤ)=
        (BufferProgram.rotations a.service.word : ℤ)+
          (ss.map (fun b => (BufferProgram.rotations b.service.word : ℤ))).sum := by
      simp [Function.comp_def]
    rw [hcast]
    linarith
  exact ⟨a,ha,hcanonical,hpair,hprod,hrot⟩

#print axioms enclosing_selected_family
end LRX.FiniteCuts
