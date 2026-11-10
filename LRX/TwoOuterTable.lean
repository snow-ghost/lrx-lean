import LRX.TwoOuterTableData

namespace LRX.FinitePeak

theorem two_outer_mem_table (p f e a U v : ℤ) (h : TwoOuter p f e a U v) :
    (p,f,e,a,U,v) ∈ twoOuterRows := by
  obtain ⟨hf3,he3,ha2,hv13⟩ := two_outer_bounds p f e a U v h
  have hOriginal := h
  obtain ⟨hp0,hp1,hf0,_,he0,_,ha0,_,hU1,hU7,hv4,_⟩ := h
  let pp : Fin 2 := ⟨p.toNat,by omega⟩
  let ff : Fin 4 := ⟨f.toNat,by omega⟩
  let ee : Fin 4 := ⟨e.toNat,by omega⟩
  let aa : Fin 3 := ⟨a.toNat,by omega⟩
  let uu : Fin 7 := ⟨(U-1).toNat,by omega⟩
  let vv : Fin 10 := ⟨(v-4).toNat,by omega⟩
  have hp : (pp.val : ℤ)=p := by dsimp only [pp]; omega
  have hf : (ff.val : ℤ)=f := by dsimp only [ff]; omega
  have he : (ee.val : ℤ)=e := by dsimp only [ee]; omega
  have ha : (aa.val : ℤ)=a := by dsimp only [aa]; omega
  have hu : (uu.val : ℤ)+1=U := by dsimp only [uu]; omega
  have hv : (vv.val : ℤ)+4=v := by dsimp only [vv]; omega
  have hc := checked_two_outer_table pp ff ee aa uu vv
  simp only [hp,hf,he,ha,hu,hv] at hc
  exact hc hOriginal

theorem admissible_two_mem_table (r : Profile) (hr : r.Admissible)
    (hcore : r.CoreBound) (ht : r.t=2)
    (he : r.exterior^2 ≤ 4*r.eps+r.parity+2*(r.E2-r.exterior%2)) :
    (r.parity,r.fixed,r.eps,r.isolated,r.peak,r.exterior) ∈ twoOuterRows :=
  two_outer_mem_table _ _ _ _ _ _ (admissible_two_outer r hr hcore ht he)

#print axioms admissible_two_mem_table
end LRX.FinitePeak
