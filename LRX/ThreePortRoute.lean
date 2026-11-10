import LRX.CircularOrderedRoute

/-! M4's exceptional three-service route. The circle metric statement is
valid at every size and for three arbitrary ports, including repeated ones.
The final theorem composes actual ExactServices and applies affine reduction.
-/
namespace LRX.ThreePortRoute
open RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def portDist (a b : Fin n) : ℕ := min (b-a).val (n-(b-a).val)

def cost (s t a b c : Fin n) : ℕ :=
  portDist s a + portDist a b + portDist b c + portDist c t

omit [NeZero n] in
theorem forward_bound (a b : Fin n) (h : a.val ≤ b.val) :
    portDist a b ≤ b.val-a.val := short_move_le_difference a b h

omit [NeZero n] in
theorem backward_bound (a b : Fin n) (h : b.val ≤ a.val) :
    portDist a b ≤ a.val-b.val := short_move_le_backward_difference a b h

omit [NeZero n] in
theorem forward_wrap_bound (a b : Fin n) (h : a.val ≤ b.val) :
    portDist a b ≤ n-b.val+a.val := by
  have hv := Fin.sub_val_of_le (show a ≤ b from h)
  have hm := min_le_right (b-a).val (n-(b-a).val)
  have hb := b.isLt
  unfold portDist
  rw [hv] at hm ⊢
  omega

theorem backward_wrap_bound (a b : Fin n) (h : b.val ≤ a.val) :
    portDist a b ≤ n-a.val+b.val := by
  by_cases he : b=a
  · subst b
    simp [portDist]
  · have hlt : b < a := by
      have : b.val ≠ a.val := fun h => he (Fin.ext h)
      omega
    have hv := Fin.coe_sub_iff_lt.mpr hlt
    have hm := min_le_left (b-a).val (n-(b-a).val)
    have ha := a.isLt
    unfold portDist
    rw [hv] at hm ⊢
    omega

/-- After ordering the ports clockwise from zero, four explicit orders
suffice. The two middle cases use opposite detours whose bounds sum to 2n. -/
theorem ordered_three (a b c t : Fin n) (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val) :
    cost 0 t a b c ≤ n ∨ cost 0 t a c b ≤ n ∨
    cost 0 t c a b ≤ n ∨ cost 0 t c b a ≤ n := by
  have hac : a.val ≤ c.val := by omega
  have h0a := forward_bound (0 : Fin n) a (by simp)
  have h0c := forward_wrap_bound (0 : Fin n) c (by simp)
  have habd := forward_bound a b hab
  have hbcd := forward_bound b c hbc
  have hbad := backward_bound b a hab
  have hcbd := backward_bound c b hbc
  have hacw := forward_wrap_bound a c hac
  have hcaw := backward_wrap_bound c a hac
  simp only [Fin.val_zero, Nat.sub_zero, Nat.add_zero] at h0a h0c
  by_cases hct : c.val ≤ t.val
  · have hctd := forward_bound c t hct
    have ht := t.isLt
    left
    unfold cost
    omega
  by_cases hta : t.val ≤ a.val
  · have hatd := backward_bound a t hta
    right; right; right
    unfold cost
    omega
  by_cases htb : t.val ≤ b.val
  · have hbtd := backward_bound b t htb
    have hatd := forward_bound a t (by omega)
    by_cases hnear : 2*a.val ≤ t.val
    · right; left
      unfold cost
      omega
    · right; right; right
      unfold cost
      omega
  · have hctd := backward_bound c t (by omega)
    have hbtd := forward_bound b t (by omega)
    by_cases hnear : 2*c.val ≤ n+t.val
    · left
      unfold cost
      omega
    · right; right; left
      unfold cost
      omega

theorem cost_recenter (s t a b c : Fin n) :
    cost 0 (t-s) (a-s) (b-s) (c-s) = cost s t a b c := by
  have hab : (b-s)-(a-s)=b-a := by ring
  have hbc : (c-s)-(b-s)=c-b := by ring
  have hct : (t-s)-(c-s)=t-c := by ring
  simp only [cost, portDist, sub_zero, hab, hbc, hct]

/-- Reordering the three complete services pays every cursor movement. -/
theorem three_services_walk (services : List (ExactService n))
    (hlen : services.length=3) (s t : Fin n) :
    ∃ ordered : List (ExactService n), services.Perm ordered ∧
      walkCost s t (ordered.map ExactService.service) ≤ n := by
  obtain ⟨ordered,hperm,horder⟩ := arc_ordered_services true s services
  obtain ⟨a,b,c,rfl⟩ := List.length_eq_three.mp (hperm.length_eq.symm.trans hlen)
  have hab := (List.pairwise_cons.mp horder).1 b (by simp)
  have hbc := (List.pairwise_cons.mp (List.pairwise_cons.mp horder).2).1 c (by simp)
  change (a.service.port-s).val ≤ (b.service.port-s).val at hab
  change (b.service.port-s).val ≤ (c.service.port-s).val at hbc
  have h := ordered_three (a.service.port-s) (b.service.port-s) (c.service.port-s) (t-s) hab hbc
  simp only [cost_recenter] at h
  rcases h with h | h | h | h
  · exact ⟨[a,b,c],hperm,by simpa [walkCost,cost,portDist,Nat.add_assoc] using h⟩
  · refine ⟨[a,c,b], hperm.trans (List.Perm.cons a (List.Perm.swap c b [])), ?_⟩
    simpa [walkCost,cost,portDist,Nat.add_assoc] using h
  · have hp : ([a,b,c] : List (ExactService n)).Perm [c,a,b] := by
      exact List.perm_append_comm (l₁ := [a,b]) (l₂ := [c])
    exact ⟨[c,a,b], hperm.trans hp, by simpa [walkCost,cost,portDist,Nat.add_assoc] using h⟩
  · have hp : ([a,b,c] : List (ExactService n)).Perm [c,b,a] := by
      simpa using (List.reverse_perm [a,b,c]).symm
    exact ⟨[c,b,a], hperm.trans hp, by simpa [walkCost,cost,portDist,Nat.add_assoc] using h⟩

/-- The metric lemma produces a literal word for the original permutation,
with exactly the original inversion price and at most n additional cursor rotations.
No diameter statement or permutation-size restriction is assumed. -/
theorem three_services_reduced_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (services : List (ExactService n))
    (hlen : services.length=3)
    (hdis : services.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (htarget : (services.map (fun a => a.service.target)).prod=p)
    (hdisp : ∀ i, (services.map (fun a => a.displacement i)).sum=d i)
    (s t : Fin n) :
    ∃ w : List Letter, eval w=(rotation s)⁻¹*p*rotation t ∧
      w.length ≤ LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i)+
        (services.map (fun a => BufferProgram.rotations a.service.word)).sum+n := by
  obtain ⟨ordered,hperm,hcost⟩ := three_services_walk services hlen s t
  have hdo : ordered.Pairwise (fun a b => a.service.target.Disjoint b.service.target) :=
    (hperm.pairwise_iff (fun h => h.symm)).mp hdis
  have hto : (ordered.map (fun a => a.service.target)).prod=p := by
    rw [← Equiv.Perm.disjoint_prod_perm (List.pairwise_map.mpr hdis)
      (hperm.map (fun a => a.service.target))]
    exact htarget
  have hdisp' (i : Fin n) : (ordered.map (fun a => a.displacement i)).sum=d i := by
    rw [← (hperm.map (fun a => a.displacement i)).sum_eq]
    exact hdisp i
  obtain ⟨w,he,hl⟩ := reduced_route_from hn hd ordered hdo hto hdisp' s t
  have hrot := (hperm.map (fun a => BufferProgram.rotations a.service.word)).sum_eq
  exact ⟨w,he,by omega⟩

/-- The last arithmetic step for the n=16,20 exceptions, stated for n<=20.
The services, their savings and the deficit remain explicit inputs. -/
theorem exceptional_three_services_sharp (hn : 2 ≤ n) (hn20 : n ≤ 20)
    {p : State n} {d : Fin n → ℤ} (hd : AffineLift.IsLift p 0 d)
    (services : List (ExactService n)) (hlen : services.length=3)
    (hdis : services.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (htarget : (services.map (fun a => a.service.target)).prod=p)
    (hdisp : ∀ i, (services.map (fun a => a.displacement i)).sum=d i)
    (hrot : ((services.map (fun a => BufferProgram.rotations a.service.word)).sum : ℤ)+12 ≤
      ∑ i, |d i|)
    (hdeficit : ((n/2 : ℕ) : ℤ)-2 ≤ (n.choose 2 : ℤ)-
      (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)-∑ i, |d i|)
    (s t : Fin n) :
    ∃ w : List Letter, eval w=(rotation s)⁻¹*p*rotation t ∧ w.length ≤ n.choose 2 := by
  obtain ⟨w,he,hl⟩ := three_services_reduced_word hn hd services hlen hdis htarget hdisp s t
  exact ⟨w,he,by omega⟩

#print axioms ordered_three
#print axioms three_services_walk
#print axioms three_services_reduced_word
#print axioms exceptional_three_services_sharp
end LRX.ThreePortRoute
