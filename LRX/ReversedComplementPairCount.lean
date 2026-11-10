module

public import LRX.ReversedWindowFixedCount
public import LRX.RootAndPairsCount

@[expose] public section

namespace LRX.FiniteWindow
open FiniteCuts
variable {n : ℕ}

theorem apart_family_positions_card (As : List (FillingWindow n))
    (hd : As.Pairwise FillingWindow.Apart) :
    (familyPositions As).card=(As.map (fun A => A.size)).sum := by
  classical
  induction As with
  | nil => simp [familyPositions]
  | cons A As ih =>
    obtain ⟨hA,hAs⟩ := List.pairwise_cons.mp hd
    have hdis : Disjoint (windowPositions A.window) (familyPositions As) := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      obtain ⟨B,hB,hBi⟩ := (mem_family_positions As i).mp hj
      exact hA B hB i (Finset.mem_filter.mp hi).2 hBi
    simp only [familyPositions,Finset.card_union_of_disjoint hdis,
      window_positions_card,ih hAs,List.map_cons,List.sum_cons]

theorem window_sizes_half_parity (As : List (FillingWindow n)) :
    2*(As.map (fun A => A.size/2)).sum+(As.map (fun A => A.size%2)).sum=
      (As.map (fun A => A.size)).sum := by
  induction As with
  | nil => simp
  | cons A As ih => simp only [List.map_cons,List.sum_cons]; omega

theorem reversed_complement_support_card (As : List (FillingWindow n)) (Q : State n)
    (S : Finset (Fin n))
    (hrev : ∀ A ∈ As, ∀ i, Q (embed A.window i)=embed A.window (Fin.revPerm i))
    (hd : As.Pairwise FillingWindow.Apart) (hcover : familyPositions As=Sᶜ)
    (hmoved : S ⊆ Q.support) :
    Q.support.card+(As.map (fun A => A.size%2)).sum=n := by
  classical
  have hfixed := reversed_window_family_fixed_count As Q hrev hd
  have hset : familyPositions As \ Q.support=Q.supportᶜ := by
    rw [hcover]
    ext i
    simp only [Finset.mem_sdiff,Finset.mem_compl]
    exact ⟨And.right,fun hi => ⟨fun hs => hi (hmoved hs),hi⟩⟩
  rw [hset,Finset.card_compl,Fintype.card_fin] at hfixed
  have hle : Q.support.card ≤ n := by simpa using Finset.card_le_univ Q.support
  omega

end LRX.FiniteWindow

namespace LRX.FiniteCuts
open FiniteWindow
variable {n : ℕ} [NeZero n]

theorem support_mul_swap_of_endpoints_moved (Q : State n) (u v : Fin n)
    (hu : u ∈ Q.support) (hv : v ∈ Q.support)
    (hu' : u ∈ (Q*Equiv.swap u v).support)
    (hv' : v ∈ (Q*Equiv.swap u v).support) :
    (Q*Equiv.swap u v).support=Q.support := by
  classical
  ext i
  by_cases hiu : i=u
  · subst i; simp only [hu,hu']
  · by_cases hiv : i=v
    · subst i; simp only [hv,hv']
    · simp only [Equiv.Perm.mem_support,Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne hiu hiv]

/-- The joined root consumes exactly one of the reversal pairs. All other
pair services are counted by the very same physical window sizes. -/
theorem reversed_complement_pairs_count (As : List (FillingWindow n)) (Q G C : State n)
    (S : Finset (Fin n))
    (hrev : ∀ A ∈ As, ∀ i, Q (embed A.window i)=embed A.window (Fin.revPerm i))
    (hd : As.Pairwise FillingWindow.Apart) (hcover : familyPositions As=Sᶜ)
    (hmoved : S ⊆ Q.support) (hsupport : G.support=Q.support)
    (hC : C ∈ G.cycleFactorsFinset) (hCcard : C.support.card=S.card+2)
    (hpairs : ∀ D ∈ G.cycleFactorsFinset, D ≠ C →
      ∃ a b : Fin n, a ≠ b ∧ D=Equiv.swap a b) :
    (G.cycleFactorsFinset.erase C).card+1=(As.map (fun A => A.size/2)).sum := by
  have hcount := (root_and_pairs_count G C hC hpairs).1
  rw [hCcard,hsupport] at hcount
  have htotal := reversed_complement_support_card As Q S hrev hd hcover hmoved
  have hsize := apart_family_positions_card As hd
  rw [hcover,Finset.card_compl,Fintype.card_fin] at hsize
  have hparts := window_sizes_half_parity As
  have hle : S.card ≤ n := by simpa using Finset.card_le_univ S
  omega

#print axioms reversed_complement_pairs_count
end LRX.FiniteCuts
