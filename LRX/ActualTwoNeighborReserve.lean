import LRX.TwoNeighborReserve
import LRX.ShallowShellBoundaryJoin
import LRX.OriginalShallowExteriorDeficit

namespace LRX.FiniteCuts
open ContractionBlocks.System RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The linear reserve for the actual even source core. Neither a chosen
gap nor a hypothesis about its dominance is needed. -/
theorem prefix_even_zero_defect_linear_reserve (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0)
    (heven : (prefixSourceCore p).card%2=0) :
    let L := (componentSet p 0).card
    let l := (prefixSourceCore p).card/2
    ((n-L : ℕ) : ℤ)-1 ≤
      (l : ℤ)*((n : ℤ)-l)-(∑ i ∈ prefixSourceCore p, |displacement p.symm i|) := by
  classical
  let L := (componentSet p 0).card
  let R := (prefixSourceCore p).card
  let l := R/2
  let c := L-R
  let outside := n-L
  have hRL : R ≤ L := by
    apply Finset.card_le_card
    intro i hi
    exact (zero_component_prefix p i).mpr (Finset.mem_filter.mp hi).2
  have hLn : L ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ (componentSet p 0)
  obtain ⟨r,P,emb,hP,hsh,hfull,hcard,hδ,hmono,he0,heR,hwide,hmass,_⟩ :=
    prefix_zero_defect_physical_model p hmaj hm hlarge hz
  have hc0 : 2 ≤ (componentSet p 0).card := by have := NeZero.pos n; omega
  have hends := prefix_root_packet_extremes p hm hc0
  have hR : r+1=R := hcard
  have hsplit : r+1=2*l := by dsimp only [l,R]; omega
  have hsize : n=r+1+c+outside := by dsimp only [c,outside]; omega
  have hholes : holeMass (fun i => (emb i : ℤ))=(c : ℤ) := by
    rw [holeMass_span,he0,heR]
    have hw : (componentRight p 0).val+1=L := hends.2.2
    dsimp only [c]
    norm_num only [Fin.val_zero,Nat.cast_zero,sub_zero]
    omega
  have hh := even_shallow_exterior_reserve P hP hsh hfull (fun i => (emb i : ℤ)) hmono
    (canonical_lift p.symm).1 hmaj emb.toEmbedding hδ l c outside hsplit hsize hholes hwide
  unfold shellDeficit at hh
  rw [hmass] at hh
  exact hh

/-- In particular H=0 is excluded for every even actual large source core,
before any case split on the internal or external gaps. -/
theorem prefix_even_zero_defect_positive_reserve (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card)
    (hlarge : (n+1)/2 < (componentSet p 0).card) (hz : cycleDefect p=0)
    (heven : (prefixSourceCore p).card%2=0) :
    let l := (prefixSourceCore p).card/2
    1 ≤ (l : ℤ)*((n : ℤ)-l)-(∑ i ∈ prefixSourceCore p, |displacement p.symm i|) := by
  have hh := prefix_even_zero_defect_linear_reserve p hmaj hm hlarge hz heven
  have hc : 2 ≤ (componentSet p 0).card := by have := NeZero.pos n; omega
  have he := prefix_multiple_components_exterior_size p hc hm
  dsimp only at hh ⊢
  omega

#print axioms prefix_even_zero_defect_linear_reserve
#print axioms prefix_even_zero_defect_positive_reserve
end LRX.FiniteCuts
