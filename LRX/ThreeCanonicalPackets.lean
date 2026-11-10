module

public import LRX.CanonicalPacketPeakService
public import LRX.GlobalPeakServiceFamily
public import LRX.ThreePortRoute

@[expose] public section

/-! Extract the services required by M4 directly from three canonical packets.
The exceptional structural classification is not assumed proved here. -/
namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n : ℕ} [NeZero n]

theorem canonical_packet_peak_family (hn : 2 ≤ n) (p : State n)
    (roots : List (Fin n))
    (hpos : ∀ r ∈ roots, 0 < leftPeak (canonicalRootPacket p r).symm n) :
    ∃ ss : List (ExactService n),
      ss.map (fun a => a.service.target)=roots.map (canonicalRootPacket p) ∧
      CanonicalFamily ss ∧
      (∀ a ∈ ss, (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i, |a.displacement i|)-2*(leftPeak a.service.target⁻¹ n : ℤ)) := by
  induction roots with
  | nil => exact ⟨[],rfl,by simp [CanonicalFamily],by simp⟩
  | cons r rest ih =>
    obtain ⟨a,ht,hd,hr⟩ := canonical_packet_peak_exact_service hn p r (hpos r (by simp))
    obtain ⟨ss,hst,hcan,hprice⟩ := ih (fun t ht => hpos t (List.mem_cons_of_mem _ ht))
    refine ⟨a::ss,by simp [ht,hst],?_,?_⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · rw [hd,ht]; rfl
      · exact hcan b hb
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · simpa only [hd,ht,Equiv.Perm.inv_def] using hr
      · exact hprice b hb

/-- The three services and their savings are constructed from the packet maps.
Only structural packet conditions and the scalar inversion deficit remain. -/
theorem three_canonical_packets_sharp (hn : 2 ≤ n) (hn20 : n ≤ 20)
    (p : State n) (roots : List (Fin n)) (hlen : roots.length=3)
    (hdis : (roots.map (canonicalRootPacket p)).Pairwise Equiv.Perm.Disjoint)
    (htarget : (roots.map (canonicalRootPacket p)).prod=p)
    (hpos : ∀ r ∈ roots, 0 < leftPeak (canonicalRootPacket p r).symm n)
    (hsave : 12 ≤ (roots.map (fun r =>
      2*(leftPeak (canonicalRootPacket p r).symm n : ℤ))).sum)
    (hdeficit : ((n/2 : ℕ) : ℤ)-2 ≤ (n.choose 2 : ℤ)-
      (LiftedModel.inversionCount (fun i : Fin n => (p.symm i : ℤ)) : ℤ)-
      ∑ i, |displacement p.symm i|)
    (s t : Fin n) :
    ∃ w : List Letter, eval w=(rotation s)⁻¹*p*rotation t ∧ w.length ≤ n.choose 2 := by
  obtain ⟨ss,ht,hcan,hprice⟩ := canonical_packet_peak_family hn p roots hpos
  have hsdis : ss.Pairwise (fun a b => a.service.target.Disjoint b.service.target) := by
    apply List.pairwise_map.mp
    rw [ht]
    exact hdis
  have hslen : ss.length=3 := by
    have hh := congrArg List.length ht
    simpa only [List.length_map,hlen] using hh
  have hsprod : (ss.map (fun a => a.service.target)).prod=p := by rw [ht,htarget]
  have hdisp (i : Fin n) : (ss.map (fun a => a.displacement i)).sum=displacement p.symm i := by
    have hh := canonical_family_displacement ss hsdis hcan i
    rw [hsprod] at hh
    exact hh
  have hsum := global_peak_family_price ss hsdis hcan hprice
  rw [hsprod] at hsum
  have hpeaks : (ss.map (fun a => 2*(leftPeak a.service.target⁻¹ n : ℤ))).sum=
      (roots.map (fun r => 2*(leftPeak (canonicalRootPacket p r).symm n : ℤ))).sum := by
    have hh := congrArg (fun qs : List (State n) =>
      (qs.map (fun q => 2*(leftPeak q⁻¹ n : ℤ))).sum) ht
    simpa only [List.map_map,Function.comp_def,Equiv.Perm.inv_def] using hh
  rw [hpeaks] at hsum
  have hrot : ((ss.map (fun a => BufferProgram.rotations a.service.word)).sum : ℤ)+12 ≤
      ∑ i, |displacement p.symm i| := by
    have hcast : ((ss.map (fun a => BufferProgram.rotations a.service.word)).sum : ℤ)=
        (ss.map (fun a => (BufferProgram.rotations a.service.word : ℤ))).sum := by
      simp [Function.comp_def]
    rw [hcast]
    change _=(∑ i, |displacement p.symm i|)-_ at hsum
    omega
  apply ThreePortRoute.exceptional_three_services_sharp hn hn20
    (p := p) (d := displacement p.symm)
    (by simpa only [Equiv.symm_symm] using canonical_lift p.symm)
    ss hslen hsdis hsprod hdisp hrot ?_ s t
  simpa only [displacement_endpoint] using hdeficit

#print axioms canonical_packet_peak_family
#print axioms three_canonical_packets_sharp
end LRX.FiniteCuts
