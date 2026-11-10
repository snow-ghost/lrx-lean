module

public import LRX.FilteredExteriorCatalogue
public import LRX.OffsetExtraArrowSignConstraint

@[expose] public section
namespace LRX.FiniteCuts
open FiniteWindow RotationWords
set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- Complete dimension split of every actual catalogue pair of width7.
https://oeis.org/A186783 -/
theorem width_seven_cases (A B : SmallExteriorMap)
    (ha : A ∈ smallExteriorCatalogue) (hb : B ∈ smallExteriorCatalogue) (hw : A.1+B.1=7)
    (P : SmallExteriorMap → SmallExteriorMap → Prop)
    (h25 : ∀ a : State 2,∀ b : State 5,P ⟨2,a⟩ ⟨5,b⟩)
    (h34 : ∀ a : State 3,∀ b : State 4,P ⟨3,a⟩ ⟨4,b⟩)
    (h43 : ∀ a : State 4,∀ b : State 3,P ⟨4,a⟩ ⟨3,b⟩)
    (h52 : ∀ a : State 5,∀ b : State 2,P ⟨5,a⟩ ⟨2,b⟩) : P A B := by
  obtain ⟨ha0,ha1⟩ := catalogue_member_size A ha
  obtain ⟨hb0,hb1⟩ := catalogue_member_size B hb
  rcases A with ⟨a,A⟩
  rcases B with ⟨b,B⟩
  dsimp only at ha0 ha1 hb0 hb1 hw
  interval_cases a <;> interval_cases b
  all_goals first | omega | exact h25 A B | exact h34 A B | exact h43 A B | exact h52 A B

def SevenArrowConclusion (A B : SmallExteriorMap) : Prop :=
  ((∃ i,A.2 i=i) ∨ (∃ i,B.2 i=i)) ∧
    ∀ s : Fin 2,∀ l : Fin 2,¬OffsetExtraArrowSignConstraint A.2 B.2 1 0 0
      (if s.val=0 then 1 else -1) ((l.val : Int)+1)
instance (A B : SmallExteriorMap) : Decidable (SevenArrowConclusion A B) := by
  unfold SevenArrowConclusion
  infer_instance

def SevenArrowGuard (A B : SmallExteriorMap) : Prop :=
  (A.1-A.2.support.card)+(B.1-B.2.support.card) ≤ 1 →
    compatibleSignOffsets A B 1 1 0=true → SevenArrowConclusion A B
instance (A B : SmallExteriorMap) : Decidable (SevenArrowGuard A B) := by
  unfold SevenArrowGuard
  infer_instance

def SevenEmptyGuard (A B : SmallExteriorMap) : Prop :=
  (A.1-A.2.support.card)+(B.1-B.2.support.card) ≤ 2 →
    compatibleSignOffsets A B 0 2 1=false
instance (A B : SmallExteriorMap) : Decidable (SevenEmptyGuard A B) := by
  unfold SevenEmptyGuard
  infer_instance
#print axioms width_seven_cases
end LRX.FiniteCuts
