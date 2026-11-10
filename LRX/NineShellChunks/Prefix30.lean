module

public import LRX.NineShellData

@[expose] public section
namespace LRX.NineShellCertificate
open FiniteCuts FiniteWindow RotationWords
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Complete suffix and endpoint check for the unchanged shell word table.
https://oeis.org/A186783 -/
private theorem check_3_0_start_0 : ∀ c : PermCode 4,
    Eligible (decode (n := 6) ((3 : Fin 6),(0 : Fin 5),c)) → ∀ finish : Fin 9,
    eval (table ((3 : Fin 6),(0 : Fin 5),c) (0 : Fin 9) finish)=
      (rotation (0 : Fin 9))⁻¹*target (decode ((3 : Fin 6),(0 : Fin 5),c))*rotation finish ∧
      (table ((3 : Fin 6),(0 : Fin 5),c) (0 : Fin 9) finish).length ≤ 36 := by
  decide +kernel
/-- Complete suffix and endpoint check for the unchanged shell word table.
https://oeis.org/A186783 -/
private theorem check_3_0_start_1 : ∀ c : PermCode 4,
    Eligible (decode (n := 6) ((3 : Fin 6),(0 : Fin 5),c)) → ∀ finish : Fin 9,
    eval (table ((3 : Fin 6),(0 : Fin 5),c) (1 : Fin 9) finish)=
      (rotation (1 : Fin 9))⁻¹*target (decode ((3 : Fin 6),(0 : Fin 5),c))*rotation finish ∧
      (table ((3 : Fin 6),(0 : Fin 5),c) (1 : Fin 9) finish).length ≤ 36 := by
  decide +kernel
/-- Complete suffix and endpoint check for the unchanged shell word table.
https://oeis.org/A186783 -/
private theorem check_3_0_start_2 : ∀ c : PermCode 4,
    Eligible (decode (n := 6) ((3 : Fin 6),(0 : Fin 5),c)) → ∀ finish : Fin 9,
    eval (table ((3 : Fin 6),(0 : Fin 5),c) (2 : Fin 9) finish)=
      (rotation (2 : Fin 9))⁻¹*target (decode ((3 : Fin 6),(0 : Fin 5),c))*rotation finish ∧
      (table ((3 : Fin 6),(0 : Fin 5),c) (2 : Fin 9) finish).length ≤ 36 := by
  decide +kernel
/-- Complete suffix and endpoint check for the unchanged shell word table.
https://oeis.org/A186783 -/
private theorem check_3_0_start_3 : ∀ c : PermCode 4,
    Eligible (decode (n := 6) ((3 : Fin 6),(0 : Fin 5),c)) → ∀ finish : Fin 9,
    eval (table ((3 : Fin 6),(0 : Fin 5),c) (3 : Fin 9) finish)=
      (rotation (3 : Fin 9))⁻¹*target (decode ((3 : Fin 6),(0 : Fin 5),c))*rotation finish ∧
      (table ((3 : Fin 6),(0 : Fin 5),c) (3 : Fin 9) finish).length ≤ 36 := by
  decide +kernel
/-- Complete suffix and endpoint check for the unchanged shell word table.
https://oeis.org/A186783 -/
private theorem check_3_0_start_4 : ∀ c : PermCode 4,
    Eligible (decode (n := 6) ((3 : Fin 6),(0 : Fin 5),c)) → ∀ finish : Fin 9,
    eval (table ((3 : Fin 6),(0 : Fin 5),c) (4 : Fin 9) finish)=
      (rotation (4 : Fin 9))⁻¹*target (decode ((3 : Fin 6),(0 : Fin 5),c))*rotation finish ∧
      (table ((3 : Fin 6),(0 : Fin 5),c) (4 : Fin 9) finish).length ≤ 36 := by
  decide +kernel
/-- Complete suffix and endpoint check for the unchanged shell word table.
https://oeis.org/A186783 -/
private theorem check_3_0_start_5 : ∀ c : PermCode 4,
    Eligible (decode (n := 6) ((3 : Fin 6),(0 : Fin 5),c)) → ∀ finish : Fin 9,
    eval (table ((3 : Fin 6),(0 : Fin 5),c) (5 : Fin 9) finish)=
      (rotation (5 : Fin 9))⁻¹*target (decode ((3 : Fin 6),(0 : Fin 5),c))*rotation finish ∧
      (table ((3 : Fin 6),(0 : Fin 5),c) (5 : Fin 9) finish).length ≤ 36 := by
  decide +kernel
/-- Complete suffix and endpoint check for the unchanged shell word table.
https://oeis.org/A186783 -/
private theorem check_3_0_start_6 : ∀ c : PermCode 4,
    Eligible (decode (n := 6) ((3 : Fin 6),(0 : Fin 5),c)) → ∀ finish : Fin 9,
    eval (table ((3 : Fin 6),(0 : Fin 5),c) (6 : Fin 9) finish)=
      (rotation (6 : Fin 9))⁻¹*target (decode ((3 : Fin 6),(0 : Fin 5),c))*rotation finish ∧
      (table ((3 : Fin 6),(0 : Fin 5),c) (6 : Fin 9) finish).length ≤ 36 := by
  decide +kernel
/-- Complete suffix and endpoint check for the unchanged shell word table.
https://oeis.org/A186783 -/
private theorem check_3_0_start_7 : ∀ c : PermCode 4,
    Eligible (decode (n := 6) ((3 : Fin 6),(0 : Fin 5),c)) → ∀ finish : Fin 9,
    eval (table ((3 : Fin 6),(0 : Fin 5),c) (7 : Fin 9) finish)=
      (rotation (7 : Fin 9))⁻¹*target (decode ((3 : Fin 6),(0 : Fin 5),c))*rotation finish ∧
      (table ((3 : Fin 6),(0 : Fin 5),c) (7 : Fin 9) finish).length ≤ 36 := by
  decide +kernel
/-- Complete suffix and endpoint check for the unchanged shell word table.
https://oeis.org/A186783 -/
private theorem check_3_0_start_8 : ∀ c : PermCode 4,
    Eligible (decode (n := 6) ((3 : Fin 6),(0 : Fin 5),c)) → ∀ finish : Fin 9,
    eval (table ((3 : Fin 6),(0 : Fin 5),c) (8 : Fin 9) finish)=
      (rotation (8 : Fin 9))⁻¹*target (decode ((3 : Fin 6),(0 : Fin 5),c))*rotation finish ∧
      (table ((3 : Fin 6),(0 : Fin 5),c) (8 : Fin 9) finish).length ≤ 36 := by
  decide +kernel
/-- All starting and finishing cursors for this complete code prefix.
https://oeis.org/A186783 -/
theorem code_prefix_3_0 (c : PermCode 4)
    (hc : Eligible (decode (n := 6) ((3 : Fin 6),(0 : Fin 5),c))) (start finish : Fin 9) :
    eval (table ((3 : Fin 6),(0 : Fin 5),c) start finish)=
      (rotation start)⁻¹*target (decode ((3 : Fin 6),(0 : Fin 5),c))*rotation finish ∧
      (table ((3 : Fin 6),(0 : Fin 5),c) start finish).length ≤ 36 := by
  fin_cases start
  · exact check_3_0_start_0 c hc finish
  · exact check_3_0_start_1 c hc finish
  · exact check_3_0_start_2 c hc finish
  · exact check_3_0_start_3 c hc finish
  · exact check_3_0_start_4 c hc finish
  · exact check_3_0_start_5 c hc finish
  · exact check_3_0_start_6 c hc finish
  · exact check_3_0_start_7 c hc finish
  · exact check_3_0_start_8 c hc finish
#print axioms code_prefix_3_0
end LRX.NineShellCertificate
