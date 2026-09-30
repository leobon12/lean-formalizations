import QuantumZipper.Proofs.Zipper.D3PlusN2Scale
import QuantumZipper.Proofs.GFF.CameronMartinTV

/-!
# D3⁺(i), node N2: the Cameron–Martin increment input

`CMIncrStmt` (D3PlusN2CMLoc.lean) is exactly the Cameron–Martin total-variation bound
`CMTV.abs_integral_incr_shift_sub_le` (Berestycki–Powell arXiv:2004.04720, Lemmas 3.12 and 3.14;
`balIncr` is definitionally `CMTV.incr`). So D3⁺(i) in rich form rests on the two remaining N2
nodes `D3PlusIN2TmZeroStmt` and `D3PlusN2HarmPartStmt`.
-/

namespace QuantumZipper
namespace D3Plus

/-- The Cameron–Martin increment node of N2 holds. -/
theorem cmIncrStmt_holds : CMIncrStmt := by
  intro Ω _ P _ X ψ hX h2 hc he F hF hFb
  exact CMTV.abs_integral_incr_shift_sub_le hX h2 hc he hF hFb

/-- D3⁺(i) (rich form, N2) from the two remaining nodes. -/
theorem d3PlusIN2Rich_of_two (hZ : D3PlusIN2TmZeroStmt) (hHP : D3PlusN2HarmPartStmt) :
    D3PlusIN2RichStmt :=
  d3PlusIN2Rich_of_core hZ cmIncrStmt_holds hHP

end D3Plus
end QuantumZipper
