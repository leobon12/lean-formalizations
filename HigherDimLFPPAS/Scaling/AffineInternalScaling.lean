import HigherDimLFPPAS.Core.Interfaces
import HigherDimLQGMetric.Sharp.ScaledMetric

/-!
# Internal distances under affine homotheties

Combine the existing affine-coordinate and positive metric-scaling identities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace HigherDimLFPPAS.Scaling

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

theorem affineInternalScaling_holds (d : ℕ) : Core.AffineInternalScaling d := by
  intro G G' z r c hr hc hscale V u v
  let H : ContMetric d := G'.affine r hr.ne' z
  have hEq : H = G.smul c hc := by
    apply Subtype.ext
    ext p
    rcases p with ⟨x, y⟩
    change G'.1 (r • x + z, r • y + z) = c * G.1 (x, y)
    rw [show r • x + z = z + r • x from add_comm _ _,
      show r • y + z = z + r • y from add_comm _ _]
    exact hscale x y
  have hImage : (fun x => r • x + z) '' V = (fun x => z + r • x) '' V := by
    congr 1
    funext x
    exact add_comm _ _
  rw [← hImage]
  rw [show z + r • u = r • u + z from add_comm _ _,
    show z + r • v = r • v + z from add_comm _ _]
  rw [← ContMetric.internal_affine (d := d) hr.ne' z G' V u v]
  change H.internal V u v = _
  rw [hEq, ContMetric.internal_smul]

end HigherDimLFPPAS.Scaling
