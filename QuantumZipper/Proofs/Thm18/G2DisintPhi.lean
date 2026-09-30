import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Support

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 disintegration: the concrete bump `φ`

Sheffield (arXiv:1012.4797, proof of Prop. 5.5, p. 66) uses "a smooth bump function `φ_i`
supported in `U_i`". We take the radial bump `g2Phi p R z = smoothTransition (R² − ‖z − p‖²)`
around a real centre `p`: smooth, `[0, 1]`-valued, positive exactly on `ball p R`, supported in
`closedBall p R`, and even (`φ(z̄) = φ(z)`, since `p` is real), as `G2BumpDecompStmt` requires.
Own elementary construction.
-/

noncomputable section

open Set Metric
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm

/-- The radial bump around the real point `p` with radius `R`. -/
def g2Phi (p R : ℝ) (z : ℂ) : ℝ := Real.smoothTransition (R ^ 2 - ‖z - (p : ℂ)‖ ^ 2)

theorem contDiff_g2Phi (p R : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g2Phi p R) :=
  Real.smoothTransition.contDiff.comp
    (contDiff_const.sub ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)))

theorem continuous_g2Phi (p R : ℝ) : Continuous (g2Phi p R) :=
  (contDiff_g2Phi p R).continuous

theorem g2Phi_nonneg (p R : ℝ) (z : ℂ) : 0 ≤ g2Phi p R z := Real.smoothTransition.nonneg _

theorem g2Phi_le_one (p R : ℝ) (z : ℂ) : g2Phi p R z ≤ 1 := Real.smoothTransition.le_one _

theorem g2Phi_eq_zero {p R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz : R ≤ ‖z - (p : ℂ)‖) :
    g2Phi p R z = 0 :=
  Real.smoothTransition.zero_of_nonpos (by nlinarith [norm_nonneg (z - (p : ℂ))])

theorem g2Phi_pos {p R : ℝ} {z : ℂ} (hz : ‖z - (p : ℂ)‖ < R) : 0 < g2Phi p R z :=
  Real.smoothTransition.pos_of_pos (by nlinarith [norm_nonneg (z - (p : ℂ))])

theorem g2Phi_pos_iff {p R : ℝ} (hR : 0 ≤ R) (z : ℂ) : 0 < g2Phi p R z ↔ ‖z - (p : ℂ)‖ < R := by
  refine ⟨fun h => ?_, g2Phi_pos⟩
  by_contra hc
  exact (lt_irrefl (0 : ℝ)) (g2Phi_eq_zero hR (not_lt.1 hc) ▸ h)

theorem tsupport_g2Phi_subset {p R : ℝ} (hR : 0 ≤ R) :
    tsupport (g2Phi p R) ⊆ closedBall (p : ℂ) R := by
  refine closure_minimal (fun z hz => ?_) isClosed_closedBall
  rw [mem_closedBall, dist_eq_norm]
  by_contra hc
  exact hz (g2Phi_eq_zero hR (not_le.1 hc).le)

theorem hasCompactSupport_g2Phi {p R : ℝ} (hR : 0 ≤ R) : HasCompactSupport (g2Phi p R) :=
  HasCompactSupport.intro (isCompact_closedBall (p : ℂ) R) fun z hz => g2Phi_eq_zero hR (by
    rw [mem_closedBall, dist_eq_norm] at hz
    exact (not_le.1 hz).le)

theorem g2Phi_conj (p R : ℝ) (z : ℂ) : g2Phi p R (starRingEnd ℂ z) = g2Phi p R z := by
  unfold g2Phi
  congr 3
  rw [← Complex.conj_ofReal p, ← map_sub, Complex.norm_conj, Complex.conj_ofReal]

theorem g2Phi_center_ne_zero {p R : ℝ} (hR : 0 < R) : g2Phi p R (p : ℂ) ≠ 0 :=
  (g2Phi_pos (by simpa using hR)).ne'

end Thm18Asm
end QuantumZipper
