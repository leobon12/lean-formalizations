import QuantumZipper.Proofs.Zipper.SWCoreB5Map
import QuantumZipper.Proofs.Zipper.BdryAllMapsDist

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B5 (6): uniform boundary transport from the window node and the class core

Task SWC-B5 (`handoff/SW-CORE.md`): **`bdryTransportUnifStmt_of_window_distClass :
F1.BdryWindowStmt → BdryDistClassStmt → BdryTransportUnifStmt`**.

Source: S. Sheffield, M. Wang, arXiv:1605.06171 (`literature/1605.06171.pdf`), proof of
Theorem 4.3, p. 19 (following the proof of Theorem 1.4, pp. 11–12): change of coordinates, the
comparison of the pushed and the round regularizations (here the class core, uniform over the
class), and the window sandwich of the proof of Thm 4.2 (p. 19, "as in the proof of Thm 1.1").
SW state all-maps-at-once convergence for each map; the uniformity over a class is obtained here
by making every error term depend only on the class data (`perMap_sandwich`): the partition of
unity is taken in the target variable and independent of the map, the weights and window indices
are read off one point per piece, and the inverse-Lipschitz bound `Re ψ' ≥ m` and the Cauchy bound
on `ψ''` (`data_of_class`) control the oscillation of `f ∘ ψ⁻¹` and of `log|ψ'|` on a piece
uniformly. Own bookkeeping (SW give no details for the uniformity).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace SWCore

theorem up_arith {L Y ε θ B c e : ℝ} (hL0 : 0 ≤ L) (hLB : L ≤ B) (hY : Y ≤ L + ε / 3)
    (hε : 0 < ε) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθ : θ * (B + ε / 3) ≤ ε / 3)
    (hc : 1 - θ / 4 < c) (he : e = 1 + θ / 4) : e * (1 / c) * Y ≤ L + ε := by
  have hc0 : 0 < c := by linarith
  have hr : e * (1 / c) ≤ 1 + θ := by
    rw [mul_one_div, div_le_iff₀ hc0, he]; nlinarith
  have hr0 : 0 ≤ e * (1 / c) := by rw [he]; positivity
  rcases le_or_gt Y 0 with hY0 | hY0
  · nlinarith
  · have h1 : e * (1 / c) * Y ≤ (1 + θ) * Y := mul_le_mul_of_nonneg_right hr hY0.le
    have h2 : θ * L ≤ θ * B := mul_le_mul_of_nonneg_left hLB hθ0
    nlinarith

theorem lo_arith {L Y ε θ B c e : ℝ} (hLB : L ≤ B) (hY : L - ε / 3 ≤ Y) (hLε : 0 < L - ε)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθ : θ * (B + ε / 3) ≤ ε / 3) (hε : 0 < ε)
    (hc0 : 0 < c) (hc : c < 1 + θ / 4) (he : e = 1 + θ / 4) : c * e * (L - ε) ≤ Y := by
  have hq : c * e ≤ 1 + θ := by
    rw [he]
    have : c * (1 + θ / 4) ≤ (1 + θ / 4) * (1 + θ / 4) :=
      mul_le_mul_of_nonneg_right hc.le (by positivity)
    nlinarith
  have h1 : c * e * (L - ε) ≤ (1 + θ) * (L - ε) := mul_le_mul_of_nonneg_right hq hLε.le
  have h2 : θ * (L - ε) ≤ θ * B := mul_le_mul_of_nonneg_left (by linarith) hθ0
  nlinarith

theorem abs_dist_le {A E cc l Q e1 e2 : ℝ} (h1 : |A - Q * cc - E| ≤ e1)
    (h2 : |Q| * |cc - l| ≤ e2) : |A - Q * l - E| ≤ e1 + e2 := by
  have e : A - Q * l - E = (A - Q * cc - E) + Q * (cc - l) := by ring
  rw [e]
  calc _ ≤ |A - Q * cc - E| + |Q * (cc - l)| := abs_add_le _ _
    _ ≤ e1 + e2 := by rw [abs_mul]; linarith

/-- The two-level inner intervals carrying the support of `f`. -/
theorem exists_inner {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ Ioo a b) : ∃ d0 : ℝ, 0 < d0 ∧
      (∀ t, f t ≠ 0 → t ∈ Icc (a + 2 * d0) (b - 2 * d0)) := by
  obtain ⟨N, hN⟩ := CoordChange.tsupport_sub_IN hab hfc hfs
  refine ⟨CoordChange.δN a b N / 2, by linarith [CoordChange.δN_pos hab N], fun t ht => ?_⟩
  have := hN (subset_tsupport f ht)
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

end SWCore
end QuantumZipper
