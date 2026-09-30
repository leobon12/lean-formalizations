import QuantumZipper.Proofs.Thm18.G2DisintXA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 disintegration, `x` side: the almost sure identifications

For the bump coefficient `α` and `h₀ = g2Y φ α`, almost surely (`g2x_ae_ident`):

* `ν_h = e^{α g} ν₀(h₀)` and `ν₀(h₀) = e^{−α g} ν_h` (`g = γφ/2`; local rule `g2_ae_bdryM_loc`);
* on the margin set `M` (left of the bump) `ν₀(h₀)|_M = ν_h|_M`;
* every margin root `x` is good, and the length `ν_h[x, 0]` equals `g2xf (h₀, x) α`.

Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- The margin set of roots. -/
def g2xM (i : G3Idx) (m : ℝ) : Set ℝ := {x | |x - i.t₁| + m < i.r₁} ∩ Icc (-i.δ) 0

theorem measurableSet_g2xM (i : G3Idx) (m : ℝ) : MeasurableSet (g2xM i m) :=
  (measurableSet_lt (by fun_prop) measurable_const).inter measurableSet_Icc

theorem g2xM_left (i : G3Idx) {m x : ℝ} (hm : 0 < m) (hx : x ∈ g2xM i m) :
    x + g2xR i m < g2xP i m - g2xR i m := g2x_margin_left i hm hx.1

/-- The density `e^{c φ γ/2}` on the line. -/
def g2xD (γ : ℝ) (i : G3Idx) (m c : ℝ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ / 2 * (c * g2xφ i m (t : ℂ))))

theorem g2xD_left {γ : ℝ} (i : G3Idx) {m : ℝ} (hm : 0 < m) (c : ℝ) {t : ℝ}
    (ht : t ≤ g2xP i m - g2xR i m) : g2xD γ i m c t = 1 := by
  simp [g2xD, g2xφ_real_left i hm ht]

theorem g2xD_le {γ : ℝ} (hγ : 0 < γ) (i : G3Idx) (m c t : ℝ) :
    g2xD γ i m c t ≤ ENNReal.ofReal (Real.exp (γ / 2 * |c|)) := by
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (by positivity)))
  have h0 := g2Phi_nonneg (g2xP i m) (g2xR i m) (t : ℂ)
  have h1 := g2Phi_le_one (g2xP i m) (g2xR i m) (t : ℂ)
  calc c * g2xφ i m (t : ℂ) ≤ |c| * g2xφ i m (t : ℂ) :=
        mul_le_mul_of_nonneg_right (le_abs_self c) h0
    _ ≤ |c| := mul_le_of_le_one_right (abs_nonneg c) h1

theorem g2xD_ge {γ : ℝ} (hγ : 0 < γ) (i : G3Idx) (m c t : ℝ) :
    ENNReal.ofReal (Real.exp (-(γ / 2 * |c|))) ≤ g2xD γ i m c t := by
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have h0 : 0 ≤ g2xφ i m (t : ℂ) := g2Phi_nonneg (g2xP i m) (g2xR i m) (t : ℂ)
  have h1 : g2xφ i m (t : ℂ) ≤ 1 := g2Phi_le_one (g2xP i m) (g2xR i m) (t : ℂ)
  have h2 : 0 ≤ (c + |c|) * g2xφ i m (t : ℂ) := mul_nonneg (by linarith [neg_abs_le c]) h0
  have h3 : |c| * g2xφ i m (t : ℂ) ≤ |c| := mul_le_of_le_one_right (abs_nonneg c) h1
  have h4 : -|c| ≤ c * g2xφ i m (t : ℂ) := by nlinarith
  have h5 : -(γ / 2 * |c|) = γ / 2 * (-|c|) := by ring
  rw [h5]
  exact mul_le_mul_of_nonneg_left h4 (by positivity)

/-- **The almost sure identifications of the `x` side.** -/
theorem g2x_ae_ident {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {m : ℝ} (hm : 0 < m)
    (α : Ω₀ → ℝ) :
    ∀ᵐ ω ∂gffBase.P,
      g3Hν γ ω = (g2ν₀ γ (g2xφ i m) (g2Y (g2xφ i m) α ω)).withDensity (g2xD γ i m (α ω)) ∧
      g2ν₀ γ (g2xφ i m) (g2Y (g2xφ i m) α ω) = (g3Hν γ ω).withDensity (g2xD γ i m (-α ω)) ∧
      g3Hν γ ω (Icc (-i.δ) 0) < ⊤ ∧ 0 < g3Hν γ ω (g2xJ i m) := by
  have hφc : Continuous (g2xφ i m) := continuous_g2Phi _ _
  have hφm : Measurable fun t : ℝ => g2xφ i m (t : ℂ) :=
    (hφc.comp Complex.continuous_ofReal).measurable
  have hfin : ∀ᵐ ω ∂gffBase.P, g3Mass γ i ω < ⊤ := by
    refine ae_lt_top (measurable_g3Mass γ i) ?_
    rw [← g3Z_eq_lintegral_g3Mass]; exact (g3Z_pos_lt_top hγ hγ2 i).2.ne
  filter_upwards [g2_ae_bdryM_loc hγ hγ2 hφc α, g2_ae_bdryM_loc_Y hγ hγ2 hφc hφm α,
    g2_ae_pos_g3Hν hγ hγ2, hfin, g3Mass_ae_eq_honest hγ hγ2 i] with ω hL hLY hpos hf he
  have e0 := hL 0
  have eα := hL (α ω)
  have eY := hLY (α ω)
  simp only [sub_self, zero_mul, mul_zero, Real.exp_zero, ENNReal.ofReal_one] at eα
  rw [show (fun _ : ℝ => (1 : ℝ≥0∞)) = 1 from rfl, withDensity_one] at eα
  refine ⟨?_, ?_, he ▸ hf, ?_⟩
  · rw [← eα, eY]; rfl
  · rw [g2ν₀, e0]
    congr 1; funext t; simp only [g2xD, zero_sub, neg_mul]
  · have hJ : g2xJ i m = Ioo (g2xP i m - g2xR i m) (g2xP i m + g2xR i m) := rfl
    rw [hJ]
    exact hpos _ _ (by linarith [g2xR_pos i hm]) (g2x_bump_neg i hm)

end Thm18Asm
end QuantumZipper
