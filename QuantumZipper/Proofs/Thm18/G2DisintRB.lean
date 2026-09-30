import QuantumZipper.Proofs.Thm18.G2DisintRA
import QuantumZipper.Proofs.Thm18.G2DisintXB
import QuantumZipper.Proofs.Thm18.G2LenSmoothRMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 disintegration, `R` side: the almost sure identifications

For the bump coefficient `α` and `h₀ = g2Y φ α`, almost surely (`g2r_ae_ident`):

* `ν_h = e^{α g} ν₀(h₀)` and `ν₀(h₀) = e^{−α g} ν_h` (`g = γφ/2`; local rule `g2_ae_bdryM_loc`);
* on the margin set `M` (left of the bump) `ν₀(h₀)|_M = ν_h|_M`;
* every margin root `x` is good, and the length `ν_h[x, 0]` equals `g2rf (h₀, x) α`.

Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- The margin set of roots. -/
def g2rM (i : G3Idx) (m : ℝ) : Set ℝ := {x | |x - i.t₂| + m < i.r₂} ∩ Icc 0 (i.t₂ + i.r₂)

theorem measurableSet_g2rM (i : G3Idx) (m : ℝ) : MeasurableSet (g2rM i m) :=
  (measurableSet_lt (by fun_prop) measurable_const).inter measurableSet_Icc

theorem g2rM_right (i : G3Idx) {m x : ℝ} (hm : 0 < m) (hx : x ∈ g2rM i m) :
    g2rP i m + g2rR i m < x - g2rR i m := g2r_margin_right i hm hx.1

theorem g2rM_le_W (i : G3Idx) {m x : ℝ} (hm : 0 < m) (hx : x ∈ g2rM i m) : x ≤ g2rW i m := by
  have h1 : g2rM' i m ≤ m := min_le_left _ _
  have h2 := g2rM'_pos i hm
  have h3 := le_abs_self (x - i.t₂)
  have h4 : |x - i.t₂| + m < i.r₂ := hx.1
  unfold g2rW; linarith

/-- The density `e^{c φ γ/2}` on the line. -/
def g2rD (γ : ℝ) (i : G3Idx) (m c : ℝ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ / 2 * (c * g2rφ i m (t : ℂ))))

theorem g2rD_right {γ : ℝ} (i : G3Idx) {m : ℝ} (hm : 0 < m) (c : ℝ) {t : ℝ}
    (ht : g2rP i m + g2rR i m ≤ t) : g2rD γ i m c t = 1 := by
  simp [g2rD, g2rφ_real_right i hm ht]

theorem g2rD_le {γ : ℝ} (hγ : 0 < γ) (i : G3Idx) (m c t : ℝ) :
    g2rD γ i m c t ≤ ENNReal.ofReal (Real.exp (γ / 2 * |c|)) := by
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (by positivity)))
  have h0 := g2Phi_nonneg (g2rP i m) (g2rR i m) (t : ℂ)
  have h1 := g2Phi_le_one (g2rP i m) (g2rR i m) (t : ℂ)
  calc c * g2rφ i m (t : ℂ) ≤ |c| * g2rφ i m (t : ℂ) :=
        mul_le_mul_of_nonneg_right (le_abs_self c) h0
    _ ≤ |c| := mul_le_of_le_one_right (abs_nonneg c) h1

theorem g2rD_ge {γ : ℝ} (hγ : 0 < γ) (i : G3Idx) (m c t : ℝ) :
    ENNReal.ofReal (Real.exp (-(γ / 2 * |c|))) ≤ g2rD γ i m c t := by
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have h0 : 0 ≤ g2rφ i m (t : ℂ) := g2Phi_nonneg (g2rP i m) (g2rR i m) (t : ℂ)
  have h1 : g2rφ i m (t : ℂ) ≤ 1 := g2Phi_le_one (g2rP i m) (g2rR i m) (t : ℂ)
  have h2 : 0 ≤ (c + |c|) * g2rφ i m (t : ℂ) := mul_nonneg (by linarith [neg_abs_le c]) h0
  have h3 : |c| * g2rφ i m (t : ℂ) ≤ |c| := mul_le_of_le_one_right (abs_nonneg c) h1
  have h4 : -|c| ≤ c * g2rφ i m (t : ℂ) := by nlinarith
  have h5 : -(γ / 2 * |c|) = γ / 2 * (-|c|) := by ring
  rw [h5]
  exact mul_le_mul_of_nonneg_left h4 (by positivity)

theorem g2_ae_pos_g3Hν_right {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂gffBase.P, ∀ a b : ℝ, 0 < a → a < b → 0 < g3Hν γ ω (Ioo a b) := by
  have hX' := isFreeGFFModConstH_normX gffBase.gff
  filter_upwards [G3Fid.ae_normField_good gffBase.gff hγ hγ2,
    BdryExist.ae_isVagueLimitR_qBoundaryMeasure hX' hγ hγ2, RegSample.ae_isRegularSample hX',
    Positivity.ae_forall_pos_qBoundaryMeasure_Ioo hX' hγ hγ2] with ω hgood hv hreg hpos
  intro a b ha hab
  have hU : IsOpen (Ioo a b) := isOpen_Ioo
  have key := F2.restrict_eq_withDensity_add_ofFun (x := normField γ gffBase.X ω)
    (y := normX gffBase.X ω) hU ⟨_, hgood.1⟩ ⟨_, hv⟩ hreg (φ := h0rev (γ ^ 2))
    (V := {z : ℂ | z ≠ 0}) isOpen_ne
    (fun t ht => by
      simp only [mem_setOf_eq, ne_eq, Complex.ofReal_eq_zero]
      exact (ha.trans ht.1).ne')
    ((E1.continuousOn_h0rev _).mono inter_subset_left)
    (Eventually.of_forall fun k t _ => by
      unfold avgReg
      congr 1
      funext n
      simp only [normField, Pi.add_apply, normX_of_prob]
      ring)
  have hρ : ∀ t ∈ Ioo a b, ENNReal.ofReal (Real.exp (γ / 2 * h0rev (γ ^ 2) (a : ℂ))) ≤
      ENNReal.ofReal (Real.exp (γ / 2 * h0rev (γ ^ 2) (t : ℂ))) := by
    intro t ht
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    unfold h0rev
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    refine Real.log_le_log (abs_pos.2 ha.ne') ?_
    rw [abs_of_pos ha, abs_of_pos (ha.trans ht.1)]
    exact ht.1.le
  have h := pos_of_withDensity_ge' hU.measurableSet key
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' hρ
    (by rw [Measure.restrict_apply_self]; exact hpos a b hab)
  rwa [Measure.restrict_apply_self] at h

theorem g2r_ae_fin {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {m : ℝ} (hm : 0 < m) :
    ∀ᵐ ω ∂gffBase.P, g3Hν γ ω (Icc 0 (g2rW i m)) < ⊤ := by
  have hW0 : 0 ≤ g2rW i m := by
    have := g2rM'_pos i hm; have := min_le_right m i.r₂; have := i.hη
    unfold g2rW g2rM' at *; unfold G3Idx.t₂ G3Idx.r₂ at *; linarith
  have hW1 : g2rW i m < 1 / 2 + i.η / 4 := by
    have := g2rM'_pos i hm; unfold g2rW; unfold G3Idx.t₂ G3Idx.r₂; linarith
  have hsub : Icc 0 (g2rW i m) ⊆ Ioo (-(3 * i.η / 4)) (1 / 2 + i.η / 4) := fun t ht =>
    ⟨by linarith [ht.1, i.hη], by linarith [ht.2]⟩
  have hmeas : Measurable fun ω => (g3ν₀ γ i ω + g3ν₂ γ i ω) (Icc 0 (g2rW i m)) :=
    (Measure.measurable_coe measurableSet_Icc).comp (measurable_g3sum₂' γ i)
  have hae : ∀ᵐ ω ∂gffBase.P, (g3ν₀ γ i ω + g3ν₂ γ i ω) (Icc 0 (g2rW i m)) =
      g3Hν γ ω (Icc 0 (g2rW i m)) :=
    (ae_g3Fid_sets hγ hγ2).mono fun ω hω => (hω i).2 _ hsub
  have hlt : ∫⁻ ω, (g3ν₀ γ i ω + g3ν₂ γ i ω) (Icc 0 (g2rW i m)) ∂gffBase.P < ⊤ := by
    rw [lintegral_congr_ae hae]
    exact lintegral_hν_Icc_zero_lt_top hγ hγ2 hW0 (by have := i.hη; have := i.hηδ; have := i.hδ; linarith)
  filter_upwards [ae_lt_top hmeas hlt.ne, hae] with ω h1 h2
  rwa [← h2]

/-- **The almost sure identifications of the `x` side.** -/
theorem g2r_ae_ident {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {m : ℝ} (hm : 0 < m)
    (α : Ω₀ → ℝ) :
    ∀ᵐ ω ∂gffBase.P,
      g3Hν γ ω = (g2ν₀ γ (g2rφ i m) (g2Y (g2rφ i m) α ω)).withDensity (g2rD γ i m (α ω)) ∧
      g2ν₀ γ (g2rφ i m) (g2Y (g2rφ i m) α ω) = (g3Hν γ ω).withDensity (g2rD γ i m (-α ω)) ∧
      g3Hν γ ω (Icc 0 (g2rW i m)) < ⊤ ∧ 0 < g3Hν γ ω (g2rJ i m) := by
  have hφc : Continuous (g2rφ i m) := continuous_g2Phi _ _
  have hφm : Measurable fun t : ℝ => g2rφ i m (t : ℂ) :=
    (hφc.comp Complex.continuous_ofReal).measurable
  filter_upwards [g2_ae_bdryM_loc hγ hγ2 hφc α, g2_ae_bdryM_loc_Y hγ hγ2 hφc hφm α,
    g2_ae_pos_g3Hν_right hγ hγ2, g2r_ae_fin hγ hγ2 i hm] with ω hL hLY hpos hf
  have e0 := hL 0
  have eα := hL (α ω)
  have eY := hLY (α ω)
  simp only [sub_self, zero_mul, mul_zero, Real.exp_zero, ENNReal.ofReal_one] at eα
  rw [show (fun _ : ℝ => (1 : ℝ≥0∞)) = 1 from rfl, withDensity_one] at eα
  refine ⟨?_, ?_, hf, ?_⟩
  · rw [← eα, eY]; rfl
  · rw [g2ν₀, e0]
    congr 1; funext t; simp only [g2rD, zero_sub, neg_mul]
  · have hJ : g2rJ i m = Ioo (g2rP i m - g2rR i m) (g2rP i m + g2rR i m) := rfl
    rw [hJ]
    exact hpos _ _ (g2r_bump_pos i hm) (by linarith [g2rR_pos i hm])

end Thm18Asm
end QuantumZipper
