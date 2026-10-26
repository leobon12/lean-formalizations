import SupercriticalLFPPAS.Field.RadialHeatIdentity
import SupercriticalLFPPAS.Field.CircleAverageBounds
import SupercriticalLFPPAS.Field.LocalizedHeatEstimates
import SupercriticalLFPPAS.Field.HeatVersion
import SupercriticalLFPPAS.Implementation.Exists_jointHeatVersion
import SupercriticalLFPPAS.Implementation.JointHeatVersion
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Log-scale continuity of the heat field

This file proves the compact-uniform window estimate (2.2) from the radial heat representation
and the circle-average logarithmic growth bound.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open LQGMetric (DistC heatMollify)

namespace SupercriticalLFPPAS.Field

private def heatRadialIntegrand {Ω : Type*} (H : ℝ → ℂ → Ω → ℝ) (z : ℂ) (ω : Ω)
    (θ s : ℝ) : ℝ :=
  2 * Real.exp (-2 * θ) * s * H s z ω * Real.exp (-s ^ 2 * Real.exp (-2 * θ))

private def heatRadialIntegrandDeriv {Ω : Type*} (H : ℝ → ℂ → Ω → ℝ) (z : ℂ) (ω : Ω)
    (θ s : ℝ) : ℝ :=
  4 * Real.exp (-2 * θ) * s * (s ^ 2 * Real.exp (-2 * θ) - 1) *
    H s z ω * Real.exp (-s ^ 2 * Real.exp (-2 * θ))

private def heatKernelLogWeight (θ s : ℝ) : ℝ :=
  4 * Real.exp (-2 * θ) * s * |s ^ 2 * Real.exp (-2 * θ) - 1| *
    Real.exp (-s ^ 2 * Real.exp (-2 * θ)) * (1 + |Real.log s|)

private def heatKernelLogWeightScaled (θ u : ℝ) : ℝ :=
  4 * u * |u ^ 2 - 1| * Real.exp (-u ^ 2) * (1 + |θ + Real.log u|)

private def heatKernelLogPolyIntegral : ℝ :=
  ∫ u in Ioi (0 : ℝ),
    (1 + u + u ^ 2 + u ^ 3 + u ^ 4) * Real.exp (-u ^ 2)

private lemma hasDerivAt_heatRadialIntegrand {Ω : Type*} [MeasurableSpace Ω]
    (H : ℝ → ℂ → Ω → ℝ) (z : ℂ) (ω : Ω) (s θ : ℝ) :
    HasDerivAt (fun t => heatRadialIntegrand H z ω t s)
      (heatRadialIntegrandDeriv H z ω θ s) θ := by
  have hscale : HasDerivAt (fun t : ℝ => Real.exp (-2 * t))
      (-2 * Real.exp (-2 * θ)) θ := by
    have h0 := (Real.hasDerivAt_exp (-2 * θ)).comp θ
      ((hasDerivAt_id θ).const_mul (-2))
    have h1 := h0.congr_of_eventuallyEq
      (Eventually.of_forall fun t => by rfl)
    exact h1.congr_deriv (by ring_nf)
  have hE : HasDerivAt (fun t : ℝ => -s ^ 2 * Real.exp (-2 * t))
      (-s ^ 2 * (-2 * Real.exp (-2 * θ))) θ := hscale.const_mul (-s ^ 2)
  have hExp : HasDerivAt (fun t : ℝ => Real.exp (-s ^ 2 * Real.exp (-2 * t)))
      (Real.exp (-s ^ 2 * Real.exp (-2 * θ)) *
        (-s ^ 2 * (-2 * Real.exp (-2 * θ)))) θ :=
    (Real.hasDerivAt_exp _).comp θ hE
  have hA : HasDerivAt (fun t : ℝ => 2 * Real.exp (-2 * t) * s)
      (2 * (-2 * Real.exp (-2 * θ)) * s) θ := (hscale.const_mul 2).mul_const s
  have h := ((hA.mul_const (H s z ω)).mul hExp)
  have hfun : (fun t => heatRadialIntegrand H z ω t s) =ᶠ[𝓝 θ]
      ((fun t => 2 * Real.exp (-2 * t) * s * H s z ω) *
        fun t => Real.exp (-s ^ 2 * Real.exp (-2 * t))) :=
    Eventually.of_forall fun t => by simp [heatRadialIntegrand]
  have h' := h.congr_of_eventuallyEq hfun
  apply h'.congr_deriv
  simp [heatRadialIntegrandDeriv]
  ring

private lemma abs_log_le_inv_add (s : ℝ) (hs : 0 < s) :
    |Real.log s| ≤ 1 / s + s := by
  by_cases h : s < 1
  · have hs1 : Real.log s ≤ 0 := Real.log_nonpos hs.le h.le
    rw [abs_of_nonpos hs1]
    have hlog : Real.log (1 / s) ≤ 1 / s := Real.log_le_self (by positivity)
    have hinv : Real.log (1 / s) = -Real.log s := by
      rw [one_div, Real.log_inv]
    rw [hinv] at hlog
    linarith [inv_pos.mpr hs]
  · have h1 : 1 ≤ s := le_of_not_gt h
    have hs1 : 0 ≤ Real.log s := Real.log_nonneg h1
    rw [abs_of_nonneg hs1]
    exact (Real.log_le_self hs.le).trans (by linarith [one_div_pos.mpr hs])

private lemma integrableOn_polyGaussian {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun s : ℝ =>
      (1 + s + s ^ 2 + s ^ 3 + s ^ 4) * Real.exp (-c * s ^ 2)) (Ioi 0) := by
  have h0 : IntegrableOn (fun s : ℝ => Real.exp (-c * s ^ 2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq hc).integrableOn
  have h1 : IntegrableOn (fun s : ℝ => s * Real.exp (-c * s ^ 2)) (Ioi 0) := by
    convert integrableOn_rpow_mul_exp_neg_mul_sq hc (by norm_num : (-1 : ℝ) < 1) using 1
    ext s
    simp [Real.rpow_natCast]
  have h2 : IntegrableOn (fun s : ℝ => s ^ 2 * Real.exp (-c * s ^ 2)) (Ioi 0) := by
    convert integrableOn_rpow_mul_exp_neg_mul_sq hc (by norm_num : (-1 : ℝ) < 2) using 1
    ext s
    simp [Real.rpow_natCast]
  have h3 : IntegrableOn (fun s : ℝ => s ^ 3 * Real.exp (-c * s ^ 2)) (Ioi 0) := by
    convert integrableOn_rpow_mul_exp_neg_mul_sq hc (by norm_num : (-1 : ℝ) < 3) using 1
    ext s
    simp [Real.rpow_natCast]
  have h4 : IntegrableOn (fun s : ℝ => s ^ 4 * Real.exp (-c * s ^ 2)) (Ioi 0) := by
    convert integrableOn_rpow_mul_exp_neg_mul_sq hc (by norm_num : (-1 : ℝ) < 4) using 1
    ext s
    simp [Real.rpow_natCast]
  have hsum := h0.add h1 |>.add h2 |>.add h3 |>.add h4
  have heq : (fun s : ℝ => Real.exp (-c * s ^ 2) + s * Real.exp (-c * s ^ 2) +
      s ^ 2 * Real.exp (-c * s ^ 2) + s ^ 3 * Real.exp (-c * s ^ 2) +
      s ^ 4 * Real.exp (-c * s ^ 2)) =
    (fun s : ℝ => (1 + s + s ^ 2 + s ^ 3 + s ^ 4) * Real.exp (-c * s ^ 2)) := by
    funext s
    ring
  rw [← heq]
  exact hsum

private lemma heatKernelLogWeightScaled_bound (θ u : ℝ) (hu : 0 < u) :
    0 ≤ heatKernelLogWeightScaled θ u ∧
      heatKernelLogWeightScaled θ u ≤
        8 * (2 + |θ|) * (1 + u + u ^ 2 + u ^ 3 + u ^ 4) * Real.exp (-u ^ 2) := by
  have hu0 : 0 ≤ u := hu.le
  have hlog : |Real.log u| ≤ 1 / u + u := abs_log_le_inv_add u hu
  have habs : |u ^ 2 - 1| ≤ u ^ 2 + 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg u]
  have htheta : |θ + Real.log u| ≤ |θ| + |Real.log u| := abs_add_le _ _
  have hlog' : 1 + |θ + Real.log u| ≤ 1 + |θ| + 1 / u + u := by
    linarith
  have hP : 0 ≤ 1 + u + u ^ 2 + u ^ 3 + u ^ 4 := by positivity
  have hpolyA : u + u ^ 3 ≤ 1 + u + u ^ 2 + u ^ 3 + u ^ 4 := by
    nlinarith [sq_nonneg u, pow_nonneg hu0 3, pow_nonneg hu0 4]
  have hpolyB : 1 + 2 * u ^ 2 + u ^ 4 ≤
      2 * (1 + u + u ^ 2 + u ^ 3 + u ^ 4) := by
    nlinarith [sq_nonneg u, pow_nonneg hu0 3, pow_nonneg hu0 4]
  have heq : u * (u ^ 2 + 1) * (1 + |θ| + 1 / u + u) =
      (u + u ^ 3) * (1 + |θ|) + (1 + 2 * u ^ 2 + u ^ 4) := by
    have huNe : u ≠ 0 := ne_of_gt hu
    field_simp
    <;> ring
  have hcore : 4 * u * |u ^ 2 - 1| * (1 + |θ + Real.log u|) ≤
      8 * (2 + |θ|) * (1 + u + u ^ 2 + u ^ 3 + u ^ 4) := by
    have hprod : |u ^ 2 - 1| * (1 + |θ + Real.log u|) ≤
        (u ^ 2 + 1) * (1 + |θ| + 1 / u + u) := by
      calc |u ^ 2 - 1| * (1 + |θ + Real.log u|)
          ≤ (u ^ 2 + 1) * (1 + |θ + Real.log u|) :=
            mul_le_mul_of_nonneg_right habs (by positivity)
        _ ≤ (u ^ 2 + 1) * (1 + |θ| + 1 / u + u) :=
            mul_le_mul_of_nonneg_left hlog' (by positivity)
    have hcoef : 0 ≤ 4 * u := by positivity
    have hpoly :
        4 * ((u + u ^ 3) * (1 + |θ|) + (1 + 2 * u ^ 2 + u ^ 4)) ≤
          8 * (2 + |θ|) * (1 + u + u ^ 2 + u ^ 3 + u ^ 4) := by
      have hleft : (u + u ^ 3) * (1 + |θ|) + (1 + 2 * u ^ 2 + u ^ 4) ≤
          (1 + u + u ^ 2 + u ^ 3 + u ^ 4) * (1 + |θ|) +
            2 * (1 + u + u ^ 2 + u ^ 3 + u ^ 4) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hpolyA (by positivity)) hpolyB
      calc 4 * ((u + u ^ 3) * (1 + |θ|) + (1 + 2 * u ^ 2 + u ^ 4))
          ≤ 4 * ((1 + u + u ^ 2 + u ^ 3 + u ^ 4) * (1 + |θ|) +
              2 * (1 + u + u ^ 2 + u ^ 3 + u ^ 4)) := by gcongr
        _ = 4 * (1 + u + u ^ 2 + u ^ 3 + u ^ 4) * (3 + |θ|) := by ring
        _ ≤ 8 * (2 + |θ|) * (1 + u + u ^ 2 + u ^ 3 + u ^ 4) := by
          have ht : 0 ≤ |θ| := abs_nonneg θ
          have hlin : 3 + |θ| ≤ 2 * (2 + |θ|) := by linarith
          calc 4 * (1 + u + u ^ 2 + u ^ 3 + u ^ 4) * (3 + |θ|)
              ≤ 4 * (1 + u + u ^ 2 + u ^ 3 + u ^ 4) * (2 * (2 + |θ|)) := by
                exact mul_le_mul_of_nonneg_left hlin (by positivity)
            _ = 8 * (2 + |θ|) * (1 + u + u ^ 2 + u ^ 3 + u ^ 4) := by ring
    calc 4 * u * |u ^ 2 - 1| * (1 + |θ + Real.log u|)
        = 4 * u * (|u ^ 2 - 1| * (1 + |θ + Real.log u|)) := by ring
      _ ≤ 4 * u * ((u ^ 2 + 1) * (1 + |θ| + 1 / u + u)) :=
          mul_le_mul_of_nonneg_left hprod hcoef
      _ = 4 * (u * (u ^ 2 + 1) * (1 + |θ| + 1 / u + u)) := by ring
      _ = 4 * ((u + u ^ 3) * (1 + |θ|) + (1 + 2 * u ^ 2 + u ^ 4)) := by rw [heq]
      _ ≤ 8 * (2 + |θ|) * (1 + u + u ^ 2 + u ^ 3 + u ^ 4) := hpoly
  constructor
  · unfold heatKernelLogWeightScaled
    positivity
  · unfold heatKernelLogWeightScaled
    calc 4 * u * |u ^ 2 - 1| * Real.exp (-u ^ 2) * (1 + |θ + Real.log u|)
        ≤ (8 * (2 + |θ|) * (1 + u + u ^ 2 + u ^ 3 + u ^ 4)) *
            Real.exp (-u ^ 2) := by
          rw [show 4 * u * |u ^ 2 - 1| * Real.exp (-u ^ 2) *
              (1 + |θ + Real.log u|) =
              (4 * u * |u ^ 2 - 1| * (1 + |θ + Real.log u|)) *
                Real.exp (-u ^ 2) by ring]
          exact mul_le_mul_of_nonneg_right hcore (Real.exp_pos _).le
      _ = _ := by ring

private lemma heatKernelLogWeight_scale (θ u : ℝ) (hu : 0 < u) :
    heatKernelLogWeight θ (Real.exp θ * u) * Real.exp θ =
      heatKernelLogWeightScaled θ u := by
  have hb : 0 < Real.exp θ := Real.exp_pos θ
  have hlog : Real.log (Real.exp θ * u) = θ + Real.log u := by
    rw [Real.log_mul hb.ne' (ne_of_gt hu), Real.log_exp]
  have hscalePow : Real.exp (-2 * θ) * Real.exp θ * Real.exp θ = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    rw [show -2 * θ + θ + θ = 0 by ring, Real.exp_zero]
  have hSq : (Real.exp θ * u) ^ 2 * Real.exp (-2 * θ) = u ^ 2 := by
    rw [mul_pow]
    calc Real.exp θ ^ 2 * u ^ 2 * Real.exp (-2 * θ)
        = (Real.exp θ * Real.exp θ * Real.exp (-2 * θ)) * u ^ 2 := by ring
      _ = u ^ 2 := by
        rw [show Real.exp θ * Real.exp θ * Real.exp (-2 * θ) = 1 by
          calc Real.exp θ * Real.exp θ * Real.exp (-2 * θ)
              = Real.exp (-2 * θ) * Real.exp θ * Real.exp θ := by ring
            _ = 1 := hscalePow]
        ring
  unfold heatKernelLogWeight heatKernelLogWeightScaled
  rw [hlog, hSq]
  have hcoef : Real.exp (-2 * θ) * (Real.exp θ * u) * Real.exp θ = u := by
    calc Real.exp (-2 * θ) * (Real.exp θ * u) * Real.exp θ
        = (Real.exp (-2 * θ) * Real.exp θ * Real.exp θ) * u := by ring
      _ = u := by rw [hscalePow]; ring
  have hExpArg : -(Real.exp θ * u) ^ 2 * Real.exp (-2 * θ) = -u ^ 2 := by
    calc -(Real.exp θ * u) ^ 2 * Real.exp (-2 * θ)
        = -((Real.exp θ * u) ^ 2 * Real.exp (-2 * θ)) := by ring
      _ = -u ^ 2 := by rw [hSq]
  have hexp : Real.exp (-(Real.exp θ * u) ^ 2 * Real.exp (-2 * θ)) =
      Real.exp (-u ^ 2) := by rw [hExpArg]
  rw [hexp]
  calc 4 * Real.exp (-2 * θ) * (Real.exp θ * u) * |u ^ 2 - 1| *
        Real.exp (-u ^ 2) * (1 + |θ + Real.log u|) * Real.exp θ
      = 4 * (Real.exp (-2 * θ) * (Real.exp θ * u) * Real.exp θ) *
          |u ^ 2 - 1| * Real.exp (-u ^ 2) * (1 + |θ + Real.log u|) := by ring
    _ = 4 * u * |u ^ 2 - 1| * Real.exp (-u ^ 2) *
          (1 + |θ + Real.log u|) := by rw [hcoef]

private lemma heatKernelLogWeight_integrable (θ : ℝ) :
    Integrable (fun s : ℝ => heatKernelLogWeight θ s)
      (volume.restrict (Ioi (0 : ℝ))) := by
  let scale : ℝ := Real.exp (-2 * θ)
  let A : ℝ := 4 * scale * (scale + 1)
  have hscale : 0 < scale := by positivity
  have hA : 0 ≤ A := by positivity
  have hpoly : IntegrableOn
      (fun s : ℝ => (1 + s + s ^ 2 + s ^ 3 + s ^ 4) * Real.exp (-scale * s ^ 2))
      (Ioi 0) := integrableOn_polyGaussian hscale
  have hmajor : Integrable (fun s : ℝ => A *
      ((1 + s + s ^ 2 + s ^ 3 + s ^ 4) * Real.exp (-scale * s ^ 2)))
      (volume.restrict (Ioi 0)) := by
    simpa using hpoly.const_mul A
  have hcont : ContinuousOn (fun s : ℝ => heatKernelLogWeight θ s) (Ioi 0) := by
    unfold heatKernelLogWeight
    have hlog : ContinuousOn Real.log (Ioi 0) :=
      Real.continuousOn_log.mono (by intro s hs; exact (mem_Ioi.mp hs).ne')
    fun_prop
  apply Integrable.mono' hmajor (hcont.aestronglyMeasurable measurableSet_Ioi)
  apply (ae_restrict_iff' measurableSet_Ioi).2
  filter_upwards with s hs
  have hs : 0 < s := hs
  have hlog := abs_log_le_inv_add s hs
  have hfactor : |s ^ 2 * scale - 1| ≤ scale * s ^ 2 + 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg s]
  have hpoly' : s * (scale * s ^ 2 + 1) * (1 + 1 / s + s) ≤
      (scale + 1) * (1 + s + s ^ 2 + s ^ 3 + s ^ 4) := by
    have hsne : s ≠ 0 := ne_of_gt hs
    have heq : s * (scale * s ^ 2 + 1) * (1 + 1 / s + s) =
        scale * s ^ 4 + scale * s ^ 3 + (scale + 1) * s ^ 2 + s + 1 := by
      field_simp
      <;> ring
    rw [heq]
    have hs0 : 0 ≤ s := hs.le
    nlinarith [pow_nonneg hs0 3, pow_nonneg hs0 4]
  rw [Real.norm_eq_abs, heatKernelLogWeight]
  simp only [abs_mul, abs_abs,
    abs_of_pos (by positivity : 0 < (4 : ℝ) * Real.exp (-2 * θ)),
    abs_of_pos hs, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (show 0 ≤ 1 + |Real.log s| by positivity)]
  dsimp [scale]
  have hlog' : 1 + |Real.log s| ≤ 1 + 1 / s + s := by linarith [hlog]
  have hprod : |s ^ 2 * scale - 1| * (1 + |Real.log s|) ≤
      (scale * s ^ 2 + 1) * (1 + 1 / s + s) := by
    calc |s ^ 2 * scale - 1| * (1 + |Real.log s|)
        ≤ (scale * s ^ 2 + 1) * (1 + |Real.log s|) :=
          mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ ≤ (scale * s ^ 2 + 1) * (1 + 1 / s + s) :=
          mul_le_mul_of_nonneg_left hlog' (by positivity)
  have hExp : 0 ≤ Real.exp (-scale * s ^ 2) := (Real.exp_pos _).le
  have hpolyScale : 0 ≤ 4 * scale * Real.exp (-scale * s ^ 2) := by positivity
  calc 4 * scale * s * |s ^ 2 * scale - 1| * Real.exp (-s ^ 2 * scale) *
        (1 + |Real.log s|)
      = (4 * scale * Real.exp (-scale * s ^ 2) * s) *
          (|s ^ 2 * scale - 1| * (1 + |Real.log s|)) := by
          rw [show Real.exp (-s ^ 2 * scale) = Real.exp (-scale * s ^ 2) by
            congr 1
            ring]
          ring
    _ ≤ (4 * scale * Real.exp (-scale * s ^ 2) * s) *
          ((scale * s ^ 2 + 1) * (1 + 1 / s + s)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = (4 * scale * Real.exp (-scale * s ^ 2)) *
          (s * (scale * s ^ 2 + 1) * (1 + 1 / s + s)) := by ring
    _ ≤ (4 * scale * Real.exp (-scale * s ^ 2)) *
          ((scale + 1) * (1 + s + s ^ 2 + s ^ 3 + s ^ 4)) :=
          mul_le_mul_of_nonneg_left hpoly' hpolyScale
    _ = A * ((1 + s + s ^ 2 + s ^ 3 + s ^ 4) *
          Real.exp (-scale * s ^ 2)) := by dsimp [A]; ring

private lemma heatKernelLogWeight_integral_le (θ : ℝ) :
    ∫ s in Ioi (0 : ℝ), heatKernelLogWeight θ s ≤
      8 * (2 + |θ|) * heatKernelLogPolyIntegral := by
  let b : ℝ := Real.exp θ
  let T : ℝ → ℝ := fun u => heatKernelLogWeight θ (b * u) * b
  let G : ℝ → ℝ := fun u =>
    8 * (2 + |θ|) * (1 + u + u ^ 2 + u ^ 3 + u ^ 4) * Real.exp (-u ^ 2)
  have hb : 0 < b := by positivity
  have hpoly : IntegrableOn
      (fun u : ℝ => (1 + u + u ^ 2 + u ^ 3 + u ^ 4) * Real.exp (-u ^ 2))
      (Ioi 0) := by
    simpa [neg_one_mul] using
      (integrableOn_polyGaussian (c := (1 : ℝ)) (by norm_num))
  have hGint : Integrable G (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [G, mul_assoc] using hpoly.const_mul (8 * (2 + |θ|))
  have hTmeas : AEStronglyMeasurable T (volume.restrict (Ioi (0 : ℝ))) := by
    apply Measurable.aestronglyMeasurable
    dsimp [T, heatKernelLogWeight]
    measurability
  have hTbound : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), ‖T u‖ ≤ G u := by
    apply (ae_restrict_iff' measurableSet_Ioi).2
    filter_upwards with u hu
    have hu : 0 < u := hu
    have heq : T u = heatKernelLogWeightScaled θ u := by
      dsimp [T, b]
      exact heatKernelLogWeight_scale θ u hu
    rw [heq, Real.norm_eq_abs,
      abs_of_nonneg (heatKernelLogWeightScaled_bound θ u hu).1]
    exact heatKernelLogWeightScaled_bound θ u hu |>.2
  have hTint : Integrable T (volume.restrict (Ioi (0 : ℝ))) :=
    Integrable.mono' hGint hTmeas hTbound
  have hTmono : T ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] G := by
    filter_upwards [hTbound, ae_restrict_mem measurableSet_Ioi] with u hu hmem
    have huPos : 0 < u := hmem
    have hpos : 0 ≤ T u := by
      change 0 ≤ heatKernelLogWeight θ (b * u) * b
      rw [heatKernelLogWeight_scale θ u huPos]
      exact (heatKernelLogWeightScaled_bound θ u huPos).1
    rw [Real.norm_eq_abs, abs_of_nonneg hpos] at hu
    exact hu
  have hTle := integral_mono_ae hTint hGint hTmono
  have hGval : (∫ u in Ioi (0 : ℝ), G u) =
      8 * (2 + |θ|) * heatKernelLogPolyIntegral := by
    have hG_eq : G = fun u : ℝ => (8 * (2 + |θ|)) *
        ((1 + u + u ^ 2 + u ^ 3 + u ^ 4) * Real.exp (-u ^ 2)) := by
      funext u
      dsimp [G]
      ring
    rw [hG_eq, integral_const_mul]
    rfl
  have hchange := MeasureTheory.integral_comp_mul_left_Ioi'
    (fun s : ℝ => heatKernelLogWeight θ s) (a := 0) (b := b) hb
  have hTchange : (∫ u in Ioi (0 : ℝ), T u) =
      ∫ s in Ioi (0 : ℝ), heatKernelLogWeight θ s := by
    calc (∫ u in Ioi (0 : ℝ), T u)
        = (∫ u in Ioi (0 : ℝ), heatKernelLogWeight θ (b * u)) * b := by
            dsimp [T]
            rw [integral_mul_const]
      _ = b * (∫ u in Ioi (0 : ℝ), heatKernelLogWeight θ (b * u)) := by ring
      _ = ∫ s in Ioi (0 : ℝ), heatKernelLogWeight θ s := by
            simpa [smul_eq_mul, b] using hchange
  calc (∫ s in Ioi (0 : ℝ), heatKernelLogWeight θ s)
      = ∫ u in Ioi (0 : ℝ), T u := hTchange.symm
    _ ≤ ∫ u in Ioi (0 : ℝ), G u := hTle
    _ = 8 * (2 + |θ|) * heatKernelLogPolyIntegral := hGval

private lemma heatRadialIntegrandDeriv_abs_le {Ω : Type*} [MeasurableSpace Ω]
    {H : ℝ → ℂ → Ω → ℝ} {z : ℂ} {ω : Ω} {C θ₀ θ s : ℝ}
    (hC : 0 ≤ C) (hbound : |H s z ω| ≤ C * (1 + |Real.log s|))
    (hs : 0 < s) (hθ : θ ∈ Metric.ball θ₀ 1) :
    |heatRadialIntegrandDeriv H z ω θ s| ≤
      (4 * C * max (Real.exp (-2 * (θ₀ - 1))) 1 *
        (max (Real.exp (-2 * (θ₀ - 1))) 1 + 1)) *
        (1 + s + s ^ 2 + s ^ 3 + s ^ 4) *
        Real.exp (-Real.exp (-2 * (θ₀ + 1)) * s ^ 2) := by
  let m : ℝ := Real.exp (-2 * (θ₀ + 1))
  let M : ℝ := max (Real.exp (-2 * (θ₀ - 1))) 1
  have hm : 0 < m := by positivity
  have hM0 : 1 ≤ M := le_max_right _ _
  have hM : 0 ≤ M := by linarith
  have hθ' : |θ - θ₀| < 1 := by simpa [Real.dist_eq] using hθ
  have hθlo : θ₀ - 1 < θ := by rw [abs_lt] at hθ'; linarith
  have hθhi : θ < θ₀ + 1 := by rw [abs_lt] at hθ'; linarith
  have hscaleLo : m ≤ Real.exp (-2 * θ) := by
    simpa [m] using (Real.exp_le_exp.mpr (by nlinarith :
      -2 * (θ₀ + 1) ≤ -2 * θ))
  have hscaleHi : Real.exp (-2 * θ) ≤ M := by
    calc Real.exp (-2 * θ) ≤ Real.exp (-2 * (θ₀ - 1)) :=
          Real.exp_le_exp.mpr (by nlinarith)
      _ ≤ M := le_max_left _ _
  have hexp : Real.exp (-s ^ 2 * Real.exp (-2 * θ)) ≤
      Real.exp (-m * s ^ 2) := by
    apply Real.exp_le_exp.mpr
    dsimp [m]
    have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
    nlinarith
  have hfactor : |s ^ 2 * Real.exp (-2 * θ) - 1| ≤ M * s ^ 2 + 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg s, hscaleHi]
  have hlog := abs_log_le_inv_add s hs
  have hH : |H s z ω| ≤ C * (1 + 1 / s + s) := by
    calc |H s z ω| ≤ C * (1 + |Real.log s|) := hbound
      _ ≤ C * (1 + 1 / s + s) := by
        apply mul_le_mul_of_nonneg_left _ hC
        linarith [hlog]
  have hpoly : s * (M * s ^ 2 + 1) * (1 + 1 / s + s) ≤
      (M + 1) * (1 + s + s ^ 2 + s ^ 3 + s ^ 4) := by
    have hsne : s ≠ 0 := ne_of_gt hs
    have heq : s * (M * s ^ 2 + 1) * (1 + 1 / s + s) =
        M * s ^ 4 + M * s ^ 3 + (M + 1) * s ^ 2 + s + 1 := by
      field_simp
      <;> ring
    rw [heq]
    have hs0 : 0 ≤ s := hs.le
    have hterms :
        M * s ^ 4 + M * s ^ 3 + (M + 1) * s ^ 2 + s + 1 ≤
          (M + 1) * (1 + s + s ^ 2 + s ^ 3 + s ^ 4) := by
      nlinarith [sq_nonneg s, pow_nonneg hs0 3, pow_nonneg hs0 4]
    exact hterms
  rw [heatRadialIntegrandDeriv]
  simp only [abs_mul,
    abs_of_pos (by positivity : 0 < (4 : ℝ) * Real.exp (-2 * θ)),
    abs_of_pos hs, abs_of_pos (Real.exp_pos _)]
  calc
    4 * Real.exp (-2 * θ) * s * |s ^ 2 * Real.exp (-2 * θ) - 1| *
        |H s z ω| * Real.exp (-s ^ 2 * Real.exp (-2 * θ))
      ≤ 4 * M * s * (M * s ^ 2 + 1) * (C * (1 + 1 / s + s)) * Real.exp (-m * s ^ 2) := by
        gcongr
    _ ≤ (4 * C * M * (M + 1)) *
        (1 + s + s ^ 2 + s ^ 3 + s ^ 4) * Real.exp (-m * s ^ 2) := by
        have hcoef : 0 ≤ 4 * C * M := by positivity
        have hExp : 0 ≤ Real.exp (-m * s ^ 2) := (Real.exp_pos _).le
        calc 4 * M * s * (M * s ^ 2 + 1) * (C * (1 + 1 / s + s)) *
              Real.exp (-m * s ^ 2)
            = (4 * C * M) * (s * (M * s ^ 2 + 1) * (1 + 1 / s + s)) *
                Real.exp (-m * s ^ 2) := by ring
          _ ≤ (4 * C * M) * ((M + 1) * (1 + s + s ^ 2 + s ^ 3 + s ^ 4)) *
                Real.exp (-m * s ^ 2) := by gcongr
          _ = _ := by ring

private lemma heatRadialIntegrand_abs_le {Ω : Type*} [MeasurableSpace Ω]
    {H : ℝ → ℂ → Ω → ℝ} {z : ℂ} {ω : Ω} {C θ₀ θ s : ℝ}
    (hC : 0 ≤ C) (hbound : |H s z ω| ≤ C * (1 + |Real.log s|))
    (hs : 0 < s) (hθ : θ ∈ Metric.ball θ₀ 1) :
    |heatRadialIntegrand H z ω θ s| ≤
      (4 * C * max (Real.exp (-2 * (θ₀ - 1))) 1 *
        (max (Real.exp (-2 * (θ₀ - 1))) 1 + 1)) *
        (1 + s + s ^ 2 + s ^ 3 + s ^ 4) *
        Real.exp (-Real.exp (-2 * (θ₀ + 1)) * s ^ 2) := by
  let m : ℝ := Real.exp (-2 * (θ₀ + 1))
  let M : ℝ := max (Real.exp (-2 * (θ₀ - 1))) 1
  have hM : 1 ≤ M := le_max_right _ _
  have hθ' : |θ - θ₀| < 1 := by simpa [Real.dist_eq] using hθ
  have hθlo : θ₀ - 1 < θ := by rw [abs_lt] at hθ'; linarith
  have hθhi : θ < θ₀ + 1 := by rw [abs_lt] at hθ'; linarith
  have hscaleLo : m ≤ Real.exp (-2 * θ) := by
    simpa [m] using (Real.exp_le_exp.mpr (by nlinarith : -2 * (θ₀ + 1) ≤ -2 * θ))
  have hscaleHi : Real.exp (-2 * θ) ≤ M := by
    calc Real.exp (-2 * θ) ≤ Real.exp (-2 * (θ₀ - 1)) :=
          Real.exp_le_exp.mpr (by nlinarith)
      _ ≤ M := le_max_left _ _
  have hexp : Real.exp (-s ^ 2 * Real.exp (-2 * θ)) ≤ Real.exp (-m * s ^ 2) := by
    apply Real.exp_le_exp.mpr
    dsimp [m]
    nlinarith [sq_nonneg s]
  have hlog := abs_log_le_inv_add s hs
  have hH : |H s z ω| ≤ C * (1 + 1 / s + s) := by
    calc |H s z ω| ≤ C * (1 + |Real.log s|) := hbound
      _ ≤ C * (1 + 1 / s + s) := by
        apply mul_le_mul_of_nonneg_left _ hC
        linarith [hlog]
  rw [heatRadialIntegrand]
  simp only [abs_mul, abs_of_pos (by positivity : 0 < (2 : ℝ) * Real.exp (-2 * θ)),
    abs_of_pos hs, abs_of_pos (Real.exp_pos _)]
  have hpoly : s * (1 + 1 / s + s) ≤ 1 + s + s ^ 2 := by
    have hsne : s ≠ 0 := ne_of_gt hs
    field_simp
    <;> nlinarith [sq_nonneg s]
  calc
    2 * Real.exp (-2 * θ) * s * |H s z ω| * Real.exp (-s ^ 2 * Real.exp (-2 * θ))
      ≤ 2 * M * s * (C * (1 + 1 / s + s)) * Real.exp (-m * s ^ 2) := by
        gcongr
    _ ≤ (4 * C * M * (M + 1)) *
        (1 + s + s ^ 2 + s ^ 3 + s ^ 4) * Real.exp (-m * s ^ 2) := by
        have hcoef : 0 ≤ 2 * C * M := by positivity
        have hcoef' : 2 * C * M ≤ 4 * C * M * (M + 1) := by
          have hfac : 0 ≤ 2 * (M + 1) - 1 := by linarith
          nlinarith [mul_nonneg hcoef hfac]
        have hP : 0 ≤ 1 + s + s ^ 2 := by positivity
        have hs0 : 0 ≤ s := hs.le
        have hQ : 1 + s + s ^ 2 ≤ 1 + s + s ^ 2 + s ^ 3 + s ^ 4 := by
          nlinarith [pow_nonneg hs0 3, pow_nonneg hs0 4]
        have hE : 0 ≤ Real.exp (-m * s ^ 2) := (Real.exp_pos _).le
        calc 2 * M * s * (C * (1 + 1 / s + s)) * Real.exp (-m * s ^ 2)
            = (2 * C * M) * (s * (1 + 1 / s + s)) * Real.exp (-m * s ^ 2) := by ring
          _ ≤ (2 * C * M) * (1 + s + s ^ 2) * Real.exp (-m * s ^ 2) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpoly hcoef) hE
          _ ≤ (2 * C * M) * (1 + s + s ^ 2 + s ^ 3 + s ^ 4) *
              Real.exp (-m * s ^ 2) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hQ hcoef) hE
          _ ≤ (4 * C * M * (M + 1)) *
              (1 + s + s ^ 2 + s ^ 3 + s ^ 4) * Real.exp (-m * s ^ 2) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hcoef' (by positivity)) hE
          _ = _ := by ring

private lemma continuousOn_heatRadialIntegrand {Ω : Type*}
    {H : ℝ → ℂ → Ω → ℝ} {z : ℂ} {ω : Ω} {θ : ℝ}
    (hHcont : ContinuousOn (fun p : ℝ × ℂ => H p.1 p.2 ω)
      (Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ))) :
    ContinuousOn (fun s : ℝ => heatRadialIntegrand H z ω θ s) (Ioi 0) := by
  have hHr : ContinuousOn (fun s : ℝ => H s z ω) (Ioi 0) :=
    hHcont.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, mem_univ _⟩)
  have hcoef : Continuous fun s : ℝ =>
      2 * Real.exp (-2 * θ) * s * Real.exp (-s ^ 2 * Real.exp (-2 * θ)) := by fun_prop
  have heq : (fun s : ℝ => heatRadialIntegrand H z ω θ s) =
      fun s => (2 * Real.exp (-2 * θ) * s * Real.exp (-s ^ 2 * Real.exp (-2 * θ))) *
        H s z ω := by
    funext s
    simp [heatRadialIntegrand]
    ring
  rw [heq]
  exact hcoef.continuousOn.mul hHr

private lemma continuousOn_heatRadialIntegrandDeriv {Ω : Type*}
    {H : ℝ → ℂ → Ω → ℝ} {z : ℂ} {ω : Ω} {θ : ℝ}
    (hHcont : ContinuousOn (fun p : ℝ × ℂ => H p.1 p.2 ω)
      (Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ))) :
    ContinuousOn (fun s : ℝ => heatRadialIntegrandDeriv H z ω θ s) (Ioi 0) := by
  have hHr : ContinuousOn (fun s : ℝ => H s z ω) (Ioi 0) :=
    hHcont.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, mem_univ _⟩)
  have hcoef : Continuous fun s : ℝ =>
      4 * Real.exp (-2 * θ) * s * (s ^ 2 * Real.exp (-2 * θ) - 1) *
        Real.exp (-s ^ 2 * Real.exp (-2 * θ)) := by fun_prop
  have heq : (fun s : ℝ => heatRadialIntegrandDeriv H z ω θ s) =
      fun s => (4 * Real.exp (-2 * θ) * s * (s ^ 2 * Real.exp (-2 * θ) - 1) *
        Real.exp (-s ^ 2 * Real.exp (-2 * θ))) * H s z ω := by
    funext s
    simp [heatRadialIntegrandDeriv]
    ring
  rw [heq]
  exact hcoef.continuousOn.mul hHr

private lemma heatRadialIntegrandDeriv_circle_bound {Ω : Type*}
    {H : ℝ → ℂ → Ω → ℝ} {z : ℂ} {ω : Ω} {C θ s : ℝ}
    (hC : 0 ≤ C) (hbound : |H s z ω| ≤ C * (1 + |Real.log s|)) (hs : 0 < s) :
    |heatRadialIntegrandDeriv H z ω θ s| ≤ C * heatKernelLogWeight θ s := by
  have hscale : 0 < Real.exp (-2 * θ) := Real.exp_pos _
  have hExp : 0 < Real.exp (-s ^ 2 * Real.exp (-2 * θ)) := Real.exp_pos _
  have hfac : 0 ≤ |s ^ 2 * Real.exp (-2 * θ) - 1| := abs_nonneg _
  rw [heatRadialIntegrandDeriv]
  simp only [abs_mul, abs_abs, abs_of_pos (by positivity :
    0 < (4 : ℝ) * Real.exp (-2 * θ)), abs_of_pos hs, abs_of_pos hExp]
  have hcoeff : 0 ≤ 4 * Real.exp (-2 * θ) * s *
      |s ^ 2 * Real.exp (-2 * θ) - 1| * Real.exp (-s ^ 2 * Real.exp (-2 * θ)) := by
    positivity
  calc 4 * Real.exp (-2 * θ) * s * |s ^ 2 * Real.exp (-2 * θ) - 1| *
        |H s z ω| * Real.exp (-s ^ 2 * Real.exp (-2 * θ))
      = (4 * Real.exp (-2 * θ) * s *
          |s ^ 2 * Real.exp (-2 * θ) - 1| *
          Real.exp (-s ^ 2 * Real.exp (-2 * θ))) * |H s z ω| := by ring
    _ ≤ (4 * Real.exp (-2 * θ) * s *
          |s ^ 2 * Real.exp (-2 * θ) - 1| *
          Real.exp (-s ^ 2 * Real.exp (-2 * θ))) *
          (C * (1 + |Real.log s|)) :=
          mul_le_mul_of_nonneg_left hbound hcoeff
    _ = C * heatKernelLogWeight θ s := by
          unfold heatKernelLogWeight
          ring

private theorem hasDerivAt_heatRadialIntegral {Ω : Type*} [MeasurableSpace Ω]
    {H : ℝ → ℂ → Ω → ℝ} {z : ℂ} {ω : Ω} {C θ₀ : ℝ}
    (hHcont : ContinuousOn (fun p : ℝ × ℂ => H p.1 p.2 ω)
      (Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ)))
    (hC : 0 ≤ C) (hbound : ∀ s : ℝ, 0 < s →
      |H s z ω| ≤ C * (1 + |Real.log s|)) :
    Integrable (fun s : ℝ => heatRadialIntegrandDeriv H z ω θ₀ s)
        (volume.restrict (Ioi (0 : ℝ))) ∧
      HasDerivAt (fun θ => ∫ s in Ioi (0 : ℝ), heatRadialIntegrand H z ω θ s)
        (∫ s in Ioi (0 : ℝ), heatRadialIntegrandDeriv H z ω θ₀ s) θ₀ := by
  let m : ℝ := Real.exp (-2 * (θ₀ + 1))
  let M : ℝ := max (Real.exp (-2 * (θ₀ - 1))) 1
  let B : ℝ → ℝ := fun s =>
    (4 * C * M * (M + 1)) * (1 + s + s ^ 2 + s ^ 3 + s ^ 4) *
      Real.exp (-m * s ^ 2)
  have hm : 0 < m := by positivity
  have hpolyInt : IntegrableOn
      (fun s : ℝ => (1 + s + s ^ 2 + s ^ 3 + s ^ 4) * Real.exp (-m * s ^ 2))
      (Ioi 0) := integrableOn_polyGaussian hm
  have hBint : Integrable B (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [B, mul_assoc] using hpolyInt.const_mul (4 * C * M * (M + 1))
  have hFcont : ∀ θ : ℝ, ContinuousOn
      (fun s : ℝ => heatRadialIntegrand H z ω θ s) (Ioi 0) :=
    fun θ => continuousOn_heatRadialIntegrand hHcont
  have hFprimeCont : ContinuousOn
      (fun s : ℝ => heatRadialIntegrandDeriv H z ω θ₀ s) (Ioi 0) :=
    continuousOn_heatRadialIntegrandDeriv hHcont
  have hFmeas : ∀ᶠ θ in 𝓝 θ₀,
      AEStronglyMeasurable (fun s : ℝ => heatRadialIntegrand H z ω θ s)
        (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards with θ
    exact (hFcont θ).aestronglyMeasurable measurableSet_Ioi
  have hFint : Integrable (fun s : ℝ => heatRadialIntegrand H z ω θ₀ s)
      (volume.restrict (Ioi (0 : ℝ))) := by
    apply Integrable.mono' hBint
      ((hFcont θ₀).aestronglyMeasurable measurableSet_Ioi)
    apply (ae_restrict_iff' measurableSet_Ioi).2
    filter_upwards with s hs
    have hs : 0 < s := hs
    rw [Real.norm_eq_abs]
    exact heatRadialIntegrand_abs_le hC (hbound s hs) hs
      (Metric.mem_ball_self one_pos)
  have hFprimeMeas : AEStronglyMeasurable
      (fun s : ℝ => heatRadialIntegrandDeriv H z ω θ₀ s)
      (volume.restrict (Ioi (0 : ℝ))) :=
    hFprimeCont.aestronglyMeasurable measurableSet_Ioi
  have hDerivBound : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ θ ∈ Metric.ball θ₀ 1,
        ‖heatRadialIntegrandDeriv H z ω θ s‖ ≤ B s := by
    apply (ae_restrict_iff' measurableSet_Ioi).2
    filter_upwards with s hs
    have hs : 0 < s := hs
    intro θ hθ
    rw [Real.norm_eq_abs]
    exact heatRadialIntegrandDeriv_abs_le hC (hbound s hs) hs hθ
  have hDiff : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ θ ∈ Metric.ball θ₀ 1,
        HasDerivAt (fun t => heatRadialIntegrand H z ω t s)
          (heatRadialIntegrandDeriv H z ω θ s) θ := by
    exact ae_of_all _ fun s θ hθ => hasDerivAt_heatRadialIntegrand H z ω s θ
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (s := Metric.ball θ₀ 1) (x₀ := θ₀)
    (F := fun θ s => heatRadialIntegrand H z ω θ s)
    (F' := fun θ s => heatRadialIntegrandDeriv H z ω θ s)
    (bound := B) (Metric.ball_mem_nhds θ₀ one_pos) hFmeas hFint hFprimeMeas
    hDerivBound hBint hDiff
  exact hresult

private theorem abs_heatRadialIntegral_deriv_le {Ω : Type*} [MeasurableSpace Ω]
    {H : ℝ → ℂ → Ω → ℝ} {z : ℂ} {ω : Ω} {C θ : ℝ}
    (hHcont : ContinuousOn (fun p : ℝ × ℂ => H p.1 p.2 ω)
      (Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ)))
    (hC : 0 ≤ C) (hbound : ∀ s : ℝ, 0 < s →
      |H s z ω| ≤ C * (1 + |Real.log s|)) :
    |∫ s in Ioi (0 : ℝ), heatRadialIntegrandDeriv H z ω θ s| ≤
      C * (8 * (2 + |θ|) * heatKernelLogPolyIntegral) := by
  have hD := hasDerivAt_heatRadialIntegral hHcont hC hbound (θ₀ := θ)
  have hweight := heatKernelLogWeight_integrable θ
  have hmajor : Integrable (fun s : ℝ => C * heatKernelLogWeight θ s)
      (volume.restrict (Ioi (0 : ℝ))) := by
    simpa only [smul_eq_mul] using hweight.const_mul C
  have hpoint : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖heatRadialIntegrandDeriv H z ω θ s‖ ≤ C * heatKernelLogWeight θ s := by
    apply (ae_restrict_iff' measurableSet_Ioi).2
    filter_upwards with s hs
    have hs : 0 < s := hs
    rw [Real.norm_eq_abs]
    exact heatRadialIntegrandDeriv_circle_bound hC (hbound s hs) hs
  have hnorm := norm_integral_le_of_norm_le hmajor hpoint
  rw [Real.norm_eq_abs] at hnorm
  calc |∫ s in Ioi (0 : ℝ), heatRadialIntegrandDeriv H z ω θ s|
      ≤ ∫ s in Ioi (0 : ℝ), C * heatKernelLogWeight θ s := hnorm
    _ = C * ∫ s in Ioi (0 : ℝ), heatKernelLogWeight θ s := by
      rw [integral_const_mul]
    _ ≤ C * (8 * (2 + |θ|) * heatKernelLogPolyIntegral) :=
      mul_le_mul_of_nonneg_left (heatKernelLogWeight_integral_le θ) hC
    _ = C * (8 * (2 + |θ|) * heatKernelLogPolyIntegral) := rfl

private theorem heatRadialIntegral_log_lipschitz {Ω : Type*} [MeasurableSpace Ω]
    {H : ℝ → ℂ → Ω → ℝ} {z : ℂ} {ω : Ω} {C θ₁ θ₂ : ℝ}
    (hHcont : ContinuousOn (fun p : ℝ × ℂ => H p.1 p.2 ω)
      (Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ)))
    (hC : 0 ≤ C) (hbound : ∀ s : ℝ, 0 < s →
      |H s z ω| ≤ C * (1 + |Real.log s|)) :
    |(∫ s in Ioi (0 : ℝ), heatRadialIntegrand H z ω θ₁ s) -
      (∫ s in Ioi (0 : ℝ), heatRadialIntegrand H z ω θ₂ s)| ≤
      (8 * heatKernelLogPolyIntegral) * C * |θ₁ - θ₂| *
        (2 + max |θ₁| |θ₂|) := by
  by_cases hθ : θ₁ = θ₂
  · simp [hθ]
  · let a := min θ₁ θ₂
    let b := max θ₁ θ₂
    have hab : a < b := by
      rcases le_total θ₁ θ₂ with h | h
      · simpa [a, b, min_eq_left h, max_eq_right h] using
          (lt_of_le_of_ne h hθ)
      · simpa [a, b, min_eq_right h, max_eq_left h] using
          (lt_of_le_of_ne h (Ne.symm hθ))
    let F : ℝ → ℝ := fun t => ∫ s in Ioi (0 : ℝ), heatRadialIntegrand H z ω t s
    have hFderiv : ∀ t : ℝ, HasDerivAt F
        (∫ s in Ioi (0 : ℝ), heatRadialIntegrandDeriv H z ω t s) t := by
      intro t
      exact (hasDerivAt_heatRadialIntegral hHcont hC hbound (θ₀ := t)).2
    have hcont : ContinuousOn F (Icc a b) := by
      intro t ht
      exact (hFderiv t).continuousAt.continuousWithinAt
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope F
      (fun t => ∫ s in Ioi (0 : ℝ), heatRadialIntegrandDeriv H z ω t s)
      hab hcont (fun t ht => hFderiv t)
    have hderivBound : ∀ t : ℝ,
        |∫ s in Ioi (0 : ℝ), heatRadialIntegrandDeriv H z ω t s| ≤
          C * (8 * (2 + |t|) * heatKernelLogPolyIntegral) := by
      intro t
      exact abs_heatRadialIntegral_deriv_le (θ := t) hHcont hC hbound
    have habsθ : |c| ≤ max |θ₁| |θ₂| := by
      have hcab : a < c ∧ c < b := hc
      have habsAB : |c| ≤ max |a| |b| := by
        apply abs_le.mpr
        constructor
        · calc -max |a| |b| ≤ -|a| := neg_le_neg (le_max_left _ _)
            _ ≤ a := neg_abs_le a
            _ ≤ c := hcab.1.le
        · calc c ≤ b := hcab.2.le
            _ ≤ |b| := le_abs_self b
            _ ≤ max |a| |b| := le_max_right _ _
      rcases le_total θ₁ θ₂ with h12 | h21
      · simpa [a, b, min_eq_left h12, max_eq_right h12, or_comm] using habsAB
      · simpa [a, b, min_eq_right h21, max_eq_left h21, or_comm] using habsAB
    have hdiffθ : |θ₁ - θ₂| = b - a := by
      dsimp [a, b]
      rcases le_total θ₁ θ₂ with h12 | h21
      · rw [max_eq_right h12, min_eq_left h12, abs_of_nonpos (by linarith)]
        ring
      · rw [max_eq_left h21, min_eq_right h21, abs_of_nonneg (by linarith)]
    have hslope' : |F b - F a| ≤
        (C * (8 * (2 + |c|) * heatKernelLogPolyIntegral)) * (b - a) := by
      have hratio : |(F b - F a) / (b - a)| ≤
          C * (8 * (2 + |c|) * heatKernelLogPolyIntegral) := by
        rw [← hslope]
        exact hderivBound c
      have hratio' : |F b - F a| / (b - a) ≤
          C * (8 * (2 + |c|) * heatKernelLogPolyIntegral) := by
        simpa [abs_div, abs_of_pos (sub_pos.mpr hab)] using hratio
      exact (div_le_iff₀ (sub_pos.mpr hab)).1 hratio'
    have hI0 : 0 ≤ heatKernelLogPolyIntegral := by
      unfold heatKernelLogPolyIntegral
      apply setIntegral_nonneg measurableSet_Ioi
      intro u hu
      have hu0 : 0 ≤ u := (mem_Ioi.mp hu).le
      positivity
    have hbound' : |F b - F a| ≤
        (C * (8 * (2 + max |θ₁| |θ₂|) * heatKernelLogPolyIntegral)) * (b - a) := by
      apply hslope'.trans
      apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr hab.le)
      apply mul_le_mul_of_nonneg_left _ hC
      apply mul_le_mul_of_nonneg_right _ hI0
      exact mul_le_mul_of_nonneg_left (by linarith [habsθ])
        (by norm_num : (0 : ℝ) ≤ 8)
    have hswap : |F θ₁ - F θ₂| = |F b - F a| := by
      rcases le_total θ₁ θ₂ with h12 | h21
      · simpa [a, b, max_eq_right h12, min_eq_left h12, abs_sub_comm]
      · simpa [a, b, max_eq_left h21, min_eq_right h21, abs_sub_comm]
    rw [show (∫ s in Ioi (0 : ℝ), heatRadialIntegrand H z ω θ₁ s) = F θ₁ by rfl,
      show (∫ s in Ioi (0 : ℝ), heatRadialIntegrand H z ω θ₂ s) = F θ₂ by rfl,
      hswap, hdiffθ]
    convert hbound' using 1 <;> ring

private theorem exp_neg_two_log {δ : ℝ} (hδ : 0 < δ) :
    Real.exp (-2 * Real.log δ) = 1 / δ ^ 2 := by
  have hsum : Real.exp (Real.log δ + Real.log δ) = δ ^ 2 := by
    calc Real.exp (Real.log δ + Real.log δ)
        = Real.exp (Real.log δ) * Real.exp (Real.log δ) := Real.exp_add _ _
      _ = δ * δ := by rw [Real.exp_log hδ]
      _ = δ ^ 2 := by ring
  calc Real.exp (-2 * Real.log δ)
      = Real.exp (-(Real.log δ + Real.log δ)) := by congr 1 <;> ring
    _ = (Real.exp (Real.log δ + Real.log δ))⁻¹ := Real.exp_neg _
    _ = (δ ^ 2)⁻¹ := by rw [hsum]
    _ = 1 / δ ^ 2 := by rw [one_div]

private theorem polarInt_one_eq_heatRadialIntegral {Ω : Type*}
    (H : ℝ → ℂ → Ω → ℝ) (z : ℂ) (ω : Ω) {δ : ℝ} (hδ : 0 < δ) :
    SupercriticalLQGUniqueness.B2.Polylog.polarInt (fun _ _ => 1)
        (fun s z => H s z ω) (δ, z) =
      ∫ s in Ioi (0 : ℝ), heatRadialIntegrand H z ω (Real.log δ) s := by
  have hexp := exp_neg_two_log hδ
  have hpoint : ∀ s : ℝ,
      heatRadialIntegrand H z ω (Real.log δ) s =
        (2 / δ ^ 2) * (s * H s z ω * Real.exp (-s ^ 2 / δ ^ 2)) := by
    intro s
    unfold heatRadialIntegrand
    rw [hexp]
    have harg : -s ^ 2 * (1 / δ ^ 2) = -s ^ 2 / δ ^ 2 := by ring
    rw [harg]
    ring
  have hint : ∫ s in Ioi (0 : ℝ), heatRadialIntegrand H z ω (Real.log δ) s =
      (2 / δ ^ 2) * ∫ s in Ioi (0 : ℝ),
        s * H s z ω * Real.exp (-s ^ 2 / δ ^ 2) := by
    calc ∫ s in Ioi (0 : ℝ), heatRadialIntegrand H z ω (Real.log δ) s
        = ∫ s in Ioi (0 : ℝ),
            (2 / δ ^ 2) * (s * H s z ω * Real.exp (-s ^ 2 / δ ^ 2)) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro s hs
              exact hpoint s
      _ = _ := by rw [integral_const_mul]
  rw [SupercriticalLQGUniqueness.B2.Polylog.polarInt]
  simpa using hint.symm

private theorem rpow_eq_exp_mul_log {x y : ℝ} (hx : 0 < x) :
    Real.rpow x y = Real.exp (y * Real.log x) := by
  calc Real.rpow x y = Real.exp (Real.log x * y) := Real.rpow_def_of_pos hx y
    _ = Real.exp (y * Real.log x) := by congr 1 <;> ring

/-- The deterministic bound in the log-window estimate tends to zero. -/
theorem tendsto_logWindowRate_zero (C a : ℝ) :
    Tendsto (fun n : ℕ =>
      2 * C * a * (2 + a * Real.log ((n : ℝ) + 1)) / (n : ℝ))
      atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hnPlus : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    hn.atTop_add (tendsto_const_nhds)
  have hlogOverX : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero)
  have hlogDiv' : Tendsto (fun n : ℕ =>
      Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    exact hlogOverX.comp hnPlus
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hn
  have hfactor : Tendsto (fun n : ℕ => 1 + (n : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add hinv)
  have hlogDivNat : Tendsto (fun n : ℕ =>
      Real.log ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 0) := by
    have hEq : (fun n : ℕ => Real.log ((n : ℝ) + 1) / (n : ℝ)) =
        fun n : ℕ => (Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1)) *
          (1 + (n : ℝ)⁻¹) := by
      funext n
      by_cases hn0 : (n : ℝ) = 0
      · have hn0' : n = 0 := by exact_mod_cast hn0
        subst n
        simp
      · field_simp [hn0]
        <;> ring
    rw [hEq]
    simpa using hlogDiv'.mul hfactor
  have hrateParts : Tendsto (fun n : ℕ =>
      (4 * C * a) * (n : ℝ)⁻¹ +
        (2 * C * a ^ 2) * (Real.log ((n : ℝ) + 1) / (n : ℝ)))
      atTop (𝓝 0) := by
    simpa using (hinv.const_mul (4 * C * a)).add
      (hlogDivNat.const_mul (2 * C * a ^ 2))
  have hrateEq : (fun n : ℕ =>
      2 * C * a * (2 + a * Real.log ((n : ℝ) + 1)) / (n : ℝ)) =
        fun n : ℕ => (4 * C * a) * (n : ℝ)⁻¹ +
          (2 * C * a ^ 2) * (Real.log ((n : ℝ) + 1) / (n : ℝ)) := by
    funext n
    by_cases hn0 : (n : ℝ) = 0
    · have hn0' : n = 0 := by exact_mod_cast hn0
      subst n
      simp
    · field_simp [hn0]
      <;> ring
  rw [hrateEq]
  exact hrateParts

/-- The compact-uniform log-window estimate (2.2), with the circle-average constant enlarged
by the universal Gaussian kernel integral.  The quantified pointwise estimate is simultaneous
in all scales, window exponents, and points of the compact. -/
theorem ae_jointHeatVersion_logWindow_estimate {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC)
    (hh : SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, SupercriticalLQGUniqueness.IsHeatSmoothing P h ε (X ε))
    (hXc : ∀ᵐ ω ∂P,
      Continuous fun p : Set.Ioi (0 : ℝ) × ℂ => X p.1 ω p.2)
    (K : Set ℂ) (hK : IsCompact K) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a →
      ∀ n : ℕ, 1 ≤ n →
      ∀ ε δ : Set.Ioi (0 : ℝ),
        (ε : ℝ) ∈ Icc (Real.rpow ((n : ℝ) + 1) (-a)) (Real.rpow (n : ℝ) (-a)) →
        (δ : ℝ) ∈ Icc (Real.rpow ((n : ℝ) + 1) (-a)) (Real.rpow (n : ℝ) (-a)) →
        ∀ z ∈ K,
          |X ε ω z - X δ ω z| ≤
            2 * C * a * (2 + a * Real.log ((n : ℝ) + 1)) / n := by
  classical
  obtain ⟨Y, hYpath, hYc⟩ :=
    SupercriticalLFPPAS.Implementation.exists_jointHeatVersion_pathwise P h hh.1
  have hYs : ∀ ε, SupercriticalLQGUniqueness.IsHeatSmoothing P h ε (Y ε) := by
    intro ε z
    filter_upwards [hYpath] with ω hω
    exact hω ε z
  have hXY := SupercriticalLFPPAS.ae_eq_of_jointHeatVersions hX hYs hXc hYc
  have hYM : ∀ᵐ ω ∂P, ∀ ε : Set.Ioi (0 : ℝ), ∀ z : ℂ,
      Y ε ω z = heatMollify (ε : ℝ) (h ω) z := by
    have hJ := LQGMetric.DFGPS.lem2_1HeatJoint P h hh.1
    filter_upwards [hYpath, hJ] with ω hω hωJ
    intro ε z
    obtain ⟨L, hL⟩ := hωJ.1 (ε : ℝ) ε.2 z
    have hlim : Tendsto
        (fun n : ℕ => h ω (SupercriticalLQGUniqueness.positiveHeatTrunc
          ⟨(ε : ℝ) ^ 2 / 2, Set.mem_Ioi.mpr
            (div_pos (pow_pos ε.2 2) two_pos)⟩ z n)) atTop (𝓝 L) := by
      unfold SupercriticalLQGUniqueness.positiveHeatTrunc
      exact hL
    have huniq := tendsto_nhds_unique (hω ε z) hlim
    have hLmoll : heatMollify (ε : ℝ) (h ω) z = L := hL.limUnder_eq
    exact huniq.trans hLmoll.symm
  have hXM : ∀ᵐ ω ∂P, ∀ ε : Set.Ioi (0 : ℝ), ∀ z : ℂ,
      X ε ω z = heatMollify (ε : ℝ) (h ω) z := by
    filter_upwards [hXY, hYM] with ω hXYω hYMω
    intro ε z
    exact (congrArg (fun f : C(ℂ, ℝ) => f z) (hXYω ε)).trans (hYMω ε z)
  obtain ⟨H, hH, hBoundAE⟩ :=
    exists_circleAverage_log_bound P h hh K hK
  have hPolarAE := ae_heatMollify_eq_polarInt_forVersion P h hh H hH
  -- The compact circle-average bound and both radial/version identities hold together.
  filter_upwards [hBoundAE, hPolarAE, hXM] with ω hB hP hXω
  obtain ⟨C₀, hC₀, hB₀⟩ := hB
  have hI0 : 0 ≤ heatKernelLogPolyIntegral := by
    unfold heatKernelLogPolyIntegral
    apply setIntegral_nonneg measurableSet_Ioi
    intro u hu
    have hu0 : 0 ≤ u := (mem_Ioi.mp hu).le
    positivity
  let C := 4 * heatKernelLogPolyIntegral * C₀
  refine ⟨C, mul_nonneg (mul_nonneg (by norm_num) hI0) hC₀, ?_⟩
  intro a ha n hn ε δ hε hδ z hz
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  have hn1 : 0 < (n : ℝ) + 1 := by linarith
  have hε0 : 0 < (ε : ℝ) := ε.2
  have hδ0 : 0 < (δ : ℝ) := δ.2
  have hlogLo : -a * Real.log ((n : ℝ) + 1) ≤ Real.log ε := by
    have hpow : Real.rpow ((n : ℝ) + 1) (-a) =
        Real.exp (-a * Real.log ((n : ℝ) + 1)) := by
      exact rpow_eq_exp_mul_log hn1
    have hlo := (mem_Icc.mp hε).1
    rw [hpow] at hlo
    calc -a * Real.log ((n : ℝ) + 1)
        = Real.log (Real.exp (-a * Real.log ((n : ℝ) + 1))) := (Real.log_exp _).symm
      _ ≤ Real.log ε := Real.log_le_log (Real.exp_pos _) hlo
  have hlogHi : Real.log ε ≤ -a * Real.log (n : ℝ) := by
    have hpow : Real.rpow (n : ℝ) (-a) =
        Real.exp (-a * Real.log (n : ℝ)) := by
      exact rpow_eq_exp_mul_log hn0
    have hle := (mem_Icc.mp hε).2
    rw [hpow] at hle
    calc Real.log ε ≤ Real.log (Real.exp (-a * Real.log (n : ℝ))) :=
        Real.log_le_log hε0 hle
      _ = -a * Real.log (n : ℝ) := Real.log_exp _
  have hδlogLo : -a * Real.log ((n : ℝ) + 1) ≤ Real.log δ := by
    have hpow : Real.rpow ((n : ℝ) + 1) (-a) =
        Real.exp (-a * Real.log ((n : ℝ) + 1)) := by
      exact rpow_eq_exp_mul_log hn1
    have hlo := (mem_Icc.mp hδ).1
    rw [hpow] at hlo
    calc -a * Real.log ((n : ℝ) + 1)
        = Real.log (Real.exp (-a * Real.log ((n : ℝ) + 1))) := (Real.log_exp _).symm
      _ ≤ Real.log δ := Real.log_le_log (Real.exp_pos _) hlo
  have hδlogHi : Real.log δ ≤ -a * Real.log (n : ℝ) := by
    have hpow : Real.rpow (n : ℝ) (-a) =
        Real.exp (-a * Real.log (n : ℝ)) := by
      exact rpow_eq_exp_mul_log hn0
    have hle := (mem_Icc.mp hδ).2
    rw [hpow] at hle
    calc Real.log δ ≤ Real.log (Real.exp (-a * Real.log (n : ℝ))) :=
        Real.log_le_log hδ0 hle
      _ = -a * Real.log (n : ℝ) := Real.log_exp _
  have hlogN : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hlogN1 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hθboundε : |Real.log ε| ≤ a * Real.log ((n : ℝ) + 1) := by
    apply abs_le.mpr
    constructor
    · simpa [neg_mul] using hlogLo
    · calc Real.log ε ≤ -a * Real.log (n : ℝ) := hlogHi
        _ ≤ 0 := by nlinarith [mul_nonneg ha.le hlogN]
        _ ≤ a * Real.log ((n : ℝ) + 1) := mul_nonneg ha.le hlogN1
  have hθboundδ : |Real.log δ| ≤ a * Real.log ((n : ℝ) + 1) := by
    apply abs_le.mpr
    constructor
    · simpa [neg_mul] using hδlogLo
    · calc Real.log δ ≤ -a * Real.log (n : ℝ) := hδlogHi
        _ ≤ 0 := by nlinarith [mul_nonneg ha.le hlogN]
        _ ≤ a * Real.log ((n : ℝ) + 1) := mul_nonneg ha.le hlogN1
  have hlogdiff : Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) =
      Real.log (1 + 1 / (n : ℝ)) := by
    rw [← Real.log_div (ne_of_gt hn1) (ne_of_gt hn0)]
    congr 1
    field_simp
  have hlogstep : Real.log (1 + 1 / (n : ℝ)) ≤ 1 / (n : ℝ) := by
    have ht := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / (n : ℝ))
    nlinarith
  have hwidth : |Real.log ε - Real.log δ| ≤ a / (n : ℝ) := by
    have hdiff : |Real.log ε - Real.log δ| ≤
        a * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := by
      rw [abs_le]
      constructor <;> nlinarith [hlogLo, hlogHi, hδlogLo, hδlogHi]
    rw [hlogdiff] at hdiff
    calc |Real.log ε - Real.log δ|
        ≤ a * Real.log (1 + 1 / (n : ℝ)) := hdiff
      _ ≤ a * (1 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogstep ha.le
      _ = a / (n : ℝ) := by ring
  have hHcont : ContinuousOn (fun p : ℝ × ℂ => H p.1 p.2 ω)
      (Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ)) := hH.cont ω
  have hheat (η : ℝ) (hη : 0 < η) :
      heatMollify η (h ω) z =
        ∫ s in Ioi (0 : ℝ), heatRadialIntegrand H z ω (Real.log η) s := by
    calc heatMollify η (h ω) z =
        SupercriticalLQGUniqueness.B2.Polylog.polarInt (fun _ _ => 1)
          (fun s z => H s z ω) (η, z) := hP η hη z
      _ = ∫ s in Ioi (0 : ℝ), heatRadialIntegrand H z ω (Real.log η) s :=
        polarInt_one_eq_heatRadialIntegral H z ω hη
  have hraw := heatRadialIntegral_log_lipschitz hHcont hC₀
    (fun s hs => hB₀ s hs z hz)
    (θ₁ := Real.log (ε : ℝ)) (θ₂ := Real.log (δ : ℝ))
  have hraw' : |heatMollify (ε : ℝ) (h ω) z -
      heatMollify (δ : ℝ) (h ω) z| ≤
      (8 * heatKernelLogPolyIntegral) * C₀ *
        |Real.log (ε : ℝ) - Real.log (δ : ℝ)| *
        (2 + max |Real.log (ε : ℝ)| |Real.log (δ : ℝ)|) := by
    simpa [hheat (ε : ℝ) hε0, hheat (δ : ℝ) hδ0] using hraw
  have hK0 : 0 ≤ 8 * heatKernelLogPolyIntegral := by positivity
  have hmax : max |Real.log ε| |Real.log δ| ≤
      a * Real.log ((n : ℝ) + 1) := max_le hθboundε hθboundδ
  have hfac : 0 ≤ 2 + a * Real.log ((n : ℝ) + 1) := by positivity
  have hraw'' : |heatMollify ε (h ω) z - heatMollify δ (h ω) z| ≤
      (8 * heatKernelLogPolyIntegral) * C₀ * (a / (n : ℝ)) *
        (2 + a * Real.log ((n : ℝ) + 1)) := by
    calc _ ≤ (8 * heatKernelLogPolyIntegral) * C₀ *
          |Real.log ε - Real.log δ| *
          (2 + max |Real.log ε| |Real.log δ|) := hraw'
      _ ≤ (8 * heatKernelLogPolyIntegral) * C₀ * (a / (n : ℝ)) *
          (2 + a * Real.log ((n : ℝ) + 1)) := by
        gcongr
  have hXvalues := hXω ε z
  have hXvalues' := hXω δ z
  rw [hXvalues, hXvalues']
  calc |heatMollify (↑ε) (h ω) z - heatMollify (↑δ) (h ω) z|
      ≤ (8 * heatKernelLogPolyIntegral) * C₀ * (a / (n : ℝ)) *
          (2 + a * Real.log ((n : ℝ) + 1)) := hraw''
    _ = 2 * C * a * (2 + a * Real.log ((n : ℝ) + 1)) / n := by
      dsimp [C]
      ring

end SupercriticalLFPPAS.Field
