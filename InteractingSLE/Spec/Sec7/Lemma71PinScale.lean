/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71FixedChart

/-!
# The canonical wall-pair chart with the scale fixed at the base point

Packet PROVE-LEMMA71S. Specification §7.1, p. 222: "the scale factor can be determined by an arbitrary rule".
`Lemma71F.Lemma71PocketPinStatement` fixes the scale by `|ψ(b)| = 1` at a base point `b` of the pocket. The canonical
wall-pair chart of PROVE-LEMMA71K (`Lemma71K.IsWallPairChart`) is normalized only at the two marked points (`0` and
`∞`); every clause of `IsWallPairChart` is invariant under a positive dilation of the chart. This file rescales it so
that `|ψ(e (Np x))| = 1` at its base point `e (Np x)`:

* `wallScale`, `scaledChart` (`cw x` followed by the dilation by `wallScale x = |cw x (e (Np x))|⁻¹`);
* **`isWallPairChart_scaled`**: the rescaled chart is again a canonical wall-pair chart;
* **`norm_scaledChart_base`**: `|scaledChart x (e (Np x))| = 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71S

open QuantumZipper (H)
open SupercriticalConformalCovariance (IsConformalBijection)
open Lemma71K

/-- The scale `|cw x (e (Np x))|⁻¹` that makes the chart have modulus one at the base point. -/
def wallScale (e : ℕ → ℂ) (Np : WallPair → ℕ) (cw : WallPair → Chart) (x : WallPair) : ℝ :=
  ‖(cw x).1 (e (Np x))‖⁻¹

/-- The wall-pair chart followed by the dilation by `wallScale`. -/
def scaledChart (e : ℕ → ℂ) (Np : WallPair → ℕ) (cw : WallPair → Chart) (x : WallPair) : Chart :=
  (cw x).trans (Chart.dilation (wallScale e Np cw x))

variable {e : ℕ → ℂ} {Cw : WallPair → Set ℂ} {Np : WallPair → ℕ} {Nx Ny : ℕ → WallPair → ℕ}
  {cw : WallPair → Chart}

theorem scaledChart_fst (x : WallPair) (z : ℂ) :
    (scaledChart e Np cw x).1 z = (wallScale e Np cw x : ℂ) * (cw x).1 z := rfl

theorem scaledChart_lift (x : WallPair) (z : ℂ) : (scaledChart e Np cw x).2.2 z = (cw x).2.2 z := by
  show 0 + (cw x).2.2 z = (cw x).2.2 z
  rw [zero_add]

/-- A positive multiple of a conformal bijection onto `ℍ` is a conformal bijection onto `ℍ`. -/
theorem isConformalBijection_const_mul {f : ℂ → ℂ} {U : Set ℂ} (hf : IsConformalBijection f U H) {r : ℝ}
    (hr : 0 < r) : IsConformalBijection (fun z => (r : ℂ) * f z) U H := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  obtain ⟨hd, hmaps, hinj, hsurj⟩ := hf
  refine ⟨hd.const_mul _, fun z hz => Chart.dilation_mem_H hr (hmaps hz), fun z hz w hw hzw =>
    hinj hz hw (mul_left_cancel₀ hr0 hzw), fun w hw => ?_⟩
  obtain ⟨z, hz, hzw⟩ := hsurj (Chart.div_mem_H hr hw)
  refine ⟨z, hz, ?_⟩
  show (r : ℂ) * f z = w
  rw [hzw]
  field_simp

theorem wallScale_pos (hW : IsWallPairChart e Cw Np Nx Ny cw) (x : WallPair) : 0 < wallScale e Np cw x := by
  obtain ⟨-, -, -, -, -, -, hNpC, -, -, -, -, -, hbij, -⟩ := hW
  have hH : (cw x).1 (e (Np x)) ∈ H := (hbij x).2.1 (hNpC x)
  have hne : (cw x).1 (e (Np x)) ≠ 0 := fun h0 => by
    have h1 : (0 : ℝ) < ((cw x).1 (e (Np x))).im := hH
    rw [h0, Complex.zero_im] at h1
    exact lt_irrefl _ h1
  exact inv_pos.2 (norm_pos_iff.2 hne)

theorem measurable_wallScale (hW : IsWallPairChart e Cw Np Nx Ny cw) : Measurable (wallScale e Np cw) := by
  obtain ⟨-, hNp, -, -, -, -, hNpC, -, -, -, -, hdom, -, hfm, -⟩ := hW
  have h := Lemma71E.measurable_at_seq (C := fun x => ((cw x).dom : Set ℂ)) (f := fun x z => (cw x).1 z) hNp
    (fun x => by rw [hdom x]; exact hNpC x) hfm
  exact (h.norm).inv

/-- **The rescaled chart has modulus one at the base point.** -/
theorem norm_scaledChart_base (hW : IsWallPairChart e Cw Np Nx Ny cw) (x : WallPair) :
    ‖(scaledChart e Np cw x).1 (e (Np x))‖ = 1 := by
  have hr := wallScale_pos hW x
  have hne : ‖(cw x).1 (e (Np x))‖ ≠ 0 := by
    have : 0 < ‖(cw x).1 (e (Np x))‖⁻¹ := hr
    exact (inv_pos.1 this).ne'
  rw [scaledChart_fst, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, wallScale,
    inv_mul_cancel₀ hne]

/-- **The rescaled canonical wall-pair chart is again a canonical wall-pair chart** (every clause of
`IsWallPairChart` is invariant under a positive dilation of the chart). -/
theorem isWallPairChart_scaled (hW : IsWallPairChart e Cw Np Nx Ny cw) :
    IsWallPairChart e Cw Np Nx Ny (scaledChart e Np cw) := by
  have hr := wallScale_pos hW
  have hrm := measurable_wallScale hW
  obtain ⟨he, hNp, hNx, hNy, hC, hCm, hNpC, hNxC, hNyC, hbet, hconf, hdom, hbij, hfm, hlm, hlc, hL, hnorm, huniq,
    hmark⟩ := hW
  have hconf' : ∀ x, (scaledChart e Np cw x).IsConformal := fun x =>
    (hconf x).trans (Chart.isConformal_dilation (hr x))
  have hdom' : ∀ x, ((scaledChart e Np cw x).dom : Set ℂ) = Cw x := fun x => by
    rw [(hconf' x).coe_dom, scaledChart, Chart.trans_image, Chart.dilation_image_H (hr x), ← (hconf x).coe_dom,
      hdom x]
  have hdomeq : ∀ x, ((scaledChart e Np cw x).dom : Set ℂ) = (cw x).dom := fun x => (hdom' x).trans (hdom x).symm
  have hset : ∀ z, {x | z ∈ (scaledChart e Np cw x).dom} = {x | z ∈ (cw x).dom} := fun z => by
    ext x
    show z ∈ ((scaledChart e Np cw x).dom : Set ℂ) ↔ z ∈ ((cw x).dom : Set ℂ)
    rw [hdomeq x]
  refine ⟨he, hNp, hNx, hNy, hC, hCm, hNpC, hNxC, hNyC, hbet, hconf', hdom', fun x => ?_, fun z => ?_, fun z => ?_,
    fun x => ?_, fun x => ?_, fun x => ?_, fun x ψ₁ hψ₁ h0 hinf => ?_, hmark⟩
  · exact isConformalBijection_const_mul (hbij x) (hr x)
  · have e1 : ({x | z ∈ (scaledChart e Np cw x).dom}.indicator fun x => (scaledChart e Np cw x).1 z) =
        fun x => (wallScale e Np cw x : ℂ) * ({x | z ∈ (cw x).dom}.indicator fun x => (cw x).1 z) x := by
      funext x
      rw [hset z]
      by_cases hx : x ∈ {x | z ∈ (cw x).dom}
      · rw [indicator_of_mem hx, indicator_of_mem hx, scaledChart_fst]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]
    rw [e1]
    exact (Complex.measurable_ofReal.comp hrm).mul (hfm z)
  · have e1 : ({x | z ∈ (scaledChart e Np cw x).dom}.indicator fun x => (scaledChart e Np cw x).2.2 z) =
        {x | z ∈ (cw x).dom}.indicator fun x => (cw x).2.2 z := by
      rw [hset z]
      exact indicator_congr fun x _ => scaledChart_lift x z
    rw [e1]
    exact hlm z
  · rw [hdomeq x]
    exact (hlc x).congr fun z _ => scaledChart_lift x z
  · obtain ⟨L, hLd, hLe⟩ := hL x
    have hCo : IsOpen (Cw x) := (hC x).1
    refine ⟨fun z => L z + ((Real.log (wallScale e Np cw x) : ℝ) : ℂ), ⟨hLd.1.add_const _, fun z hz => ?_⟩,
      fun z hz => ?_⟩
    · have hd : DifferentiableAt ℂ (cw x).1 z := (hbij x).1.differentiableAt (hCo.mem_nhds hz)
      have hfun : (scaledChart e Np cw x).1 = fun z => (wallScale e Np cw x : ℂ) * (cw x).1 z :=
        funext fun z => scaledChart_fst x z
      rw [hfun, deriv_const_mul _ hd, Complex.exp_add, hLd.2 z hz, ← Complex.ofReal_exp,
        Real.exp_log (hr x), mul_comm]
    · rw [scaledChart_lift, hLe z hz, Complex.add_im, Complex.ofReal_im, add_zero]
  · obtain ⟨h1, h2⟩ := hnorm x
    refine ⟨?_, ?_⟩
    · have := h1.const_mul (wallScale e Np cw x : ℂ)
      rw [mul_zero] at this
      exact this.congr fun m => (scaledChart_fst x _).symm
    · refine (h2.const_mul_atTop (hr x)).congr fun m => ?_
      rw [scaledChart_fst, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr x)]
  · obtain ⟨a, ha, hEq⟩ := huniq x ψ₁ hψ₁ h0 hinf
    refine ⟨wallScale e Np cw x * a, mul_pos (hr x) ha, fun z hz => ?_⟩
    show (scaledChart e Np cw x).1 z = ((wallScale e Np cw x * a : ℝ) : ℂ) * ψ₁ z
    rw [scaledChart_fst, hEq hz, Complex.ofReal_mul, mul_assoc]

end InteractingSLE.Sec7.Lemma71S
