/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsIntegratedSLEPath

/-!
# Integrated `SLE_κ(ρ)` paths: monotonicity, (N1), same-side spreads, reflection

Packet PROVE-SEC2-TERM. Pathwise consequences of the integrated equations of Definition 2.1
(Specification p. 20; the frozen `IsIntegratedSLEPath`) used in the proof of Aux. lemma 3
(`source/spec/p001-048.md`, anchor `aux-3-proof`, L555–L566). Everything here is deterministic.

* `Sec2.IsForcePath` (a structure: every condition of Definition 2.1 except the driving equation)
  and `Sec2.DriverEq` (the driving equation); `IsIntegratedSLEPath.iff_isForcePath_and_driverEq`
  splits the frozen definition into the two;
* `vL_sub` / `vR_sub` / `w_sub`: increments as interval integrals between two times before `ζ`;
* `vL_le_of_le` / `le_vR_of_le`, `antitoneOn_vL` / `monotoneOn_vR`: each left force coordinate is
  nonincreasing and each right one nondecreasing before `ζ`;
* `w_eq_N1`: display (N1), `W_t = √κ B_t − ½ ∑ ρ^{i,q} (V_t^{i,q} − x^{i,q})`;
* `vL_sub_vL_le` / `vR_sub_vR_le`: same-side spreads are bounded by their initial values
  (the source: "differences of two coordinates on the same side are nonincreasing in absolute
  value");
* `IsForcePath.reflect`, `DriverEq.reflect`, `IsIntegratedSLEPath.reflect`: the reflection
  `x ↦ −x` exchanges the two sides (the source's "reflection handles right escape").

Time integrals are interval integrals over `ℝ` of `s ↦ f s.toNNReal`, as in `IsIntegratedSLEPath`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

/-- `ρ / (y − x) = −(ρ / 2) · (2 / (x − y))`: the driving integrand in terms of the force integrand. -/
theorem div_sub_eq_neg_half_mul (ρ x y : ℝ) : ρ / (y - x) = -(ρ / 2) * (2 / (x - y)) := by
  rw [← neg_sub x y, div_neg]
  ring

/-- `2 / (x − y) = −2 · (y − x)⁻¹`. -/
theorem two_div_sub_eq (x y : ℝ) : 2 / (x - y) = -2 * (y - x)⁻¹ := by
  rw [← neg_sub y x, div_neg, div_eq_mul_inv]
  ring

/-- `c / (−x − −y) = −(c / (x − y))`. -/
theorem div_neg_sub_neg (c x y : ℝ) : c / (-x - -y) = -(c / (x - y)) := by
  rw [show -x - -y = -(x - y) by ring, div_neg]

/-- The drift of the driving equation at real time `s`:
`∑ ρ^{i,L} / (w − v^{i,L}) + ∑ ρ^{i,R} / (w − v^{i,R})`, evaluated at `s.toNNReal`. -/
def driverDrift {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ)
    (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (s : ℝ) : ℝ :=
  ∑ i, ρL i / (w s.toNNReal - vL i s.toNNReal) + ∑ i, ρR i / (w s.toNNReal - vR i s.toNNReal)

/-- **The driving equation of Definition 2.1** (Specification p. 20): for `t < ζ`,
`w t = √a b t + ∑ᵢ ∫₀ᵗ ρ^{i,L}/(w − v^{i,L}) + ∑ᵢ ∫₀ᵗ ρ^{i,R}/(w − v^{i,R})`. This is verbatim the
`w_eq` conjunct of the frozen `IsIntegratedSLEPath` (v2, ruling R28; the v1 text parsed the second
sum inside the first integral). Lemmas that use the driving equation take it as this separate
hypothesis so that they apply to the reflected path as well (`DriverEq.reflect`). -/
def DriverEq (a : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ)
    (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop :=
  ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
    w t = Real.sqrt a * b t
      + (∑ i, ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal))
      + (∑ i, ∫ s in (0 : ℝ)..t, ρR i / (w s.toNNReal - vR i s.toNNReal))

/-- Membership of a real time in `[0, t]` gives `s.toNNReal ≤ t`. -/
theorem toNNReal_le_of_mem_Icc {t : ℝ≥0} {s : ℝ} (hs : s ∈ Icc (0 : ℝ) t) : s.toNNReal ≤ t :=
  Real.toNNReal_le_iff_le_coe.2 hs.2

/-- A real time in `[0, t]` with `t < ζ` is before `ζ`. -/
theorem toNNReal_lt_of_mem_Icc {ζ : ℝ≥0∞} {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) t) : (s.toNNReal : ℝ≥0∞) < ζ :=
  lt_of_le_of_lt (by exact_mod_cast toNNReal_le_of_mem_Icc hs) ht

/-- **All conditions of `IsIntegratedSLEPath` except the driving equation** (Definition 2.1,
Specification p. 20): initial values, continuity before `ζ`, the side ordering, integrability of the
reciprocal gaps, the force-point equations, null collision sets, and the threshold/maximality
conditions. Together with `DriverEq` this is Definition 2.1
(`IsIntegratedSLEPath.iff_isForcePath_and_driverEq`). It is invariant under the reflection `x ↦ −x` that exchanges the two sides (`IsForcePath.reflect`). -/
structure IsForcePath {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ)
    (ζ : ℝ≥0∞) : Prop where
  w_zero : w 0 = 0
  vL_zero : ∀ i, vL i 0 = xL i
  vR_zero : ∀ i, vR i 0 = xR i
  continuousOn_w : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}
  continuousOn_vL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ}
  continuousOn_vR : ∀ i, ContinuousOn (vR i) {t | (t : ℝ≥0∞) < ζ}
  antitone_vL : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → Antitone fun i => vL i t
  vL_le_w : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ i, vL i t ≤ w t
  w_le_vR : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ i, w t ≤ vR i t
  monotone_vR : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → Monotone fun i => vR i t
  integrable_gapL : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ i,
    IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vL i s.toNNReal)⁻¹) volume 0 t
  integrable_gapR : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ i,
    IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vR i s.toNNReal)⁻¹) volume 0 t
  vL_eq : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ i,
    vL i t = xL i + ∫ s in (0 : ℝ)..t, 2 / (vL i s.toNNReal - w s.toNNReal)
  vR_eq : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ i,
    vR i t = xR i + ∫ s in (0 : ℝ)..t, 2 / (vR i s.toNNReal - w s.toNNReal)
  volume_collisionL : ∀ i,
    volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = vL i s.toNNReal} = 0
  volume_collisionR : ∀ i,
    volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = vR i s.toNNReal} = 0
  not_threshold : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ →
    ¬ ForceWord.ThresholdCondition ρL ρR (w t) (fun i => vL i t) (fun i => vR i t)
  threshold_of_eq_zero : ζ = 0 → ForceWord.ThresholdCondition ρL ρR 0 xL xR
  threshold_of_tendsto : ∀ {T : ℝ≥0}, 0 < T → (T : ℝ≥0∞) = ζ →
    ∀ {w₀ : ℝ} {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ},
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T)
        (𝓝 (w₀, vL₀, vR₀)) →
      ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀

end Sec2

open Sec2

namespace IsIntegratedSLEPath

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The frozen definition gives every condition except the driving equation. -/
theorem isForcePath (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) :
    IsForcePath xL xR ρL ρR w vL vR ζ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -, h14, h15, h16, h17, h18, h19,
    h20⟩ := h
  exact
    { w_zero := h1, vL_zero := h2, vR_zero := h3, continuousOn_w := h4, continuousOn_vL := h5,
      continuousOn_vR := h6, antitone_vL := fun {t} ht => h7 t ht,
      vL_le_w := fun {t} ht => h8 t ht, w_le_vR := fun {t} ht => h9 t ht,
      monotone_vR := fun {t} ht => h10 t ht, integrable_gapL := fun {t} ht => h11 t ht,
      integrable_gapR := fun {t} ht => h12 t ht, vL_eq := fun {t} ht => h14 t ht,
      vR_eq := fun {t} ht => h15 t ht, volume_collisionL := h16, volume_collisionR := h17,
      not_threshold := fun {t} ht => h18 t ht, threshold_of_eq_zero := h19,
      threshold_of_tendsto := fun {T} hT hζ {w₀ vL₀ vR₀} hlim => h20 T hT hζ w₀ vL₀ vR₀ hlim }

/-- The frozen `w_eq` conjunct (v2, ruling R28) is the driving equation `Sec2.DriverEq`. -/
theorem driverEq (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) :
    DriverEq a ρL ρR w vL vR b ζ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h; exact h

/-- **Definition 2.1 split** into the driving equation and all other conditions. -/
theorem iff_isForcePath_and_driverEq :
    IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ ↔
      IsForcePath xL xR ρL ρR w vL vR ζ ∧ DriverEq a ρL ρR w vL vR b ζ := by
  refine ⟨fun h => ⟨h.isForcePath, h.driverEq⟩, fun ⟨hp, hw⟩ => ?_⟩
  exact ⟨hp.w_zero, hp.vL_zero, hp.vR_zero, hp.continuousOn_w, hp.continuousOn_vL,
    hp.continuousOn_vR, fun _ ht => hp.antitone_vL ht, fun _ ht => hp.vL_le_w ht,
    fun _ ht => hp.w_le_vR ht, fun _ ht => hp.monotone_vR ht, fun _ ht => hp.integrable_gapL ht,
    fun _ ht => hp.integrable_gapR ht, hw, fun _ ht => hp.vL_eq ht, fun _ ht => hp.vR_eq ht,
    hp.volume_collisionL, hp.volume_collisionR, fun _ ht => hp.not_threshold ht,
    hp.threshold_of_eq_zero, fun _ hT hζ _ _ _ hlim => hp.threshold_of_tendsto hT hζ hlim⟩

end IsIntegratedSLEPath

namespace Sec2

namespace IsForcePath

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

section Increments

variable (h : IsForcePath xL xR ρL ρR w vL vR ζ)
include h

/-- The left force integrand is interval integrable on `[0, t]` for `t < ζ`. -/
theorem intervalIntegrable_forceL {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (i : Fin nL) :
    IntervalIntegrable (fun s : ℝ => 2 / (vL i s.toNNReal - w s.toNNReal)) volume 0 t := by
  have := (h.integrable_gapL ht i).const_mul (-2)
  simpa only [two_div_sub_eq] using this

/-- The right force integrand is interval integrable on `[0, t]` for `t < ζ`. -/
theorem intervalIntegrable_forceR {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (i : Fin nR) :
    IntervalIntegrable (fun s : ℝ => 2 / (vR i s.toNNReal - w s.toNNReal)) volume 0 t := by
  have := (h.integrable_gapR ht i).const_mul (-2)
  simpa only [two_div_sub_eq] using this

/-- Each left driving integrand `ρ^{i,L}/(w − v^{i,L})` is interval integrable on `[0, t]`, `t < ζ`. -/
theorem intervalIntegrable_driftL {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (i : Fin nL) :
    IntervalIntegrable (fun s : ℝ => ρL i / (w s.toNNReal - vL i s.toNNReal)) volume 0 t := by
  simpa only [div_eq_mul_inv] using (h.integrable_gapL ht i).const_mul (ρL i)

/-- Each right driving integrand `ρ^{i,R}/(w − v^{i,R})` is interval integrable on `[0, t]`, `t < ζ`. -/
theorem intervalIntegrable_driftR {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (i : Fin nR) :
    IntervalIntegrable (fun s : ℝ => ρR i / (w s.toNNReal - vR i s.toNNReal)) volume 0 t := by
  simpa only [div_eq_mul_inv] using (h.integrable_gapR ht i).const_mul (ρR i)

theorem intervalIntegrable_sum_driftL {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    IntervalIntegrable (fun s : ℝ => ∑ i, ρL i / (w s.toNNReal - vL i s.toNNReal)) volume 0 t := by
  have := IntervalIntegrable.sum Finset.univ fun i _ => h.intervalIntegrable_driftL ht i
  rwa [Finset.sum_fn] at this

theorem intervalIntegrable_sum_driftR {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    IntervalIntegrable (fun s : ℝ => ∑ i, ρR i / (w s.toNNReal - vR i s.toNNReal)) volume 0 t := by
  have := IntervalIntegrable.sum Finset.univ fun i _ => h.intervalIntegrable_driftR ht i
  rwa [Finset.sum_fn] at this

/-- The driving drift is interval integrable on `[0, t]` for `t < ζ`. -/
theorem intervalIntegrable_driverDrift {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    IntervalIntegrable (driverDrift ρL ρR w vL vR) volume 0 t :=
  (h.intervalIntegrable_sum_driftL ht).add (h.intervalIntegrable_sum_driftR ht)

/-- The driving equation with the drift collected: `w t = √a b t + ∫₀ᵗ drift`. -/
theorem w_eq_integral_driverDrift (hw : DriverEq a ρL ρR w vL vR b ζ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) :
    w t = Real.sqrt a * b t + ∫ s in (0 : ℝ)..t, driverDrift ρL ρR w vL vR s := by
  rw [hw t ht, add_assoc]
  congr 1
  unfold driverDrift
  rw [intervalIntegral.integral_add (h.intervalIntegrable_sum_driftL ht)
      (h.intervalIntegrable_sum_driftR ht),
    intervalIntegral.integral_finsetSum fun i _ => h.intervalIntegrable_driftL ht i,
    intervalIntegral.integral_finsetSum fun i _ => h.intervalIntegrable_driftR ht i]

/-- Increment of a left force coordinate between two times before `ζ`. -/
theorem vL_sub {s t : ℝ≥0} (hst : s ≤ t) (ht : (t : ℝ≥0∞) < ζ) (i : Fin nL) :
    vL i t - vL i s = ∫ r in (s : ℝ)..t, 2 / (vL i r.toNNReal - w r.toNNReal) := by
  have hs : (s : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hst) ht
  rw [h.vL_eq ht i, h.vL_eq hs i, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (h.intervalIntegrable_forceL ht i)
      (h.intervalIntegrable_forceL hs i)]

/-- Increment of a right force coordinate between two times before `ζ`. -/
theorem vR_sub {s t : ℝ≥0} (hst : s ≤ t) (ht : (t : ℝ≥0∞) < ζ) (i : Fin nR) :
    vR i t - vR i s = ∫ r in (s : ℝ)..t, 2 / (vR i r.toNNReal - w r.toNNReal) := by
  have hs : (s : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hst) ht
  rw [h.vR_eq ht i, h.vR_eq hs i, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (h.intervalIntegrable_forceR ht i)
      (h.intervalIntegrable_forceR hs i)]

/-- Increment of the driver between two times before `ζ`:
`w t − w s = √a (b t − b s) + ∫ₛᵗ drift`. -/
theorem w_sub (hw : DriverEq a ρL ρR w vL vR b ζ) {s t : ℝ≥0} (hst : s ≤ t)
    (ht : (t : ℝ≥0∞) < ζ) :
    w t - w s = Real.sqrt a * (b t - b s)
      + ∫ r in (s : ℝ)..t, driverDrift ρL ρR w vL vR r := by
  have hs : (s : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hst) ht
  rw [h.w_eq_integral_driverDrift hw ht, h.w_eq_integral_driverDrift hw hs,
    ← intervalIntegral.integral_interval_sub_left (h.intervalIntegrable_driverDrift ht)
      (h.intervalIntegrable_driverDrift hs)]
  ring

end Increments

section Monotone

variable (h : IsForcePath xL xR ρL ρR w vL vR ζ)
include h

/-- Each left force coordinate is nonincreasing before `ζ`. -/
theorem vL_le_of_le {s t : ℝ≥0} (hst : s ≤ t) (ht : (t : ℝ≥0∞) < ζ) (i : Fin nL) :
    vL i t ≤ vL i s := by
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hint : IntervalIntegrable (fun r : ℝ => 2 / (vL i r.toNNReal - w r.toNNReal)) volume s t :=
    (h.intervalIntegrable_forceL ht i).mono_set (by
      rw [uIcc_of_le hst', uIcc_of_le (NNReal.coe_nonneg t)]
      exact Icc_subset_Icc (NNReal.coe_nonneg s) le_rfl)
  have hle : ∫ r in (s : ℝ)..t, 2 / (vL i r.toNNReal - w r.toNNReal) ≤
      ∫ _ in (s : ℝ)..t, (0 : ℝ) := by
    refine intervalIntegral.integral_mono_on hst' hint intervalIntegrable_const fun r hr => ?_
    have hr0 : r ∈ Icc (0 : ℝ) t := ⟨(NNReal.coe_nonneg s).trans hr.1, hr.2⟩
    exact div_nonpos_of_nonneg_of_nonpos (by norm_num)
      (sub_nonpos.2 (h.vL_le_w (toNNReal_lt_of_mem_Icc ht hr0) i))
  rw [intervalIntegral.integral_zero, ← h.vL_sub hst ht i] at hle
  linarith

/-- Each right force coordinate is nondecreasing before `ζ`. -/
theorem le_vR_of_le {s t : ℝ≥0} (hst : s ≤ t) (ht : (t : ℝ≥0∞) < ζ) (i : Fin nR) :
    vR i s ≤ vR i t := by
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hint : IntervalIntegrable (fun r : ℝ => 2 / (vR i r.toNNReal - w r.toNNReal)) volume s t :=
    (h.intervalIntegrable_forceR ht i).mono_set (by
      rw [uIcc_of_le hst', uIcc_of_le (NNReal.coe_nonneg t)]
      exact Icc_subset_Icc (NNReal.coe_nonneg s) le_rfl)
  have hle : ∫ _ in (s : ℝ)..t, (0 : ℝ) ≤
      ∫ r in (s : ℝ)..t, 2 / (vR i r.toNNReal - w r.toNNReal) := by
    refine intervalIntegral.integral_mono_on hst' intervalIntegrable_const hint fun r hr => ?_
    have hr0 : r ∈ Icc (0 : ℝ) t := ⟨(NNReal.coe_nonneg s).trans hr.1, hr.2⟩
    exact div_nonneg (by norm_num)
      (sub_nonneg.2 (h.w_le_vR (toNNReal_lt_of_mem_Icc ht hr0) i))
  rw [intervalIntegral.integral_zero, ← h.vR_sub hst ht i] at hle
  linarith

theorem antitoneOn_vL (i : Fin nL) : AntitoneOn (vL i) {t | (t : ℝ≥0∞) < ζ} :=
  fun _ _ _ ht hst => h.vL_le_of_le hst ht i

theorem monotoneOn_vR (i : Fin nR) : MonotoneOn (vR i) {t | (t : ℝ≥0∞) < ζ} :=
  fun _ _ _ ht hst => h.le_vR_of_le hst ht i

/-- Left force coordinates stay below their initial positions. -/
theorem vL_le_xL {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (i : Fin nL) : vL i t ≤ xL i := by
  simpa [h.vL_zero i] using h.vL_le_of_le (zero_le : (0 : ℝ≥0) ≤ t) ht i

/-- Right force coordinates stay above their initial positions. -/
theorem xR_le_vR {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (i : Fin nR) : xR i ≤ vR i t := by
  simpa [h.vR_zero i] using h.le_vR_of_le (zero_le : (0 : ℝ≥0) ≤ t) ht i

end Monotone

section N1

variable (h : IsForcePath xL xR ρL ρR w vL vR ζ)
include h

/-- `∫₀ᵗ ρ^{i,L}/(w − v^{i,L}) = −(ρ^{i,L}/2) (v^{i,L}_t − x^{i,L})`. -/
theorem integral_driftL {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (i : Fin nL) :
    ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal) = -(ρL i / 2) * (vL i t - xL i) := by
  have hfun : (fun s : ℝ => ρL i / (w s.toNNReal - vL i s.toNNReal)) =
      fun s => -(ρL i / 2) * (2 / (vL i s.toNNReal - w s.toNNReal)) :=
    funext fun s => div_sub_eq_neg_half_mul _ _ _
  rw [hfun, intervalIntegral.integral_const_mul, h.vL_eq ht i]
  ring

/-- `∫₀ᵗ ρ^{i,R}/(w − v^{i,R}) = −(ρ^{i,R}/2) (v^{i,R}_t − x^{i,R})`. -/
theorem integral_driftR {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (i : Fin nR) :
    ∫ s in (0 : ℝ)..t, ρR i / (w s.toNNReal - vR i s.toNNReal) = -(ρR i / 2) * (vR i t - xR i) := by
  have hfun : (fun s : ℝ => ρR i / (w s.toNNReal - vR i s.toNNReal)) =
      fun s => -(ρR i / 2) * (2 / (vR i s.toNNReal - w s.toNNReal)) :=
    funext fun s => div_sub_eq_neg_half_mul _ _ _
  rw [hfun, intervalIntegral.integral_const_mul, h.vR_eq ht i]
  ring

/-- **(N1)** (Specification p. 25): `W_t = √κ B_t − ½ ∑_{i,q} ρ^{i,q} (V_t^{i,q} − x^{i,q})`. -/
theorem w_eq_N1 (hw : DriverEq a ρL ρR w vL vR b ζ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    w t = Real.sqrt a * b t - (1 / 2) * ∑ i, ρL i * (vL i t - xL i)
      - (1 / 2) * ∑ i, ρR i * (vR i t - xR i) := by
  rw [hw t ht, Finset.sum_congr rfl fun i _ => h.integral_driftL ht i,
    Finset.sum_congr rfl fun i _ => h.integral_driftR ht i]
  have e1 : ∑ i, -(ρL i / 2) * (vL i t - xL i) = -((1 / 2) * ∑ i, ρL i * (vL i t - xL i)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, -(ρR i / 2) * (vR i t - xR i) = -((1 / 2) * ∑ i, ρR i * (vR i t - xR i)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2]
  ring

end N1

section Spreads

variable (h : IsForcePath xL xR ρL ρR w vL vR ζ)
include h

/-- **Same-side spreads on the left** (Specification p. 25): for `i ≤ j` (so `v^{j,L} ≤ v^{i,L}`),
`0 ≤ v^{i,L}_t − v^{j,L}_t ≤ x^{i,L} − x^{j,L}` before `ζ`. -/
theorem vL_sub_vL_le {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {i j : Fin nL} (hij : i ≤ j) :
    vL i t - vL j t ≤ xL i - xL j := by
  have hint := (h.intervalIntegrable_forceL ht i).sub (h.intervalIntegrable_forceL ht j)
  have key : vL i t - vL j t - (xL i - xL j) = ∫ s in (0 : ℝ)..t,
      (2 / (vL i s.toNNReal - w s.toNNReal) - 2 / (vL j s.toNNReal - w s.toNNReal)) := by
    rw [intervalIntegral.integral_sub (h.intervalIntegrable_forceL ht i)
      (h.intervalIntegrable_forceL ht j)]
    conv_lhs => rw [h.vL_eq ht i, h.vL_eq ht j]
    ring
  have hae : (fun s : ℝ => 2 / (vL i s.toNNReal - w s.toNNReal) -
      2 / (vL j s.toNNReal - w s.toNNReal)) ≤ᵐ[volume.restrict (Icc (0 : ℝ) t)] fun _ => 0 := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (h.volume_collisionL i)] with s hs hsI
    have hlt := toNNReal_lt_of_mem_Icc ht hsI
    have hne : w s.toNNReal ≠ vL i s.toNNReal := fun he => hs ⟨hsI.1, hlt, he⟩
    have hp : 0 < w s.toNNReal - vL i s.toNNReal :=
      sub_pos.2 (lt_of_le_of_ne (h.vL_le_w hlt i) (Ne.symm hne))
    have hpq : w s.toNNReal - vL i s.toNNReal ≤ w s.toNNReal - vL j s.toNNReal :=
      sub_le_sub_left (h.antitone_vL hlt hij) _
    have h1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hp hpq
    rw [← neg_sub (w s.toNNReal) (vL i s.toNNReal), ← neg_sub (w s.toNNReal) (vL j s.toNNReal),
      div_neg, div_neg]
    linarith
  have hle := intervalIntegral.integral_mono_ae_restrict (NNReal.coe_nonneg t) hint
    intervalIntegrable_const hae
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_zero] at hle
  linarith

/-- **Same-side spreads on the right**: for `i ≤ j` (so `v^{i,R} ≤ v^{j,R}`),
`v^{j,R}_t − v^{i,R}_t ≤ x^{j,R} − x^{i,R}` before `ζ`. -/
theorem vR_sub_vR_le {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {i j : Fin nR} (hij : i ≤ j) :
    vR j t - vR i t ≤ xR j - xR i := by
  have hint := (h.intervalIntegrable_forceR ht j).sub (h.intervalIntegrable_forceR ht i)
  have key : vR j t - vR i t - (xR j - xR i) = ∫ s in (0 : ℝ)..t,
      (2 / (vR j s.toNNReal - w s.toNNReal) - 2 / (vR i s.toNNReal - w s.toNNReal)) := by
    rw [intervalIntegral.integral_sub (h.intervalIntegrable_forceR ht j)
      (h.intervalIntegrable_forceR ht i)]
    conv_lhs => rw [h.vR_eq ht i, h.vR_eq ht j]
    ring
  have hae : (fun s : ℝ => 2 / (vR j s.toNNReal - w s.toNNReal) -
      2 / (vR i s.toNNReal - w s.toNNReal)) ≤ᵐ[volume.restrict (Icc (0 : ℝ) t)] fun _ => 0 := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (h.volume_collisionR i)] with s hs hsI
    have hlt := toNNReal_lt_of_mem_Icc ht hsI
    have hne : w s.toNNReal ≠ vR i s.toNNReal := fun he => hs ⟨hsI.1, hlt, he⟩
    have hp : 0 < vR i s.toNNReal - w s.toNNReal :=
      sub_pos.2 (lt_of_le_of_ne (h.w_le_vR hlt i) hne)
    have hpq : vR i s.toNNReal - w s.toNNReal ≤ vR j s.toNNReal - w s.toNNReal :=
      sub_le_sub_right (h.monotone_vR hlt hij) _
    have h1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hp hpq
    linarith
  have hle := intervalIntegral.integral_mono_ae_restrict (NNReal.coe_nonneg t) hint
    intervalIntegrable_const hae
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_zero] at hle
  linarith

end Spreads

section Reflection

/-- The threshold condition is invariant under the reflection `x ↦ −x`, which exchanges the sides. -/
theorem _root_.InteractingSLE.Sec2.thresholdCondition_neg_iff {w₀ : ℝ} {vL₀ : Fin nL → ℝ}
    {vR₀ : Fin nR → ℝ} :
    ForceWord.ThresholdCondition ρR ρL (-w₀) (fun i => -vR₀ i) (fun i => -vL₀ i) ↔
      ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀ := by
  unfold ForceWord.ThresholdCondition
  simp only [neg_inj]
  exact Or.comm

/-- **Reflection** (the source's "reflection handles right escape"): `(−w, −v^R, −v^L)` with the
sides exchanged satisfies all conditions except the driving equation. -/
theorem reflect (h : IsForcePath xL xR ρL ρR w vL vR ζ) :
    IsForcePath (-xR) (-xL) ρR ρL (-w) (fun i => -vR i) (fun i => -vL i) ζ where
  w_zero := by simp [h.w_zero]
  vL_zero i := by simp [h.vR_zero i]
  vR_zero i := by simp [h.vL_zero i]
  continuousOn_w := h.continuousOn_w.neg
  continuousOn_vL i := (h.continuousOn_vR i).neg
  continuousOn_vR i := (h.continuousOn_vL i).neg
  antitone_vL ht _ _ hij := neg_le_neg (h.monotone_vR ht hij)
  vL_le_w ht i := neg_le_neg (h.w_le_vR ht i)
  w_le_vR ht i := neg_le_neg (h.vL_le_w ht i)
  monotone_vR ht _ _ hij := neg_le_neg (h.antitone_vL ht hij)
  integrable_gapL {t} ht i := by
    have e : (fun s : ℝ => ((-w) s.toNNReal - (fun i => -vR i) i s.toNNReal)⁻¹) =
        fun s => -(w s.toNNReal - vR i s.toNNReal)⁻¹ := by
      funext s
      simp only [Pi.neg_apply]
      rw [neg_sub_neg, ← inv_neg, neg_sub]
    rw [e]
    exact (h.integrable_gapR ht i).neg
  integrable_gapR {t} ht i := by
    have e : (fun s : ℝ => ((-w) s.toNNReal - (fun i => -vL i) i s.toNNReal)⁻¹) =
        fun s => -(w s.toNNReal - vL i s.toNNReal)⁻¹ := by
      funext s
      simp only [Pi.neg_apply]
      rw [neg_sub_neg, ← inv_neg, neg_sub]
    rw [e]
    exact (h.integrable_gapL ht i).neg
  vL_eq {t} ht i := by
    have e : (fun s : ℝ => 2 / ((fun i => -vR i) i s.toNNReal - (-w) s.toNNReal)) =
        fun s => -(2 / (vR i s.toNNReal - w s.toNNReal)) := by
      funext s
      simp only [Pi.neg_apply]
      exact div_neg_sub_neg _ _ _
    simp only [Pi.neg_apply] at e ⊢
    rw [e, intervalIntegral.integral_neg, h.vR_eq ht i]
    ring
  vR_eq {t} ht i := by
    have e : (fun s : ℝ => 2 / ((fun i => -vL i) i s.toNNReal - (-w) s.toNNReal)) =
        fun s => -(2 / (vL i s.toNNReal - w s.toNNReal)) := by
      funext s
      simp only [Pi.neg_apply]
      exact div_neg_sub_neg _ _ _
    simp only [Pi.neg_apply] at e ⊢
    rw [e, intervalIntegral.integral_neg, h.vL_eq ht i]
    ring
  volume_collisionL i := by simpa [neg_inj] using h.volume_collisionR i
  volume_collisionR i := by simpa [neg_inj] using h.volume_collisionL i
  not_threshold {t} ht := by
    have := h.not_threshold ht
    rwa [← thresholdCondition_neg_iff] at this
  threshold_of_eq_zero hζ := by
    have := (thresholdCondition_neg_iff (w₀ := 0)).2 (h.threshold_of_eq_zero hζ)
    rw [neg_zero] at this
    exact this
  threshold_of_tendsto {T} hT hζ {w₀ vL₀ vR₀} hlim := by
    let φ : ℝ × (Fin nR → ℝ) × (Fin nL → ℝ) → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
      fun p => (-p.1, -p.2.2, -p.2.1)
    have hφ : Continuous φ := by fun_prop
    have h2 := (hφ.tendsto (w₀, vL₀, vR₀)).comp hlim
    have h3 : Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T)
        (𝓝 (-w₀, -vR₀, -vL₀)) := by
      convert h2 using 2 with t
      ext i <;> simp [φ]
    have := (thresholdCondition_neg_iff).2 (h.threshold_of_tendsto hT hζ h3)
    simpa using this

/-- The driving equation is invariant under the reflection. -/
theorem _root_.InteractingSLE.Sec2.DriverEq.reflect (hw : DriverEq a ρL ρR w vL vR b ζ) :
    DriverEq a ρR ρL (-w) (fun i => -vR i) (fun i => -vL i) (-b) ζ := by
  intro t ht
  have e : ∀ (c : ℝ) (v : ℝ≥0 → ℝ), (fun s : ℝ => c / ((-w) s.toNNReal - (-v) s.toNNReal)) =
      fun s => -(c / (w s.toNNReal - v s.toNNReal)) := fun c v => by
    funext s
    simp only [Pi.neg_apply]
    exact div_neg_sub_neg _ _ _
  simp only [Pi.neg_apply] at e ⊢
  simp only [e, intervalIntegral.integral_neg, Finset.sum_neg_distrib, hw t ht]
  ring

end Reflection

end IsForcePath

end Sec2

/-- **Reflection of Definition 2.1**: `(−w, −v^R, −v^L, −b)` with the sides exchanged is again an
integrated `SLE_a(ρ)` path. -/
theorem IsIntegratedSLEPath.reflect {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) :
    IsIntegratedSLEPath a (-xR) (-xL) ρR ρL (-w) (fun i => -vR i) (fun i => -vL i) (-b) ζ :=
  IsIntegratedSLEPath.iff_isForcePath_and_driverEq.2 ⟨h.isForcePath.reflect, h.driverEq.reflect⟩

end InteractingSLE
