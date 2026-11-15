/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb7Clock

/-!
# Aux. lemma 102: the band martingale

Packet PROVE-SEC7-C7. Specification p. 354 (Aux. lemma 106, "the alternating bands `U ≤ 2/3` and `U ≥ 1/3` have only
finitely many switches on that clock: Brownian motion and the finite-variation error have finite terminal limits, and
the drift is bounded on the middle band").

Let `h = hB` be a smooth transition, `0` on `u ≤ 1/3` and `1` on `u ≥ 2/3`. Its derivatives vanish off
`[1/3, 2/3]`, where the driver is at distance `≥ D/3` from both nearest marks, so the generator of `h(U)` is bounded
by `C₁ D^{-2} + C₂ |E|` (`abs_genExpr_hB_le`). With the extra coordinate `I = ∫ itoGen h(U)` (`bandI`, adapted as the
running integral of a Borel function of the stopped state), the localized Itô formula gives that
`N = h(U) − I` and `N² − ∫ κ h'(U)² D^{-2}` (stopped at `σ_n`) are martingales (`martingale_bandN`,
`martingale_bandN_sq`), hence the `L²` increment identity `E (N_t − N_s)² = E (J_t − J_s)`
(`integral_sq_sub_bandN`).

## Main results

* `hB`, `hB'`, `hB''`: the band function; `stS`, `genSt`, `bandC`, `bandI`;
* `abs_genExpr_hB_le`, `martingale_bandN`, `martingale_bandN_sq`, `integral_sq_sub_bandN`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Clock

open Zhan

variable {nL nR : ℕ}

/-! ### The band function -/

section BandFun

/-- The band function: `0` for `u ≤ 1/3`, `1` for `u ≥ 2/3`, smooth. -/
def hB (u : ℝ) : ℝ := Real.smoothTransition (3 * u - 1)

/-- `h'`. -/
def hB' (u : ℝ) : ℝ := deriv hB u

/-- `h''`. -/
def hB'' (u : ℝ) : ℝ := deriv hB' u

theorem contDiff_hB : ContDiff ℝ (⊤ : ℕ∞) hB :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem contDiff_hB' : ContDiff ℝ (⊤ : ℕ∞) hB' := (contDiff_infty_iff_deriv.1 contDiff_hB).2

theorem hasDerivAt_hB (u : ℝ) : HasDerivAt hB (hB' u) u :=
  ((contDiff_hB.differentiable (by simp)) u).hasDerivAt

theorem hasDerivAt_hB' (u : ℝ) : HasDerivAt hB' (hB'' u) u :=
  ((contDiff_hB'.differentiable (by simp)) u).hasDerivAt

theorem continuous_hB' : Continuous hB' := contDiff_hB'.continuous

theorem continuous_hB'' : Continuous hB'' := (contDiff_infty_iff_deriv.1 contDiff_hB').2.continuous

theorem hB_eq_zero {u : ℝ} (hu : u ≤ 1 / 3) : hB u = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem hB_eq_one {u : ℝ} (hu : 2 / 3 ≤ u) : hB u = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem hB'_eq_zero {u : ℝ} (hu : u < 1 / 3 ∨ 2 / 3 < u) : hB' u = 0 := by
  rcases hu with hu | hu
  · have h : hB =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hu] with v hv using hB_eq_zero (le_of_lt hv)
    simp only [hB', h.deriv_eq, deriv_const]
  · have h : hB =ᶠ[𝓝 u] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds hu] with v hv using hB_eq_one (le_of_lt hv)
    simp only [hB', h.deriv_eq, deriv_const]

theorem hB''_eq_zero {u : ℝ} (hu : u < 1 / 3 ∨ 2 / 3 < u) : hB'' u = 0 := by
  rcases hu with hu | hu
  · have h : hB' =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hu] with v hv using hB'_eq_zero (Or.inl hv)
    simp only [hB'', h.deriv_eq, deriv_const]
  · have h : hB' =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hu] with v hv using hB'_eq_zero (Or.inr hv)
    simp only [hB'', h.deriv_eq, deriv_const]

theorem exists_bound_of_support {f : ℝ → ℝ} (hf : Continuous f) (h0 : ∀ u, u < 1 / 3 ∨ 2 / 3 < u → f u = 0) :
    ∃ K, 0 ≤ K ∧ ∀ u, |f u| ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (1 / 3 : ℝ)) (b := 2 / 3)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max K 0, le_max_right _ _, fun u => ?_⟩
  by_cases hu : u ∈ Icc (1 / 3 : ℝ) (2 / 3)
  · rw [← Real.norm_eq_abs]; exact (hK u hu).trans (le_max_left _ _)
  · rw [mem_Icc, not_and_or, not_le, not_le] at hu
    rw [h0 u hu, abs_zero]; exact le_max_right _ _

theorem exists_bound_hB' : ∃ K, 0 ≤ K ∧ ∀ u, |hB' u| ≤ K :=
  exists_bound_of_support continuous_hB' fun _ hu => hB'_eq_zero hu

theorem exists_bound_hB'' : ∃ K, 0 ≤ K ∧ ∀ u, |hB'' u| ≤ K :=
  exists_bound_of_support continuous_hB'' fun _ hu => hB''_eq_zero hu

theorem hB_nonneg (u : ℝ) : 0 ≤ hB u := Real.smoothTransition.nonneg _

theorem hB_le_one (u : ℝ) : hB u ≤ 1 := Real.smoothTransition.le_one _

end BandFun

/-! ### The generator bound along a path -/

section PathBand

variable {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ}
  {ρR : Fin (nR + 1) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- (P2)–(P3) at a time with `V^{L,0} < W < V^{R,0}`. -/
theorem numAt_div_eq {t : ℝ≥0} (hL0 : vL 0 t < w t) (hR0 : w t < vR 0 t) :
    numAt ρL ρR w vL vR t / gapAt vL vR t =
      angDrift (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) (angAt w vL vR t) / gapAt vL vR t ^ 2 +
        angErr ρL ρR (w t) (fun i => vL i t) (fun j => vR j t) / gapAt vL vR t := by
  have h := drift_angU_eq ρL ρR (w := w t) (vL := fun i => vL i t) (vR := fun j => vR j t) hL0 hR0 0
  rw [driftLin₀_angDens] at h
  simpa only [numAt, angAt, gapAt, angDens] using h

/-- The constant `C₁` of the band generator bound. -/
def bandC₁ (κ a b K' K'' : ℝ) : ℝ := K' * (3 * |a| + 3 * |b|) + κ / 2 * K''

variable (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
include hp

/-- **The band generator bound**: at a non-collision time, `|itoGen h(U)| ≤ C₁ D^{-2} + (K'/D₀) |E|`. -/
theorem abs_genExpr_hB_le (hκ : 0 ≤ κ) (hx : 0 < xR 0 - xL 0) {K' K'' : ℝ} (hK' : ∀ u, |hB' u| ≤ K')
    (hK'' : ∀ u, |hB'' u| ≤ K'') {s : ℝ} (hs : (s.toNNReal : ℝ≥0∞) < ζ)
    (hL0 : vL 0 s.toNNReal < w s.toNNReal) (hR0 : w s.toNNReal < vR 0 s.toNNReal) :
    |genExpr κ ρL ρR hB' hB'' w vL vR s| ≤
      bandC₁ κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) K' K'' * (vR 0 s.toNNReal - vL 0 s.toNNReal)⁻¹ ^ 2 +
        K' / (xR 0 - xL 0) * errAbs ρL ρR w vL vR s := by
  have hF := hp.isForcePath
  set t := s.toNNReal
  have hD : 0 < gapAt vL vR t := sub_pos.2 (hL0.trans hR0)
  have hDx : xR 0 - xL 0 ≤ gapAt vL vR t := le_gapAt hp hs
  have hE := abs_angErr_le (ρL := ρL) (ρR := ρR) hL0 hR0 (hF.antitone_vL hs) (hF.monotone_vR hs)
  have hEn := errAbs_nonneg (ρL := ρL) (ρR := ρR) hL0 hR0 (hF.antitone_vL hs) (hF.monotone_vR hs)
  have herr : errAbs ρL ρR w vL vR s = (∑ i, |ρL i| * ((w t - vL 0 t)⁻¹ - (w t - vL i t)⁻¹)) +
      ∑ j, |ρR j| * ((vR 0 t - w t)⁻¹ - (vR j t - w t)⁻¹) := rfl
  have hK'0 : 0 ≤ K' := (abs_nonneg _).trans (hK' 0)
  have hK''0 : 0 ≤ K'' := (abs_nonneg _).trans (hK'' 0)
  have hC1 : 0 ≤ bandC₁ κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) K' K'' := by unfold bandC₁; positivity
  have hDinv : (vR 0 t - vL 0 t)⁻¹ ^ 2 = 1 / gapAt vL vR t ^ 2 := by simp only [gapAt]; rw [inv_pow, one_div]
  rw [hDinv, herr]
  set A := (∑ i, |ρL i| * ((w t - vL 0 t)⁻¹ - (w t - vL i t)⁻¹)) +
      ∑ j, |ρR j| * ((vR 0 t - w t)⁻¹ - (vR j t - w t)⁻¹)
  set U := angAt w vL vR t
  set D := gapAt vL vR t
  have hrhs : 0 ≤ bandC₁ κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) K' K'' * (1 / D ^ 2) + K' / (xR 0 - xL 0) * A := by
    have : 0 ≤ K' / (xR 0 - xL 0) := div_nonneg hK'0 hx.le
    positivity
  by_cases hU : U < 1 / 3 ∨ 2 / 3 < U
  · simp only [genExpr]
    rw [show angAt w vL vR s.toNNReal = U from rfl, hB'_eq_zero hU, hB''_eq_zero hU]
    simpa using hrhs
  · rw [not_or, not_lt, not_lt] at hU
    simp only [genExpr]
    rw [show angAt w vL vR s.toNNReal = U from rfl, show gapAt vL vR s.toNNReal = D from rfl,
      show numAt ρL ρR w vL vR s.toNNReal = numAt ρL ρR w vL vR t from rfl, numAt_div_eq hL0 hR0]
    set E := angErr ρL ρR (w t) (fun i => vL i t) (fun j => vR j t)
    have hdr : |angDrift (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) U| ≤ 3 * |2 + ∑ i, ρL i| + 3 * |2 + ∑ j, ρR j| := by
      unfold angDrift
      have hu0 : 0 < U := by linarith
      have hu1 : 0 < 1 - U := by linarith
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [abs_div, abs_of_pos hu0, div_le_iff₀ hu0]
        nlinarith [abs_nonneg (2 + ∑ i, ρL i)]
      · rw [abs_div, abs_of_pos hu1, div_le_iff₀ hu1]
        nlinarith [abs_nonneg (2 + ∑ j, ρR j)]
    have hD2 : 0 < D ^ 2 := by positivity
    calc |hB' U * (angDrift (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) U / D ^ 2 + E / D) + κ / 2 * hB'' U / D ^ 2|
        ≤ |hB' U| * (|angDrift (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) U| / D ^ 2 + |E| / D) +
            κ / 2 * |hB'' U| / D ^ 2 := by
          refine (abs_add_le _ _).trans (add_le_add ?_ (le_of_eq ?_))
          · rw [abs_mul]
            refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (le_of_eq ?_)) (abs_nonneg _)
            rw [abs_div, abs_div, abs_of_pos hD2, abs_of_pos hD]
          · rw [abs_div, abs_mul, abs_of_pos hD2, abs_of_nonneg (by positivity : (0 : ℝ) ≤ κ / 2)]
      _ ≤ K' * ((3 * |2 + ∑ i, ρL i| + 3 * |2 + ∑ j, ρR j|) / D ^ 2 + A / (xR 0 - xL 0)) +
            κ / 2 * K'' / D ^ 2 := by
          refine add_le_add (mul_le_mul (hK' U) (add_le_add ?_ ?_) (by positivity) hK'0) ?_
          · exact div_le_div_of_nonneg_right hdr hD2.le
          · exact div_le_div₀ hEn hE hx hDx
          · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hK'' U) (by positivity)) hD2.le
      _ = bandC₁ κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) K' K'' * (1 / D ^ 2) + K' / (xR 0 - xL 0) * A := by
          unfold bandC₁; field_simp; ring

end PathBand

/-! ### The stopped state and the band coordinate -/

section BandCoord

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The state stopped at `σ` on the good event (`(0, x^L, x^R)` off it). -/
def stS (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0) (r : ℝ≥0) (ω : Ω) :
    ℝ × (Fin (nL + 1) → ℝ) × (Fin (nR + 1) → ℝ) :=
  open scoped Classical in
  if ω ∈ G then Coupling.stateAt W VL VR (min r (σ ω)) ω else (0, xL, xR)

/-- The generator of `φ(U)` as a function of a state `(w, v^L, v^R)`. -/
def genSt (κ : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (φ' φ'' : ℝ → ℝ)
    (st : ℝ × (Fin (nL + 1) → ℝ) × (Fin (nR + 1) → ℝ)) : ℝ :=
  φ' ((st.1 - st.2.1 0) / (st.2.2 0 - st.2.1 0)) *
      (((∑ i, ρL i * (st.1 - st.2.1 i)⁻¹) + (∑ j, ρR j * (st.1 - st.2.2 j)⁻¹) - 2 / (st.2.1 0 - st.1) -
        (st.1 - st.2.1 0) / (st.2.2 0 - st.2.1 0) * (2 / (st.2.2 0 - st.1) - 2 / (st.2.1 0 - st.1))) /
        (st.2.2 0 - st.2.1 0)) +
    κ / 2 * φ'' ((st.1 - st.2.1 0) / (st.2.2 0 - st.2.1 0)) / (st.2.2 0 - st.2.1 0) ^ 2

theorem genExpr_eq_genSt (κ : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (φ' φ'' : ℝ → ℝ)
    (w : ℝ≥0 → ℝ) (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin (nR + 1) → ℝ≥0 → ℝ) (s : ℝ) :
    genExpr κ ρL ρR φ' φ'' w vL vR s =
      genSt κ ρL ρR φ' φ'' (w s.toNNReal, fun i => vL i s.toNNReal, fun j => vR j s.toNNReal) := rfl

theorem measurable_genSt (κ : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) {φ' φ'' : ℝ → ℝ}
    (hφ' : Continuous φ') (hφ'' : Continuous φ'') : Measurable (genSt κ ρL ρR φ' φ'') := by
  have h1 := hφ'.measurable
  have h2 := hφ''.measurable
  unfold genSt
  fun_prop

/-- The rate of the band coordinate: the generator of `h(U)` at the stopped state. -/
def bandC (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin (nR + 1) → ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0) (s : ℝ) (ω : Ω) : ℝ :=
  genSt κ ρL ρR hB' hB'' (stS xL xR G W VL VR σ s.toNNReal ω)

/-- The band coordinate `I_t = ∫₀ᵗ itoGen h(U)` (at the stopped state). -/
def bandI (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin (nR + 1) → ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ u in (0 : ℝ)..t, bandC κ xL xR ρL ρR G W VL VR σ u ω

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ}
  {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
  {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω} {T : ℕ → Ω → ℝ≥0}

section Facts

variable (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω) (n : ℕ)
include hgood

omit hgood in
theorem bandC_eq {ω : Ω} (hω : ω ∈ G) {u : ℝ} (hu : u ∈ Icc 0 (angLoc G T W VL VR B ζ n ω : ℝ)) :
    bandC κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n) u ω =
      genExpr κ ρL ρR hB' hB'' (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) u := by
  have hus : u.toNNReal ≤ angLoc G T W VL VR B ζ n ω := Sec2.toNNReal_le_of_mem_Icc hu
  simp only [bandC, stS, hω, ↓reduceIte, min_eq_left hus, genExpr_eq_genSt, Coupling.stateAt]

theorem intervalIntegrable_bandC (hx : 0 < xR 0 - xL 0) {ω : Ω} (hω : ω ∈ G) :
    IntervalIntegrable (bandC κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n) · ω) volume 0
      (angLoc G T W VL VR B ζ n ω) := by
  have h := intervalIntegrable_genExpr (hgood ω hω).1 hx continuous_hB' continuous_hB'' (κ := κ)
    (angLoc_lt_lifetime (n := n) (G := G) (hgood ω hω))
  refine h.congr fun u hu => ?_
  rw [uIoc_of_le (angLoc G T W VL VR B ζ n ω).coe_nonneg] at hu
  exact (bandC_eq n hω ⟨hu.1.le, hu.2⟩).symm

/-- The bound `∫₀^{σ_n} |itoGen h(U)| ≤ K_c(n)`. -/
def bandKc (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin (nR + 1) → ℝ) (K' K'' : ℝ) (n : ℕ) : ℝ :=
  bandC₁ κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) K' K'' * (n * ((xR 0 - xL 0) ^ 2)⁻¹) +
    K' / (xR 0 - xL 0) * errK xL xR ρL ρR

theorem integral_abs_bandC_le (hκ : 0 ≤ κ) (hx : 0 < xR 0 - xL 0) {K' K'' : ℝ} (hK' : ∀ u, |hB' u| ≤ K')
    (hK'' : ∀ u, |hB'' u| ≤ K'') {ω : Ω} (hω : ω ∈ G) :
    ∫ u in (0 : ℝ)..(angLoc G T W VL VR B ζ n ω : ℝ),
      |bandC κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n) u ω| ≤ bandKc κ xL xR ρL ρR K' K'' n := by
  set σ := angLoc G T W VL VR B ζ n ω with hσdef
  have hp := (hgood ω hω).1
  have hF := hp.isForcePath
  have hσζ : (σ : ℝ≥0∞) < ζ ω := angLoc_lt_lifetime (hgood ω hω)
  have hK'0 : 0 ≤ K' := (abs_nonneg _).trans (hK' 0)
  have hci := intervalIntegrable_clockRate hp hx hσζ
  have hei := intervalIntegrable_errAbs hp hσζ (ρL := ρL) (ρR := ρR)
  have hbi := intervalIntegrable_bandC hgood n hx hω (κ := κ) (ρL := ρL) (ρR := ρR)
  calc ∫ u in (0 : ℝ)..σ, |bandC κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n) u ω|
      ≤ ∫ u in (0 : ℝ)..σ, (bandC₁ κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) K' K'' *
          (VR 0 u.toNNReal ω - VL 0 u.toNNReal ω)⁻¹ ^ 2 +
          K' / (xR 0 - xL 0) * errAbs ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) u) := by
        refine intervalIntegral.integral_mono_ae_restrict σ.coe_nonneg hbi.abs
          ((hci.const_mul _).add (hei.const_mul _)) ?_
        have hnc := ae_not_collision hF hσζ
        rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
        filter_upwards [hnc, Measure.ae_ne volume 0] with u hu hu0 huI
        have huI' : u ∈ Ioc 0 (σ : ℝ) := ⟨lt_of_le_of_ne huI.1 (Ne.symm hu0), huI.2⟩
        obtain ⟨hL, hR⟩ := hu huI'
        have huζ := Sec2.toNNReal_lt_of_mem_Icc hσζ huI
        rw [bandC_eq n hω huI]
        exact abs_genExpr_hB_le hp hκ hx hK' hK'' huζ (lt_of_le_of_ne (hF.vL_le_w huζ 0) (hL 0))
          (lt_of_le_of_ne (hF.w_le_vR huζ 0) (Ne.symm (hR 0)))
    _ = bandC₁ κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) K' K'' * (∫ u in (0 : ℝ)..σ,
          (VR 0 u.toNNReal ω - VL 0 u.toNNReal ω)⁻¹ ^ 2) + K' / (xR 0 - xL 0) *
          ∫ u in (0 : ℝ)..σ, errAbs ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) u := by
        rw [intervalIntegral.integral_add (hci.const_mul _) (hei.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ bandKc κ xL xR ρL ρR K' K'' n := by
        have hc := clockI_le hgood n hx (t := σ) (angLoc_le_n n ω) ω
        rw [clockI_eq n hω le_rfl, abs_of_nonneg (intervalIntegral.integral_nonneg σ.coe_nonneg
          fun _ _ => by positivity)] at hc
        have he := integral_errAbs_le hp hσζ (ρL := ρL) (ρR := ρR)
        have hC1 : 0 ≤ bandC₁ κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) K' K'' := by
          have hK''0 : 0 ≤ K'' := (abs_nonneg _).trans (hK'' 0)
          unfold bandC₁; positivity
        have hC2 : 0 ≤ K' / (xR 0 - xL 0) := div_nonneg hK'0 hx.le
        unfold bandKc
        exact add_le_add (mul_le_mul_of_nonneg_left hc hC1) (mul_le_mul_of_nonneg_left he hC2)

theorem abs_bandI_le (hκ : 0 ≤ κ) (hx : 0 < xR 0 - xL 0) {K' K'' : ℝ} (hK' : ∀ u, |hB' u| ≤ K')
    (hK'' : ∀ u, |hB'' u| ≤ K'') {ω : Ω} (hω : ω ∈ G) {t : ℝ≥0} (ht : t ≤ angLoc G T W VL VR B ζ n ω) :
    |bandI κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n) t ω| ≤ bandKc κ xL xR ρL ρR K' K'' n := by
  have hbi := intervalIntegrable_bandC hgood n hx hω (κ := κ) (ρL := ρL) (ρR := ρR)
  refine (intervalIntegral.abs_integral_le_integral_abs t.coe_nonneg).trans
    ((intervalIntegral.integral_mono_interval le_rfl t.coe_nonneg (by exact_mod_cast ht)
      (ae_of_all _ fun _ => abs_nonneg _) hbi.abs).trans
    (integral_abs_bandC_le hgood n hκ hx hK' hK'' hω))

theorem continuousOn_bandI (hx : 0 < xR 0 - xL 0) {ω : Ω} (hω : ω ∈ G) :
    ContinuousOn (bandI κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n) · ω)
      (Iic (angLoc G T W VL VR B ζ n ω)) := by
  have hbi := intervalIntegrable_bandC hgood n hx hω (κ := κ) (ρL := ρL) (ρR := ρR)
  have hc := intervalIntegral.continuousOn_primitive_interval' hbi
    (left_mem_uIcc (a := (0 : ℝ)) (b := angLoc G T W VL VR B ζ n ω))
  refine hc.comp NNReal.continuous_coe.continuousOn fun s hs => ?_
  rw [uIcc_of_le (angLoc G T W VL VR B ζ n ω).coe_nonneg]
  exact ⟨s.coe_nonneg, by exact_mod_cast hs⟩

theorem continuous_stS (ω : Ω) :
    Continuous fun r => stS xL xR G W VL VR (angLoc G T W VL VR B ζ n) r ω := by
  by_cases hω : ω ∈ G
  · have hF := (hgood ω hω).1.isForcePath
    have hsub : Iic (angLoc G T W VL VR B ζ n ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs =>
      lt_of_le_of_lt (by exact_mod_cast hs) (angLoc_lt_lifetime (hgood ω hω))
    have hc := (hF.continuousOn_w.prodMk ((continuousOn_pi.2 hF.continuousOn_vL).prodMk
      (continuousOn_pi.2 hF.continuousOn_vR))).mono hsub
    simp only [stS, hω, ↓reduceIte, Coupling.stateAt]
    exact hc.comp_continuous (continuous_id.min continuous_const) fun r => mem_Iic.2 (min_le_right _ _)
  · simp only [stS, hω, ↓reduceIte]; exact continuous_const

end Facts

section Meas

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T)

include hE hGm hGc hgood hT in
theorem measurable_stS (n : ℕ) (r : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P r] (stS xL xR G W VL VR (angLoc G T W VL VR B ζ n) r) := by
  obtain ⟨-, hWa, hVLa, hVRa, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) 0
  have hσ := isStoppingTime_angLoc hE hGm hGc hgood hT n
  have hK : ∀ s, Measurable[usualAugmentation 𝓕 P s] fun ω =>
      ((killedAt ζ W s ω, fun i => killedAt ζ (VL i) s ω, fun j => killedAt ζ (VR j) s ω) :
        ℝ × (Fin (nL + 1) → ℝ) × (Fin (nR + 1) → ℝ)) := fun s =>
    (Sec2.TwoSeed.measurable_killed hWa s).prodMk
      ((@Measurable.of_eval Ω (Fin (nL + 1)) (fun _ => ℝ) (usualAugmentation 𝓕 P s) _ _ fun i =>
          Sec2.TwoSeed.measurable_killed (hVLa i) s).prodMk
        (@Measurable.of_eval Ω (Fin (nR + 1)) (fun _ => ℝ) (usualAugmentation 𝓕 P s) _ _ fun j =>
          Sec2.TwoSeed.measurable_killed (hVRa j) s))
  have h := Ito.measurable_stopped_of_agree (X := fun s ω => Coupling.stateAt W VL VR s ω) hσ hK hG0
    ((0, xL, xR) : ℝ × (Fin (nL + 1) → ℝ) × (Fin (nR + 1) → ℝ)) (fun ω hω s hs => ?_) (fun ω hω => ?_) r
  · convert h using 2 with ω
    by_cases hω : ω ∈ G <;> simp [stS, hω]
  · have hsζ : (s : ℝ≥0∞) < ζ ω :=
      lt_of_le_of_lt (by exact_mod_cast hs) (angLoc_lt_lifetime (hgood ω hω))
    simp only [killedAt, hsζ, ↓reduceIte, Coupling.stateAt]
  · have hsub : Iic (angLoc G T W VL VR B ζ n ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs =>
      lt_of_le_of_lt (by exact_mod_cast hs) (angLoc_lt_lifetime (hgood ω hω))
    exact (continuousOn_stateAt_ang hgood hω).mono hsub

include hE hGm hGc hgood hT in
theorem measurable_bandI (n : ℕ) (t : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P t] (bandI κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n) t) := by
  have hprog : IsStronglyProgressive (usualAugmentation 𝓕 P)
      (stS xL xR G W VL VR (angLoc G T W VL VR B ζ n)) :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun r => (measurable_stS hE hGm hGc hgood hT n r).stronglyMeasurable) (continuous_stS hgood n)
  have hj : StronglyMeasurable[MeasurableSpace.prod _ (usualAugmentation 𝓕 P t)]
      fun p : Set.Iic t × Ω => genSt κ ρL ρR hB' hB'' (stS xL xR G W VL VR (angLoc G T W VL VR B ζ n) p.1 p.2) :=
    ((measurable_genSt κ ρL ρR continuous_hB' continuous_hB'').comp (hprog t).measurable).stronglyMeasurable
  exact (@Girsanov.stronglyMeasurable_integral_comp_aux Ω (usualAugmentation 𝓕 P t) t
    (fun u ω => genSt κ ρL ρR hB' hB'' (stS xL xR G W VL VR (angLoc G T W VL VR B ζ n) u ω)) hj id
    measurable_id).measurable

end Meas

end BandCoord

/-! ### The band observable and its generators -/

section Obs

variable (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (ρL : Fin (nL + 1) → ℝ)
  (ρR : Fin (nR + 1) → ℝ)

/-- The band observable `h(U) − I`. -/
def bandΦ (q : SCoord nL (nR + 1) × ℝ) : ℝ := hB (angU κ xL xR ρL ρR q) - q.1.2.2

theorem contDiff_coordI {n : WithTop ℕ∞} : ContDiff ℝ n fun q : SCoord nL (nR + 1) × ℝ => q.1.2.2 := by
  fun_prop

theorem contDiffOn_bandΦ : ContDiffOn ℝ 3 (bandΦ κ xL xR ρL ρR) angRegion :=
  (contDiffOn_comp_angU κ xL xR ρL ρR (contDiff_hB.of_le (by simp))).sub contDiff_coordI.contDiffOn

theorem contDiffOn_bandΦ_sq :
    ContDiffOn ℝ 3 (fun q => bandΦ κ xL xR ρL ρR q * bandΦ κ xL xR ρL ρR q) angRegion :=
  (contDiffOn_bandΦ κ xL xR ρL ρR).mul (contDiffOn_bandΦ κ xL xR ρL ρR)

omit κ xL xR ρL ρR in
theorem itoGen_coordI (p : SCoord nL (nR + 1) × ℝ) (v : SCoord nL (nR + 1)) :
    Ito.itoGen (fun q : SCoord nL (nR + 1) × ℝ => q.1.2.2) p v = v.2.2 := by
  have hd : DifferentiableAt ℝ (fun q : SCoord nL (nR + 1) × ℝ => q.1.2.2) p :=
    (contDiff_coordI (n := 1)).differentiable (by norm_num) p
  have h1 : Ito.partialFst (fun q : SCoord nL (nR + 1) × ℝ => q.1.2.2) p v = v.2.2 := by
    refine Ito.partialFst_eq_of_hasDerivAt hd ?_
    have : (fun t : ℝ => ((p.1 + t • v, p.2) : SCoord nL (nR + 1) × ℝ).1.2.2) = fun t => p.1.2.2 + t * v.2.2 := by
      funext t; simp [smul_eq_mul]
    rw [this]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v.2.2).const_add p.1.2.2
  have h2 : Ito.partialSndSnd (fun q : SCoord nL (nR + 1) × ℝ => q.1.2.2) p = 0 := by
    refine Ito.partialSndSnd_eq_of_hasDerivAt (contDiff_coordI.contDiffAt) (g := fun _ => 0) ?_
      (hasDerivAt_const _ _)
    refine Eventually.of_forall fun y => ?_
    refine Ito.partialSnd_eq_of_hasDerivAt ((contDiff_coordI (n := 1)).differentiable (by norm_num) _) ?_
    simpa using hasDerivAt_const y p.1.2.2
  rw [Ito.itoGen, h1, h2]; ring

omit κ xL xR ρL ρR in
theorem partialSnd_coordI (p : SCoord nL (nR + 1) × ℝ) :
    Ito.partialSnd (fun q : SCoord nL (nR + 1) × ℝ => q.1.2.2) p = 0 := by
  refine Ito.partialSnd_eq_of_hasDerivAt ((contDiff_coordI (n := 1)).differentiable (by norm_num) _) ?_
  simpa using hasDerivAt_const p.2 p.1.2.2

variable {κ xL xR ρL ρR} {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
include hp

theorem itoGen_bandΦ_path (hκ : 0 ≤ κ) (hx : 0 < xR 0 - xL 0) (I c : ℝ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) :
    Ito.itoGen (bandΦ κ xL xR ρL ρR) (pathCoord vL vR b I t)
        (angDens (w t) (fun i => vL i t) (fun j => vR j t) c) =
      genExpr κ ρL ρR hB' hB'' w vL vR t - c := by
  have hD : 0 < gapD (pathCoord vL vR b I t) := hx.trans_le (le_gapAt hp ht)
  have h1 : ContDiffAt ℝ 2 (fun q => hB (angU κ xL xR ρL ρR q)) (pathCoord vL vR b I t) :=
    (contDiff_hB.of_le (by simp)).contDiffAt.comp _ (contDiffAt_angU κ xL xR ρL ρR hD)
  rw [show bandΦ κ xL xR ρL ρR = fun q => hB (angU κ xL xR ρL ρR q) - q.1.2.2 from rfl,
    itoGen_sub h1 contDiff_coordI.contDiffAt, itoGen_coordI,
    itoGen_pathCoord_eq hp hκ hx (contDiff_hB.of_le (by simp)) hasDerivAt_hB hasDerivAt_hB' I c ht]
  rfl

theorem partialSnd_bandΦ_path (hx : 0 < xR 0 - xL 0) (I : ℝ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) :
    Ito.partialSnd (bandΦ κ xL xR ρL ρR) (pathCoord vL vR b I t) =
      hB' (angAt w vL vR t) * (Real.sqrt κ / gapAt vL vR t) := by
  have hD : 0 < gapD (pathCoord vL vR b I t) := hx.trans_le (le_gapAt hp ht)
  have hdU := (contDiffAt_angU κ xL xR ρL ρR (n := 1) hD).differentiableAt (by norm_num)
  have h1 : DifferentiableAt ℝ (fun q => hB (angU κ xL xR ρL ρR q)) (pathCoord vL vR b I t) :=
    (hasDerivAt_hB _).differentiableAt.comp _ hdU
  rw [show bandΦ κ xL xR ρL ρR = fun q => hB (angU κ xL xR ρL ρR q) - q.1.2.2 from rfl,
    partialSnd_sub h1 ((contDiff_coordI (n := 1)).differentiable (by norm_num) _), partialSnd_coordI,
    partialSnd_comp_of_hasDerivAt hdU (hasDerivAt_hB _), partialSnd_angU κ xL xR ρL ρR hD,
    angU_pathCoord hp I ht]
  simp only [sub_zero]
  rfl

theorem itoGen_bandΦ_sq_path (hκ : 0 ≤ κ) (hx : 0 < xR 0 - xL 0) (I : ℝ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) :
    Ito.itoGen (fun q => bandΦ κ xL xR ρL ρR q * bandΦ κ xL xR ρL ρR q) (pathCoord vL vR b I t)
        (angDens (w t) (fun i => vL i t) (fun j => vR j t) (genExpr κ ρL ρR hB' hB'' w vL vR t)) =
      κ * hB' (angAt w vL vR t) ^ 2 / gapAt vL vR t ^ 2 := by
  have hD : 0 < gapD (pathCoord vL vR b I t) := hx.trans_le (le_gapAt hp ht)
  have hc := (contDiffOn_bandΦ κ xL xR ρL ρR).contDiffAt (isOpen_angRegion.mem_nhds hD)
  have hc2 : ContDiffAt ℝ 2 (bandΦ κ xL xR ρL ρR) (pathCoord vL vR b I t) := hc.of_le (by norm_num)
  rw [Ito.itoGen_mul hc2 hc2, itoGen_bandΦ_path hp hκ hx I _ ht, partialSnd_bandΦ_path hp hx I ht,
    sub_self, mul_zero, zero_add, zero_add]
  have hD' : gapAt vL vR t ≠ 0 := hD.ne'
  field_simp
  rw [Real.sq_sqrt hκ]

end Obs

/-! ### The band martingales -/

section BandMartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The stopped band process `N_t = h(U_{t∧σ_n}) − I_{t∧σ_n}`. -/
def bandN (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin (nR + 1) → ℝ) (G : Set Ω) (T : ℕ → Ω → ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  bandΦ κ xL xR ρL ρR (coordA xL xR G VL VR (bandI κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n))
    (min t (angLoc G T W VL VR B ζ n ω)) ω, Sec2.TwoSeed.brownG G B (min t (angLoc G T W VL VR B ζ n ω)) ω)

/-- Its compensator `J_t = ∫₀^{t∧σ_n} κ h'(U)² D^{-2}` (as the integrated generator of `N²`). -/
def bandJ (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin (nR + 1) → ℝ) (G : Set Ω) (T : ℕ → Ω → ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..(min t (angLoc G T W VL VR B ζ n ω) : ℝ≥0),
    Ito.itoGen (fun q => bandΦ κ xL xR ρL ρR q * bandΦ κ xL xR ρL ρR q)
      (coordA xL xR G VL VR (bandI κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n)) s.toNNReal ω,
        Sec2.TwoSeed.brownG G B s.toNNReal ω)
      (densA G W VL VR (bandC κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n)) s ω)

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ}
  {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
  {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω} {T : ℕ → Ω → ℝ≥0}

section Path

variable (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω) (n : ℕ)
include hgood

/-- On `[0, σ_n]` the generator of `N` vanishes along the path. -/
theorem itoGen_bandΦ_eq_zero (hκ : 0 ≤ κ) (hx : 0 < xR 0 - xL 0) {ω : Ω} (hω : ω ∈ G) {s : ℝ}
    (hs : s ∈ Icc 0 (angLoc G T W VL VR B ζ n ω : ℝ)) :
    Ito.itoGen (bandΦ κ xL xR ρL ρR)
      (coordA xL xR G VL VR (bandI κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n)) s.toNNReal ω,
        Sec2.TwoSeed.brownG G B s.toNNReal ω)
      (densA G W VL VR (bandC κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n)) s ω) = 0 := by
  have hsζ := Sec2.toNNReal_lt_of_mem_Icc (angLoc_lt_lifetime (n := n) (G := G) (hgood ω hω)) hs
  have h := itoGen_bandΦ_path (hgood ω hω).1 hκ hx
    (bandI κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n) s.toNNReal ω)
    (bandC κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n) s ω) hsζ
  simp only [coordA, densA, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
  refine h.trans ?_
  rw [bandC_eq n hω hs]
  simp only [genExpr, Real.toNNReal_coe, sub_self]

/-- On `[0, σ_n]` the generator of `N²` is `κ h'(U)² D^{-2}`. -/
theorem itoGen_bandΦ_sq_eq (hκ : 0 ≤ κ) (hx : 0 < xR 0 - xL 0) {ω : Ω} (hω : ω ∈ G) {s : ℝ}
    (hs : s ∈ Icc 0 (angLoc G T W VL VR B ζ n ω : ℝ)) :
    Ito.itoGen (fun q => bandΦ κ xL xR ρL ρR q * bandΦ κ xL xR ρL ρR q)
      (coordA xL xR G VL VR (bandI κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n)) s.toNNReal ω,
        Sec2.TwoSeed.brownG G B s.toNNReal ω)
      (densA G W VL VR (bandC κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n)) s ω) =
      κ * hB' (angAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s.toNNReal) ^ 2 /
        gapAt (fun i t => VL i t ω) (fun j t => VR j t ω) s.toNNReal ^ 2 := by
  have hsζ := Sec2.toNNReal_lt_of_mem_Icc (angLoc_lt_lifetime (n := n) (G := G) (hgood ω hω)) hs
  have h := itoGen_bandΦ_sq_path (hgood ω hω).1 hκ hx
    (bandI κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n) s.toNNReal ω) hsζ
  have e : genExpr κ ρL ρR hB' hB'' (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (s.toNNReal : ℝ) =
      genExpr κ ρL ρR hB' hB'' (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s := by
    simp only [genExpr, Real.toNNReal_coe]
  simp only [coordA, densA, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
  rw [bandC_eq n hω hs, ← e]
  exact h

/-- **The compensator increments are controlled by the angular clock**: for `s ≤ t`,
`J_t − J_s ≤ κ K'² ∫_{s∧σ}^{σ} D^{-2}`. -/
theorem bandJ_sub_le (hκ : 0 ≤ κ) (hx : 0 < xR 0 - xL 0) {K' : ℝ} (hK' : ∀ u, |hB' u| ≤ K') {ω : Ω}
    (hω : ω ∈ G) {s t : ℝ≥0} (hst : s ≤ t) :
    bandJ κ xL xR ρL ρR G T W VL VR B ζ n t ω - bandJ κ xL xR ρL ρR G T W VL VR B ζ n s ω ≤
      κ * K' ^ 2 * ∫ u in (min s (angLoc G T W VL VR B ζ n ω) : ℝ)..(angLoc G T W VL VR B ζ n ω : ℝ),
        (VR 0 u.toNNReal ω - VL 0 u.toNNReal ω)⁻¹ ^ 2 := by
  set σ := angLoc G T W VL VR B ζ n ω with hσdef
  have hp := (hgood ω hω).1
  have hσζ : (σ : ℝ≥0∞) < ζ ω := angLoc_lt_lifetime (hgood ω hω)
  set g : ℝ → ℝ := fun u => Ito.itoGen (fun q => bandΦ κ xL xR ρL ρR q * bandΦ κ xL xR ρL ρR q)
      (coordA xL xR G VL VR (bandI κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n)) u.toNNReal ω,
        Sec2.TwoSeed.brownG G B u.toNNReal ω)
      (densA G W VL VR (bandC κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n)) u ω) with hgdef
  set g' : ℝ → ℝ := fun u => κ * hB' (angAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) u.toNNReal) ^ 2 /
      gapAt (fun i t => VL i t ω) (fun j t => VR j t ω) u.toNNReal ^ 2 with hg'def
  have hgg : EqOn g g' (Icc 0 (σ : ℝ)) := fun u hu => itoGen_bandΦ_sq_eq hgood n hκ hx hω hu
  have hg'c : ContinuousOn g' (Icc 0 (σ : ℝ)) :=
    (continuousOn_const.mul ((continuous_hB'.comp_continuousOn (continuousOn_angAt hp hx hσζ)).pow 2)).div
      ((continuousOn_gapAt hp hσζ).pow 2) fun u hu => pow_ne_zero 2 (gapAt_pos hp hx hσζ hu).ne'
  have hgi : IntervalIntegrable g volume 0 σ := by
    refine (hg'c.intervalIntegrable_of_Icc σ.coe_nonneg).congr fun u hu => ?_
    rw [uIoc_of_le σ.coe_nonneg] at hu
    exact (hgg ⟨hu.1.le, hu.2⟩).symm
  have hsub : ∀ r : ℝ≥0, uIcc (0 : ℝ) (min (r : ℝ) σ) ⊆ uIcc 0 (σ : ℝ) := fun r => by
    rw [uIcc_of_le (le_min r.coe_nonneg σ.coe_nonneg), uIcc_of_le σ.coe_nonneg]
    exact Icc_subset_Icc_right (min_le_right _ _)
  have hJ : bandJ κ xL xR ρL ρR G T W VL VR B ζ n t ω - bandJ κ xL xR ρL ρR G T W VL VR B ζ n s ω =
      ∫ u in (min s σ : ℝ)..(min t σ : ℝ), g u := by
    simp only [bandJ, ← hσdef, NNReal.coe_min]
    exact intervalIntegral.integral_interval_sub_left (hgi.mono_set (hsub t)) (hgi.mono_set (hsub s))
  have hcr := intervalIntegrable_clockRate hp hx hσζ
  have hle : ∀ u ∈ Icc (0 : ℝ) σ, g u ≤ κ * K' ^ 2 * (VR 0 u.toNNReal ω - VL 0 u.toNNReal ω)⁻¹ ^ 2 := by
    intro u hu
    rw [hgg hu]
    simp only [hg'def, gapAt]
    have h1 : hB' (angAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) u.toNNReal) ^ 2 ≤ K' ^ 2 :=
      sq_le_sq' (abs_le.1 (hK' _)).1 (abs_le.1 (hK' _)).2
    rw [div_eq_mul_inv, inv_pow]
    gcongr
  have hmst : (min s σ : ℝ) ≤ min t σ := by exact_mod_cast min_le_min_right σ hst
  have hmt : (min t σ : ℝ) ≤ σ := by exact_mod_cast min_le_right t σ
  have hm0 : (0 : ℝ) ≤ min s σ := (min s σ).coe_nonneg
  have hint_sub : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ σ → ∀ f : ℝ → ℝ, IntervalIntegrable f volume 0 σ →
      IntervalIntegrable f volume a b := fun {a b} ha hab hb f hf =>
    hf.mono_set (by rw [uIcc_of_le hab, uIcc_of_le σ.coe_nonneg]; exact Icc_subset_Icc ha hb)
  rw [hJ]
  calc ∫ u in (min s σ : ℝ)..(min t σ : ℝ), g u
      ≤ ∫ u in (min s σ : ℝ)..(min t σ : ℝ), κ * K' ^ 2 * (VR 0 u.toNNReal ω - VL 0 u.toNNReal ω)⁻¹ ^ 2 :=
        intervalIntegral.integral_mono_on hmst (hint_sub hm0 hmst hmt g hgi)
          (hint_sub hm0 hmst hmt _ (hcr.const_mul _)) fun u hu =>
            hle u ⟨hm0.trans hu.1, hu.2.trans hmt⟩
    _ ≤ ∫ u in (min s σ : ℝ)..(σ : ℝ), κ * K' ^ 2 * (VR 0 u.toNNReal ω - VL 0 u.toNNReal ω)⁻¹ ^ 2 :=
        intervalIntegral.integral_mono_interval le_rfl hmst hmt
          (ae_of_all _ fun u => by positivity) (hint_sub hm0 (hmst.trans hmt) le_rfl _ (hcr.const_mul _))
    _ = _ := intervalIntegral.integral_const_mul _ _

end Path

section Mart

variable (hκ : 0 < κ) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T) (hx : 0 < xR 0 - xL 0)
  {K' K'' : ℝ} (hK' : ∀ u, |hB' u| ≤ K') (hK'' : ∀ u, |hB'' u| ≤ K'')

include hκ hE hGm hGc hgood hT hx hK' hK'' in
/-- **The band process is a martingale.** -/
theorem martingale_bandN (n : ℕ) :
    Martingale (bandN κ xL xR ρL ρR G T W VL VR B ζ n) (usualAugmentation 𝓕 P) P := by
  have hM := martingale_angLoc hE hGm hGc hgood hT hx (contDiffOn_bandΦ κ xL xR ρL ρR) n
    (I := bandI κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n))
    (c := bandC κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n))
    (KI := bandKc κ xL xR ρL ρR K' K'' n) (Kc := bandKc κ xL xR ρL ρR K' K'' n) (fun _ _ _ _ => rfl)
    (fun ω hω => intervalIntegrable_bandC hgood n hx hω)
    (fun ω hω => integral_abs_bandC_le hgood n hκ.le hx hK' hK'' hω)
    (fun ω hω t ht => abs_bandI_le hgood n hκ.le hx hK' hK'' hω ht)
    ⟨_, measurable_bandI hE hGm hGc hgood hT n, fun _ _ _ _ => rfl⟩
    (fun ω hω => continuousOn_bandI hgood n hx hω)
  convert hM using 1
  funext t ω
  have h0 : ∫ s in (0 : ℝ)..(min t (angLoc G T W VL VR B ζ n ω) : ℝ≥0), Ito.itoGen (bandΦ κ xL xR ρL ρR)
      (coordA xL xR G VL VR (bandI κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n)) s.toNNReal ω,
        Sec2.TwoSeed.brownG G B s.toNNReal ω)
      (densA G W VL VR (bandC κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n)) s ω) = 0 := by
    by_cases hω : ω ∈ G
    · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_]
      · simp
      rw [uIcc_of_le (min t (angLoc G T W VL VR B ζ n ω)).coe_nonneg] at hs
      exact itoGen_bandΦ_eq_zero hgood n hκ.le hx hω
        ⟨hs.1, hs.2.trans (by exact_mod_cast min_le_right t (angLoc G T W VL VR B ζ n ω))⟩
    · simp [angLoc_of_not_mem hω]
  rw [h0, sub_zero]
  rfl

include hκ hE hGm hGc hgood hT hx hK' hK'' in
/-- **`N² − J` is a martingale.** -/
theorem martingale_bandN_sq (n : ℕ) :
    Martingale (fun t ω => bandN κ xL xR ρL ρR G T W VL VR B ζ n t ω ^ 2 -
      bandJ κ xL xR ρL ρR G T W VL VR B ζ n t ω) (usualAugmentation 𝓕 P) P := by
  have hM := martingale_angLoc hE hGm hGc hgood hT hx (contDiffOn_bandΦ_sq κ xL xR ρL ρR) n
    (I := bandI κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n))
    (c := bandC κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n))
    (KI := bandKc κ xL xR ρL ρR K' K'' n) (Kc := bandKc κ xL xR ρL ρR K' K'' n) (fun _ _ _ _ => rfl)
    (fun ω hω => intervalIntegrable_bandC hgood n hx hω)
    (fun ω hω => integral_abs_bandC_le hgood n hκ.le hx hK' hK'' hω)
    (fun ω hω t ht => abs_bandI_le hgood n hκ.le hx hK' hK'' hω ht)
    ⟨_, measurable_bandI hE hGm hGc hgood hT n, fun _ _ _ _ => rfl⟩
    (fun ω hω => continuousOn_bandI hgood n hx hω)
  convert hM using 1
  funext t ω
  simp only [bandN, bandJ, sq]

include hκ hE hGc hgood hx hK' hK'' in
theorem abs_bandN_le (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    |bandN κ xL xR ρL ρR G T W VL VR B ζ n t ω| ≤ 1 + bandKc κ xL xR ρL ρR K' K'' n := by
  have hP := hE.1.isProbabilityMeasure'
  obtain ⟨ω₀, hω₀⟩ : G.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, compl_empty, measure_univ] at hGc
    exact one_ne_zero hGc
  have hKc : 0 ≤ bandKc κ xL xR ρL ρR K' K'' n :=
    (abs_nonneg _).trans (abs_bandI_le hgood n hκ.le hx hK' hK'' hω₀ (t := 0) bot_le)
  by_cases hω : ω ∈ G
  · simp only [bandN, bandΦ, coordA, hω, ↓reduceIte]
    have h1 := abs_bandI_le hgood n hκ.le hx hK' hK'' hω (min_le_right t (angLoc G T W VL VR B ζ n ω))
    set U := angU κ xL xR ρL ρR ((fun i => VL i (min t (angLoc G T W VL VR B ζ n ω)) ω,
      fun j => VR j (min t (angLoc G T W VL VR B ζ n ω)) ω,
      bandI κ xL xR ρL ρR G W VL VR (angLoc G T W VL VR B ζ n) (min t (angLoc G T W VL VR B ζ n ω)) ω),
      Sec2.TwoSeed.brownG G B (min t (angLoc G T W VL VR B ζ n ω)) ω)
    have h2 := hB_nonneg U
    have h3 := hB_le_one U
    rw [abs_le] at h1 ⊢
    constructor <;> linarith [h1.1, h1.2]
  · simp only [bandN, bandΦ, coordA, hω, ↓reduceIte, sub_zero]
    set U := angU κ xL xR ρL ρR ((xL, xR, 0), Sec2.TwoSeed.brownG G B (min t (angLoc G T W VL VR B ζ n ω)) ω)
    have h2 := hB_nonneg U
    have h3 := hB_le_one U
    rw [abs_le]
    constructor <;> linarith

include hκ hE hGm hGc hgood hT hx hK' hK'' in
/-- **The `L²` increment identity** `E (N_t − N_s)² = E (J_t − J_s)`, `s ≤ t`. -/
theorem integral_sq_sub_bandN (n : ℕ) {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ ω, (bandN κ xL xR ρL ρR G T W VL VR B ζ n t ω - bandN κ xL xR ρL ρR G T W VL VR B ζ n s ω) ^ 2 ∂P =
      ∫ ω, (bandJ κ xL xR ρL ρR G T W VL VR B ζ n t ω - bandJ κ xL xR ρL ρR G T W VL VR B ζ n s ω) ∂P := by
  have hP := hE.1.isProbabilityMeasure'
  have hM := martingale_bandN hκ hE hGm hGc hgood hT hx hK' hK'' n
  have hM2 := martingale_bandN_sq hκ hE hGm hGc hgood hT hx hK' hK'' n
  set N := bandN κ xL xR ρL ρR G T W VL VR B ζ n with hNdef
  set J := bandJ κ xL xR ρL ρR G T W VL VR B ζ n with hJdef
  set C := 1 + bandKc κ xL xR ρL ρR K' K'' n
  have hb : ∀ r ω, |N r ω| ≤ C := abs_bandN_le hκ hE hGc hgood hx hK' hK'' n
  have hNm : ∀ r, StronglyMeasurable[usualAugmentation 𝓕 P r] (N r) := fun r => hM.1 r
  have hNm' : ∀ r, StronglyMeasurable (N r) := fun r => (hNm r).mono ((usualAugmentation 𝓕 P).le r)
  have hint : ∀ {f : Ω → ℝ} {c : ℝ}, StronglyMeasurable f → (∀ ω, |f ω| ≤ c) → Integrable f P :=
    fun hf hfc => Integrable.of_bound hf.aestronglyMeasurable _
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hfc ω)
  have hNN : ∀ r r', Integrable (fun ω => N r ω * N r' ω) P := fun r r' =>
    hint ((hNm' r).mul (hNm' r')) (c := C * C) fun ω => by
      rw [abs_mul]; exact mul_le_mul (hb r ω) (hb r' ω) (abs_nonneg _) ((abs_nonneg _).trans (hb r ω))
  have hN2 : ∀ r, Integrable (fun ω => N r ω ^ 2) P := fun r => by
    simpa only [sq] using hNN r r
  have hJi : ∀ r, Integrable (J r) P := fun r => by
    have h := (hN2 r).sub (hM2.integrable r)
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only [Pi.sub_apply]; ring
  -- `E[N_s N_t] = E[N_s²]`
  have hcross : ∫ ω, N s ω * N t ω ∂P = ∫ ω, N s ω * N s ω ∂P := by
    have hce : P[N t | usualAugmentation 𝓕 P s] =ᵐ[P] N s := hM.2 s t hst
    have hpull : P[(N s) * (N t) | usualAugmentation 𝓕 P s] =ᵐ[P] (N s) * P[N t | usualAugmentation 𝓕 P s] :=
      condExp_stronglyMeasurable_mul_of_bound ((usualAugmentation 𝓕 P).le s) (hNm s) (hM.integrable t) C
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hb s ω)
    calc ∫ ω, N s ω * N t ω ∂P = ∫ ω, (P[(N s) * (N t) | usualAugmentation 𝓕 P s]) ω ∂P :=
          (integral_condExp ((usualAugmentation 𝓕 P).le s)).symm
      _ = ∫ ω, N s ω * N s ω ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hpull, hce] with ω h1 h2
          rw [h1, Pi.mul_apply, h2]
  -- `E[N_t² − J_t] = E[N_s² − J_s]`
  have hmart : ∫ ω, (N t ω ^ 2 - J t ω) ∂P = ∫ ω, (N s ω ^ 2 - J s ω) ∂P := by
    have h := hM2.setIntegral_eq hst MeasurableSet.univ
    rw [setIntegral_univ, setIntegral_univ] at h
    exact h.symm
  rw [integral_sub (hN2 t) (hJi t), integral_sub (hN2 s) (hJi s)] at hmart
  have hexp : (fun ω => (N t ω - N s ω) ^ 2) = fun ω => N t ω ^ 2 - 2 * (N s ω * N t ω) + N s ω * N s ω := by
    funext ω; ring
  have h1 : Integrable (fun ω => N t ω ^ 2 - 2 * (N s ω * N t ω)) P := (hN2 t).sub ((hNN s t).const_mul 2)
  have h2 : Integrable (fun ω => 2 * (N s ω * N t ω)) P := (hNN s t).const_mul 2
  rw [hexp, integral_add (f := fun ω => N t ω ^ 2 - 2 * (N s ω * N t ω)) (g := fun ω => N s ω * N s ω) h1 (hNN s s),
    integral_sub (f := fun ω => N t ω ^ 2) (g := fun ω => 2 * (N s ω * N t ω)) (hN2 t) h2,
    integral_const_mul, hcross, integral_sub (hJi t) (hJi s)]
  have : ∫ ω, N s ω * N s ω ∂P = ∫ ω, N s ω ^ 2 ∂P := by simp only [sq]
  rw [this]
  linarith

end Mart

end BandMartingale

end Clock

end Sec7

end InteractingSLE
