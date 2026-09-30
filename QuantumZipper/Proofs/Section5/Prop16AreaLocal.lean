import QuantumZipper.Proofs.LQG.Measurability
import QuantumZipper.Proofs.Section5.TVLocal
import QuantumZipper.LQG.Local

/-!
# Proposition 1.6, D4-a (part 1): area pairings are measurable functions of `locField`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.4–1.5 and the proof of
Proposition 1.6 (p. 25 of the PDF): the quantum area measure of a field restricted to a bounded
set is a (measurable) function of the field near that set, so total-variation convergence of the
local field laws transfers to the laws of the area measures. Blueprint
`SECTION5_BLUEPRINT.md` D4 / `handoff/S5-PLAN.md` D4-a ("A4-style measurability").

This file is the A4-style factorization (blueprint A4, `Proofs/Field/Factorization.lean`) of the
area pairings through the local coordinates `TV.locField N`:

* `locRecon N` rebuilds a field sample from `locField N x`; it agrees with `x` at every dyadic
  folded circle inside `closedBall 0 N` (`locField_locRecon`);
* `avgReg x k z` for `k ≥ 1`, `‖z‖ + 1 < N`, and hence `∫ g d(areaApprox γ x k)` for `g`
  supported in `ball 0 (N - 1)`, only depend on `locField N x`;
* `locArea γ R f` is an explicit measurable function of the sample (a supremum over cut-offs
  `bump R n` of `ℍ ∩ ball 0 R` of `liminf`s of approximating integrals, split into positive and
  negative parts, with the Bochner junk value `0` when `f` is not integrable), and
  `∫ f dμ = locArea γ R f x` for every vague limit `μ` of `areaApprox γ x` on any `V` with
  `ball 0 R ∩ ℍ ⊆ V ⊆ ℍ` (`integral_eq_locArea`); this covers both `qAreaMeasureOn` (random local
  domains) and `qAreaMeasure` (`V = ℍ`), and test functions whose support meets `ℝ`.

The measure-theoretic argument is an own elementary proof (monotone convergence against the
cut-offs `openBump`, `Proofs/LQG/Measurability.lean`); no published proof spells it out.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Area

open TV Factorization

/-- The `i`-th dyadic folded circle read by `coords`. -/
abbrev circ (i : ℕ) : Measure ℂ := foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)

open Classical in
/-- Reconstruction of a field sample from its local coordinates `locField N x` (junk `0` at every
measure that is not a dyadic folded circle inside `closedBall 0 N`). -/
def locRecon (N : ℕ) (y : ℕ → ℝ) : FieldSample := fun μ =>
  if h : ∃ i, inBall N i ∧ circ i = μ then y h.choose else 0

theorem measurable_locRecon (N : ℕ) : Measurable (locRecon N) := by
  refine measurable_pi_iff.2 fun μ => ?_
  unfold locRecon
  by_cases h : ∃ i, inBall N i ∧ circ i = μ
  · simp only [dif_pos h]; exact measurable_pi_apply _
  · simp only [dif_neg h]; exact measurable_const

theorem locRecon_apply (N : ℕ) (x : FieldSample) {i : ℕ} (hi : inBall N i) :
    locRecon N (locField N x) (circ i) = x (circ i) := by
  have h : ∃ j, inBall N j ∧ circ j = circ i := ⟨i, hi, rfl⟩
  unfold locRecon
  rw [dif_pos h]
  have hs := h.choose_spec
  have h1 : locField N x h.choose = coords x h.choose := if_pos hs.1
  rw [h1]
  exact congrArg x hs.2

theorem locField_locRecon (N : ℕ) (x : FieldSample) :
    locField N (locRecon N (locField N x)) = locField N x := by
  funext i
  by_cases hi : inBall N i
  · have h1 : locField N (locRecon N (locField N x)) i = coords (locRecon N (locField N x)) i :=
      if_pos hi
    have h2 : locField N x i = coords x i := if_pos hi
    rw [h1, h2]
    exact locRecon_apply N x hi
  · have h1 : locField N (locRecon N (locField N x)) i = 0 := if_neg hi
    have h2 : locField N x i = 0 := if_neg hi
    rw [h1, h2]

theorem radius_le_half {k : ℕ} (hk : 1 ≤ k) : radius k ≤ 1 / 2 := by
  unfold radius
  calc (2 : ℝ)⁻¹ ^ k ≤ (2 : ℝ)⁻¹ ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
    _ = 1 / 2 := by norm_num

/-- Locality of `avgReg`: at scales `k ≥ 1` and points with `‖z‖ + 1 < N`, it only reads the
coordinates recorded in `locField N`. -/
theorem avgReg_eq_of_locField_eq {N : ℕ} {x x' : FieldSample}
    (hxx : locField N x = locField N x') {k : ℕ} (hk : 1 ≤ k) {z : ℂ} (hz : ‖z‖ + 1 < N) :
    avgReg x k z = avgReg x' k z := by
  unfold avgReg
  have hev : (fun n => x (foldedCircle (dyadicRoundC n z) (radius k))) =ᶠ[atTop]
      (fun n => x' (foldedCircle (dyadicRoundC n z) (radius k))) := by
    have hball : ∀ᶠ n in atTop, dist (dyadicRoundC n z) z < 1 / 2 :=
      (Metric.tendsto_nhds.1 (RegClosure.tendsto_dyadicRoundC z)) (1 / 2) (by norm_num)
    filter_upwards [hball] with n hn
    obtain ⟨i, hi⟩ := dyadicIndex_surj n k z
    have hin : inBall N i := by
      show ‖(dyadicIndex i).1‖ + radius (dyadicIndex i).2 ≤ (N : ℝ)
      rw [hi]
      dsimp only
      have h1 := norm_sub_norm_le (dyadicRoundC n z) z
      rw [dist_eq_norm] at hn
      have h2 := radius_le_half hk
      linarith
    have h := congrFun hxx i
    have e1 : locField N x i = coords x i := if_pos hin
    have e2 : locField N x' i = coords x' i := if_pos hin
    rw [e1, e2] at h
    simp only [coords, hi] at h
    exact h
  simp only [limUnder, Filter.map_congr hev]

theorem measurable_areaDensity (γ : ℝ) (k : ℕ) (y : FieldSample) :
    Measurable fun z => radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg y k z) :=
  (Real.measurable_exp.comp (((measurable_avgReg k).comp
    (measurable_const.prodMk measurable_id)).const_mul γ)).const_mul _

/-- Locality of the approximating area integrals. -/
theorem integral_areaApprox_eq_of_locField_eq {N : ℕ} {x x' : FieldSample}
    (hxx : locField N x = locField N x') {k : ℕ} (hk : 1 ≤ k) {g : ℂ → ℝ}
    (hg : ∀ z, g z ≠ 0 → ‖z‖ + 1 < N) (γ : ℝ) :
    ∫ z, g z ∂areaApprox γ x k = ∫ z, g z ∂areaApprox γ x' k := by
  have h0 : ∀ (y : FieldSample) z, 0 ≤ radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg y k z) :=
    fun _ _ => mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le
  unfold areaApprox
  rw [GoodSample.integral_withDensity_ofReal (measurable_areaDensity γ k x) (h0 x) g,
    GoodSample.integral_withDensity_ofReal (measurable_areaDensity γ k x') (h0 x') g]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases h : g z = 0
  · simp [h]
  · show _ * g z = _ * g z
    rw [avgReg_eq_of_locField_eq hxx hk (hg z h)]

/-! ## The explicit measurable area pairing -/

/-- The half-ball `ball 0 R ∩ ℍ`. -/
def hball (R : ℕ) : Set ℂ := Metric.ball (0 : ℂ) R ∩ H

/-- Continuous cut-offs increasing to the indicator of `ball 0 R ∩ ℍ`. -/
def bump (R n : ℕ) : ℂ → ℝ := LQGMeas.openBump (hball R) n

/-- Candidate for `∫⁻ ofReal g dμ`: supremum over the cut-offs of the `liminf`s of the
approximating integrals. -/
def liApprox (γ : ℝ) (R : ℕ) (g : ℂ → ℝ) (x : FieldSample) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (LQGMeas.areaFun γ (fun z => g z * bump R n z) x)

/-- The measurable candidate for `∫ f dμ` (Bochner convention: `0` if not integrable). -/
def locArea (γ : ℝ) (R : ℕ) (f : ℂ → ℝ) (x : FieldSample) : ℝ :=
  if liApprox γ R (fun z => |f z|) x < ⊤ then
    (liApprox γ R (fun z => max (f z) 0) x).toReal -
      (liApprox γ R (fun z => max (-f z) 0) x).toReal
  else 0

theorem measurable_liApprox (γ : ℝ) (R : ℕ) {g : ℂ → ℝ} (hg : Measurable g) :
    Measurable (liApprox γ R g) :=
  Measurable.iSup fun n => ENNReal.measurable_ofReal.comp
    (LQGMeas.measurable_areaFun γ (hg.mul (LQGMeas.continuous_openBump _ n).measurable))

theorem measurable_locArea (γ : ℝ) (R : ℕ) {f : ℂ → ℝ} (hf : Measurable f) :
    Measurable (locArea γ R f) := by
  unfold locArea
  refine Measurable.ite (measurableSet_lt (measurable_liApprox γ R (continuous_abs.measurable.comp hf)) measurable_const) ?_
    measurable_const
  exact ((measurable_liApprox γ R (hf.max measurable_const)).ennreal_toReal).sub
    (measurable_liApprox γ R (hf.neg.max measurable_const)).ennreal_toReal

theorem norm_lt_of_bump_ne_zero {R n : ℕ} {z : ℂ} (h : bump R n z ≠ 0) : ‖z‖ < R := by
  have hz : z ∈ hball R :=
    LQGMeas.tsupport_openBump_subset _ n (subset_tsupport _ h)
  simpa using hz.1

theorem liApprox_congr {γ : ℝ} {R N : ℕ} (hRN : (R : ℝ) + 1 ≤ N) {x x' : FieldSample}
    (hxx : locField N x = locField N x') (g : ℂ → ℝ) :
    liApprox γ R g x = liApprox γ R g x' := by
  unfold liApprox LQGMeas.areaFun
  congr 1
  funext n
  congr 1
  have hev : (fun k => ∫ z, g z * bump R n z ∂areaApprox γ x k) =ᶠ[atTop]
      (fun k => ∫ z, g z * bump R n z ∂areaApprox γ x' k) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    refine integral_areaApprox_eq_of_locField_eq hxx hk (fun z hz => ?_) γ
    have := norm_lt_of_bump_ne_zero (right_ne_zero_of_mul hz)
    linarith
  simp only [Filter.liminf, Filter.map_congr hev]

theorem locArea_congr {γ : ℝ} {R N : ℕ} (hRN : (R : ℝ) + 1 ≤ N) {x x' : FieldSample}
    (hxx : locField N x = locField N x') (f : ℂ → ℝ) :
    locArea γ R f x = locArea γ R f x' := by
  unfold locArea
  rw [liApprox_congr hRN hxx, liApprox_congr hRN hxx, liApprox_congr hRN hxx]

/-- **A4-style factorization.** `locArea γ R f` is a function of the local coordinates
`locField N`, through the measurable map `locArea γ R f ∘ locRecon N`. -/
theorem locArea_eq_comp_locField {γ : ℝ} {R N : ℕ} (hRN : (R : ℝ) + 1 ≤ N) (f : ℂ → ℝ)
    (x : FieldSample) :
    locArea γ R f x = (locArea γ R f ∘ locRecon N) (locField N x) :=
  locArea_congr hRN (locField_locRecon N x).symm f

end Prop16Area

end QuantumZipper
