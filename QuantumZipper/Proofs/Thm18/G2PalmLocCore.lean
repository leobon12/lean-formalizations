import QuantumZipper.Proofs.Thm18.G2AgreeMass
import QuantumZipper.Proofs.Thm18.G3Fid2Region

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 locality of the cut length: the deterministic core

Sheffield, arXiv:1012.4797, proof of Prop. 5.5 (p. 65): the boundary length `ν_h[x + κ, 0]` is a
function of the field outside `B_κ(x)`. Here the deterministic half: for a good field sample `y`
(`IsLQGGood`), a far point `c`, a radius `ρ` and an interval `[a, b]` whose `w`-neighbourhood
stays at distance `> ρ + w` from `c`, the functional

  `locLen γ Y a b w = ⨅ j, liminf_k ∫⁻ trap_{w/(j+1)} d(bdryApprox γ Y k)`

(`trap_δ` the trapezoid, `1` on `[a, b]`, `0` off `(a − δ, b + δ)`) evaluated at the field `y`
read only on the folded circles missing `B(c, ρ)` (`restrictField (circOut c ρ c ρ) y`) equals
`ν_y[a, b]` (`locLen_restrict_eq`). Indeed near `[a, b]` the approximations of the restricted
field are those of `y` once `2^{-k} ≤ w` (`G3Fid.avgReg_gap_in`, the Duplantier–Sheffield
locality of circle averages), the vague limit gives the `liminf`, and the trapezoids decrease to
the indicator of `[a, b]`. `locLen` is measurable in the field (`measurable_locLen`), and the
restricted Palm field is measurable for the D3⁺ conditioning σ-algebra
(`measurable_restrict_xPalm`). No atomlessness of `ν_y` is needed.

Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G2PalmLoc

open S5.FieldLaw.Raw

local notation "Ω₀" => gffBase.Ω

/-! ## Trapezoid test functions -/

/-- The trapezoid: `1` on `[a, b]`, `0` off `(a − δ, b + δ)`, linear in between. -/
def trap (δ a b : ℝ) (t : ℝ) : ℝ :=
  max 0 (min 1 (min (1 + (t - a) / δ) (1 + (b - t) / δ)))

theorem continuous_trap (δ a b : ℝ) : Continuous (trap δ a b) := by
  unfold trap; fun_prop

theorem trap_nonneg (δ a b t : ℝ) : 0 ≤ trap δ a b t := le_max_left _ _

theorem trap_le_one (δ a b t : ℝ) : trap δ a b t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem trap_eq_one {δ a b t : ℝ} (hδ : 0 < δ) (ht : t ∈ Icc a b) : trap δ a b t = 1 := by
  have h1 : 0 ≤ (t - a) / δ := div_nonneg (by linarith [ht.1]) hδ.le
  have h2 : 0 ≤ (b - t) / δ := div_nonneg (by linarith [ht.2]) hδ.le
  unfold trap
  rw [min_eq_left (le_min (by linarith) (by linarith)), max_eq_right zero_le_one]

theorem trap_eq_zero {δ a b t : ℝ} (hδ : 0 < δ) (ht : t ∉ Ioo (a - δ) (b + δ)) :
    trap δ a b t = 0 := by
  unfold trap
  refine max_eq_left ?_
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at ht
  rcases ht with ht | ht
  · have : (t - a) / δ ≤ -1 := by rw [div_le_iff₀ hδ]; linarith
    exact (min_le_right _ _).trans ((min_le_left _ _).trans (by linarith))
  · have : (b - t) / δ ≤ -1 := by rw [div_le_iff₀ hδ]; linarith
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (by linarith))

theorem hasCompactSupport_trap {δ a b : ℝ} (hδ : 0 < δ) : HasCompactSupport (trap δ a b) :=
  HasCompactSupport.intro (isCompact_Icc (a := a - δ) (b := b + δ)) fun _ ht =>
    trap_eq_zero hδ fun h => ht (Ioo_subset_Icc_self h)

theorem trap_le_indicator {δ a b : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ENNReal.ofReal (trap δ a b t) ≤ (Icc (a - δ) (b + δ)).indicator 1 t := by
  by_cases ht : t ∈ Ioo (a - δ) (b + δ)
  · rw [indicator_of_mem (Ioo_subset_Icc_self ht), Pi.one_apply]
    exact ENNReal.ofReal_le_one.2 (trap_le_one _ _ _ _)
  · rw [trap_eq_zero hδ ht, ENNReal.ofReal_zero]; exact zero_le

theorem measurable_ofReal_trap (δ a b : ℝ) :
    Measurable fun t => ENNReal.ofReal (trap δ a b t) :=
  ENNReal.measurable_ofReal.comp (continuous_trap δ a b).measurable

/-- `⨅ⱼ ∫ trap_{w/(j+1)} dν = ν[a, b]` for a locally finite `ν`. -/
theorem iInf_lintegral_trap (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] {a b w : ℝ} (hw : 0 < w) :
    ⨅ j : ℕ, ∫⁻ t, ENNReal.ofReal (trap (w / (j + 1)) a b t) ∂ν = ν (Icc a b) := by
  have hδ : ∀ j : ℕ, 0 < w / (j + 1) := fun j => div_pos hw (Nat.cast_add_one_pos j)
  have h0 : Tendsto (fun j : ℕ => w / (j + 1)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul w
    rw [mul_zero] at this
    exact this.congr fun j => mul_one_div _ _
  refine le_antisymm ?_ (le_iInf fun j => ?_)
  · have hanti : Antitone fun j : ℕ => Icc (a - w / (j + 1)) (b + w / (j + 1)) := by
      intro j j' hjj'
      have : w / ((j' : ℝ) + 1) ≤ w / ((j : ℝ) + 1) :=
        div_le_div_of_nonneg_left hw.le (Nat.cast_add_one_pos j)
          (by exact_mod_cast Nat.add_le_add_right hjj' 1)
      exact Icc_subset_Icc (by linarith) (by linarith)
    have hI : ⋂ j : ℕ, Icc (a - w / (j + 1)) (b + w / (j + 1)) = Icc a b := by
      ext t
      simp only [mem_iInter, mem_Icc]
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · have := (tendsto_const_nhds (x := a)).sub h0
          rw [sub_zero] at this
          exact le_of_tendsto' this fun j => (h j).1
        · have := (tendsto_const_nhds (x := b)).add h0
          rw [add_zero] at this
          exact ge_of_tendsto' this fun j => (h j).2
      · intro h j
        exact ⟨by linarith [hδ j, h.1], by linarith [hδ j, h.2]⟩
    have hlim := tendsto_measure_iInter_atTop (μ := ν)
      (fun j => measurableSet_Icc.nullMeasurableSet) hanti
      ⟨0, (isCompact_Icc.measure_lt_top).ne⟩
    rw [hI] at hlim
    refine ge_of_tendsto' hlim fun j => (iInf_le _ j).trans ?_
    calc _ ≤ ∫⁻ t, (Icc (a - w / (j + 1)) (b + w / (j + 1))).indicator 1 t ∂ν :=
          lintegral_mono fun t => trap_le_indicator (hδ j) t
      _ = _ := lintegral_indicator_one measurableSet_Icc
  · calc ν (Icc a b) = ∫⁻ t, (Icc a b).indicator 1 t ∂ν :=
          (lintegral_indicator_one measurableSet_Icc).symm
      _ ≤ _ := lintegral_mono fun t => by
        by_cases ht : t ∈ Icc a b
        · rw [indicator_of_mem ht, trap_eq_one (hδ j) ht, Pi.one_apply, ENNReal.ofReal_one]
        · rw [indicator_of_notMem ht]; exact zero_le

/-- Vague convergence gives convergence of the lintegrals of nonnegative test functions. -/
theorem tendsto_lintegral_ofReal_of_vague {νs : ℕ → Measure ℝ} {ν : Measure ℝ}
    (hν : IsVagueLimitR νs ν) (hfin : ∀ k, IsFiniteMeasureOnCompacts (νs k)) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (h0 : ∀ t, 0 ≤ f t) :
    Tendsto (fun k => ∫⁻ t, ENNReal.ofReal (f t) ∂νs k) atTop
      (𝓝 (∫⁻ t, ENNReal.ofReal (f t) ∂ν)) := by
  have := hν.1
  have e : ∀ μ : Measure ℝ, IsFiniteMeasureOnCompacts μ →
      ∫⁻ t, ENNReal.ofReal (f t) ∂μ = ENNReal.ofReal (∫ t, f t ∂μ) := fun μ hμ => by
    have := hμ
    exact (ofReal_integral_eq_lintegral_ofReal (hf.integrable_of_hasCompactSupport hfc)
      (ae_of_all _ h0)).symm
  have e' : (fun k => ∫⁻ t, ENNReal.ofReal (f t) ∂νs k) =
      fun k => ENNReal.ofReal (∫ t, f t ∂νs k) := funext fun k => e _ (hfin k)
  rw [e', e ν inferInstance]
  exact ENNReal.tendsto_ofReal (hν.2 f hf hfc)

/-! ## The length functional -/

/-- The boundary length of `[a, b]` read from the approximations with the trapezoids of
widths `w/(j+1)`. -/
def locLen (γ : ℝ) (Y : FieldSample) (a b w : ℝ) : ℝ≥0∞ :=
  ⨅ j : ℕ, liminf (fun k => ∫⁻ t, ENNReal.ofReal (trap (w / (j + 1)) a b t)
    ∂bdryApprox γ Y k) atTop

theorem measurable_locLen (γ a b w : ℝ) :
    Measurable fun Y : FieldSample => locLen γ Y a b w :=
  Measurable.iInf fun _ => Measurable.liminf fun k =>
    (Measure.measurable_lintegral (measurable_ofReal_trap _ a b)).comp (measurable_bdryApprox γ k)

/-- Near `[a, b]` the approximations of the restricted field are those of `y`. -/
theorem lintegral_trap_restrict_eq (γ : ℝ) (y : FieldSample) {c ρ a b w δ : ℝ} (hδ : 0 < δ)
    (hδw : δ ≤ w) (hfar : ∀ s ∈ Icc (a - w) (b + w), ρ + w < |s - c|) {k : ℕ}
    (hk : radius k ≤ w) :
    ∫⁻ t, ENNReal.ofReal (trap δ a b t) ∂bdryApprox γ (restrictField (circOut c ρ c ρ) y) k =
      ∫⁻ t, ENNReal.ofReal (trap δ a b t) ∂bdryApprox γ y k := by
  rw [G3Fid.bdryApprox_eq_bDens, G3Fid.bdryApprox_eq_bDens,
    lintegral_withDensity_eq_lintegral_mul _ (G3Fid.measurable_bDens _ _ _)
      (measurable_ofReal_trap δ a b),
    lintegral_withDensity_eq_lintegral_mul _ (G3Fid.measurable_bDens _ _ _)
      (measurable_ofReal_trap δ a b)]
  refine lintegral_congr fun t => ?_
  by_cases ht : t ∈ Ioo (a - δ) (b + δ)
  · have hs : ρ + radius k < |t - c| := by
      have := hfar t ⟨by linarith [ht.1], by linarith [ht.2]⟩
      linarith
    simp only [Pi.mul_apply, G3Fid.bDens, G3Fid.avgReg_gap_in hs hs]
  · simp only [Pi.mul_apply, trap_eq_zero hδ ht, ENNReal.ofReal_zero, mul_zero]

/-- **Locality of the boundary length (deterministic).** -/
theorem locLen_restrict_eq {γ : ℝ} {y : FieldSample} (hy : IsLQGGood γ y) {c ρ a b w : ℝ}
    (hw : 0 < w) (hfar : ∀ s ∈ Icc (a - w) (b + w), ρ + w < |s - c|) :
    locLen γ (restrictField (circOut c ρ c ρ) y) a b w = qBoundaryMeasure γ y (Icc a b) := by
  have hν : IsVagueLimitR (bdryApprox γ y) (qBoundaryMeasure γ y) :=
    ⟨hy.qBoundaryMeasure_spec.1, fun f hf hfc => LQGMeas.tendsto_bdryApprox_of_good hy hf hfc⟩
  have hfin : ∀ k, IsFiniteMeasureOnCompacts (bdryApprox γ y k) := fun k =>
    LogSing.isFiniteMeasureOnCompacts_bdryApprox hy.1 γ k
  have := hν.1
  have hr : ∀ᶠ k in atTop, radius k ≤ w :=
    (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually (ge_mem_nhds hw)
  unfold locLen
  rw [← iInf_lintegral_trap _ hw]
  refine iInf_congr fun j => ?_
  have hδ : 0 < w / (j + 1) := div_pos hw (Nat.cast_add_one_pos j)
  have hδw : w / (j + 1) ≤ w :=
    div_le_self hw.le (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  refine ((tendsto_lintegral_ofReal_of_vague hν hfin (continuous_trap _ a b)
    (hasCompactSupport_trap hδ) (trap_nonneg _ a b)).congr' ?_).liminf_eq
  filter_upwards [hr] with k hk
  exact (lintegral_trap_restrict_eq γ y hδ hδw hfar hk).symm

/-! ## Measurability of the restricted Palm field -/

theorem refS_ball_null_of {t r x κ : ℝ} (hB : ball (x : ℂ) (κ / 2) ⊆ ball (t : ℂ) r)
    (hu : |t| + r ≤ 1) : refS (ball (x : ℂ) (κ / 2)) = 0 := by
  refine measure_mono_null (hB.trans fun z hz => ?_)
    (LateralGerm.foldedCircle_ball_eq_zero (s := 1) (δ := 1) one_pos le_rfl)
  rw [mem_ball, dist_eq_norm] at hz
  rw [mem_ball, dist_zero_right]
  have hn : ‖(t : ℂ)‖ = |t| := by rw [Complex.norm_real, Real.norm_eq_abs]
  calc ‖z‖ = ‖(z - t) + (t : ℂ)‖ := by ring_nf
    _ ≤ ‖z - t‖ + ‖(t : ℂ)‖ := norm_add_le _ _
    _ < 1 := by rw [hn]; linarith

/-- The Palm field read on the folded circles missing `B(x, κ/2)` is `condSigma`-measurable. -/
theorem measurable_restrict_xPalm (γ : ℝ) {x κ : ℝ} (hS : refS (ball (x : ℂ) (κ / 2)) = 0) :
    Measurable[D3Plus.condSigma (fun _ : Ω₀ => ()) (palmCField gffBase.X x) (κ / 2)]
      fun ω => restrictField (circOut x (κ / 2) x (κ / 2)) (normField γ (xPalm γ x) ω) := by
  refine measurable_restrictField_of _ fun μ hμ => ?_
  obtain ⟨d, ρ, hρ, rfl, hnull⟩ := hμ
  rw [union_self] at hnull
  exact measurable_normField_xPalm_apply γ (D3Plus.isAdmissibleH_foldedCircle' d hρ)
    measure_univ hnull hS

end G2PalmLoc
end Thm18Asm
end QuantumZipper
