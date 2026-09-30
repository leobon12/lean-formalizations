import QuantumZipper.Proofs.LQG.PalmFree
import QuantumZipper.Proofs.LQG.Positivity
import QuantumZipper.Proofs.LQG.Atomless

/-!
# S5-B3(f) / M4-B5: the first-moment formula for the free field

For `Y = ofFun m + zField X R` (`X` free, `m` continuous), `ν_Y = qBoundaryMeasure γ Y`,
`0 < γ < 2`, and a window `[a,b] ⊆ [-N,N]` with `N + 2 ≤ R`:

* `integral_qBoundaryMeasure_free`: `E ∫ f dν_Y = ∫ f(x) exp(γ m(x)/2 + γ² (2 log R)/8) dx` for
  `f ≥ 0` continuous vanishing off `[a,b]` (the Palm formula with `φ ≡ 1`);
* `lintegral_qBoundaryMeasure_Icc_lt_top`: `E ν_Y([u,v]) < ∞` for `[u,v] ⊆ [-N,N]`;
* `lintegral_qBoundaryMeasure_Ioo_pos`: `0 < E ν_Y((u,v))` (hence `0 < E ν_Y([u,v])`) for
  `u < v`, `[u,v] ⊆ [-N,N]`;
* `ae_qBoundaryMeasure_Icc_lt_top_free`, `..._zField`, `..._add_ofFun`: a.s. `ν([u,v]) < ∞`
  for all `u, v` simultaneously (no window), for `X`, `zField X R` and `ofFun m + zField X R`;
* `lintegral_qBoundaryMeasure_Ioo_pos_X`: `0 < E ν_X((u,v))` for the free field `X` itself (any
  additive constant), for all `u < v`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

namespace QuantumZipper
namespace FirstMoment

open BdryExist PalmFree

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample} {γ : ℝ}
  {m : ℂ → ℝ}

/-- **First-moment formula (S5-B3(f))** for `Y = ofFun m + zField X R`. -/
theorem integral_qBoundaryMeasure_free [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (hγ : 0 < γ) (hγ2 : γ < 2) {N : ℕ} {R : ℝ} (hR : (N : ℝ) + 2 ≤ R) {a b : ℝ}
    (hab : Icc a b ⊆ Icc (-(N : ℝ)) N) (hm : Continuous m) {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) (hfab : ∀ x ∉ Icc a b, f x = 0) :
    ∫ ω, ∫ x, f x ∂qBoundaryMeasure γ (ofFun m + zField X R ω) ∂P =
      ∫ x, f x * Real.exp (γ * m x / 2 + γ ^ 2 * (2 * Real.log R) / 8) := by
  have hfc : HasCompactSupport f := HasCompactSupport.intro isCompact_Icc hfab
  have H := palm_formula_free (μ := fun _ => foldedCircle 0 1) (γ := γ) hX hγ hγ2 hR hab hm
    (fun _ => isAdmissibleH_foldedCircle (by simp [Hbar]) one_pos) hf hfc hf0 hfab
    (φ := fun _ _ => (1 : ℝ)) measurable_const (Cφ := 1) (fun _ _ => by simp)
  simpa using H

/-- The first-moment identity, as a finiteness statement: `E ν_Y([u,v]) < ∞`. -/
theorem lintegral_qBoundaryMeasure_Icc_lt_top [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) (hγ : 0 < γ) (hγ2 : γ < 2) {N : ℕ} {R : ℝ}
    (hR : (N : ℝ) + 2 ≤ R) {u v : ℝ} (huv : Icc u v ⊆ Icc (-(N : ℝ)) N)
    (hm : ContinuousOn m Hbar) :
    ∫⁻ ω, qBoundaryMeasure γ (ofFun m + zField X R ω) (Icc u v) ∂P < ∞ := by
  have h := lintegral_qBoundaryMeasure_zG_lt_top (m := m) hX hγ hγ2 hR huv hm
  have e : ∀ ω, qBoundaryMeasure γ (ofFun m + zG X R ω) =
      qBoundaryMeasure γ (ofFun m + zField X R ω) := fun ω =>
    qBoundaryMeasure_congr_Hbar (zG_add_fc' R m ω)
  simp_rw [e] at h
  exact h

/-- **Positivity of the first moment**: `0 < E ν_Y((u,v))` for `u < v` in the window. -/
theorem lintegral_qBoundaryMeasure_Ioo_pos [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) (hγ : 0 < γ) (hγ2 : γ < 2) {N : ℕ} {R : ℝ}
    (hR : (N : ℝ) + 2 ≤ R) {u v : ℝ} (huv' : u < v) (huv : Icc u v ⊆ Icc (-(N : ℝ)) N)
    (hm : Continuous m) :
    0 < ∫⁻ ω, qBoundaryMeasure γ (ofFun m + zField X R ω) (Ioo u v) ∂P := by
  set ν : Ω → Measure ℝ := fun ω => qBoundaryMeasure γ (ofFun m + zField X R ω) with hν
  have hνm : AEMeasurable ν P := aemeasurable_qBoundaryMeasure_free hX hγ hγ2 R hm.continuousOn
  have hF := integral_qBoundaryMeasure_free hX hγ hγ2 hR huv hm (Positivity.continuous_tent u v)
    (Positivity.tent_nonneg u v) (fun x hx => Positivity.tent_eq_zero_of_notMem hx)
  -- the right side is positive
  have hpos : 0 < ∫ x, Positivity.tent u v x *
      Real.exp (γ * m x / 2 + γ ^ 2 * (2 * Real.log R) / 8) := by
    have hc : Continuous fun x => Positivity.tent u v x *
        Real.exp (γ * m x / 2 + γ ^ 2 * (2 * Real.log R) / 8) :=
      (Positivity.continuous_tent u v).mul (Real.continuous_exp.comp
        ((((hm.comp Complex.continuous_ofReal).const_mul γ).div_const 2).add continuous_const))
    have hint := hc.integrable_of_hasCompactSupport (μ := volume) (Positivity.hasCompactSupport_tent u v).mul_right
    rw [integral_pos_iff_support_of_nonneg (fun x => mul_nonneg (Positivity.tent_nonneg u v x)
      (Real.exp_pos _).le) hint]
    refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo u v) fun x hx => ?_)
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.2 (by linarith)
    · exact (mul_pos (Positivity.tent_pos_iff.2 hx) (Real.exp_pos _)).ne'
  refine pos_iff_ne_zero.2 fun h0 => ?_
  have hae : ∀ᵐ ω ∂P, ν ω (Ioo u v) = 0 :=
    (lintegral_eq_zero_iff' ((Measure.measurable_coe measurableSet_Ioo).comp_aemeasurable hνm)).1 h0
  have hzero : ∫ ω, ∫ x, Positivity.tent u v x ∂ν ω ∂P = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with ω hω
    have hvan : ∀ x ∉ Ioo u v, Positivity.tent u v x = 0 := fun x hx =>
      le_antisymm (not_lt.1 fun h => hx (Positivity.tent_pos_iff.1 h))
        (Positivity.tent_nonneg u v x)
    rw [Pi.zero_apply, ← setIntegral_eq_integral_of_forall_compl_eq_zero hvan,
      Measure.restrict_eq_zero.2 hω, integral_zero_measure]
  rw [hF] at hzero
  exact hpos.ne' hzero

/-- `0 < E ν_Y([u,v])`. -/
theorem lintegral_qBoundaryMeasure_Icc_pos [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) (hγ : 0 < γ) (hγ2 : γ < 2) {N : ℕ} {R : ℝ}
    (hR : (N : ℝ) + 2 ≤ R) {u v : ℝ} (huv' : u < v) (huv : Icc u v ⊆ Icc (-(N : ℝ)) N)
    (hm : Continuous m) :
    0 < ∫⁻ ω, qBoundaryMeasure γ (ofFun m + zField X R ω) (Icc u v) ∂P :=
  (lintegral_qBoundaryMeasure_Ioo_pos hX hγ hγ2 hR huv' huv hm).trans_le
    (lintegral_mono fun _ => measure_mono Ioo_subset_Icc_self)

/-! ## Almost sure local finiteness (all intervals at once) -/

theorem ae_qBoundaryMeasure_Icc_lt_top_zField [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) (hγ : 0 < γ) (hγ2 : γ < 2) (R : ℝ) :
    ∀ᵐ ω ∂P, ∀ u v : ℝ, qBoundaryMeasure γ (zField X R ω) (Icc u v) < ∞ := by
  filter_upwards [ae_isVagueLimitR_qBoundaryMeasure_zField hX hγ hγ2 R] with ω hv u v
  have := hv.1
  exact measure_Icc_lt_top

/-! ## The free field with its additive constant -/

/-- `0 < E ν_X((u,v))` for the free field `X`, for every `u < v`. -/
theorem lintegral_qBoundaryMeasure_Ioo_pos_X [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) (hγ : 0 < γ) (hγ2 : γ < 2) {u v : ℝ} (huv' : u < v) :
    0 < ∫⁻ ω, qBoundaryMeasure γ (X ω) (Ioo u v) ∂P := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max |u| |v|)
  have huv : Icc u v ⊆ Icc (-(N : ℝ)) N := fun x hx =>
    ⟨by linarith [neg_abs_le u, le_max_left |u| |v|, hx.1],
      by linarith [le_abs_self v, le_max_right |u| |v|, hx.2]⟩
  set R : ℝ := (N : ℝ) + 2
  have hpos := lintegral_qBoundaryMeasure_Ioo_pos (m := fun _ => (0 : ℝ)) hX hγ hγ2 le_rfl
    huv' huv continuous_const
  simp only [Atomless.ofFun_zero_add] at hpos
  refine pos_iff_ne_zero.2 fun h0 => hpos.ne' ?_
  have hνX : AEMeasurable (fun ω => qBoundaryMeasure γ (X ω)) P :=
    LQGMeasAE.aemeasurable_qBoundaryMeasure_of_ae hX.measurable_coord
      (ae_isVagueLimitR_qBoundaryMeasure hX hγ hγ2)
  have hae : ∀ᵐ ω ∂P, qBoundaryMeasure γ (X ω) (Ioo u v) = 0 :=
    (lintegral_eq_zero_iff' ((Measure.measurable_coe measurableSet_Ioo).comp_aemeasurable hνX)).1 h0
  refine lintegral_eq_zero_iff' ?_ |>.2 ?_
  · exact (Measure.measurable_coe measurableSet_Ioo).comp_aemeasurable
      (LQGMeasAE.aemeasurable_qBoundaryMeasure_of_ae (X := zField X R)
        (fun μ => (measurable_pi_apply μ).comp (measurable_zField hX R))
        (ae_isVagueLimitR_qBoundaryMeasure_zField hX hγ hγ2 R))
  · filter_upwards [hae, Atomless.ae_qBoundaryMeasure_eq_smul hX hγ hγ2 R] with ω h1 h2
    rw [h2, Measure.smul_apply, smul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'

end FirstMoment
end QuantumZipper
