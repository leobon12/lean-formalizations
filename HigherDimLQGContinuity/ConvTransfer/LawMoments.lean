import HigherDimLQGContinuity.ConvTransfer.UpperDet

/-!
# Measurability and law transfer for convolution field functionals
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- Coordinatewise a.e. measurability and a.s. continuity suffice for the
continuous-map totalization of a random field. -/
theorem convEnv_aemeasurable_toFieldCMap {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (X : Rd d → Ω → ℝ)
    (hm : ∀ z, AEMeasurable (X z) P)
    (hc : ∀ᵐ ω ∂P, Continuous fun z => X z ω) :
    AEMeasurable (fun ω => l6a_toFieldCMap (fun z => X z ω)) P := by
  have hcoord (z : Rd d) : AEMeasurable
      (fun ω => (l6a_toFieldCMap (fun z => X z ω)) z) P := by
    have heq : (fun ω => (l6a_toFieldCMap (fun z => X z ω)) z) =ᵐ[P] X z := by
      filter_upwards [hc] with ω hω
      simp only [l6a_toFieldCMap, dite_eq_left hω, ContinuousMap.coe_mk]
    exact (hm z).congr heq.symm
  have hnull : @Measurable (NullMeasurableSpace Ω P) C(Rd d, ℝ) _ _
      (fun ω => l6a_toFieldCMap (fun z => X z ω)) :=
    (ContinuousMap.measurable_iff_eval (Z := NullMeasurableSpace Ω P)).2
      (fun z => (hcoord z).nullMeasurable)
  exact (show NullMeasurable
    (fun ω => l6a_toFieldCMap (fun z => X z ω)) P
    from fun s hs => hnull hs).aemeasurable

/-- Coordinatewise a.e. measurability for a normalized LGF convolution. -/
theorem convEnv_aemeasurable_convMollifyNorm_coord {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) (z : Rd d) :
    AEMeasurable (fun ω => convMollifyNorm κ ε (h ω) z) P := by
  have hmeas := l2b_measurable_pairCenteredKernel d hd κ hκ h
    hh.1.measurable hε z
  have heq : (fun ω => convMollifyNorm κ ε (h ω) z) =ᵐ[P]
      fun ω => l2b_pairCenteredKernel hd hκ hε z (h ω) := by
    filter_upwards [l2b_ae_pairCenteredKernel_eq_convMollifyNorm d hd κ hκ P h hh]
      with ω heqω
    exact (heqω ε hε z).symm
  exact hmeas.aemeasurable.congr heq.symm

/-- Equality of the continuous-field laws transfers nonnegative integrals of
measurable functionals. -/
theorem convEnv_lintegral_of_field_law {d : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    (X : Ω → C(Rd d, ℝ)) (Y : Ω' → C(Rd d, ℝ))
    (hXm : AEMeasurable X P) (hYm : AEMeasurable Y P')
    (hLaw : ∀ A : Set C(Rd d, ℝ), MeasurableSet A →
      P {ω | X ω ∈ A} = P' {ω' | Y ω' ∈ A})
    (F : C(Rd d, ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω, F (X ω) ∂P = ∫⁻ ω', F (Y ω') ∂P' := by
  have hmap : P.map X = P'.map Y := by
    apply Measure.ext
    intro A hA
    rw [Measure.map_apply_of_aemeasurable hXm hA,
      Measure.map_apply_of_aemeasurable hYm hA]
    exact hLaw A hA
  calc
    ∫⁻ ω, F (X ω) ∂P = ∫⁻ φ, F φ ∂(P.map X) :=
      (lintegral_map' hF.aemeasurable hXm).symm
    _ = ∫⁻ φ, F φ ∂(P'.map Y) := by rw [hmap]
    _ = ∫⁻ ω', F (Y ω') ∂P' := lintegral_map' hF.aemeasurable hYm

/-- The explicit model decomposition makes its random continuous field
measurable as a continuous-map-valued variable. -/
theorem convEnv_aemeasurable_modelField {d : ℕ} {κ : Rd d → ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : HigherDimLFPP.WN d → Ω → ℝ}
    {H : ℕ → Rd d → Ω → ℝ} (hH : HigherDimLQGMetric.DGZ.IsDyadicRealization κ P W H)
    {r : ℝ} (hr : 0 < r) (N : ℕ)
    {T I Φ : Rd d → Ω → ℝ} (hT : HigherDimLFPP.IsBandVersion P W κ 1 (1 / r) T)
    (hIm : ∀ x, Measurable (I x)) (m : Ω → ℝ) (hmm : Measurable m)
    (hΦc : ∀ ω, Continuous fun x => Φ x ω)
    (hΦeq : ∀ z ω, Φ (r • z) ω = H N z ω + T z ω - m ω + I (r • z) ω) :
    AEMeasurable (fun ω => (⟨fun x => Φ x ω, hΦc ω⟩ : C(Rd d, ℝ))) P := by
  have hmcoord (x : Rd d) : AEMeasurable (Φ x) P := by
    let z : Rd d := r⁻¹ • x
    have hx : r • z = x := by
      simp only [z, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have heq : Φ x = fun ω => H N z ω + T z ω - m ω + I x ω := by
      funext ω
      simpa only [hx] using hΦeq z ω
    rw [heq]
    exact ((((hH.band N).measurable z).add (hT.measurable z)).sub hmm |>.add
      (hIm x)).aemeasurable
  have hnull : @Measurable (NullMeasurableSpace Ω P) C(Rd d, ℝ) _ _
      (fun ω => (⟨fun x => Φ x ω, hΦc ω⟩ : C(Rd d, ℝ))) := by
    apply (ContinuousMap.measurable_iff_eval (Z := NullMeasurableSpace Ω P)).2
    intro x
    exact (hmcoord x).nullMeasurable
  exact (show NullMeasurable
    (fun ω => (⟨fun x => Φ x ω, hΦc ω⟩ : C(Rd d, ℝ))) P
    from fun s hs => hnull hs).aemeasurable

/-- An elementary two-factor replacement for Cauchy--Schwarz that requires
only the two square moments. -/
theorem convEnv_lintegral_mul_le_sq_sum {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ}
    (hX : AEMeasurable X P) :
    ∫⁻ ω, ENNReal.ofReal (X ω * Y ω) ∂P ≤
      (∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂P) +
        ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂P := by
  have hm : AEMeasurable (fun ω => ENNReal.ofReal (X ω ^ 2)) P :=
    (hX.mul hX).ennreal_ofReal.congr (by filter_upwards [] with ω; simp [pow_two])
  calc
    ∫⁻ ω, ENNReal.ofReal (X ω * Y ω) ∂P ≤
        ∫⁻ ω, (ENNReal.ofReal (X ω ^ 2) + ENNReal.ofReal (Y ω ^ 2)) ∂P := by
      apply lintegral_mono
      intro ω
      change ENNReal.ofReal (X ω * Y ω) ≤
        ENNReal.ofReal (X ω ^ 2) + ENNReal.ofReal (Y ω ^ 2)
      rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (X ω - Y ω)])
    _ = (∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂P) +
          ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂P := lintegral_add_left' hm _

/-- A two-factor moment estimate by the pointwise inequality
`uv ≤ u² + v²`. No independence is used. -/
theorem convEnv_lintegral_rpow_product_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {A X Y : Ω → ℝ} {p K BX BY : ℝ}
    (hp : 0 < p) (hK : 0 ≤ K) (hBX : 0 ≤ BX) (hBY : 0 ≤ BY)
    (hXm : AEMeasurable X P)
    (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hA0 : ∀ ω, 0 ≤ A ω)
    (hbound : ∀ᵐ ω ∂P, A ω ≤ K * X ω * Y ω)
    (hXmom : ∫⁻ ω, ENNReal.ofReal (X ω ^ (2 * p)) ∂P ≤ ENNReal.ofReal BX)
    (hYmom : ∫⁻ ω, ENNReal.ofReal (Y ω ^ (2 * p)) ∂P ≤ ENNReal.ofReal BY) :
    ∫⁻ ω, ENNReal.ofReal (A ω ^ p) ∂P ≤
      ENNReal.ofReal (K ^ p * (BX + BY)) := by
  have hp2 : 0 ≤ 2 * p := by positivity
  have hX2m : AEMeasurable (fun ω => ENNReal.ofReal (X ω ^ (2 * p))) P :=
    ((Real.continuous_rpow_const hp2).measurable.comp_aemeasurable hXm).ennreal_ofReal
  have hKp : 0 ≤ K ^ p := Real.rpow_nonneg hK _
  have hpoint (ω : Ω) (hb : A ω ≤ K * X ω * Y ω) :
      A ω ^ p ≤ K ^ p * (X ω ^ (2 * p) + Y ω ^ (2 * p)) := by
    have hprod : 0 ≤ K * X ω := mul_nonneg hK (hX0 ω)
    have hpow : A ω ^ p ≤ (K * X ω * Y ω) ^ p :=
      Real.rpow_le_rpow (hA0 ω) hb hp.le
    rw [Real.mul_rpow hprod (hY0 ω), Real.mul_rpow hK (hX0 ω)] at hpow
    have hxy : X ω ^ p * Y ω ^ p ≤
        X ω ^ (2 * p) + Y ω ^ (2 * p) := by
      rw [show X ω ^ (2 * p) = (X ω ^ p) ^ 2 by
          rw [show 2 * p = p * 2 by ring, Real.rpow_mul (hX0 ω)]; norm_cast,
        show Y ω ^ (2 * p) = (Y ω ^ p) ^ 2 by
          rw [show 2 * p = p * 2 by ring, Real.rpow_mul (hY0 ω)]; norm_cast]
      nlinarith [sq_nonneg (X ω ^ p - Y ω ^ p)]
    exact hpow.trans (by simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left hxy hKp))
  have hboundE : ∀ᵐ ω ∂P,
      ENNReal.ofReal (A ω ^ p) ≤
        ENNReal.ofReal (K ^ p * (X ω ^ (2 * p) + Y ω ^ (2 * p))) := by
    filter_upwards [hbound] with ω hb
    exact ENNReal.ofReal_le_ofReal (hpoint ω hb)
  calc
    ∫⁻ ω, ENNReal.ofReal (A ω ^ p) ∂P ≤
        ∫⁻ ω, ENNReal.ofReal (K ^ p *
          (X ω ^ (2 * p) + Y ω ^ (2 * p))) ∂P := lintegral_mono_ae hboundE
    _ = ENNReal.ofReal (K ^ p) *
          ((∫⁻ ω, ENNReal.ofReal (X ω ^ (2 * p)) ∂P) +
            ∫⁻ ω, ENNReal.ofReal (Y ω ^ (2 * p)) ∂P) := by
      simp_rw [ENNReal.ofReal_mul hKp,
        ENNReal.ofReal_add (Real.rpow_nonneg (hX0 _) _) (Real.rpow_nonneg (hY0 _) _)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left' hX2m]
    _ ≤ ENNReal.ofReal (K ^ p) * (ENNReal.ofReal BX + ENNReal.ofReal BY) := by
      gcongr
    _ = ENNReal.ofReal (K ^ p * (BX + BY)) := by
      rw [← ENNReal.ofReal_add hBX hBY, ENNReal.ofReal_mul hKp]

end HigherDimLQGContinuity
