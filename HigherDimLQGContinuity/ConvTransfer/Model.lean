import HigherDimLQGContinuity.ConvTransfer.Envelope
import HigherDimLQGMetric.Law.Main
import HigherDimLQGMetric.LfppTight.CoupledVec
import HigherDimLQGMetric.LfppTight.LawTransfer
import HigherDimLQGMetric.DGZ.AdapterBasics
import HigherDimLFPP.Field.Exists

/-!
# White-noise model for a real convolution cutoff

The centered convolution field is transferred in law to a white-noise field.
Its finite band, after the real-to-dyadic similarity, is a dyadic band plus a
bounded-width upper band on the same probability space.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd WN)

/-- Structural real-cutoff white-noise model; the quantitative tails are proved separately. -/
theorem convModel_law {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    ∃ N : ℕ, ∃ r : ℝ, 1 / 2 < r ∧ r ≤ 1 ∧
      ε = ((2 : ℝ)⁻¹ ^ N) * r ∧
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
        (W₀ W' : WN d → Ω' → ℝ) (H : ℕ → Rd d → Ω' → ℝ)
        (T I : Rd d → Ω' → ℝ) (m : Ω' → ℝ),
        IsProbabilityMeasure P' ∧
        HigherDimLFPP.IsWhiteNoise P' W₀ ∧
        HigherDimLQGMetric.DGZ.IsDyadicRealization κ P' W' H ∧
        HigherDimLFPP.IsBandVersion P' W' κ 1 (1 / r) T ∧
        (∀ ω', Continuous fun x => I x ω') ∧
        (∀ x, Measurable (I x)) ∧ Measurable m ∧
        (∀ x, I x =ᵐ[P'] W₀ (HigherDimLFPP.bandVecM κ (Ioi 1)
          (Measure.dirac x) (unitSphereProb d))) ∧
        (∀ ω', m ω' = W₀ (HigherDimLFPP.bandVecM κ (Ioo ε 1)
          (unitSphereProb d) 0) ω') ∧
        (∀ᵐ ω ∂P, Continuous (convMollifyNorm κ ε (h ω))) ∧
        ∃ (Φ : Rd d → Ω' → ℝ) (hΦc : ∀ ω', Continuous fun x => Φ x ω'),
          (∀ z ω', Φ (r • z) ω' = H N z ω' + T z ω' - m ω' + I (r • z) ω') ∧
          (∀ A : Set C(Rd d, ℝ), MeasurableSet A →
            P {ω | l6a_toFieldCMap (convMollifyNorm κ ε (h ω)) ∈ A} =
              P' {ω' | (⟨fun x => Φ x ω', hΦc ω'⟩ : C(Rd d, ℝ)) ∈ A}) := by
  obtain ⟨N, r, hrhalf, hr1, hεeq⟩ :=
    HigherDimLQGMetric.DGZ.adapter_exists_dyadic_scale hε.1 hε.2.le
  have hr : 0 < r := by linarith
  obtain ⟨_, hfield⟩ := HigherDimLFPP.field_exists_impl d (by omega : 1 ≤ d)
  obtain ⟨Ω', inst', P', W, G, hP', hW, hG⟩ := hfield κ hκ
  letI : MeasurableSpace Ω' := inst'
  letI : IsProbabilityMeasure P' := hP'
  obtain ⟨I, hIc, hIm, hIeq, hsplit⟩ :=
    l6a_exists_coupled_centered_version hd hκ hW G hG
  let m : Ω' → ℝ := fun ω' =>
    W (HigherDimLFPP.bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω'
  have hmm : Measurable m := hW.measurable _
  let Φ : Rd d → Ω' → ℝ := fun x ω' => G ε x ω' - m ω' + I x ω'
  have hΦc : ∀ ω', Continuous fun x => Φ x ω' := by
    intro ω'
    exact ((hG ε hε).continuous ω').sub continuous_const |>.add (hIc ω')
  have hΦW (x : Rd d) : Φ x =ᵐ[P']
      W (HigherDimLFPP.bandVecM κ (Ioi ε) (Measure.dirac x) (unitSphereProb d)) :=
    hsplit ε hε x
  obtain ⟨hZc, hlaw⟩ := l1e_law d hd κ hκ ε hε.1 P h hh P' W Φ hW hΦc hΦW
  obtain ⟨H, hH, T, hT, hscale⟩ :=
    HigherDimLQGMetric.DGZ.adapter_realScale_coupling hκ hW hε.1
      (hG ε hε) N hr hr1 hεeq
  let W' : WN d → Ω' → ℝ :=
    fun f => W (HigherDimLFPP.simL2 (LinearIsometryEquiv.refl ℝ (Rd d)) 0 hr f)
  refine ⟨N, r, hrhalf, hr1, hεeq, Ω', inst', P', W, W', H, T, I, m,
    hP', hW, hH, hT, hIc, hIm, hmm, ?_, (fun _ => rfl), hZc,
    Φ, hΦc, ?_, ?_⟩
  · intro x
    rw [← l6a_high_band_vec_eq hd hκ x]
    exact hIeq x
  · intro z ω'
    dsimp [Φ]
    rw [hscale z ω']
  · intro A hA
    have h := l6a_aeContinuousFunctional_law P P'
      (fun x ω => convMollifyNorm κ ε (h ω) x) Φ hZc hΦc hlaw
      (fun q : C(Rd d, ℝ) => q) measurable_id hA
    simpa only [id_eq] using h

/-- Point-distance laws obtained by evaluating the continuous-field law. -/
theorem convModel_pointDist_law {d : ℕ} (ξ : ℝ)
    {κ : Rd d → ℝ} {ε : ℝ}
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (h : Ω → DistRd d)
    {Φ : Rd d → Ω' → ℝ}
    (hZc : ∀ᵐ ω ∂P, Continuous (convMollifyNorm κ ε (h ω)))
    (hΦc : ∀ ω', Continuous fun x => Φ x ω')
    (hLaw : ∀ A : Set C(Rd d, ℝ), MeasurableSet A →
      P {ω | l6a_toFieldCMap (convMollifyNorm κ ε (h ω)) ∈ A} =
        P' {ω' | (⟨fun x => Φ x ω', hΦc ω'⟩ : C(Rd d, ℝ)) ∈ A})
    (B : Set ℝ) (hB : MeasurableSet B) :
    P {ω | HigherDimLQGMetric.DGZ.lfppMetric ξ
      (convMollifyNorm κ ε (h ω)) 0 (HigherDimLFPP.e₁ d) ∈ B} =
    P' {ω' | HigherDimLQGMetric.DGZ.lfppMetric ξ
      (fun x => Φ x ω') 0 (HigherDimLFPP.e₁ d) ∈ B} := by
  let A : Set C(Rd d, ℝ) :=
    {φ | HigherDimLQGMetric.DGZ.lfppMetric ξ φ 0 (HigherDimLFPP.e₁ d) ∈ B}
  have hA : MeasurableSet A :=
    (HigherDimLQGMetric.DGZ.measurable_lfppMetric_continuousMap ξ 0
      (HigherDimLFPP.e₁ d)) hB
  have hlaw := hLaw A hA
  have hleft : P {ω | HigherDimLQGMetric.DGZ.lfppMetric ξ
      (convMollifyNorm κ ε (h ω)) 0 (HigherDimLFPP.e₁ d) ∈ B} =
      P {ω | l6a_toFieldCMap (convMollifyNorm κ ε (h ω)) ∈ A} := by
    apply measure_congr
    filter_upwards [hZc] with ω hc
    simp only [A, l6a_toFieldCMap, dite_eq_left hc]
    rfl
  rw [hleft, hlaw]
  rfl

end HigherDimLQGContinuity
