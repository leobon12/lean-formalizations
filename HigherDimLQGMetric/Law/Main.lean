import HigherDimLQGMetric.Law.CovLimit
import HigherDimLQGMetric.B3.Interfaces
import HigherDimLFPP.Field.LawTransfer

/-!
# Law of the normalized convolution field

The covariance identity of [1, Lemma 2.9], L2b's Gaussian test process, and
finite-dimensional Gaussian uniqueness give [1, Proposition 1.10] in the
normalized form of the B3 interface.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

private theorem law_pair_mean_zero (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {ε : ℝ} (hε : 0 < ε) (x : Rd d) :
    ∫ ω, l2b_pairCenteredKernel hd hκ hε x (h ω) ∂P = 0 := by
  let Yn : ℕ → Ω → ℝ := fun n ω => h ω (l2b_centeredTruncTest hd hκ hε x n).1
  let Y : Ω → ℝ := fun ω => l2b_pairCenteredKernel hd hκ hε x (h ω)
  have hG (n : ℕ) : HasGaussianLaw (Yn n) P :=
    hh.1.gaussian.hasGaussianLaw_eval (l2b_centeredTruncTest hd hκ hε x n)
  have hc (n : ℕ) : ∫ ω, Yn n ω ∂P = 0 :=
    hh.1.centered (l2b_centeredTruncTest hd hκ hε x n)
  have hm : AEMeasurable Y P :=
    (l2b_measurable_pairCenteredKernel d hd κ hκ h hh.1.measurable hε x).aemeasurable
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Yn n ω) atTop (𝓝 (Y ω)) := by
    filter_upwards [l2b_ae_centeredTrunc_tendsto d hd κ hκ P h hh,
      l2b_ae_pairCenteredKernel_eq_convMollifyNorm d hd κ hκ P h hh]
      with ω hω hp
    have ht := hω ε hε x
    rwa [← hp ε hε x] at ht
  exact (LQGMetric.CircleAvgIndep.gaussian_of_ae_tendsto hG hc hm hlim).2.1

private theorem law_pair_cov_eq (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {ε : ℝ} (hε : 0 < ε) (x y : Rd d) :
    cov[(fun ω => l2b_pairCenteredKernel hd hκ hε x (h ω)),
      (fun ω => l2b_pairCenteredKernel hd hκ hε y (h ω)); P] =
      HigherDimLFPP.scaleCov κ (Ioi ε) (Measure.dirac x) (unitSphereProb d)
        (Measure.dirac y) (unitSphereProb d) := by
  have h1 := l2b_tendsto_centeredKernel_covariance d hd κ hκ P h hh hε x y
  have h2 := law_tendsto_centered_covariance d hd κ hκ hε x y
  have hcov := tendsto_nhds_unique h1 h2
  haveI := isProbabilityMeasure_unitSphereProb (show 1 ≤ d by omega)
  have hmass : (Measure.dirac x).real univ = (unitSphereProb d).real univ := by
    simp only [probReal_univ]
  have hmass' : (Measure.dirac y).real univ = (unitSphereProb d).real univ := by
    simp only [probReal_univ]
  let D : ℝ := max 1 (max ‖x‖ ‖y‖)
  have hD : ∃ D : ℝ,
      (∀ᵐ z ∂(Measure.dirac x), ‖z‖ ≤ D) ∧
      (∀ᵐ z ∂(unitSphereProb d), ‖z‖ ≤ D) ∧
      (∀ᵐ z ∂(Measure.dirac y), ‖z‖ ≤ D) ∧
      (∀ᵐ z ∂(unitSphereProb d), ‖z‖ ≤ D) := by
    refine ⟨D, ?_, ?_, ?_, ?_⟩
    · exact (ae_dirac_iff (measurableSet_le continuous_norm.measurable measurable_const)).2
        ((le_max_left ‖x‖ ‖y‖).trans (le_max_right 1 _))
    · filter_upwards [ae_unitSphereProb_norm_eq_one d] with z hz
      rw [hz]
      exact le_max_left _ _
    · exact (ae_dirac_iff (measurableSet_le continuous_norm.measurable measurable_const)).2
        ((le_max_right ‖x‖ ‖y‖).trans (le_max_right 1 _))
    · filter_upwards [ae_unitSphereProb_norm_eq_one d] with z hz
      rw [hz]
      exact le_max_left _ _
  have hl := (l1d_cov d hd κ hκ ε hε (Measure.dirac x) (unitSphereProb d)
    (Measure.dirac y) (unitSphereProb d) hmass hmass' hD).2.2
  exact hcov.trans hl.symm

private theorem law_map_pair_eq_white (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (W : HigherDimLFPP.WN d → Ω' → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P' W) :
    P.map (fun ω x => l2b_pairCenteredKernel hd hκ hε x (h ω)) =
      P'.map (fun ω x => W (HigherDimLFPP.bandVecM κ (Ioi ε)
        (Measure.dirac x) (unitSphereProb d)) ω) := by
  let v : Rd d → HigherDimLFPP.WN d := fun x =>
    HigherDimLFPP.bandVecM κ (Ioi ε) (Measure.dirac x) (unitSphereProb d)
  let X : Rd d → Ω → ℝ := fun x ω => l2b_pairCenteredKernel hd hκ hε x (h ω)
  let Y : Rd d → Ω' → ℝ := fun x ω => W (v x) ω
  have hXg : IsGaussianProcess X P :=
    l2b_isGaussianProcess_pairCenteredKernel d hd κ hκ P h hh hε
  have hYg : IsGaussianProcess Y P' := hW.isGaussianProcess_comp v
  have hXm (x : Rd d) : Measurable (X x) :=
    l2b_measurable_pairCenteredKernel d hd κ hκ h hh.1.measurable hε x
  have hYm (x : Rd d) : Measurable (Y x) := hW.measurable (v x)
  have hXmean (x : Rd d) : ∫ ω, X x ω ∂P = 0 :=
    law_pair_mean_zero d hd κ hκ P h hh hε x
  have hYmean (x : Rd d) : ∫ ω, Y x ω ∂P' = 0 := hW.integral_eq_zero (v x)
  have hcov (x y : Rd d) : cov[X x, X y; P] = cov[Y x, Y y; P'] := by
    rw [hW.cov_eq]
    exact law_pair_cov_eq d hd κ hκ P h hh hε x y
  change P.map (fun ω x => X x ω) = P'.map (fun ω x => Y x ω)
  apply LQGMetric.WhiteNoise.map_eq_of_forall_finset'
    (measurable_pi_iff.mpr hXm).aemeasurable
    (measurable_pi_iff.mpr hYm).aemeasurable
  intro I
  exact QuantumZipper.WedgeRes.map_eq_of_gaussian_vec (ι := I)
    (U := fun i => X i) (V := fun i => Y i)
    (hXg.hasGaussianLaw I) (hYg.hasGaussianLaw I)
    (fun i => hXm i) (fun i => hYm i)
    (fun i => (hXg.hasGaussianLaw_eval i).memLp_two)
    (fun i => (hYg.hasGaussianLaw_eval i).memLp_two)
    (fun i => hXmean i) (fun i => hYmean i)
    (fun i j => hcov i j)

private theorem law_ae_continuous_norm (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, Continuous (convMollifyNorm κ ε (h ω)) := by
  filter_upwards [l2b_ae_convMollify_continuousOn d hd κ hκ P h hh]
    with ω hcont
  have hc : Continuous (fun x : Rd d => convMollify κ ε (h ω) x) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hp : (ε, x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (Rd d)) := ⟨hε, trivial⟩
    have hOpen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (Rd d))) :=
      isOpen_Ioi.prod isOpen_univ
    exact (hcont.continuousAt (hOpen.mem_nhds hp)).comp
      (continuousAt_const.prodMk continuousAt_id)
  change Continuous (fun x : Rd d => convMollify κ ε (h ω) x -
    ∫ u : Rd d, convMollify κ ε (h ω) u ∂(unitSphereProb d))
  exact hc.sub continuous_const

private theorem law_aemeasurable_cont_process {d : ℕ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Rd d → Ω → ℝ)
    (hm : ∀ x, AEMeasurable (Y x) P)
    (hc : ∀ ω, Continuous fun x => Y x ω) :
    AEMeasurable (fun ω x => Y x ω) P := by
  let Z : Ω → C(Rd d, ℝ) := fun ω => ⟨fun x => Y x ω, hc ω⟩
  have hZnull : NullMeasurable Z P := by
    have key : @Measurable (NullMeasurableSpace Ω P) C(Rd d, ℝ) _ _ Z := by
      refine (ContinuousMap.measurable_iff_eval
        (Z := NullMeasurableSpace Ω P)).2 fun x => ?_
      exact (hm x).nullMeasurable
    exact fun s hs => key hs
  have hcoe : Measurable (fun q : C(Rd d, ℝ) => (q : Rd d → ℝ)) :=
    measurable_pi_iff.mpr fun x => (continuous_eval_const x).measurable
  exact hcoe.comp_aemeasurable hZnull.aemeasurable

/-- [1, Proposition 1.10] in normalized form: the convolution of a normalized
whole-space LGF agrees in law with the corresponding white-noise band field. -/
theorem l1e_law : L1e_law := by
  intro d hd κ hκ ε hε Ω _ P _ h hh Ω' _ P' _ W Φ hW _hΦ hΦW
  constructor
  · exact law_ae_continuous_norm d hd κ hκ P h hh hε
  · intro A hA
    classical
    let X : Rd d → Ω → ℝ := fun x ω => l2b_pairCenteredKernel hd hκ hε x (h ω)
    let C : Rd d → Ω → ℝ := fun x ω => convMollifyNorm κ ε (h ω) x
    let v : Rd d → HigherDimLFPP.WN d := fun x =>
      HigherDimLFPP.bandVecM κ (Ioi ε) (Measure.dirac x) (unitSphereProb d)
    let Y : Rd d → Ω' → ℝ := fun x ω => W (v x) ω
    let Z : Rd d → Ω' → ℝ := fun x ω => Φ x ω
    have hXm (x : Rd d) : Measurable (X x) :=
      l2b_measurable_pairCenteredKernel d hd κ hκ h hh.1.measurable hε x
    have hYm (x : Rd d) : Measurable (Y x) := hW.measurable (v x)
    have hCX (x : Rd d) : C x =ᵐ[P] X x := by
      filter_upwards [l2b_ae_pairCenteredKernel_eq_convMollifyNorm d hd κ hκ P h hh]
        with ω hω
      exact (hω ε hε x).symm
    have hZY (x : Rd d) : Z x =ᵐ[P'] Y x := hΦW x
    have hXa : AEMeasurable (fun ω x => X x ω) P :=
      (measurable_pi_iff.mpr hXm).aemeasurable
    have hYa : AEMeasurable (fun ω x => Y x ω) P' :=
      (measurable_pi_iff.mpr hYm).aemeasurable
    let Cgood : Rd d → Ω → ℝ := fun x ω =>
      if hc : Continuous (fun z => C z ω) then C x ω else 0
    have hCae : ∀ᵐ ω ∂P, Continuous (fun x => C x ω) :=
      law_ae_continuous_norm d hd κ hκ P h hh hε
    have hCgoodc (ω : Ω) : Continuous (fun x => Cgood x ω) := by
      by_cases hc : Continuous (fun x => C x ω)
      · have he : (fun x => Cgood x ω) = fun x => C x ω := by
          funext x
          simp only [Cgood, dite_eq_left hc]
        rw [he]
        exact hc
      · have he : (fun x => Cgood x ω) = fun _ => 0 := by
          funext x
          simp only [Cgood, dite_eq_right hc]
        rw [he]
        exact continuous_const
    have hCgoodEq : (fun ω x => C x ω) =ᵐ[P] (fun ω x => Cgood x ω) := by
      filter_upwards [hCae] with ω hc
      funext x
      simp only [Cgood, dite_eq_left hc]
    have hCgoodm (x : Rd d) : AEMeasurable (Cgood x) P := by
      have h1 : AEMeasurable (C x) P :=
        (hXm x).aemeasurable.congr (hCX x).symm
      have h2 : C x =ᵐ[P] Cgood x := hCgoodEq.mono fun ω hω => congrFun hω x
      exact h1.congr h2
    have hCgooda : AEMeasurable (fun ω x => Cgood x ω) P :=
      law_aemeasurable_cont_process P Cgood hCgoodm hCgoodc
    have hCa : AEMeasurable (fun ω x => C x ω) P :=
      hCgooda.congr hCgoodEq.symm
    have hZa : AEMeasurable (fun ω x => Z x ω) P' :=
      law_aemeasurable_cont_process P' Z
        (fun x => (hYm x).aemeasurable.congr (hZY x).symm) _hΦ
    have heq : P.map (fun ω x => C x ω) = P'.map (fun ω x => Z x ω) := by
      calc
        _ = P.map (fun ω x => X x ω) :=
          ProbabilityTheory.map_eq_of_forall_ae_eq hCa hXa hCX
        _ = P'.map (fun ω x => Y x ω) :=
          law_map_pair_eq_white d hd κ hκ hε P h hh P' W hW
        _ = P'.map (fun ω x => Z x ω) :=
          ProbabilityTheory.map_eq_of_forall_ae_eq hYa hZa fun x => (hZY x).symm
    change P ((fun ω x => C x ω) ⁻¹' A) = P' ((fun ω x => Z x ω) ⁻¹' A)
    rw [← Measure.map_apply_of_aemeasurable hCa hA,
      ← Measure.map_apply_of_aemeasurable hZa hA, heq]

end HigherDimLQGMetric
