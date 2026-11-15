/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLaw3Rand
import InteractingSLE.Spec.Sec7.LocalExtGKernel

/-!
# The conditional law at the stop for an admissible seed

Packet PROVE-STAGEDLAW3. For an angle-`θ` flow-line driver `E` of a field `g` with datum `c` whose flow-line seed is
admissible, the conditional law of the field read in the record chart given the record, on `{min t ζ < ∞}`, is the
Gaussian law of the stop word (`ae_condExp_recField_of_admissible`):

1. the announced kernel at the stop (`ae_condExp_cexp_stop`, given the announced history `𝓗 = ⋁ₙ 𝓓_{ρₙ}`,
   `ρₙ = min t σₙ`, here `annSigma t hσ`);
2. at the pushed test function (`ae_condExp_cexp_pushTest`, through the `𝓗`-measurable version `recVersion` of the
   record, `recVersion_eq`);
3. read in the record chart (`recField_apply_eq`, `cexp_chartShift_mul_eq_gaussCF`; the shift is pulled out of the
   conditional expectation);
4. the tower property from `𝓗` to the record σ-algebra on `{min t ζ < ∞}` (`ae_condExp_eq_of_setIntegral_eq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open QuantumZipper Staged Restart LQGMetric

theorem padFL_fst_fst_fin (b : ℝ → ℝ) (J : Finset ℝ) (i : Fin (flowLineNL b J 0)) :
    (padFL 0 0 b J).1.1 i = flowLineXL b J 0 i := by
  simp only [padFL, i.2, ↓reduceDIte, Fin.eta]

theorem padFL_fst_snd_fin (b : ℝ → ℝ) (J : Finset ℝ) (j : Fin (flowLineNR b J 0)) :
    (padFL 0 0 b J).1.2 j = flowLineXR b J 0 j := by
  simp only [padFL, j.2, ↓reduceDIte, Fin.eta]

theorem padFL_snd_fst_fin (κ θ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (i : Fin (flowLineNL b J 0)) :
    (padFL κ θ b J).2.1 i = flowLineRhoL κ b J 0 θ i := by
  simp only [padFL, i.2, ↓reduceDIte, Fin.eta]

theorem padFL_snd_snd_fin (κ θ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (j : Fin (flowLineNR b J 0)) :
    (padFL κ θ b J).2.2 j = flowLineRhoR κ b J 0 θ j := by
  simp only [padFL, j.2, ↓reduceDIte, Fin.eta]

theorem measurable_stopSeq_of {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {t : ℝ≥0∞}
    {σ : ℕ → Ω → ℝ≥0} (hσ : ∀ n, IsStoppingTime 𝓖 fun ω => (σ n ω : WithTop ℝ≥0)) (n : ℕ) :
    Measurable[(isStoppingTime_stopSeq t hσ n).measurableSpace] (stopSeq t σ n) := by
  have h : Measurable[(isStoppingTime_stopSeq t hσ n).measurableSpace]
      ((fun x : WithTop ℝ≥0 => x.untopD 0) ∘ (fun ω => (stopSeq t σ n ω : WithTop ℝ≥0))) :=
    (WithTop.measurable_untopD (0 : ℝ≥0)).comp (isStoppingTime_stopSeq t hσ n).measurable
  have e : (fun x : WithTop ℝ≥0 => x.untopD 0) ∘ (fun ω => (stopSeq t σ n ω : WithTop ℝ≥0)) = stopSeq t σ n := by
    funext ω
    simp only [Function.comp_apply, WithTop.untopD_coe]
  rw [e] at h
  exact h

/-- The announced history `⋁ₙ 𝓓_{ρₙ}` of the stops `ρₙ = min t σₙ`. -/
abbrev annSigma {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} (t : ℝ≥0∞) {σ : ℕ → Ω → ℝ≥0}
    (hσ : ∀ n, IsStoppingTime 𝓖 fun ω => (σ n ω : WithTop ℝ≥0)) : MeasurableSpace Ω :=
  ⨆ n, (isStoppingTime_stopSeq t hσ n).measurableSpace

theorem annSigma_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} (t : ℝ≥0∞)
    {σ : ℕ → Ω → ℝ≥0} (hσ : ∀ n, IsStoppingTime 𝓖 fun ω => (σ n ω : WithTop ℝ≥0)) : annSigma t hσ ≤ mΩ :=
  iSup_le fun n => (isStoppingTime_stopSeq t hσ n).measurableSpace_le

theorem le_annSigma {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} (t : ℝ≥0∞)
    {σ : ℕ → Ω → ℝ≥0} (hσ : ∀ n, IsStoppingTime 𝓖 fun ω => (σ n ω : WithTop ℝ≥0)) (n : ℕ) :
    (isStoppingTime_stopSeq t hσ n).measurableSpace ≤ annSigma t hσ :=
  le_iSup (fun n => (isStoppingTime_stopSeq t hσ n).measurableSpace) n

/-- **The conditional law at the stop for an admissible seed.** -/
theorem ae_condExp_recField_of_admissible {κ : ℝ} (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ) (t : ℝ≥0∞)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (g : Ω → DistOn upperHalfPlaneOpens) (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (hE : Measurable E)
    (hreg : ∀ ω, IsRegularDriver (E ω))
    (hfl : IsFlowLineDriver κ c.fn c.jumps θ Q g (fun s ω => (E ω).1 s) (fun ω => (E ω).2))
    (hseed : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) 0
      (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂Q, min t (E ω).2 ≠ ⊤ →
      Q[fun ω' => Complex.exp (Complex.I * (recField κ (recOf t (E ω')) (g ω') φ : ℂ)) |
          MeasurableSpace.comap (fun ω' => recOf t (E ω')) inferInstance] ω =
        gaussCF (stopWord κ (c, θ, recOf t (E ω))) φ := by
  classical
  obtain ⟨h', 𝓕, VL, VR, B, htr, hC⟩ := hfl
  obtain ⟨hX, -⟩ := hC.2.2.2
  set R : Ω → RecData := fun ω => recOf t (E ω) with hRdef
  have hRm : Measurable R := measurable_recOf hE hreg t
  -- the announcing sequence and the stops
  have : (drivingFiltration Q hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨σ, hσ, -⟩ := WholeField.exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration Q hX) (B := B)
    (κ := κ) (xL := flowLineXL c.fn c.jumps 0) (xR := flowLineXR c.fn c.jumps 0)
    (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VL hX i))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VR hX i))
    hC.1.2.2.2.2 (hC.1.ae_tendsto_threshold hκ) hseed
  have hρ := isStoppingTime_stopSeq t hσ.1
  have h𝓗 : annSigma t hσ.1 ≤ mΩ := annSigma_le t hσ.1
  -- the version of the record
  have hKex : ∀ n, ∃ K : Ω → LocalExt.DrivingHist (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0),
      Measurable[(isStoppingTime_stopSeq t hσ.1 n).measurableSpace] K ∧
      ∀ ω, IsIntegratedSLEPath κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
          (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) (fun s => (E ω).1 s)
          (fun i s => VL i s ω) (fun j s => VR j s ω) (fun s => B s ω) (E ω).2 →
        (stopSeq t σ n ω : ℝ≥0∞) < (E ω).2 →
        K ω = Sec7.stoppedHistory (Sec7.completedState (fun s ω => (E ω).1 s) VL VR fun ω => (E ω).2)
          (fun ω => (stopSeq t σ n ω : WithTop ℝ≥0)) ω := fun n =>
    LocalExt.exists_measurable_stoppedHistory_version hX (hρ n)
  choose K hKm hKeq using hKex
  set R' : Ω → RecData := recVersion t (stopSeq t σ) K with hR'def
  have hR' : Measurable[annSigma t hσ.1] R' := by
    have := @measurable_recVersion Ω (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0) (annSigma t hσ.1) t _ _
      (fun n => (measurable_stopSeq_of hσ.1 n).mono (le_annSigma t hσ.1 n) le_rfl)
      (fun n => (hKm n).mono (le_annSigma t hσ.1 n) le_rfl)
    exact this
  set F : Set Ω := {ω | min t (E ω).2 ≠ ⊤} with hFdef
  set F' : Set Ω := {ω | (⨆ n, (stopSeq t σ n ω : ℝ≥0∞)) ≠ ⊤} with hF'def
  have hF' : MeasurableSet[annSigma t hσ.1] F' := by
    have hm : Measurable[annSigma t hσ.1] fun ω => (⨆ n, (stopSeq t σ n ω : ℝ≥0∞)) :=
      Measurable.iSup fun n => measurable_coe_nnreal_ennreal.comp
        ((measurable_stopSeq_of hσ.1 n).mono (le_annSigma t hσ.1 n) le_rfl)
    exact (hm (measurableSet_singleton ⊤)).compl
  have hFF' : ∀ᵐ ω ∂Q, ω ∈ F' ↔ ω ∈ F := by
    filter_upwards [hσ.2.2.2, ae_all_iff.2 hσ.2.2.1] with ω hann hlt
    have := iSup_coe_stopSeq (t := t) (σ := fun n => σ n ω) hlt hann
    change (⨆ n, ((min t (σ n ω : ℝ≥0∞)).toNNReal : ℝ≥0∞)) ≠ ⊤ ↔ min t (E ω).2 ≠ ⊤
    rw [this]
  have hRR' : ∀ᵐ ω ∂Q, ω ∈ F → R' ω = R ω := by
    filter_upwards [ae_isGoodStopPath hκ hreg hC.1 hseed t, hσ.2.2.2, ae_all_iff.2 hσ.2.2.1, hC.1.2.2.2.2]
      with ω hgood hann hlt hp hωF
    refine recVersion_eq t (hgood hωF) (hσ.2.1 ω) hlt hann fun n => hKeq n ω hp ?_
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (stopSeq_le t σ n ω)) (hlt n)
  -- the kernel at the stop, at fixed and at pushed test functions
  set xLp := (padFL 0 0 c.fn c.jumps).1.1
  set xRp := (padFL 0 0 c.fn c.jumps).1.2
  set ρLp := (padFL κ θ c.fn c.jumps).2.1
  set ρRp := (padFL κ θ c.fn c.jumps).2.2
  set nL := flowLineNL c.fn c.jumps 0
  set nR := flowLineNR c.fn c.jumps 0
  have hker := fun ψ => ae_condExp_cexp_stop hκ hreg hC hseed hX hσ t (padFL_snd_fst_fin κ θ c.fn c.jumps)
    (padFL_snd_snd_fin κ θ c.fn c.jumps) (padFL_fst_fst_fin c.fn c.jumps) (padFL_fst_snd_fin c.fn c.jumps)
    (θ * chiC κ) ψ
  have hM : ∀ r, ContinuousOn (stopMean κ nL nR xLp xRp ρLp ρRp (θ * chiC κ) r) (H \ stopHull r) := by
    intro r
    refine LocalExt.continuousOn_couplingMean_alive (continuous_rdrv r) (rtime_nonneg r) ?_
    exact (LocalExt.continuousOn_of_isBoundedHarmonicExtension
      (BoundaryWord.isBoundedHarmonicExtension_mean _ (isSorted_forceWord _ _ _ _ _ _ _ _))).add continuousOn_const
  have hpush := ae_condExp_cexp_pushTest (Q := Q) h𝓗 hC.2.1 hR' hFF' hRR' hM (fun ψ => hker ψ) φ
  -- the field read in the record chart, through the version
  set X : Ω → ℂ := fun ω => Complex.exp (Complex.I * (recField κ (R ω) (g ω) φ : ℂ)) with hXdef
  set Y : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h' ω (Chart.pushTest (isConformal_recChart (R' ω)) φ) : ℂ))
    with hYdef
  set S : Ω → ℂ := fun ω => Complex.exp (Complex.I * (chartShift κ θ (R' ω) φ : ℂ)) with hSdef
  have hYm : Measurable Y := by
    have hT : ∀ z, Measurable fun ω => Chart.pushTest (isConformal_recChart (R' ω)) φ z := fun z =>
      ((measurable_pushTest_recChart φ z).comp hR').mono h𝓗 le_rfl
    exact GFF.measurable_exp_I_mul (RandomTest.measurable_apply_of_forall_measurable hC.2.1 hT)
  have hYi : Integrable Y Q := GFF.integrable_exp_I_mul
    (RandomTest.measurable_apply_of_forall_measurable hC.2.1 fun z =>
      ((measurable_pushTest_recChart φ z).comp hR').mono h𝓗 le_rfl)
  have hSm : StronglyMeasurable[annSigma t hσ.1] S :=
    (@GFF.measurable_exp_I_mul Ω (annSigma t hσ.1) _ ((measurable_chartShift κ θ φ).comp hR')).stronglyMeasurable
  have hSY : Integrable (fun ω => S ω * Y ω) Q :=
    hYi.bdd_mul (hSm.mono h𝓗).aestronglyMeasurable
      (Eventually.of_forall fun ω => (Complex.norm_exp_I_mul_ofReal _).le)
  have hpull : Q[fun ω => S ω * Y ω | annSigma t hσ.1] =ᵐ[Q] fun ω => S ω * Q[Y | annSigma t hσ.1] ω := by
    have hp := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hSm
      (by simpa [ContinuousLinearMap.mul_apply'] using hSY) hYi
    simpa [ContinuousLinearMap.mul_apply'] using hp
  have hg : Measurable g := by
    refine LQGMetric.measurable_distOn_iff.2 fun ψ => ?_
    have e : (fun ω => g ω ψ) = fun ω => h' ω ψ - θ * chiC κ * ∫ z, ψ z := by
      funext ω
      have := htr ω ψ ψ (fun z => by rw [Complex.ofReal_zero, add_zero])
      linarith
    rw [e]
    exact ((measurable_distOn_apply ψ).comp hC.2.1).sub_const _
  have hXr : Measurable fun ω => recField κ (R ω) (g ω) φ := by
    have h1 := (measurable_recField κ).comp (hRm.prodMk hg)
    have h2 := (measurable_distOn_apply φ).comp h1
    exact h2
  have hXi : Integrable X Q := by
    have h3 := GFF.integrable_exp_I_mul (P := Q) hXr
    exact h3
  have hXSY : ∀ᵐ ω ∂Q, ω ∈ F → X ω = S ω * Y ω := by
    filter_upwards [hRR'] with ω hR hωF
    show Complex.exp (Complex.I * (recField κ (R ω) (g ω) φ : ℂ)) =
      Complex.exp (Complex.I * (chartShift κ θ (R' ω) φ : ℂ)) *
        Complex.exp (Complex.I * (h' ω (Chart.pushTest (isConformal_recChart (R' ω)) φ) : ℂ))
    rw [hR hωF, recField_apply_eq (htr ω) (R ω) φ, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- the conditional law given the announced history
  have hcond : ∀ᵐ ω ∂Q, ω ∈ F → Q[X|annSigma t hσ.1] ω = gaussCF (stopWord κ (c, θ, R ω)) φ := by
    have hind : F'.indicator X =ᵐ[Q] F'.indicator (fun ω => S ω * Y ω) := by
      filter_upwards [hXSY, hFF'] with ω h1 h2
      by_cases hω : ω ∈ F'
      · rw [indicator_of_mem hω, indicator_of_mem hω, h1 (h2.1 hω)]
      · rw [indicator_of_notMem hω, indicator_of_notMem hω]
    have hc1 : Q[F'.indicator X|annSigma t hσ.1] =ᵐ[Q] F'.indicator (Q[X|annSigma t hσ.1]) := condExp_indicator hXi hF'
    have hc2 : Q[F'.indicator (fun ω => S ω * Y ω)|annSigma t hσ.1] =ᵐ[Q]
        F'.indicator (Q[fun ω => S ω * Y ω|annSigma t hσ.1]) :=
      condExp_indicator hSY hF'
    have hc3 : Q[F'.indicator X|annSigma t hσ.1] =ᵐ[Q]
        Q[F'.indicator (fun ω => S ω * Y ω)|annSigma t hσ.1] := condExp_congr_ae hind
    filter_upwards [hc1, hc2, hc3, hpull, hpush, hFF', hRR'] with ω h1 h2 h3 h4 h5 h6 h7 hωF
    have hω : ω ∈ F' := h6.2 hωF
    have e1 : Q[X|annSigma t hσ.1] ω = Q[fun ω => S ω * Y ω|annSigma t hσ.1] ω := by
      have := h1.symm.trans (h3.trans h2)
      simpa only [indicator_of_mem hω] using this
    rw [e1, h4, h5 hωF]
    simp only [hSdef, h7 hωF]
    exact cexp_chartShift_mul_eq_gaussCF κ θ nL nR xLp xRp ρLp ρRp (R ω) φ
  -- the tower property to the record σ-algebra
  have hRle : MeasurableSpace.comap R inferInstance ≤ mΩ := hRm.comap_le
  have hYgm : Measurable[MeasurableSpace.comap R inferInstance]
      fun ω => gaussCF (stopWord κ (c, θ, R ω)) φ :=
    ((measurable_gaussCF φ).comp ((measurable_stopWord κ).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id)))).comp (comap_measurable R)
  have hYgi : Integrable (fun ω => gaussCF (stopWord κ (c, θ, R ω)) φ) Q :=
    Integrable.of_bound (C := 1) (hYgm.mono hRle le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun ω => norm_gaussCF_le _ φ)
  have hFm : MeasurableSet[MeasurableSpace.comap R inferInstance] F := by
    refine ⟨{r : RecData | r.2.1 ≠ ⊤}, ?_, rfl⟩
    exact ((measurable_fst.comp measurable_snd) (measurableSet_singleton ⊤)).compl
  refine ae_condExp_eq_of_setIntegral_eq hRle hFm hXi hYgm.stronglyMeasurable hYgi ?_
  rintro A ⟨S0, hS0, rfl⟩
  set Bset : Set Ω := R' ⁻¹' S0 ∩ F' with hBdef
  have hB : MeasurableSet[annSigma t hσ.1] Bset := (hR' hS0).inter hF'
  have hAB : (R ⁻¹' S0 ∩ F : Set Ω) =ᵐ[Q] Bset := by
    rw [Filter.eventuallyEqSet_iff]
    filter_upwards [hFF', hRR'] with ω h1 h2
    simp only [hBdef, mem_inter_iff, mem_preimage]
    by_cases hωF : ω ∈ F
    · rw [h2 hωF]
      exact ⟨fun h => ⟨h.1, h1.2 h.2⟩, fun h => ⟨h.1, hωF⟩⟩
    · exact ⟨fun h => absurd h.2 hωF, fun h => absurd (h1.1 h.2) hωF⟩
  calc ∫ ω in R ⁻¹' S0 ∩ F, X ω ∂Q = ∫ ω in Bset, X ω ∂Q := setIntegral_congr_set hAB
    _ = ∫ ω in Bset, (Q[X|annSigma t hσ.1]) ω ∂Q := (setIntegral_condExp h𝓗 hXi hB).symm
    _ = ∫ ω in Bset, gaussCF (stopWord κ (c, θ, R ω)) φ ∂Q := by
        refine setIntegral_congr_ae (h𝓗 _ hB) ?_
        filter_upwards [hcond, hFF'] with ω h1 h2 hωB using h1 (h2.1 hωB.2)
    _ = ∫ ω in R ⁻¹' S0 ∩ F, gaussCF (stopWord κ (c, θ, R ω)) φ ∂Q := (setIntegral_congr_set hAB).symm

end StagedLaw

end Exist

end InteractingSLE
