import InteractingSLE.Spec.Coupling.WholeField2Kernel
import InteractingSLE.Spec.Coupling.CouplingThrough

/-!
# WF2 kernel statements for couplings through a stop

The zero-boundary GFF clause transfers directly from the WFS interface. The remaining kernel copies will be
added here after their stopping-time localization prerequisites are available.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open LocalSets QuantumZipper LQGMetric Coupling

universe u

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ V : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

omit [IsProbabilityMeasure P] in
/-- `h − 𝔥₀` is a zero-boundary GFF for a coupling through a stop. -/
theorem isZeroBoundaryGFF_centredField_through
    (hC : WFS.IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) :
    IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P := by
  refine ⟨measurable_centredField hC.2.2.1 u₀, ?_⟩
  have e : (fun φ ω => centredField h u₀ ω φ) = fun φ ω => h ω φ - ∫ z, u₀ z * φ z := by
    funext φ ω
    exact centredField_apply h hu₀.1 ω φ
  rw [e]
  exact hC.2.2.2.1 u₀ hu₀

omit [IsProbabilityMeasure P] in
/-- The support avoidance event is measurable in the stopped history up to null sets when the cutoff is announced. -/
theorem exists_measurableSet_ae_iff_disjoint_through
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hXV : IsMeasurableKilledDriving W VL VR V) (hVζ : ∀ ω, V ω ≤ ζ ω)
    {σ : ℕ → Ω → ℝ≥0} (hσ : IsAnnouncingSeq (drivingFiltration P hXV) P V σ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (drivingFiltration P hXV) τ)
    (hτV : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < V ω) {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) :
    ∃ G : Set Ω, MeasurableSet[hτ.measurableSpace] G ∧
      ∀ᵐ ω ∂P, (ω ∈ G ↔ Disjoint C (fwdHull (fun s : ℝ => W s.toNNReal ω)
        ((τ ω).untopD 0 : ℝ≥0))) := by
  obtain ⟨m, hm, hCm⟩ := exists_pos_le_im_of_isCompact hC hCH
  have hpath : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 := by
    filter_upwards [hE.2.2.2.2] with ω hp using ⟨hp.2.2.2.1, hp.1⟩
  have hpathV : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < V ω} ∧ W 0 ω = 0 := by
    filter_upwards [hpath] with ω hp
    have hsubset : {t : ℝ≥0 | (t : ℝ≥0∞) < V ω} ⊆ {t | (t : ℝ≥0∞) < ζ ω} :=
      fun _ ht => lt_of_lt_of_le ht (hVζ ω)
    exact ⟨hp.1.mono hsubset, hp.2⟩
  obtain ⟨ρ, hρst, -, -, hρsafe, hρex⟩ := exists_safeSeq_of_adapted (𝓗 := killedDrivingFiltration hXV)
    (adaptedBefore_killedDriving_W hXV) hpathV hC hCH hm hCm hσ.1 hσ.2.1 hσ.2.2.1
  refine ⟨⋃ n, {ω | τ ω ≤ ((ρ n ω : ℝ≥0) : WithTop ℝ≥0)},
    MeasurableSet.iUnion fun n => hτ.measurableSet_le_stopping_time (hρst n), ?_⟩
  filter_upwards [hτV, ae_all_iff.2 hρsafe, hρex, hσ.2.2.2, hE.2.2.2.2] with ω hτω hsafe hex hann hp
  have hτtop : τ ω ≠ ⊤ := fun h' => by rw [h'] at hτω; exact absurd hτω (not_lt.2 le_top)
  set s : ℝ≥0 := (τ ω).untopD 0 with hs_def
  have hτs : τ ω = (s : WithTop ℝ≥0) := (coe_untopD_of_ne_top hτtop).symm
  have hsV : (s : ℝ≥0∞) < V ω := by
    change (τ ω : ℝ≥0∞) < V ω at hτω
    rw [hτs] at hτω
    exact hτω
  have hsζ : (s : ℝ≥0∞) < ζ ω := lt_of_lt_of_le hsV (hVζ ω)
  constructor
  · rintro hω
    obtain ⟨n, hn⟩ := mem_iUnion.1 hω
    have hsn : s ≤ ρ n ω := by
      have : (s : WithTop ℝ≥0) ≤ ((ρ n ω : ℝ≥0) : WithTop ℝ≥0) := by rw [← hτs]; exact hn
      exact_mod_cast this
    refine Set.disjoint_left.2 fun z hz hzK => ?_
    have hS := hsafe n
    have hz' : z ∉ fwdHull (Ito.rpath fun t => W t ω) (ρ n ω) :=
      notMem_fwdHull_of_alive hp.2.2.2.1 (lt_of_lt_of_le hS.1 (hVζ ω)) (hCH hz)
        (hS.2.2.2 z hz).1
    exact hz' ((QuantumZipper.fwdHull_mono).1 (by exact_mod_cast hsn) hzK)
  · intro hdis
    have halive : ∀ z ∈ C, ∃ u, IsForwardSol (Ito.rpath fun t => W t ω) z s u := fun z hz =>
      Ito.exists_isForwardSol_of_mem s.coe_nonneg ⟨hCH hz, fun h' => hdis.ne_of_mem hz h' rfl⟩
    obtain ⟨j, hj⟩ := hann s hsV
    obtain ⟨n, hn⟩ := (hex j s hj halive).exists
    refine mem_iUnion.2 ⟨n, ?_⟩
    show τ ω ≤ ((ρ n ω : ℝ≥0) : WithTop ℝ≥0)
    rw [hτs]
    exact_mod_cast hn

omit [IsProbabilityMeasure P] in
/-- A hitting-measurable hull version is measurable in the cutoff history up to null sets. -/
theorem measurable_hull_stopping_through
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hXV : IsMeasurableKilledDriving W VL VR V) (hVζ : ∀ ω, V ω ≤ ζ ω)
    {σ₀ : ℕ → Ω → ℝ≥0} (hσ₀ : IsAnnouncingSeq (drivingFiltration P hXV) P V σ₀)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (drivingFiltration P hXV) τ)
    (hτV : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < V ω)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAK : ∀ᵐ ω ∂P, A ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) :
    Measurable[hτ.measurableSpace, hittingSigma] A := by
  refine @measurable_generateFrom _ _ hτ.measurableSpace _ _ ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have hne : Uᶜ.Nonempty := ⟨0, fun h0 => by
    have : (0 : ℝ) < (0 : ℂ).im := hUH h0
    simp at this⟩
  choose G hGm hGiff using fun k => exists_measurableSet_ae_iff_disjoint_through hE hXV hVζ hσ₀ hτ hτV
    (isCompact_openExhaust U k) ((openExhaust_subset k).trans hUH)
  refine measurableSet_of_ae_eq hτ.measurableSpace_le
    (fun N hN h0 => measurableSet_stopping_driving_of_null hXV hτ hN h0)
    (hA (measurableSet_hitting hU hUH)) (MeasurableSet.iInter fun k => hGm k).compl ?_
  filter_upwards [ae_all_iff.2 hGiff, hAK] with ω h1 h2
  apply propext
  simp only [mem_preimage, mem_ofPred_eq, mem_compl_iff, mem_iInter, not_forall, h1, h2]
  constructor
  · rintro ⟨z, hzA, hzU⟩
    rw [← iUnion_openExhaust hU hne] at hzU
    obtain ⟨k, hk⟩ := mem_iUnion.1 hzU
    exact ⟨k, fun hd => Set.disjoint_left.1 hd hk hzA⟩
  · rintro ⟨k, hk⟩
    obtain ⟨z, hzC, hzK⟩ := Set.not_disjoint_iff.1 hk
    exact ⟨z, hzK, openExhaust_subset k hzC⟩

omit [IsProbabilityMeasure P] in
/-- Nesting of history-marked germs for cutoff-filtration stopping times. -/
theorem histGerm_hull_mono_through
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hXV : IsMeasurableKilledDriving W VL VR V) (hVζ : ∀ ω, V ω ≤ ζ ω)
    {σ₀ : ℕ → Ω → ℝ≥0} (hσ₀ : IsAnnouncingSeq (drivingFiltration P hXV) P V σ₀)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime (drivingFiltration P hXV) σ)
    (hτ : IsStoppingTime (drivingFiltration P hXV) τ) (hστ : σ ≤ τ)
    (hσV : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < V ω) (hτV : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < V ω)
    {Aσ Aτ : Ω → Set ℂ} (hAσ : Measurable[mΩ, hittingSigma] Aσ)
    (hAτ : Measurable[mΩ, hittingSigma] Aτ)
    (hAσK : ∀ᵐ ω ∂P, Aσ ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0))
    (hAτK : ∀ᵐ ω ∂P, Aτ ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
    (hh : Measurable h) :
    histGerm hσ.measurableSpace Aσ h ≤ histGerm hτ.measurableSpace Aτ h := by
  refine histGerm_mono (P := P) (hσ.measurableSpace_mono hτ hστ) hτ.measurableSpace_le
    (fun N hN h0 => measurableSet_stopping_driving_of_null hXV hτ hN h0)
    ((measurable_hull_stopping_through hE hXV hVζ hσ₀ hσ hσV hAσ hAσK).mono
      (hσ.measurableSpace_mono hτ hστ) le_rfl)
    hAτ hh ?_
  filter_upwards [hAσK, hAτK, hτV] with ω h1 h2 h3
  rw [h1, h2]
  refine (QuantumZipper.fwdHull_mono).1 ?_
  have hτtop : τ ω ≠ ⊤ := fun h' => by rw [h'] at h3; exact absurd h3 (not_lt.2 le_top)
  have hle := hστ ω
  rw [← coe_untopD_of_ne_top hτtop] at hle
  have hσtop : σ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hle
  rw [← coe_untopD_of_ne_top hσtop] at hle
  exact NNReal.coe_le_coe.2 (WithTop.coe_le_coe.1 hle)

/-- History-marked avoidance for a coupling through `V`, assuming an announcing sequence of `V`. -/
theorem isHistoryAvoidanceLocal_hull_through
    (hC : WFS.IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h)
    (_hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {σ₀ : ℕ → Ω → ℝ≥0}
    (hσ₀ : IsAnnouncingSeq (drivingFiltration P hC.2.2.2.2.choose) P V σ₀)
    {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hC.2.2.2.2.choose) τ)
    (hτV : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < V ω)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAK : ∀ᵐ ω ∂P, A ω = fwdHull (fun s : ℝ => W s.toNNReal ω)
      ((τ ω).untopD 0 : ℝ≥0)) :
    IsHistoryAvoidanceLocal hτ.measurableSpace A (centredField h u₀) P := by
  have hE := hC.1
  have hker := hC.2.2.2.2.choose_spec
  have hFd := isHarmonicDistOn_smoothDist hu₀.1
  have hh0m := measurable_centredField hC.2.2.1 u₀
  have hΦK : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < V ω →
      hullClock (fwdHull (Ito.rpath fun s => W s ω) t) = t := by
    filter_upwards [hE.2.2.2.2] with ω hp t ht
    exact hullClock_fwdHull_rpath hp.2.2.2.1 hp.1 (lt_of_lt_of_le ht (hC.2.1 ω))
  refine isHistoryAvoidanceLocal_of_capacity (K := fun t ω => fwdHull (fun s : ℝ => W s.toNNReal ω) t)
    hh0m measurable_hullClock hΦK hσ₀ ?_ hτ hτV hA hAK
  intro S hS hSV
  have hloc := hker S hS hSV
  have hloc' := IsLocalSet.sub_dist hloc.1 hFd
  obtain ⟨A', hA'm, hA'e, hA'loc⟩ := IsLocalSet.exists_measurable_version hloc' hh0m
  exact ⟨A', hA'm, hA'e, LocalSets.IsLocalSet.isMarkedAvoidanceLocal hh0m hA'm hA'loc⟩

/-- The frozen kernel given the hull germ and stopped history for a coupling through `V`, assuming `V` is announced. -/
theorem ae_condExp_germSigma_hull_eq_through
    (hC : WFS.IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {σ₀ : ℕ → Ω → ℝ≥0}
    (hσ₀ : IsAnnouncingSeq (drivingFiltration P hC.2.2.2.2.choose) P V σ₀)
    {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hC.2.2.2.2.choose) τ)
    (hτV : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < V ω)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAK : ∀ᵐ ω ∂P, A ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
    {u : Ω → ℂ → ℝ}
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (u ω))
    (φ : TestOn upperHalfPlaneOpens) :
    (∀ᵐ ω ∂P, Disjoint (tsupport φ) (A ω) →
      (P[fun ω' => centredField h u₀ ω' φ | germSigma A (centredField h u₀) ⊔ hτ.measurableSpace]) ω =
        (∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) z * φ z) -
          ∫ z, u₀ z * φ z) ∧
    ∀ᵐ ω ∂P, Disjoint (tsupport φ) (A ω) →
      (P[fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)) |
          germSigma A (centredField h u₀) ⊔ hτ.measurableSpace]) ω =
        Complex.exp (Complex.I * (((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω)
          ((τ ω).untopD 0 : ℝ≥0) (u ω) z * φ z) - ∫ z, u₀ z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ A ω) φ φ) : ℝ) : ℂ) := by
  classical
  set h0 := centredField h u₀ with hh0_def
  let hX := hC.2.2.2.2.choose
  have hℋ : hτ.measurableSpace ≤ mΩ := hτ.measurableSpace_le
  have hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens h0 P := isZeroBoundaryGFF_centredField_through hC hu₀
  have hloc := isHistoryAvoidanceLocal_hull_through hC hκ hu₀ hσ₀ hτ hτV hA hAK
  have hE := hC.1
  have hker := hC.2.2.2.2.choose_spec
  have hker' := hker τ hτ hτV
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := by
    filter_upwards [hker'.1.2.1, hAK] with ω h1 h2
    rw [h2]
    exact h1
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · exfalso
    have hF : ∀ᵐ ω ∂P, False := by
      filter_upwards [hE.2.2.2.2, hτV] with ω hp hlt
      have hltζ : (τ ω : ℝ≥0∞) < ζ ω := lt_of_lt_of_le hlt (hC.2.1 ω)
      rw [WangWu.IsIntegratedSLEPath.lifetime_eq_zero_of_threshold hp hseed] at hltζ
      exact ENNReal.not_lt_zero hltζ
    obtain ⟨_, h⟩ := hF.exists
    exact h
  obtain ⟨G, hGm, hGiff⟩ := exists_measurableSet_ae_iff_disjoint_through hE hX hC.2.1 hσ₀ hτ hτV
    φ.hasCompactSupport.isCompact φ.tsupport_subset
  set M : Ω → ℝ := fun ω => ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω)
    ((τ ω).untopD 0 : ℝ≥0) (u ω) z * φ z with hM_def
  set a : ℝ := ∫ z, u₀ z * φ z with ha_def
  have hfreq : ∀ c : ℝ, ∀ᵐ ω ∂P, Disjoint (tsupport φ) (A ω) →
      (P[fun ω' => Complex.exp (Complex.I * ((c * h0 ω' φ : ℝ) : ℂ)) | hτ.measurableSpace]) ω =
        Complex.exp (Complex.I * ((c * (M ω - a) : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (c ^ 2 * zeroGFFTestCov (H \ A ω) φ φ)) : ℝ) : ℂ) := by
    intro c
    have hk := hker'.2 u hu (c • φ)
    have hsm := condExp_smul (μ := P) (Complex.exp (-(Complex.I * ((c * a : ℝ) : ℂ))))
      (fun ω' => Complex.exp (Complex.I * (h ω' (c • φ) : ℂ))) hτ.measurableSpace
    have e1 : (fun ω' => Complex.exp (Complex.I * ((c * h0 ω' φ : ℝ) : ℂ))) =
        Complex.exp (-(Complex.I * ((c * a : ℝ) : ℂ))) •
          fun ω' => Complex.exp (Complex.I * (h ω' (c • φ) : ℂ)) := by
      funext ω'
      rw [Pi.smul_apply, smul_eq_mul, ← Complex.exp_add, hh0_def, centredField_apply h hu₀.1, map_smul,
        smul_eq_mul]
      congr 1
      push_cast
      ring
    filter_upwards [hk, hsm, hAK, hE.2.2.2.2, hτV] with ω hkω hsmω hAω hp hτω hdis
    have hdisK : Disjoint (tsupport φ)
        (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) := hAω ▸ hdis
    have hdisc := hdisK.mono_left (tsupport_smul_testOn_subset c φ)
    have hτtop : τ ω ≠ ⊤ := fun h' => by rw [h'] at hτω; exact absurd hτω (not_lt.2 le_top)
    have hsζ : (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by
      rw [← coe_untopD_of_ne_top hτtop] at hτω
      exact lt_of_lt_of_le hτω (hC.2.1 ω)
    have hen := loewnerGreenEnergy_rpath_eq_zeroGFFTestCov hp.2.2.2.1 hp.1 hsζ φ hdisK
    rw [e1, hsmω, Pi.smul_apply, smul_eq_mul, hkω hdisc, integral_mul_smul, FunLike.coe_smul,
      loewnerGreenEnergy_smul, hen, ← hAω, ← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  set ψ : ℕ → Ω → ℂ := fun n =>
    P[fun ω' => Complex.exp (Complex.I *
      ((1 / ((n : ℝ) + 1) * h0 ω' φ : ℝ) : ℂ)) | hτ.measurableSpace] with hψ_def
  have hψm : ∀ n, StronglyMeasurable[hτ.measurableSpace] (ψ n) := fun n => stronglyMeasurable_condExp
  have hmm : Measurable[hτ.measurableSpace] (meanOfCharFun ψ) := measurable_meanOfCharFun hψm
  have hmeq : ∀ᵐ ω ∂P, Disjoint (tsupport φ) (A ω) → meanOfCharFun ψ ω = M ω - a := by
    filter_upwards [ae_all_iff.2 fun n : ℕ => hfreq (1 / ((n : ℝ) + 1))] with ω hω hdis
    exact meanOfCharFun_eq fun n => hω n hdis
  have hkern : ∀ c : ℝ, ∀ᵐ ω ∂P, ω ∈ G →
      (P[fun ω' => Complex.exp (Complex.I * ((c * h0 ω' φ : ℝ) : ℂ)) | hτ.measurableSpace]) ω =
        Complex.exp (Complex.I * ((c * meanOfCharFun ψ ω : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (c ^ 2 * zeroGFFTestCov (H \ A ω) φ φ)) : ℝ) : ℂ) := by
    intro c
    filter_upwards [hfreq c, hmeq, hGiff, hAK] with ω h1 h2 h3 h4 hωG
    have hdis : Disjoint (tsupport φ) (A ω) := by rw [h4]; exact h3.1 hωG
    rw [h2 hdis]
    exact h1 hdis
  obtain ⟨k1, k2⟩ := ae_condExp_germSigma_history_eq hh0 hA hℋ hloc hAc φ hGm hmm hkern
  refine ⟨?_, ?_⟩
  · filter_upwards [k1, hmeq, hGiff, hAK] with ω h1 h2 h3 h4 hdis
    have hωG : ω ∈ G := h3.2 (h4 ▸ hdis)
    rw [h1 hωG, h2 hdis]
  · filter_upwards [k2, hmeq, hGiff, hAK] with ω h1 h2 h3 h4 hdis
    have hωG : ω ∈ G := h3.2 (h4 ▸ hdis)
    rw [h1 hωG, h2 hdis]

/-- The same conditional kernel holds given the history-marked germ `Γτ`, assuming `V` is announced. -/
theorem ae_condExp_histGerm_hull_eq_through
    (hC : WFS.IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {σ₀ : ℕ → Ω → ℝ≥0}
    (hσ₀ : IsAnnouncingSeq (drivingFiltration P hC.2.2.2.2.choose) P V σ₀)
    {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hC.2.2.2.2.choose) τ)
    (hτV : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < V ω)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAK : ∀ᵐ ω ∂P, A ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
    {u : Ω → ℂ → ℝ}
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (u ω))
    (φ : TestOn upperHalfPlaneOpens) :
    (∀ᵐ ω ∂P, Disjoint (tsupport φ) (A ω) →
      (P[fun ω' => centredField h u₀ ω' φ | histGerm hτ.measurableSpace A (centredField h u₀)]) ω =
        (∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) z * φ z) -
          ∫ z, u₀ z * φ z) ∧
    ∀ᵐ ω ∂P, Disjoint (tsupport φ) (A ω) →
      (P[fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)) |
          histGerm hτ.measurableSpace A (centredField h u₀)]) ω =
        Complex.exp (Complex.I * (((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω)
          ((τ ω).untopD 0 : ℝ≥0) (u ω) z * φ z) - ∫ z, u₀ z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ A ω) φ φ) : ℝ) : ℂ) := by
  have hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P :=
    isZeroBoundaryGFF_centredField_through hC hu₀
  have hℋ : hτ.measurableSpace ≤ mΩ := hτ.measurableSpace_le
  have hloc := isHistoryAvoidanceLocal_hull_through hC hκ hu₀ hσ₀ hτ hτV hA hAK
  have hmk := isCoverMarking_history hh0 hA hℋ hloc
  have hker := hC.2.2.2.2.choose_spec
  have hker' := hker τ hτ hτV
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := by
    filter_upwards [hker'.1.2.1, hAK] with ω h1 h2
    rw [h2]
    exact h1
  have h𝒦tr : ∀ j, histGerm hτ.measurableSpace A (centredField h u₀) ≤
      aeSigma (coverSigmaM (MeasurableSpace.comap A hittingSigma ⊔ hτ.measurableSpace) j A
        (centredField h u₀)) P := by
    intro j
    refine (iInf_le _ (j + 1)).trans (sup_le ?_ ?_)
    · exact (le_sup_right : hτ.measurableSpace ≤ MeasurableSpace.comap A hittingSigma ⊔ hτ.measurableSpace).trans
        ((le_sup_left : _ ≤ coverSigmaM _ j A (centredField h u₀)).trans (le_aeSigma _ P))
    · rw [← coverRad_eq j]
      exact germSigmaAt_le_aeSigmaM hh0 le_sup_left j
  have h𝒦le := histGerm_le (h := centredField h u₀) hℋ hA hh0.measurable
  obtain ⟨M, hMg, -, hM1, hM2⟩ := exists_condExp_germSigmaK hh0 hA hmk hAc
    (germSigma_le_histGerm A (centredField h u₀)) h𝒦le h𝒦tr φ
  have h12 : germSigma A (centredField h u₀) ⊔ hτ.measurableSpace ≤
      histGerm hτ.measurableSpace A (centredField h u₀) :=
    sup_le (germSigma_le_histGerm A _) (le_histGerm A _)
  have hmean : P[fun ω' => centredField h u₀ ω' φ | histGerm hτ.measurableSpace A (centredField h u₀)] =ᵐ[P]
      P[fun ω' => centredField h u₀ ω' φ | germSigma A (centredField h u₀) ⊔ hτ.measurableSpace] := by
    have hM' : Measurable[germSigma A (centredField h u₀) ⊔ hτ.measurableSpace] M :=
      hMg.mono le_sup_left le_rfl
    have hMs : StronglyMeasurable[germSigma A (centredField h u₀) ⊔ hτ.measurableSpace] M :=
      hM'.stronglyMeasurable
    exact hM1.symm.trans (condExp_ae_eq_of_le_of_ae_eq h12 h𝒦le hMs hM1.symm).symm
  have hchar : P[fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)) |
        histGerm hτ.measurableSpace A (centredField h u₀)] =ᵐ[P]
      P[fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)) |
        germSigma A (centredField h u₀) ⊔ hτ.measurableSpace] := by
    have hv : Measurable[germSigma A (centredField h u₀) ⊔ hτ.measurableSpace]
        fun ω => zeroGFFTestCov (H \ relClosureH (A ω)) φ φ :=
      (measurable_comap_zeroGFFTestCov_compl A φ φ).mono
        ((comap_le_germSigma A _).trans le_sup_left) le_rfl
    have hM' : Measurable[germSigma A (centredField h u₀) ⊔ hτ.measurableSpace] M :=
      hMg.mono le_sup_left le_rfl
    have hF : Measurable[germSigma A (centredField h u₀) ⊔ hτ.measurableSpace]
        fun ω => Complex.exp (Complex.I * (M ω : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (A ω)) φ φ) : ℝ) : ℂ) := by
      refine Measurable.mul ?_ ?_
      · exact Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hM'))
      · exact Complex.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hv))
    exact hM2.symm.trans
      (condExp_ae_eq_of_le_of_ae_eq h12 h𝒦le hF.stronglyMeasurable hM2.symm).symm
  obtain ⟨k1, k2⟩ := ae_condExp_germSigma_hull_eq_through hC hκ hu₀ hσ₀ hτ hτV hA hAK hu φ
  refine ⟨?_, ?_⟩
  · filter_upwards [k1, hmean] with ω h1 h2 hdis
    rw [h2]
    exact h1 hdis
  · filter_upwards [k2, hchar] with ω h1 h2 hdis
    rw [h2]
    exact h1 hdis

/-- The stopped history-marked germ filtration carries the frozen conditional mean up to `V`. -/
theorem exists_germFiltration_martingale_through
    (hC : WFS.IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {σ₀ : ℕ → Ω → ℝ≥0}
    (hσ₀ : IsAnnouncingSeq (drivingFiltration P hC.2.2.2.2.choose) P V σ₀)
    {σ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hC.2.2.2.2.choose) σ)
    (hσV : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < V ω) :
    ∃ (A : ℝ≥0 → Ω → Set ℂ) (𝒢 : Filtration ℝ≥0 mΩ),
      (∀ t, Measurable[mΩ, hittingSigma] (A t)) ∧
      (∀ t, ∀ᵐ ω ∂P, A t ω = fwdHull (fun s : ℝ => W s.toNNReal ω)
        ((min (σ ω) (t : WithTop ℝ≥0)).untopD 0 : ℝ≥0)) ∧
      (∀ t, 𝒢 t = histGerm (hσ.min_const t).measurableSpace (A t) (centredField h u₀)) ∧
      (∀ t, (hσ.min_const t).measurableSpace ≤ 𝒢 t) ∧
      ∀ φ : TestOn upperHalfPlaneOpens,
        Martingale (fun t => P[fun ω => centredField h u₀ ω φ | 𝒢 t]) 𝒢 P ∧
        ∀ (u : ℝ≥0 → Ω → ℂ → ℝ), (∀ (t : ℝ≥0) (ω : Ω), IsBoundedHarmonicExtension
            (forceBoundaryData κ ρL ρR
              (fun i => VL i ((min (σ ω) (t : WithTop ℝ≥0)).untopD 0) ω -
                W ((min (σ ω) (t : WithTop ℝ≥0)).untopD 0) ω)
              (fun i => VR i ((min (σ ω) (t : WithTop ℝ≥0)).untopD 0) ω -
                W ((min (σ ω) (t : WithTop ℝ≥0)).untopD 0) ω))
            (forceJumpSet
              (fun i => VL i ((min (σ ω) (t : WithTop ℝ≥0)).untopD 0) ω -
                W ((min (σ ω) (t : WithTop ℝ≥0)).untopD 0) ω)
              (fun i => VR i ((min (σ ω) (t : WithTop ℝ≥0)).untopD 0) ω -
                W ((min (σ ω) (t : WithTop ℝ≥0)).untopD 0) ω)) (u t ω)) →
          ∀ t : ℝ≥0, ∀ᵐ ω ∂P, Disjoint (tsupport φ) (A t ω) →
            (P[fun ω' => centredField h u₀ ω' φ | 𝒢 t]) ω =
              (∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω)
                ((min (σ ω) (t : WithTop ℝ≥0)).untopD 0 : ℝ≥0) (u t ω) z * φ z) -
                ∫ z, u₀ z * φ z := by
  have hτ : ∀ t : ℝ≥0, IsStoppingTime (drivingFiltration P hC.2.2.2.2.choose)
      (fun ω => min (σ ω) (t : WithTop ℝ≥0)) := fun t => hσ.min_const t
  have hτV : ∀ t : ℝ≥0, ∀ᵐ ω ∂P,
      ((min (σ ω) (t : WithTop ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) < V ω := by
    intro t
    filter_upwards [hσV] with ω hω
    exact lt_of_le_of_lt (min_le_left _ _) hω
  have hh0m := measurable_centredField hC.2.2.1 u₀
  have hE := hC.1
  let hX := hC.2.2.2.2.choose
  have hker := hC.2.2.2.2.choose_spec
  have hver : ∀ t : ℝ≥0, ∃ A' : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A' ∧
      A' =ᵐ[P] fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω)
        ((min (σ ω) (t : WithTop ℝ≥0)).untopD 0 : ℝ≥0) := fun t => by
    obtain ⟨A', hA'm, hA'e, -⟩ := IsLocalSet.exists_measurable_version
      ((hker _ (hτ t) (hτV t)).1) hC.2.2.1
    exact ⟨A', hA'm, hA'e⟩
  choose A hAm hAK using hver
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · exfalso
    have hF : ∀ᵐ ω ∂P, False := by
      filter_upwards [hE.2.2.2.2, hσV] with ω hp hlt
      have hltζ : (σ ω : ℝ≥0∞) < ζ ω := lt_of_lt_of_le hlt (hC.2.1 ω)
      rw [WangWu.IsIntegratedSLEPath.lifetime_eq_zero_of_threshold hp hseed] at hltζ
      exact ENNReal.not_lt_zero hltζ
    obtain ⟨_, h'⟩ := hF.exists
    exact h'
  let 𝒢 : Filtration ℝ≥0 mΩ :=
    { seq := fun t => histGerm (hτ t).measurableSpace (A t) (centredField h u₀)
      mono' := fun s t hst => histGerm_hull_mono_through hE hX hC.2.1 hσ₀
        (hτ s) (hτ t) (fun ω => min_le_min le_rfl (WithTop.coe_le_coe.2 hst)) (hτV s) (hτV t)
        (hAm s) (hAm t) (hAK s) (hAK t) hh0m
      le' := fun t => histGerm_le (hτ t).measurableSpace_le (hAm t) hh0m }
  refine ⟨A, 𝒢, hAm, hAK, fun t => rfl, fun t => le_histGerm _ _, fun φ => ⟨?_, ?_⟩⟩
  · exact martingale_condExp _ 𝒢 P
  · intro u hu t
    exact (ae_condExp_histGerm_hull_eq_through hC hκ hu₀ hσ₀ (hτ t) (hτV t) (hAm t) (hAK t)
      (hu t) φ).1

end WholeField

end InteractingSLE
