/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtOHull
import InteractingSLE.Spec.Sec7.LocalExtMMain

/-!
# Locality of the restarted hulls under `Q`, on one piece of the cell

Packet PROVE-LOCEXT-O. For the data of `RestartLocalityInput` and a stop `τ ≤ S₀` of the restarted filtration (finite
everywhere), take a stopping time `σ < ζ` of the driving filtration and an event `E ⊆ D` of the stopped σ-algebra `𝓓_σ`
on which `σ = T + τ` and the energy of the restart word's source is bounded. On `E`, conditionally on
`𝒢 = 𝒜_B ∨ 𝓓_σ` (`B` the hull at `σ`):

1. (locality conditional on the history at the restart, with the word in `𝒢`) `h⁰ = h₁ + Z`, `Z` a zero-boundary GFF
   on `ℍ ∖ K_σ` given `𝒢` (history-marked locality `isHistoryAvoidanceLocal_hull`, Lemma 3.6 (iii) with marks);
2. (transport by the restart chart) the restarted field `restartField κ (h, K)` is a `𝒢`-measurable harmonic part plus
   a zero-boundary GFF on `ℍ ∖ K'_τ` given `𝒢` (`exists_condDecomp_chart`, `ℍ ∖ K_σ = f_T⁻¹(ℍ ∖ K'_τ)` by `restart_path`);
3. (the tilt with a random source) under `Q[· | E]` the recoded field has the same structure (`exists_condLocal_withDensity_tilt_rand`
   with the `𝒢`-measurable source `srcTestW` of the restart word and shift `f − q` of the word).

Main result: **`exists_condLocal_restart_piece`**. Helpers: `IsCondZeroBoundaryGFF.congr_ae`, `cond_withDensity_eq`,
`compl_fwdHull_restart_eq_image`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open QuantumZipper (H fwdHull zeroGFFTestCov)
open scoped ENNReal NNReal

universe u

namespace InteractingSLE

namespace LocalExt

open LQGMetric LocalSets WholeField Sec7 Sec5.Markov Sec2.Restart

/-! ### Generic helpers -/

section Helpers

variable {Ω : Type*}

/-- A conditional zero-boundary law is unchanged by almost sure modifications of the domain and of the field. -/
theorem IsCondZeroBoundaryGFF.congr_ae {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {U U' : Ω → Set ℂ}
    {X X' : Ω → DistOn upperHalfPlaneOpens} (hX : IsCondZeroBoundaryGFF P 𝒢 U X) (hU : ∀ᵐ ω ∂P, U ω = U' ω)
    (hXX : ∀ᵐ ω ∂P, X ω = X' ω) : IsCondZeroBoundaryGFF P 𝒢 U' X' := by
  intro φ
  have e : (fun ω => Complex.exp (Complex.I * (X' ω φ : ℂ))) =ᵐ[P]
      fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) := by
    filter_upwards [hXX] with ω hω
    rw [hω]
  filter_upwards [condExp_congr_ae e, hX φ, hU] with ω h1 h2 h3
  rw [h1, h2, h3]

/-- **The conditioned tilted measure**: `(f · μ)[· | E] = (c f) · μ[· | E]` with `c = μ(E) / (f · μ)(E)`. -/
theorem cond_withDensity_eq [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ≥0∞} (hf : Measurable f) {E : Set Ω} (hE : MeasurableSet E)
    (hμE : μ E ≠ 0) (hμE' : μ E ≠ ∞) :
    (μ.withDensity f)[|E] = (μ[|E]).withDensity fun ω => μ E * ((μ.withDensity f) E)⁻¹ * f ω := by
  ext S hS
  rw [cond_apply hE, withDensity_apply _ (hE.inter hS), withDensity_apply _ hS, ProbabilityTheory.cond,
    Measure.restrict_smul, lintegral_smul_measure, Measure.restrict_restrict hS,
    lintegral_const_mul _ hf, inter_comm S E, smul_eq_mul, ← mul_assoc, ← mul_assoc,
    ENNReal.inv_mul_cancel hμE hμE', one_mul]

end Helpers

/-! ### The hull at the restart time through the restart chart -/

section Hull

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {T : Ω → ℝ≥0}

/-- **`ℍ ∖ K_{T+τ} = f_T⁻¹(ℍ ∖ K'_τ)`** on a path continuous before `ζ` with `W₀ = 0` and `T + τ < ζ`, with the chart
read from the recorded history and the restarted hull read from the stopped restarted history. -/
theorem compl_fwdHull_restart_eq_image {τ : Ω → WithTop ℝ≥0} {ω : Ω}
    (hWc : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
    (hτζ : (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < restartLife ζ T ω) :
    H \ fwdHull (fun s : ℝ => W s.toNNReal ω) ((T ω + (τ ω).untopD 0 : ℝ≥0) : ℝ) =
      (histChart (stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω)).2.1 ''
        (H \ tsHull (restartHist ζ W T τ ω)) := by
  have hlt : ((T ω + (τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω := (coe_lt_sub_iff _ _).1 hτζ
  have hTζ : (T ω : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast le_self_add) hlt
  rw [tsHull_restartHist hWc hτζ, ← restartChart_eq_histChart (VL := VL) (VR := VR) hWc hW0 hTζ]
  exact (restart_path (w := fun t => W t ω) hWc hW0 hlt 0 0).1.symm

end Hull

/-! ### One piece -/

section Piece

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {G : Set Ω} {T : Ω → ℝ≥0}
  {SL : Finset (Fin nL)} {SR : Finset (Fin nR)} {r : ℝ} {D : Set Ω}

omit [IsProbabilityMeasure P] in
open Classical in
/-- The restarted hull on a piece `E` (`∅` off `E`): measurable for `𝓓_σ` and relatively closed in `ℍ`. -/
theorem measurable_restartHull_piece (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (restartFiltration (drivingFiltration P hX) T hT) τ)
    (hτfin : ∀ ω, τ ω ≠ ⊤) {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime (drivingFiltration P hX) σ)
    {E : Set Ω} (hE : MeasurableSet[hσ.measurableSpace] E) (hEσ : ∀ ω ∈ E, σ ω = restartTime T τ ω) :
    Measurable[hσ.measurableSpace, hittingSigma]
      (E.piecewise (fun ω => tsHull (restartHist ζ W T τ ω)) fun _ => ∅) := by
  have hrc : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → ∀ t, MeasurableSet[drivingFiltration P hX t] s :=
    fun s hs h0 t => Ito.measurableSet_usualAugmentation_of_null hs h0 t
  have hτfin' : ∀ᵐ ω ∂P, τ ω ≠ ⊤ := ae_of_all _ hτfin
  have hσ' := isStoppingTime_restartTime hT hnull hτ hτfin'
  have hτσ' := measurableSpace_restartTime_eq hT hnull hτ hτfin'
  have hKhm : Measurable[hσ'.measurableSpace, hittingSigma] fun ω => tsHull (restartHist ζ W T τ ω) := by
    rw [← hτσ']
    exact measurable_tsHull_comp (measurable_restartHist hX hT hτ hτfin)
  exact @measurable_piecewise_stopping Ω mΩ _ _ _ hσ' hσ (Set ℂ) hittingSigma _ hKhm E hE
    (fun ω hω => (hEσ ω hω).symm.le) ∅

open Classical in
theorem relClosed_restartHull_piece (E : Set Ω) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    (E.piecewise (fun ω => tsHull (restartHist ζ W T τ ω)) fun _ => ∅) ω ⊆ H ∧
      IsOpen (H \ (E.piecewise (fun ω => tsHull (restartHist ζ W T τ ω)) fun _ => ∅) ω) := by
  by_cases hω : ω ∈ E
  · rw [Set.piecewise_eq_of_mem _ _ _ hω]
    exact tsHull_relClosed _
  · rw [Set.piecewise_eq_of_notMem _ _ _ hω, sdiff_empty]
    exact ⟨empty_subset _, QuantumZipper.isOpen_H⟩

open Classical in
/-- **Steps (1)–(2) on one piece**: under `P[· | E]` the restarted field, with the chart read from a `𝓓_σ`-measurable
version `Kp` of the history at the restart, is a part measurable for a σ-algebra `𝒢 ⊇ 𝓓_σ` and harmonic off the restarted
hull, plus a conditional zero-boundary GFF on the complement of the restarted hull given `𝒢`. -/
theorem exists_condDecomp_restart_piece (hκ : 0 < κ) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω)
    (hDp : IsRestartCell W VL VR ζ G T SL SR r D)
    {K : Ω → DrivingHist nL nR} (hKm : Measurable[hT.measurableSpace] K)
    (hK : ∀ ω, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (fun t => B t ω) (ζ ω) → (T ω : ℝ≥0∞) < ζ ω →
        K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω)
    {τ : Ω → WithTop ℝ≥0}
    (hτfin : ∀ ω, τ ω ≠ ⊤) (hτD : ∀ ω ∈ D, τ ω ≤ capStop r G (restartLife ζ T) (restartDrv W T) ω)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime (drivingFiltration P hX) σ) (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω)
    {E : Set Ω} (hE : MeasurableSet[hσ.measurableSpace] E) (hED : E ⊆ D)
    (hEσ : ∀ ω ∈ E, σ ω = restartTime T τ ω) (hPE : P E ≠ 0) :
    ∃ (Bv : Ω → Set ℂ) (Kp : Ω → DrivingHist nL nR) (M : Ω → DistOn upperHalfPlaneOpens),
      Measurable[mΩ, hittingSigma] Bv ∧ Measurable[hσ.measurableSpace] Kp ∧ (∀ ω ∈ E, Kp ω = K ω) ∧
      Measurable[germSigma Bv (centredField h (bheAt κ ρL ρR xL xR)) ⊔ hσ.measurableSpace] M ∧
      (∀ᵐ ω ∂(P[|E]), IsHarmonicDistOn (M ω)
        (H \ (E.piecewise (fun ω => tsHull (restartHist ζ W T τ ω)) fun _ => ∅) ω)) ∧
      @IsCondZeroBoundaryGFF Ω mΩ (P[|E]) (germSigma Bv (centredField h (bheAt κ ρL ρR xL xR)) ⊔ hσ.measurableSpace)
        (fun ω => H \ (E.piecewise (fun ω => tsHull (restartHist ζ W T τ ω)) fun _ => ∅) ω)
        (fun ω => restartField κ (h ω, Kp ω) - M ω) := by
  have hEm : MeasurableSet E := hσ.measurableSpace_le _ hE
  have : IsProbabilityMeasure (P[|E]) := cond_isProbabilityMeasure hPE
  have hEac : P[|E] ≪ P := cond_absolutelyContinuous
  have hEae : ∀ᵐ ω ∂(P[|E]), ω ∈ E := ae_cond_mem hEm
  have hpathP := hC.1.2.2.2.2
  have hTσ : ∀ ω ∈ E, ((T ω : ℝ≥0) : WithTop ℝ≥0) ≤ σ ω := fun ω hω => by
    rw [hEσ ω hω, restartTime]
    exact WithTop.coe_le_coe.2 le_self_add
  obtain ⟨ω₀, -⟩ := nonempty_of_measure_ne_zero hPE
  -- the chart read from the history, as a function measurable for `𝓓_σ`
  obtain ⟨Kp, hKpdef⟩ : ∃ Kp : Ω → DrivingHist nL nR, Kp = E.piecewise K fun _ => K ω₀ := ⟨_, rfl⟩
  have hKpm : Measurable[hσ.measurableSpace] Kp := by
    rw [hKpdef]; exact measurable_piecewise_stopping hT hσ hKm hE hTσ (K ω₀)
  have hKpE : ∀ ω ∈ E, Kp ω = K ω := fun ω hω => by rw [hKpdef]; exact Set.piecewise_eq_of_mem _ _ _ hω
  have hdom : ∀ z, MeasurableSet[hσ.measurableSpace] {ω | z ∈ (histChart (Kp ω)).dom} := fun z =>
    hKpm (measurableSet_mem_dom_histChart z)
  have hfwd : ∀ z, Measurable[hσ.measurableSpace]
      ({ω | z ∈ (histChart (Kp ω)).dom}.indicator fun ω => (histChart (Kp ω)).1 z) := fun z =>
    (measurable_indicator_fwd_histChart z).comp hKpm
  have hliftm : ∀ z, Measurable[hσ.measurableSpace]
      ({ω | z ∈ (histChart (Kp ω)).dom}.indicator fun ω => (histChart (Kp ω)).2.2 z) := fun z =>
    (measurable_indicator_lift_histChart z).comp hKpm
  -- the hull at `σ`
  have hpath : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 := by
    filter_upwards [hpathP] with ω hp using ⟨hp.2.2.2.1, hp.1⟩
  obtain ⟨A₀, hA₀m, hA₀K, -⟩ := Coupling.exists_hittingVersion_hull hX hpath hσ hσζ
  have hBm : Measurable[mΩ, hittingSigma] fun ω => relClosureH (A₀ ω) := measurable_relClosureH.comp hA₀m
  have hBc : ∀ ω, relClosureH (A₀ ω) ⊆ H ∧ IsOpen (H \ relClosureH (A₀ ω)) := fun ω =>
    ⟨relClosureH_subset _, isOpen_H_diff_relClosureH _⟩
  have hσζ' : ∀ᵐ ω ∂P, (((σ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω :=
    hσζ.mono fun ω h => Coupling.coe_untopD_lt_zeta h
  have hBK : ∀ᵐ ω ∂P, relClosureH (A₀ ω) = fwdHull (fun s : ℝ => W s.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) := by
    filter_upwards [hA₀K, Coupling.ae_hull_subset_isOpen (hpath.mono fun ω h => h.1) hσζ'] with ω h1 h2
    rw [h1]
    exact relClosureH_eq h2.1 h2.2
  have hu₀ := isBoundedHarmonicExtension_bheAt κ ρL ρR xL xR
  have hloc := isHistoryAvoidanceLocal_hull hC hκ hu₀ hX hσ hσζ hBm hBK
  have hh0 := isZeroBoundaryGFF_centredField hC hu₀
  have hh0m := measurable_centredField hC.2.1 (bheAt κ ρL ρR xL xR)
  -- the path facts on `E`
  have hτlt : ∀ ω ∈ E, (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < restartLife ζ T ω := fun ω hω => by
    obtain ⟨hωG, hTζ, -, -, hrad⟩ := hDp ω (hED hω)
    have h1 := capStop_restart_lt (hG ω hωG) hTζ hωG hrad
    have h2 := hτD ω (hED hω)
    obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.1 (hτfin ω)
    rw [← hv, WithTop.untopD_coe]
    rw [← hv] at h2
    exact lt_of_le_of_lt (by exact_mod_cast h2) h1
  have hBK' : ∀ᵐ ω ∂(P[|E]), H \ relClosureH (A₀ ω) = (histChart (Kp ω)).2.1 ''
      (H \ (E.piecewise (fun ω => tsHull (restartHist ζ W T τ ω)) fun _ => ∅) ω) := by
    filter_upwards [hEae, hEac.ae_le hpathP, hEac.ae_le hBK] with ω hωE hp hB
    obtain ⟨hωG, hTζ, -, -, -⟩ := hDp ω (hED hωE)
    have hσv : (σ ω).untopD 0 = T ω + (τ ω).untopD 0 := by rw [hEσ ω hωE, restartTime_untopD]
    rw [hB, hσv, hKpE ω hωE, hK ω hp hTζ, Set.piecewise_eq_of_mem _ _ _ hωE]
    exact compl_fwdHull_restart_eq_image hp.2.2.2.1 hp.1 (hτlt ω hωE)
  obtain ⟨M, hMm, hMharm, hMcond⟩ := exists_condDecomp_chart (P := P) hC.2.1 hu₀.1 hh0
    (fun ω => isConformal_histChart (Kp ω)) hdom hfwd hliftm
    (fun ω => continuousOn_lift_histChart (Kp ω)) (fun ω => harmonicOnNhd_lift_histChart (Kp ω))
    hσ.measurableSpace_le hBm hBc hloc (fun ω => relClosed_restartHull_piece E τ ω) hE hPE hBK' 0
    (QuantumZipper.chiC κ)
  exact ⟨_, Kp, M, hBm, hKpm, hKpE, hMm, hMharm, hMcond⟩

/-- **The conditioned restart measure as a tilt of `P[· | E]`**: on a piece `E ⊆ D`,
`Q[· | E] = e^{−Λ + b} · P[· | E]` with `Λ` the source pairing of the restart word and `b` its centre and norm and the
normalization `log(P[E | D] / Q(E))`, read through any version `Kp` of the history equal to `K` on `E`. -/
theorem restartQ_cond_eq {K Kp : Ω → DrivingHist nL nR} [IsFiniteMeasure (restartQ κ ρL ρR r P D K h)] (hhK : Measurable fun ω => restartField κ (h ω, K ω))
    (hcm : Measurable (restartWord r K)) {E : Set Ω} (hDm : MeasurableSet D) (hEm : MeasurableSet E)
    (hED : E ⊆ D) (hPDE : P[|D] E ≠ 0) (hQE : restartQ κ ρL ρR r P D K h E ≠ 0) (hKpE : ∀ ω ∈ E, Kp ω = K ω) :
    (restartQ κ ρL ρR r P D K h)[|E] = (P[|E]).withDensity fun ω => ENNReal.ofReal (Real.exp
      (-srcPairW κ ρL ρR r (restartWord r Kp ω) (restartField κ (h ω, Kp ω)) +
        (centreW κ ρL ρR r (restartWord r Kp ω) - normW κ ρL ρR r (restartWord r Kp ω) / 2 +
          Real.log (P[|D] E * (restartQ κ ρL ρR r P D K h E)⁻¹).toReal))) := by
  have hcst0 : P[|D] E * (restartQ κ ρL ρR r P D K h E)⁻¹ ≠ 0 :=
    mul_ne_zero hPDE (ENNReal.inv_ne_zero.2 (measure_ne_top _ _))
  have hcsttop : P[|D] E * (restartQ κ ρL ρR r P D K h E)⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (ENNReal.inv_ne_top.2 hQE)
  have hcstpos : 0 < (P[|D] E * (restartQ κ ρL ρR r P D K h E)⁻¹).toReal := ENNReal.toReal_pos hcst0 hcsttop
  have hf : Measurable fun ω => ENNReal.ofReal (densW κ ρL ρR r (restartWord r K ω) (restartField κ (h ω, K ω))) :=
    ENNReal.measurable_ofReal.comp (measurable_densW_word hhK hcm)
  have h1 := cond_withDensity_eq (μ := P[|D]) hf hEm hPDE (measure_ne_top _ _)
  have hPEeq : P[|E] = (P[|D])[|E] := by rw [cond_cond_eq_cond_inter hDm hEm, inter_eq_right.2 hED]
  change (wordMeasure κ ρL ρR r (P[|D]) (restartWord r K) fun ω => restartField κ (h ω, K ω))[|E] = _
  rw [wordMeasure, h1, ← hPEeq]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_cond_mem hEm] with ω hω
  have hw : restartWord r Kp ω = restartWord r K ω := by simp only [restartWord, hKpE ω hω]
  rw [hw, hKpE ω hω]
  have he : Real.exp (-srcPairW κ ρL ρR r (restartWord r K ω) (restartField κ (h ω, K ω)) +
      (centreW κ ρL ρR r (restartWord r K ω) - normW κ ρL ρR r (restartWord r K ω) / 2 +
        Real.log (P[|D] E * (restartQ κ ρL ρR r P D K h E)⁻¹).toReal)) =
      densW κ ρL ρR r (restartWord r K ω) (restartField κ (h ω, K ω)) *
        (P[|D] E * (restartQ κ ρL ρR r P D K h E)⁻¹).toReal := by
    rw [densW, ← Real.exp_log hcstpos, ← Real.exp_add, Real.exp_log hcstpos]
    congr 1
    ring
  rw [he, ENNReal.ofReal_mul (densW_pos κ ρL ρR r _ _).le, ENNReal.ofReal_toReal hcsttop, mul_comm]
  rfl

/-- **Locality of the restarted hull under `Q`, conditionally, on one piece.** For the data of `RestartLocalityInput`,
a restarted stop `τ` (finite everywhere, `τ ≤ S₀` on the cell `D`), a driving stop `σ < ζ` and an event `E ⊆ D` of
`𝓓_σ` on which `σ = T + τ` and the energy of the source of the restart word is at most `C`, with `Q(E) ≠ 0`: there are
a σ-algebra `𝒢 ∋ E` and a `𝒢`-measurable `h₁` with a `𝒢`-measurable version of the restarted hull on `E`, `h₁` harmonic
off the restarted hull and, under `Q[· | E]`, the recoded restarted field minus `h₁` conditionally a zero-boundary GFF
on its complement given `𝒢`. -/
theorem exists_condLocal_restart_piece (hκ : 0 < κ) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω)
    (hD : MeasurableSet[hT.measurableSpace] D) (hPD : P D ≠ 0) (hDp : IsRestartCell W VL VR ζ G T SL SR r D)
    {K : Ω → DrivingHist nL nR} (hKm : Measurable[hT.measurableSpace] K)
    (hK : ∀ ω, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (fun t => B t ω) (ζ ω) → (T ω : ℝ≥0∞) < ζ ω →
        K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (restartFiltration (drivingFiltration P hX) T hT) τ)
    (hτfin : ∀ ω, τ ω ≠ ⊤) (hτD : ∀ ω ∈ D, τ ω ≤ capStop r G (restartLife ζ T) (restartDrv W T) ω)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime (drivingFiltration P hX) σ) (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω)
    {E : Set Ω} (hE : MeasurableSet[hσ.measurableSpace] E) (hED : E ⊆ D)
    (hEσ : ∀ ω ∈ E, σ ω = restartTime T τ ω) {C : ℝ}
    (hEC : ∀ ω ∈ E, covBound (srcTestW κ ρL ρR r (restartWord r K ω)) ≤ C)
    (hQE : restartQ κ ρL ρR r P D K h E ≠ 0) :
    ∃ (𝒢 : MeasurableSpace Ω) (h₁ : Ω → DistOn upperHalfPlaneOpens), 𝒢 ≤ mΩ ∧ MeasurableSet[𝒢] E ∧
      (∃ A : Ω → Set ℂ, Measurable[𝒢, hittingSigma] A ∧ ∀ ω ∈ E, A ω = tsHull (restartHist ζ W T τ ω)) ∧
      Measurable[𝒢] h₁ ∧
      (∀ᵐ ω ∂((restartQ κ ρL ρR r P D K h)[|E]),
        IsHarmonicDistOn (h₁ ω) (H \ tsHull (restartHist ζ W T τ ω))) ∧
      @IsCondZeroBoundaryGFF Ω mΩ ((restartQ κ ρL ρR r P D K h)[|E]) 𝒢
        (fun ω => H \ tsHull (restartHist ζ W T τ ω)) (fun ω => restartRecode κ ρL ρR r (h ω, K ω) - h₁ ω) := by
  classical
  have hDm : MeasurableSet D := hT.measurableSpace_le _ hD
  have hr : 0 < r := pos_radius_of_isRestartCell hPD hDp
  have hEm : MeasurableSet E := hσ.measurableSpace_le _ hE
  have hcf := isCouplingCharFun_restartWord hC hκ hX hT hG hD hPD hDp hKm hK
  have hhK := measurable_restartField_word hC hX hT hKm
  have hcw0 := measurable_restartWord_zero (r := r) hX hT hKm
  have hadm : ∀ ω, IsAdmWord r (restartWord r K ω) := isAdmWord_restartWord hPD hDp
  have hgood := ae_isWordPath_restart hX hT hG hD hDp hK
  have : IsProbabilityMeasure (P[|D]) := cond_isProbabilityMeasure hPD
  have hQprob : IsProbabilityMeasure (restartQ κ ρL ρR r P D K h) :=
    isProbabilityMeasure_wordMeasure hcf hhK hcw0 hadm hgood
  have hQac : restartQ κ ρL ρR r P D K h ≪ P[|D] := withDensity_absolutelyContinuous _ _
  have hDac : P[|D] ≪ P := cond_absolutelyContinuous
  have hPDE : P[|D] E ≠ 0 := fun h0 => hQE (hQac h0)
  have hPE : P E ≠ 0 := fun h0 => hPDE (hDac h0)
  have : IsProbabilityMeasure (P[|E]) := cond_isProbabilityMeasure hPE
  have hPEeq : P[|E] = (P[|D])[|E] := by rw [cond_cond_eq_cond_inter hDm hEm, inter_eq_right.2 hED]
  have hEac : P[|E] ≪ P[|D] := by rw [hPEeq]; exact cond_absolutelyContinuous
  have hEae : ∀ᵐ ω ∂(P[|E]), ω ∈ E := ae_cond_mem hEm
  -- steps (1)–(2)
  obtain ⟨Bv, Kp, M, hBm, hKpm, hKpE, hMm, hMharm, hMcond⟩ :=
    exists_condDecomp_restart_piece hκ hC hX hT hG hDp hKm hK hτfin hτD hσ hσζ hE hED hEσ hPE
  have hh0m := measurable_centredField hC.2.1 (bheAt κ ρL ρR xL xR)
  have h𝒢 : germSigma Bv (centredField h (bheAt κ ρL ρR xL xR)) ⊔ hσ.measurableSpace ≤ mΩ :=
    sup_le (germSigma_le hBm hh0m) hσ.measurableSpace_le
  have hℋ𝒢 : hσ.measurableSpace ≤ germSigma Bv (centredField h (bheAt κ ρL ρR xL xR)) ⊔ hσ.measurableSpace :=
    le_sup_right
  have hK'm := measurable_restartHull_piece hX hT hτ hτfin hσ hE hEσ
  have hK'E : ∀ ω ∈ E, (E.piecewise (fun ω => tsHull (restartHist ζ W T τ ω)) fun _ => ∅) ω =
      tsHull (restartHist ζ W T τ ω) := fun ω hω => Set.piecewise_eq_of_mem _ _ _ hω
  -- step (3): the word, its source and its shift
  have hcwm : Measurable[hσ.measurableSpace] (restartWord r Kp) :=
    measurable_restartWord (m := hσ.measurableSpace) r hKpm
  have hcwadm : ∀ ω, IsAdmWord r (restartWord r Kp ω) := fun ω => isAdmWord_admWord hr _
  have hcwE : ∀ ω ∈ E, restartWord r Kp ω = restartWord r K ω := fun ω hω => by
    simp only [restartWord, hKpE ω hω]
  have hsm : ∀ k z, Measurable[germSigma Bv (centredField h (bheAt κ ρL ρR xL xR)) ⊔ hσ.measurableSpace]
      fun ω => srcTestW κ ρL ρR r (restartWord r Kp ω) k z := fun k z =>
    ((measurable_srcTestW_apply κ ρL ρR r k).comp
      (hcwm.prodMk (@measurable_const ℂ Ω _ hσ.measurableSpace z))).mono hℋ𝒢 le_rfl
  have hbd : ∀ᵐ ω ∂(P[|E]), covBound (srcTestW κ ρL ρR r (restartWord r Kp ω)) ≤ C := by
    filter_upwards [hEae] with ω hω
    rw [hcwE ω hω]
    exact hEC ω hω
  have hh'm : Measurable fun ω => restartField κ (h ω, Kp ω) :=
    (measurable_restartField κ).comp (hC.2.1.prodMk (hKpm.mono hσ.measurableSpace_le le_rfl))
  have hMm' : Measurable M := hMm.mono h𝒢 le_rfl
  have hYm : Measurable fun ω => restartField κ (h ω, Kp ω) - M ω := measurable_distOn_iff.2 fun φ =>
    ((measurable_distOn_apply φ).comp hh'm).sub ((measurable_distOn_apply φ).comp hMm')
  have hΛm : Measurable fun ω => srcPairW κ ρL ρR r (restartWord r Kp ω) (restartField κ (h ω, Kp ω)) := by
    have hp : Measurable fun ω => (restartWord r Kp ω, restartField κ (h ω, Kp ω)) :=
      (hcwm.mono hσ.measurableSpace_le le_rfl).prodMk hh'm
    have h1 := (measurable_srcPairW (nL := nL) (nR := nR) κ ρL ρR r).comp hp
    exact h1
  have hsrc := ae_tendsto_srcPairW_word (r := r) hcf hhK hcw0 hadm hgood
  have hconv : ∀ᵐ ω ∂(P[|E]), Tendsto (fun k => (M ω + (restartField κ (h ω, Kp ω) - M ω))
      (srcTestW κ ρL ρR r (restartWord r Kp ω) k)) atTop
      (𝓝 (srcPairW κ ρL ρR r (restartWord r Kp ω) (restartField κ (h ω, Kp ω)))) := by
    filter_upwards [hEac.ae_le hsrc, hEae] with ω h1 hω
    rw [add_sub_cancel, hcwE ω hω, hKpE ω hω]
    exact h1
  have hbm : Measurable[germSigma Bv (centredField h (bheAt κ ρL ρR xL xR)) ⊔ hσ.measurableSpace]
      fun ω => centreW κ ρL ρR r (restartWord r Kp ω) - normW κ ρL ρR r (restartWord r Kp ω) / 2 +
        Real.log (P[|D] E * (restartQ κ ρL ρR r P D K h E)⁻¹).toReal :=
    ((((measurable_centreW κ ρL ρR r).comp hcwm).sub (((measurable_normW κ ρL ρR r).comp hcwm).div_const 2)).add_const
      _).mono hℋ𝒢 le_rfl
  have hQEeq := restartQ_cond_eq hhK (hcw0.mono ((restartFiltration (drivingFiltration P hX) T hT).le 0) le_rfl)
    hDm hEm hED hPDE hQE hKpE
  have hZ : ∫⁻ ω, ENNReal.ofReal (Real.exp
      (-srcPairW κ ρL ρR r (restartWord r Kp ω) (restartField κ (h ω, Kp ω)) +
        (centreW κ ρL ρR r (restartWord r Kp ω) - normW κ ρL ρR r (restartWord r Kp ω) / 2 +
          Real.log (P[|D] E * (restartQ κ ρL ρR r P D K h E)⁻¹).toReal))) ∂(P[|E]) = 1 := by
    have : IsProbabilityMeasure ((restartQ κ ρL ρR r P D K h)[|E]) := cond_isProbabilityMeasure hQE
    have h1 := measure_univ (μ := (restartQ κ ρL ρR r P D K h)[|E])
    rw [hQEeq, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
    exact h1
  have hcsm : Measurable[germSigma Bv (centredField h (bheAt κ ρL ρR xL xR)) ⊔ hσ.measurableSpace]
      fun ω => recode κ (restartWord r Kp ω).1 (restartWord r Kp ω).2 ρL ρR r 0 :=
    ((measurable_recode_word κ ρL ρR r).comp
      (hcwm.prodMk (@measurable_const (DistOn upperHalfPlaneOpens) Ω _ hσ.measurableSpace 0))).mono hℋ𝒢 le_rfl
  have hcspair : ∀ ω (U : Opens ℂ) (_ : U ≤ upperHalfPlaneOpens) (g : MarkovZB.zsSub (U : Set ℂ)),
      Tendsto (fun k => ∫ z, srcTestW κ ρL ρR r (restartWord r Kp ω) k z * g.1 z) atTop
        (𝓝 (recode κ (restartWord r Kp ω).1 (restartWord r Kp ω).2 ρL ρR r 0 (lapTest U g))) := by
    intro ω U hU g
    rw [recode, zero_add]
    exact tendsto_integral_srcTestW_mul_eq_recode (hcwadm ω) U hU g
  -- the tilt
  obtain ⟨h₁', hh₁'m, hh₁'harm, hh₁'cond⟩ := exists_condLocal_withDensity_tilt_rand (P := P[|E]) h𝒢
    (hK'm.mono hℋ𝒢 le_rfl) (relClosed_restartHull_piece E τ) hMm hMharm hYm hMcond hsm
    (fun ω => isCovCauchy_srcTestW (hcwadm ω)) hbd hΛm hconv hbm hZ hcsm hcspair
  have hEaeQ : ∀ᵐ ω ∂((P[|E]).withDensity fun ω => ENNReal.ofReal (Real.exp
      (-srcPairW κ ρL ρR r (restartWord r Kp ω) (restartField κ (h ω, Kp ω)) +
        (centreW κ ρL ρR r (restartWord r Kp ω) - normW κ ρL ρR r (restartWord r Kp ω) / 2 +
          Real.log (P[|D] E * (restartQ κ ρL ρR r P D K h E)⁻¹).toReal)))), ω ∈ E :=
    (withDensity_absolutelyContinuous _ _).ae_le hEae
  have hpathQ : ∀ᵐ ω ∂((P[|E]).withDensity fun ω => ENNReal.ofReal (Real.exp
      (-srcPairW κ ρL ρR r (restartWord r Kp ω) (restartField κ (h ω, Kp ω)) +
        (centreW κ ρL ρR r (restartWord r Kp ω) - normW κ ρL ρR r (restartWord r Kp ω) / 2 +
          Real.log (P[|D] E * (restartQ κ ρL ρR r P D K h E)⁻¹).toReal)))),
      IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
        (fun t => B t ω) (ζ ω) :=
    (withDensity_absolutelyContinuous _ _).ae_le (hEac.ae_le (hDac.ae_le hC.1.2.2.2.2))
  refine ⟨_, h₁', h𝒢, hℋ𝒢 _ hE, ⟨_, hK'm.mono hℋ𝒢 le_rfl, hK'E⟩, hh₁'m, ?_, ?_⟩
  · rw [hQEeq]
    filter_upwards [hh₁'harm, hEaeQ] with ω h1 h2
    rwa [hK'E ω h2] at h1
  · rw [hQEeq]
    refine IsCondZeroBoundaryGFF.congr_ae hh₁'cond ?_ ?_
    · filter_upwards [hEaeQ] with ω hω
      rw [hK'E ω hω]
    · filter_upwards [hEaeQ, hpathQ] with ω hω hp
      obtain ⟨hωG, hTζ, -, -, hrad⟩ := hDp ω (hED hω)
      have hadmc : IsAdmWord r (curL VL W T ω, curR VR W T ω) :=
        ⟨isOrderedForceWord_cur (hG ω hωG) hTζ, hrad⟩
      have hKω := hK ω hp hTζ
      rw [restartRecode_eq_recode_restartWord hKω hKω hTζ hadmc, add_sub_cancel, hcwE ω hω, hKpE ω hω, recode,
        recode, zero_add]

end Piece

end LocalExt

end InteractingSLE
