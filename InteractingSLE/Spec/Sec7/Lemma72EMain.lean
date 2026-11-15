/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma72EKernel
import InteractingSLE.Spec.Sec7.Lemma72EDatum
import InteractingSLE.Spec.Sec7.Lemma72CMain
import InteractingSLE.Spec.Sec7.Lemma72CRecord
import InteractingSLE.Spec.Sec7.Lemma72DClause
import InteractingSLE.Spec.Sec7.Lemma71Joint
import InteractingSLE.Spec.Coupling.Assembly11BProvider

/-!
# Lemma 7.1's joint law, last steps, IV: the conditional pocket coupling and Lemma 7.1's joint law

Packet PROVE-LEMMA72E. Specification §7.1, proofs of Lemma 7.1 (`source/spec/p193-240.md` L576–L620, pp. 222–226)
and Lemma 7.2 (L622–L640, pp. 226–227: "The identical argument … conditionally on `A`").

On a three-curve space with a pocket construction `(C, c, γ')` (PROVE-LEMMA71K), a `σ(β, α)`-measurable branch `n` and
the fixed-time chart coupling clause for the prefix filtration `𝓐` of the mapped segment (PROVE-LEMMA71L's `hcf`), for
every event `G` of the exterior record `Q = ((β, α), h|_{ℍ ∖ C̄})` of positive probability
(`exists_cond_of_isPocketConstruction`):
* the filtration `𝓖_G = usualAugmentation (𝓐 ∨ σ(Q)) P[· | G]` is right-continuous, contains `𝓖 = usualAugmentation 𝓐 P`
  and the `P[· | G]`-null sets;
* the chart coupling clause holds under `P[· | G]` for `𝓖_G` (`Lemma72D.isChartCouplingCharFunConst_cond`: given
  `𝒢_t = germs(B_t) ∨ ℋ_t ⊇ 𝓐_t ∨ σ(Q)` the conditional characteristic function has the modulus of the clause, by the
  datum (R2′) `exists_marks_of_isPocketConstruction`; then all stopping times,
  `Lemma71D.isChartCouplingCharFun_usualAugmentation`);
* the mapped hulls `K_τ` are local sets of `h_ψ` under `P[· | G]` at every stopping time `τ < T` of `𝓖_G`
  (`Lemma72D.isLocalSet_hull_of_kernels` for `X = h_ψ − 𝔥₀`, with the Gaussian kernels of
  `exists_condExp_cexp_chartTransport_cond` given `𝒢_s` at rational times `s`, the zero-boundary GFF property of `X`
  under `P[· | G]` from the clause at time `0` (`Lemma71Joint.isZBGFFProcess_of_isCouplingCharFun`), then
  `IsLocalSet.add_dist`).

Hence `pocketCondStatement_of_clause : PocketClauseStatement → Lemma72C.PocketCondStatement`, and with
`Lemma72C.pocketJointStatement_of_cond` and `Lemma72B.lemma71JointStatement_of_pocketJoint`,
`Lemma72B.PocketJointStatement`
and `Lemma72.Lemma71JointStatement` from the fixed-time clause alone (`PocketClauseStatement`, the remaining work of
PROVE-LEMMA71L: the prime-end premise (P), B4 and the inherited branch (N)). Conditional helpers; they replace no source
theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Real

open QuantumZipper (H fwdHull zeroGFFTestCov chiC)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Sec7.Lemma72E

open LQGMetric Lemma71C Lemma71D Lemma71E Lemma71K Sec6 LocalSets WholeField MartChar

/-! ### The conditional pocket coupling on a given space -/

section Space

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ θ₁ θ₂ a b : ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {ζβ ζα ζγ : Ω → ℝ≥0∞}
  {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}

omit [IsProbabilityMeasure P] in
/-- The shifted lift of the pocket chart is harmonic on the chart domain (it is `Im L + 2πn` for a holomorphic
logarithm `L` of the derivative). -/
theorem harmonicOnNhd_shiftLift (hpc : IsPocketConstruction P β α γ C c γ') (n : Ω → ℤ) (ω : Ω) :
    InnerProductSpace.HarmonicOnNhd (shiftLift (c ω) (n ω)).2.2 (shiftLift (c ω) (n ω)).dom := by
  obtain ⟨hC, -, -, hdom, -, -, -, hL, -⟩ := hpc
  obtain ⟨L, hLd, hLe⟩ := hL ω
  intro z hz
  have hzC : z ∈ C ω := by
    have hz' : z ∈ ((c ω).dom : Set ℂ) := hz
    rwa [hdom ω] at hz'
  have han : AnalyticAt ℂ L z := hLd.1.analyticAt ((hC ω).1.mem_nhds hzC)
  have h2 : InnerProductSpace.HarmonicAt (c ω).2.2 z := by
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).2 han.harmonicAt_im
    filter_upwards [(hC ω).1.mem_nhds hzC] with w hw
    exact hLe w hw
  exact h2.add (InnerProductSpace.harmonicAt_const _)

/-- **The pocket coupling conditionally on the exterior record, on a given space** (see the module docstring). -/
theorem exists_cond_of_isPocketConstruction
    (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ) (hpc : IsPocketConstruction P β α γ C c γ')
    {n : Ω → ℤ} (hn : Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n) {a' k : ℝ}
    (hcf : IsChartCouplingCharFunConst κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁) P
      (prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ')
      (fun s ω => segDriver (γ' ω) s) (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL)
      (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR) (fun ω => capLife (γ' ω))
      (fun ω => shiftLift (c ω) (n ω)) a' k h)
    (G : Set Ω) (hG : MeasurableSet[MeasurableSpace.comap
      (Lemma72B.pocketRecord β α (fun ω => ((shiftLift (c ω) (n ω)).dom : Set ℂ)) h) inferInstance] G)
    (hPG : P G ≠ 0) :
    ∃ 𝓖G : Filtration ℝ≥0 mΩ, 𝓖G.IsRightContinuous ∧
      usualAugmentation (prefixFiltrationOf (mΩ := mΩ)
        (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ') P ≤ 𝓖G ∧
      (∀ s, MeasurableSet s → P[|G] s = 0 → MeasurableSet[𝓖G 0] s) ∧
      Coupling.MartMeans2.IsChartCouplingCharFun κ (fun _ : Fin 1 => cpf2RhoL κ θ₂)
        (fun _ : Fin 1 => cpf2RhoR κ θ₁) (P[|G]) 𝓖G (fun s ω => segDriver (γ' ω) s)
        (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL) (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR)
        (fun ω => capLife (γ' ω)) (fun ω => shiftLift (c ω) (n ω)) a' k h ∧
      ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖G τ → (∀ᵐ ω ∂(P[|G]), (τ ω : ℝ≥0∞) < capLife (γ' ω)) →
        IsLocalSet (fun ω => fwdHull (fun s : ℝ => segDriver (γ' ω) s.toNNReal) ((τ ω).untopD 0 : ℝ≥0))
          (fun ω => chartField (shiftLift (c ω) (n ω)) a' k (h ω)) (P[|G]) := by
  -- the objects
  have hh : Measurable h := hS.1.1
  have hu₀ := hS.2.1
  have hh0 := hS.2.2.1
  have hS' := hS
  obtain ⟨-, -, -, -, -, -, hβ62, hα62, -, -⟩ := hS'
  have hpc' := hpc
  obtain ⟨hC, hCm, hconf, hdom, hfm, hlm, hlc, -, -, -, hseg, -, -⟩ := hpc'
  set 𝓐 := prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ' with h𝓐def
  set W : ℝ≥0 → Ω → ℝ := fun s ω => segDriver (γ' ω) s with hWdef
  set T : Ω → ℝ≥0∞ := fun ω => capLife (γ' ω) with hTdef
  set c' : Ω → Chart := fun ω => shiftLift (c ω) (n ω) with hc'def
  have hcc' : ∀ ω, (c' ω).IsConformal := fun ω => isConformal_shiftLift (hconf ω) (n ω)
  have hlc' : ∀ ω, ContinuousOn (c' ω).2.2 (c' ω).dom := fun ω => continuousOn_shiftLift (hlc ω) (n ω)
  have hlift' : ∀ ω, InnerProductSpace.HarmonicOnNhd (c' ω).2.2 (c' ω).dom := harmonicOnNhd_shiftLift hpc n
  have hWc : ∀ ω, ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω} := fun ω =>
    (hseg ω).segDriver_spec.2.1
  have hW0 : ∀ ω, W 0 ω = 0 := fun ω => (hseg ω).segDriver_spec.1
  have hWa : AdaptedBefore 𝓐 T W := adaptedBefore_of_isPocketConstruction hS hpc
  have hTm : ∀ t : ℝ≥0, MeasurableSet[𝓐 t] {ω | (t : ℝ≥0∞) < T ω} :=
    measurableSet_lt_capLife_of_isPocketConstruction hS hpc
  have h₀ : ∀ t, MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ≤ 𝓐 t := fun t =>
    le_prefixFiltrationOf (comap_pair_le hS) γ' t
  -- the chart is a function of the outer curves
  have hdomm : ∀ z, MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      {ω | z ∈ (c' ω).dom} := fun z => by
    have e : {ω | z ∈ (c' ω).dom} = {ω | z ∈ C ω} := by
      ext ω
      show z ∈ ((c ω).dom : Set ℂ) ↔ z ∈ C ω
      rw [hdom ω]
    rw [e]
    exact @Lemma71E.measurableSet_mem_of_closedBall Ω
      (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) C (fun ω => (hC ω).1) hCm z
  have hfm' : ∀ z, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      ({ω | z ∈ (c' ω).dom}.indicator fun ω => (c' ω).1 z) := hfm
  have hlm' : ∀ z, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      ({ω | z ∈ (c' ω).dom}.indicator fun ω => (c' ω).2.2 z) := fun z =>
    @measurable_indicator_shiftLift Ω (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) c n hn z
      (hdomm z) (hlm z)
  have hCm' : ∀ (z : ℂ) (r : ℝ), MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      {ω | closedBall z r ⊆ ((c' ω).dom : Set ℂ)} := fun z r => by
    have := measurableSet_closedBall_dom hpc z r
    exact this
  have hclos : ∀ φ : TestOn upperHalfPlaneOpens, MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω))
      inferInstance] {ω | Disjoint (tsupport φ) (closure ((c' ω).dom : Set ℂ))} := fun φ =>
    @Lemma72B.measurableSet_disjoint_closure_of_mem Ω (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
      (fun ω => ((c' ω).dom : Set ℂ)) (fun ω => (c' ω).dom.isOpen) hdomm _ φ.hasCompactSupport
  -- the exterior record
  set Q := Lemma72B.pocketRecord β α (fun ω => ((c' ω).dom : Set ℂ)) h with hQdef
  have hβα : Measurable fun ω => (β ω, α ω) :=
    (measurable_pi_iff.2 hβ62.2.2.2.1).prodMk (measurable_pi_iff.2 hα62.2.2.2.1)
  have hQm : Measurable Q :=
    Lemma72B.measurable_pocketRecord hβ62.2.2.2.1 hα62.2.2.2.1 hh fun φ => hβα.comap_le _ (hclos φ)
  have h𝒬 : MeasurableSpace.comap Q inferInstance ≤ mΩ := hQm.comap_le
  -- the marks of (R2′)
  choose ℋ hℋle hℋloc hℋ𝓐 using fun t : ℝ≥0 =>
    exists_marks_of_isPocketConstruction (h := h) (u₀ := u₀) hS hpc t
  have hBm : ∀ t : ℝ≥0, Measurable[mΩ, hittingSigma] (markedSet W T c t) := fun t =>
    (measurable_markedSet_of_isPocketConstruction hS hpc t).mono (𝓐.le t) le_rfl
  have hσℋ : ∀ t, MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ≤ ℋ t := fun t =>
    (h₀ t).trans (hℋ𝓐 t)
  set 𝒢 : ℝ≥0 → MeasurableSpace Ω := fun t => germSigma (markedSet W T c t) (centredField h u₀) ⊔ ℋ t
    with h𝒢def
  have h𝒢le : ∀ t, 𝒢 t ≤ mΩ := fun t =>
    sup_le (germSigma_le (hBm t) (measurable_centredField hh u₀)) (hℋle t)
  have h𝓐𝒢 : ∀ t, 𝓐 t ≤ 𝒢 t := fun t => (hℋ𝓐 t).trans le_sup_right
  have h𝒬𝒢 : ∀ t, MeasurableSpace.comap Q inferInstance ≤ 𝒢 t := fun t => by
    have hβm : ∀ s, Measurable[ℋ t] fun ω => β ω s := fun s =>
      (((measurable_pi_apply s).comp measurable_fst).comp (comap_measurable _)).mono (hσℋ t) le_rfl
    have hαm : ∀ s, Measurable[ℋ t] fun ω => α ω s := fun s =>
      (((measurable_pi_apply s).comp measurable_snd).comp (comap_measurable _)).mono (hσℋ t) le_rfl
    exact Lemma72C.comap_pocketRecord_le (ℋ := ℋ t) (B := markedSet W T c t)
      (fun ω => H_diff_dom_subset_markedSet (hcc' ω)) hβm hαm (h := h) (smoothDist upperHalfPlaneOpens u₀)
      fun φ => hσℋ t _ (hclos φ)
  -- the clause under `P[· | G]`
  have hmod : ∀ t φ, ∀ᵐ ω ∂P, ω ∈ Lemma72D.clauseEvent W T c' t φ →
      ‖P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | 𝒢 t] ω‖ =
        Real.exp (-(1 / 2) * zeroGFFTestCov ((c' ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)))
          φ φ) := by
    intro t φ
    filter_upwards [Lemma72D.norm_condExp_cexp_of_isHistoryAvoidanceLocal hh hh0 (hBm t) (hℋle t) (hℋloc t)
      (ae_of_all _ fun ω => ⟨markedSet_subset, isOpen_H_diff_markedSet (hconf ω) (hWc ω)⟩) φ] with ω hω hE
    rw [hω, H_diff_markedSet_of_lt (hconf ω) hE.1]
    rfl
  have hcov : ∀ t φ, ∃ E : ℕ → Set Ω, (∀ j, MeasurableSet[𝓐 t] (E j)) ∧
      (∀ j, E j ⊆ Lemma72D.clauseEvent W T c' t φ) ∧ Lemma72D.clauseEvent W T c' t φ ⊆ ⋃ j, E j := fun t φ =>
    Lemma72D.exists_cover_clauseEvent hcc' hCm' hfm' hWa hWc t (h₀ t) (hTm t) φ
  have hcfG := Lemma72D.isChartCouplingCharFunConst_cond hh h𝒬 𝒢 h𝒢le h𝓐𝒢 h𝒬𝒢 hmod hcov hcf hG hPG
  have hμ : IsProbabilityMeasure (P[|G]) := cond_isProbabilityMeasure hPG
  have hac : P[|G] ≪ P := cond_absolutelyContinuous
  set 𝓗 := Lemma72D.supConst 𝓐 (MeasurableSpace.comap Q inferInstance) h𝒬 with h𝓗def
  have hcfμ : Coupling.MartMeans2.IsChartCouplingCharFun κ (fun _ : Fin 1 => cpf2RhoL κ θ₂)
      (fun _ : Fin 1 => cpf2RhoR κ θ₁) (P[|G]) (usualAugmentation 𝓗 (P[|G])) W (geomL W LP.twoSeedXL)
      (geomR W LP.twoSeedXR) T c' a' k h :=
    isChartCouplingCharFun_usualAugmentation hh hcc' hlc' hWc (fun i ω => continuousOn_geomL hWc LP.twoSeedXL i ω)
      (fun i ω => continuousOn_geomR hWc LP.twoSeedXR i ω)
      (fun ω t ht => geomL_le_le_geomR hWc LP.twoSeedXL LP.twoSeedXR ht) hcfG
  refine ⟨usualAugmentation 𝓗 (P[|G]), Ito.isRightContinuous_usualAugmentation 𝓗 (P[|G]),
    Lemma72D.usualAugmentation_le_cond _ 𝓐 h𝒬 G, fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0,
    hcfμ, ?_⟩
  -- locality under `P[· | G]`
  intro τ hτ hτT
  have hψω : ∀ ω, chartField (c' ω) a' k (h ω) = Chart.chartTransport (hcc' ω) 1 a' k (h ω) := fun ω =>
    dite_eq_left (hcc' ω)
  have hψe : (fun ω => chartField (shiftLift (c ω) (n ω)) a' k (h ω)) =
      fun ω => Chart.chartTransport (hcc' ω) 1 a' k (h ω) := funext hψω
  have ht : ∀ ω, IsChartTransport (c' ω) 1 a' k (h ω) (Chart.chartTransport (hcc' ω) 1 a' k (h ω)) := fun ω => by
    have := isChartTransport_chartField (hcc' ω) (hlc' ω) a' k (h ω)
    rwa [hψω ω] at this
  rw [hψe]
  -- the σ-algebras at time `0` of `𝓖_G`
  have h0G : MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ≤ usualAugmentation 𝓗 (P[|G]) 0 :=
    (h₀ 0).trans ((Lemma72D.le_supConst 𝓐 _ h𝒬 0).trans (Ito.le_usualAugmentation 𝓗 (P[|G]) 0))
  have hψm : Measurable fun ω => Chart.chartTransport (hcc' ω) 1 a' k (h ω) :=
    Chart.measurable_chartTransport_random' hcc' (fun z => (comap_pair_le hS) _ (hdomm z))
      (fun z => (hfm' z).mono (comap_pair_le hS) le_rfl) (fun z => (hlm' z).mono (comap_pair_le hS) le_rfl)
      hlc' hh 1 a' k
  -- the centred field is a zero-boundary GFF under `P[· | G]`
  obtain ⟨u₀', hu₀'⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ
    (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁) (fun _ : Fin 1 => (0 : ℝ))
    (fun _ : Fin 1 => (0 : ℝ))
  have hu₀'c : ContinuousOn u₀' H := fun z hz => ((hu₀'.1 z hz).1.continuousAt).continuousWithinAt
  have hcpl := Coupling.MartMeans2.isCouplingCharFun_of_isChartTransport hcc' (fun z => h0G _ (hdomm z))
    (fun z => (hfm' z).mono h0G le_rfl) (fun z => (hlm' z).mono h0G le_rfl) hlc' hh
    (Eventually.of_forall fun ω => ⟨hW0 ω, hWc ω⟩) hcfμ ht
  have hzb := Lemma71J.isZBGFFProcess_of_isCouplingCharFun hcpl hψm
    (Eventually.of_forall fun ω => ⟨bot_le.trans_lt ((hseg ω).ofReal_capClock_lt zero_le_one), hWc ω, hW0 ω,
      fun i => geomL_twoSeed_zero_of (hW0 ω) i, fun i => geomR_twoSeed_zero_of (hW0 ω) i⟩) hu₀'
  have hX := Coupling.isZeroBoundaryGFF_sub_smoothDist hψm hu₀'c hzb
  -- the kernels at rational times
  have hu₀'h := Coupling.isHarmonicDistOn_smoothDist_of hu₀'
  have hker0 : ∀ s : ℚ≥0, ∃ Ms : Ω → DistOn upperHalfPlaneOpens,
      (∀ᵐ ω ∂P, IsHarmonicDistOn (Ms ω) (openPart W T (s : ℝ≥0) ω)) ∧
      ∀ χ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂(P[|G]),
        (P[|G])[fun ω' => Complex.exp (Complex.I *
          ((Chart.chartTransport (hcc' ω') 1 a' k (h ω') - smoothDist upperHalfPlaneOpens u₀') χ : ℂ)) |
            𝒢 (s : ℝ≥0)] ω = rangeKerCF (Ms ω) (openPart W T (s : ℝ≥0) ω) χ := by
    intro s
    obtain ⟨Ms, hMh, hMk⟩ := exists_condExp_cexp_chartTransport_cond (ℋ := ℋ (s : ℝ≥0)) hh hu₀.1 hh0 hcc'
      (fun z => hσℋ _ _ (hdomm z)) (fun z => (hfm' z).mono (hσℋ _) le_rfl)
      (fun z => (hlm' z).mono (hσℋ _) le_rfl) hlc' hlift' (O := openPart W T (s : ℝ≥0))
      (fun ω => isOpen_openPart (hWc ω)) (fun ω => openPart_subset) (hℋle _) (hBm _) (hℋloc _) a' k hu₀'h
    exact ⟨Ms, hMh, fun χ => hMk G (h𝒬𝒢 _ G hG) hPG χ⟩
  choose Mk hMkh hMkk using hker0
  have hloc := Lemma72D.isLocalSet_hull_of_kernels (P := P[|G]) (𝓗 := 𝓗) (W := W) (ζ := T)
    (𝒦 := fun s : ℚ≥0 => 𝒢 (s : ℝ≥0)) (M := Mk) (V := fun s : ℚ≥0 => openPart W T (s : ℝ≥0)) hX
    (Ito.adaptedBefore_mono (Lemma72D.le_supConst 𝓐 _ h𝒬) hWa) (Eventually.of_forall fun ω => ⟨hWc ω, hW0 ω⟩)
    (fun s => h𝒢le _) hMkk ?_ ?_ ?_ hτ hτT
  · have := Coupling.IsLocalSet.add_dist hloc hu₀'h
    simpa only [sub_add_cancel] using this
  · -- the kernel domains
    intro s
    filter_upwards [hac.ae_le (hMkh s)] with ω hω hlt
    rw [openPart_of_lt (ζ := T) (ω := ω) hlt] at hω ⊢
    exact ⟨Coupling.MartMeans2.isOpen_H_diff_fwdHull_rpath (hWc ω) hlt, sdiff_subset, subset_rfl, hω⟩
  · -- the events of `𝓖_G` before `s`
    intro r s hrs D hD
    obtain ⟨D', hD', hDD'⟩ := Ito.exists_ae_eq_of_measurableSet_usualAugmentation
      (show (r : ℝ≥0) < (s : ℝ≥0) by exact_mod_cast hrs) hD
    exact ⟨D', (sup_le (h𝓐𝒢 _) (h𝒬𝒢 _) : 𝓗 (s : ℝ≥0) ≤ 𝒢 (s : ℝ≥0)) D' hD', hDD'⟩
  · -- the safety events
    intro s F hFH
    exact ⟨_, h𝓐𝒢 _ _ (Lemma72D.measurableSet_lt_disjoint_ballsK hWa hWc (s : ℝ≥0) (hTm _) hFH),
      EventuallyEq.rfl⟩

end Space

/-! ### The named input and the statements -/

/-- **Named input: Lemma 7.1's fixed-time chart coupling clause on the pocket construction** (specification §7.1,
pp. 222–225; PROVE-LEMMA71L's `hcf`, in flight: `Lemma71L.isChartCouplingCharFunConst_of_primeEnd` from the prime-end
premise (P), the measurability B4 and the inherited branch (N)). For `0 < κ < 4`, `θ₁ < 0 < θ₂` and boundary values
`a, b` large enough for Proposition 5.5, on every three-curve space there are a pocket construction `(C, c, γ')`
(`Lemma71K.IsPocketConstruction`, e.g. `Lemma71K.exists_isPocketConstruction`), a `σ(β, α)`-measurable branch shift `n`
and constants `a', k` for which the chart coupling clause of the two-seed word with the (CPF2) weights holds at fixed
times for the prefix filtration of `σ(β, α)` and `γ'`, with the chart `shiftLift c n`
(`Lemma71D.IsChartCouplingCharFunConst`,
the hypothesis `hcf` of `Lemma71K.isPocketChartData_of_isPocketConstruction`). -/
def PocketClauseStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ a b : ℝ, θ₁ < 0 → 0 < θ₂ →
    sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a → sleLambda κ - θ₁ * chiC κ ≤ b →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) (β α γ : Ω → ℝ≥0 → ℂ) (ζβ ζα ζγ : Ω → ℝ≥0∞),
      Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ →
    ∃ (C : Ω → Set ℂ) (c : Ω → Chart) (γ' : Ω → ℝ → ℂ) (n : Ω → ℤ) (a' k : ℝ),
      IsPocketConstruction P β α γ C c γ' ∧
      Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n ∧
      IsChartCouplingCharFunConst κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁) P
        (prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ')
        (fun s ω => segDriver (γ' ω) s) (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL)
        (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR) (fun ω => capLife (γ' ω))
        (fun ω => shiftLift (c ω) (n ω)) a' k h

/-- **`Lemma72C.PocketCondStatement` from the fixed-time clause.** The pocket data are
`Lemma71K.isPocketChartData_of_isPocketConstruction` (filtration `usualAugmentation 𝓐 P`), `h_ψ = chartField`
(`Lemma71K.isChartTransport_chartField`), and the conditional coupling is `exists_cond_of_isPocketConstruction`.
Conditional helper. -/
theorem pocketCondStatement_of_clause (hcl : PocketClauseStatement.{u}) : Lemma72C.PocketCondStatement.{u} := by
  intro κ hκ hκ4 θ₁ θ₂ a b hθ₁ hθ₂ ha hb Ω mΩ P hP h u₀ β α γ ζβ ζα ζγ hS
  obtain ⟨C, c, γ', n, a', k, hpc, hn, hcf⟩ := hcl κ hκ hκ4 θ₁ θ₂ a b hθ₁ hθ₂ ha hb P h u₀ β α γ ζβ ζα ζγ hS
  have hpc' := hpc
  obtain ⟨-, -, hconf, -, -, -, hlc, -⟩ := hpc'
  refine ⟨_, γ', fun s ω => segDriver (γ' ω) s, fun ω => capLife (γ' ω), fun ω => shiftLift (c ω) (n ω), a', k,
    fun ω => chartField (shiftLift (c ω) (n ω)) a' k (h ω), isPocketChartData_of_isPocketConstruction hS hpc hn hcf,
    fun ω => isChartTransport_chartField (isConformal_shiftLift (hconf ω) (n ω))
      (continuousOn_shiftLift (hlc ω) (n ω)) a' k (h ω), fun G hG hPG => ?_⟩
  exact exists_cond_of_isPocketConstruction hS hpc hn hcf G hG hPG

/-- **`Lemma72B.PocketJointStatement` from the fixed-time clause** (`Lemma72C.pocketJointStatement_of_cond`).
Conditional helper. -/
theorem pocketJointStatement_of_clause (hcl : PocketClauseStatement.{u}) : Lemma72B.PocketJointStatement.{u} :=
  Lemma72C.pocketJointStatement_of_cond (pocketCondStatement_of_clause hcl)

/-- **Lemma 7.1's joint law (`Lemma72.Lemma71JointStatement`) from the fixed-time clause**, with the named inputs of
the three-curve space (`Lemma72B.lemma71JointStatement_of_pocketJoint`). Conditional helper. -/
theorem lemma71JointStatement_of_clause (href : Lemma71H.Cond44ReferenceStatement.{u})
    (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) (hMD : Lemma71I.Lemma613ContactStatement.{u})
    (hcl : PocketClauseStatement.{u}) : Lemma72.Lemma71JointStatement.{u} :=
  Lemma72B.lemma71JointStatement_of_pocketJoint href h55 hMD (pocketJointStatement_of_clause hcl)

end InteractingSLE.Sec7.Lemma72E
