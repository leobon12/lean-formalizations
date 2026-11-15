/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseClauseLaw
import InteractingSLE.Spec.Sec7.PocketStopSideLimPhase
import InteractingSLE.Spec.Sec7.Lemma725RefChartGen

/-!
# The pocket mean identification for the phase word, from R.5 up to phase

Packet PROVE-PHASECLAUSE. Specification Aux. lemma 36 (`source/spec/p193-240.md` L60–L78: the boundary germs flattened
in a uniformizing coordinate, the bounded Poisson extension, "The cited uniqueness lemma makes the difference zero"),
Aux. lemmas 120 and 122 (`source/spec/p385-432.md` L104–L131: the word heights at the relative time and the common
lattice phase `d` of the exposed interval) and Astra's follow-up 5 (3.1) (R73: R.5 gives the current finite word with
the exposed heights `−Λ + δ_t`, `+Λ + δ_t`).

PROVE-STRIPSYS33's `PocketStop.pocketStopMeanAt_of_sideLimit` identifies the central pocket mean from the zero-phase
side limits (`PocketStopSideLimit`); PROVE-LEMMA725REF4's `Lemma725RefChart.pocketChartData_of_stop` assembles it with
the marked union law into the physical kernel and the mean identification. This file does the same for R.5 **up to
phase** (`PocketStopSide.PocketStopPhaseSideLimit`, PROVE-STRIPSYS38): the boundary data are the phase word
`phaseData` of the common lattice phase `δ_q`, whose bounded harmonic extension is `PhaseClause.phaseProc (δ q)`, and
the uniqueness step (Aux. lemmas 27–28, `Aux2728Pocket.ae_eqOn_of_sideLimit`) is data-generic.

* **`phaseMeanAt_of_phaseSideLimit`**: the central pocket mean at `T(q)` is the coupling mean of `phaseProc (δ q)`;
* **`pocketChartPhaseData_of_stop`**: the explicit shifted canonical pocket chart is regular, the canonical sets
  `ℍ ∖ activeDom` are hitting-measurable and history-local, and there are σ-algebras `𝓜_q` and means `M_q` with the
  physical kernel (`PocketCoupling.PocketKernel`) and the phase mean identification.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd chiC zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.PhaseClause

open PocketStop PocketTraversal PocketAdapt Lemma71C LocalSets WholeField PocketCoupling PocketUnionPt PhaseSel
  Lemma725RefChart PocketStopField Lemma725RefSafe

universe u

section Mean

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The central pocket mean at `T(q)` from R.5 up to phase** (`PocketStop.pocketStopMeanAt_of_sideLimit` for the
phase word): the side limits of the phase word with the phase `d` give, for every version `g` of the local-set mean,
a continuous representative `v` of `g + 𝔥` on `S` with `v + a + χ ℓ_c` the coupling mean at `q` of the explicit
extension `phaseProc d` of the phase word, read through the pocket chart. -/
theorem phaseMeanAt_of_phaseSideLimit [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart} {q : ℝ≥0} {K : Ω → Set ℂ}
    (hKm : Measurable[mΩ, hittingSigma] K) (hloc : IsLocalSet K h₀ P)
    (hK : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → H \ K ω = activeDom A γ c q ω)
    {S : Ω → Set ℂ} (hS : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → S ω = activeDom A γ c q ω)
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) {ℓ : Ω → ℂ → ℂ}
    (hc : ∀ ω ∈ A, (c ω).IsConformal ∧ IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧
      ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im)
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    {𝔥 : DistOn upperHalfPlaneOpens} (h𝔥 : ∀ φ : TestOn upperHalfPlaneOpens, 𝔥 φ = ∫ z, u z * φ z)
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {a : ℝ} {d : Ω → ℝ}
    (hside : PocketStopSide.PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR c a h₀ u K d q) :
    ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean K h₀ P g →
      ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∃ v : ℂ → ℝ, ContinuousOn v (S ω) ∧
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ S ω → (g ω + 𝔥) φ = ∫ z, v z * φ z) ∧
        ∀ z ∈ S ω, v z + a + chiC κ * (c ω).2.2 z =
          couplingMean κ (fun s : ℝ => segDriver (γ ω) s.toNNReal) q
            (phaseProc κ ρL ρR (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
              (geomRW (fun t ω => segDriver (γ ω) t) xR) d ω q) ((c ω).1 z) := by
  intro g hg
  filter_upwards [Aux2728Pocket.ae_eqOn_of_sideLimit hh₀ hKm hloc hg hu hub (chiC κ), hside.2 g hg, hg.2.1]
    with ω hω hsω hharm hωA hq
  obtain ⟨v, hvh, hvrep⟩ := hharm
  obtain ⟨hcc, hℓ, hlift⟩ := hc ω hωA
  obtain ⟨W, hW, hW0, q', hqq', hWeq, hrel⟩ := exists_relChart_eq_loewner (c := c) (hγ ω hωA) hq
  set w : ℝ → ℝ := fun s => segDriver (γ ω) s.toNNReal with hw
  set c' : Chart := (c ω).loewner W q with hc'
  have hq0 : (0 : ℝ) ≤ q := q.coe_nonneg
  have hc'conf : c'.IsConformal := hcc.loewner hW hW0 hq0
  have hhull : fwdHull w q = fwdHull W q := fwdHull_eq_of_eqOn hq0 hqq' hWeq
  -- the active domain is the domain of the relative chart
  have himg : c'.2.1 '' H = (c ω).2.1 '' (H \ fwdHull W q) := by
    rw [show c'.2.1 = (c ω).2.1 ∘ fwdMapInv W q from rfl, image_comp,
      QuantumZipper.RS.image_fwdMapInv_H hW hW0 hq0]
  have hdomK : H \ K ω = (c'.dom : Set ℂ) := by
    rw [hK ω hωA hq, activeDom_eq hωA hq, hc'conf.coe_dom, himg, ← hhull]
  have hdomS : S ω = (c'.dom : Set ℂ) := by
    rw [hS ω hωA hq, ← hdomK, hK ω hωA hq]
  have hsub : (c'.dom : Set ℂ) ⊆ (c ω).dom := by
    rw [hc'conf.coe_dom, himg, hcc.coe_dom]
    exact image_mono sdiff_subset
  -- the chart data of Aux. lemmas 27–28
  have hpre : IsPreconnected (c'.dom : Set ℂ) := by
    rw [hc'conf.coe_dom]
    exact (convex_halfSpace_gt Complex.imLm.isLinear 0).isPreconnected.image _ hc'conf.1.continuousOn
  have hI : c'.2.1 Complex.I ∈ (c'.dom : Set ℂ) := by
    rw [hc'conf.coe_dom]
    exact mem_image_of_mem _ (show (0 : ℝ) < Complex.I.im by simp)
  have hcomp : ∃ z₀ ∈ H \ K ω, (c'.dom : Set ℂ) = connectedComponentIn (H \ K ω) z₀ :=
    ⟨c'.2.1 Complex.I, hdomK ▸ hI, by rw [hdomK, hpre.connectedComponentIn hI]⟩
  have hmaps : MapsTo (c ω).1 c'.dom (H \ fwdHull W q) := by
    intro z hz
    rw [hc'conf.coe_dom, himg] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [hcc.2.2 y hy.1]
    exact hy
  have hψd : DifferentiableOn ℂ (fwdMap W q) (H \ fwdHull W q) := fun z hz =>
    (QuantumZipper.FwdHolo.hasDerivAt_fwdMap hW hq0 hz).differentiableAt.differentiableWithinAt
  have hℓ'0 := IsDerivLog.comp (ψ := fwdMap W q) (φ := (c ω).1) (Lψ := logDerivFwd W q) (Lφ := ℓ ω)
    (D := (c'.dom : Set ℂ)) (E := H \ fwdHull W q) c'.dom.isOpen
    (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hq0) hψd (hcc.differentiableOn_fwd.mono hsub) hmaps
    (isDerivLog_fwdMap hW hq0) (hℓ.mono hsub)
  have hℓ' : IsDerivLog c'.1 (fun z => logDerivFwd W q ((c ω).1 z) + ℓ ω z) c'.dom := hℓ'0
  have hlift' : ∀ z ∈ (c'.dom : Set ℂ), c'.2.2 z = ((fun z => logDerivFwd W q ((c ω).1 z) + ℓ ω z) z).im :=
    fun z hz => by
      show (logDerivFwd W q ((c ω).1 z)).im + (c ω).2.2 z = _
      rw [Complex.add_im, hlift z (hsub hz)]
  -- the word's boundary data at `q` and its bounded harmonic extension, shifted by `a`
  set vL : Fin (nL + 1) → ℝ := fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q
  set vR : Fin (nR + 1) → ℝ := fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q
  obtain ⟨G₀, hG₀eq⟩ : ∃ G : ℂ → ℝ, G = phaseProc κ ρL ρR (fun t ω => segDriver (γ ω) t)
      (geomLW (fun t ω => segDriver (γ ω) t) xL) (geomRW (fun t ω => segDriver (γ ω) t) xR) d ω q := ⟨_, rfl⟩
  have hG₀ : IsBoundedHarmonicExtension (phaseData κ ρL ρR vL vR (d ω)) (forceJumpSet vL vR) G₀ :=
    hG₀eq ▸ isBoundedHarmonicExtension_phaseProc (W := fun t ω => segDriver (γ ω) t)
      (VL := geomLW (fun t ω => segDriver (γ ω) t) xL) (VR := geomRW (fun t ω => segDriver (γ ω) t) xR)
      (ω := ω) (s := q) hκ d
      (PocketMartLife.geomLW_le_of_lt (W := fun t ω => segDriver (γ ω) t) (ω := ω)
        (hγ ω hωA).segDriver_spec.2.1 hq xL 0)
      (PocketMartLife.le_geomRW_of_lt (W := fun t ω => segDriver (γ ω) t) (ω := ω)
        (hγ ω hωA).segDriver_spec.2.1 hq xR 0)
  have hG : IsBoundedHarmonicExtension (fun ξ => phaseData κ ρL ρR vL vR (d ω) ξ - a) (forceJumpSet vL vR)
      fun z => G₀ z - a := by
    obtain ⟨hGh, ⟨M, hM⟩, hGt⟩ := hG₀
    refine ⟨fun z hz => ?_, ⟨M + |a|, fun z hz => ?_⟩, fun ξ hξ => (hGt ξ hξ).sub_const a⟩
    · exact (hGh z hz).sub (InnerProductSpace.harmonicAt_const a)
    · calc |G₀ z - a| ≤ |G₀ z| + |a| := abs_sub _ _
        _ ≤ M + |a| := by linarith [hM z hz]
  have hJ : (forceJumpSet vL vR).Finite := ((finite_range vL).union (finite_range vR)).insert 0
  have hsideω : ∀ ξ : ℝ, ξ ∉ forceJumpSet vL vR →
      Tendsto (fun y => v (c'.2.1 y) + u (c'.2.1 y) + chiC κ * (c'.2.2 (c'.2.1 y) + 2 * π * ((0 : ℤ) : ℝ)))
        (𝓝[H] (ξ : ℂ)) (𝓝 (phaseData κ ρL ρR vL vR (d ω) ξ - a)) := by
    intro ξ hξ
    have h1 := hsω hωA hq v hvh hvrep ξ hξ
    rw [hrel] at h1
    simpa only [Int.cast_zero, mul_zero, add_zero] using h1
  have key := hω v hvh hvrep c' (fun z => logDerivFwd W q ((c ω).1 z) + ℓ ω z) 0 _ _ _ hc'conf hcomp hℓ'
    hlift' hJ hG hsideω
  -- the conclusion
  have hvc : ContinuousOn v (H \ K ω) := fun z hz => (hvh z hz).1.continuousAt.continuousWithinAt
  have huc : ContinuousOn u H := fun z hz => (hu z hz).1.continuousAt.continuousWithinAt
  have hSK : S ω = H \ K ω := by rw [hdomS, hdomK]
  refine ⟨fun z => v z + u z, ?_, fun φ hφ => ?_, fun z hz => ?_⟩
  · rw [hSK]
    exact hvc.add (huc.mono sdiff_subset)
  · have hφK : tsupport φ ⊆ H \ K ω := hSK ▸ hφ
    have hi₁ : Integrable fun z => v z * φ z := integrable_mul_testOn hvc φ hφK
    have hi₂ : Integrable fun z => u z * φ z := integrable_mul_testOn huc φ (hφK.trans sdiff_subset)
    rw [add_apply, hvrep φ hφK, h𝔥 φ, ← integral_add hi₁ hi₂]
    exact integral_congr_ae (Eventually.of_forall fun z => by simp only [add_mul])
  · have hz' : z ∈ (c'.dom : Set ℂ) := hdomS ▸ hz
    have hk := key z hz'
    have e1 : fwdMap w q ((c ω).1 z) = fwdMap W q ((c ω).1 z) :=
      fwdMap_eq_of_eqOn hq0 fun r hr => hWeq r ⟨hr.1, hr.2.trans hqq'.le⟩
    have e2 : logDerivFwd w q ((c ω).1 z) = logDerivFwd W q ((c ω).1 z) :=
      Ito.logDerivFwd_congr_of_eqOn (T := q) (fun r hr => hWeq r ⟨hr.1, hr.2.trans hqq'.le⟩) hq0 le_rfl
    rw [← hG₀eq]
    show v z + u z + a + chiC κ * (c ω).2.2 z = couplingMean κ w q G₀ ((c ω).1 z)
    rw [couplingMean, e1, e2]
    have hc'1 : c'.1 z = fwdMap W q ((c ω).1 z) := rfl
    have hc'2 : c'.2.2 z = (logDerivFwd W q ((c ω).1 z)).im + (c ω).2.2 z := rfl
    rw [hc'1, hc'2] at hk
    simp only [Int.cast_zero, mul_zero, add_zero] at hk
    linarith

end Mean

section Gen

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The field-level pocket data for the explicit shifted canonical pocket chart, with the phase word**
(`Lemma725RefChart.pocketChartData_of_stop` with `PocketStopPhaseSideLimit` and the phase mean identification): the
chart is regular on all of `Ω`, the canonical sets `ℍ ∖ activeDom` are hitting-measurable and history-local for the
centred field, and there are σ-algebras `𝓜_q` and means `M_q` with the physical kernel and, at every relative time `q`,
the chart transport of `M_q` equal to the coupling mean of `phaseProc (δ q)` against every test function off the hull.
-/
theorem pocketChartPhaseData_of_stop [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A) {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {C : Ω → Set ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hCH : ∀ ω ∈ A, C ω ⊆ H) {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H)
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z)) {F : ℝ≥0 → Ω → Set ℂ}
    (hFo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ F q ω))
    (hgeo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      ψ ω '' (C ω ∩ (H \ F q ω)) = H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M) {n : Ω → ℤ}
    (hn : Measurable[𝓦] n) {a : ℝ} (hU : ∀ q : ℝ≥0, PocketStopUnionLaw 𝓦 P A γ C (F q) h₀ q)
    {δ : ℝ≥0 → Ω → ℝ}
    (hside : ∀ q : ℝ≥0, PocketStopSide.PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR
      (fun ω => shiftChart (pChart A C ψ ω) (n ω)) a h₀ u
      (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q) (δ q) q) :
    (∀ ω, (shiftChart (pChart A C ψ ω) (n ω)).IsConformal) ∧
    (∀ z, MeasurableSet[𝓦] {ω | z ∈ (shiftChart (pChart A C ψ ω) (n ω)).dom}) ∧
    (∀ z, Measurable[𝓦] ({ω | z ∈ (shiftChart (pChart A C ψ ω) (n ω)).dom}.indicator
      fun ω => (shiftChart (pChart A C ψ ω) (n ω)).1 z)) ∧
    (∀ z, Measurable[𝓦] ({ω | z ∈ (shiftChart (pChart A C ψ ω) (n ω)).dom}.indicator
      fun ω => (shiftChart (pChart A C ψ ω) (n ω)).2.2 z)) ∧
    (∀ ω, ContinuousOn (shiftChart (pChart A C ψ ω) (n ω)).2.2 (shiftChart (pChart A C ψ ω) (n ω)).dom) ∧
    (∀ ω, InnerProductSpace.HarmonicOnNhd (shiftChart (pChart A C ψ ω) (n ω)).2.2
      (shiftChart (pChart A C ψ ω) (n ω)).dom) ∧
    (∀ s, Measurable[mΩ, hittingSigma] (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) s)) ∧
    (∀ s, IsHistoryAvoidanceLocal (locPrefixSigma 𝓦 A γ s)
      (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) s) h₀ P) ∧
    ∃ (𝓜 : ℝ≥0 → MeasurableSpace Ω) (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens),
      PocketKernel 𝓦 P A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω))
        (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) 𝓜 M ∧
      ∀ (q : ℝ≥0) (ψ' : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ A →
        ω ∈ Restart.DomainMarkov.avoidSet (fun t ω => segDriver (γ ω) t) (fun ω => capLife (γ ω)) ψ' q →
        ∀ hc : (shiftChart (pChart A C ψ ω) (n ω)).IsConformal, Chart.chartTransport hc 1 a (chiC κ) (M q ω) ψ' =
          ∫ z, couplingMean κ (fun s : ℝ => segDriver (γ ω) s.toNNReal) q
            (phaseProc κ ρL ρR (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
              (geomRW (fun t ω => segDriver (γ ω) t) xR) (δ q) ω q) z * ψ' z := by
  set c : Ω → Chart := fun ω => shiftChart (pChart A C ψ ω) (n ω) with hcdef
  have hprops := pChart_props hCo hCH hψ
  have hcc : ∀ ω, (c ω).IsConformal := fun ω => (hprops ω).2.2.1
  have hpch := isPocketChartOn_pChart (mΩ := 𝓦) hA hCo hCH hψ hCm hψm
  have hcOn : IsPocketChartOn 𝓦 A C ψ c := isPocketChartOn_shift hpch.1 hCm hn
  have hℓ : ∀ ω ∈ A, IsDerivLog (c ω).1 (fun z => pLog A C ψ ω z - n ω * (2 * π * I)) (c ω).dom ∧
      ∀ z ∈ (c ω).dom, (c ω).2.2 z = (pLog A C ψ ω z - n ω * (2 * π * I)).im := fun ω hω =>
    ⟨isDerivLog_sub_int (hpch.2 ω hω).1 (n ω), fun z hz => by
      change (pChart A C ψ ω).2.2 z - 2 * π * (n ω : ℝ) = _
      rw [im_sub_int_mul, (hpch.2 ω hω).2 z hz]⟩
  have hinj : ∀ ω ∈ A, InjOn (ψ ω) (C ω) := fun ω hω => (hψ ω hω).2.injOn
  have hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A γ q ≤ mΩ := PocketUnionPt.locPrefixSigma_le h𝓦 hA hγ hγm
  -- `pocketStopChartLaw_of_sideLimit`, with the chart explicit
  have hact : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → activeDom A γ c q ω = C ω ∩ (H \ F q ω) :=
    fun q ω hω hq => PocketUnionPt.activeDom_eq_inter hω hq (hcOn.1 ω hω).1 (hcOn.1 ω hω).2.1
      (hcOn.1 ω hω).2.2.1 (hinj ω hω) (hgeo q ω hω hq)
  have hlaw : ∀ q : ℝ≥0, PocketUnionPt.PocketStopLaw 𝓦 P A γ C (F q) h₀ (activeCompl A γ c q) q := fun q =>
    pocketStopLaw_activeCompl (hpre q) (hact q) hCo (hFo q) (hU q)
  have hloc : ∀ q, IsLocalSet (activeCompl A γ c q) h₀ P := fun q =>
    ((isLocalSet_tfae hh₀ (hlaw q).1 (hlaw q).2.1).out 1 4).1
      (IsHistoryAvoidanceLocal.isAvoidanceLocal (hlaw q).2.2.1)
  have h𝔥 : ∀ φ : TestOn upperHalfPlaneOpens, smoothDist upperHalfPlaneOpens u φ = ∫ z, u z * φ z :=
    smoothDist_eq_integral hu
  have hmeanAt : ∀ q : ℝ≥0, ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (activeCompl A γ c q) h₀ P g →
      ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∃ v : ℂ → ℝ, ContinuousOn v (C ω ∩ (H \ F q ω)) ∧
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ C ω ∩ (H \ F q ω) →
          (g ω + smoothDist upperHalfPlaneOpens u) φ = ∫ z, v z * φ z) ∧
        ∀ z ∈ C ω ∩ (H \ F q ω), v z + a + chiC κ * (c ω).2.2 z =
          couplingMean κ (fun s : ℝ => segDriver (γ ω) s.toNNReal) q
            (phaseProc κ ρL ρR (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
              (geomRW (fun t ω => segDriver (γ ω) t) xR) (δ q) ω q) ((c ω).1 z) := by
    intro q
    refine phaseMeanAt_of_phaseSideLimit hκ hh₀ (hlaw q).1 (hloc q) (fun ω hω hq => ?_)
      (fun ω hω hq => (hact q ω hω hq).symm) hγ (fun ω hω => ⟨(hcOn.1 ω hω).1, (hℓ ω hω).1, (hℓ ω hω).2⟩) hu hub
      h𝔥 (hside q)
    rw [activeCompl, sdiff_sdiff_cancel_left]
    rw [hact q ω hω hq]
    exact inter_subset_right.trans sdiff_subset
  -- `pocketUnionPtChartLaw_of_stop`, with the chart explicit
  have hgex : ∀ q, ∃ g, IsLocalSetMean (activeCompl A γ c q) h₀ P g := fun q =>
    IsLocalSet.exists_isLocalSetMean hh₀ (hlaw q).1 (hloc q)
  choose g hg using hgex
  have h𝓦ℋ : ∀ q : ℝ≥0, ∀ s, MeasurableSet[𝓦] s → MeasurableSet[locPrefixSigma 𝓦 A γ q] s :=
    fun q s hs => le_sup_left (b := MeasurableSpace.generateFrom _) _ hs
  have hUL : PocketUnionLaw 𝓦 P A γ c h₀ (fun q => activeCompl A γ c q) (fun q => locPrefixSigma 𝓦 A γ q) g := by
    intro q
    obtain ⟨hKm, -, hhist, hgeoK⟩ := hlaw q
    refine ⟨hKm, hpre q, hloc q, hhist, hg q, le_sup_right.trans le_sup_left, ?_, ?_⟩
    · exact PocketUnionPt.measurable_compl_activeDom (h𝓦ℋ q _ hA) (PocketUnionPt.measurableSet_live A γ q) hCo
        (fun z => h𝓦ℋ q _ (hCm z)) (hact q) hgeoK
    · refine Eventually.of_forall fun ω => ?_
      by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)
      · rw [hact q ω hl.1 hl.2]
        obtain ⟨hfr, hF, hKC⟩ := hgeoK ω hl.1 hl.2
        refine ⟨fun z hz => ⟨hz.2.1, fun hzK => hz.2.2 (hKC ⟨hzK, hz.1⟩)⟩, fun z hz =>
          PocketUnionPt.connectedComponentIn_subset_inter (hCo ω hl.1) hfr (fun x hx => ?_) hz⟩
        refine hF ⟨?_, hx.1⟩
        by_contra hxF
        exact hx.2 ⟨hx.1, hxF⟩
      · rw [PocketUnionPt.activeDom_eq_empty hl]
        exact ⟨empty_subset _, fun z hz => hz.elim⟩
  have hpt : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∃ v : ℂ → ℝ,
      ContinuousOn v ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q)) ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) →
          (g q ω + smoothDist upperHalfPlaneOpens u) φ = ∫ z, v z * φ z) ∧
      ∀ w ∈ H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q,
        v ((c ω).2.1 w) + a + chiC κ * (c ω).2.2 ((c ω).2.1 w) =
          couplingMean κ (fun s : ℝ => segDriver (γ ω) s.toNNReal) q
            (phaseProc κ ρL ρR (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
              (geomRW (fun t ω => segDriver (γ ω) t) xR) (δ q) ω q) w := by
    intro q
    filter_upwards [hmeanAt q (g q) (hg q)] with ω hω hωA hq
    obtain ⟨v, hvc, hvrep, hvid⟩ := hω hωA hq
    have hE : (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) = C ω ∩ (H \ F q ω) := by
      rw [← activeDom_eq hωA hq]
      exact hact q ω hωA hq
    refine ⟨v, by rw [hE]; exact hvc, fun φ hφ => hvrep φ (by rw [← hE]; exact hφ), fun w hw => ?_⟩
    have hz : (c ω).2.1 w ∈ C ω ∩ (H \ F q ω) := by
      rw [← hE]
      exact mem_image_of_mem _ hw
    have h := hvid _ hz
    rwa [(hcOn.1 ω hωA).1.2.2 w hw.1] at h
  refine ⟨hcc, fun z => measurableSet_mem_dom_shiftChart hCo hCH hψ hA hCm n z,
    fun z => measurable_fwd_shiftChart hCo hCH hψ hA hψm n z,
    fun z => measurable_lift_shiftChart hCo hCH hψ hA hCm hψm hn z,
    continuousOn_lift_shiftChart hCo hCH hψ n, harmonicOnNhd_lift_shiftChart hCo hCH hψ n, fun s => (hlaw s).1,
    fun s => (hlaw s).2.2.1, _, _, pocketKernel_of_unionLaw hh₀ _ (fun _ => rfl) hUL,
    fun q ψ' => ?_⟩
  filter_upwards [hpt q] with ω hω hωA hav hc'
  obtain ⟨hq, hdisj⟩ := hav
  obtain ⟨v, hvc, hM, hid⟩ := hω hωA hq
  have hVo : IsOpen (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) :=
    Coupling.MartMeans2.isOpen_H_diff_fwdHull_rpath (hγ ω hωA).segDriver_spec.2.1 hq
  exact chartTransport_eq_of_pointwise hc' ((hcOn.1 ω hωA).2.2.2) a (chiC κ) hVo sdiff_subset hvc hM hid ψ'
    fun z hz => ⟨ψ'.tsupport_subset hz, fun h => hdisj.notMem_of_mem_left hz h⟩


end Gen

end InteractingSLE.Sec7.PhaseClause
