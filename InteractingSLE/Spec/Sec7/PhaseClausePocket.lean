/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseClauseMean
import InteractingSLE.Spec.Sec7.PhaseClauseRead
import InteractingSLE.Spec.Sec7.PhaseSideR7
import InteractingSLE.Spec.Sec7.PhaseMartR7
import InteractingSLE.WangWu.ReverseContactMartFilt2

/-!
# R.7's retained hypothesis (M) on one pocket, from R.5 up to a constant phase

Packet PROVE-PHASECLAUSE. Specification Aux. lemma 122 (`source/spec/p385-432.md`, pp. 389–391) and Astra's follow-up
5 §3.2 (R73, `source/external/AstraIG1/ig1_followup5.txt` L456–L483): "The adopted mean continuity and the continuous
Loewner coordinates make the quotient in (3.2) continuous in positive time. It is lattice-valued, hence constant on the
positive lifetime. […] Right continuity of the retained filtration makes this constant measurable at time zero."

On one pocket test (a walls-event `A` with the pocket data of `Lemma725RefChart.pocketChartData_of_stop`), given R.5 up
to phase (`PocketStopSide.PocketStopPhaseSideLimit`, phase `δ_q`) and the constancy of the phase on the positive
lifetime (`δ_q = c` almost surely on the live event, every `q > 0`), this file proves Aux. lemma 122's retained
hypothesis (M) (`PhaseSide.TwoSeedPhaseMeans`) and hence `PhaseSide.TwoSeedPhaseMeansAt`:

* the kernel and the phase mean identification (`pocketChartPhaseData_of_stop`), transferred to the test subtype;
* the phase read from the retained σ-algebras at positive times (`exists_measurableSet_iff_phase`), a measurable
  lattice version `c₁` of the constant phase (`aemeasurable_of_forall_pos_iff`);
* the retained filtration `𝓗_q = 𝓦 ∨ prefix events up to q ∨ σ(c₁)` on the subtype, its transfer to the kernel
  σ-algebras (`exists_ae_eq_of_sup_comap`), and the phase clause (`isPhaseCouplingCharFun_chartTransport`);
* integrable pairings (`integrable_apply_of_isPhaseCouplingCharFun`) and PROVE-PHASEMART's
  `twoSeedPhaseMeans_of_phaseCharFun_adapted`.

## Main results

* `integrable_apply_of_isPhaseCouplingCharFun`;
* **`twoSeedPhaseMeansAt_of_stop`**: `TwoSeedPhaseMeansAt` on one pocket test from its stop data, R.5 up to phase and
  the constancy of the phase.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open QuantumZipper (H fwdHull chiC zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.PhaseClause

open PocketStop PocketTraversal PocketAdapt Lemma71C LocalSets WholeField PocketCoupling PocketUnionPt PhaseSel
  Lemma725RefChart PocketStopField Lemma725RefSafe PhaseMart MartChar

/-! ### Integrable pairings from the phase clause at time `0` -/

section Integrable

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {nL nR : ℕ} {κ : ℝ}
  {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
  {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Integrable pairings of a field with the phase clause** (`WangWu.integrable_apply_of_isCouplingCharFun_of_bounded`
for the phase clause): when the seeds start at the driver, the exposed interval at time `0` is empty, so the clause at
time `0` is the force-word clause, and the pairing is a conditionally Gaussian variable with bounded mean and
deterministic variance. -/
theorem integrable_apply_of_isPhaseCouplingCharFun [IsProbabilityMeasure P] {d : ℝ≥0 → Ω → ℝ}
    (hcf : IsPhaseCouplingCharFun κ ρL ρR P 𝓖 W VL VR d ζ h)
    (h0 : ∀ᵐ ω ∂P, 0 < ζ ω ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0)
    (hseed : ∀ ω, VR 0 0 ω - W 0 ω ≤ VL 0 0 ω - W 0 ω)
    (φ : TestOn upperHalfPlaneOpens) (hφm : Measurable fun ω => h ω φ) :
    Integrable (fun ω => h ω φ) P := by
  set E₀ : ℝ := loewnerGreenEnergy (fun _ => 0) 0 φ with hE₀
  have hE0 : 0 ≤ E₀ := Coupling.MartMeans2.loewnerGreenEnergy_zero_nonneg φ
  have hτ : IsStoppingTime 𝓖 fun _ : Ω => ((0 : ℝ≥0) : WithTop ℝ≥0) := isStoppingTime_const 𝓖 0
  have hτm : hτ.measurableSpace = 𝓖 0 := IsStoppingTime.measurableSpace_const 𝓖 0
  have hlt : ∀ᵐ ω ∂P, ((((0 : ℝ≥0) : WithTop ℝ≥0)) : ℝ≥0∞) < ζ ω := by
    filter_upwards [h0] with ω hω
    exact hω.1
  set u : Ω → ℂ → ℝ := fun ω => meanExt κ ρL ρR (W 0 ω) (fun i => VL i 0 ω) (fun i => VR i 0 ω) with hudef
  have hu : ∀ ω, IsBoundedHarmonicExtension
      (phaseData κ ρL ρR (fun i => VL i ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω -
          W ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω)
        (fun i => VR i ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω - W ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω)
        (d ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω -
          W ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω)
        (fun i => VR i ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω - W ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω))
      (u ω) := fun ω => by
    rw [WithTop.untopD_coe, phaseData_eq_of_le (vL := fun i => VL i 0 ω - W 0 ω)
      (vR := fun i => VR i 0 ω - W 0 ω) (hseed ω) _ 0]
    refine PhaseSel.isBoundedHarmonicExtension_congr_data (isBoundedHarmonicExtension_meanExt κ ρL ρR _ _ _)
      fun x _ => ?_
    simp only [phaseData, zero_mul, add_zero]
  set M : Ω → ℝ := fun ω => ∫ z, u ω z * φ z with hMdef
  have hcond : ∀ θ : ℝ, P[fun ω => cexp (I * ((θ * h ω φ : ℝ) : ℂ)) | 𝓖 0] =ᵐ[P]
      fun ω => cexp (I * ((θ * M ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (θ ^ 2 * E₀)) : ℝ) : ℂ) := by
    intro θ
    have hcl := hcf _ hτ hlt u hu (θ • φ)
    rw [hτm] at hcl
    have e1 : (fun ω' => cexp (I * (h ω' (θ • φ) : ℂ))) = fun ω' => cexp (I * ((θ * h ω' φ : ℝ) : ℂ)) := by
      funext ω'
      rw [map_smul, smul_eq_mul]
    rw [e1] at hcl
    filter_upwards [hcl, h0] with ω hω hgω
    obtain ⟨hζ, hwc, hw0⟩ := hgω
    have ht0 : (((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0 : ℝ≥0) : ℝ) = 0 := by
      rw [WithTop.untopD_coe, NNReal.coe_zero]
    have hK : fwdHull (fun s : ℝ => W s.toNNReal ω) (((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0 : ℝ≥0) : ℝ) = ∅ := by
      rw [ht0]
      exact Coupling.MartMeans2.fwdHull_rpath_zero (w := fun t => W t ω) hwc hζ
    rw [hω (by rw [hK]; exact disjoint_empty _), ht0]
    have hr0 : (fun s : ℝ => W s.toNNReal ω) 0 = 0 := by
      simp only [Real.toNNReal_zero, hw0]
    have hcoe : (⇑(θ • φ) : ℂ → ℝ) = θ • ⇑φ := by
      funext y
      simp
    have hmean : (∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) 0 (u ω) z * (θ • φ) z) = θ * M ω := by
      rw [hcoe, ← Coupling.MartMeans.integral_mul_smul (u ω) θ φ]
      congr 1
      funext z
      by_cases hz : (θ • ⇑φ) z = 0
      · simp only [hz, mul_zero]
      · have hzH : z ∈ H := φ.tsupport_subset (subset_tsupport _ fun h0 => hz (by
          simp only [Pi.smul_apply, smul_eq_mul, h0, mul_zero]))
        have hz0 : z ≠ 0 := by
          intro h; rw [h] at hzH; exact lt_irrefl _ (show (0 : ℂ).im > 0 from hzH)
        rw [Coupling.MartMeans2.couplingMean_zero κ hr0 (u ω) hz0]
    have hen : loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) 0 ⇑(θ • φ) = θ ^ 2 * E₀ := by
      rw [hcoe, Coupling.MartMeans.loewnerGreenEnergy_smul, Coupling.MartMeans2.loewnerGreenEnergy_zero_eq hr0 φ]
    rw [hmean, hen, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- a `𝓖₀`-measurable version of the mean
  obtain ⟨M', hM'm, hM'e⟩ := Sec6.Prop65.exists_measurable_ae_eq_of_condCharFun
    (V := fun _ => E₀) (@measurable_const _ _ _ (𝓖 0) _) hcond
  have hcond' : ∀ θ : ℝ, P[fun ω => cexp (I * ((θ * h ω φ : ℝ) : ℂ)) | 𝓖 0] =ᵐ[P]
      fun ω => cexp (I * ((θ * M' ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (θ ^ 2 * E₀)) : ℝ) : ℂ) := by
    intro θ
    filter_upwards [hcond θ, hM'e] with ω h1 h2
    rw [h1, h2]
  have hsub : ∀ θ : ℝ, P[fun ω => cexp (I * ((θ * (h ω φ - M' ω) : ℝ) : ℂ)) | 𝓖 0] =ᵐ[P]
      fun _ => ((Real.exp (-(1 / 2) * (θ ^ 2 * E₀)) : ℝ) : ℂ) := fun θ =>
    Sec6.Prop65.condCharFun_sub_of_condCharFun (V := fun _ => E₀) hφm hM'm (𝓖.le 0) θ (hcond' θ)
  have hY := Sec6.Prop65.integrable_pow_of_condCharFun (𝓖.le 0) (hφm.sub (hM'm.mono (𝓖.le 0) le_rfl))
    (V := fun _ => E₀) measurable_const (fun _ => hE0) (K := E₀) (fun _ => le_rfl) hsub 1
  simp only [pow_one] at hY
  -- the mean is bounded
  set C : ℝ := |Real.pi / Real.sqrt κ| *
    (3 + 2 * ∑ i, |(Ito.weightWord ρL ρR).ρL i| + ∑ i, |(Ito.weightWord ρL ρR).ρR i|) with hC
  have hφi : Integrable (fun z => C * |φ z|) :=
    (φ.continuous.abs.integrable_of_hasCompactSupport φ.hasCompactSupport.abs).const_mul C
  have hMb : ∀ ω, |M ω| ≤ ∫ z, C * |φ z| := fun ω => by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hφi (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hz : φ z = 0
    · simp [hz]
    · have hzH : z ∈ H := φ.tsupport_subset (subset_tsupport _ hz)
      exact mul_le_mul_of_nonneg_right (WangWu.abs_meanExt_le κ ρL ρR _ _ _ hzH) (abs_nonneg _)
  have hM'i : Integrable M' P := by
    refine Integrable.of_bound (hM'm.mono (𝓖.le 0) le_rfl).aestronglyMeasurable (∫ z, C * |φ z|) ?_
    filter_upwards [hM'e] with ω hω
    rw [hω, Real.norm_eq_abs]
    exact hMb ω
  have e : (fun ω => h ω φ) = fun ω => (h ω φ - M' ω) + M' ω := by
    funext ω; ring
  rw [e]
  exact hY.add hM'i

end Integrable

/-! ### (M) on one pocket test -/

section Assembly

universe u

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **Aux. lemma 122's retained hypothesis on one two-seed pocket, from R.5 up to a constant phase** (follow-up 5 §3.2).
On a walls-event `A` of positive probability with the pocket stop data of `Lemma725RefChart.pocketChartData_of_stop`
(the erased traversal `γ`, the open pocket `C` with its Jordan coordinate `ψ`, the hull sets `F q`, the marked union
laws `hU`), R.5 up to phase (`hside`, phase `δ_q`) and the constancy of the phase (`δ_q = c` almost surely on the live
event at every `q > 0`) give `PhaseSide.TwoSeedPhaseMeansAt` for the shifted canonical pocket chart: the offset `a` and
the phase `δ'_q = c₁` (a measurable lattice version of `c`) with R.5 up to phase and Aux. lemma 122's retained
hypothesis (M). -/
theorem twoSeedPhaseMeansAt_of_stop [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ) (h𝓦 : 𝓦 ≤ mΩ)
    {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hPA : 0 < P A) {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    (hunb : ∀ ω ∈ A, ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    {C : Ω → Set ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z)) {F : ℝ≥0 → Ω → Set ℂ}
    (hFo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ F q ω))
    (hgeo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      ψ ω '' (C ω ∩ (H \ F q ω)) = H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M) {n : Ω → ℤ}
    (hn : Measurable[𝓦] n) {a : ℝ} (hU : ∀ q : ℝ≥0, PocketStopUnionLaw 𝓦 P A γ C (F q) h₀ q)
    {δ : ℝ≥0 → Ω → ℝ}
    (hside : ∀ q : ℝ≥0, PocketStopSide.PocketStopPhaseSideLimit κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ
      (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) (fun ω => shiftChart (pChart A C ψ ω) (n ω)) a h₀ u
      (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q) (δ q) q)
    {c : Ω → ℝ} (hconst : ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → δ q ω = c ω) :
    PhaseSide.TwoSeedPhaseMeansAt κ rL rR P A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) h₀ u := by
  classical
  set ch : Ω → Chart := fun ω => shiftChart (pChart A C ψ ω) (n ω) with hchdef
  obtain ⟨hcc, hdom, hfwd, hliftm, hliftc, -, -, -, 𝓜, M, ⟨h𝓜, h𝓜pre, hK⟩, hmean⟩ :=
    pocketChartPhaseData_of_stop hκ (ρL := fun _ : Fin 1 => rL) (ρR := fun _ : Fin 1 => rR)
      (xL := fun _ => LP.twoSeedXL) (xR := fun _ => LP.twoSeedXR) h𝓦 hA hγ hγm hCo hCH hψ hCm hψm hFo hgeo hh₀
      hu hub hn hU hside
  set hf : Ω → DistOn upperHalfPlaneOpens := fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u with hfdef
  have hfm : Measurable hf := measurable_add_const hh₀.measurable _ (fun _ => rfl)
  have hAm : MeasurableSet A := h𝓦 _ hA
  have hP' : IsProbabilityMeasure (condSub P A) := isProbabilityMeasure_condSub hAm hPA.ne'
  -- the relative history filtration on `A`
  have h𝓔 : MeasurableSpace.comap Subtype.val 𝓦 ≤ (inferInstance : MeasurableSpace A) :=
    MeasurableSpace.comap_mono h𝓦
  have hdrive : ∀ ω : A, IsDrivenCurve (γ ω) := fun ω => hγ ω ω.2
  have hm : ∀ r n k, MeasurableSet (prefixEvent (fun ω : A => γ ω) r n k) := fun r n k =>
    PocketMeas.measurableSet_prefixEvent hdrive hγm r n k
  set 𝓗₀ := prefixFilt (MeasurableSpace.comap Subtype.val 𝓦) h𝓔 (fun ω : A => γ ω) hm with h𝓗₀def
  have hpre₀ : IsPrefixAdapted 𝓗₀ (fun ω : A => γ ω) := isPrefixAdapted_prefixFilt h𝓔 hm
  have h0 : MeasurableSpace.comap Subtype.val 𝓦 ≤ 𝓗₀ 0 := le_prefixFilt_zero h𝓔 hm
  have h𝓗𝓜 : ∀ q, 𝓗₀ q ≤ MeasurableSpace.comap Subtype.val (𝓜 q) := fun q => by
    show prefixSigma _ (fun ω : A => γ ω) q ≤ _
    rw [← comap_locPrefixSigma]
    exact MeasurableSpace.comap_mono (h𝓜pre q)
  have h𝓜' : ∀ q, MeasurableSpace.comap (Subtype.val : A → Ω) (𝓜 q) ≤ (inferInstance : MeasurableSpace A) :=
    fun q => MeasurableSpace.comap_mono (h𝓜 q)
  have hA𝓜 : ∀ q, MeasurableSet[𝓜 q] A := fun q =>
    h𝓜pre q _ ((le_sup_left : 𝓦 ≤ locPrefixSigma 𝓦 A γ q) _ hA)
  have h𝒢𝓜 : ∀ q, 𝓗₀ 0 ≤ MeasurableSpace.comap Subtype.val (𝓜 q) := fun q =>
    (𝓗₀.mono (zero_le (a := q))).trans (h𝓗𝓜 q)
  -- the chart on `A`
  have hind : ∀ {β : Type} [Zero β] [MeasurableSpace β] (z : ℂ) (f : Ω → ℂ → β),
      Measurable[𝓦] ({ω | z ∈ (ch ω).dom}.indicator fun ω => f ω z) →
      Measurable[𝓗₀ 0] ({ω : A | z ∈ (ch ω).dom}.indicator fun ω => f ω z) := fun z f hf' => by
    have e : ({ω : A | z ∈ (ch ω).dom}.indicator fun ω => f ω z) =
        ({ω | z ∈ (ch ω).dom}.indicator fun ω => f ω z) ∘ Subtype.val := by
      funext ω
      by_cases hz : z ∈ (ch ω).dom
      · simp only [Function.comp_apply, indicator_of_mem (show ω ∈ {ω : A | z ∈ (ch ω).dom} from hz),
          indicator_of_mem (show (ω : Ω) ∈ {ω | z ∈ (ch ω).dom} from hz)]
      · simp only [Function.comp_apply, indicator_of_notMem (show ω ∉ {ω : A | z ∈ (ch ω).dom} from hz),
          indicator_of_notMem (show (ω : Ω) ∉ {ω | z ∈ (ch ω).dom} from hz)]
    rw [e]
    exact (hf'.comp (comap_measurable (Subtype.val : A → Ω))).mono h0 le_rfl
  have hdomA : ∀ z, MeasurableSet[𝓗₀ 0] {ω : A | z ∈ (ch ω).dom} := fun z => h0 _ ⟨_, hdom z, rfl⟩
  have hfwdA := fun z => hind z (fun ω => (ch ω).1) (hfwd z)
  have hliftA := fun z => hind z (fun ω => (ch ω).2.2) (hliftm z)
  have hh' : Measurable fun ω : A => hf ω := hfm.comp measurable_subtype_coe
  -- the kernel and the phase mean identification on `A`
  have hcond : ∀ (q : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ (ω : A) ∂(condSub P A),
      (q : ℝ≥0∞) < capLife (γ ω) →
      tsupport φ ⊆ (ch ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) →
      condExp (MeasurableSpace.comap Subtype.val (𝓜 q)) (condSub P A)
          (fun ω : A => Complex.exp (Complex.I * (hf ω φ : ℂ))) ω =
        Complex.exp (Complex.I * (M q ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((ch ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q))
            φ φ : ℝ) : ℂ)) := fun q φ => by
    have hint : Integrable (fun ω => Complex.exp (Complex.I * (hf ω φ : ℂ))) P :=
      GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hfm)
    filter_upwards [condExp_condSub_ae_eq (h𝓜 q) (hA𝓜 q) hPA.ne' hint, ae_condSub_of_ae hAm (hK q φ)]
      with ω h1 h2 hq hs
    rw [h1]
    exact h2 ω.2 hq hs
  have hmean' : ∀ (q : ℝ≥0) (ψ' : TestOn upperHalfPlaneOpens), ∀ᵐ (ω : A) ∂(condSub P A),
      ω ∈ Restart.DomainMarkov.avoidSet (fun t (ω : A) => segDriver (γ ω) t) (fun ω : A => capLife (γ ω)) ψ' q →
      Chart.chartTransport (hcc ω) 1 a (chiC κ) (M q ω) ψ' =
        ∫ z, couplingMean κ (fun s : ℝ => segDriver (γ ω) s.toNNReal) q
          (phaseProc κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun t (ω : A) => segDriver (γ ω) t)
            (geomLW (fun t (ω : A) => segDriver (γ ω) t) fun _ : A => LP.twoSeedXL)
            (geomRW (fun t (ω : A) => segDriver (γ ω) t) fun _ : A => LP.twoSeedXR)
            (fun ω : A => δ q ω) ω q) z * ψ' z := fun q ψ' => by
    filter_upwards [ae_condSub_of_ae hAm (hmean q ψ')] with ω hω hav
    exact hω ω.2 hav (hcc ω)
  -- the phase read from the retained σ-algebras at positive times
  have hcA : ∀ q : ℝ≥0, 0 < q → ∀ᵐ (ω : A) ∂(condSub P A), (q : ℝ≥0∞) < capLife (γ ω) → δ q ω = c ω :=
    fun q hq => by
      filter_upwards [ae_condSub_of_ae hAm (hconst q hq)] with ω hω hl
      exact hω ω.2 hl
  have hread : ∀ c₀ : A → ℝ, (∀ q : ℝ≥0, 0 < q → ∀ᵐ (ω : A) ∂(condSub P A), (q : ℝ≥0∞) < capLife (γ ω) →
      δ q ω = c₀ ω) → ∀ q : ℝ≥0, 0 < q → ∀ B : Set ℝ, MeasurableSet B → ∃ S : Set A,
        MeasurableSet[MeasurableSpace.comap Subtype.val (𝓜 q)] S ∧
        ∀ᵐ (ω : A) ∂(condSub P A), (q : ℝ≥0∞) < capLife (γ ω) → (c₀ ω ∈ B ↔ ω ∈ S) :=
    fun c₀ hc₀ q hq B hB => exists_measurableSet_iff_phase (P := condSub P A) (ρL := fun _ : Fin 1 => rL)
      (ρR := fun _ : Fin 1 => rR) hκ (𝓗 := 𝓗₀) hdrive hpre₀ (xL := fun _ : A => LP.twoSeedXL)
      (xR := fun _ : A => LP.twoSeedXR) measurable_const measurable_const (c := fun ω : A => ch ω)
      (fun ω : A => hcc ω) hdomA hfwdA hliftA (fun ω : A => hliftc ω) hh' a (chiC κ) hq
      (fun q => MeasurableSpace.comap Subtype.val (𝓜 q)) (h𝓜' q) (h𝒢𝓜 q) (h𝓗𝓜 q) (fun ω : A => M q ω)
      (hcond q) (d := fun ω : A => δ q ω) (hmean' q) (hc₀ q hq) hB
  have hae : AEMeasurable (fun ω : A => c ω) (condSub P A) :=
    aemeasurable_of_forall_pos_iff hdrive hpre₀ (fun q => MeasurableSpace.comap Subtype.val (𝓜 q)) h𝓜'
      (hread (fun ω : A => c ω) hcA)
  -- the phase is lattice-valued
  have hlatA : ∀ᵐ (ω : A) ∂(condSub P A), ∃ m : ℤ, c ω = m * phaseStep κ := by
    have h1 : ∀ k : ℕ, ∀ᵐ (ω : A) ∂(condSub P A),
        (((1 / ((k : ℝ) + 1)).toNNReal : ℝ≥0) : ℝ≥0∞) < capLife (γ ω) → ∃ m : ℤ, c ω = m * phaseStep κ := by
      intro k
      have hq : 0 < (1 / ((k : ℝ) + 1)).toNNReal := Real.toNNReal_pos.2 (by positivity)
      filter_upwards [ae_condSub_of_ae hAm (hside _).1, hcA _ hq] with ω h1 h2 hl
      obtain ⟨m, hm⟩ := h1 ω.2 hl
      exact ⟨m, (h2 hl).symm.trans hm⟩
    filter_upwards [ae_all_iff.2 h1] with ω hω
    obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (PocketPhaseMeans.capLife_pos (hdrive ω))
    have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hr0'
    exact hω k (lt_trans (ENNReal.coe_lt_coe.2 ((Real.toNNReal_lt_iff_lt_coe (by positivity)).2 hk)) hr)
  -- a measurable lattice version `c₁` of the phase
  set c₂ : A → ℝ := hae.mk _ with hc₂def
  have hc₂m : Measurable c₂ := hae.measurable_mk
  have hc₂e : (fun ω : A => c ω) =ᵐ[condSub P A] c₂ := hae.ae_eq_mk
  set Lat : Set ℝ := range fun m : ℤ => (m : ℝ) * phaseStep κ with hLat
  have hLatm : MeasurableSet Lat := (countable_range _).measurableSet
  set c₁ : A → ℝ := fun ω => if c₂ ω ∈ Lat then c₂ ω else 0 with hc₁def
  have hc₁m : Measurable c₁ := Measurable.ite (hc₂m hLatm) hc₂m measurable_const
  have hc₁lat : ∀ ω : A, ∃ m : ℤ, c₁ ω = m * phaseStep κ := fun ω => by
    by_cases hL : c₂ ω ∈ Lat
    · obtain ⟨m, hm⟩ := hL
      refine ⟨m, ?_⟩
      simp only [hc₁def, show c₂ ω ∈ Lat from ⟨m, hm⟩, ↓reduceIte]
      exact hm.symm
    · exact ⟨0, by simp only [hc₁def, hL, ↓reduceIte, Int.cast_zero, zero_mul]⟩
  have hc₁e : ∀ᵐ (ω : A) ∂(condSub P A), c₁ ω = c ω := by
    filter_upwards [hc₂e, hlatA] with ω h1 h2
    have hL : c₂ ω ∈ Lat := by
      obtain ⟨m, hm⟩ := h2
      exact ⟨m, hm.symm.trans h1⟩
    simp only [hc₁def, hL, ↓reduceIte]
    exact h1.symm
  have hc₁A : ∀ q : ℝ≥0, 0 < q → ∀ᵐ (ω : A) ∂(condSub P A), (q : ℝ≥0∞) < capLife (γ ω) → δ q ω = c₁ ω :=
    fun q hq => by
      filter_upwards [hcA q hq, hc₁e] with ω h1 h2 hl
      rw [h1 hl, h2]
  -- the retained filtration: the relative history and the phase
  let 𝓗 : Filtration ℝ≥0 (inferInstance : MeasurableSpace A) :=
    { seq := fun q => 𝓗₀ q ⊔ MeasurableSpace.comap c₁ inferInstance
      mono' := fun _ _ hst => sup_le_sup_right (𝓗₀.mono hst) _
      le' := fun q => sup_le (𝓗₀.le q) hc₁m.comap_le }
  have hpre : IsPrefixAdapted 𝓗 (fun ω : A => γ ω) := fun r n k =>
    (le_sup_left : 𝓗₀ r ≤ 𝓗₀ r ⊔ MeasurableSpace.comap c₁ inferInstance) _ (hpre₀ r n k)
  have hc₁0 : Measurable[usualAugmentation 𝓗 (condSub P A) 0] c₁ :=
    (comap_measurable c₁).mono ((le_sup_right : MeasurableSpace.comap c₁ inferInstance ≤
      𝓗₀ 0 ⊔ MeasurableSpace.comap c₁ inferInstance).trans (Ito.le_usualAugmentation 𝓗 (condSub P A) 0)) le_rfl
  have hT : ∀ q : ℝ≥0, 0 < q → ∀ D : Set A, MeasurableSet[𝓗 q] D →
      (∀ᵐ ω ∂(condSub P A), ω ∈ D → (q : ℝ≥0∞) < capLife (γ ω)) →
      ∃ D' : Set A, MeasurableSet[MeasurableSpace.comap Subtype.val (𝓜 q)] D' ∧ D =ᵐ[condSub P A] D' :=
    fun q hq D hD hDL => exists_ae_eq_of_sup_comap (P := condSub P A) (𝓐 := 𝓗₀ q)
      (𝓑 := MeasurableSpace.comap Subtype.val (𝓜 q)) (h𝓗𝓜 q) (L := {ω : A | (q : ℝ≥0∞) < capLife (γ ω)})
      (measurableSet_lt_capLife hpre₀ (fun ω => (hdrive ω).zero) q) (hread c₁ hc₁A q hq) hD hDL
  -- the phase clause
  have hcf := isPhaseCouplingCharFun_chartTransport (P := condSub P A) (ρL := fun _ : Fin 1 => rL)
    (ρR := fun _ : Fin 1 => rR) hκ (𝓗 := 𝓗) hdrive hpre (xL := fun _ : A => LP.twoSeedXL)
    (xR := fun _ : A => LP.twoSeedXR) measurable_const measurable_const (c := fun ω : A => ch ω)
    (fun ω : A => hcc ω) (fun q => MeasurableSpace.comap Subtype.val (𝓜 q)) h𝓜' h𝒢𝓜 hdomA hfwdA hliftA
    (fun ω : A => hliftc ω) hh' a (chiC κ) hT (fun q (ω : A) => M q ω) hcond (d := fun q (ω : A) => δ q ω) hmean'
    hc₁0 hc₁A
  -- integrable pairings
  have hX : Measurable fun ω : A => Chart.chartTransport (hcc ω) 1 a (chiC κ) (hf ω) :=
    Chart.measurable_chartTransport_random' (fun ω : A => hcc ω) (fun z => 𝓗₀.le 0 _ (hdomA z))
      (fun z => (hfwdA z).mono (𝓗₀.le 0) le_rfl) (fun z => (hliftA z).mono (𝓗₀.le 0) le_rfl)
      (fun ω : A => hliftc ω) hh' 1 a (chiC κ)
  have hz0 : ∀ ω : A, geomLW (fun t (ω : A) => segDriver (γ ω) t) (fun _ : A => LP.twoSeedXL) 0 0 ω = 0 ∧
      geomRW (fun t (ω : A) => segDriver (γ ω) t) (fun _ : A => LP.twoSeedXR) 0 0 ω = 0 := fun ω =>
    geomLW_geomRW_zero_of_seed (T := fun ω : A => capLife (γ ω)) (W := fun t (ω : A) => segDriver (γ ω) t)
      (fun ω => (hdrive ω).segDriver_spec.1) (fun ω => (hdrive ω).segDriver_spec.2.1)
      (xL := fun _ : A => LP.twoSeedXL) (xR := fun _ : A => LP.twoSeedXR) (fun _ => rfl) (fun _ => rfl)
      (PocketPhaseMeans.capLife_pos (hdrive ω))
  have hseed : ∀ ω : A, geomRW (fun t (ω : A) => segDriver (γ ω) t) (fun _ : A => LP.twoSeedXR) 0 0 ω -
      segDriver (γ ω) 0 ≤ geomLW (fun t (ω : A) => segDriver (γ ω) t) (fun _ : A => LP.twoSeedXL) 0 0 ω -
      segDriver (γ ω) 0 := fun ω => by
    rw [(hz0 ω).1, (hz0 ω).2]
  have hint : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω : A => Chart.chartTransport (hcc ω) 1 a (chiC κ) (hf ω) φ) (condSub P A) := fun φ =>
    integrable_apply_of_isPhaseCouplingCharFun hcf
      (ae_of_all _ fun ω => ⟨PocketPhaseMeans.capLife_pos (hdrive ω), (hdrive ω).segDriver_spec.2.1,
        (hdrive ω).segDriver_spec.1⟩) hseed φ ((LQGMetric.measurable_distOn_apply φ).comp hX)
  -- (M) for the phase `c₁`
  set δ' : ℝ≥0 → Ω → ℝ := fun _ ω => if hω : ω ∈ A then c₁ ⟨ω, hω⟩ else 0 with hδ'def
  have hδ'A : ∀ t (ω : A), δ' t ω = c₁ ω := fun t ω => by
    simp only [hδ'def, ω.2, ↓reduceDIte]
  have hδa : AdaptedBefore (usualAugmentation 𝓗 (condSub P A)) (fun ω : A => capLife (γ ω))
      (fun t (ω : A) => δ' t ω) := by
    intro t B hB
    have e : {ω : A | (t : ℝ≥0∞) < capLife (γ ω) ∧ δ' t ω ∈ B} =
        {ω : A | (t : ℝ≥0∞) < capLife (γ ω)} ∩ c₁ ⁻¹' B := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, hδ'A]
    rw [e]
    refine MeasurableSet.inter ?_ ?_
    · exact Ito.le_usualAugmentation 𝓗 _ t _ (measurableSet_lt_capLife hpre (fun ω => (hdrive ω).zero) t)
    · exact (usualAugmentation 𝓗 (condSub P A)).mono (zero_le (a := t)) _ (hc₁0 hB)
  have hM := twoSeedPhaseMeans_of_phaseCharFun_adapted (P := P) (κ := κ) (rL := rL) (rR := rR) hκ hAm hPA.ne'
    (fun ω hω => ⟨hγ ω hω, hunb ω hω⟩) (usualAugmentation 𝓗 (condSub P A))
    (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (fun r n k => Ito.le_usualAugmentation 𝓗 _ r _ (hpre r n k)) hint hδa hc₁lat (fun ω t _ _ => hδ'A t ω) hcf
  -- R.5 up to phase for the phase `c₁`
  have hcc₁ : ∀ᵐ ω ∂P, ω ∈ A → ∀ hω : ω ∈ A, c ω = c₁ ⟨ω, hω⟩ := by
    refine PocketMartLife.ae_of_ae_condSub (p := fun ω => ∀ hω : ω ∈ A, c ω = c₁ ⟨ω, hω⟩) hAm ?_
    filter_upwards [hc₁e] with ω h _
    exact h.symm
  have hside' : ∀ q : ℝ≥0, PocketStopSide.PocketStopPhaseSideLimit κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A
      γ (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) ch a h₀ u (activeCompl A γ ch q) (δ' q) q := by
    intro q
    refine ⟨Eventually.of_forall fun ω hω _ => ?_, fun g hg => ?_⟩
    · obtain ⟨m, hm⟩ := hc₁lat ⟨ω, hω⟩
      exact ⟨m, (hδ'A q ⟨ω, hω⟩).trans hm⟩
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ q) with hq0 | hqpos
    · subst hq0
      filter_upwards [(hside 0).2 g hg] with ω hω hωA hl v hv hvr ξ hξ
      have h := hω hωA hl v hv hvr ξ hξ
      have hL : geomLW (fun t ω => segDriver (γ ω) t) (fun _ : Ω => LP.twoSeedXL) 0 0 ω = 0 := (hz0 ⟨ω, hωA⟩).1
      have hR : geomRW (fun t ω => segDriver (γ ω) t) (fun _ : Ω => LP.twoSeedXR) 0 0 ω = 0 := (hz0 ⟨ω, hωA⟩).2
      have hW0 : segDriver (γ ω) 0 = 0 := (hγ ω hωA).segDriver_spec.1
      rwa [phaseData_eq_of_le (vL := fun i => geomLW (fun t ω => segDriver (γ ω) t) (fun _ : Ω => LP.twoSeedXL) i 0 ω -
        segDriver (γ ω) 0) (vR := fun j => geomRW (fun t ω => segDriver (γ ω) t) (fun _ : Ω => LP.twoSeedXR) j 0 ω -
        segDriver (γ ω) 0) (by simp only [hL, hR, hW0, le_refl]) (δ 0 ω) (δ' 0 ω)] at h
    · filter_upwards [(hside q).2 g hg, hconst q hqpos, hcc₁] with ω hω hd hcω hωA hl v hv hvr ξ hξ
      have e : δ q ω = δ' q ω := by
        rw [hd hωA hl, hcω hωA hωA]
        exact (hδ'A q ⟨ω, hωA⟩).symm
      rw [← e]
      exact hω hωA hl v hv hvr ξ hξ
  exact ⟨a, δ', hside', hM⟩

end Assembly

end InteractingSLE.Sec7.PhaseClause
