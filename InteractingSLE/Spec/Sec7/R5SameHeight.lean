/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideHeightHull
import InteractingSLE.Spec.Sec7.Aux119Heights
import InteractingSLE.Spec.Sec7.StripSideHeightProbSide
import InteractingSLE.GFF.LocalSets.Prop38
import InteractingSLE.Spec.Sec6.CondMeanStop
import InteractingSLE.Spec.Sec6.Prop61Mean
import InteractingSLE.Spec.Sec5.GlueCondTopo
import InteractingSLE.Spec.Sec5.CrossRestartKernelUnionMean
import InteractingSLE.Foundations.Loewner.Capacity
import InteractingSLE.Spec.Sec7.StripSysField
import InteractingSLE.Spec.Coupling.Locality11Gauss
import InteractingSLE.Impl.ForceBoundaryData

/-!
# Lemma R.5's same-time step: a reference at an original time keeps the ambient heights at the hull

Packet PROVE-R5-SAMETIME (Theorem 1.2's R.5, part (b) of `planning/handoffs/PROVE-R5-PHASE.md`, "Analysis of the open
clauses"). Lemma R.5's old reference at an original time `s` is `B ∪ R_s`: a set `B` determined by the field (the
pocket exterior, read from the walls) together with the counterflow hull `R_s = K_s` at the deterministic time `s`
(`source/spec/p433-480.md` L1013–L1020, p. 475). Its boundary heights near hull points inside the pocket are the
ambient coupling's heights at time `s`:

* `ae_eqOn_hullMean` (**ambient heights**): every harmonic representative `v` of a local-set mean of the hull `K_s`
  (for the centred field `h − 𝔥₀`) satisfies `v + 𝔥₀ = G_s ∘ f_s − χ arg f_s′` off `K_s`, for every bounded harmonic
  extension `G_s` of the force data at the centred positions at time `s` (Theorem 1.1's coupling at the constant
  stopping time `s`; `SideHeight.ae_apply_eq_of_isLocalSetMean_flowHull`);
* **`ae_tendsto_unionMean_hull`** (**the same-time comparison**): for a local, field-determined random set `B` and
  every local-set mean `g` of `B ∪ K_s`, almost surely every harmonic representative `v` of `g` satisfies
  `v + 𝔥₀ + χ arg f_s′ − G_s ∘ f_s → 0` at every point `z₀ ∈ K_s` near which `B ⊆ K_s` (Proposition 3.8,
  `LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union`; the conditional independence of `B` and `K_s` given the field is
  automatic because `B` is field-determined, `Sec6.condIndepEv_of_le_aeSigma`);
* `tendsto_unionMean_chart` (pathwise corollary): along any approach `F` to such a point whose image under `f_s`
  tends to a real non-jump point `x`, `v + 𝔥₀ + χ arg f_s′` tends to the force data `β_s(x)` — R.5's reference height in
  the ambient lift.

The comparison is physical (in the whole neighbourhood of `z₀` in `ℍ ∖ (B ∪ K_s)`), so it holds at every prime end over
`z₀`. No enlarged stop and no old-chart increment law is needed for this step: the reference and the ambient hull are
read at the same deterministic time. Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`,
`Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open QuantumZipper (H fwdMap fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec7.R5Same

open LocalSets WholeField Aux119Heights

section Hull

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- The force-word jump set is finite. -/
theorem forceJumpSet_finite' {m n : ℕ} (vL : Fin m → ℝ) (vR : Fin n → ℝ) : (forceJumpSet vL vR).Finite :=
  ((Set.finite_range vL).union (Set.finite_range vR)).insert 0

/-- A bounded harmonic extension of the force data at the centred positions at time `s` (chosen). -/
def wordExt (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (W : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℂ → ℝ :=
  (StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω)
    (fun i => VR i s ω - W s ω)).choose

omit mΩ in
theorem isBoundedHarmonicExtension_wordExt (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (W : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) :
    IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (wordExt κ ρL ρR VL VR W s ω) :=
  (StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω)
    (fun i => VR i s ω - W s ω)).choose_spec

omit [IsProbabilityMeasure P] in
/-- **The hull is a local set of the centred field** at a deterministic time before the lifetime. -/
theorem isLocalSet_hull (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (s : ℝ≥0) (hsζ : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζ ω)
    {K : Ω → Set ℂ} (hKeq : ∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => W r.toNNReal ω) s) :
    IsLocalSet K (centredField h u₀) P := by
  have htr : ∀ ω, IsTranslateAddConst 0 0 (h ω) (h ω) := fun ω => by
    simpa using StripSysField.isTranslateAddConst_zero_self (h ω) 0
  have hloc := SideHeight.isLocalSet_flowHull hC htr hu₀.1 hu₀ (fun z _ => by simp) hX
    (isStoppingTime_const (drivingFiltration P hX) s)
    (by filter_upwards [hsζ] with ω hω using hω)
  refine Coupling.IsLocalSet.congr_set hloc ?_
  filter_upwards [hKeq] with ω hω
  rw [hω]
  simp only [Complex.ofReal_zero, add_zero, image_id']
  rfl

/-- **Ambient heights at a deterministic time** (Theorem 1.1's coupling at the constant stopping time `s`): almost
surely every harmonic representative `v` of a local-set mean of the hull `K = K_s` for the centred field satisfies
`v + 𝔥₀ + χ arg f_s′ = G ∘ f_s` off `K`, for every bounded harmonic extension `G` of the force data at the centred
positions at time `s`. -/
theorem ae_eqOn_hullMean (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (s : ℝ≥0) (hsζ : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζ ω)
    {K : Ω → Set ℂ} (hKm : Measurable[mΩ, hittingSigma] K)
    (hKeq : ∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => W r.toNNReal ω) s)
    {g₂ : Ω → DistOn upperHalfPlaneOpens} (hg₂ : IsLocalSetMean K (centredField h u₀) P g₂) :
    ∀ᵐ ω ∂P, ∀ GE : ℂ → ℝ, IsBoundedHarmonicExtension
        (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
        (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) GE →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ K ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ K ω → g₂ ω φ = ∫ z, v z * φ z) →
      EqOn (fun z => v z + u₀ z + chiC κ * (logDerivFwd (fun r : ℝ => W r.toNNReal ω) s z).im)
        (fun z => GE (fwdMap (fun r : ℝ => W r.toNNReal ω) s z)) (H \ K ω) := by
  have hh0 := isZeroBoundaryGFF_centredField hC hu₀
  have htr : ∀ ω, IsTranslateAddConst 0 0 (h ω) (h ω) := fun ω => by
    simpa using StripSysField.isTranslateAddConst_zero_self (h ω) 0
  have hmean := SideHeight.ae_apply_eq_of_isLocalSetMean_flowHull hC hκ htr hh0 hu₀.1 hu₀ (fun z _ => by simp) hX
    (isStoppingTime_const (drivingFiltration P hX) s) (by filter_upwards [hsζ] with ω hω using hω) hKm
    (by
      filter_upwards [hKeq] with ω hω
      rw [hω]
      simp only [Complex.ofReal_zero, add_zero, image_id']
      rfl) hg₂ (u := fun ω => wordExt κ ρL ρR VL VR W s ω)
    (fun ω => isBoundedHarmonicExtension_wordExt κ ρL ρR VL VR W s ω)
  filter_upwards [hmean, hC.1.2.2.2.2, hsζ, hKeq, (isLocalSet_hull hC hu₀ hX s hsζ hKeq).2.1]
    with ω hmω hp hlt hKω ⟨_, hKo⟩ GE hGE v hv hrep
  have hwc : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := hp.2.2.2.1
  have hext := isBoundedHarmonicExtension_wordExt κ ρL ρR VL VR W s ω
  set Wω : ℝ → ℝ := fun r : ℝ => W r.toNNReal ω with hWω
  have hcm := SideHeight.harmonicOnNhd_couplingMean_rpath (κ := κ) hwc hlt hext.1
  have hm : InnerProductSpace.HarmonicOnNhd
      (fun z => couplingMean κ Wω s (wordExt κ ρL ρR VL VR W s ω) z - u₀ z) (H \ K ω) := by
    rw [hKω]
    exact fun z hz => (hcm z hz).sub (hu₀.1 z hz.1)
  have hcont : ∀ {U : Set ℂ} {w : ℂ → ℝ}, InnerProductSpace.HarmonicOnNhd w U →
      ContinuousOn w U := fun hw z hz => (hw z hz).1.continuousAt.continuousWithinAt
  have hvm : EqOn v (fun z => couplingMean κ Wω s (wordExt κ ρL ρR VL VR W s ω) z - u₀ z) (H \ K ω) := by
    refine Sec6.eqOn_of_integral_mul_eq hKo sdiff_subset hv hm fun φ hφ => ?_
    rw [← hrep φ hφ, hmω φ hφ]
    congr 1
    funext z
    simp only [WithTop.untopD_coe, Complex.ofReal_zero, sub_zero]
  have hGE' : EqOn GE (wordExt κ ρL ρR VL VR W s ω) H :=
    Impl.eqOn_of_isBoundedHarmonicExtension (forceJumpSet_finite' _ _) hext hGE
  intro z hz
  have hzK : z ∈ H \ fwdHull Wω s := hKω ▸ hz
  have hfz := StripSideHeightProb.mapsTo_fwdMap_rpath hwc hlt hzK
  simp only
  rw [hvm hz, hGE' hfz]
  simp only [couplingMean]
  ring

/-- **The same-time comparison (Proposition 3.8)**: for a local random set `E` determined by the field and every
local-set mean `g` of `E ∪ K` (`K` the hull at the deterministic time `s`), almost surely every harmonic
representative `v` of `g` satisfies `v + 𝔥₀ + χ arg f_s′ − G ∘ f_s → 0` at every point `z₀ ∈ K` near which `E ⊆ K`,
in the whole neighbourhood of `z₀` in `ℍ ∖ (E ∪ K)` (so at every prime end over `z₀`). -/
theorem ae_tendsto_unionMean_hull (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (s : ℝ≥0) (hsζ : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζ ω)
    {K : Ω → Set ℂ} (hKm : Measurable[mΩ, hittingSigma] K)
    (hKeq : ∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => W r.toNNReal ω) s)
    {E : Ω → Set ℂ} (hEm : Measurable[mΩ, hittingSigma] E)
    (hEd : MeasurableSpace.comap E hittingSigma ≤
      aeSigma (MeasurableSpace.comap (centredField h u₀) inferInstance) P)
    (hEl : IsLocalSet E (centredField h u₀) P)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean (fun ω => E ω ∪ K ω) (centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ∀ GE : ℂ → ℝ, IsBoundedHarmonicExtension
        (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
        (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) GE →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (E ω ∪ K ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (E ω ∪ K ω) → g ω φ = ∫ z, v z * φ z) →
      ∀ z₀ ∈ K ω, (∃ r > 0, E ω ∩ ball z₀ r ⊆ K ω) →
        Tendsto (fun z => v z + u₀ z + chiC κ * (logDerivFwd (fun r : ℝ => W r.toNNReal ω) s z).im -
          GE (fwdMap (fun r : ℝ => W r.toNNReal ω) s z)) (𝓝[H \ (E ω ∪ K ω)] z₀) (𝓝 0) := by
  have hh0 := isZeroBoundaryGFF_centredField hC hu₀
  have hKl := isLocalSet_hull hC hu₀ hX s hsζ hKeq
  obtain ⟨g₂, hg₂⟩ := IsLocalSet.exists_isLocalSetMean hh0 hKm hKl
  have hci : LQGMetric.CondIndepEv (MeasurableSpace.comap (centredField h u₀) inferInstance)
      (MeasurableSpace.comap E hittingSigma) (MeasurableSpace.comap K hittingSigma) P :=
    Sec6.condIndepEv_of_le_aeSigma hh0.measurable.comap_le hKm.comap_le hEd
  have hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (K ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (K ω)) z) := by
    filter_upwards [hKeq, hC.1.2.2.2.2, hsζ] with ω hKω hp hlt
    rw [hKω]
    exact Sec5.GlueCond.not_isBounded_lowerUnion_of_isHPHull
      (Sec5.CrossRestart.isHPHull_fwdHull_rpath hp.2.2.2.1 hlt)
  filter_upwards [IsLocalSetMean.ae_tendsto_sub_of_union hh0 hEm hKm hci hEl hKl hunb hg hg₂,
    ae_eqOn_hullMean hC hκ hu₀ hX s hsζ hKm hKeq hg₂, hg₂.2.1, hKl.2.1, hEl.2.1]
    with ω ⟨u, hu, hurep, hulim⟩ hHM hg₂ω ⟨_, hKo⟩ ⟨_, hEo⟩ GE hGE v hv hrep z₀ hz₀ hball
  obtain ⟨w₂, hw₂, hrep₂⟩ := hg₂ω
  have hUeq : H \ (E ω ∪ K ω) = (H \ E ω) ∩ (H \ K ω) := by
    ext z; simp only [Set.mem_sdiff, mem_union, mem_inter_iff, not_or]; tauto
  have hoU : IsOpen (H \ (E ω ∪ K ω)) := hUeq ▸ hEo.inter hKo
  have hUK : H \ (E ω ∪ K ω) ⊆ H \ K ω := sdiff_subset_sdiff_right subset_union_right
  have hcont : ∀ {U : Set ℂ} {w : ℂ → ℝ}, InnerProductSpace.HarmonicOnNhd w U →
      ContinuousOn w U := fun hw z hz => (hw z hz).1.continuousAt.continuousWithinAt
  have huv : EqOn u (fun z => v z - w₂ z) (H \ (E ω ∪ K ω)) := by
    refine Sec6.eqOn_of_integral_mul_eq hoU sdiff_subset hu
      (hv.sub fun z hz => hw₂ z (hUK hz)) fun φ hφ => ?_
    rw [← hurep φ hφ, hrep φ hφ, hrep₂ φ (hφ.trans hUK),
      ← integral_sub (integrable_mul_test hoU (hcont hv) φ hφ)
        (integrable_mul_test hoU ((hcont hw₂).mono hUK) φ hφ)]
    congr 1; funext z; ring
  have hE := hHM GE hGE w₂ hw₂ hrep₂
  refine (hulim z₀ (Or.inl hz₀) hball).congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
  have h1 := huv hz
  have h2 := hE (hUK hz)
  simp only at h1 h2 ⊢
  rw [h1, ← h2]
  ring

/-- Pathwise composition: a comparison `v + u₀ + χ ℓ − G ∘ f → 0` at `z₀` within `U`, an approach `F` to `z₀` inside `U`
along which `f ∘ F` tends to `x` within `ℍ`, and a boundary limit `b` of `G` at `x` give the limit `b` of
`v + u₀ + χ ℓ` along `F`. -/
theorem tendsto_height_of_comparison {U : Set ℂ} {z₀ x : ℂ} {χ b : ℝ} {v u₀ ℓ G : ℂ → ℝ} {f : ℂ → ℂ}
    (hcmp : Tendsto (fun z => v z + u₀ z + χ * ℓ z - G (f z)) (𝓝[U] z₀) (𝓝 0)) {α : Type*} {l : Filter α}
    {F : α → ℂ} (hF : Tendsto F l (𝓝 z₀)) (hFU : ∀ᶠ y in l, F y ∈ U) (hfF : Tendsto (fun y => f (F y)) l (𝓝[H] x))
    (hG : Tendsto G (𝓝[H] x) (𝓝 b)) :
    Tendsto (fun y => v (F y) + u₀ (F y) + χ * ℓ (F y)) l (𝓝 b) := by
  have h1 := hcmp.comp (tendsto_nhdsWithin_iff.2 ⟨hF, hFU⟩)
  have h2 := hG.comp hfF
  have h3 := h1.add h2
  rw [zero_add] at h3
  refine h3.congr fun y => ?_
  simp only [Function.comp_apply]
  ring

/-- **R.5's reference height in the ambient lift** (the form of the cover's height clause): almost surely, along any
approach `F` (within `ℍ` at `ξ`) to a point `z₀ ∈ K` near which `E ⊆ K`, staying in `ℍ ∖ (E ∪ K)`, along which
`f_s ∘ F` tends to a real point `x` off the jump set at time `s`, the canonical harmonic representative of the mean of
`E ∪ K`, plus `𝔥₀` and `χ arg f_s′`, tends to the force data `β_s(x)` at the centred positions at time `s`. -/
theorem ae_tendsto_harmRep_unionMean (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (s : ℝ≥0) (hsζ : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζ ω)
    {K : Ω → Set ℂ} (hKm : Measurable[mΩ, hittingSigma] K)
    (hKeq : ∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => W r.toNNReal ω) s)
    {E : Ω → Set ℂ} (hEm : Measurable[mΩ, hittingSigma] E)
    (hEd : MeasurableSpace.comap E hittingSigma ≤
      aeSigma (MeasurableSpace.comap (centredField h u₀) inferInstance) P)
    (hEl : IsLocalSet E (centredField h u₀) P)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean (fun ω => E ω ∪ K ω) (centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ K ω, (∃ r > 0, E ω ∩ ball z₀ r ⊆ K ω) → ∀ (F : ℂ → ℂ) (ξ : ℂ) (x : ℝ),
      x ∉ forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω) →
      Tendsto F (𝓝[H] ξ) (𝓝 z₀) → (∀ᶠ y in 𝓝[H] ξ, F y ∈ H \ (E ω ∪ K ω)) →
      Tendsto (fun y => fwdMap (fun r : ℝ => W r.toNNReal ω) s (F y)) (𝓝[H] ξ) (𝓝 (x : ℂ)) →
      Tendsto (fun y => harmRep (g ω) (H \ (E ω ∪ K ω)) (F y) + u₀ (F y) +
          chiC κ * (logDerivFwd (fun r : ℝ => W r.toNNReal ω) s (F y)).im) (𝓝[H] ξ)
        (𝓝 (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω) x)) := by
  filter_upwards [ae_tendsto_unionMean_hull hC hκ hu₀ hX s hsζ hKm hKeq hEm hEd hEl hg, hg.2.1,
    hC.1.2.2.2.2, hsζ, hKeq] with ω hcmp hgω hp hlt hKω z₀ hz₀ hball F ξ x hx hF hFU hfF
  have hext := isBoundedHarmonicExtension_wordExt κ ρL ρR VL VR W s ω
  obtain ⟨hv, hrep⟩ := harmRep_spec hgω
  have hcmp' := hcmp _ hext _ hv hrep z₀ hz₀ hball
  have hUK : H \ (E ω ∪ K ω) ⊆ H \ fwdHull (fun r : ℝ => W r.toNNReal ω) s :=
    hKω ▸ sdiff_subset_sdiff_right subset_union_right
  have hfF' : Tendsto (fun y => fwdMap (fun r : ℝ => W r.toNNReal ω) s (F y)) (𝓝[H] ξ) (𝓝[H] (x : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hfF, hFU.mono fun y hy =>
      StripSideHeightProb.mapsTo_fwdMap_rpath hp.2.2.2.1 hlt (hUK hy)⟩
  exact tendsto_height_of_comparison hcmp' hF hFU hfF' (hext.2.2 x hx)

end Hull

end InteractingSLE.Sec7.R5Same
