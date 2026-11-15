/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5WallSplit
import InteractingSLE.Spec.Supplement.SB2FinCompP38

/-!
# R.5's reference heights at the pocket boundary: the same-time step per prime end (ruling R86a)

Packet PROVE-R5-WALL (second round). R5-SAMETIME's same-time comparison (`R5Same.ae_tendsto_unionMean_hull`) compares
the mean of `E ∪ K_s` (`E` the pocket exterior, `K_s` the counterflow hull at an original time `s`) with the ambient
coupling's reading at points `z₀ ∈ K_s` near which `E ⊆ K_s`; at a point of the pocket wall visited by the counterflow
that fails (`E` reaches `z₀` from outside the pocket). Here the comparison is made **per prime end** with the
component form of Proposition 3.8 (`Theorem14.SB.FinRel.ae_tendsto_sub_of_union_comp`, ruling R84): along the
`E`-free components of `(ℍ ∖ K_s) ∩ B(z₀, r)` (`freeNear E K_s z₀ r`).

* **`ae_tendsto_unionMean_hull_comp`**: the comparison `v + 𝔥₀ + χ arg f_s′ − G_s ∘ f_s → 0` along `freeNear`;
* **`ae_tendsto_harmRep_unionMean_comp`**: the reference height in the ambient lift along an approach that eventually
  stays in `freeNear`;
* **`ae_tendsto_harmRep_ref_comp`**, **`ae_tendsto_harmRep_refHull_comp`**: the R.7 instances (pocket exterior and the
  counterflow hulls at the rational original times; walls' data of `R5Phase.pocketStopUnionLaw_ref`), at every
  point of the hull — inside the pocket or on its walls.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open QuantumZipper (H fwdMap fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec7.R5Wall

open LocalSets WholeField Aux119Heights R5Same
open Theorem14.SB.FinRel (freeNear freeNear_subset ae_tendsto_sub_of_union_comp)

section Hull

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The same-time comparison per prime end**: for a local, field-determined random set `E` and every local-set mean
`g` of `E ∪ K_s`, almost surely every harmonic representative `v` of `g` satisfies
`v + 𝔥₀ + χ arg f_s′ − G_s ∘ f_s → 0` at every `z₀ ∈ K_s` along the `E`-free components of `(ℍ ∖ K_s) ∩ B(z₀, r)`. -/
theorem ae_tendsto_unionMean_hull_comp (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
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
      ∀ z₀ ∈ K ω, ∀ r > 0,
        Tendsto (fun z => v z + u₀ z + chiC κ * (logDerivFwd (fun r : ℝ => W r.toNNReal ω) s z).im -
          GE (fwdMap (fun r : ℝ => W r.toNNReal ω) s z)) (𝓝[freeNear (E ω) (K ω) z₀ r] z₀) (𝓝 0) := by
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
  filter_upwards [ae_tendsto_sub_of_union_comp hh0 hEm hKm hci hEl hKl hunb hg hg₂,
    ae_eqOn_hullMean hC hκ hu₀ hX s hsζ hKm hKeq hg₂, hg₂.2.1, hKl.2.1, hEl.2.1]
    with ω ⟨u, hu, hurep, hulim⟩ hHM hg₂ω ⟨_, hKo⟩ ⟨_, hEo⟩ GE hGE v hv hrep z₀ hz₀ r hr
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
  refine (hulim z₀ (Or.inl hz₀) r hr).congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
  have hz' := freeNear_subset hz
  have h1 := huv hz'
  have h2 := hE (hUK hz')
  simp only at h1 h2 ⊢
  rw [h1, ← h2]
  ring

/-- **R.5's reference height in the ambient lift per prime end**: almost surely, along any approach `F` (within `ℍ` at
`ξ`) to a point `z₀ ∈ K_s` that eventually stays in an `E`-free component of `(ℍ ∖ K_s) ∩ B(z₀, r)`, along which
`f_s ∘ F` tends to a real point `x` off the jump set at time `s`, the canonical harmonic representative of the mean of
`E ∪ K_s`, plus `𝔥₀` and `χ arg f_s′`, tends to the force data `β_s(x)`. -/
theorem ae_tendsto_harmRep_unionMean_comp (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (s : ℝ≥0) (hsζ : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζ ω)
    {K : Ω → Set ℂ} (hKm : Measurable[mΩ, hittingSigma] K)
    (hKeq : ∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => W r.toNNReal ω) s)
    {E : Ω → Set ℂ} (hEm : Measurable[mΩ, hittingSigma] E)
    (hEd : MeasurableSpace.comap E hittingSigma ≤
      aeSigma (MeasurableSpace.comap (centredField h u₀) inferInstance) P)
    (hEl : IsLocalSet E (centredField h u₀) P)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean (fun ω => E ω ∪ K ω) (centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ K ω, ∀ r > 0, ∀ (F : ℂ → ℂ) (ξ : ℂ) (x : ℝ),
      x ∉ forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω) →
      Tendsto F (𝓝[H] ξ) (𝓝 z₀) → (∀ᶠ y in 𝓝[H] ξ, F y ∈ freeNear (E ω) (K ω) z₀ r) →
      Tendsto (fun y => fwdMap (fun r : ℝ => W r.toNNReal ω) s (F y)) (𝓝[H] ξ) (𝓝 (x : ℂ)) →
      Tendsto (fun y => harmRep (g ω) (H \ (E ω ∪ K ω)) (F y) + u₀ (F y) +
          chiC κ * (logDerivFwd (fun r : ℝ => W r.toNNReal ω) s (F y)).im) (𝓝[H] ξ)
        (𝓝 (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω) x)) := by
  filter_upwards [ae_tendsto_unionMean_hull_comp hC hκ hu₀ hX s hsζ hKm hKeq hEm hEd hEl hg, hg.2.1,
    hC.1.2.2.2.2, hsζ, hKeq] with ω hcmp hgω hp hlt hKω z₀ hz₀ r hr F ξ x hx hF hFU hfF
  have hext := isBoundedHarmonicExtension_wordExt κ ρL ρR VL VR W s ω
  obtain ⟨hv, hrep⟩ := harmRep_spec hgω
  have hcmp' := hcmp _ hext _ hv hrep z₀ hz₀ r hr
  have hUK : freeNear (E ω) (K ω) z₀ r ⊆ H \ fwdHull (fun r : ℝ => W r.toNNReal ω) s := fun z hz =>
    hKω ▸ sdiff_subset_sdiff_right subset_union_right (freeNear_subset hz)
  have hfF' : Tendsto (fun y => fwdMap (fun r : ℝ => W r.toNNReal ω) s (F y)) (𝓝[H] ξ) (𝓝[H] (x : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hfF, hFU.mono fun y hy =>
      StripSideHeightProb.mapsTo_fwdMap_rpath hp.2.2.2.1 hlt (hUK hy)⟩
  exact tendsto_height_of_comparison hcmp' hF hFU hfF' (hext.2.2 x hx)

end Hull

section R7

open PocketStopField PocketStopWalls PocketStopWallsFin PocketCoupling PocketStop PocketWordPerQ PocketCoord
  PocketJordan PocketTraversal Lemma71C R5Phase PocketUnionPt

variable {Ω : Type*} {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ} {u₀ : ℂ → ℝ}
  {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {u₀' : ℂ → ℝ} {R L : Ω → ℝ≥0 → ℂ}

/-- **The reference height at time `s` per prime end** (R.7 test; walls' data of `R5Phase.pocketStopUnionLaw_ref`):
almost surely on the test, at every point `z₀` of the hull `K_s` (inside the pocket or on its walls), along every
approach that eventually stays in a component of `(ℍ ∖ K_s) ∩ B(z₀, r)` missing the pocket exterior and whose image
under `f_s` tends to a real non-jump point `x`, the reference mean read in the ambient lift tends to `β_s(x)`. -/
theorem ae_tendsto_harmRep_ref_comp
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ')
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {G A : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (s : ℝ≥0) {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0)
      (centredField h'' u₀') P g) :
    ∀ᵐ ω ∂P, ω ∈ A → ∀ z₀ ∈ regHull W' ζ' s ω, ∀ ρ > 0, ∀ (F : ℂ → ℂ) (ξ : ℂ) (x : ℝ),
      x ∉ forceJumpSet (fun i => VL i s ω - W' s ω) (fun i => VR i s ω - W' s ω) →
      Tendsto F (𝓝[H] ξ) (𝓝 z₀) →
      (∀ᶠ y in 𝓝[H] ξ, F y ∈ freeNear (pocketExt A γ (fun ω => cfPocket (R ω) (L ω) r) ω)
        (regHull W' ζ' s ω) z₀ ρ) →
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) s (F y)) (𝓝[H] ξ) (𝓝 (x : ℂ)) →
      Tendsto (fun y => harmRep (g ω) (H \ liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0 ω)
          (F y) + u₀' (F y) + chiC κ' * (logDerivFwd (fun t : ℝ => W' t.toNNReal ω) s (F y)).im) (𝓝[H] ξ)
        (𝓝 (forceBoundaryData κ' ρL ρR (fun i => VL i s ω - W' s ω) (fun i => VR i s ω - W' s ω) x)) := by
  obtain ⟨hEm, hEd, hEl⟩ := pocketExt_facts hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL
    hlocR hlocL hGm hG hA hAG hγ
  have hKH : ∀ ω, regHull W' ζ' s ω ⊆ H := fun ω z hz => hz.1
  have hunion : (fun ω => pocketExt A γ (fun ω => cfPocket (R ω) (L ω) r) ω ∪ regHull W' ζ' s ω) =
      liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0 := funext (pocketExt_union hKH)
  have hg' : IsLocalSetMean (fun ω => pocketExt A γ (fun ω => cfPocket (R ω) (L ω) r) ω ∪ regHull W' ζ' s ω)
      (centredField h'' u₀') P g := by
    rw [hunion]
    exact hg
  have hKm : Measurable[mΩ, hittingSigma] (regHull W' ζ' s) :=
    measurable_regHull (T := fun _ => s) hX measurable_const
  have hsζ : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζ' ω := by
    filter_upwards [hζ] with ω hω
    rw [hω]
    exact ENNReal.coe_lt_top
  have hKeq : ∀ᵐ ω ∂P, regHull W' ζ' s ω = fwdHull (fun t : ℝ => W' t.toNNReal ω) s := by
    filter_upwards [hζ, hC.1.2.2.2.2] with ω hζω hp
    have hcont : Continuous fun t => W' t ω := by
      rw [← continuousOn_univ]
      refine hp.2.2.2.1.mono fun t _ => ?_
      show ((t : ℝ≥0∞)) < ζ' ω
      rw [hζω]
      exact ENNReal.coe_lt_top
    exact regHull_eq hcont hζω s
  filter_upwards [ae_tendsto_harmRep_unionMean_comp hC hκ' hu₀' hX s hsζ hKm hKeq hEm hEd hEl hg']
    with ω hω _ z₀ hz₀ ρ hρ F ξ x hx hF hFU hfF
  have he := pocketExt_union (A := A) (γ := γ) (C := fun ω => cfPocket (R ω) (L ω) r) hKH ω
  rw [← he]
  exact hω z₀ hz₀ ρ hρ F ξ x hx hF hFU hfF

/-- **`ae_tendsto_harmRep_ref_comp` for R.5's whole countable reference family** (`R5Phase.refHull`), on one
event. -/
theorem ae_tendsto_harmRep_refHull_comp
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ')
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {G A : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) {gB : ℕ → Ω → DistOn upperHalfPlaneOpens}
    (hgB : ∀ i, IsLocalSetMean (liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0)
      (centredField h'' u₀') P (gB i)) :
    ∀ᵐ ω ∂P, ω ∈ A → ∀ i : ℕ, let s := Wire.Current.SideTest.rationalOriginalTime i;
      ∀ z₀ ∈ refHull W' ζ' i ω, ∀ ρ > 0, ∀ (F : ℂ → ℂ) (ξ : ℂ) (x : ℝ),
      x ∉ forceJumpSet (fun j => VL j s ω - W' s ω) (fun j => VR j s ω - W' s ω) →
      Tendsto F (𝓝[H] ξ) (𝓝 z₀) →
      (∀ᶠ y in 𝓝[H] ξ, F y ∈ freeNear (pocketExt A γ (fun ω => cfPocket (R ω) (L ω) r) ω)
        (refHull W' ζ' i ω) z₀ ρ) →
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) s (F y)) (𝓝[H] ξ) (𝓝 (x : ℂ)) →
      Tendsto (fun y => harmRep (gB i ω) (H \ liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0 ω)
          (F y) + u₀' (F y) + chiC κ' * (logDerivFwd (fun t : ℝ => W' t.toNNReal ω) s (F y)).im) (𝓝[H] ξ)
        (𝓝 (forceBoundaryData κ' ρL ρR (fun j => VL j s ω - W' s ω) (fun j => VR j s ω - W' s ω) x)) := by
  have hall := ae_all_iff.2 fun i => ae_tendsto_harmRep_ref_comp hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0
    hL0 hRm hLm hdetR hdetL hlocR hlocL hGm hG hA hAG hγ (Wire.Current.SideTest.rationalOriginalTime i) (hgB i)
  filter_upwards [hall] with ω hω hωA i
  exact hω i hωA

end R7

end InteractingSLE.Sec7.R5Wall
