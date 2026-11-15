/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideHeight
import InteractingSLE.Spec.Sec7.RS133Prob

/-!
# A flow line's side heights from Lemma 6.2's inputs (no field determination of the flow line)

Packet PROVE-STRIPSYS25. Specification §7.2, proof of Aux. lemma 70 (p. 275: "The single-path coupling gives, in the
`gᵢ` coordinate, height `λ − θ₁χ` on the right side of the first trace and height `−λ − θ₂χ` on the left side of the
second"), used by Aux. lemma 119's proof (p. 386: "the own height `λ − θ_Lχ` on a right side of the left path, and
`−λ − θ_Rχ` on a left side of the right path") for the walls' pieces before their angle change.

PROVE-SIDEHEIGHT's `SideHeight.singlePathSideHeightStatement_of_inputs` derives the side heights of a flow line from
Lemma 7.5 (field determination, `Theorem15.Lemma75Statement`) and Aux. 56, used only to produce a version of the flow
line with Lemma 6.2's inputs (continuous, measurable, field-determined at fixed times, history-sensitively local),
which makes the stopped range a field-determined local set. **Here that version is given** (`hηcc … hloc`), so the
side heights follow from the frozen coupling of the flow line alone: no Lemma 7.5, no Theorem 1.2/1.3 (R43, R48). The
rest of the proof is PROVE-SIDEHEIGHT's: (1) on `{q < ζ}` the range mean is the coupling mean off the filling
(`SideHeight.ae_apply_eq_flowMean_of_range`); (2) harmonic representatives agree there; (3) the coupling mean has the
side values `±λ` (`SideHeight.tendsto_comp_fwdMap_of_pos/neg`).

## Main results

* **`ae_hasSideHeights_of_isFlowLine`**: almost surely on `{q < ζ}`, every harmonic representative of the mean of the
  stopped range has the side heights of angle `θ` (`StripGeom.HasSideHeights`) at every trace point `η(t₀) ∈ ℍ`,
  `t₀ < q`, at the stop `q`, for the flow line from `0`.

Conditional helper; it replaces no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Aux119Heights

open QuantumZipper (H fwdMap fwdHull)
open LQGMetric (DistOn TestOn)
open LocalSets Sec6 SideHeight

/-- **A flow line's side heights from Lemma 6.2's inputs of a version** (see the module docstring). For the angle-`θ`
flow line `η` from `0` of the GFF `h` with boundary data `b` (`0 < κ < 4`), its driving function `W`, a bounded
harmonic extension `u₀` of `b`, a version `ηc` of `η` on `[0, q] ∩ [0, ζ)` with Lemma 6.2's inputs for the centred
field `h − u₀`, and a version `g` of the local-set mean of `ηc([0, q]) ∩ ℍ`: almost surely on `{q < ζ}`, for every
harmonic representative `v` of `g` and every trace point `η(t₀) ∈ ℍ`, `t₀ < q`, the side heights `±λ − θχ` hold at
`η(t₀)` at the stop `q`. -/
theorem ae_hasSideHeights_of_isFlowLine {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps 0 θ P h η ζ) {W : ℝ≥0 → Ω → ℝ}
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η ω t - ((0 : ℝ) : ℂ)))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {ηc : Ω → ℝ≥0 → ℂ}
    (hηcc : ∀ ω, Continuous (ηc ω)) (hηc0 : ∀ ω, ηc ω 0 = 0) (hηcm : ∀ t, Measurable fun ω => ηc ω t)
    (hdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => ηc ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    (hloc : Sec6.IsEntranceHistoryLocal ηc (WholeField.centredField h u₀) P) (q : ℝ≥0)
    (hηce : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ q → (t : ℝ≥0∞) < ζ ω → ηc ω t = η ω t)
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => ηc ω '' Icc 0 q ∩ H) (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ ω → ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (ηc ω '' Icc 0 q ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (ηc ω '' Icc 0 q ∩ H) → g ω φ = ∫ z, v z * φ z) →
      ∀ t₀ : ℝ≥0, t₀ < q → η ω t₀ ∈ H →
        StripGeom.HasSideHeights κ θ (η ω) 0 (fun t => W t ω) q (η ω t₀) v u₀ := by
  classical
  obtain ⟨h', 𝓕, W', VL, VR, B, htrans, hC, htr'⟩ := id hη
  obtain ⟨u₀', hu₀'⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ (flowLineRhoL κ b jumps 0 θ)
    (flowLineRhoR κ b jumps 0 θ) (flowLineXL b jumps 0) (flowLineXR b jumps 0)
  have hrel := Exist.eqOn_flowLine_harmonicExtension hκ hb 0 θ hu₀ hu₀'
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨hX, -⟩ := hC.2.2.2
  -- the stopped range of the version: a field-determined local set (Lemma 6.2)
  set A₁ : Ω → Set ℂ := fun ω => ηc ω '' Icc 0 q ∩ H with hA₁_def
  obtain ⟨hA₁loc, hA₁det⟩ := RS133.isLocalSet_range_and_aeDetermined hh0 hηcc hηc0 hηcm hdet hloc q
  have hA₁m : Measurable[_, hittingSigma] A₁ := StripMark.measurable_range hηcc hηcm q
  have hA₁b : ∀ ω, Bornology.IsBounded (A₁ ω) := fun ω =>
    ((isCompact_Icc.image (hηcc ω)).isBounded).subset inter_subset_left
  -- the range is the stopped range of the flow line on `{q < ζ}`
  have hA₁q : ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ ω → A₁ ω = η ω '' Icc 0 q ∩ H := by
    filter_upwards [hηce] with ω hce hq
    show ηc ω '' Icc 0 q ∩ H = η ω '' Icc 0 q ∩ H
    rw [image_congr fun t ht => hce t ht.2 ((ENNReal.coe_le_coe.2 ht.2).trans_lt hq)]
  -- every earlier hull lies in the filling of the range
  have hA₁fill : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ q → (t : ℝ≥0∞) < ζ ω →
      (fun z : ℂ => z + ((0 : ℝ) : ℂ)) '' fwdHull (fun s : ℝ => W' s.toNNReal ω) t ⊆ fillH (A₁ ω) := by
    filter_upwards [htr', hηce] with ω htrω hce t htq htζ
    rw [fwdHull_eq_fillH_of_isGeneratingTrace htrω htζ, ← Restart.fillH_image_add_real,
      Restart.image_add_real_eq, hA₁_def, fillH_inter_H]
    refine fillH_mono ?_
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨s, ⟨hs.1, hs.2.trans htq⟩, ?_⟩
    exact hce s (hs.2.trans htq) ((ENNReal.coe_le_coe.2 hs.2).trans_lt htζ)
  -- the force data at `q`
  choose u hu using fun ω => Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ (flowLineRhoL κ b jumps 0 θ)
    (flowLineRhoR κ b jumps 0 θ) (fun i => VL i q ω - W' q ω) (fun i => VR i q ω - W' q ω)
  have hmain := ae_apply_eq_flowMean_of_range hC hκ htrans hh0 hu₀.1 hu₀' hrel hX htr' hA₁m
    (fun ω => inter_subset_right) hA₁b hA₁loc hA₁det hA₁q hA₁fill hg hu
  filter_upwards [hmain, htr, htr', hC.1.2.2.2.2, hA₁q, hA₁fill] with ω hmω htrω htr'ω hp h1 hfill hq v hv hrep
    t₀ _ hη₀ F hFne hFle y hy
  have := hFne
  set χ := QuantumZipper.chiC κ with hχ
  set x : ℝ := 0 with hx
  -- the unbounded part and the identification of `v`
  set U := H \ fillH (A₁ ω) with hU
  have hUo : IsOpen U := isOpen_H_diff_fillH (hA₁b ω)
  have hUA : U ⊆ H \ A₁ ω := fun z hz => ⟨hz.1, fun h => hz.2 (subset_fillH inter_subset_right h)⟩
  set M : ℂ → ℝ := fun z => couplingMean κ (fun s : ℝ => W' s.toNNReal ω) q (u ω) (z - x) - θ * χ - u₀ z with hM
  have hKU : U ⊆ H \ (fun z : ℂ => z + x) '' fwdHull (fun s : ℝ => W' s.toNNReal ω) q := fun z hz =>
    ⟨hz.1, fun h => hz.2 (hfill q le_rfl hq h)⟩
  have hMh : InnerProductSpace.HarmonicOnNhd M U :=
    (harmonicOnNhd_flowMean hp.2.2.2.1 hq (hu ω).1 x (θ * χ) hu₀.1).mono hKU
  have hvM : EqOn v M U := eqOn_of_integral_mul_eq hUo (hUA.trans sdiff_subset) (hv.mono hUA) hMh
    fun φ hφ => by rw [← hrep φ (hφ.trans hUA), hmω hq φ hφ]
  have hfillη : fillH (η ω '' Icc 0 q) = fillH (A₁ ω) := by rw [h1 hq, fillH_inter_H]
  have hev : ∀ᶠ z in F, z ∈ U := by
    have := hFle self_mem_nhdsWithin
    rwa [hfillη] at this
  -- the coupling's driver generates the same trace
  have hf := fwdMap_eq_of_isGeneratingTrace htrω htr'ω hq
  have hL := logDerivFwd_eq_of_isGeneratingTrace htrω htr'ω hq
  -- the approach in the centred chart
  set F' : Filter ℂ := Filter.map (fun z => z - x) F with hF'
  have hp0 : η ω t₀ - x ∈ H := show 0 < (η ω t₀ - x).im by simpa using (show 0 < (η ω t₀).im from hη₀)
  have hF'le : F' ≤ 𝓝[H \ fwdHull (fun s : ℝ => W' s.toNNReal ω) q] (η ω t₀ - x) := by
    refine tendsto_nhdsWithin_iff.2 ⟨((continuous_sub_right (x : ℂ)).tendsto _).comp
      (hFle.trans nhdsWithin_le_nhds), hev.mono fun z hz => ?_⟩
    have hz' := hKU hz
    refine ⟨show 0 < (z - x).im by simpa using (show 0 < z.im from hz'.1), fun hK => hz'.2 ⟨z - x, hK, by ring⟩⟩
  have hy' : Tendsto (fwdMap (fun s : ℝ => W' s.toNNReal ω) q) F' (𝓝 (y : ℂ)) := by
    rw [← hf]
    exact tendsto_map'_iff.2 hy
  -- the function along `F`
  have hcongr : (fun z => v z + u₀ z + χ * (QuantumZipper.logDerivFwd (fun s : ℝ => W s.toNNReal ω) q (z - x)).im)
      =ᶠ[F] fun z => u ω (fwdMap (fun s : ℝ => W' s.toNNReal ω) q (z - x)) - θ * χ := by
    filter_upwards [hev] with z hz
    rw [hvM hz, hM, hL]
    simp only [couplingMean]
    ring
  refine ⟨fun hy0 => ?_, fun hy0 => ?_⟩
  · have hlim := tendsto_comp_fwdMap_of_pos hp htr'ω hq (hu ω) hp0 hF'le hy' hy0
    have hlim' : Tendsto (fun z => u ω (fwdMap (fun s : ℝ => W' s.toNNReal ω) q (z - x))) F (𝓝 (sleLambda κ)) :=
      tendsto_map'_iff.1 hlim
    exact (hlim'.sub_const (θ * χ)).congr' hcongr.symm
  · have hlim := tendsto_comp_fwdMap_of_neg hp htr'ω hq (hu ω) hp0 hF'le hy' hy0
    have hlim' : Tendsto (fun z => u ω (fwdMap (fun s : ℝ => W' s.toNNReal ω) q (z - x))) F
        (𝓝 (-sleLambda κ)) :=
      tendsto_map'_iff.1 hlim
    exact (hlim'.sub_const (θ * χ)).congr' hcongr.symm

/-- **Side heights depend only on the prefix and its driver up to the stop**: they transfer between two curves that
agree on `[0, q]` with drivers that agree on `[0, q]` (for instance from a flow line to a wall whose first piece it
is). -/
theorem hasSideHeights_congr {κ θ : ℝ} {α α' : ℝ≥0 → ℂ} {x : ℝ} {W W' : ℝ≥0 → ℝ} {q : ℝ≥0} {z₀ : ℂ}
    {v u₀ : ℂ → ℝ} (hα : ∀ t, t ≤ q → α t = α' t) (hW : ∀ t, t ≤ q → W t = W' t)
    (h : StripGeom.HasSideHeights κ θ α x W q z₀ v u₀) : StripGeom.HasSideHeights κ θ α' x W' q z₀ v u₀ := by
  have hWr : ∀ r ∈ Icc (0 : ℝ) q, W r.toNNReal = W' r.toNNReal := fun r hr =>
    hW _ (Real.toNNReal_le_iff_le_coe.2 hr.2)
  have hf : fwdMap (fun s : ℝ => W s.toNNReal) q = fwdMap (fun s : ℝ => W' s.toNNReal) q :=
    funext fun _ => fwdMap_eq_of_eqOn q.coe_nonneg hWr
  have hl : QuantumZipper.logDerivFwd (fun s : ℝ => W s.toNNReal) q =
      QuantumZipper.logDerivFwd (fun s : ℝ => W' s.toNNReal) q := by
    funext z
    unfold QuantumZipper.logDerivFwd
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le q.coe_nonneg] at hs
    rw [fwdMap_eq_of_eqOn hs.1 fun r hr => hWr r ⟨hr.1, hr.2.trans hs.2⟩]
  have himg : α '' Icc 0 q = α' '' Icc 0 q := image_congr fun t ht => hα t ht.2
  intro F hF hFle y hy
  rw [← himg] at hFle
  rw [← hf] at hy
  have h' := h F hF hFle y hy
  rw [hl] at h'
  exact h'

/-- A nonnegative rational strictly between two nonnegative reals (Mathlib's `NNReal.lt_iff_exists_rat_btwn`). -/
theorem exists_nnrat_btwn' {a b : ℝ≥0} (h : a < b) : ∃ q : ℚ≥0, a < (q : ℝ≥0) ∧ (q : ℝ≥0) < b := by
  obtain ⟨q, hq0, h1, h2⟩ := (NNReal.lt_iff_exists_rat_btwn a b).1 h
  have e : ((q.toNNRat : ℚ≥0) : ℝ≥0) = Real.toNNReal q := by
    ext
    rw [Real.coe_toNNReal _ (Rat.cast_nonneg.2 hq0)]
    have h3 : (((q.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = ((q.toNNRat : ℚ) : ℝ) := by norm_cast
    rw [h3, Rat.coe_toNNRat q hq0]
  exact ⟨q.toNNRat, e ▸ h1, e ▸ h2⟩

/-- **The side heights of a two-angle wall at rational stops** (the input `hsideL`/`hsideR` of `ae_ownHeights`): if
the wall has the side heights of angle `θ₀` at every point before a rational stop `q ≤ t₀` (its first piece, e.g.
`ae_hasSideHeights_of_isFlowLine` with `hasSideHeights_congr`), and of angle `θ` at every point after its change
time `t₀` before a rational stop `q > t₀` (its second piece, e.g. `RS133.ae_sideHeights_stage`), each almost surely,
then almost surely every wall point `γ(s)`, `s ≠ t₀`, off the other wall has a rational stop `q > s` with the side
heights of the angle of its piece. -/
theorem ae_sideHeights_rat_of_stages {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ ρ : Ω → ℝ≥0 → ℂ}
    (hγ0 : ∀ ω, γ ω 0 = 0) (hρ0 : ∀ ω, ρ ω 0 = 0) (hγH : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, 0 < s → γ ω s ∈ H)
    {g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens} {W : Ω → ℝ≥0 → ℝ} {κ θ₀ θ : ℝ} {u₀ : ℂ → ℝ} {t₀ : ℝ≥0}
    (hst0 : ∀ q : ℚ≥0, (q : ℝ≥0) ≤ t₀ → ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H) →
        g q ω φ = ∫ z, v z * φ z) →
      ∀ s : ℝ≥0, s < q → γ ω s ∈ H → StripGeom.HasSideHeights κ θ₀ (γ ω) 0 (W ω) q (γ ω s) v u₀)
    (hst1 : ∀ q : ℚ≥0, t₀ < (q : ℝ≥0) → ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H) →
        g q ω φ = ∫ z, v z * φ z) →
      ∀ s : ℝ≥0, t₀ < s → s < q → γ ω s ∈ H → StripGeom.HasSideHeights κ θ (γ ω) 0 (W ω) q (γ ω s) v u₀) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0, γ ω s ∉ range (ρ ω) → s ∉ ({t₀} : Set ℝ≥0) → ∃ q : ℚ≥0, s < q ∧
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H)) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H) →
          g q ω φ = ∫ z, v z * φ z) →
        StripGeom.HasSideHeights κ (if s < t₀ then θ₀ else θ) (γ ω) 0 (W ω) q (γ ω s) v u₀ := by
  have h0 : ∀ᵐ ω ∂P, ∀ q : ℚ≥0, (q : ℝ≥0) ≤ t₀ → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H) →
        g q ω φ = ∫ z, v z * φ z) →
      ∀ s : ℝ≥0, s < q → γ ω s ∈ H → StripGeom.HasSideHeights κ θ₀ (γ ω) 0 (W ω) q (γ ω s) v u₀ := by
    refine ae_all_iff.2 fun q => ?_
    by_cases hq : (q : ℝ≥0) ≤ t₀
    · exact (hst0 q hq).mono fun ω hω _ => hω
    · exact Eventually.of_forall fun ω h => absurd h hq
  have h1 : ∀ᵐ ω ∂P, ∀ q : ℚ≥0, t₀ < (q : ℝ≥0) → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H) →
        g q ω φ = ∫ z, v z * φ z) →
      ∀ s : ℝ≥0, t₀ < s → s < q → γ ω s ∈ H → StripGeom.HasSideHeights κ θ (γ ω) 0 (W ω) q (γ ω s) v u₀ := by
    refine ae_all_iff.2 fun q => ?_
    by_cases hq : t₀ < (q : ℝ≥0)
    · exact (hst1 q hq).mono fun ω hω _ => hω
    · exact Eventually.of_forall fun ω h => absurd h hq
  filter_upwards [h0, h1, hγH] with ω hω0 hω1 hωH s hsρ hst
  have hs0 : 0 < s := pos_of_ne_zero fun h => hsρ ⟨0, by rw [h, hγ0, hρ0]⟩
  have hsH := hωH s hs0
  have hst' : s ≠ t₀ := fun h => hst (Set.mem_singleton_iff.2 h)
  rcases lt_or_gt_of_ne hst' with hlt | hgt
  · obtain ⟨q, hsq, hqt⟩ := exists_nnrat_btwn' hlt
    refine ⟨q, hsq, fun v hv hgv => ?_⟩
    simp only [hlt, ↓reduceIte]
    exact hω0 q hqt.le v hv hgv s hsq hsH
  · obtain ⟨q, hsq, -⟩ := exists_nnrat_btwn' (lt_add_one s)
    refine ⟨q, hsq, fun v hv hgv => ?_⟩
    have hn : ¬ s < t₀ := not_lt.2 hgt.le
    simp only [hn, ↓reduceIte]
    exact hω1 q (hgt.trans hsq) v hv hgv s hgt hsq hsH

end InteractingSLE.Sec7.Aux119Heights
