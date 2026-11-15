/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Prop419Lines
import InteractingSLE.WangWu.ChamberArcs
import InteractingSLE.Spec.Sec5.GlueCondMean

/-!
# Wang–Wu Proposition 4.19: the setting (one field, its seed lines at several heights) and the statement

Packet PROVE-WW-B20. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), Proposition 4.19
(L1655–L1708):

> **Proposition 4.19 (Order of non-boundary-intersecting seed lines).** Let `h` have finite piecewise constant original
> boundary data `b₀` in `ℍ`, and let `u₁ < u₂`. Suppose `b₀ + uᵢ ≤ −λ` on `ℝ₋` and `b₀ + uᵢ ≥ λ` on `ℝ₊` for `i = 1, 2`.
> Then `γ_{u₂}` lies to the left of `γ_{u₁}` almost surely.

Here the height-`u` seed line of `h` is the level line of `h + u` (Definition 1.9). For the two-seed data
`b₀ = −λ(1 + ρL)` on `ℝ₋`, `λ(1 + ρR)` on `ℝ₊` (`λ = π/2`), the field `h + u` (`Exist.flowField 0 u h`, the distribution
`φ ↦ h(φ) + u ∫ φ`) has the two-seed data of the word `(ρL − u/λ; ρR + u/λ)`, and the hypothesis of Proposition 4.19 is
that this word is nonnegative.

* `forceBoundaryData_twoSeed_four_add`, **`isGFFWithBoundaryData_twoSeed_shift`**: the height shift of a two-seed GFF;
* **`exists_seedLineSpace`**: for any family of heights whose words are nonnegative, one probability space carries a
  GFF `h` with the base data and, for every height `uᵢ`, an optional hull coupling of the word `(ρL − uᵢ/λ; ρR + uᵢ/λ)`
  with the field `h + uᵢ` (Proposition 4.24's "seed lines at heights `u₁, 0, u₂` … determined by the field");
* **`Prop419Statement`** (named input): Proposition 4.19 for two-seed base data, in the exact form Lemma 4.22
  (`IsOrderedArcs`) consumes: the seed line of the larger height avoids the right side of the other one;
* **`ae_isOrderedArcs_of_prop419`**: three heights `u₁ < u₂ < u₃` on one space give almost surely three ordered simple
  proper arcs (`IsOrderedArcs`), the input of Lemmas 4.21–4.22 and of Proposition 4.24's chamber.

The proof of Proposition 4.19 itself needs Lemma 4.17 (forbidden boundary arcs) and hence Lemmas 4.15–4.16 (the local
Cameron–Martin comparison with a strip reference); see `planning/handoffs/PROVE-WW-B20.md`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu.SeedField

/-! ### The height shift of a two-seed GFF -/

theorem sleLambda_four : Real.pi / Real.sqrt 4 = wwLambda := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rfl

/-- The two-seed data at `κ = 4` shifted by `c` is the two-seed data of the word `(ρL − c/λ; ρR + c/λ)`. -/
theorem forceBoundaryData_twoSeed_four_add (rL rR c x : ℝ) :
    forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) LP.twoSeedXL LP.twoSeedXR x + c =
      forceBoundaryData 4 (fun _ : Fin 1 => rL - c / wwLambda) (fun _ : Fin 1 => rR + c / wwLambda) LP.twoSeedXL
        LP.twoSeedXR x := by
  have hl : wwLambda ≠ 0 := wwLambda_pos.ne'
  rw [forceBoundaryData_twoSeed, forceBoundaryData_twoSeed, sleLambda_four]
  split_ifs
  · field_simp; ring
  · field_simp; ring

/-- **The height shift of a two-seed GFF** (Definition 1.9): if `h` is a GFF with the two-seed data of `(ρL; ρR)` at
`κ = 4`, then `h + c` is a GFF with the two-seed data of `(ρL − c/λ; ρR + c/λ)`. -/
theorem isGFFWithBoundaryData_twoSeed_shift {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {rL rR : ℝ}
    (hh : IsGFFWithBoundaryData P h (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) LP.twoSeedXL
      LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR)) (c : ℝ) :
    IsGFFWithBoundaryData P (fun ω => Exist.flowField 0 c (h ω))
      (forceBoundaryData 4 (fun _ : Fin 1 => rL - c / wwLambda) (fun _ : Fin 1 => rR + c / wwLambda) LP.twoSeedXL
        LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) := by
  refine ⟨(Exist.measurable_flowField 0 c).comp hh.1, fun v hv => ?_⟩
  obtain ⟨u₀, hu₀, -⟩ := Spec.Provider.existsUnique_isBoundedHarmonicExtension_forceBoundaryData (κ := 4)
    (ρL := fun _ : Fin 1 => rL) (ρR := fun _ : Fin 1 => rR) (vL := LP.twoSeedXL) (vR := LP.twoSeedXR)
  have hmi : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun w => u₀ (w + (0 : ℝ)) * φ w) := fun φ =>
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn (S := H)
      ((hu₀.1.continuousOn).comp (continuousOn_id.add continuousOn_const) fun z hz => Exist.add_real_mem_H hz 0) φ
      φ.tsupport_subset
  have hX := Exist.isZBGFFProcess_flowField (hh.2 u₀ hu₀) 0 c hmi
  have hshift := Sec5.GlueCond.isBoundedHarmonicExtension_add_const hu₀ c
  have hdata : (fun x => forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) LP.twoSeedXL
      LP.twoSeedXR x + c) = forceBoundaryData 4 (fun _ : Fin 1 => rL - c / wwLambda)
        (fun _ : Fin 1 => rR + c / wwLambda) LP.twoSeedXL LP.twoSeedXR :=
    funext fun x => forceBoundaryData_twoSeed_four_add rL rR c x
  rw [hdata] at hshift
  have heq := Impl.eqOn_of_isBoundedHarmonicExtension
    (by rw [forceJumpSet_twoSeed]; exact Finset.finite_toSet _) hshift hv
  convert hX using 4 with φ ω
  congr 1
  funext z
  by_cases hz : z ∈ H
  · rw [heq hz, Complex.ofReal_zero, add_zero]
  · have h0 : φ z = 0 := φ.zero_on_compl (show z ∈ ((upperHalfPlaneOpens : Set ℂ))ᶜ from hz)
    rw [h0, mul_zero, mul_zero]

/-! ### One field and its seed lines at several heights -/

/-- **One field and its seed lines at a family of heights** (Proposition 4.24: "Choose `a, b` sufficiently
large that the
seed lines at heights `u₁, 0, u₂` are all non-boundary-intersecting. By Propositions 4.18 and 4.19, these are simple,
continuous, transient, determined by the field"). For base two-seed weights `(ρL; ρR)` and heights `uᵢ` whose words
`(ρL − uᵢ/λ; ρR + uᵢ/λ)` are nonnegative, one probability space (in any universe) carries a GFF `h` with the
base data and,
for every `i`, an optional hull coupling of the word of height `uᵢ` with the field `h + uᵢ`. -/
theorem exists_seedLineSpace {ι : Type*} {rL rR : ℝ} (u : ι → ℝ) (hL : ∀ i, 0 ≤ rL - u i / wwLambda)
    (hR : ∀ i, 0 ≤ rR + u i / wwLambda) :
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) LP.twoSeedXL
        LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) ∧
      ∀ i, ∃ (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
        (ζ : Ω → ℝ≥0∞),
        IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - u i / wwLambda)
          (fun _ => rR + u i / wwLambda) P 𝓕 W VL VR B ζ (fun ω => Exist.flowField 0 (u i) (h ω)) := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h, hcoup⟩ :=
    Spec.Provider.exists_isOptionalHullCoupling.{u} (κ := 4) (xL := LP.twoSeedXL) (xR := LP.twoSeedXR)
      (ρL := fun _ : Fin 1 => rL) (ρR := fun _ : Fin 1 => rR) (by norm_num) LP.isOrderedForceWord_twoSeed
  have hh : IsGFFWithBoundaryData P h (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) := ⟨hcoup.2.1, hcoup.2.2.1⟩
  exact ⟨Ω, mΩ, P, hP, h, hh, fun i =>
    exists_isOptionalHullCoupling_twoSeed_of_field (hL i) (hR i) (isGFFWithBoundaryData_twoSeed_shift hh (u i))⟩

/-! ### Proposition 4.19 (named input) and the ordered triple -/

/-- **Proposition 4.19 for two-seed base data** (Wang–Wu L1655–L1708; named input). For base weights `(ρL; ρR)` and
heights `u₁ < u₂` whose words `(ρL − uᵢ/λ; ρR + uᵢ/λ)` are nonnegative: on every probability space carrying a field `h`
and optional hull couplings of these words with the fields `h + u₁` and `h + u₂`, almost surely the seed line of height
`u₂` avoids the right side of the seed line of height `u₁` ("`γ_{u₂}` lies to the left of `γ_{u₁}`"). -/
def Prop419Statement : Prop :=
  ∀ (rL rR u₁ u₂ : ℝ), u₁ < u₂ → 0 ≤ rL - u₂ / wwLambda → 0 ≤ rR + u₁ / wwLambda →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens)
      (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ) (VL₁ VR₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ)
      (ζ₁ : Ω → ℝ≥0∞)
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω → ℝ) (B₂ : ℝ≥0 → Ω → ℝ)
      (ζ₂ : Ω → ℝ≥0∞),
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - u₁ / wwLambda)
        (fun _ => rR + u₁ / wwLambda) P 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ (fun ω => Exist.flowField 0 u₁ (h ω)) →
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - u₂ / wwLambda)
        (fun _ => rR + u₂ / wwLambda) P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ (fun ω => Exist.flowField 0 u₂ (h ω)) →
      ∀ᵐ ω ∂P, Disjoint (arcRange (seedLine ζ₂ W₂ ω)) (rightSideOf (arcRange (seedLine ζ₁ W₁ ω)))

/-- Each seed line of a nonnegative two-seed coupling is almost surely a simple proper arc. -/
theorem ae_isProperArc_seedLine {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {rL rR : ℝ}
    (hL : 0 ≤ rL) (hR : 0 ≤ rR) {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h) :
    ∀ᵐ ω ∂P, IsProperArc (seedLine ζ W ω) := by
  filter_upwards [IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hC.1]
    with ω hω
  exact hω.2.2.2.1

/-- **Three ordered seed lines** (Lemma 4.22's hypothesis "three seed lines of heights `u₁ < 0 < u₂` be ordered"), from
Proposition 4.19: for heights `u₁ < u₂ < u₃` with nonnegative words, the seed lines `R = γ_{u₁}`, `M = γ_{u₂}`,
`L = γ_{u₃}` of one field are almost surely three ordered simple proper arcs. -/
theorem ae_isOrderedArcs_of_prop419 (h419 : Prop419Statement.{u}) {rL rR u₁ u₂ u₃ : ℝ} (h12 : u₁ < u₂)
    (h23 : u₂ < u₃) (hL : 0 ≤ rL - u₃ / wwLambda) (hR : 0 ≤ rR + u₁ / wwLambda) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {𝓕₁ 𝓕₂ 𝓕₃ : Filtration ℝ≥0 mΩ} {W₁ W₂ W₃ : ℝ≥0 → Ω → ℝ} {VL₁ VR₁ VL₂ VR₂ VL₃ VR₃ : Fin 1 → ℝ≥0 → Ω → ℝ}
    {B₁ B₂ B₃ : ℝ≥0 → Ω → ℝ} {ζ₁ ζ₂ ζ₃ : Ω → ℝ≥0∞}
    (hC₁ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - u₁ / wwLambda)
      (fun _ => rR + u₁ / wwLambda) P 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ (fun ω => Exist.flowField 0 u₁ (h ω)))
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - u₂ / wwLambda)
      (fun _ => rR + u₂ / wwLambda) P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ (fun ω => Exist.flowField 0 u₂ (h ω)))
    (hC₃ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - u₃ / wwLambda)
      (fun _ => rR + u₃ / wwLambda) P 𝓕₃ W₃ VL₃ VR₃ B₃ ζ₃ (fun ω => Exist.flowField 0 u₃ (h ω))) :
    ∀ᵐ ω ∂P, IsOrderedArcs (seedLine ζ₁ W₁ ω) (seedLine ζ₂ W₂ ω) (seedLine ζ₃ W₃ ω) := by
  have hl : 0 < wwLambda := wwLambda_pos
  have hd : ∀ {a b : ℝ}, a ≤ b → a / wwLambda ≤ b / wwLambda := fun hab => div_le_div_of_nonneg_right hab hl.le
  have hL₁ : 0 ≤ rL - u₁ / wwLambda := by linarith [hd (h12.trans h23).le]
  have hL₂ : 0 ≤ rL - u₂ / wwLambda := by linarith [hd h23.le]
  have hR₂ : 0 ≤ rR + u₂ / wwLambda := by linarith [hd h12.le]
  have hR₃ : 0 ≤ rR + u₃ / wwLambda := by linarith [hd (h12.trans h23).le]
  have hL₂' : 0 ≤ rL - u₂ / wwLambda := hL₂
  filter_upwards [ae_isProperArc_seedLine hL₁ hR hC₁, ae_isProperArc_seedLine hL₂ hR₂ hC₂,
    ae_isProperArc_seedLine hL hR₃ hC₃,
    h419 rL rR u₁ u₂ h12 hL₂' hR P h 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ hC₁ hC₂,
    h419 rL rR u₂ u₃ h23 hL hR₂ P h 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₃ W₃ VL₃ VR₃ B₃ ζ₃ hC₂ hC₃]
    with ω h1 h2 h3 h12' h23'
  exact ⟨h1, h2, h3, h12', h23'⟩

end InteractingSLE.WangWu.SeedField
