import InteractingSLE.Spec.Dimension.FiniteCover
import InteractingSLE.Spec.Dimension.FiniteGirsanov
import InteractingSLE.Spec.Dimension.ForceGaps

/-!
# Aux. lemma 15 (DU7): interior dimension of continuous finite-force traces

Packet PROVE-T11-DU2. Specification, Aux. lemma 15 (`source/spec/p049-096.md`, L856–L872, pp. 88–89): for
`0 < κ < 8` and an integrated finite-force `SLE_κ(ρ)` with an available continuous trace before its
continuation threshold, almost surely `dim_H(γ ∩ ℍ) ≤ d_κ < 2` (DU7), with `d_κ` from Aux. lemma 14
(`interiorDimBound κ = 3/2 + κ/16`). The result applies to every stopped prefix and to its completion by one
continuous finite terminal endpoint.

Assembly (graph slice `GX-SPEC-04`, nodes `SPEC.aux-15#localized-girsanov`, `#first-visit-cover`,
`SPEC.aux-15`):

* countably many localizations, indexed by a rational start `a ≥ 0` and `n ∈ ℕ` (elapsed time `≤ n`, all gaps
  `≥ 1/(n+1)`), each giving a path `X` whose law is `≪` a Brownian law (`exists_brownian_localization`);
* by Aux. lemma 14 transferred through `≪` (`ae_trace_good_of_absolutelyContinuous`), almost surely each
  localized trace has radial limits and interior dimension `≤ d_κ`;
* nonzero force gaps at the first visit `t₁` of an interior point, continuity of the gaps, a rational
  `a < t₁` close to `t₁`, and `n` large give a localization lasting up to `t₁`;
* the first-visit cover (`dimH_image_inter_H_le_of_cover`).

## Main results

* `ae_dimH_image_inter_H_le_of_gaps`: (DU7) from the nonzero-gap property (O2) (a named conditional form).
* `dimH_image_le_inter_H_le`: the completion by a terminal endpoint does not alter the bound.
-/

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Dimension

open QuantumZipper QuantumZipper.RS

/-- The gaps bounded below near a time where they are nonzero: if all gaps are nonzero at `t₁ < ζ` (and the
coordinates are continuous before `ζ`), there is `ε > 0` such that for `|s − t₁| < ε` every gap exceeds half
its value at `t₁`. -/
theorem exists_gap_half_lt {nL nR : ℕ} {ζ : ℝ≥0∞} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hvL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ})
    (hvR : ∀ i, ContinuousOn (vR i) {t | (t : ℝ≥0∞) < ζ}) {t₁ : ℝ≥0} (ht₁ : (t₁ : ℝ≥0∞) < ζ) :
    ∃ ε > 0, ∀ s : ℝ≥0, dist s t₁ < ε →
      (∀ i, |w t₁ - vL i t₁| / 2 < |w s - vL i s| ∨ w t₁ = vL i t₁) ∧
      ∀ i, |w t₁ - vR i t₁| / 2 < |w s - vR i s| ∨ w t₁ = vR i t₁ := by
  have hO : {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} ∈ 𝓝 t₁ :=
    (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds ht₁
  have hev : ∀ᶠ s in 𝓝 t₁,
      (∀ i, |w t₁ - vL i t₁| / 2 < |w s - vL i s| ∨ w t₁ = vL i t₁) ∧
      ∀ i, |w t₁ - vR i t₁| / 2 < |w s - vR i s| ∨ w t₁ = vR i t₁ := by
    refine (Filter.eventually_all.2 fun i => ?_).and (Filter.eventually_all.2 fun i => ?_)
    · by_cases h : w t₁ = vL i t₁
      · exact Eventually.of_forall fun _ => Or.inr h
      have hpos : 0 < |w t₁ - vL i t₁| := abs_pos.2 (sub_ne_zero.2 h)
      have hc : ContinuousAt (fun s => |w s - vL i s|) t₁ :=
        ((hw.continuousAt hO).sub ((hvL i).continuousAt hO)).abs
      exact (hc.eventually (lt_mem_nhds (half_lt_self hpos))).mono fun s hs => Or.inl hs
    · by_cases h : w t₁ = vR i t₁
      · exact Eventually.of_forall fun _ => Or.inr h
      have hpos : 0 < |w t₁ - vR i t₁| := abs_pos.2 (sub_ne_zero.2 h)
      have hc : ContinuousAt (fun s => |w s - vR i s|) t₁ :=
        ((hw.continuousAt hO).sub ((hvR i).continuousAt hO)).abs
      exact (hc.eventually (lt_mem_nhds (half_lt_self hpos))).mono fun s hs => Or.inl hs
  exact Metric.eventually_nhds_iff.1 hev

/-- **(DU7) from nonzero gaps at interior tips** (Aux. lemma 15; conditional form with the input (O2) as an
explicit hypothesis `hgaps`, which `ForceGaps.lean` proves). Let `0 < κ < 8` and let `(W, V, B)` be an
integrated `SLE_κ(ρ)` evolution with lifetime `ζ`. If almost surely, for every continuous generating trace `η`
of `W` before `ζ`, all force gaps are nonzero at every time `t < ζ` with `η(t) ∈ ℍ`, then almost surely every
continuous generating trace satisfies `dim_H(η([0, ζ)) ∩ ℍ) ≤ d_κ`. -/
theorem ae_dimH_image_inter_H_le_of_gaps {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hgaps : ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → η t ∈ H →
        (∀ i, W t ω ≠ VL i t ω) ∧ ∀ i, W t ω ≠ VR i t ω) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
      dimH (η '' {t | (t : ℝ≥0∞) < ζ ω} ∩ H) ≤ ENNReal.ofReal (interiorDimBound κ) := by
  have hδ : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hloc := fun p : ℚ × ℕ =>
    exists_brownian_localization hκ hE ((p.1 : ℝ).toNNReal) (p.2 : ℝ≥0) (hδ p.2)
  choose X hXm μ hμprob hμBM hac hXeq using hloc
  have hgood : ∀ p : ℚ × ℕ, ∀ᵐ ω ∂P, (∀ u : ℝ, 0 ≤ u → Tendsto
        (fun y : ℝ => fwdMapInv (drive κ canonBM (X p ω)) u (y * Complex.I)) (𝓝[>] 0)
        (𝓝 (trace (drive κ canonBM (X p ω)) u))) ∧
      ContinuousOn (trace (drive κ canonBM (X p ω))) (Ici 0) ∧
      HasInteriorDimBound (interiorDimBound κ) (drive κ canonBM (X p ω)) := fun p => by
    have := hμprob p
    exact ae_trace_good_of_absolutelyContinuous hκ hκ8 (hXm p).aemeasurable (hμBM p) (hac p)
  filter_upwards [ae_all_iff.2 hgood, ae_all_iff.2 hXeq, hgaps, hE.2.2.2.2] with ω hg hx hgap hp
    η hη
  have hw : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := hp.2.2.2.1
  refine dimH_image_inter_H_le_of_cover hη hw hp.1 (κ := κ) (fun p : ℚ × ℕ => (p.1 : ℝ).toNNReal)
    (fun p => X p ω) (fun p => (hg p).1) (fun p => (hg p).2.2.1) ?_
  intro t₁ ht₁ ht₁ζ hzH
  obtain ⟨hgL, hgR⟩ := hgap η hη t₁ ht₁ζ hzH
  obtain ⟨ε, hε, hεgap⟩ := exists_gap_half_lt hw hp.2.2.2.2.1 hp.2.2.2.2.2.1 ht₁ζ
  -- a rational start `a ∈ (t₁ − ε, t₁)`, `a > 0`
  have ht₁r : (0 : ℝ) < t₁ := by exact_mod_cast ht₁
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max ((t₁ : ℝ) - ε) 0 < t₁ from
    max_lt (by linarith) ht₁r)
  have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (le_max_right _ _) hq1
  set a : ℝ≥0 := (q : ℝ).toNNReal with ha
  have haq : (a : ℝ) = q := Real.coe_toNNReal _ hq0.le
  have hat₁ : a < t₁ := by rw [← NNReal.coe_lt_coe, haq]; exact hq2
  -- `n` large: small gap threshold and long elapsed time
  have hevn : ∀ᶠ n : ℕ in atTop, ((∀ i, 1 / ((n : ℝ) + 1) < |W t₁ ω - VL i t₁ ω| / 2) ∧
      ∀ i, 1 / ((n : ℝ) + 1) < |W t₁ ω - VR i t₁ ω| / 2) ∧ t₁ - a ≤ (n : ℝ≥0) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine ((Filter.eventually_all.2 fun i => h0.eventually (gt_mem_nhds ?_)).and
      (Filter.eventually_all.2 fun i => h0.eventually (gt_mem_nhds ?_))).and
      ((tendsto_natCast_atTop_atTop (R := ℝ≥0)).eventually_ge_atTop (t₁ - a))
    · exact half_pos (abs_pos.2 (sub_ne_zero.2 (hgL i)))
    · exact half_pos (abs_pos.2 (sub_ne_zero.2 (hgR i)))
  obtain ⟨n, ⟨hnL, hnR⟩, hnT⟩ := hevn.exists
  refine ⟨(q, n), hat₁, fun t ht => ?_⟩
  have htn : t ≤ (n : ℝ≥0) := by
    refine le_trans ?_ hnT
    rw [le_tsub_iff_left hat₁.le]
    exact ht
  have htζ : ((a + t : ℝ≥0) : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) ht₁ζ
  refine hx (q, n) t htn htζ fun s hs1 hs2 => ?_
  have hsd : dist s t₁ < ε := by
    rw [NNReal.dist_eq, abs_lt]
    have h1 : (a : ℝ) ≤ s := by exact_mod_cast hs1
    have h2 : (s : ℝ) ≤ t₁ := by exact_mod_cast hs2.trans ht
    constructor <;> [linarith [le_max_left ((t₁ : ℝ) - ε) 0]; linarith]
  obtain ⟨hL, hR⟩ := hεgap s hsd
  constructor
  · intro i
    rcases hL i with h | h
    · exact (hnL i).le.trans h.le
    · exact absurd h (hgL i)
  · intro i
    rcases hR i with h | h
    · exact (hnR i).le.trans h.le
    · exact absurd h (hgR i)

/-- **Completion by one terminal endpoint** (Aux. lemma 15: "Adding a single continuous terminal point does
not alter the bound"): the bound for `η([0, ζ))` gives the same bound for `η([0, ζ])`. -/
theorem dimH_image_le_inter_H_le {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ} {d : ℝ≥0∞}
    (h : dimH (η '' {t | (t : ℝ≥0∞) < ζ} ∩ H) ≤ d) :
    dimH (η '' {t | (t : ℝ≥0∞) ≤ ζ} ∩ H) ≤ d := by
  have hsub : η '' {t | (t : ℝ≥0∞) ≤ ζ} ∩ H ⊆
      (η '' {t | (t : ℝ≥0∞) < ζ} ∩ H) ∪ η '' {t | (t : ℝ≥0∞) = ζ} := by
    rintro _ ⟨⟨t, ht, rfl⟩, hH⟩
    rcases (show (t : ℝ≥0∞) ≤ ζ from ht).lt_or_eq with h | h
    · exact Or.inl ⟨⟨t, h, rfl⟩, hH⟩
    · exact Or.inr ⟨t, h, rfl⟩
  have hss : (η '' {t : ℝ≥0 | (t : ℝ≥0∞) = ζ}).Subsingleton := by
    rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩
    have : t = t' := ENNReal.coe_injective ((show (t : ℝ≥0∞) = ζ from ht).trans
      (show (t' : ℝ≥0∞) = ζ from ht').symm)
    rw [this]
  refine (dimH_mono hsub).trans ?_
  rw [dimH_union, hss.dimH_zero]
  exact max_le h (by simp)

/-- **Aux. lemma 15 (DU7).** Let `0 < κ < 8` and let `(W, V, B)` be an integrated finite-force `SLE_κ(ρ)`
evolution with lifetime (continuation threshold) `ζ`. Almost surely, every continuous generating trace `η` of
the driver before `ζ` (an "available continuous trace"; continuity is assumed, not proved, and simplicity is not
assumed) satisfies `dim_H(η(S) ∩ ℍ) ≤ d_κ` for every set of times `S ⊆ [0, ζ]`: every stopped prefix, and its
completion by the terminal endpoint. Here `d_κ = interiorDimBound κ = 3/2 + κ/16 < 2` (Aux. lemma 14,
`interiorDimBound_lt_two`). -/
theorem _root_.InteractingSLE.IsIntegratedSLEEvolution.ae_dimH_image_inter_H_le {κ : ℝ}
    (hκ : 0 < κ) (hκ8 : κ < 8) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
      ∀ S : Set ℝ≥0, S ⊆ {t | (t : ℝ≥0∞) ≤ ζ ω} →
        dimH (η '' S ∩ H) ≤ ENNReal.ofReal (interiorDimBound κ) := by
  filter_upwards [ae_dimH_image_inter_H_le_of_gaps hκ hκ8 hE hE.ae_forall_ne_of_mem_H] with ω h
    η hη S hS
  exact (dimH_mono (inter_subset_inter_left _ (image_mono hS))).trans
    (dimH_image_le_inter_H_le (h η hη))

theorem interiorDimBound_pos {κ : ℝ} (hκ : 0 < κ) : 0 < interiorDimBound κ := by
  simp only [interiorDimBound, onePointExponent]
  linarith

/-- **(DU7) supplies (SR3)** (consequence after Aux. lemma 15, `source/spec/p049-096.md` L874, graph node
`SPEC.aux-15#sr3-consequence`, first half). For `0 < ε < β_κ/4`, almost surely every available continuous
trace `η` and every set of times `S ⊆ [0, ζ]` give `dim_H(η(S) ∩ K) < 2 − 2ε` for every `K ⊆ ℍ`, in particular
for every compact `K ⋐ ℍ`: the hypothesis (SR3) of Aux. lemmas 12–13 (in the form of
`Sobolev.eq_zero_of_isLocNegSobolev_of_dimH_lt`, with `U = ℍ`). -/
theorem _root_.InteractingSLE.IsIntegratedSLEEvolution.ae_dimH_image_inter_lt {κ ε : ℝ}
    (hκ : 0 < κ) (hκ8 : κ < 8) (hε : ε < onePointExponent κ / 4) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
      ∀ S : Set ℝ≥0, S ⊆ {t | (t : ℝ≥0∞) ≤ ζ ω} → ∀ K : Set ℂ, K ⊆ H →
        dimH (η '' S ∩ K) < ENNReal.ofReal (2 - 2 * ε) := by
  have hd := interiorDimBound_lt_two_sub hε
  have hlt : ENNReal.ofReal (interiorDimBound κ) < ENNReal.ofReal (2 - 2 * ε) :=
    (ENNReal.ofReal_lt_ofReal_iff ((interiorDimBound_pos hκ).trans hd)).2 hd
  filter_upwards [hE.ae_dimH_image_inter_H_le hκ hκ8] with ω h η hη S hS K hK
  exact lt_of_le_of_lt ((dimH_mono (inter_subset_inter_right _ hK)).trans (h η hη S hS)) hlt

end InteractingSLE.Dimension
