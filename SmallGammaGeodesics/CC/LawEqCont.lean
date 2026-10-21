import SmallGammaGeodesics.Core.Interfaces
import SmallGammaGeodesics.CC.Lusin
import SmallGammaGeodesics.CC.LusinRestrict
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Law-equality continuity (track CC, packet CC5, target T2)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D7** ("LawEqCont"); the statement
`CC.LawEqCont` is fixed in `SmallGammaGeodesics/Core/Interfaces.lean`.

**Theorem** (`lawEqCont : LawEqCont`). Let `μ` be a probability measure on `ℕ → ℝ`, `T` a second-countable
pseudo-metric space with its Borel σ-algebra and `F : (ℕ → ℝ) → T` Borel. If, for each `n`, `Y n` and
`Y' n` are random sequences on a probability space `(Ω n, P n)`, both with law `μ`, and
`Y n k - Y' n k → 0` in probability for every coordinate `k`, then `dist (F (Y n)) (F (Y' n)) → 0` in
probability.

*Proof* (D7, with the product uniformity of `ℕ → ℝ` in place of the metric `Σ 2⁻ᵏ min(1, |x k - y k|)`).
Fix `δ > 0` and `ε > 0`.
1. Lusin (`exists_isCompact_measure_compl_lt_continuousOn`; `ℕ → ℝ` is Polish) gives a compact `K` with
   `μ Kᶜ < ε / 3` and `F` continuous on `K`.
2. Heine–Cantor: `F` is uniformly continuous on `K`, and every entourage of the product uniformity contains
   a cylinder over finitely many coordinates. So there are a finite `I ⊆ ℕ` and `κ i > 0` (`i ∈ I`) with
   `x, y ∈ K`, `|x i - y i| < κ i` for all `i ∈ I` ⟹ `dist (F x) (F y) < δ`
   (`exists_finset_dist_lt_of_continuousOn`).
3. Hence `{δ ≤ dist (F (Y n)) (F (Y' n))} ⊆ {Y n ∉ K} ∪ {Y' n ∉ K} ∪ ⋃_{i ∈ I} {κ i ≤ |Y n i - Y' n i|}`,
   so `P n [δ ≤ dist …] ≤ 2 μ Kᶜ + Σ_{i ∈ I} P n [κ i ≤ |Y n i - Y' n i|]` by equality of laws. The finite
   sum tends to `0`, so it is `≤ ε / 3` for large `n`, and then `P n [δ ≤ dist …] ≤ ε`. ∎

No measurability of the events is needed: the bounds use only monotonicity and subadditivity of the
(outer) measures `P n`.

`lawEqCont_restrictPair` is the instance used by CC0 D9 step 5: `F = restrictPair d K₁`, the
`C(K₁ × K₁, ℝ)`-valued restriction functional of `CC/LusinRestrict.lean` (the corrected T3′).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal Uniformity

namespace SmallGammaGeodesics.CC

/-- An entourage of a product of pseudo-metric spaces contains a cylinder: finitely many coordinates
`i ∈ I`, each with a positive tolerance `κ i`. -/
theorem exists_finset_of_mem_uniformity_pi {ι : Type*} {E : ι → Type*}
    [∀ i, PseudoMetricSpace (E i)] {V : Set ((∀ i, E i) × (∀ i, E i))}
    (hV : V ∈ 𝓤 (∀ i, E i)) :
    ∃ I : Finset ι, ∃ κ : ι → ℝ, (∀ i ∈ I, 0 < κ i) ∧
      ∀ x y : ∀ i, E i, (∀ i ∈ I, dist (x i) (y i) < κ i) → (x, y) ∈ V := by
  rw [Pi.uniformity] at hV
  obtain ⟨⟨I, κ⟩, ⟨hI, hκ⟩, hsub⟩ :=
    (Filter.HasBasis.iInf' fun i => (Metric.uniformity_basis_dist (α := E i)).comap
      (fun a : (∀ i, E i) × (∀ i, E i) => (a.1 i, a.2 i))).mem_iff.1 hV
  refine ⟨hI.toFinset, κ, fun i hi => hκ i (hI.mem_toFinset.1 hi), fun x y hxy => hsub ?_⟩
  simp only [mem_iInter₂, mem_preimage, mem_ofPred_eq]
  exact fun i hi => hxy i (hI.mem_toFinset.2 hi)

/-- **Heine–Cantor in coordinates**: a map continuous on a compact subset of a product of
pseudo-metric spaces is uniformly continuous there, with a modulus that reads finitely many
coordinates. -/
theorem exists_finset_dist_lt_of_continuousOn {ι : Type*} {E : ι → Type*}
    [∀ i, PseudoMetricSpace (E i)] {T : Type*} [PseudoMetricSpace T] {F : (∀ i, E i) → T}
    {K : Set (∀ i, E i)} (hK : IsCompact K) (hF : ContinuousOn F K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ I : Finset ι, ∃ κ : ι → ℝ, (∀ i ∈ I, 0 < κ i) ∧
      ∀ x ∈ K, ∀ y ∈ K, (∀ i ∈ I, dist (x i) (y i) < κ i) → dist (F x) (F y) < δ := by
  have hmem := hK.uniformContinuousOn_of_continuous hF (Metric.dist_mem_uniformity hδ)
  rw [Filter.mem_map, Filter.mem_inf_principal] at hmem
  obtain ⟨I, κ, hκ, hV⟩ := exists_finset_of_mem_uniformity_pi hmem
  exact ⟨I, κ, hκ, fun x hx y hy hxy => hV x y hxy ⟨hx, hy⟩⟩

/-- **Law-equality continuity** (CC0 D7; target T2 of packet CC5): the interface statement
`CC.LawEqCont` of `Core/Interfaces.lean`, proved. -/
theorem lawEqCont : LawEqCont := by
  intro T _ _ _ _ F hF μ hμ Ω _ P _ Y Y' hY hY' hlawY hlawY' hconv δ hδ
  have := hμ
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : 0 < ε / 3 := ENNReal.div_pos hε.ne' (by norm_num)
  -- step 1: a Lusin compact set
  obtain ⟨K, hK, hKμ, hFK⟩ := exists_isCompact_measure_compl_lt_continuousOn hF μ hε3
  -- step 2: uniform continuity on `K`, in finitely many coordinates
  obtain ⟨I, κ, hκ, hIK⟩ := exists_finset_dist_lt_of_continuousOn hK hFK hδ
  -- step 3: the coordinate deviations
  have hsum : Tendsto (fun n => ∑ i ∈ I, P n {ω | κ i ≤ |Y n ω i - Y' n ω i|}) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum I fun i hi => hconv i (κ i) (hκ i hi)
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hsum (ε / 3) hε3] with n hn
  have hKm : MeasurableSet Kᶜ := hK.isClosed.measurableSet.compl
  have h1 : P n (Y n ⁻¹' Kᶜ) = μ Kᶜ := by rw [← Measure.map_apply (hY n) hKm, hlawY n]
  have h2 : P n (Y' n ⁻¹' Kᶜ) = μ Kᶜ := by rw [← Measure.map_apply (hY' n) hKm, hlawY' n]
  calc P n {ω | δ ≤ dist (F (Y n ω)) (F (Y' n ω))}
      ≤ P n ((Y n ⁻¹' Kᶜ ∪ Y' n ⁻¹' Kᶜ) ∪ ⋃ i ∈ I, {ω | κ i ≤ |Y n ω i - Y' n ω i|}) := by
        refine measure_mono fun ω hω => ?_
        by_contra hcon
        simp only [mem_union, mem_preimage, mem_compl_iff, not_or, not_not, mem_iUnion,
          mem_ofPred_eq, not_exists, not_le] at hcon
        obtain ⟨⟨hYK, hY'K⟩, hcoord⟩ := hcon
        refine absurd hω (not_le.2 (hIK _ hYK _ hY'K fun i hi => ?_))
        rw [Real.dist_eq]
        exact hcoord i hi
    _ ≤ P n (Y n ⁻¹' Kᶜ) + P n (Y' n ⁻¹' Kᶜ) +
          ∑ i ∈ I, P n {ω | κ i ≤ |Y n ω i - Y' n ω i|} :=
        (measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) (measure_biUnion_finset_le I _))
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        rw [h1, h2]
        exact add_le_add (add_le_add hKμ.le hKμ.le) hn
    _ = ε := ENNReal.add_thirds ε

/-- **`LawEqCont` for the restriction functional** (CC0 D9 step 5): with
`F̂ = restrictPair d K₁ : (ℕ → ℝ) → C(K₁ × K₁, ℝ)` (sup metric),
`dist (F̂ (Y n)) (F̂ (Y' n)) → 0` in probability. On the event where `d (Y n ω)` and `d (Y' n ω)` are
finite and continuous on `K₁ × K₁`, this distance is `sup_{K₁²} |d (Y n ω) - d (Y' n ω)|`
(`restrictPair_apply`, `abs_sub_le_dist_restrictPair`). -/
theorem lawEqCont_restrictPair {E : Type} [PseudoMetricSpace E] {d : (ℕ → ℝ) → E → E → ℝ≥0∞}
    (hd : ∀ u v, Measurable fun x => d x u v) (K₁ : Set E) [CompactSpace K₁]
    (μ : Measure (ℕ → ℝ)) [IsProbabilityMeasure μ] (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)] (Y Y' : ∀ n, Ω n → ℕ → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hY' : ∀ n, Measurable (Y' n))
    (hlawY : ∀ n, (P n).map (Y n) = μ) (hlawY' : ∀ n, (P n).map (Y' n) = μ)
    (hconv : ∀ k : ℕ, ∀ η : ℝ, 0 < η →
      Tendsto (fun n => P n {ω | η ≤ |Y n ω k - Y' n ω k|}) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => P n {ω | δ ≤ dist (restrictPair d K₁ (Y n ω)) (restrictPair d K₁ (Y' n ω))})
      atTop (𝓝 0) :=
  lawEqCont (restrictPair d K₁) (measurable_restrictPair hd) μ inferInstance Ω P Y Y' hY hY'
    hlawY hlawY' hconv δ hδ

end SmallGammaGeodesics.CC
