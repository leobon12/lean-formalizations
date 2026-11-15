/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR7Source
import InteractingSLE.Spec.Sec2.CriticalLifetime

/-! # Every finite terminal SDE state contains a nonadmissible colliding prefix -/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2JDetR7

/-- For an ordered side, the force marks at the driver form an initial
segment. A nonadmissible collision is therefore a nonadmissible prefix. -/
theorem exists_bad_prefix_of_collision_sum {n : ℕ} {ρ v : Fin n → ℝ} {w : ℝ}
    (hv : Monotone v) (hw : ∀ i, w ≤ v i)
    (hs : ∑ i ∈ univ.filter (fun i => v i = w), ρ i ≤ -2) :
    ∃ j : Fin n, v j = w ∧ ∑ i ∈ univ.filter (fun i => i ≤ j), ρ i ≤ -2 := by
  let S := univ.filter fun i => v i = w
  have hS : S.Nonempty := by
    by_contra he
    have heq := Finset.not_nonempty_iff_eq_empty.mp he
    change ∑ i ∈ S, ρ i ≤ -2 at hs
    rw [heq, sum_empty] at hs
    norm_num at hs
  let j := S.max' hS
  have hj : v j = w := (mem_filter.mp (S.max'_mem hS)).2
  have heq : S = univ.filter (fun i => i ≤ j) := by
    ext i
    simp only [S, mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      exact S.le_max' i (mem_filter.mpr ⟨mem_univ _, hi⟩)
    · intro hij
      exact le_antisymm ((hv hij).trans hj.le) (hw i)
  refine ⟨j, hj, ?_⟩
  change ∑ i ∈ S, ρ i ≤ -2 at hs
  rwa [heq] at hs

/-- A threshold at a two-sided ordered state has a colliding mark whose
complete side prefix has total weight at most `-2`. -/
theorem exists_bad_prefix_of_threshold {nL nR : ℕ}
    {ρL vL : Fin nL → ℝ} {ρR vR : Fin nR → ℝ} {w : ℝ}
    (hL : Antitone vL) (hR : Monotone vR)
    (hLw : ∀ i, vL i ≤ w) (hwR : ∀ i, w ≤ vR i)
    (hth : ForceWord.ThresholdCondition ρL ρR w vL vR) :
    (∃ i : Fin nL, vL i = w ∧ ∑ j ∈ univ.filter (fun j => j ≤ i), ρL j ≤ -2) ∨
      ∃ i : Fin nR, vR i = w ∧ ∑ j ∈ univ.filter (fun j => j ≤ i), ρR j ≤ -2 := by
  rcases hth with ht | ht
  · have hn : Monotone fun i => -vL i := fun i j hij => neg_le_neg (hL hij)
    have ht' : ∑ i ∈ univ.filter (fun i => -vL i = -w), ρL i ≤ -2 := by
      simpa only [neg_inj] using ht
    obtain ⟨i, hi, hs⟩ := exists_bad_prefix_of_collision_sum hn
      (fun i => neg_le_neg (hLw i)) ht'
    exact Or.inl ⟨i, neg_injective hi, hs⟩
  · exact Or.inr (exists_bad_prefix_of_collision_sum hR hwR ht)

section Evolution

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- Aux. 3 gives finite terminal coordinates; their preserved order identifies
the actual colliding nonadmissible prefix, including coincident labels. -/
theorem ae_terminal_bad_prefix (ha : 0 < a)
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
      ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
        Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω))
          (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
        ((∃ i : Fin nL, vL₀ i = w₀ ∧
          ∑ j ∈ univ.filter (fun j => j ≤ i), ρL j ≤ -2) ∨
          ∃ i : Fin nR, vR₀ i = w₀ ∧
            ∑ j ∈ univ.filter (fun j => j ≤ i), ρR j ≤ -2) := by
  filter_upwards [hE.ae_tendsto_threshold ha, hE.ae_isIntegratedSLEPath]
    with ω hlim hp T hT hζ
  obtain ⟨w₀, vL₀, vR₀, hconv, hth⟩ := hlim T hT hζ
  have : NeBot (𝓝[<] T) := nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  have hev : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, (t : ℝ≥0∞) < ζ ω := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← hζ]
    exact_mod_cast ht
  have hw := hconv.fst_nhds
  have hvL : ∀ i, Tendsto (fun t => VL i t ω) (𝓝[<] T) (𝓝 (vL₀ i)) :=
    tendsto_pi_nhds.mp hconv.snd_nhds.fst_nhds
  have hvR : ∀ i, Tendsto (fun t => VR i t ω) (𝓝[<] T) (𝓝 (vR₀ i)) :=
    tendsto_pi_nhds.mp hconv.snd_nhds.snd_nhds
  refine ⟨w₀, vL₀, vR₀, hconv, exists_bad_prefix_of_threshold ?_ ?_ ?_ ?_ hth⟩
  · intro i j hij
    exact le_of_tendsto_of_tendsto (hvL j) (hvL i)
      (hev.mono fun t ht => hp.isForcePath.antitone_vL ht hij)
  · intro i j hij
    exact le_of_tendsto_of_tendsto (hvR i) (hvR j)
      (hev.mono fun t ht => hp.isForcePath.monotone_vR ht hij)
  · intro i
    exact le_of_tendsto_of_tendsto (hvL i) hw
      (hev.mono fun t ht => hp.isForcePath.vL_le_w ht i)
  · intro i
    exact le_of_tendsto_of_tendsto hw (hvR i)
      (hev.mono fun t ht => hp.isForcePath.w_le_vR ht i)

/-- Admissible side partial sums allow boundary collisions but never a finite
continuation lifetime. This is weaker than the nonhitting-sector hypothesis. -/
theorem ae_lifetime_top_of_admissible_prefixes (ha : 0 < a)
    (hword : IsOrderedForceWord xL xR)
    (hL : ∀ i, -2 < ∑ j ∈ univ.filter (fun j => j ≤ i), ρL j)
    (hR : ∀ i, -2 < ∑ j ∈ univ.filter (fun j => j ≤ i), ρR j)
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ := by
  have hbad : ∀ {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} {w : ℝ},
      ¬ ((∃ i, vL i = w ∧ ∑ j ∈ univ.filter (fun j => j ≤ i), ρL j ≤ -2) ∨
        ∃ i, vR i = w ∧ ∑ j ∈ univ.filter (fun j => j ≤ i), ρR j ≤ -2) := by
    rintro vL vR w (⟨i, -, hi⟩ | ⟨i, -, hi⟩)
    · exact (not_le.mpr (hL i)) hi
    · exact (not_le.mpr (hR i)) hi
  filter_upwards [ae_terminal_bad_prefix ha hE, hE.ae_isIntegratedSLEPath]
    with ω hlim hp
  by_contra hfin
  let T := (ζ ω).toNNReal
  have hT : (T : ℝ≥0∞) = ζ ω := ENNReal.coe_toNNReal hfin
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ T) with hz | hz
  · have hζ0 : ζ ω = 0 := by rw [← hT, ← hz, ENNReal.coe_zero]
    obtain ⟨hxL, hxL0, hxR, hxR0⟩ := hword
    exact hbad (exists_bad_prefix_of_threshold hxL hxR hxL0 hxR0
      (hp.isForcePath.threshold_of_eq_zero hζ0))
  · obtain ⟨w₀, vL₀, vR₀, -, hb⟩ := hlim T hz hT
    exact hbad hb

end Evolution

end InteractingSLE.Theorem14.GW2JDetR7
