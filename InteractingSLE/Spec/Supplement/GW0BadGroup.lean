/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW0BadGroupCompare
import InteractingSLE.Spec.Supplement.GW0Forward
import InteractingSLE.Spec.Sec4.RepulsionNoncollision

/-!
# Lemma GW0, third sentence: a first bad left group is reached, from BR3's bounded reference

Packet PROVE-T14-GW3. Lemma GW0 (supplement p. 617, `source/spec/p577-624.md` L922–L928): "If both initial seed
groups are admissible, any first inadmissible separated group is reached at a finite continuation threshold with
positive probability." Its proof (L926–L928): "suppose both seed groups are admissible, let `a` be a first bad left
mark, and preserve all its nearer left groups and its actual bad cumulative. Preserve the original right seed and
place one new opposite mark `b > 0` […] The inverse complete reference is therefore a bounded continuous curve ending
exactly at `a`, at its finite original continuation threshold. Its completed hull fits, with positive probability, in
one of the countable bounded crosscut buffers […] The actual and reference words agree on that whole base; all changed
groups lie outside the buffer. The compactly supported finite-energy cutoff used in BR3 and Aux. 108 transfers this
positive-probability whole-history common-threshold event to the original word."

This file proves the transfer for a **separated start** (every left mark strictly left of every right mark), in
driver form:

* the reference keeps the left weights through the first bad left group end `j` and puts `0` beyond
  (`refρL`; "remove its farther left marks"), keeps the right marks at the seed and may change the other right
  weights (the reference's right side must have admissible group ends: "Preserve the original right seed and put one
  right jump at a deterministic `b > 0` […] so that the total right weight is `c`");
* the **named input** `BR3ReferenceStatement` is the bounded-reference part of BR3 in driver form: every evolution of
  such a reference word reaches a finite lifetime with positive probability while the removed far-left marks and the
  right marks off the seed stay at a positive distance from the driver (BR3, p. 609: "The original real range of this
  reference lies in `[a, b)`", "All changed groups lie beyond the crosscut and remain separated");
* the transfer is `GW0BadGroup.measure_lifetime_le_ne_zero` (Aux. 108 through a common threshold,
  `GW0BadGroupCompare.lean`) with `Ψ = |W − V_j|`: every reference threshold is at the group of `j`
  (`eq_of_thresholdCondition_ref`), and on a path of the original word the group of `j` at the driver, with the
  changed marks away from it, is the original threshold (`thresholdAtZero_ref`).

## Main results

* `BR3ReferenceStatement` (named input);
* `neg_two_lt_sum_collision_left_of_ne`: a colliding left group before the first bad group end is admissible;
* **`measure_lifetime_lt_top_ne_zero_of_sep`**: for a separated ordered word with a first bad left group end and an
  admissible right seed group, every integrated evolution has a finite lifetime with positive probability.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace GW0BadGroup

open Zhan Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart Girsanov Coupling

/-! ### The reference word and the named input -/

/-- **BR3's reference left weights** at the first bad left group end `j`: the original weights through `j`, `0`
beyond ("Preserve the entire left word through `a` and remove its farther left marks"). -/
def refρL {nL : ℕ} (j : Fin nL) (ρL : Fin nL → ℝ) : Fin nL → ℝ := fun i => if i ≤ j then ρL i else 0

theorem refρL_of_le {nL : ℕ} {j i : Fin nL} (ρL : Fin nL → ℝ) (h : i ≤ j) : refρL j ρL i = ρL i := by
  simp [refρL, h]

theorem refρL_of_lt {nL : ℕ} {j i : Fin nL} (ρL : Fin nL → ℝ) (h : j < i) : refρL j ρL i = 0 := by
  simp [refρL, not_le.2 h]

/-- **Named input: BR3's bounded reference, separated form, in driver form** (supplement pp. 608–609, proof of BR3:
"This reference has a bounded continuous complete history ending exactly at `a` at its finite original continuation
threshold […] The original real range of this reference lies in `[a, b)`"; p. 617, proof of GW0: "The inverse complete
reference is therefore a bounded continuous curve ending exactly at `a`, at its finite original continuation
threshold"). For `k > 4`, a separated ordered word with a left group end `j` whose partial sum is `≤ −2`, every
earlier left group end admissible and an admissible right seed group, there are reference right weights, equal to the
original ones at the seed and with admissible right group ends, such that every integrated evolution of the reference
word (left weights `refρL j ρL`) has, with positive probability, a finite lifetime before which the far-left marks
`i > j` and the right marks off the seed stay at a positive distance from the driver. -/
def BR3ReferenceStatement : Prop :=
  ∀ (k : ℝ), 4 < k → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (j : Fin nL), IsOrderedForceWord xL xR → (∀ i i', xL i < xR i') → (∀ i, j < i → xL i < xL j) →
    ∑ i ∈ univ.filter (· ≤ j), ρL i ≤ -2 →
    (∀ m : Fin nL, (∀ i, m < i → xL i < xL m) → xL j < xL m → -2 < ∑ i ∈ univ.filter (· ≤ m), ρL i) →
    -2 < ∑ i ∈ univ.filter (fun i => xR i = 0), ρR i →
    ∃ ρR' : Fin nR → ℝ, (∀ i, xR i = 0 → ρR' i = ρR i) ∧
      (∀ m : Fin nR, (∀ i, m < i → xR m < xR i) → -2 < ∑ i ∈ univ.filter (· ≤ m), ρR' i) ∧
      ∀ {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
        (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
        (ζ : Ω → ℝ≥0∞), IsIntegratedSLEEvolution k xL xR (refρL j ρL) ρR' P 𝓕 W VL VR B ζ →
        P {ω | ζ ω < ⊤ ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
          (∀ i, j < i → δ ≤ W t ω - VL i t ω) ∧ (∀ i, 0 < xR i → δ ≤ VR i t ω - W t ω)} ≠ 0

/-! ### Colliding groups before the first bad group -/

section Collision

variable {n : ℕ}

/-- **A colliding left group before the first bad group end is admissible**: for antitone positions `x`, antitone
current positions `v₀ ≤ w₀`, constant on coincident marks, if the mark `j` is not at the driver and every group end
strictly right of `x j` has partial sum `> −2`, then the colliding weight exceeds `−2`. -/
theorem neg_two_lt_sum_collision_left_of_ne {ρ x v₀ : Fin n → ℝ} {w₀ : ℝ} (hx : Antitone x) (hv : Antitone v₀)
    (hvw : ∀ i, v₀ i ≤ w₀) (hco : ∀ i i', x i = x i' → v₀ i = v₀ i') (j : Fin n)
    (hadm : ∀ m : Fin n, (∀ i, m < i → x i < x m) → x j < x m → -2 < ∑ i ∈ univ.filter (· ≤ m), ρ i)
    (hj : v₀ j ≠ w₀) : -2 < ∑ i ∈ univ.filter (fun i => v₀ i = w₀), ρ i := by
  set S := univ.filter (fun i => v₀ i = w₀) with hS
  by_cases hne : S.Nonempty
  · set m := S.max' hne
    have hmS : m ∈ S := S.max'_mem hne
    have hm : v₀ m = w₀ := (mem_filter.1 hmS).2
    have hmem : ∀ i, i ∈ S ↔ i ≤ m := fun i => by
      refine ⟨fun hi => S.le_max' i hi, fun hi => ?_⟩
      simp only [hS, mem_filter, Finset.mem_univ, true_and]
      exact le_antisymm (hvw i) (hm ▸ hv hi)
    have hSeq : S = univ.filter (· ≤ m) := by
      ext i; simp only [mem_filter, Finset.mem_univ, true_and]; exact hmem i
    have hend : ∀ i, m < i → x i < x m := by
      intro i hmi
      refine lt_of_le_of_ne (hx hmi.le) fun heq => ?_
      have hiS : i ∈ S := by
        simp only [hS, mem_filter, Finset.mem_univ, true_and]; rw [hco i m heq, hm]
      exact absurd ((hmem i).1 hiS) (not_le.2 hmi)
    have hmj : m < j := by
      by_contra hjm
      exact hj (mem_filter.1 ((hmem j).2 (not_lt.1 hjm))).2
    rw [hSeq]
    exact hadm m hend (hend j hmj)
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne, sum_empty]
    norm_num

end Collision

/-! ### The two threshold facts -/

section Thresholds

variable {k : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {j : Fin nL}

/-- The functional `Ψ = |W − V_j|`. -/
def gapJ (j : Fin nL) (p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : ℝ := |p.1 - p.2.1 j|

theorem continuous_gapJ (j : Fin nL) : Continuous (gapJ (nR := nR) j) := by
  unfold gapJ; fun_prop

/-- **On a path of the original word, the group of `j` at the driver is the original threshold** when every far-left
mark whose weight changes is away from the driver. -/
theorem thresholdAtZero_ref {ρR ρR' : Fin nR → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hL : ∑ i ∈ univ.filter (· ≤ j), ρL i ≤ -2) :
    ThresholdAtZero k xL xR (refρL j ρL) ρL ρR' ρR (gapJ j) δ := by
  intro w vL vR b ζ hp t ht hΨ hgap
  have hwj : vL j t = w t := by
    have h0 : |w t - vL j t| = 0 := le_antisymm hΨ (abs_nonneg _)
    rw [abs_eq_zero, sub_eq_zero] at h0
    exact h0.symm
  have hne := (ne_of_le_chGap hδ (hgap t le_rfl)).1
  have hfp := hp.isForcePath
  left
  have hsub : univ.filter (· ≤ j) ⊆ univ.filter (fun i => vL i t = w t) := by
    intro i hi
    simp only [mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact le_antisymm (hfp.vL_le_w ht i) (hwj ▸ hfp.antitone_vL ht hi)
  rw [← Finset.sum_subset hsub fun i hi hni => ?_]
  · exact hL
  · simp only [mem_filter, Finset.mem_univ, true_and, not_le] at hi hni
    by_contra hρ
    exact hne i (by rw [refρL_of_lt ρL hni]; exact hρ) hi

/-- **Every reference threshold is at the group of `j`**: at an ordered limit state, constant on coincident marks, of
the reference word (earlier left group ends and every right group end admissible), a threshold has `v_j = w`. -/
theorem eq_of_thresholdCondition_ref {ρR' : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR)
    (hadm : ∀ m : Fin nL, (∀ i, m < i → xL i < xL m) → xL j < xL m → -2 < ∑ i ∈ univ.filter (· ≤ m), ρL i)
    (hRadm : ∀ m : Fin nR, (∀ i, m < i → xR m < xR i) → -2 < ∑ i ∈ univ.filter (· ≤ m), ρR' i)
    {w₀ : ℝ} {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ} (hvL : Antitone vL₀) (hvR : Monotone vR₀)
    (hLw : ∀ i, vL₀ i ≤ w₀) (hwR : ∀ i, w₀ ≤ vR₀ i) (hcoL : ∀ i i', xL i = xL i' → vL₀ i = vL₀ i')
    (hcoR : ∀ i i', xR i = xR i' → vR₀ i = vR₀ i')
    (hth : ForceWord.ThresholdCondition (refρL j ρL) ρR' w₀ vL₀ vR₀) : vL₀ j = w₀ := by
  by_contra hne
  have hadm' : ∀ m : Fin nL, (∀ i, m < i → xL i < xL m) → xL j < xL m →
      -2 < ∑ i ∈ univ.filter (· ≤ m), refρL j ρL i := by
    intro m hm hmj
    have hmj' : m < j := by
      by_contra h
      exact absurd (hF.1 (not_lt.1 h)) (not_le.2 hmj)
    rw [Finset.sum_congr rfl fun i hi => refρL_of_le ρL
      ((Finset.mem_filter.1 hi).2.trans hmj'.le)]
    exact hadm m hm hmj
  have hleft := neg_two_lt_sum_collision_left_of_ne hF.1 hvL hLw hcoL j hadm' hne
  obtain ⟨c, hc, hcle⟩ := GW0.exists_neg_two_lt_le (fun m => ∑ i ∈ univ.filter (· ≤ m), ρR' i)
    (fun m => ∀ i, m < i → xR m < xR i) hRadm
  have hright := Sec4.neg_two_lt_sum_collision hc hF.2.2.1 (fun m hm => hcle m hm) hvR hwR hcoR
  rcases hth with h | h <;> linarith

end Thresholds

/-! ### The transfer at a separated start -/

section Sep

variable {k : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {j : Fin nL}

/-- **Lemma GW0, third sentence, at a separated start, from BR3's reference**: for `k > 4`, a separated ordered word
with a left group end `j` of partial sum `≤ −2`, every earlier left group end admissible and an admissible right seed
group, every integrated evolution has a finite lifetime with positive probability. -/
theorem measure_lifetime_lt_top_ne_zero_of_sep (hBR3 : BR3ReferenceStatement) (hk : 4 < k)
    (hF : IsOrderedForceWord xL xR) (hsep : ∀ i i', xL i < xR i') (hj : ∀ i, j < i → xL i < xL j)
    (hL : ∑ i ∈ univ.filter (· ≤ j), ρL i ≤ -2)
    (hadm : ∀ m : Fin nL, (∀ i, m < i → xL i < xL m) → xL j < xL m → -2 < ∑ i ∈ univ.filter (· ≤ m), ρL i)
    (hR0 : -2 < ∑ i ∈ univ.filter (fun i => xR i = 0), ρR i)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P'] {𝓕' : Filtration ℝ≥0 mΩ'}
    {W' : ℝ≥0 → Ω' → ℝ} {VL' : Fin nL → ℝ≥0 → Ω' → ℝ} {VR' : Fin nR → ℝ≥0 → Ω' → ℝ} {B' : ℝ≥0 → Ω' → ℝ}
    {ζ' : Ω' → ℝ≥0∞} (hO : IsIntegratedSLEEvolution k xL xR ρL ρR P' 𝓕' W' VL' VR' B' ζ') :
    P' {ω | ζ' ω < ⊤} ≠ 0 := by
  have hκ : 0 < k := by linarith
  -- an inadmissible seed: the lifetime is `0`
  by_cases hxj : xL j = 0
  · have hset : univ.filter (fun i => xL i = 0) = univ.filter (· ≤ j) := by
      ext i
      simp only [mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun hi => ?_, fun hi => le_antisymm (hF.2.1 i) (hxj ▸ hF.1 hi)⟩
      by_contra hji
      exact absurd (hj i (not_le.1 hji)) (by rw [hi, hxj]; exact lt_irrefl 0)
    have hthr : ForceWord.ThresholdCondition ρL ρR 0 xL xR := Or.inl (by
      show (∑ i ∈ univ.filter (fun i => xL i = 0), ρL i) ≤ -2
      rw [hset]
      exact hL)
    have h0 : ∀ᵐ ω ∂P', ζ' ω = 0 := by
      filter_upwards [hO.2.2.2.2] with ω hω
      exact (GW0.lifetime_eq_zero_iff hω).2 hthr
    intro hP0
    have hn : ∀ᵐ ω ∂P', ω ∉ {ω | ζ' ω < ⊤} := measure_eq_zero_iff_ae_notMem.1 hP0
    obtain ⟨ω, h1, h2⟩ := (h0.and hn).exists
    exact h2 (show ζ' ω < ⊤ by rw [h1]; exact ENNReal.zero_lt_top)
  have hxj' : xL j < 0 := lt_of_le_of_ne (hF.2.1 j) hxj
  obtain ⟨ρR', hR'0, hR'adm, hev⟩ := hBR3 k hk xL xR ρL ρR j hF hsep hj hL hadm hR0
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hF (ρL := refρL j ρL) (ρR := ρR')
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hpos := hev P 𝓕 W VL VR B ζ hE
  have hadm' : ∀ m : Fin nL, (∀ i, m < i → xL i < xL m) → xL j < xL m →
      -2 < ∑ i ∈ univ.filter (· ≤ m), refρL j ρL i := by
    intro m hm hmj
    have hmj' : m < j := by
      by_contra h
      exact absurd (hF.1 (not_lt.1 h)) (not_le.2 hmj)
    rw [Finset.sum_congr rfl fun i hi => refρL_of_le ρL ((Finset.mem_filter.1 hi).2.trans hmj'.le)]
    exact hadm m hm hmj
  -- the reference has no seed threshold
  have hseed : ¬ ForceWord.ThresholdCondition (refρL j ρL) ρR' 0 xL xR := by
    rintro (h | h)
    · exact absurd h (not_le.2 (neg_two_lt_sum_collision_left_of_ne hF.1 hF.1 hF.2.1 (fun _ _ h => h) j hadm'
        (by rw [Ne]; exact hxj)))
    · have e : ∑ i ∈ univ.filter (fun i => xR i = 0), ρR' i = ∑ i ∈ univ.filter (fun i => xR i = 0), ρR i :=
        Finset.sum_congr rfl fun i hi => hR'0 i (Finset.mem_filter.1 hi).2
      have h' : (∑ i ∈ univ.filter (fun i => xR i = 0), ρR' i) ≤ -2 := h
      rw [e] at h'
      linarith
  -- the good event
  set Good : Ω → Prop := fun ω => IsIntegratedSLEPath k xL xR (refρL j ρL) ρR' (fun t => W t ω)
      (fun i t => VL i t ω) (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) ∧
    ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
      ForceWord.ThresholdCondition (refρL j ρL) ρR' w₀ vL₀ vR₀ with hGood
  have hgood : ∀ᵐ ω ∂P, Good ω := hE.ae_isIntegratedSLEPath.and (hE.ae_tendsto_threshold hκ)
  set N := {ω | ¬ Good ω} with hNdef
  have hN : P N = 0 := ae_iff.1 hgood
  set G := (toMeasurable P N)ᶜ with hGdef
  have hGm : MeasurableSet[usualAugmentation 𝓕 P 0] G :=
    (Ito.measurableSet_usualAugmentation_of_null (measurableSet_toMeasurable P N)
      (by rw [measure_toMeasurable]; exact hN) 0).compl
  have hGgood : ∀ ω ∈ G, Good ω := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable P N h)
  have hGc : P Gᶜ = 0 := by rw [hGdef, compl_compl, measure_toMeasurable]; exact hN
  have hGcont : ∀ ω ∈ G, ContinuousOn (fun s => Coupling.stateAt W VL VR s ω) {s | (s : ℝ≥0∞) < ζ ω} := by
    intro ω hω
    obtain ⟨-, -, -, hcw, hcvL, hcvR, -⟩ := (hGgood ω hω).1
    exact hcw.prodMk ((continuousOn_pi.2 hcvL).prodMk (continuousOn_pi.2 hcvR))
  -- `Ψ = |W − V_j|` tends to `0` at every finite lifetime
  have hGΨ : ∀ ω ∈ G, ζ ω ≠ ⊤ → ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω ∧
      gapJ j (Coupling.stateAt W VL VR t ω) < ε := by
    intro ω hω hζ ε hε
    obtain ⟨hp, hlim⟩ := hGgood ω hω
    obtain ⟨T, hT⟩ : ∃ T : ℝ≥0, (T : ℝ≥0∞) = ζ ω := ⟨(ζ ω).toNNReal, ENNReal.coe_toNNReal hζ⟩
    have hT0 : 0 < T := by
      rcases eq_zero_or_pos T with h0 | h0
      · exact absurd ((GW0.lifetime_eq_zero_iff hp).1 (by rw [← hT, h0]; rfl)) hseed
      · exact h0
    obtain ⟨w₀, vL₀, vR₀, hlim', hth⟩ := hlim T hT0 hT
    have : NeBot (𝓝[<] T) := nhdsLT_neBot_of_exists_lt ⟨0, hT0⟩
    have hfp := hp.isForcePath
    have hev : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, (t : ℝ≥0∞) < ζ ω := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [← hT]; exact_mod_cast ht
    have hw : Tendsto (fun t => W t ω) (𝓝[<] T) (𝓝 w₀) := hlim'.fst_nhds
    have hvL : ∀ i, Tendsto (fun t => VL i t ω) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
      tendsto_pi_nhds.1 hlim'.snd_nhds.fst_nhds i
    have hvR : ∀ i, Tendsto (fun t => VR i t ω) (𝓝[<] T) (𝓝 (vR₀ i)) := fun i =>
      tendsto_pi_nhds.1 hlim'.snd_nhds.snd_nhds i
    have hj0 : vL₀ j = w₀ := by
      refine eq_of_thresholdCondition_ref hF hadm hR'adm ?_ ?_ ?_ ?_ ?_ ?_ hth
      · intro i i' hii'
        exact le_of_tendsto_of_tendsto (hvL i') (hvL i) (hev.mono fun t ht => hfp.antitone_vL ht hii')
      · intro i i' hii'
        exact le_of_tendsto_of_tendsto (hvR i) (hvR i') (hev.mono fun t ht => hfp.monotone_vR ht hii')
      · intro i
        exact le_of_tendsto_of_tendsto (hvL i) hw (hev.mono fun t ht => hfp.vL_le_w ht i)
      · intro i
        exact le_of_tendsto_of_tendsto hw (hvR i) (hev.mono fun t ht => hfp.w_le_vR ht i)
      · intro i i' hii'
        exact tendsto_nhds_unique (hvL i)
          ((hvL i').congr' (hev.mono fun t ht => (hp.vL_eq_of_xL_eq ht hii').symm))
      · intro i i' hii'
        exact tendsto_nhds_unique (hvR i)
          ((hvR i').congr' (hev.mono fun t ht => (hp.vR_eq_of_xR_eq ht hii').symm))
    have hΨlim : Tendsto (fun t => gapJ j (Coupling.stateAt W VL VR t ω)) (𝓝[<] T) (𝓝 0) := by
      have h1 := ((continuous_gapJ (nR := nR) j).tendsto (w₀, vL₀, vR₀)).comp hlim'
      have h2 : gapJ (nR := nR) j (w₀, vL₀, vR₀) = 0 := by simp [gapJ, hj0]
      rw [h2] at h1
      exact h1
    obtain ⟨t, ht1, ht2⟩ := ((hΨlim.eventually (gt_mem_nhds hε)).and hev).exists
    exact ⟨t, ht2, ht1⟩
  -- the reference event at some level and horizon
  set A := {ω | ζ ω < ⊤ ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
    (∀ i, j < i → δ ≤ W t ω - VL i t ω) ∧ (∀ i, 0 < xR i → δ ≤ VR i t ω - W t ω)} with hAdef
  set Ev : ℕ → ℕ → Set Ω := fun n M =>
    refEvent (refρL j ρL) ρL ρR' ρR G (1 / ((n : ℝ) + 1)) (M : ℝ≥0) ζ W VL VR with hEv
  have hcover : A ∩ G ⊆ ⋃ n, ⋃ M, Ev n M := by
    rintro ω ⟨⟨hζ, δ, hδ, hgapω⟩, hωG⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min hδ one_pos)
    obtain ⟨M, hM⟩ := exists_nat_gt (ζ ω).toNNReal
    refine mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨M, hωG, ?_, fun t ht => ?_⟩⟩
    · calc ζ ω = (ζ ω).toNNReal := (ENNReal.coe_toNNReal hζ.ne).symm
        _ < (M : ℝ≥0) := by exact_mod_cast hM
    · obtain ⟨hgL, hgR⟩ := hgapω t ht
      have hn1 : 1 / ((n : ℝ) + 1) ≤ δ := (hn.trans_le (min_le_left _ _)).le
      refine le_chGap_iff.2 ⟨(hn.trans_le (min_le_right _ _)).le, fun i hi => ?_, fun i hi => ?_⟩
      · have hji : j < i := by
          by_contra h
          exact hi (refρL_of_le ρL (not_lt.1 h)).symm
        exact hn1.trans ((hgL i hji).trans (le_abs_self _))
      · have hx0 : 0 < xR i := by
          refine lt_of_le_of_ne (hF.2.2.2 i) fun h => hi ?_
          exact (hR'0 i h.symm).symm
        exact hn1.trans ((hgR i hx0).trans (by rw [abs_sub_comm]; exact le_abs_self _))
  obtain ⟨n, M, hnM⟩ : ∃ n M, P (Ev n M) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hpos
    have h1 : P (⋃ n, ⋃ M, Ev n M) = 0 := measure_iUnion_null fun n => measure_iUnion_null fun M => hall n M
    refine measure_mono_null (fun ω hω => ?_) (measure_union_null h1 hGc)
    by_cases hωG : ω ∈ G
    · exact Or.inl (hcover ⟨hω, hωG⟩)
    · exact Or.inr hωG
  have h := measure_lifetime_le_ne_zero hκ hF hsep hE𝓖 hGm hGcont (continuous_gapJ j) hGΨ
    (δ := 1 / ((n : ℝ) + 1)) (by positivity) (M : ℝ≥0) (thresholdAtZero_ref (by positivity) hL) hnM hO
  intro h0
  exact h (measure_mono_null (fun ω hω => lt_of_le_of_lt hω ENNReal.coe_lt_top) h0)

end Sep

/-! ### Two-sided seeds: restarting at a small positive time -/

section Restart

variable {k : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- The realized word of a path before its lifetime is ordered. -/
theorem isOrderedForceWord_at' {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ζ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    IsOrderedForceWord (fun i => vL i t - w t) (fun j => vR j t - w t) := by
  have hf := hp.isForcePath
  refine ⟨fun i i' hii' => ?_, fun i => ?_, fun i i' hii' => ?_, fun i => ?_⟩
  · have := hf.antitone_vL ht hii'; simp only; linarith
  · have := hf.vL_le_w ht i; simp only; linarith
  · have := hf.monotone_vR ht hii'; simp only; linarith
  · have := hf.w_le_vR ht i; simp only; linarith

/-- The restart times `t_n = 1/(n + 1)`. -/
def tn (n : ℕ) : ℝ≥0 := (1 / ((n : ℝ) + 1)).toNNReal

theorem tn_pos (n : ℕ) : 0 < tn n := by
  unfold tn; rw [Real.toNNReal_pos]; positivity

/-- **The first bad left group end**: if the left group ends are not all admissible, there is a left group end `j`
of partial sum `≤ −2` such that every left group end strictly right of `x_j` is admissible. -/
theorem exists_first_bad_left (hx : Antitone xL) (hbad : ¬ GW0.LeftGroupEndsAdmissible xL ρL) :
    ∃ j : Fin nL, (∀ i, j < i → xL i < xL j) ∧ ∑ i ∈ univ.filter (· ≤ j), ρL i ≤ -2 ∧
      ∀ m : Fin nL, (∀ i, m < i → xL i < xL m) → xL j < xL m → -2 < ∑ i ∈ univ.filter (· ≤ m), ρL i := by
  classical
  unfold GW0.LeftGroupEndsAdmissible at hbad
  push Not at hbad
  set S := univ.filter (fun m : Fin nL => (∀ i, m < i → xL i < xL m) ∧ ∑ i ∈ univ.filter (· ≤ m), ρL i ≤ -2)
    with hS
  obtain ⟨j₀, hj₀, hj₀'⟩ := hbad
  have hne : S.Nonempty := ⟨j₀, by simp only [hS, mem_filter, Finset.mem_univ, true_and]; exact ⟨hj₀, hj₀'⟩⟩
  set j := S.min' hne
  have hjS := (mem_filter.1 (S.min'_mem hne)).2
  refine ⟨j, hjS.1, hjS.2, fun m hm hmj => ?_⟩
  by_contra hle
  push Not at hle
  have hmS : m ∈ S := by simp only [hS, mem_filter, Finset.mem_univ, true_and]; exact ⟨hm, hle⟩
  have hjm : j ≤ m := S.min'_le m hmS
  exact absurd (hx hjm) (not_le.2 hmj)

/-- **Lemma GW0, third sentence, for a first bad left group** (from BR3's reference): for `k > 4`, an ordered word
without a threshold at the seed whose left group ends are not all admissible, the lifetime of an integrated evolution
is not almost surely infinite. The evolution is restarted at a small positive time `t_n`, where its word is
separated, the first bad left group end is still a group end (no far-left mark has merged with it yet), and the right
group at the driver is admissible (no threshold before the lifetime); the separated case
(`measure_lifetime_lt_top_ne_zero_of_sep`) and the restart law (`Sec7.RandRestart.restart_core`) conclude. -/
theorem not_ae_lifetime_eq_top_left (hBR3 : BR3ReferenceStatement) (hk : 4 < k) (hF : IsOrderedForceWord xL xR)
    (hbad : ¬ GW0.LeftGroupEndsAdmissible xL ρL) {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) : ¬ (∀ᵐ ω ∂P, ζ ω = ⊤) := by
  intro htop
  have hκ : 0 < k := by linarith
  obtain ⟨j, hj, hL, hadm⟩ := exists_first_bad_left hF.1 hbad
  set S : Set (XCode nL nR) := {x | cζ x < ⊤} with hSdef
  have hSm : MeasurableSet S := measurableSet_lt measurable_cζ measurable_const
  -- the restart at `t_n`
  have hrc : ∀ n : ℕ, ∃ (st : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)) (g : Ω → ℝ≥0 → ℝ) (c : Ω → XCode nL nR),
      Measurable st ∧ Measurable g ∧
      (∀ E : Set (((Fin nL → ℝ) × (Fin nR → ℝ)) × (ℝ≥0 → ℝ)), MeasurableSet E →
        P ({ω | (tn n : ℝ≥0∞) < ζ ω} ∩ (fun ω => (st ω, g ω)) ⁻¹' E) =
          ∫⁻ ω in {ω | (tn n : ℝ≥0∞) < ζ ω}, wienerPath (Prod.mk (st ω) ⁻¹' E) ∂P) ∧
      ∀ᵐ ω ∂P, ω ∈ {ω | (tn n : ℝ≥0∞) < ζ ω} → st ω = wordAt W VL VR (fun _ => tn n) ω ∧ SepStart (st ω) ∧
        c ω ∈ CRel k (st ω).1 (st ω).2 ρL ρR ∧ (c ω).1 = enc (g ω) ∧ cζ (c ω) = ζ ω - tn n ∧
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω - tn n → cw (c ω) t = W (tn n + t) ω - W (tn n) ω) ∧
        HasLimW (c ω) := by
    intro n
    have hT : IsStoppingTime 𝓕 fun _ : Ω => ((tn n : ℝ≥0) : WithTop ℝ≥0) := isStoppingTime_const 𝓕 _
    have hA : MeasurableSet[hT.measurableSpace] {ω | (tn n : ℝ≥0∞) < ζ ω} := by
      rw [show hT.measurableSpace = 𝓕 (tn n) from IsStoppingTime.measurableSpace_const 𝓕 _]
      have := hE.2.1 (tn n) univ MeasurableSet.univ
      simpa only [Set.mem_univ, and_true] using this
    exact restart_core hκ hE hT hA fun ω hω => ⟨hω, Or.inl (tn_pos n)⟩
  choose st g c hstm hgm hlaw hid using hrc
  -- the restarted canonical law of a finite lifetime vanishes
  have hzero : ∀ n : ℕ, ∀ᵐ ω ∂P, ω ∈ {ω | (tn n : ℝ≥0∞) < ζ ω} → codeLaw k ρL ρR S (st n ω) = 0 := by
    intro n
    set A := {ω | (tn n : ℝ≥0∞) < ζ ω} with hAdef
    have hAm : MeasurableSet A := by
      have := hE.2.1 (tn n) univ MeasurableSet.univ
      exact (𝓕.le _ _ (by simpa only [Set.mem_univ, and_true] using this))
    have hE0 : MeasurableSet (restartSetS k ρL ρR S) := measurableSet_restartSetS hSm
    have hP0 : P (A ∩ (fun ω => (st n ω, g n ω)) ⁻¹' restartSetS k ρL ρR S) = 0 := by
      refine measure_eq_zero_iff_ae_notMem.2 ?_
      filter_upwards [hid n, htop] with ω h hζ ⟨hωA, hωE⟩
      obtain ⟨-, hsep, hc, hc1, hcζ, -⟩ := h hωA
      have hmem : ((st n ω), (c n ω).1) ∈ lawSetS k ρL ρR S := by rw [hc1]; exact hωE
      have hxS := (mem_lawSetS_iff hsep hc).1 hmem
      simp only [hSdef, mem_ofPred_eq, hcζ, hζ] at hxS
      exact absurd hxS (by simp)
    rw [hlaw n _ hE0] at hP0
    have hmeas : Measurable fun ω => wienerPath (Prod.mk (st n ω) ⁻¹' restartSetS k ρL ρR S) :=
      (measurable_codeLaw hSm).comp (hstm n)
    have h := (lintegral_eq_zero_iff hmeas).1 hP0
    rw [Filter.EventuallyEq, ae_restrict_iff' hAm] at h
    filter_upwards [h] with ω hω hωA
    exact hω hωA
  -- a good path
  obtain ⟨ω, ⟨hp, hζ⟩, hω⟩ := ((hE.ae_isIntegratedSLEPath.and htop).and (ae_all_iff.2 fun n =>
    (hid n).and (hzero n))).exists
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω := fun t => by rw [hζ]; exact ENNReal.coe_lt_top
  have hfp := hp.isForcePath
  -- for small `t`, no far-left mark has merged with `V_j`
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ≥0), ∀ i, j < i → VL i t ω < VL j t ω := by
    rw [Filter.eventually_all]
    intro i
    by_cases hji : j < i
    · have hci : ContinuousAt (fun t => VL j t ω - VL i t ω) 0 :=
        ((hfp.continuousOn_vL j).continuousAt (IsOpen.mem_nhds (isOpen_lt ENNReal.continuous_coe
          continuous_const) (hlt 0))).sub ((hfp.continuousOn_vL i).continuousAt (IsOpen.mem_nhds
          (isOpen_lt ENNReal.continuous_coe continuous_const) (hlt 0)))
      have h0 : 0 < VL j 0 ω - VL i 0 ω := by
        have e1 : VL j 0 ω = xL j := hp.2.1 j
        have e2 : VL i 0 ω = xL i := hp.2.1 i
        rw [e1, e2]; linarith [hj i hji]
      filter_upwards [hci.eventually (lt_mem_nhds h0)] with t ht _
      linarith
    · exact Eventually.of_forall fun t h => absurd h hji
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  have htn : dist (tn n) 0 < ε := by
    rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, tn, Real.coe_toNNReal _ (by positivity),
      abs_of_pos (by positivity)]
    exact hn
  have hfar := hball htn
  obtain ⟨hid', hcl⟩ := hω n
  obtain ⟨hst', hsep, -⟩ := hid' (hlt _)
  have hcl' := hcl (hlt _)
  set s := st n ω with hsdef
  have hs1 : ∀ i, s.1 i = VL i (tn n) ω - W (tn n) ω := fun i => by rw [hst']; rfl
  have hs2 : ∀ i, s.2 i = VR i (tn n) ω - W (tn n) ω := fun i => by rw [hst']; rfl
  have hFs : IsOrderedForceWord s.1 s.2 := by
    have h := isOrderedForceWord_at' hp (hlt (tn n))
    have e : s = ((fun i => VL i (tn n) ω - W (tn n) ω), fun i => VR i (tn n) ω - W (tn n) ω) := hst'
    rw [e]; exact h
  -- the separated case at the restarted word
  have hjs : ∀ i, j < i → s.1 i < s.1 j := fun i hji => by
    rw [hs1, hs1]; linarith [hfar i hji]
  have hadms : ∀ m : Fin nL, (∀ i, m < i → s.1 i < s.1 m) → s.1 j < s.1 m →
      -2 < ∑ i ∈ univ.filter (· ≤ m), ρL i := by
    intro m hm hmj
    have hmend : ∀ i, m < i → xL i < xL m := by
      intro i hmi
      refine lt_of_le_of_ne (hF.1 hmi.le) fun heq => ?_
      have := hm i hmi
      rw [hs1, hs1, hp.vL_eq_of_xL_eq (hlt _) heq] at this
      exact lt_irrefl _ this
    have hmj' : m < j := by
      by_contra h
      exact absurd (hFs.1 (not_lt.1 h)) (not_le.2 hmj)
    exact hadm m hmend (hmend j hmj')
  have hR0s : -2 < ∑ i ∈ univ.filter (fun i => s.2 i = 0), ρR i := by
    have hnt := hfp.not_threshold (hlt (tn n))
    unfold ForceWord.ThresholdCondition at hnt
    push Not at hnt
    have e : univ.filter (fun i => s.2 i = 0) = univ.filter (fun i => VR i (tn n) ω = W (tn n) ω) := by
      ext i; simp only [mem_filter, Finset.mem_univ, true_and, hs2, sub_eq_zero]
    rw [e]; exact hnt.2
  obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE'⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hFs (ρL := ρL) (ρR := ρR)
  have hpos := measure_lifetime_lt_top_ne_zero_of_sep hBR3 hk hFs hsep hjs hL hadms hR0s hE'
  have heq := measure_eventOf_eq_codeLaw hκ hsep hE' (S := S) (Φ := fun _ τ => τ < ⊤) hSm
    (fun _ _ _ => Iff.rfl) (fun _ _ _ _ h => h)
  exact hpos (heq.trans hcl')

end Restart

/-! ### Lemma GW0's third sentence and forward implication -/

section Assembly

universe u

/-- **Lemma GW0, third sentence, from BR3's bounded reference** (`GW0.GW0SeparatedBadGroupStatement`): a first bad
left group by `not_ae_lifetime_eq_top_left`; a first bad right group by reflection
(`IsIntegratedSLEEvolution.reflect`, "Reflection treats a first bad right group"). -/
theorem gw0SeparatedBadGroupStatement_of_br3 (hBR3 : BR3ReferenceStatement) :
    GW0.GW0SeparatedBadGroupStatement.{u} := by
  intro k hk nL nR xL xR ρL ρR hword _ hbad Ω mΩ P _ 𝓕 W VL VR B ζ h
  by_cases hL : GW0.LeftGroupEndsAdmissible xL ρL
  · have hR : ¬ GW0.RightGroupEndsAdmissible xR ρR := fun hR => hbad ⟨hL, hR⟩
    have hFr : IsOrderedForceWord (-xR) (-xL) :=
      ⟨fun i i' hii' => neg_le_neg (hword.2.2.1 hii'), fun i => neg_nonpos.2 (hword.2.2.2 i),
        fun i i' hii' => neg_le_neg (hword.1 hii'), fun i => neg_nonneg.2 (hword.2.1 i)⟩
    have hbadr : ¬ GW0.LeftGroupEndsAdmissible (-xR) ρR := fun h' =>
      hR fun j hj => h' j fun i hi => neg_lt_neg (hj i hi)
    exact not_ae_lifetime_eq_top_left hBR3 hk hFr hbadr h.reflect
  · exact not_ae_lifetime_eq_top_left hBR3 hk hword hL h

/-- **Lemma GW0, forward implication, from BR3's bounded reference.** -/
theorem gw0ForwardStatement_of_br3 (hBR3 : BR3ReferenceStatement) : GW0.GW0ForwardStatement.{u} :=
  GW0.gw0ForwardStatement_of_separated (gw0SeparatedBadGroupStatement_of_br3 hBR3)

end Assembly

end GW0BadGroup

end Theorem14

end InteractingSLE
