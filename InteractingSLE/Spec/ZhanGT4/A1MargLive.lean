/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1MargSpace
import InteractingSLE.Spec.ZhanGT4.A1CanonCore

/-!
# (m1)–(m2): the live events and image words of a regular marginal are progressive

Packet PROVE-A1-MARG (R76). Clauses (m1)–(m2) of `A1Core.IsRectImageCore`: the indicator of the live event and the
random image words `ΘL`, `ΘR` of the conditioning curve are strongly progressive for the usual augmentation of its
filtration. For a regular marginal (`IsRegMarginal`: solution paths at every sample, progressive coordinates):

* `isStronglyProgressive_indicator_lt`: the indicator of `{t < ζ}`;
* `isStronglyProgressive_indicator_isStripLife`: the indicator of the strip life `{t < ζ, V < W on [0, t]}` (a
  countable formula, `A1RefCD.isStripLife_iff_nnrat`, with the progressive values at the stopped rational times);
* `isStronglyProgressive_of_measurable`, `isStronglyProgressive_vec`: vectors of progressive real processes;
* `isStronglyProgressive_usualAugmentation`: the passage to the usual augmentation.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Marg

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- A strongly progressive real process is jointly measurable on `[0, t] × Ω` for the filtration at `t`. -/
theorem measurable_prod_of_isStronglyProgressive {u : ℝ≥0 → Ω → ℝ} (h : IsStronglyProgressive 𝓕 u) (t : ℝ≥0) :
    Measurable[(inferInstance : MeasurableSpace (Iic t)).prod (𝓕 t)] fun p : Iic t × Ω => u p.1 p.2 :=
  (h t).measurable

/-- A process with values in a second countable metrizable Borel space is strongly progressive as soon as it is
jointly measurable on each `[0, t] × Ω`. -/
theorem isStronglyProgressive_of_measurable {β : Type*} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] [SecondCountableTopology β] {u : ℝ≥0 → Ω → β}
    (h : ∀ t : ℝ≥0, Measurable[(inferInstance : MeasurableSpace (Iic t)).prod (𝓕 t)]
      fun p : Iic t × Ω => u p.1 p.2) : IsStronglyProgressive 𝓕 u := fun t =>
  (h t).stronglyMeasurable

/-- Measurability into `Fin n → ℝ` from the coordinates, for an explicit σ-algebra on the domain. -/
theorem measurable_vec_of {α : Type*} (m : MeasurableSpace α) {n : ℕ} {g : α → Fin n → ℝ}
    (h : ∀ i, Measurable[m] fun x => g x i) : Measurable[m] g := by
  let _ : MeasurableSpace α := m
  exact Measurable.of_eval h

/-- A vector of strongly progressive real processes is strongly progressive. -/
theorem isStronglyProgressive_vec {n : ℕ} {Θ : ℝ≥0 → Ω → Fin n → ℝ}
    (h : ∀ i, IsStronglyProgressive 𝓕 fun t ω => Θ t ω i) : IsStronglyProgressive 𝓕 Θ :=
  isStronglyProgressive_of_measurable fun t =>
    measurable_vec_of _ fun i => measurable_prod_of_isStronglyProgressive (h i) t

/-- Differences of strongly progressive real processes. -/
theorem isStronglyProgressive_sub_real {u v : ℝ≥0 → Ω → ℝ} (hu : IsStronglyProgressive 𝓕 u)
    (hv : IsStronglyProgressive 𝓕 v) : IsStronglyProgressive 𝓕 fun t ω => u t ω - v t ω :=
  isStronglyProgressive_of_measurable fun t =>
    (measurable_prod_of_isStronglyProgressive hu t).sub (measurable_prod_of_isStronglyProgressive hv t)

/-- Passage to the usual augmentation. -/
theorem isStronglyProgressive_usualAugmentation {β : Type*} [TopologicalSpace β] {u : ℝ≥0 → Ω → β}
    (h : IsStronglyProgressive 𝓕 u) (P : Measure Ω) : IsStronglyProgressive (usualAugmentation 𝓕 P) u :=
  A1Canon.isStronglyProgressive_mono h (Ito.le_usualAugmentation 𝓕 P)

/-- **The indicator of `{t < ζ}` is strongly progressive** for a filtration in which `{t < ζ} ∈ 𝓕_t`. -/
theorem isStronglyProgressive_indicator_lt {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} (ha : AdaptedBefore 𝓕 ζ W) :
    IsStronglyProgressive 𝓕 fun t ω => {ω | (t : ℝ≥0∞) < ζ ω}.indicator (fun _ => (1 : ℝ)) ω := by
  refine isStronglyProgressive_of_measurable fun t => ?_
  have e : (fun p : Iic t × Ω => {ω | (p.1.val : ℝ≥0∞) < ζ ω}.indicator (fun _ => (1 : ℝ)) p.2) =
      {p : Iic t × Ω | (p.1.val : ℝ≥0∞) < ζ p.2}.indicator fun _ => (1 : ℝ) := by
    funext p
    by_cases hp : (p.1.val : ℝ≥0∞) < ζ p.2
    · rw [indicator_of_mem (show p.2 ∈ {ω | (p.1.val : ℝ≥0∞) < ζ ω} from hp),
        indicator_of_mem (show p ∈ {p : Iic t × Ω | (p.1.val : ℝ≥0∞) < ζ p.2} from hp)]
    · rw [indicator_of_notMem (show p.2 ∉ {ω | (p.1.val : ℝ≥0∞) < ζ ω} from hp),
        indicator_of_notMem (show p ∉ {p : Iic t × Ω | (p.1.val : ℝ≥0∞) < ζ p.2} from hp)]
  rw [e]
  exact measurable_const.indicator (measurableSet_lt_lifetime_prod ha t)

/-- The stop of `[0, t]` at `min q ·` as a measurable self-map of `[0, t] × Ω`. -/
theorem measurable_minStop (t q : ℝ≥0) :
    Measurable[(inferInstance : MeasurableSpace (Iic t)).prod (𝓕 t),
      (inferInstance : MeasurableSpace (Iic t)).prod (𝓕 t)]
      fun p : Iic t × Ω => ((⟨min q p.1.val, mem_Iic.2 ((min_le_right _ _).trans p.1.2)⟩ : Iic t), p.2) := by
  have hc : Measurable fun s : Iic t => (⟨min q s.val, mem_Iic.2 ((min_le_right _ _).trans s.2)⟩ : Iic t) :=
    ((continuous_const.min continuous_subtype_val).subtype_mk _).measurable
  exact (hc.comp measurable_fst).prodMk measurable_snd

/-- **The indicator of the strip life is strongly progressive** when the driver and the mark are strongly
progressive and continuous before the lifetime at every sample. -/
theorem isStronglyProgressive_indicator_isStripLife {ζ : Ω → ℝ≥0∞} {W V : ℝ≥0 → Ω → ℝ}
    (hWa : AdaptedBefore 𝓕 ζ W) (hWp : IsStronglyProgressive 𝓕 W) (hVp : IsStronglyProgressive 𝓕 V)
    (hcW : ∀ ω, ContinuousOn (W · ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hcV : ∀ ω, ContinuousOn (V · ω) {s | (s : ℝ≥0∞) < ζ ω}) :
    IsStronglyProgressive 𝓕 fun t ω =>
      {ω | Strip.IsStripLife (W · ω) (V · ω) (ζ ω) t}.indicator (fun _ => (1 : ℝ)) ω := by
  refine isStronglyProgressive_of_measurable fun t => ?_
  set S : Set (Iic t × Ω) := {p | Strip.IsStripLife (W · p.2) (V · p.2) (ζ p.2) p.1.val} with hSdef
  have e : (fun p : Iic t × Ω => {ω | Strip.IsStripLife (W · ω) (V · ω) (ζ ω) p.1.val}.indicator
      (fun _ => (1 : ℝ)) p.2) = S.indicator fun _ => (1 : ℝ) := by
    funext p
    by_cases hp : p ∈ S
    · rw [indicator_of_mem hp, indicator_of_mem (show p.2 ∈ {ω | Strip.IsStripLife (W · ω) (V · ω) (ζ ω)
        p.1.val} from hp)]
    · rw [indicator_of_notMem hp, indicator_of_notMem (show p.2 ∉ {ω | Strip.IsStripLife (W · ω) (V · ω) (ζ ω)
        p.1.val} from hp)]
  rw [e]
  refine measurable_const.indicator ?_
  have hS : S = {p : Iic t × Ω | (p.1.val : ℝ≥0∞) < ζ p.2} ∩ ⋃ n : ℕ, ⋂ q : ℚ≥0,
      {p : Iic t × Ω | 1 / (n + 1 : ℝ) ≤ W (min (q : ℝ≥0) p.1.val) p.2 - V (min (q : ℝ≥0) p.1.val) p.2} := by
    ext p
    simp only [hSdef, mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter]
    exact A1RefCD.isStripLife_iff_nnrat (hcW p.2) (hcV p.2)
  rw [hS]
  refine (measurableSet_lt_lifetime_prod hWa t).inter (MeasurableSet.iUnion fun n => MeasurableSet.iInter fun q => ?_)
  have hW' := (measurable_prod_of_isStronglyProgressive hWp t).comp (measurable_minStop (𝓕 := 𝓕) t q)
  have hV' := (measurable_prod_of_isStronglyProgressive hVp t).comp (measurable_minStop (𝓕 := 𝓕) t q)
  exact measurableSet_le measurable_const (hW'.sub hV')

end InteractingSLE.ZhanGT4.A1Marg
