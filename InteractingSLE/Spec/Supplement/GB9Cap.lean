/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ScheduleL25
import Mathlib.Probability.ConditionalExpectation

/-!
# GB9: capacity cannot accumulate in a bounded range

Packet PROVE-T14-TIP6. Theorem GB9 (supplement §8.9, `source/spec/p481-528.md` L1085–L1102, p. 526), paragraph
"Capacity cannot accumulate in a bounded range", in the form reused by the shortcut note (ruling R52,
`source/external/AstraIG1/ig1_shortcuts_audited.txt` §1.2, "Capacity cannot accumulate"). The source argument has four
steps; the stage-independent drift bound (Abel summation, `8M/3 + (4/3) Σ |ρᵢ|`) is `Supp8.gb9_abel_abs_le`,
`Supp8.gb9_initial_le`, and the uniform one-stage estimate is Lemma 5.10 at a stopping time
(`Sec5.crossing_lower_bound_restart`, constant `p₀` depending only on `κ`, the drift bound `C` and a compact interval
`J ⊂ (−2, ∞)` of first right weights, here `J = [−M, M]`). This file proves the other three steps:

* **the conditional geometric estimate** (`measureReal_iInter_Ico_le_pow`, `measure_iInter_Ici_eq_zero`,
  `measure_liminf_eq_zero`): "For integers `n ≥ m ≥ 2`, the conditional probability that all stages through `2n`
  succeed and each of stages `2m, …, 2n` has increment less than one is at most `(1 − p₀)^{n−m+1}`. This follows by
  iterating the conditional estimate; no independence is needed. Let `n → ∞`, then take the union over `m`." Stated for
  increasing σ-algebras `𝓕 j` (the information at the start of stage `j`), events `F j ∈ 𝓕 (j + 1)` (stage `j` succeeds
  with increment less than one) and one-stage estimates `p₀ P(A) ≤ P(A ∩ G j)` for `A ∈ 𝓕 j` with `G j` disjoint from
  `F j` (`G j`: the driver stays in `(−1, 1)` for one unit of relative capacity, so the stage aborts or spends at
  least one unit); the hypothesis shape is that of `Sec5.crossing_lower_bound_restart`;
* **bounded trace range bounds the capacity** (`two_mul_le_of_image_subset_closedBall`,
  `not_isBounded_image_of_forall`): "A bounded trace range would bound its filled hull in a rectangle and hence bound
  its half-plane capacity": `2t = hcap(fill η[0, t]) ≤ 3R²` when `η[0, t] ⊆ B̄(0, R)`;
* **unbounded chart points pull back to the tip** (`mem_closure_image_of_tendsto_cobounded`): "Unbounded points in
  the `ψ` chart pull back to `p` by continuity of `ψ⁻¹` at infinity".
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp8

namespace GB9Cap

/-! ### The conditional geometric estimate -/

section Geometric

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **One stage of the geometric estimate**: if `p₀ P(A) ≤ P(A ∩ G)` for an event `A` and `G` is disjoint from `F`,
then `P(A ∩ F) ≤ (1 − p₀) P(A)`. -/
theorem measureReal_inter_le_of_disjoint [IsFiniteMeasure P] {A F G : Set Ω} (hA : MeasurableSet A)
    (hF : MeasurableSet F)
    (hGF : Disjoint G F) {p₀ : ℝ} (hp : p₀ * P.real A ≤ P.real (A ∩ G)) :
    P.real (A ∩ F) ≤ (1 - p₀) * P.real A := by
  have hdisj : Disjoint (A ∩ G) (A ∩ F) := hGF.mono inter_subset_right inter_subset_right
  have hsum : P.real (A ∩ G) + P.real (A ∩ F) ≤ P.real A := by
    rw [← measureReal_union hdisj (hA.inter hF)]
    exact measureReal_mono (union_subset inter_subset_left inter_subset_left)
  linarith

/-- **The conditional geometric estimate** (GB9, p. 526; shortcut note §1.2): for increasing σ-algebras `𝓕 j`, events
`F j ∈ 𝓕 (j + 1)` and one-stage estimates `P(A ∩ F j) ≤ (1 − p₀) P(A)` for `A ∈ 𝓕 j`, the probability that the
stages `m, …, m + n − 1` all have the event `F` is at most `(1 − p₀)^n`. No independence is used. -/
theorem measureReal_iInter_Ico_le_pow [IsProbabilityMeasure P] {𝓕 : ℕ → MeasurableSpace Ω} (h𝓕 : Monotone 𝓕)
    (h𝓕le : ∀ j, 𝓕 j ≤ mΩ) {F : ℕ → Set Ω} (hF : ∀ j, MeasurableSet[𝓕 (j + 1)] (F j)) {p₀ : ℝ}
    (hp₀ : p₀ ≤ 1) (hstep : ∀ j A, MeasurableSet[𝓕 j] A → P.real (A ∩ F j) ≤ (1 - p₀) * P.real A) (m : ℕ) :
    ∀ n : ℕ, P.real (⋂ j ∈ Finset.Ico m (m + n), F j) ≤ (1 - p₀) ^ n
  | 0 => by
    simp only [add_zero, Finset.Ico_self, Finset.notMem_empty, iInter_of_empty, iInter_univ, pow_zero]
    exact measureReal_le_one
  | n + 1 => by
    have ih := measureReal_iInter_Ico_le_pow h𝓕 h𝓕le hF hp₀ hstep m n
    have hset : (⋂ j ∈ Finset.Ico m (m + (n + 1)), F j) = (⋂ j ∈ Finset.Ico m (m + n), F j) ∩ F (m + n) := by
      ext ω
      simp only [mem_iInter, Finset.mem_Ico, mem_inter_iff]
      constructor
      · intro h
        exact ⟨fun j hj => h j ⟨hj.1, by omega⟩, h (m + n) ⟨by omega, by omega⟩⟩
      · rintro ⟨h, h'⟩ j hj
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 (show j < m + n + 1 by omega)) with hlt | rfl
        · exact h j ⟨hj.1, hlt⟩
        · exact h'
    have hA : MeasurableSet[𝓕 (m + n)] (⋂ j ∈ Finset.Ico m (m + n), F j) :=
      Finset.measurableSet_biInter _ fun j hj => h𝓕 (show j + 1 ≤ m + n by
        have := (Finset.mem_Ico.1 hj).2; omega) _ (hF j)
    rw [hset, pow_succ]
    calc P.real ((⋂ j ∈ Finset.Ico m (m + n), F j) ∩ F (m + n))
        ≤ (1 - p₀) * P.real (⋂ j ∈ Finset.Ico m (m + n), F j) := hstep _ _ hA
      _ ≤ (1 - p₀) * (1 - p₀) ^ n := mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (1 - p₀) ^ n * (1 - p₀) := mul_comm _ _

/-- **Perpetual failure of the one-unit test has probability zero**: with `0 < p₀ ≤ 1`, almost surely not every stage
from `m` on has the event `F`. -/
theorem measure_iInter_Ici_eq_zero [IsProbabilityMeasure P] {𝓕 : ℕ → MeasurableSpace Ω} (h𝓕 : Monotone 𝓕)
    (h𝓕le : ∀ j, 𝓕 j ≤ mΩ) {F : ℕ → Set Ω} (hF : ∀ j, MeasurableSet[𝓕 (j + 1)] (F j)) {p₀ : ℝ}
    (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1)
    (hstep : ∀ j A, MeasurableSet[𝓕 j] A → P.real (A ∩ F j) ≤ (1 - p₀) * P.real A) (m : ℕ) :
    P (⋂ j ≥ m, F j) = 0 := by
  have hle : ∀ n : ℕ, P.real (⋂ j ≥ m, F j) ≤ (1 - p₀) ^ n := fun n =>
    (measureReal_mono fun ω hω => by
      simp only [mem_iInter, Finset.mem_Ico] at hω ⊢
      exact fun j hj => hω j hj.1).trans (measureReal_iInter_Ico_le_pow h𝓕 h𝓕le hF hp₀1 hstep m n)
  have htend : Tendsto (fun n : ℕ => (1 - p₀) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  have h0 : P.real (⋂ j ≥ m, F j) ≤ 0 := ge_of_tendsto' htend hle
  have h0' : P.real (⋂ j ≥ m, F j) = 0 := le_antisymm h0 measureReal_nonneg
  rwa [measureReal_eq_zero_iff] at h0'

/-- **Only finitely many one-unit failures… almost never**: with `0 < p₀ ≤ 1`, almost surely the event `F` fails at
infinitely many stages (`P(liminf F) = 0`). On perpetual success, infinitely many stages then spend at least one unit
of relative capacity, so the total relative capacity is infinite. -/
theorem measure_liminf_eq_zero [IsProbabilityMeasure P] {𝓕 : ℕ → MeasurableSpace Ω} (h𝓕 : Monotone 𝓕)
    (h𝓕le : ∀ j, 𝓕 j ≤ mΩ) {F : ℕ → Set Ω} (hF : ∀ j, MeasurableSet[𝓕 (j + 1)] (F j)) {p₀ : ℝ}
    (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1)
    (hstep : ∀ j A, MeasurableSet[𝓕 j] A → P.real (A ∩ F j) ≤ (1 - p₀) * P.real A) :
    P (⋃ m, ⋂ j ≥ m, F j) = 0 :=
  measure_iUnion_null fun m => measure_iInter_Ici_eq_zero h𝓕 h𝓕le hF hp₀ hp₀1 hstep m

/-- **The geometric estimate in the form of Lemma 5.10** (`Sec5.crossing_lower_bound_restart`): one-stage lower bounds
`p₀ P(A) ≤ P(A ∩ G j)` for `A ∈ 𝓕 j`, with `G j` disjoint from `F j`, give `P(liminf F) = 0`. -/
theorem measure_liminf_eq_zero_of_lower [IsProbabilityMeasure P] {𝓕 : ℕ → MeasurableSpace Ω} (h𝓕 : Monotone 𝓕)
    (h𝓕le : ∀ j, 𝓕 j ≤ mΩ) {F G : ℕ → Set Ω} (hF : ∀ j, MeasurableSet[𝓕 (j + 1)] (F j))
    (hGF : ∀ j, Disjoint (G j) (F j)) {p₀ : ℝ} (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1)
    (hlow : ∀ j A, MeasurableSet[𝓕 j] A → p₀ * P.real A ≤ P.real (A ∩ G j)) :
    P (⋃ m, ⋂ j ≥ m, F j) = 0 :=
  measure_liminf_eq_zero h𝓕 h𝓕le hF hp₀ hp₀1 fun j A hA =>
    measureReal_inter_le_of_disjoint (h𝓕le j _ hA) (h𝓕le (j + 1) _ (hF j)) (hGF j) (hlow j A hA)

end Geometric

/-! ### Bounded range, bounded capacity -/

section Capacity

open Lemma25

/-- **A bounded trace range bounds the half-plane capacity** (GB9, p. 526: "a bounded trace range bounds its filled
hull in a bounded rectangle and hence bounds its half-plane capacity"): if `η[0, t] ⊆ B̄(0, R)` then
`2t = hcap(fill η[0, t]) ≤ 3R²`. -/
theorem two_mul_le_of_image_subset_closedBall {W : ℝ → ℝ} {T : ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTraceLT W T η)
    (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) {R : ℝ} (hR : 0 < R)
    (hsub : η '' Icc 0 t ⊆ Metric.closedBall 0 R) : 2 * t ≤ 3 * R ^ 2 := by
  have hb := isBounded_image_Icc hη le_rfl htT
  have hc := isPreconnected_image_Icc_zero_union hη ht htT
  rw [← hcapFill_image_Icc hη hW hW0 ht htT hb hc]
  have hrect : η '' Icc 0 t ⊆ {z : ℂ | |z.re| ≤ R ∧ |z.im| ≤ R} := fun z hz => by
    have h := Metric.mem_closedBall.1 (hsub hz)
    rw [dist_zero_right] at h
    exact ⟨(Complex.abs_re_le_norm z).trans h, (Complex.abs_im_le_norm z).trans h⟩
  have := hcapFill_le_of_subset_rect hb hc hR hR hrect
  nlinarith

/-- **Infinite capacity forces an unbounded range** (GB9, p. 526: "Infinite capacity therefore forces the union of the
successful trace ranges to be unbounded"): a trace generating the Loewner chain of `W` for all times has an unbounded
range. -/
theorem not_isBounded_image_of_forall {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : ∀ T : ℝ, IsLoewnerTraceLT W T η)
    (hW : Continuous W) (hW0 : W 0 = 0) : ¬ Bornology.IsBounded (η '' Ici 0) := by
  intro hb
  obtain ⟨R, hR, hsub⟩ := hb.subset_closedBall_lt 0 0
  have := two_mul_le_of_image_subset_closedBall (hη (3 * R ^ 2 + 1)) hW hW0 (t := 3 * R ^ 2) (by positivity)
    (by linarith) hR ((image_mono Icc_subset_Ici_self).trans hsub)
  nlinarith

end Capacity

/-! ### Unbounded chart points pull back to the tip -/

/-- **Unbounded points in the chart pull back to the tip** (GB9, p. 526: "Unbounded points in the `ψ` chart pull back
to `p` by continuity of `ψ⁻¹` at infinity"): if `f` (the inverse chart) tends to `p` at infinity within `D`, then for
every unbounded `T ⊆ D`, `p` lies in the closure of `f(T)`. -/
theorem mem_closure_image_of_tendsto_cobounded {X : Type*} [TopologicalSpace X] {f : ℂ → X} {p : X} {D T : Set ℂ}
    (hf : Tendsto f (Bornology.cobounded ℂ ⊓ 𝓟 D) (𝓝 p)) (hTD : T ⊆ D) (hT : ¬ Bornology.IsBounded T) :
    p ∈ closure (f '' T) := by
  have hne : (Bornology.cobounded ℂ ⊓ 𝓟 T).NeBot := by
    rw [inf_principal_neBot_iff]
    intro U hU
    by_contra hemp
    apply hT
    have hUc : Bornology.IsBounded Uᶜ := Bornology.isBounded_def.2 (by rwa [compl_compl])
    refine hUc.subset fun z hz hzU => hemp ⟨z, hzU, hz⟩
  exact mem_closure_of_tendsto (hf.mono_left (inf_le_inf_left _ (principal_mono.2 hTD)))
    (eventually_inf_principal.2 (Eventually.of_forall fun z hz => mem_image_of_mem f hz))

end GB9Cap

end Supp8

end InteractingSLE
