/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.AddMarksGirsanov
import InteractingSLE.Spec.Sec2.AddMarksFlow
import InteractingSLE.Frozen.Spec.IsOrderedForceWord

/-!
# Merging a reference evolution with added marks into one ordered force word; local existence

Packet PROVE-SEC2-GIR2. Specification, proof of Theorem 2.2 (`source/spec/p001-048.md` L486, L548):
"one can obtain existence of a process with the properties above, defined up until the first time
that one of the *other* force points collides with `W_t`, using a Girsanov transformation … applied
to the standard one-force-point `SLE_κ(ρ)` that one would obtain if `V_0^{1,R}` were the only force
point", and "the extension from two force points (both at the origin) to many force points … is the
same Girsanov argument".

The full force word `(xL; xR)` (ordered, frozen `IsOrderedForceWord`) is split into the marks of a
reference sub-word, given by injections `eL : Fin kL → Fin nL`, `eR : Fin kR → Fin nR` (one right
mark for the one-force-point reference, the two seeds for the two-seed reference, any active group
in the iteration), and the other ("added") marks.

* `Sec2.IsPassiveLeft` / `IsPassiveRight`: a mark that follows the Loewner flow
  `v = x + ∫ 2/(v − w)` at distance `≥ δ` from the driver before `τ`;
* `IsSLEPathUpTo.of_passive`: a local path of the reference sub-word together with passive added
  marks is a local path of the full word, the added marks having weight `0`
  (`Function.extend eL ρL₀ 0`). The side ordering of the full word comes from
  `le_of_forceEq_left` / `le_of_forceEq_right`;
* `isPassiveLeft_markFlow` / `isPassiveRight_markFlow`: the marks `markFlow` solved pathwise
  (`AddMarksFlow`) are passive while they stay at distance `≥ δ`;
* `IsSLEEvolutionUpTo.of_passive`: the same for evolutions;
* `IsSLEEvolutionUpTo.exists_addMarks`: **local existence with the added marks** (the graph node
  "Adding separated force points by Girsanov", localized at a bounded stopping time before the
  added marks come within `δ` of the driver): from a local evolution of the reference sub-word, the
  added marks solved pathwise, and the Girsanov change of their weights from `0` to their weights in
  the full word, the processes are, under an equivalent probability measure, a local evolution of
  the full ordered force word before `τ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

/-! ### Passive marks and the facts used for every mark -/

/-- A mark on the left of the driver that follows the Loewner flow `v = x + ∫ 2/(v − w)` and stays at
distance `≥ δ` from `w` before `τ`. -/
structure IsPassiveLeft (w v : ℝ≥0 → ℝ) (x δ : ℝ) (τ : ℝ≥0∞) : Prop where
  zero : v 0 = x
  continuousOn : ContinuousOn v {t | (t : ℝ≥0∞) < τ}
  eq : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ →
    v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal)
  gap : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → δ ≤ w t - v t

/-- A mark on the right of the driver that follows the Loewner flow `v = x + ∫ 2/(v − w)` and stays at
distance `≥ δ` from `w` before `τ`. -/
structure IsPassiveRight (w v : ℝ≥0 → ℝ) (x δ : ℝ) (τ : ℝ≥0∞) : Prop where
  zero : v 0 = x
  continuousOn : ContinuousOn v {t | (t : ℝ≥0∞) < τ}
  eq : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ →
    v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal)
  gap : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → δ ≤ v t - w t

/-- The conditions of Definition 2.1 on one left mark. -/
structure LeftMarkFacts (w v : ℝ≥0 → ℝ) (x : ℝ) (τ : ℝ≥0∞) : Prop where
  zero : v 0 = x
  continuousOn : ContinuousOn v {t | (t : ℝ≥0∞) < τ}
  le_w : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → v t ≤ w t
  integrable : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ →
    IntervalIntegrable (fun s : ℝ => (w s.toNNReal - v s.toNNReal)⁻¹) volume 0 t
  eq : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ →
    v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal)
  collision : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < τ ∧ w s.toNNReal = v s.toNNReal} = 0

/-- The conditions of Definition 2.1 on one right mark. -/
structure RightMarkFacts (w v : ℝ≥0 → ℝ) (x : ℝ) (τ : ℝ≥0∞) : Prop where
  zero : v 0 = x
  continuousOn : ContinuousOn v {t | (t : ℝ≥0∞) < τ}
  w_le : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → w t ≤ v t
  integrable : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ →
    IntervalIntegrable (fun s : ℝ => (w s.toNNReal - v s.toNNReal)⁻¹) volume 0 t
  eq : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ →
    v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal)
  collision : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < τ ∧ w s.toNNReal = v s.toNNReal} = 0

variable {w v : ℝ≥0 → ℝ} {x δ : ℝ} {τ : ℝ≥0∞}

/-- `2/(v − w)` is integrable when `(w − v)⁻¹` is. -/
theorem intervalIntegrable_two_div {t : ℝ}
    (h : IntervalIntegrable (fun s : ℝ => (w s.toNNReal - v s.toNNReal)⁻¹) volume 0 t) :
    IntervalIntegrable (fun s : ℝ => 2 / (v s.toNNReal - w s.toNNReal)) volume 0 t := by
  have e : (fun s : ℝ => 2 / (v s.toNNReal - w s.toNNReal))
      = fun s : ℝ => (-2) * (w s.toNNReal - v s.toNNReal)⁻¹ := by
    funext s
    rw [div_eq_mul_inv, ← neg_sub, inv_neg]
    ring
  rw [e]
  exact h.const_mul _

/-- The gap of a mark at distance `≥ δ > 0` from a driver continuous before `τ` has an integrable
reciprocal on every `[0, t]`, `t < τ`. -/
theorem intervalIntegrable_inv_of_gap (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < τ})
    (hvc : ContinuousOn v {t | (t : ℝ≥0∞) < τ}) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → δ ≤ |w t - v t|) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ) :
    IntervalIntegrable (fun s : ℝ => (w s.toNNReal - v s.toNNReal)⁻¹) volume 0 t := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le t.coe_nonneg]
  refine ((continuousOn_toNNReal hwc ht).sub (continuousOn_toNNReal hvc ht)).inv₀ fun s hs => ?_
  have hs' : (s.toNNReal : ℝ≥0∞) < τ :=
    lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) ht
  have := hgap hs'
  intro h0
  have h0' : w s.toNNReal - v s.toNNReal = 0 := h0
  rw [h0', abs_zero] at this
  linarith

theorem IsPassiveLeft.leftMarkFacts (h : IsPassiveLeft w v x δ τ)
    (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < τ}) (hδ : 0 < δ) : LeftMarkFacts w v x τ where
  zero := h.zero
  continuousOn := h.continuousOn
  le_w := fun ht => by linarith [h.gap ht]
  integrable := fun ht => intervalIntegrable_inv_of_gap hwc h.continuousOn hδ
    (fun hs => (h.gap hs).trans (le_abs_self _)) ht
  eq := h.eq
  collision := by
    convert measure_empty (μ := (volume : Measure ℝ))
    refine eq_empty_of_forall_notMem fun s ⟨_, hs, he⟩ => ?_
    have := h.gap hs
    rw [he, sub_self] at this
    linarith

theorem IsPassiveRight.rightMarkFacts (h : IsPassiveRight w v x δ τ)
    (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < τ}) (hδ : 0 < δ) : RightMarkFacts w v x τ where
  zero := h.zero
  continuousOn := h.continuousOn
  w_le := fun ht => by linarith [h.gap ht]
  integrable := fun ht => intervalIntegrable_inv_of_gap hwc h.continuousOn hδ
    (fun hs => by rw [abs_sub_comm]; exact (h.gap hs).trans (le_abs_self _)) ht
  eq := h.eq
  collision := by
    convert measure_empty (μ := (volume : Measure ℝ))
    refine eq_empty_of_forall_notMem fun s ⟨_, hs, he⟩ => ?_
    have := h.gap hs
    rw [he, sub_self] at this
    linarith

variable {a : ℝ} {nL nR kL kR : ℕ}

theorem IsSLEPathUpTo.leftMarkFacts {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) (i : Fin nL) :
    LeftMarkFacts w (vL i) (xL i) τ :=
  ⟨h.vL_zero i, h.continuousOn_vL i, fun ht => h.vL_le_w ht i, fun ht => h.integrable_gapL ht i,
    fun ht => h.vL_eq ht i, h.volume_collisionL i⟩

theorem IsSLEPathUpTo.rightMarkFacts {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) (i : Fin nR) :
    RightMarkFacts w (vR i) (xR i) τ :=
  ⟨h.vR_zero i, h.continuousOn_vR i, fun ht => h.w_le_vR ht i, fun ht => h.integrable_gapR ht i,
    fun ht => h.vR_eq ht i, h.volume_collisionR i⟩

/-! ### Sums over extended weights -/

/-- Weights extended by `0` off the image of an injection. -/
theorem sum_extend_mul {k n : ℕ} {e : Fin k → Fin n} (he : Function.Injective e)
    (ρ₀ : Fin k → ℝ) (g : Fin n → ℝ) :
    ∑ i, Function.extend e ρ₀ 0 i * g i = ∑ j, ρ₀ j * g (e j) := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨e, he⟩)), Finset.sum_map]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.Embedding.coeFn_mk, he.extend_apply]
  · intro i _ hi
    have hne : ¬ ∃ j, e j = i := fun ⟨j, hj⟩ =>
      hi (Finset.mem_map.2 ⟨j, Finset.mem_univ _, hj⟩)
    rw [Function.extend_apply' _ _ _ hne, Pi.zero_apply, zero_mul]

theorem sum_filter_extend {k n : ℕ} {e : Fin k → Fin n} (he : Function.Injective e)
    (ρ₀ : Fin k → ℝ) (p : Fin n → Prop) [DecidablePred p] :
    ∑ i ∈ Finset.univ.filter p, Function.extend e ρ₀ 0 i
      = ∑ j ∈ Finset.univ.filter (fun j => p (e j)), ρ₀ j := by
  rw [Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨e, he⟩)), Finset.sum_map]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.Embedding.coeFn_mk, he.extend_apply]
  · intro i _ hi
    have hne : ¬ ∃ j, e j = i := fun ⟨j, hj⟩ =>
      hi (Finset.mem_map.2 ⟨j, Finset.mem_univ _, hj⟩)
    rw [Function.extend_apply' _ _ _ hne, Pi.zero_apply, ite_self]

/-! ### Merging the reference path with passive marks -/

/-- **A reference local path and passive added marks form a local path of the full word.** Let
`(xL; xR)` be an ordered force word, `eL`, `eR` injections onto the marks of a reference sub-word,
and let `(w, v ∘ e, b)` be a local path of the sub-word with weights `(ρL₀; ρR₀)` before `τ`. If every
other mark is passive before `τ` (Loewner flow at distance `≥ δ > 0`), then `(w, v, b)` is a local
path of the full word with the weights `ρ₀` on the reference marks and `0` on the added marks. -/
theorem IsSLEPathUpTo.of_passive {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {eL : Fin kL → Fin nL} {eR : Fin kR → Fin nR}
    (heL : Function.Injective eL) (heR : Function.Injective eR) {ρL₀ : Fin kL → ℝ}
    {ρR₀ : Fin kR → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (hδ : 0 < δ)
    (href : IsSLEPathUpTo a (fun j => xL (eL j)) (fun j => xR (eR j)) ρL₀ ρR₀ w
      (fun j => vL (eL j)) (fun j => vR (eR j)) b τ)
    (hpL : ∀ i, (∀ j, eL j ≠ i) → IsPassiveLeft w (vL i) (xL i) δ τ)
    (hpR : ∀ i, (∀ j, eR j ≠ i) → IsPassiveRight w (vR i) (xR i) δ τ) :
    IsSLEPathUpTo a xL xR (Function.extend eL ρL₀ 0) (Function.extend eR ρR₀ 0) w vL vR b τ := by
  have hL : ∀ i, LeftMarkFacts w (vL i) (xL i) τ := fun i => by
    by_cases h : ∃ j, eL j = i
    · obtain ⟨j, rfl⟩ := h
      exact href.leftMarkFacts j
    · exact (hpL i fun j hj => h ⟨j, hj⟩).leftMarkFacts href.continuousOn_w hδ
  have hR : ∀ i, RightMarkFacts w (vR i) (xR i) τ := fun i => by
    by_cases h : ∃ j, eR j = i
    · obtain ⟨j, rfl⟩ := h
      exact href.rightMarkFacts j
    · exact (hpR i fun j hj => h ⟨j, hj⟩).rightMarkFacts href.continuousOn_w hδ
  refine ⟨href.w_zero, fun i => (hL i).zero, fun i => (hR i).zero, href.continuousOn_w,
    fun i => (hL i).continuousOn, fun i => (hR i).continuousOn, ?_, fun ht i => (hL i).le_w ht,
    fun ht i => (hR i).w_le ht, ?_, fun ht i => (hL i).integrable ht,
    fun ht i => (hR i).integrable ht, fun {t} ht => ?_, fun ht i => (hL i).eq ht,
    fun ht i => (hR i).eq ht, fun i => (hL i).collision, fun i => (hR i).collision,
    fun {t} ht => ?_⟩
  · intro t ht i i' hii'
    exact le_of_forceEq_left (hF.1 hii') (hL i).continuousOn (hL i').continuousOn (hL i).eq
      (hL i').eq (fun hs => intervalIntegrable_two_div ((hL i).integrable hs))
      (fun hs => intervalIntegrable_two_div ((hL i').integrable hs)) (hL i').le_w
      (hL i').collision ht
  · intro t ht i i' hii'
    exact le_of_forceEq_right (hF.2.2.1 hii') (hR i').continuousOn (hR i).continuousOn (hR i').eq
      (hR i).eq (fun hs => intervalIntegrable_two_div ((hR i').integrable hs))
      (fun hs => intervalIntegrable_two_div ((hR i).integrable hs)) (hR i').w_le
      (hR i').collision ht
  · have hw := href.w_eq ht
    simp only [sum_integral_div_eq] at hw ⊢
    rw [sum_extend_mul heL, sum_extend_mul heR]
    exact hw
  · have h := href.not_threshold ht
    unfold ForceWord.ThresholdCondition at h ⊢
    rw [sum_filter_extend heL, sum_filter_extend heR]
    exact h

end Sec2

/-! ### Evolutions: passive marks solved pathwise, and local existence with added marks -/

open Girsanov

namespace Sec2

section Evolution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ τ : Ω → ℝ≥0∞} {nL nR kL kR : ℕ}

/-- The added mark on the left with initial position `y`, solved pathwise with the cut level `δ`. -/
def leftMark (δ y : ℝ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  markFlow (leftMarkDrift δ) y ζ W

/-- The added mark on the right with initial position `y`, solved pathwise with the cut level `δ`. -/
def rightMark (δ y : ℝ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  markFlow (rightMarkDrift δ) y ζ W

theorem adaptedBefore_leftMark {δ : ℝ} (hδ : 0 < δ) (y : ℝ) (hW : AdaptedBefore 𝓕 ζ W) :
    AdaptedBefore 𝓕 ζ (leftMark δ y ζ W) :=
  adaptedBefore_markFlow (lipschitzWith_leftMarkDrift hδ).continuous.measurable hW

theorem adaptedBefore_rightMark {δ : ℝ} (hδ : 0 < δ) (y : ℝ) (hW : AdaptedBefore 𝓕 ζ W) :
    AdaptedBefore 𝓕 ζ (rightMark δ y ζ W) :=
  adaptedBefore_markFlow (lipschitzWith_rightMarkDrift hδ).continuous.measurable hW

/-- The left mark solved pathwise is passive while it stays at distance `≥ δ` left of `W`. -/
theorem isPassiveLeft_leftMark {δ y : ℝ} (hδ : 0 < δ) {ω : Ω}
    (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω}) (hτζ : τ ω ≤ ζ ω)
    (hgap : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → δ ≤ W t ω - leftMark δ y ζ W t ω) :
    IsPassiveLeft (fun t => W t ω) (fun t => leftMark δ y ζ W t ω) y δ (τ ω) := by
  obtain ⟨hc, heq⟩ := markFlow_eq_of_continuousOn (y := y) (lipschitzWith_leftMarkDrift hδ)
    (abs_leftMarkDrift_le hδ) hWc
  refine ⟨markFlow_zero _ _ _ _ _, hc.mono fun t ht => lt_of_lt_of_le ht hτζ, fun {t} ht => ?_,
    fun ht => hgap _ ht⟩
  show markFlow (leftMarkDrift δ) y ζ W t ω = _
  rw [heq t (lt_of_lt_of_le ht hτζ)]
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le t.coe_nonneg] at hr
  have hr' : (r.toNNReal : ℝ≥0∞) < τ ω :=
    lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hr.2) ht
  have := hgap _ hr'
  exact leftMarkDrift_of_le (by unfold leftMark at this; linarith)

/-- The right mark solved pathwise is passive while it stays at distance `≥ δ` right of `W`. -/
theorem isPassiveRight_rightMark {δ y : ℝ} (hδ : 0 < δ) {ω : Ω}
    (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω}) (hτζ : τ ω ≤ ζ ω)
    (hgap : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → δ ≤ rightMark δ y ζ W t ω - W t ω) :
    IsPassiveRight (fun t => W t ω) (fun t => rightMark δ y ζ W t ω) y δ (τ ω) := by
  obtain ⟨hc, heq⟩ := markFlow_eq_of_continuousOn (y := y) (lipschitzWith_rightMarkDrift hδ)
    (abs_rightMarkDrift_le hδ) hWc
  refine ⟨markFlow_zero _ _ _ _ _, hc.mono fun t ht => lt_of_lt_of_le ht hτζ, fun {t} ht => ?_,
    fun ht => hgap _ ht⟩
  show markFlow (rightMarkDrift δ) y ζ W t ω = _
  rw [heq t (lt_of_lt_of_le ht hτζ)]
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le t.coe_nonneg] at hr
  have hr' : (r.toNNReal : ℝ≥0∞) < τ ω :=
    lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hr.2) ht
  have := hgap _ hr'
  exact rightMarkDrift_of_le (by unfold rightMark at this; linarith)

/-- **A reference local evolution and passive added marks form a local evolution of the full
word** (weights `0` on the added marks), before a stopping time `τ ≤ ζ`. -/
theorem IsSLEEvolutionUpTo.of_passive {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {eL : Fin kL → Fin nL} {eR : Fin kR → Fin nR}
    (heL : Function.Injective eL) (heR : Function.Injective eR) {ρL₀ : Fin kL → ℝ}
    {ρR₀ : Fin kR → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {δ : ℝ}
    (hδ : 0 < δ)
    (hE : IsSLEEvolutionUpTo κ (fun j => xL (eL j)) (fun j => xR (eR j)) ρL₀ ρR₀ P 𝓕 W
      (fun j => VL (eL j)) (fun j => VR (eR j)) B ζ)
    (hVLa : ∀ i, (∀ j, eL j ≠ i) → AdaptedBefore 𝓕 ζ (VL i))
    (hVRa : ∀ i, (∀ j, eR j ≠ i) → AdaptedBefore 𝓕 ζ (VR i))
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s}) (hτζ : ∀ ω, τ ω ≤ ζ ω)
    (hpL : ∀ᵐ ω ∂P, ∀ i, (∀ j, eL j ≠ i) →
      IsPassiveLeft (fun t => W t ω) (fun t => VL i t ω) (xL i) δ (τ ω))
    (hpR : ∀ᵐ ω ∂P, ∀ i, (∀ j, eR j ≠ i) →
      IsPassiveRight (fun t => W t ω) (fun t => VR i t ω) (xR i) δ (τ ω)) :
    IsSLEEvolutionUpTo κ xL xR (Function.extend eL ρL₀ 0) (Function.extend eR ρR₀ 0) P 𝓕 W VL VR
      B τ := by
  refine ⟨hE.brownian, hE.adapted_W.of_le hτ hτζ, fun i => ?_, fun i => ?_, ?_⟩
  · by_cases h : ∃ j, eL j = i
    · obtain ⟨j, rfl⟩ := h
      exact (hE.adapted_VL j).of_le hτ hτζ
    · exact (hVLa i fun j hj => h ⟨j, hj⟩).of_le hτ hτζ
  · by_cases h : ∃ j, eR j = i
    · obtain ⟨j, rfl⟩ := h
      exact (hE.adapted_VR j).of_le hτ hτζ
    · exact (hVRa i fun j hj => h ⟨j, hj⟩).of_le hτ hτζ
  · filter_upwards [hE.ae_path, hpL, hpR] with ω hp hl hr
    exact IsSLEPathUpTo.of_passive hF heL heR hδ (hp.mono (hτζ ω)) hl hr

/-- The weights of the reference marks, extended by `0` to the added marks. -/
def refWeights {k n : ℕ} (e : Fin k → Fin n) (ρ : Fin n → ℝ) : Fin n → ℝ :=
  Function.extend e (fun j => ρ (e j)) 0

/-- The left marks of the full word: the reference marks, and the added marks solved pathwise. -/
def fullMarksL {k n : ℕ} (e : Fin k → Fin n) (Vr : Fin k → ℝ≥0 → Ω → ℝ) (δ : ℝ)
    (x : Fin n → ℝ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) : Fin n → ℝ≥0 → Ω → ℝ :=
  Function.extend e Vr fun i => leftMark δ (x i) ζ W

/-- The right marks of the full word: the reference marks, and the added marks solved pathwise. -/
def fullMarksR {k n : ℕ} (e : Fin k → Fin n) (Vr : Fin k → ℝ≥0 → Ω → ℝ) (δ : ℝ)
    (x : Fin n → ℝ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) : Fin n → ℝ≥0 → Ω → ℝ :=
  Function.extend e Vr fun i => rightMark δ (x i) ζ W

/-- **Local existence with the added marks** (Specification L486 and L548; the graph node "Adding
separated force points by Girsanov: existence up to the next collision of an added point", at a
bounded stopping time before the added marks come within `δ` of the driver). Let `(xL; xR)`,
`(ρL; ρR)` be an ordered force word, `eL`, `eR` injections onto a reference sub-word, and
`(W, Vr, B)` a local evolution of the reference sub-word before `ζ` (e.g. the one-force-point or the
two-seed evolution). The added marks are solved pathwise (`fullMarksL`, `fullMarksR`). Let
`τ ≤ ζ ∧ T` be a stopping time before which every added mark stays at distance `≥ δ > 0` from `W`.
Then, under `Q = Z_{T+1} · P` (`Z` the Doléans density of the added drift
`κ^{-1/2} ∑ ρ/(W − V)` over the added marks, cut at `τ`), which is a probability measure equivalent to
`P`, the processes `(W, V, B̃)` are a local evolution of the full force word with its weights
`(ρL; ρR)` before `τ`. -/
theorem IsSLEEvolutionUpTo.exists_addMarks [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {eL : Fin kL → Fin nL} {eR : Fin kR → Fin nR}
    (heL : Function.Injective eL) (heR : Function.Injective eR)
    {VLr : Fin kL → ℝ≥0 → Ω → ℝ} {VRr : Fin kR → ℝ≥0 → Ω → ℝ}
    (hE : IsSLEEvolutionUpTo κ (fun j => xL (eL j)) (fun j => xR (eR j)) (fun j => ρL (eL j))
      (fun j => ρR (eR j)) P 𝓕 W VLr VRr B ζ) {δ : ℝ} (hδ : 0 < δ)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s}) (hτζ : ∀ ω, τ ω ≤ ζ ω) {T : ℝ≥0}
    (hτT : ∀ ω, τ ω ≤ T)
    (hgapL : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → ∀ i, (∀ j, eL j ≠ i) →
      δ ≤ W t ω - leftMark δ (xL i) ζ W t ω)
    (hgapR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → ∀ i, (∀ j, eR j ≠ i) →
      δ ≤ rightMark δ (xR i) ζ W t ω - W t ω) :
    MathFin.IsEquivProbMeasure P (girsanovMeasure P 𝓕 B
      (weightDrift κ δ (refWeights eL ρL) ρL (refWeights eR ρR) ρR τ τ W
        (fullMarksL eL VLr δ xL ζ W) (fullMarksR eR VRr δ xR ζ W)) (T + 1)) ∧
    IsSLEEvolutionUpTo κ xL xR ρL ρR (girsanovMeasure P 𝓕 B
      (weightDrift κ δ (refWeights eL ρL) ρL (refWeights eR ρR) ρR τ τ W
        (fullMarksL eL VLr δ xL ζ W) (fullMarksR eR VRr δ xR ζ W)) (T + 1)) 𝓕 W
      (fullMarksL eL VLr δ xL ζ W) (fullMarksR eR VRr δ xR ζ W)
      (girsanovProcess B (weightDrift κ δ (refWeights eL ρL) ρL (refWeights eR ρR) ρR τ τ W
        (fullMarksL eL VLr δ xL ζ W) (fullMarksR eR VRr δ xR ζ W))) τ := by
  set VL := fullMarksL eL VLr δ xL ζ W with hVL
  set VR := fullMarksR eR VRr δ xR ζ W with hVR
  have hVLe : (fun j => VL (eL j)) = VLr := funext fun j => heL.extend_apply _ _ j
  have hVRe : (fun j => VR (eR j)) = VRr := funext fun j => heR.extend_apply _ _ j
  have hVLp : ∀ i, (∀ j, eL j ≠ i) → VL i = leftMark δ (xL i) ζ W := fun i hi =>
    Function.extend_apply' _ _ _ fun ⟨j, hj⟩ => hi j hj
  have hVRp : ∀ i, (∀ j, eR j ≠ i) → VR i = rightMark δ (xR i) ζ W := fun i hi =>
    Function.extend_apply' _ _ _ fun ⟨j, hj⟩ => hi j hj
  have hE' : IsSLEEvolutionUpTo κ (fun j => xL (eL j)) (fun j => xR (eR j)) (fun j => ρL (eL j))
      (fun j => ρR (eR j)) P 𝓕 W (fun j => VL (eL j)) (fun j => VR (eR j)) B ζ := by
    rw [hVLe, hVRe]; exact hE
  have hM : IsSLEEvolutionUpTo κ xL xR (refWeights eL ρL) (refWeights eR ρR) P 𝓕 W VL VR B τ := by
    refine hE'.of_passive hF heL heR hδ (fun i hi => ?_) (fun i hi => ?_) hτ hτζ ?_ ?_
    · rw [hVLp i hi]; exact adaptedBefore_leftMark hδ _ hE.adapted_W
    · rw [hVRp i hi]; exact adaptedBefore_rightMark hδ _ hE.adapted_W
    · filter_upwards [hE.ae_path, hgapL] with ω hp hg i hi
      rw [hVLp i hi]
      exact isPassiveLeft_leftMark hδ hp.continuousOn_w (hτζ ω) fun t ht => hg t ht i hi
    · filter_upwards [hE.ae_path, hgapR] with ω hp hg i hi
      rw [hVRp i hi]
      exact isPassiveRight_rightMark hδ hp.continuousOn_w (hτζ ω) fun t ht => hg t ht i hi
  refine hM.girsanov_changeWeights hκ ρL ρR hτ (fun _ => le_rfl) hτT hδ ?_
  have hrefL : ∀ i, ρL i ≠ refWeights eL ρL i → ∀ j, eL j ≠ i := fun i hi j hj => by
    subst hj
    exact hi (heL.extend_apply (fun j => ρL (eL j)) 0 j).symm
  have hrefR : ∀ i, ρR i ≠ refWeights eR ρR i → ∀ j, eR j ≠ i := fun i hi j hj => by
    subst hj
    exact hi (heR.extend_apply (fun j => ρR (eR j)) 0 j).symm
  filter_upwards [hgapL, hgapR] with ω hl hr t ht
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [hVLp i (hrefL i hi)]
    exact (hl t ht i (hrefL i hi)).trans (le_abs_self _)
  · rw [hVRp i (hrefR i hi), abs_sub_comm]
    exact (hr t ht i (hrefR i hi)).trans (le_abs_self _)

end Evolution

end Sec2

end InteractingSLE
