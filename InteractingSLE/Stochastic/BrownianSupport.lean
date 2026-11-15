/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly2Life
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Data.NNRat.Encodable
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# The support theorem for Brownian motion in the sup norm

Packet PROVE-LP15. Supplement, proof of Lemma LP3 (`source/spec/p481-528.md` L25–L35, p. 481: "Continuous
dependence of those real characteristics on the driver and Brownian full support give a positive-probability
neighborhood of this final configuration"). For a Brownian motion `B`, a continuous `f` with `f 0 = 0`, a horizon
`T` and `ε > 0`,

  `P(|B_t − f(t)| < ε for every t ≤ T) > 0`   (`measure_forall_abs_sub_lt_pos`).

## Proof (direct Markov chaining; no change of measure)

* **Lipschitz targets.** Let `|f s − f t₀| ≤ a ≤ δ/4` on every step `[t₀, t₀ + h]` of a rational grid. Keep the
  invariant `G_t = {|B_q − f_q| < δ at rational q ≤ t} ∩ {|B_t − f_t| < δ/2}`. With `Y = B(t₀ + ·) − B_{t₀}`
  (independent of the past, `IsPreBrownianReal.indepFun_shift`), on `G_{t₀} ∩ {B_{t₀} ≥ f(t₀ + h)}` the step
  `{sup_{q ≤ h} |Y_q| < δ/4, Y_h ≤ −a}` gives `G_{t₀+h}`, and symmetrically with `Y_h ≥ a`
  (`measure_good_add_ge`). Both steps have the same probability `c` (the path laws of `Y`, `B` and `−B` agree,
  `Sec2.Assembly2.map_path_eq_map_path`), so `P(G_{t₀+h}) ≥ c · P(G_{t₀})` and `P(G_{nh}) ≥ cⁿ`.
* **The one-step probability.** `2c ≥ P(sup_{q ≤ h} |B_q| < δ/4) − P(|B_h| < a)`. The first term tends to `1` as
  `h → 0` (continuity at `0`), and `P(|B_h| < a) ≤ a/√h` (Gaussian density bound). With `a = L h` both are
  controlled for small `h`, so `c ≥ 1/4`.
* **General continuous targets.** Stone–Weierstrass: a polynomial `p` with `|p − f| < δ` on `[0, T + 1]`;
  `p − p(0)` is Lipschitz there and vanishes at `0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal NNRat

namespace InteractingSLE.BrownianSupport

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-! ### Path laws -/

/-- Two pre-Brownian motions with measurable coordinates on the same space give every measurable set of paths the
same probability. -/
theorem measure_path_mem_eq [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → ℝ} (hX : IsPreBrownianReal X P)
    (hXm : ∀ t, Measurable (X t)) (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    {S : Set (ℝ≥0 → ℝ)} (hS : MeasurableSet S) :
    P {ω | (fun t => X t ω) ∈ S} = P {ω | (fun t => B t ω) ∈ S} := by
  have hmX : Measurable fun ω (t : ℝ≥0) => X t ω := measurable_pi_iff.2 hXm
  have hmB : Measurable fun ω (t : ℝ≥0) => B t ω := measurable_pi_iff.2 hBm
  have h := Sec2.Assembly2.map_path_eq_map_path hX hB hmX hmB
  have h' := congrArg (fun μ : Measure (ℝ≥0 → ℝ) => μ S) h
  simp only [Measure.map_apply hmX hS, Measure.map_apply hmB hS] at h'
  exact h'

/-! ### The tube events -/

/-- The rational-time tube around `f` of half-width `δ` up to time `t`, as a set of past paths. -/
def pastTube (f : ℝ≥0 → ℝ) (δ : ℝ) (t : ℝ≥0) : Set (Iic t → ℝ) :=
  {x | ∀ q : ℚ≥0, ∀ hq : (q : ℝ≥0) ≤ t, |x ⟨q, hq⟩ - f q| < δ}

theorem measurableSet_pastTube (f : ℝ≥0 → ℝ) (δ : ℝ) (t : ℝ≥0) : MeasurableSet (pastTube f δ t) := by
  simp only [pastTube, ofPred_forall]
  exact MeasurableSet.iInter fun q => MeasurableSet.iInter fun hq =>
    measurableSet_lt (continuous_abs.measurable.comp ((measurable_pi_apply _).sub_const _)) measurable_const

/-- The value at the endpoint of a past path. -/
def pastEnd {t : ℝ≥0} (x : Iic t → ℝ) : ℝ := x ⟨t, mem_Iic.2 le_rfl⟩

theorem measurable_pastEnd (t : ℝ≥0) : Measurable (pastEnd (t := t)) := measurable_pi_apply _

/-- The invariant of the chaining: the rational-time tube of half-width `δ` up to `t`, and the endpoint within
`δ/2` of `f t`. -/
def good (B : ℝ≥0 → Ω → ℝ) (f : ℝ≥0 → ℝ) (δ : ℝ) (t : ℝ≥0) : Set Ω :=
  {ω | (∀ q : ℚ≥0, (q : ℝ≥0) ≤ t → |B q ω - f q| < δ) ∧ |B t ω - f t| < δ / 2}

/-- The downward step: the path stays within `δ/4` of `0` at rational times `≤ h` and ends at `≤ -a`. -/
def downSet (δ a : ℝ) (h : ℝ≥0) : Set (ℝ≥0 → ℝ) :=
  {y | (∀ q : ℚ≥0, (q : ℝ≥0) ≤ h → |y q| < δ / 4) ∧ y h ≤ -a}

/-- The upward step: the path stays within `δ/4` of `0` at rational times `≤ h` and ends at `≥ a`. -/
def upSet (δ a : ℝ) (h : ℝ≥0) : Set (ℝ≥0 → ℝ) :=
  {y | (∀ q : ℚ≥0, (q : ℝ≥0) ≤ h → |y q| < δ / 4) ∧ a ≤ y h}

/-- The rational-time ball of radius `r` up to time `h`. -/
def ballSet (r : ℝ) (h : ℝ≥0) : Set (ℝ≥0 → ℝ) := {y | ∀ q : ℚ≥0, (q : ℝ≥0) ≤ h → |y q| < r}

theorem measurableSet_ballSet (r : ℝ) (h : ℝ≥0) : MeasurableSet (ballSet r h) := by
  simp only [ballSet, ofPred_forall]
  exact MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ =>
    measurableSet_lt (continuous_abs.measurable.comp (measurable_pi_apply _)) measurable_const

theorem downSet_eq (δ a : ℝ) (h : ℝ≥0) : downSet δ a h = ballSet (δ / 4) h ∩ {y | y h ≤ -a} := rfl

theorem upSet_eq (δ a : ℝ) (h : ℝ≥0) : upSet δ a h = ballSet (δ / 4) h ∩ {y | a ≤ y h} := rfl

theorem measurableSet_downSet (δ a : ℝ) (h : ℝ≥0) : MeasurableSet (downSet δ a h) := by
  rw [downSet_eq]
  exact (measurableSet_ballSet _ _).inter (measurableSet_le (measurable_pi_apply _) measurable_const)

theorem measurableSet_upSet (δ a : ℝ) (h : ℝ≥0) : MeasurableSet (upSet δ a h) := by
  rw [upSet_eq]
  exact (measurableSet_ballSet _ _).inter (measurableSet_le measurable_const (measurable_pi_apply _))

theorem neg_mem_downSet_iff {δ a : ℝ} {h : ℝ≥0} {y : ℝ≥0 → ℝ} : (-y) ∈ downSet δ a h ↔ y ∈ upSet δ a h := by
  simp only [downSet, upSet, mem_ofPred_eq, Pi.neg_apply, abs_neg, neg_le_neg_iff]

/-! ### One step of the chaining -/

section Step

variable {f : ℝ≥0 → ℝ} {δ a : ℝ}

/-- The tube part of one step: the tube up to `t₀`, the endpoint within `δ/2`, increments within `δ/4` and a
target moving by at most `a ≤ δ/4` give the tube up to `t₀ + h`. -/
theorem tube_step {t₀ h : ℚ≥0} (ha : a ≤ δ / 4)
    (hf : ∀ s : ℝ≥0, (t₀ : ℝ≥0) ≤ s → s ≤ (t₀ : ℝ≥0) + h → |f s - f t₀| ≤ a) {ω : Ω}
    (hp : ∀ q : ℚ≥0, (q : ℝ≥0) ≤ t₀ → |B q ω - f q| < δ) (hend : |B t₀ ω - f t₀| < δ / 2)
    (hY : ∀ q : ℚ≥0, (q : ℝ≥0) ≤ h → |B ((t₀ : ℝ≥0) + q) ω - B t₀ ω| < δ / 4) :
    ∀ q : ℚ≥0, (q : ℝ≥0) ≤ (t₀ : ℝ≥0) + h → |B q ω - f q| < δ := by
  intro q hq
  rcases le_or_gt (q : ℝ≥0) t₀ with hle | hlt
  · exact hp q hle
  · have hle' : t₀ ≤ q := by exact_mod_cast hlt.le
    obtain ⟨s, rfl⟩ := exists_add_of_le hle'
    have hcast : ((t₀ + s : ℚ≥0) : ℝ≥0) = (t₀ : ℝ≥0) + s := NNRat.cast_add _ _
    rw [hcast] at hq ⊢
    have hs : (s : ℝ≥0) ≤ h := le_of_add_le_add_left hq
    have h1 := hY s hs
    have h2 := hf ((t₀ : ℝ≥0) + s) le_self_add hq
    have e : B ((t₀ : ℝ≥0) + s) ω - f ((t₀ : ℝ≥0) + s) =
        (B t₀ ω - f t₀) + (B ((t₀ : ℝ≥0) + s) ω - B t₀ ω) - (f ((t₀ : ℝ≥0) + s) - f t₀) := by ring
    rw [e]
    calc |(B t₀ ω - f t₀) + (B ((t₀ : ℝ≥0) + s) ω - B t₀ ω) - (f ((t₀ : ℝ≥0) + s) - f t₀)|
        ≤ |B t₀ ω - f t₀| + |B ((t₀ : ℝ≥0) + s) ω - B t₀ ω| + |f ((t₀ : ℝ≥0) + s) - f t₀| :=
          (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ < δ / 2 + δ / 4 + a := by linarith
      _ ≤ δ := by linarith

/-- A downward step from an endpoint at or above `f (t₀ + h)` keeps the invariant. -/
theorem mem_good_of_down {t₀ h : ℚ≥0} (ha : a ≤ δ / 4)
    (hf : ∀ s : ℝ≥0, (t₀ : ℝ≥0) ≤ s → s ≤ (t₀ : ℝ≥0) + h → |f s - f t₀| ≤ a) {ω : Ω}
    (hY : (fun t => B ((t₀ : ℝ≥0) + t) ω - B t₀ ω) ∈ downSet δ a h) (hω : ω ∈ good B f δ t₀)
    (hsign : f ((t₀ : ℝ≥0) + h) ≤ B t₀ ω) : ω ∈ good B f δ ((t₀ : ℝ≥0) + h) := by
  obtain ⟨hp, hend⟩ := hω
  obtain ⟨hball, hlow⟩ := hY
  refine ⟨tube_step ha hf hp hend hball, ?_⟩
  have hfa := hf ((t₀ : ℝ≥0) + h) le_self_add le_rfl
  have hh : (h : ℝ≥0) ≤ h := le_rfl
  have hb := hball h hh
  rw [abs_lt] at hb hend ⊢
  rw [abs_le] at hfa
  constructor <;> linarith [hb.1, hb.2, hend.1, hend.2, hfa.1, hfa.2]

/-- An upward step from an endpoint below `f (t₀ + h)` keeps the invariant. -/
theorem mem_good_of_up {t₀ h : ℚ≥0} (ha : a ≤ δ / 4)
    (hf : ∀ s : ℝ≥0, (t₀ : ℝ≥0) ≤ s → s ≤ (t₀ : ℝ≥0) + h → |f s - f t₀| ≤ a) {ω : Ω}
    (hY : (fun t => B ((t₀ : ℝ≥0) + t) ω - B t₀ ω) ∈ upSet δ a h) (hω : ω ∈ good B f δ t₀)
    (hsign : B t₀ ω < f ((t₀ : ℝ≥0) + h)) : ω ∈ good B f δ ((t₀ : ℝ≥0) + h) := by
  obtain ⟨hp, hend⟩ := hω
  obtain ⟨hball, hlow⟩ := hY
  refine ⟨tube_step ha hf hp hend hball, ?_⟩
  have hfa := hf ((t₀ : ℝ≥0) + h) le_self_add le_rfl
  have hh : (h : ℝ≥0) ≤ h := le_rfl
  have hb := hball h hh
  rw [abs_lt] at hb hend ⊢
  rw [abs_le] at hfa
  constructor <;> linarith [hb.1, hb.2, hend.1, hend.2, hfa.1, hfa.2]

end Step

/-! ### The Markov step -/

section MarkovStep

variable [IsProbabilityMeasure P] {f : ℝ≥0 → ℝ} {δ a : ℝ}

/-- The probability of the upward step equals that of the downward step (`B` and `−B` have the same path law). -/
theorem measure_upSet_eq (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t)) (h : ℝ≥0) :
    P {ω | (fun s => B s ω) ∈ upSet δ a h} = P {ω | (fun s => B s ω) ∈ downSet δ a h} := by
  have hneg := measure_path_mem_eq hB.neg (fun s => (hBm s).neg) hB hBm (measurableSet_downSet δ a h)
  rw [← hneg]
  congr 1
  ext ω
  exact (neg_mem_downSet_iff (y := fun s => B s ω)).symm

/-- **One Markov step.** `P(G_{t₀+h}) ≥ c · P(G_{t₀})`, where `c` is the probability of the downward step. -/
theorem measure_good_add_ge (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t)) {t₀ h : ℚ≥0}
    (ha : a ≤ δ / 4) (hf : ∀ s : ℝ≥0, (t₀ : ℝ≥0) ≤ s → s ≤ (t₀ : ℝ≥0) + h → |f s - f t₀| ≤ a) :
    P {ω | (fun s => B s ω) ∈ downSet δ a h} * P (good B f δ t₀) ≤
      P (good B f δ ((t₀ : ℝ≥0) + h)) := by
  set t : ℝ≥0 := (t₀ : ℝ≥0) with ht
  let past : Ω → (Iic t → ℝ) := fun ω s => B s ω
  let Y : Ω → (ℝ≥0 → ℝ) := fun ω s => B (t + s) ω - B t ω
  have hpast : Measurable past := measurable_pi_iff.2 fun s => hBm s
  have hYm' : ∀ s, Measurable fun ω => B (t + s) ω - B t ω := fun s => (hBm _).sub (hBm _)
  have hind : IndepFun Y past P := hB.indepFun_shift t
  have hYB : IsPreBrownianReal (fun s ω => B (t + s) ω - B t ω) P := hB.shift t
  have hc_down : P (Y ⁻¹' downSet δ a h) = P {ω | (fun s => B s ω) ∈ downSet δ a h} :=
    measure_path_mem_eq hYB hYm' hB hBm (measurableSet_downSet _ _ _)
  have hc_up : P (Y ⁻¹' upSet δ a h) = P {ω | (fun s => B s ω) ∈ downSet δ a h} := by
    rw [← measure_upSet_eq hB hBm]
    exact measure_path_mem_eq hYB hYm' hB hBm (measurableSet_upSet _ _ _)
  let U : Set (Iic t → ℝ) := pastTube f δ t ∩ {x | |pastEnd x - f t| < δ / 2}
  let U₁ : Set (Iic t → ℝ) := U ∩ {x | f (t + h) ≤ pastEnd x}
  let U₂ : Set (Iic t → ℝ) := U ∩ {x | pastEnd x < f (t + h)}
  have hU : MeasurableSet U := (measurableSet_pastTube f δ t).inter
    (measurableSet_lt (continuous_abs.measurable.comp ((measurable_pastEnd t).sub_const _)) measurable_const)
  have hU₁ : MeasurableSet U₁ := hU.inter (measurableSet_le measurable_const (measurable_pastEnd t))
  have hU₂ : MeasurableSet U₂ := hU.inter (measurableSet_lt (measurable_pastEnd t) measurable_const)
  have hgood : good B f δ t = past ⁻¹' U₁ ∪ past ⁻¹' U₂ := by
    ext ω
    simp only [good, U₁, U₂, U, pastTube, pastEnd, past, mem_preimage, mem_inter_iff, mem_union,
      mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      rcases le_or_gt (f (t + h)) (B t ω) with h3 | h3
      · exact Or.inl ⟨⟨fun q hq => h1 q hq, h2⟩, h3⟩
      · exact Or.inr ⟨⟨fun q hq => h1 q hq, h2⟩, h3⟩
    · rintro (⟨⟨h1, h2⟩, -⟩ | ⟨⟨h1, h2⟩, -⟩)
      · exact ⟨fun q hq => h1 q hq, h2⟩
      · exact ⟨fun q hq => h1 q hq, h2⟩
  have hdisj : Disjoint (past ⁻¹' U₁) (past ⁻¹' U₂) := by
    rw [Set.disjoint_left]
    rintro ω ⟨-, h1⟩ ⟨-, h2⟩
    exact absurd (show f (t + h) ≤ pastEnd (past ω) from h1) (not_le.2 h2)
  have hsub : (Y ⁻¹' downSet δ a h ∩ past ⁻¹' U₁) ∪ (Y ⁻¹' upSet δ a h ∩ past ⁻¹' U₂) ⊆
      good B f δ (t + h) := by
    rintro ω (⟨hY, hω⟩ | ⟨hY, hω⟩)
    · have hg : ω ∈ good B f δ t := by rw [hgood]; exact Or.inl hω
      exact mem_good_of_down ha hf hY hg hω.2
    · have hg : ω ∈ good B f δ t := by rw [hgood]; exact Or.inr hω
      exact mem_good_of_up ha hf hY hg hω.2
  have hdisj' : Disjoint (Y ⁻¹' downSet δ a h ∩ past ⁻¹' U₁) (Y ⁻¹' upSet δ a h ∩ past ⁻¹' U₂) :=
    hdisj.mono inter_subset_right inter_subset_right
  have hYm : Measurable Y := measurable_pi_iff.2 hYm'
  calc P {ω | (fun s => B s ω) ∈ downSet δ a h} * P (good B f δ t)
      = P (Y ⁻¹' downSet δ a h) * P (past ⁻¹' U₁) + P (Y ⁻¹' upSet δ a h) * P (past ⁻¹' U₂) := by
        rw [hgood, measure_union hdisj (hpast hU₂), mul_add, hc_down, hc_up]
    _ = P (Y ⁻¹' downSet δ a h ∩ past ⁻¹' U₁) + P (Y ⁻¹' upSet δ a h ∩ past ⁻¹' U₂) := by
        rw [hind.measure_inter_preimage_eq_mul _ _ (measurableSet_downSet _ _ _) hU₁,
          hind.measure_inter_preimage_eq_mul _ _ (measurableSet_upSet _ _ _) hU₂]
    _ = P ((Y ⁻¹' downSet δ a h ∩ past ⁻¹' U₁) ∪ (Y ⁻¹' upSet δ a h ∩ past ⁻¹' U₂)) :=
        (measure_union hdisj' ((hYm (measurableSet_upSet _ _ _)).inter (hpast hU₂))).symm
    _ ≤ P (good B f δ (t + h)) := measure_mono hsub

end MarkovStep

/-! ### Iterating the step -/

section Iterate

variable [IsProbabilityMeasure P] {f : ℝ≥0 → ℝ} {δ a : ℝ}

theorem measure_good_zero (hB : IsPreBrownianReal B P) (hf0 : f 0 = 0) (hδ : 0 < δ) :
    P (good B f δ 0) = 1 := by
  refine le_antisymm prob_le_one ?_
  rw [← measure_univ (μ := P)]
  refine measure_mono_ae ?_
  filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω _
  refine ⟨fun q hq => ?_, ?_⟩
  · have hq0 : (q : ℝ≥0) = 0 := le_antisymm hq bot_le
    rw [hq0, hω, hf0, sub_zero, abs_zero]
    exact hδ
  · rw [hω, hf0, sub_zero, abs_zero]
    exact half_pos hδ

/-- **Chaining.** If the target moves by at most `a ≤ δ/4` on each of the first `n` steps of the grid `h ℕ`,
then `P(G_{nh}) ≥ cⁿ`. -/
theorem pow_le_measure_good (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t)) (hf0 : f 0 = 0)
    (hδ : 0 < δ) {h : ℚ≥0} (ha : a ≤ δ / 4) (n : ℕ)
    (hf : ∀ k < n, ∀ s : ℝ≥0, ((k * h : ℚ≥0) : ℝ≥0) ≤ s → s ≤ ((k * h : ℚ≥0) : ℝ≥0) + h →
      |f s - f ((k * h : ℚ≥0) : ℝ≥0)| ≤ a) :
    P {ω | (fun s => B s ω) ∈ downSet δ a h} ^ n ≤ P (good B f δ ((n * h : ℚ≥0) : ℝ≥0)) := by
  induction n with
  | zero => simp [measure_good_zero hB hf0 hδ]
  | succ n ih =>
    have ih' := ih fun k hk => hf k (Nat.lt_succ_of_lt hk)
    have hstep := measure_good_add_ge (t₀ := n * h) (h := h) hB hBm ha (hf n (Nat.lt_succ_self n))
    have hcast : (((n + 1 : ℕ) * h : ℚ≥0) : ℝ≥0) = ((n * h : ℚ≥0) : ℝ≥0) + h := by
      rw [← NNRat.cast_add]
      congr 1
      push_cast
      ring
    rw [hcast, pow_succ, mul_comm]
    exact (mul_le_mul_of_nonneg_left ih' (zero_le)).trans hstep

end Iterate

/-! ### A Gaussian anti-concentration bound -/

theorem gaussianReal_Ioo_le_div {v : ℝ≥0} (hv : v ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    gaussianReal 0 v (Ioo (-c) c) ≤ ENNReal.ofReal (c / √(v : ℝ)) := by
  rw [gaussianReal_apply 0 hv]
  have hvpos : 0 < (v : ℝ) := by positivity
  have hbound : ∀ y, gaussianPDF 0 v y ≤ ENNReal.ofReal (√(2 * Real.pi * v))⁻¹ := by
    intro y
    rw [gaussianPDF]
    apply ENNReal.ofReal_le_ofReal
    rw [gaussianPDFReal]
    have h1 : Real.exp (-(y - 0) ^ 2 / (2 * v)) ≤ 1 := Real.exp_le_one_iff.2
      (div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity))
    calc (√(2 * Real.pi * v))⁻¹ * Real.exp (-(y - 0) ^ 2 / (2 * v))
        ≤ (√(2 * Real.pi * v))⁻¹ * 1 := by gcongr
      _ = (√(2 * Real.pi * v))⁻¹ := mul_one _
  have hs : √(2 * Real.pi * v) = √(2 * Real.pi) * √(v : ℝ) := Real.sqrt_mul (by positivity) _
  have hpi : 2 ≤ √(2 * Real.pi) := Real.le_sqrt_of_sq_le (by nlinarith [Real.pi_gt_three])
  have hsv : 0 < √(v : ℝ) := Real.sqrt_pos.2 hvpos
  calc ∫⁻ y in Ioo (-c) c, gaussianPDF 0 v y
      ≤ ∫⁻ _ in Ioo (-c) c, ENNReal.ofReal (√(2 * Real.pi * v))⁻¹ := lintegral_mono fun y => hbound y
    _ = ENNReal.ofReal (√(2 * Real.pi * v))⁻¹ * volume (Ioo (-c) c) := setLIntegral_const _ _
    _ = ENNReal.ofReal ((√(2 * Real.pi * v))⁻¹ * (2 * c)) := by
        rw [Real.volume_Ioo, ← ENNReal.ofReal_mul (by positivity)]
        congr 2; ring
    _ ≤ ENNReal.ofReal (c / √(v : ℝ)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hs, mul_inv, div_eq_mul_inv]
        have h2 : (√(2 * Real.pi))⁻¹ * 2 ≤ 1 := by
          rw [inv_mul_le_iff₀ (by positivity)]
          linarith
        calc (√(2 * Real.pi))⁻¹ * (√(v : ℝ))⁻¹ * (2 * c)
            = ((√(2 * Real.pi))⁻¹ * 2) * (c * (√(v : ℝ))⁻¹) := by ring
          _ ≤ 1 * (c * (√(v : ℝ))⁻¹) := by gcongr
          _ = c * (√(v : ℝ))⁻¹ := one_mul _

/-! ### The one-step probability -/

section OneStep

variable [IsProbabilityMeasure P] {δ a : ℝ}

/-- `c ≥ 1/4` once the ball has probability `≥ 3/4` and `P(|B_h| < a) ≤ 1/4`. -/
theorem quarter_le_measureReal_downSet (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    {h : ℝ≥0} (hball : 3 / 4 ≤ P.real {ω | (fun s => B s ω) ∈ ballSet (δ / 4) h})
    (hsmall : P.real {ω | |B h ω| < a} ≤ 1 / 4) :
    1 / 4 ≤ P.real {ω | (fun s => B s ω) ∈ downSet δ a h} := by
  have hsub : {ω | (fun s => B s ω) ∈ ballSet (δ / 4) h} ⊆
      ({ω | (fun s => B s ω) ∈ downSet δ a h} ∪ {ω | (fun s => B s ω) ∈ upSet δ a h}) ∪
        {ω | |B h ω| < a} := by
    intro ω hω
    rcases le_or_gt (B h ω) (-a) with h1 | h1
    · exact Or.inl (Or.inl ⟨hω, h1⟩)
    rcases le_or_gt a (B h ω) with h2 | h2
    · exact Or.inl (Or.inr ⟨hω, h2⟩)
    · exact Or.inr (abs_lt.2 ⟨h1, h2⟩)
  have hup : P.real {ω | (fun s => B s ω) ∈ upSet δ a h} =
      P.real {ω | (fun s => B s ω) ∈ downSet δ a h} := by
    simp only [measureReal_def, measure_upSet_eq hB hBm h]
  have h1 := measureReal_mono hsub (μ := P) (measure_ne_top _ _)
  have h2 := measureReal_union_le
    ({ω | (fun s => B s ω) ∈ downSet δ a h} ∪ {ω | (fun s => B s ω) ∈ upSet δ a h}) {ω | |B h ω| < a} (μ := P)
  have h3 := measureReal_union_le {ω | (fun s => B s ω) ∈ downSet δ a h}
    {ω | (fun s => B s ω) ∈ upSet δ a h} (μ := P)
  linarith

omit [IsProbabilityMeasure P] in
theorem measureReal_abs_lt_le (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t)) {h : ℝ≥0}
    (hh : h ≠ 0) (ha : 0 ≤ a) : P.real {ω | |B h ω| < a} ≤ a / √(h : ℝ) := by
  have hlaw : P.map (B h) = gaussianReal 0 h := (hB.hasLaw_eval h).map_eq
  have hset : {ω | |B h ω| < a} = B h ⁻¹' Ioo (-a) a := by
    ext ω; simp only [mem_ofPred_eq, mem_preimage, mem_Ioo, abs_lt]
  have hP : P {ω | |B h ω| < a} = gaussianReal 0 h (Ioo (-a) a) := by
    rw [hset, ← hlaw, Measure.map_apply (hBm h) measurableSet_Ioo]
  rw [measureReal_def, hP]
  have hle := gaussianReal_Ioo_le_div hh ha
  have hpos : 0 ≤ a / √(h : ℝ) := by positivity
  exact (ENNReal.toReal_le_of_le_ofReal hpos hle)

end OneStep

/-! ### Choosing the step -/

section Choose

variable [IsProbabilityMeasure P] {δ : ℝ}

/-- The rational step `1/(m+1)`. -/
def stepSize (m : ℕ) : ℚ≥0 := 1 / (m + 1)

theorem coe_stepSize (m : ℕ) : (((stepSize m : ℚ≥0) : ℝ≥0) : ℝ) = 1 / ((m : ℝ) + 1) := by
  simp [stepSize]

theorem stepSize_pos (m : ℕ) : 0 < stepSize m := by
  unfold stepSize; positivity

theorem coe_stepSize_le_one (m : ℕ) : (((stepSize m : ℚ≥0) : ℝ≥0) : ℝ) ≤ 1 := by
  rw [coe_stepSize, div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

theorem tendsto_coe_stepSize : Tendsto (fun m => (((stepSize m : ℚ≥0) : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
  simp_rw [coe_stepSize]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The rational-time balls of the shrinking steps exhaust a set of full probability (continuity at `0`). -/
theorem tendsto_measure_ballSet (hB : IsBrownianReal B P) (hδ : 0 < δ) :
    Tendsto (fun m => P {ω | (fun s => B s ω) ∈ ballSet (δ / 4) (stepSize m)}) atTop (𝓝 1) := by
  have hmono : Monotone fun m => {ω | (fun s => B s ω) ∈ ballSet (δ / 4) (stepSize m)} := by
    intro m m' hmm' ω hω q hq
    refine hω q (hq.trans ?_)
    rw [← NNReal.coe_le_coe, coe_stepSize, coe_stepSize]
    gcongr
  have hlim := tendsto_measure_iUnion_atTop (μ := P) hmono
  have hfull : P (⋃ m, {ω | (fun s => B s ω) ∈ ballSet (δ / 4) (stepSize m)}) = 1 := by
    refine le_antisymm prob_le_one ?_
    rw [← measure_univ (μ := P)]
    refine measure_mono_ae ?_
    filter_upwards [hB.tendsto_nhds_zero] with ω hω _
    obtain ⟨η, hη, hηB⟩ := Metric.tendsto_nhds_nhds.1 hω (δ / 4) (by positivity)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hη
    refine mem_iUnion.2 ⟨m, fun q hq => ?_⟩
    have hd : dist (q : ℝ≥0) 0 < η := by
      rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)]
      have hq' : ((q : ℝ≥0) : ℝ) ≤ (((stepSize m : ℚ≥0) : ℝ≥0) : ℝ) := NNReal.coe_le_coe.2 hq
      rw [coe_stepSize] at hq'
      linarith
    have := hηB hd
    rwa [Real.dist_eq, sub_zero] at this
  rw [hfull] at hlim
  exact hlim

/-- **Choice of the step.** For `δ > 0` and `L ≥ 0` there is a rational step `h ∈ (0, 1]` with `L h ≤ δ/4` and
downward-step probability at least `1/4`. -/
theorem exists_step (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t)) (hδ : 0 < δ) {L : ℝ}
    (hL : 0 ≤ L) :
    ∃ h : ℚ≥0, 0 < h ∧ ((h : ℝ≥0) : ℝ) ≤ 1 ∧ L * ((h : ℝ≥0) : ℝ) ≤ δ / 4 ∧
      1 / 4 ≤ P.real {ω | (fun s => B s ω) ∈ downSet δ (L * ((h : ℝ≥0) : ℝ)) h} := by
  have hA : ∀ᶠ m in atTop, L * (((stepSize m : ℚ≥0) : ℝ≥0) : ℝ) ≤ δ / 4 := by
    have ht := tendsto_coe_stepSize.const_mul L
    rw [mul_zero] at ht
    exact ht.eventually (Iic_mem_nhds (by positivity))
  have hC : ∀ᶠ m in atTop, L * √(((stepSize m : ℚ≥0) : ℝ≥0) : ℝ) ≤ 1 / 4 := by
    have ht := ((Real.continuous_sqrt.tendsto 0).comp tendsto_coe_stepSize).const_mul L
    rw [Real.sqrt_zero, mul_zero] at ht
    exact ht.eventually (Iic_mem_nhds (by norm_num))
  have hBall : ∀ᶠ m in atTop,
      ENNReal.ofReal (3 / 4) < P {ω | (fun s => B s ω) ∈ ballSet (δ / 4) (stepSize m)} :=
    (tendsto_measure_ballSet hB hδ).eventually (lt_mem_nhds (by
      rw [ENNReal.ofReal_lt_one]; norm_num))
  obtain ⟨m, hmA, hmC, hmB⟩ := (hA.and (hC.and hBall)).exists
  refine ⟨stepSize m, stepSize_pos m, coe_stepSize_le_one m, hmA, ?_⟩
  set h : ℝ≥0 := ((stepSize m : ℚ≥0) : ℝ≥0) with hh
  have hpos : (0 : ℝ) < h := by rw [hh, coe_stepSize]; positivity
  have hh0 : h ≠ 0 := by intro h0; rw [h0, NNReal.coe_zero] at hpos; exact lt_irrefl _ hpos
  refine quarter_le_measureReal_downSet hB.toIsPreBrownianReal hBm ?_ ?_
  · rw [measureReal_def]
    have h34 : (3 / 4 : ℝ) = (ENNReal.ofReal (3 / 4)).toReal := by
      rw [ENNReal.toReal_ofReal (by norm_num)]
    rw [h34]
    exact ENNReal.toReal_mono (measure_ne_top _ _) hmB.le
  · refine (measureReal_abs_lt_le hB.toIsPreBrownianReal hBm hh0 (by positivity)).trans ?_
    have hs : (h : ℝ) / √(h : ℝ) = √(h : ℝ) := Real.div_sqrt
    rw [mul_div_assoc, hs]
    exact hmC

end Choose

/-! ### Lipschitz targets -/

section Lipschitz

variable [IsProbabilityMeasure P] {δ : ℝ}

/-- **Support theorem for Lipschitz targets, rational times.** If `f 0 = 0` and `f` is `L`-Lipschitz on
`[0, T + 1]`, then with positive probability `|B_q − f(q)| < δ` at every rational `q ≤ T`. -/
theorem measure_ratTube_pos_of_lipschitz (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    {f : ℝ≥0 → ℝ} (hf0 : f 0 = 0) {L : ℝ} (hL : 0 ≤ L) {T : ℝ≥0}
    (hf : ∀ s t : ℝ≥0, s ≤ t → t ≤ T + 1 → |f t - f s| ≤ L * ((t : ℝ) - s)) (hδ : 0 < δ) :
    0 < P {ω | ∀ q : ℚ≥0, (q : ℝ≥0) ≤ T → |B q ω - f q| < δ} := by
  obtain ⟨h, hpos, hle1, hLh, hc⟩ := exists_step hB hBm hδ hL
  have hhpos : (0 : ℝ) < ((h : ℝ≥0) : ℝ) := by exact_mod_cast hpos
  set n : ℕ := ⌈(T : ℝ) / ((h : ℝ≥0) : ℝ)⌉₊ with hn
  have hcoe : ∀ k : ℕ, ((((k : ℚ≥0) * h : ℚ≥0) : ℝ≥0) : ℝ) = k * ((h : ℝ≥0) : ℝ) := by
    intro k; push_cast; rfl
  have hnT : (T : ℝ) ≤ n * ((h : ℝ≥0) : ℝ) := by
    rw [← div_le_iff₀ hhpos]; exact Nat.le_ceil _
  have hnT' : (n : ℝ) * ((h : ℝ≥0) : ℝ) < T + ((h : ℝ≥0) : ℝ) := by
    have h1 := Nat.ceil_lt_add_one (div_nonneg (NNReal.coe_nonneg T) hhpos.le)
    rw [← hn] at h1
    calc (n : ℝ) * ((h : ℝ≥0) : ℝ) < ((T : ℝ) / ((h : ℝ≥0) : ℝ) + 1) * ((h : ℝ≥0) : ℝ) :=
          mul_lt_mul_of_pos_right h1 hhpos
      _ = T + ((h : ℝ≥0) : ℝ) := by field_simp
  have hstep : ∀ k < n, ∀ s : ℝ≥0, (((k : ℚ≥0) * h : ℚ≥0) : ℝ≥0) ≤ s →
      s ≤ (((k : ℚ≥0) * h : ℚ≥0) : ℝ≥0) + h → |f s - f (((k : ℚ≥0) * h : ℚ≥0) : ℝ≥0)| ≤
        L * ((h : ℝ≥0) : ℝ) := by
    intro k hk s hks hsk
    have hks' : ((((k : ℚ≥0) * h : ℚ≥0) : ℝ≥0) : ℝ) ≤ s := NNReal.coe_le_coe.2 hks
    have hsk' : (s : ℝ) ≤ ((((k : ℚ≥0) * h : ℚ≥0) : ℝ≥0) : ℝ) + ((h : ℝ≥0) : ℝ) := by
      exact_mod_cast hsk
    rw [hcoe] at hks' hsk'
    have hk1 : ((k : ℝ) + 1) ≤ n := by exact_mod_cast hk
    have hsT : s ≤ T + 1 := by
      rw [← NNReal.coe_le_coe, NNReal.coe_add, NNReal.coe_one]
      nlinarith
    refine (hf _ s hks hsT).trans ?_
    rw [hcoe]
    exact mul_le_mul_of_nonneg_left (by linarith) hL
  have hpow := pow_le_measure_good hB.toIsPreBrownianReal hBm hf0 hδ hLh n
    (fun k hk => by exact_mod_cast hstep k hk)
  have hc0 : P {ω | (fun s => B s ω) ∈ downSet δ (L * ((h : ℝ≥0) : ℝ)) h} ≠ 0 := by
    intro h0
    rw [measureReal_def, h0, ENNReal.toReal_zero] at hc
    norm_num at hc
  have hsub : good B f δ (((n : ℚ≥0) * h : ℚ≥0) : ℝ≥0) ⊆
      {ω | ∀ q : ℚ≥0, (q : ℝ≥0) ≤ T → |B q ω - f q| < δ} := by
    intro ω hω q hq
    refine hω.1 q (hq.trans ?_)
    rw [← NNReal.coe_le_coe, hcoe]
    exact hnT
  exact (pos_iff_ne_zero.2 (pow_ne_zero n hc0)).trans_le (hpow.trans (measure_mono hsub))

end Lipschitz

/-! ### Continuous targets -/

section Continuous

variable [IsProbabilityMeasure P] {δ : ℝ}

/-- **Support theorem, rational times.** For a continuous `f` with `f 0 = 0`, with positive probability
`|B_q − f(q)| < δ` at every rational `q ≤ T`. -/
theorem measure_ratTube_pos (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t)) {f : ℝ≥0 → ℝ}
    (hf : Continuous f) (hf0 : f 0 = 0) (T : ℝ≥0) (hδ : 0 < δ) :
    0 < P {ω | ∀ q : ℚ≥0, (q : ℝ≥0) ≤ T → |B q ω - f q| < δ} := by
  set g : ℝ → ℝ := fun x => f x.toNNReal with hg
  have hgc : Continuous g := hf.comp continuous_real_toNNReal
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 ((T : ℝ) + 1) g hgc.continuousOn (δ / 4)
    (by positivity)
  have hpc : ContDiffOn ℝ 1 (fun x : ℝ => p.eval x) (Icc 0 ((T : ℝ) + 1)) := by
    have h0 := (p.contDiff_aeval (𝕜 := ℝ) 1).contDiffOn (s := Icc 0 ((T : ℝ) + 1))
    simpa only [Polynomial.coe_aeval_eq_eval] using h0
  obtain ⟨K, hK⟩ := hpc.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc
  set f' : ℝ≥0 → ℝ := fun t => p.eval (t : ℝ) - p.eval 0 with hf'
  have hf'0 : f' 0 = 0 := by simp [hf']
  have hmem : ∀ t : ℝ≥0, t ≤ T + 1 → (t : ℝ) ∈ Icc (0 : ℝ) ((T : ℝ) + 1) := fun t ht =>
    ⟨NNReal.coe_nonneg t, by exact_mod_cast ht⟩
  have hlip : ∀ s t : ℝ≥0, s ≤ t → t ≤ T + 1 → |f' t - f' s| ≤ (K : ℝ) * ((t : ℝ) - s) := by
    intro s t hst ht
    have h1 := hK.dist_le_mul (t : ℝ) (hmem t ht) (s : ℝ) (hmem s (hst.trans ht))
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hst))] at h1
    simp only [hf']
    rw [show p.eval (t : ℝ) - p.eval 0 - (p.eval (s : ℝ) - p.eval 0) = p.eval (t : ℝ) - p.eval (s : ℝ) by ring]
    exact h1
  have hpos := measure_ratTube_pos_of_lipschitz hB hBm hf'0 K.2 hlip (half_pos hδ)
  refine hpos.trans_le (measure_mono fun ω hω q hq => ?_)
  have h1 := hω q hq
  have h2 := hp ((q : ℝ≥0) : ℝ) (hmem q (hq.trans le_self_add))
  have h3 := hp 0 ⟨le_rfl, by positivity⟩
  have hgq : g (q : ℝ≥0) = f q := by simp [hg]
  have hg0 : g 0 = 0 := by simp [hg, hf0]
  rw [hgq] at h2
  rw [hg0, sub_zero] at h3
  have e : B q ω - f q = (B q ω - f' q) + (p.eval ((q : ℝ≥0) : ℝ) - f q) - p.eval 0 := by
    simp only [hf']; ring
  rw [e]
  calc |(B q ω - f' q) + (p.eval ((q : ℝ≥0) : ℝ) - f q) - p.eval 0|
      ≤ |B q ω - f' q| + |p.eval ((q : ℝ≥0) : ℝ) - f q| + |p.eval 0| :=
        (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ < δ / 2 + δ / 4 + δ / 4 := by linarith
    _ = δ := by ring

/-- A continuous function below `c` at the rational times `≤ T` is at most `c` on `[0, T]`. -/
theorem le_of_forall_nnrat_lt {φ : ℝ≥0 → ℝ} (hφ : Continuous φ) {T : ℝ≥0} {c : ℝ}
    (h : ∀ q : ℚ≥0, (q : ℝ≥0) ≤ T → φ q < c) : ∀ t ≤ T, φ t ≤ c := by
  intro t ht
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 (isOpen_lt continuous_const hφ) t hlt
  have hq : ∃ q : ℚ≥0, (q : ℝ≥0) ≤ t ∧ (t : ℝ) < (q : ℝ≥0) + η := by
    rcases lt_or_ge (t : ℝ) η with htη | htη
    · exact ⟨0, by simp, by simpa using htη⟩
    · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show (t : ℝ) - η < t by linarith)
      have hr0 : (0 : ℝ) ≤ r := by linarith
      have hcast : (((r.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = (r : ℝ) := by
        have h0 : (0 : ℚ) ≤ r := by exact_mod_cast hr0
        have h1 : ((r.toNNRat : ℚ≥0) : ℚ) = r := Rat.coe_toNNRat r h0
        conv_rhs => rw [← h1]
        norm_cast
      refine ⟨r.toNNRat, ?_, ?_⟩
      · rw [← NNReal.coe_le_coe, hcast]; exact hr2.le
      · rw [hcast]; linarith
  obtain ⟨q, hqt, htq⟩ := hq
  have hd : dist (q : ℝ≥0) t < η := by
    rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hqt))]
    linarith
  exact absurd (h q (hqt.trans ht)) (not_lt.2 (hball hd).le)

/-- **The support theorem for Brownian motion in the sup norm.** For a Brownian motion `B` with measurable
coordinates, a continuous `f` with `f 0 = 0`, `T ≥ 0` and `ε > 0`,
`P(|B_t − f(t)| < ε for every t ≤ T) > 0`. -/
theorem measure_forall_abs_sub_lt_pos (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    {f : ℝ≥0 → ℝ} (hf : Continuous f) (hf0 : f 0 = 0) (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    0 < P {ω | ∀ t ≤ T, |B t ω - f t| < ε} := by
  have hpos := measure_ratTube_pos hB hBm hf hf0 T (half_pos hε)
  have hcont : P {ω | Continuous (B · ω)}ᶜ = 0 := hB.cont
  rw [← measure_inter_conull hcont] at hpos
  refine hpos.trans_le (measure_mono fun ω ⟨hω, hc⟩ t ht => ?_)
  have hφ : Continuous fun s => |B s ω - f s| := (hc.sub hf).abs
  exact (le_of_forall_nnrat_lt hφ hω t ht).trans_lt (half_lt_self hε)

end Continuous

end InteractingSLE.BrownianSupport
