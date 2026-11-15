/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB8Proof


/-!
# Lemma GB8, the finite-energy buffer: Aux. 108 through an infinite horizon, and the restart

Packet PROVE-T14-TIP5 (route of `planning/handoffs/PROVE-T14-TIP4.md` §5.2, step 1). Specification supplement §8.8,
proof of **Lemma GB8** (`source/spec/p481-528.md` L1035–L1043, pp. 523–524): "Aux. 108 gives equivalence on the entire
stopped history, including the event of an infinite stopping time, by one strictly positive finite-energy density. It
therefore gives the same zero probability for the actual interior transient future. Countably many rational `q`,
reference choices, and buffers exclude the event of no far-left contact."

The buffer is the **energy buffer** `EnergySep m`: infinite lifetime, gaps bounded below on every bounded interval, and
energy of the change of weights `ρ → ρ′` (`pathEnergy`, the path form of `Zhan.changeEnergy`) at most `m` on every
horizon. Unlike the gap buffer of `Aux108Inf.sepSet` it contains the actual interior transient future
(`GB8Energy.lean`). The bound of `Aux108Inf.measure_sepHorizon_le` at horizon `N` depends only on `m`, not on the gap
level, so the union over gap levels is controlled by the reference probability of `posSetT N` (positive gaps before
`N`), which decreases to the reference probability of `posSet` (positive gaps forever) — zero by the reference's
finite swallow (`codeLaw_posSet_refW_eq_zero`, from `ReferenceSwallowStatement`, proved in `GB8InputsRef.lean`).

## Main results

* `pathEnergy`, `changeEnergy_eq_pathEnergy`, `measurable_pathEnergy_code` (the energy of a code is measurable);
* `EnergySep`, `energySet`, `posSetT`, `posSet` and their measurability; `le_of_forall_nnrat_lt`;
* `codeLaw_posSet_refW_eq_zero`: the GB8 reference leaves every positive-gap buffer;
* `codeLaw_energySet_le` (Aux. 108, energy buffer), **`codeLaw_energySet_eq_zero`**;
* **`measure_restart_energySep_eq_zero`**: at every rational time the restarted energy buffer is null.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB8

open Aux108Inf Zhan Coupling Sec7.RandRestart Sec2 Sec2.Assembly Girsanov Sec7.TrialsHi

variable {nL nR : ℕ}

/-! ### The energy along deterministic paths -/

/-- The energy `κ⁻¹ ∫₀ᵀ (Σⱼ (ρ′ⱼ − ρⱼ)/(w − uⱼ))²` of the change of weights `ρ → ρ′` along deterministic paths
(`Zhan.changeEnergy` for a one-point sample space). -/
def pathEnergy (κ : ℝ) (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (T : ℝ≥0) : ℝ :=
  changeEnergy κ ρL ρL' ρR ρR' (Ω := Unit) (fun t _ => w t) (fun i t _ => vL i t) (fun j t _ => vR j t) T ()

/-- The energy of processes is the path energy of their samples. -/
theorem changeEnergy_eq_pathEnergy (κ : ℝ) (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ) {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    changeEnergy κ ρL ρL' ρR ρR' W VL VR T ω =
      pathEnergy κ ρL ρL' ρR ρR' (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) T := by
  unfold pathEnergy changeEnergy
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  cases j using Fin.addCases with
  | left i => simp [allMarks]
  | right i => simp [allMarks]

/-- The path energy of the decoded state of a code is a measurable function of the code. -/
theorem measurable_pathEnergy_code (κ : ℝ) (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ) (T : ℝ≥0) :
    Measurable fun x : XCode nL nR => pathEnergy κ ρL ρL' ρR ρR' (cw x) (cvL x) (cvR x) T := by
  have e : (fun x : XCode nL nR => pathEnergy κ ρL ρL' ρR ρR' (cw x) (cvL x) (cvR x) T) = fun x =>
      changeEnergy κ ρL ρL' ρR ρR' (fun t (x : XCode nL nR) => cw x t) (fun i t x => cvL x i t)
        (fun j t x => cvR x j t) T x :=
    funext fun x => (changeEnergy_eq_pathEnergy κ ρL ρL' ρR ρR' (fun t (x : XCode nL nR) => cw x t)
      (fun i t x => cvL x i t) (fun j t x => cvR x j t) T x).symm
  rw [e]
  unfold changeEnergy
  refine measurable_const.mul ?_
  have hF : Measurable fun p : XCode nL nR × ℝ => (∑ j, weightDiff ρL ρL' ρR ρR' j /
      (cw p.1 p.2.toNNReal - allMarks (fun i t (x : XCode nL nR) => cvL x i t) (fun j t x => cvR x j t) j
        p.2.toNNReal p.1)) ^ 2 := by
    have hU : ∀ j, Measurable fun p : XCode nL nR × ℝ =>
        allMarks (fun i t (x : XCode nL nR) => cvL x i t) (fun j t x => cvR x j t) j p.2.toNNReal p.1 := by
      intro j
      cases j using Fin.addCases with
      | left i => simpa [allMarks] using measurable_cvL_real i
      | right i => simpa [allMarks] using measurable_cvR_real i
    have hj : ∀ j, Measurable fun p : XCode nL nR × ℝ => weightDiff ρL ρL' ρR ρR' j /
        (cw p.1 p.2.toNNReal - allMarks (fun i t (x : XCode nL nR) => cvL x i t) (fun j t x => cvR x j t) j
          p.2.toNNReal p.1) := fun j =>
      Measurable.div measurable_const ((measurable_cw_real (nL := nL) (nR := nR)).sub (hU j))
    exact (Finset.measurable_sum Finset.univ fun j _ => hj j).pow_const 2
  have h := hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ).restrict (Ioc 0 (T : ℝ)))
  convert h.measurable using 1
  funext x
  rw [intervalIntegral.integral_of_le T.coe_nonneg]


/-! ### The energy buffer as a state event and as a set of codes -/

/-- **The energy buffer, as a state event**: infinite lifetime, gaps bounded below on every bounded interval (at the
rational times), and energy of the change `ρ → ρ′` at most `m` on every horizon. -/
def EnergySep (κ : ℝ) (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ) (m : ℝ) (w : ℝ≥0 → ℝ)
    (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (τ : ℝ≥0∞) : Prop :=
  τ = ⊤ ∧ (∀ N : ℕ, ∃ n : ℕ, ∀ p : ℚ≥0, (p : ℝ≥0) < N →
      1 / ((n : ℝ) + 1) ≤ minGap ((w p, fun i => vL i p, fun j => vR j p) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) ∧
    ∀ N : ℕ, pathEnergy κ ρL ρL' ρR ρR' w vL vR N ≤ m

/-- The codes in the energy buffer. -/
def energySet (κ : ℝ) (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ) (m : ℝ) : Set (XCode nL nR) :=
  {x | EnergySep κ ρL ρL' ρR ρR' m (cw x) (cvL x) (cvR x) (cζ x)}

/-- Codes alive at least until `N` whose gaps are bounded below at the rational times before `N`. -/
def posSetT (N : ℕ) : Set (XCode nL nR) :=
  {x | ((N : ℝ≥0) : ℝ≥0∞) ≤ cζ x ∧ ∃ n : ℕ, ∀ p : ℚ≥0, (p : ℝ≥0) < N →
    1 / ((n : ℝ) + 1) ≤ minGap (Assembly.stateAt x p)}

/-- Codes with infinite lifetime whose gaps are bounded below on every bounded interval. -/
def posSet : Set (XCode nL nR) :=
  {x | cζ x = ⊤ ∧ ∀ N : ℕ, ∃ n : ℕ, ∀ p : ℚ≥0, (p : ℝ≥0) < N →
    1 / ((n : ℝ) + 1) ≤ minGap (Assembly.stateAt x p)}

theorem measurableSet_gapsT (N n : ℕ) : MeasurableSet {x : XCode nL nR | ∀ p : ℚ≥0, (p : ℝ≥0) < N →
    1 / ((n : ℝ) + 1) ≤ minGap (Assembly.stateAt x p)} :=
  measurableSet_setOfPred.2 (Measurable.forall fun _ => measurable_const_imp _ (measurableSet_setOfPred.1
    (measurableSet_le measurable_const (continuous_minGap.measurable.comp (measurable_stateAt _)))))

theorem measurableSet_posSetT (N : ℕ) : MeasurableSet (posSetT (nL := nL) (nR := nR) N) := by
  have : posSetT (nL := nL) (nR := nR) N = {x | ((N : ℝ≥0) : ℝ≥0∞) ≤ cζ x} ∩
      ⋃ n : ℕ, {x | ∀ p : ℚ≥0, (p : ℝ≥0) < N → 1 / ((n : ℝ) + 1) ≤ minGap (Assembly.stateAt x p)} := by
    ext x; simp [posSetT]
  rw [this]
  exact (measurableSet_le measurable_const measurable_cζ).inter
    (MeasurableSet.iUnion fun n => measurableSet_gapsT N n)

theorem antitone_posSetT : Antitone fun N : ℕ => posSetT (nL := nL) (nR := nR) N := by
  intro N N' hNN' x hx
  obtain ⟨hζ, n, hn⟩ := hx
  have h1 : ((N : ℝ≥0) : ℝ≥0∞) ≤ ((N' : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hNN'
  refine ⟨h1.trans hζ, n, fun p hp => hn p (lt_of_lt_of_le hp ?_)⟩
  exact_mod_cast hNN'

theorem iInter_posSetT : (⋂ N : ℕ, posSetT (nL := nL) (nR := nR) N) = posSet := by
  ext x
  simp only [mem_iInter, posSetT, posSet, mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨?_, fun N => (h N).2⟩
    by_contra hne
    obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hne
    have := (h k).1
    push_cast at this
    exact absurd hk (not_lt.2 this)
  · rintro ⟨hζ, hg⟩ N
    exact ⟨by rw [hζ]; exact le_top, hg N⟩

theorem measurableSet_posSet : MeasurableSet (posSet (nL := nL) (nR := nR)) := by
  rw [← iInter_posSetT]
  exact MeasurableSet.iInter fun N => measurableSet_posSetT N

theorem measurableSet_energySet (κ : ℝ) (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ) (m : ℝ) :
    MeasurableSet (energySet κ ρL ρL' ρR ρR' m) := by
  have : energySet κ ρL ρL' ρR ρR' m = posSet ∩
      ⋂ N : ℕ, {x | pathEnergy κ ρL ρL' ρR ρR' (cw x) (cvL x) (cvR x) N ≤ m} := by
    ext x
    simp only [energySet, EnergySep, posSet, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩
  rw [this]
  exact measurableSet_posSet.inter (MeasurableSet.iInter fun N =>
    measurableSet_le (measurable_pathEnergy_code κ ρL ρL' ρR ρR' N) measurable_const)

/-- `EnergySep` depends only on the state before the lifetime (here: everywhere, as the lifetime is infinite). -/
theorem energySep_congr {κ : ℝ} {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ} {m : ℝ} (w w' : ℝ≥0 → ℝ)
    (vL vL' : Fin nL → ℝ≥0 → ℝ) (vR vR' : Fin nR → ℝ≥0 → ℝ) (τ : ℝ≥0∞)
    (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t)
    (hs : EnergySep κ ρL ρL' ρR ρR' m w vL vR τ) : EnergySep κ ρL ρL' ρR ρR' m w' vL' vR' τ := by
  have hτ := hs.1
  have hall : ∀ t : ℝ≥0, w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t := fun t =>
    h t (by rw [hτ]; exact ENNReal.coe_lt_top)
  have hw : w = w' := funext fun t => (hall t).1
  have hvL : vL = vL' := funext fun i => funext fun t => (hall t).2.1 i
  have hvR : vR = vR' := funext fun j => funext fun t => (hall t).2.2 j
  subst hw hvL hvR
  exact hs

/-! ### Rational lower bounds before a horizon -/

/-- A continuous function on `ℝ≥0` at least `δ` at every nonnegative rational before `N` is at least `δ` on
`[0, N)`. -/
theorem le_of_forall_nnrat_lt {f : ℝ≥0 → ℝ} (hf : Continuous f) {δ : ℝ} {N : ℝ≥0}
    (h : ∀ q : ℚ≥0, (q : ℝ≥0) < N → δ ≤ f q) {s : ℝ≥0} (hs : s < N) : δ ≤ f s := by
  by_contra hlt
  push Not at hlt
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hf.continuousAt.preimage_mem_nhds (Iio_mem_nhds hlt))
  have hNs : (0 : ℝ) < (N : ℝ) - s := by rw [sub_pos]; exact_mod_cast hs
  obtain ⟨p, hp1, hp2⟩ := Zhan.exists_nnrat_near s (lt_min hε hNs)
  have hp : (p : ℝ≥0) ∈ Metric.ball s ε := by
    rw [Metric.mem_ball, NNReal.dist_eq, abs_sub_lt_iff]
    have : (s : ℝ) ≤ ((p : ℝ≥0) : ℝ) := by exact_mod_cast hp1
    constructor <;> linarith [min_le_left ε ((N : ℝ) - s)]
  have hpN : (p : ℝ≥0) < N := by
    have : ((p : ℝ≥0) : ℝ) < N := by linarith [min_le_right ε ((N : ℝ) - s)]
    exact_mod_cast this
  exact absurd (h p hpN) (not_le.2 (hball hp))


/-! ### The GB8 reference leaves every positive-gap buffer -/

/-- The state event of `posSet`. -/
def PosForever (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (τ : ℝ≥0∞) : Prop :=
  τ = ⊤ ∧ ∀ N : ℕ, ∃ n : ℕ, ∀ p : ℚ≥0, (p : ℝ≥0) < N →
    1 / ((n : ℝ) + 1) ≤ minGap ((w p, fun i => vL i p, fun j => vR j p) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))

theorem posForever_congr (w w' : ℝ≥0 → ℝ) (vL vL' : Fin nL → ℝ≥0 → ℝ) (vR vR' : Fin nR → ℝ≥0 → ℝ)
    (τ : ℝ≥0∞) (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t)
    (hs : PosForever w vL vR τ) : PosForever w' vL' vR' τ := by
  have hτ := hs.1
  have hall : ∀ t : ℝ≥0, w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t := fun t =>
    h t (by rw [hτ]; exact ENNReal.coe_lt_top)
  have hw : w = w' := funext fun t => (hall t).1
  have hvL : vL = vL' := funext fun i => funext fun t => (hall t).2.1 i
  have hvR : vR = vR' := funext fun j => funext fun t => (hall t).2.2 j
  subst hw hvL hvR
  exact hs

/-- **The GB8 reference leaves every positive-gap buffer** (from `ReferenceSwallowStatement`): from every ordered
word with marks off the seed, the canonical law of the reference gives `posSet` probability `0`. -/
theorem codeLaw_posSet_refW_eq_zero (hRef : ReferenceSwallowStatement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hnL : 0 < nL) (hnR : 0 < nR) {y : (Fin nL → ℝ) × (Fin nR → ℝ)} (hord : IsOrderedForceWord y.1 y.2)
    (hL0 : ∀ i, y.1 i < 0) (hR0 : ∀ j, 0 < y.2 j) :
    codeLaw κ (refW nL (κ - 4)) (refW nR (κ / 2 - 2)) posSet y = 0 := by
  obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE'⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hord (ρL := refW nL (κ - 4)) (ρR := refW nR (κ / 2 - 2))
  have hsep : ∀ i j, y.1 i < y.2 j := fun i j => (hL0 i).trans (hR0 j)
  rw [← ZhanGT4.measure_eventOf_eq_codeLaw_state hκ hsep hE' (S := posSet) (Ψ := PosForever)
    measurableSet_posSet (fun x _ _ => Iff.rfl) posForever_congr]
  refine measure_mono_null (fun ω hω => ?_)
    (ae_iff.1 ((hRef κ hκ hκ4 nL nR hnL hnR y.1 y.2 hord hL0 hR0 P' 𝓕' W' VL' VR' B' ζ' hE').and hE'.2.2.2.2))
  rintro ⟨hr, hp⟩
  obtain ⟨hζ, hq⟩ := hω
  rcases hr with hne | ⟨t, -, heq⟩
  · exact hne hζ
  have hpF := hp.isForcePath
  have hcon : ContinuousOn (fun s => stateAt W' VL' VR' s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ' ω} :=
    hpF.continuousOn_w.prodMk ((continuousOn_pi.2 hpF.continuousOn_vL).prodMk (continuousOn_pi.2 hpF.continuousOn_vR))
  have hc : Continuous fun s => minGap (stateAt W' VL' VR' s ω) := by
    rw [hζ] at hcon
    exact continuous_minGap.comp (continuousOn_univ.1 (hcon.mono fun _ _ => ENNReal.coe_lt_top))
  obtain ⟨n, hn⟩ := hq (⌈(t : ℝ)⌉₊ + 1)
  have htN : t < ((⌈(t : ℝ)⌉₊ + 1 : ℕ) : ℝ≥0) := by
    have : (t : ℝ) < ((⌈(t : ℝ)⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast; linarith [Nat.le_ceil (t : ℝ)]
    exact_mod_cast this
  have h1 := le_of_forall_nnrat_lt hc (fun q hq' => hn q hq') htN
  have h2 : minGap (stateAt W' VL' VR' t ω) ≤ 0 := by
    refine (Finset.inf'_le _ (Finset.mem_univ (some (Sum.inl ⟨nL - 1, Nat.sub_lt hnL one_pos⟩)))).trans
      (le_of_eq ?_)
    show |W' t ω - VL' ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ t ω| = 0
    rw [heq, sub_self, abs_zero]
  have h3 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith


/-! ### Aux. 108 with the energy buffer -/

/-- **Aux. lemma 108 with the energy buffer, canonical form** (HBT1, one horizon `N`): for an ordered word with
marks off the seed, the canonical law of `ρ` gives the energy buffer at level `m` at most
`(e^m)^{1/2} · codeLaw ρ′ (posSetT N)^{1/2}`. The energy level `m` replaces the gap level of
`Aux108Inf.codeLaw_sepSet_le`; the constant does not depend on the gap level or on `N`. -/
theorem codeLaw_energySet_le {κ : ℝ} (hκ : 0 < κ) {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ}
    {y : (Fin nL → ℝ) × (Fin nR → ℝ)} (hord : IsOrderedForceWord y.1 y.2) (hL0 : ∀ i, y.1 i < 0)
    (hR0 : ∀ j, 0 < y.2 j) (m : ℝ) (N : ℕ) :
    codeLaw κ ρL ρR (energySet κ ρL ρL' ρR ρR' m) y ≤
      ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) * codeLaw κ ρL' ρR' (posSetT N) y ^ (1 / 2 : ℝ) := by
  obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE'⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hord (ρL := ρL) (ρR := ρR)
  have hsep : ∀ i j, y.1 i < y.2 j := fun i j => (hL0 i).trans (hR0 j)
  obtain ⟨G, hG, hGc0, hGthr, hGc⟩ := exists_good hκ hL0 hR0 hE'
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE'
  rw [← ZhanGT4.measure_eventOf_eq_codeLaw_state hκ hsep hE' (S := energySet κ ρL ρL' ρR ρR' m)
    (Ψ := EnergySep κ ρL ρL' ρR ρR' m) (measurableSet_energySet κ ρL ρL' ρR ρR' m) (fun x _ _ => Iff.rfl)
    energySep_congr]
  set Hn : ℕ → Set Ω' := fun n => horizonEvent κ ρL ρL' ρR ρR' G W' VL' VR' (1 / ((n : ℝ) + 1)) (N : ℝ≥0) m
    (fun _ => True) with hHn
  have hmono : Monotone Hn := by
    intro n n' hnn' ω hω
    obtain ⟨hωG, hgap, hen, hΦ⟩ := hω
    refine ⟨hωG, fun s hs => le_trans ?_ (hgap s hs), hen, hΦ⟩
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : (n : ℝ) + 1 ≤ (n' : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hnn'
    exact one_div_le_one_div_of_le h1 h2
  have hHn : ∀ n, P' (Hn n) ≤ ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) *
      codeLaw κ ρL' ρR' (posSetT N) y ^ (1 / 2 : ℝ) := fun n =>
    measure_sepHorizon_le (ρL' := ρL') (ρR' := ρR') hκ hord hsep hE𝓖 hG hGthr hGc (by positivity) (N : ℝ≥0) m
      (measurableSet_posSetT N) fun x _ hT hg => ⟨hT, n, fun p hp => hg p hp⟩
  calc P' {ω | EnergySep κ ρL ρL' ρR ρR' m (fun t => W' t ω) (fun i t => VL' i t ω) (fun j t => VR' j t ω) (ζ' ω)}
      ≤ P' ((⋃ n, Hn n) ∪ Gᶜ) := by
        refine measure_mono fun ω hω => ?_
        by_cases hωG : ω ∈ G
        · refine Or.inl ?_
          obtain ⟨hζ, hgap, hen⟩ := hω
          obtain ⟨n, hn⟩ := hgap (N + 1)
          have hc := hGc ω hωG
          rw [hζ] at hc
          have hc' : Continuous fun s => minGap (stateAt W' VL' VR' s ω) :=
            continuous_minGap.comp (continuousOn_univ.1 (hc.mono fun _ _ => ENNReal.coe_lt_top))
          refine mem_iUnion.2 ⟨n, hωG, fun s hs => ?_, ?_, trivial⟩
          · refine le_of_forall_nnrat_lt hc' (N := ((N + 1 : ℕ) : ℝ≥0)) (fun q hq => hn q hq) ?_
            have : (s : ℝ) < ((N + 1 : ℕ) : ℝ) := by
              have := NNReal.coe_le_coe.2 hs
              push_cast at this ⊢; linarith
            exact_mod_cast this
          · rw [changeEnergy_eq_pathEnergy]
            exact hen N
        · exact Or.inr hωG
    _ ≤ P' (⋃ n, Hn n) + P' Gᶜ := measure_union_le _ _
    _ = P' (⋃ n, Hn n) := by rw [hGc0, add_zero]
    _ = ⨆ n, P' (Hn n) := hmono.measure_iUnion
    _ ≤ _ := iSup_le hHn

/-- **Zero probability transfers through the energy buffer** (GB8, p. 524: "It therefore gives the same zero
probability for the actual interior transient future"): from every ordered word with marks off the seed, the
canonical law of the GB8 word `ρ` gives every energy buffer probability `0`, since the reference leaves every
positive-gap buffer. -/
theorem codeLaw_energySet_eq_zero (hRef : ReferenceSwallowStatement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hnL : 0 < nL) (hnR : 0 < nR) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {y : (Fin nL → ℝ) × (Fin nR → ℝ)}
    (hord : IsOrderedForceWord y.1 y.2) (hL0 : ∀ i, y.1 i < 0) (hR0 : ∀ j, 0 < y.2 j) (m : ℝ) :
    codeLaw κ ρL ρR (energySet κ ρL (refW nL (κ - 4)) ρR (refW nR (κ / 2 - 2)) m) y = 0 := by
  have hlim := Zhan.tendsto_codeLaw_of_antitone (a := κ) (ρL := refW nL (κ - 4)) (ρR := refW nR (κ / 2 - 2))
    (fun N => measurableSet_posSetT (nL := nL) (nR := nR) N) antitone_posSetT y
  rw [iInter_posSetT, codeLaw_posSet_refW_eq_zero hRef hκ hκ4 hnL hnR hord hL0 hR0] at hlim
  have h1 : Tendsto (fun N : ℕ => ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) *
      codeLaw κ (refW nL (κ - 4)) (refW nR (κ / 2 - 2)) (posSetT N) y ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have h2 := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto _).comp hlim
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
    have hne : ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) ENNReal.ofReal_ne_top
    simpa using ENNReal.Tendsto.const_mul h2 (Or.inr hne)
  exact le_antisymm (ge_of_tendsto' h1 fun N => codeLaw_energySet_le hκ hord hL0 hR0 m N) bot_le


/-! ### The restart at a rational time -/

/-- A positive smallest gap puts every mark strictly off the driver. -/
theorem lt_of_minGap_pos {w : ℝ} {vL : Fin nL → ℝ} {vR : Fin nR → ℝ}
    (h : 0 < minGap ((w, vL, vR) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) (hL : ∀ i, vL i ≤ w) (hR : ∀ j, w ≤ vR j) :
    (∀ i, vL i < w) ∧ ∀ j, w < vR j := by
  refine ⟨fun i => lt_of_le_of_ne (hL i) fun he => ?_, fun j => lt_of_le_of_ne (hR j) fun he => ?_⟩
  · have h1 : minGap ((w, vL, vR) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) ≤ |w - vL i| :=
      Finset.inf'_le _ (Finset.mem_univ (some (Sum.inl i)))
    rw [he, sub_self, abs_zero] at h1
    linarith
  · have h1 : minGap ((w, vL, vR) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) ≤ |w - vR j| :=
      Finset.inf'_le _ (Finset.mem_univ (some (Sum.inr j)))
    rw [← he, sub_self, abs_zero] at h1
    linarith

/-- **The restarted energy buffer is null** (GB8, p. 524: "Countably many rational `q`, reference choices, and buffers
exclude the event of no far-left contact"): for the GB8 weights `ρ` compared with the reference, at every rational
`q > 0` the event "alive at `q` with every mark off the driver, and the restarted state in the energy buffer at level
`m`" has probability `0` (restart at `q`, `ZhanGT4.measure_restart_stateEvent`, and `codeLaw_energySet_eq_zero`). -/
theorem measure_restart_energySep_eq_zero (hRef : ReferenceSwallowStatement.{0}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) (hnL : 0 < nL) (hnR : 0 < nR) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (q : ℝ≥0) (hq : 0 < q) (m : ℝ) :
    P {ω | (q : ℝ≥0∞) < ζ ω ∧ 0 < minGap (stateAt W VL VR q ω) ∧
      EnergySep κ ρL (refW nL (κ - 4)) ρR (refW nR (κ / 2 - 2)) m (fun t => W (q + t) ω - W q ω)
        (fun i t => VL i (q + t) ω - W q ω) (fun j t => VR j (q + t) ω - W q ω) (ζ ω - q)} = 0 := by
  have hT : IsStoppingTime 𝓕 fun _ : Ω => ((q : ℝ≥0) : WithTop ℝ≥0) := isStoppingTime_const 𝓕 _
  set A := {ω | (q : ℝ≥0∞) < ζ ω ∧ (fun p => -minGap p) (stateAt W VL VR q ω) < 0} with hAdef
  have hA : MeasurableSet[hT.measurableSpace] A := by
    rw [IsStoppingTime.measurableSpace_const]
    exact measurableSet_lt_zeta_and_lt hE.2.1 hE.2.2.1 hE.2.2.2.1 continuous_minGap.neg 0 q
  have hAm : MeasurableSet A := hT.measurableSpace_le _ hA
  have hres := ZhanGT4.measure_restart_stateEvent hκ hE hT hA (fun ω hω => ⟨hω.1, Or.inl hq⟩)
    (S := energySet κ ρL (refW nL (κ - 4)) ρR (refW nR (κ / 2 - 2)) m)
    (Ψ := EnergySep κ ρL (refW nL (κ - 4)) ρR (refW nR (κ / 2 - 2)) m)
    (measurableSet_energySet κ ρL _ ρR _ m) (fun x _ _ => Iff.rfl) energySep_congr
  have hzero : ∫⁻ ω in A, codeLaw κ ρL ρR (energySet κ ρL (refW nL (κ - 4)) ρR (refW nR (κ / 2 - 2)) m)
      (wordAt W VL VR (fun _ => q) ω) ∂P = 0 := by
    rw [setLIntegral_congr_fun_ae hAm (g := fun _ => 0) ?_, lintegral_zero]
    filter_upwards [hE.2.2.2.2] with ω hp hωA
    have hpF := hp.isForcePath
    have hqζ : (q : ℝ≥0∞) < ζ ω := hωA.1
    have hpos : 0 < minGap (stateAt W VL VR q ω) := by
      have h : -minGap (stateAt W VL VR q ω) < 0 := hωA.2
      linarith
    obtain ⟨hoL, hoR⟩ := lt_of_minGap_pos hpos (fun i => hpF.vL_le_w hqζ i) (fun j => hpF.w_le_vR hqζ j)
    have hord : IsOrderedForceWord (wordAt W VL VR (fun _ => q) ω).1 (wordAt W VL VR (fun _ => q) ω).2 :=
      ⟨fun i i' hii' => sub_le_sub_right (hpF.antitone_vL hqζ hii') _, fun i => (sub_neg.2 (hoL i)).le,
        fun j j' hjj' => sub_le_sub_right (hpF.monotone_vR hqζ hjj') _, fun j => (sub_pos.2 (hoR j)).le⟩
    exact codeLaw_energySet_eq_zero hRef hκ hκ4 hnL hnR hord (fun i => sub_neg.2 (hoL i))
      (fun j => sub_pos.2 (hoR j)) m
  have hset : {ω | (q : ℝ≥0∞) < ζ ω ∧ 0 < minGap (stateAt W VL VR q ω) ∧
      EnergySep κ ρL (refW nL (κ - 4)) ρR (refW nR (κ / 2 - 2)) m (fun t => W (q + t) ω - W q ω)
        (fun i t => VL i (q + t) ω - W q ω) (fun j t => VR j (q + t) ω - W q ω) (ζ ω - q)} =
      A ∩ {ω | EnergySep κ ρL (refW nL (κ - 4)) ρR (refW nR (κ / 2 - 2)) m (fun t => W (q + t) ω - W q ω)
        (fun i t => VL i (q + t) ω - W q ω) (fun j t => VR j (q + t) ω - W q ω) (ζ ω - q)} := by
    ext ω
    simp only [hAdef, mem_inter_iff, mem_ofPred_eq, neg_lt_zero]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩
  rw [hset, hres, hzero]

end InteractingSLE.Supp8.GB8
