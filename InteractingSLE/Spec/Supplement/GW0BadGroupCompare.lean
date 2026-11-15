/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LP4SwallowCompare

/-!
# Aux. lemma 108, driver form, through a common continuation threshold

Packet PROVE-T14-GW3 (Lemma GW0, third sentence; supplement p. 617, proof "the compactly supported finite-energy cutoff
used in BR3 and Aux. 108 transfers this positive-probability whole-history common-threshold event to the original
word"; BR3, p. 609: "Aux. 108 transfers the positive-probability event that the common threshold at `a` is reached
before the buffer is swallowed. All changed groups lie beyond the crosscut and remain separated").

The landed driver-form comparisons (`Sec7.TrialsHi.measure_horizonEvent_le`, `Sec7.TrialsHi4.measure_horizonEventL_le`)
need the reference law to have an infinite lifetime and every gap (or every left gap) bounded below. Here the reference
law (weights `ρ`, the law that is run) may **end at a finite continuation threshold**, and only the marks whose weights
change (`ρ' ≠ ρ`) are kept away from the driver; the unchanged marks may collide with it, including at the end.

**The comparison.** On the event that the reference lifetime is `< T` and every changed mark stays at distance `≥ δ`
before it (`refEvent`), Girsanov's theorem with the bounded drift of the change of weights
(`Sec2.IsSLEEvolutionUpTo.girsanov_changeWeights`, stopped when a changed gap falls below `δ` or a continuous
functional `Ψ` of the state falls below `ε`) and pathwise uniqueness of the proposed law
(`Sec2.Assembly.UpTo.agree_of_lt_min`) put the canonical solution of the proposed weights in the code set
`codeSet` (`Ψ < 2ε` at a rational time before `T` with the changed gaps `≥ δ` up to it, or lifetime `≤ T`), with
probability at least `P(refEvent)² e^{−m}`, `m` independent of `ε` (`sq_measure_refEvent_le`). Letting `ε → 0`, if
`Ψ = 0` with the changed gaps `≥ δ` forces a threshold of the proposed weights (`hthr`), the proposed canonical
lifetime is `≤ T` with positive probability (`codeLaw_lifetime_le_pos`), and so is the lifetime of every evolution of
the proposed weights from the same separated start (`measure_lifetime_le_pos`).

`Ψ` must tend to `0` at every finite reference lifetime (`hGΨ`); in BR3 it is the gap to the first bad mark.

## Main results

* `chGap`: the smallest gap between the driver and the changed marks (capped at `1`);
* `sq_measure_refEvent_le`: the comparison at level `ε`;
* **`codeLaw_lifetime_le_pos`**, **`measure_lifetime_le_pos`**: the transfer of a positive-probability common
  threshold to the proposed weights.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace GW0BadGroup

open Zhan Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart Girsanov Coupling

/-! ### The gap to the changed marks -/

section ChGap

variable {nL nR : ℕ}

/-- The state with every mark whose weight does not change moved to distance `1` from the driver. -/
def chState (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ) (p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :
    ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  (p.1, fun i => if ρL' i = ρL i then p.1 - 1 else p.2.1 i,
    fun j => if ρR' j = ρR j then p.1 + 1 else p.2.2 j)

/-- The smallest gap between the driver and the marks whose weights change, capped at `1`. -/
def chGap (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ) (p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : ℝ :=
  minGap (chState ρL ρL' ρR ρR' p)

variable {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ}

theorem continuous_chGap : Continuous (chGap ρL ρL' ρR ρR') := by
  refine continuous_minGap.comp (continuous_fst.prodMk ((continuous_pi fun i => ?_).prodMk
    (continuous_pi fun j => ?_)))
  · by_cases h : ρL' i = ρL i
    · simp only [h, ↓reduceIte]; fun_prop
    · simp only [h, ↓reduceIte]; fun_prop
  · by_cases h : ρR' j = ρR j
    · simp only [h, ↓reduceIte]; fun_prop
    · simp only [h, ↓reduceIte]; fun_prop

theorem le_chGap_iff {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)} {δ : ℝ} :
    δ ≤ chGap ρL ρL' ρR ρR' p ↔ δ ≤ 1 ∧ (∀ i, ρL' i ≠ ρL i → δ ≤ |p.1 - p.2.1 i|) ∧
      ∀ j, ρR' j ≠ ρR j → δ ≤ |p.1 - p.2.2 j| := by
  rw [chGap, le_minGap_iff]
  simp only [chState]
  constructor
  · rintro ⟨h1, hL, hR⟩
    refine ⟨h1, fun i hi => ?_, fun j hj => ?_⟩
    · have := hL i; simpa only [hi, ↓reduceIte] using this
    · have := hR j; simpa only [hj, ↓reduceIte] using this
  · rintro ⟨h1, hL, hR⟩
    refine ⟨h1, fun i => ?_, fun j => ?_⟩
    · by_cases hi : ρL' i = ρL i
      · simp only [hi, ↓reduceIte, sub_sub_cancel, abs_one]; exact h1
      · simp only [hi, ↓reduceIte]; exact hL i hi
    · by_cases hj : ρR' j = ρR j
      · simp only [hj, ↓reduceIte, sub_add_cancel_left, abs_neg, abs_one]; exact h1
      · simp only [hj, ↓reduceIte]; exact hR j hj

/-- A changed mark at gap `≥ δ > 0` is not at the driver. -/
theorem ne_of_le_chGap {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)} {δ : ℝ} (hδ : 0 < δ)
    (h : δ ≤ chGap ρL ρL' ρR ρR' p) :
    (∀ i, ρL' i ≠ ρL i → p.2.1 i ≠ p.1) ∧ ∀ j, ρR' j ≠ ρR j → p.2.2 j ≠ p.1 := by
  obtain ⟨-, hL, hR⟩ := le_chGap_iff.1 h
  refine ⟨fun i hi he => ?_, fun j hj he => ?_⟩
  · have := hL i hi; rw [he, sub_self, abs_zero] at this; linarith
  · have := hR j hj; rw [he, sub_self, abs_zero] at this; linarith

end ChGap

/-! ### The stopping time -/

section Stop

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The first time before `ζ` at which a functional of the state is below `ε`, on `G` (`⊤` off `G`). -/
def hitOn (G : Set Ω) (Φ : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ) (ε : ℝ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) : Ω → WithTop ℝ≥0 := fun ω =>
  open Classical in
  if ω ∈ G then hitBelow (fun s => Φ (Coupling.stateAt W VL VR s ω)) (ζ ω) ε else ⊤

/-- The comparison stop: the first time a changed gap is below `δ` or `Ψ` is below `ε`, capped at `T`, on `G`
(`0` off `G`). -/
def cmpStop (G : Set Ω) (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ) (Ψ : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ)
    (δ ε : ℝ) (T : ℝ≥0) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) : Ω → ℝ≥0∞ := fun ω =>
  open Classical in
  if ω ∈ G then ((capTime (fun ω => min (hitOn G (chGap ρL ρL' ρR ρR') δ ζ W VL VR ω)
    (hitOn G Ψ ε ζ W VL VR ω)) T ω : ℝ≥0) : ℝ≥0∞) else 0

variable {G : Set Ω} {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ}
  {Ψ : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ} {δ ε : ℝ} {T : ℝ≥0} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem cmpStop_of_mem (hω : ω ∈ G) :
    (cmpStop G ρL ρL' ρR ρR' Ψ δ ε T ζ W VL VR ω : ℝ≥0∞) =
      ((min (min (hitBelow (fun s => chGap ρL ρL' ρR ρR' (Coupling.stateAt W VL VR s ω)) (ζ ω) δ)
        (hitBelow (fun s => Ψ (Coupling.stateAt W VL VR s ω)) (ζ ω) ε)) (T : WithTop ℝ≥0)).untopD T : ℝ≥0) := by
  simp only [cmpStop, hω, ↓reduceIte, capTime, hitOn]

theorem cmpStop_le (ω : Ω) : cmpStop G ρL ρL' ρR ρR' Ψ δ ε T ζ W VL VR ω ≤ T := by
  unfold cmpStop
  split_ifs
  · have h := coe_capTime (fun ω => min (hitOn G (chGap ρL ρL' ρR ρR') δ ζ W VL VR ω)
      (hitOn G Ψ ε ζ W VL VR ω)) T ω
    have : (capTime (fun ω => min (hitOn G (chGap ρL ρL' ρR ρR') δ ζ W VL VR ω)
        (hitOn G Ψ ε ζ W VL VR ω)) T ω : WithTop ℝ≥0) ≤ T := by
      rw [h]; exact min_le_right _ _
    exact ENNReal.coe_le_coe.2 (WithTop.coe_le_coe.1 this)
  · exact zero_le

/-- The capped stop as a `WithTop` minimum. -/
theorem coe_cmpStop (hω : ω ∈ G) :
    ∃ r : ℝ≥0, cmpStop G ρL ρL' ρR ρR' Ψ δ ε T ζ W VL VR ω = r ∧
      (r : WithTop ℝ≥0) = min (min (hitBelow (fun s => chGap ρL ρL' ρR ρR' (Coupling.stateAt W VL VR s ω))
        (ζ ω) δ) (hitBelow (fun s => Ψ (Coupling.stateAt W VL VR s ω)) (ζ ω) ε)) T := by
  refine ⟨capTime (fun ω => min (hitOn G (chGap ρL ρL' ρR ρR') δ ζ W VL VR ω)
    (hitOn G Ψ ε ζ W VL VR ω)) T ω, by simp only [cmpStop, hω, ↓reduceIte], ?_⟩
  rw [coe_capTime]
  simp only [hitOn, hω, ↓reduceIte]

/-- Before the stop, on `G` and before `ζ`, the changed gaps are `≥ δ` and `Ψ ≥ ε`. -/
theorem le_of_lt_cmpStop (hω : ω ∈ G) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < cmpStop G ρL ρL' ρR ρR' Ψ δ ε T ζ W VL VR ω) (htζ : (t : ℝ≥0∞) < ζ ω) :
    δ ≤ chGap ρL ρL' ρR ρR' (Coupling.stateAt W VL VR t ω) ∧ ε ≤ Ψ (Coupling.stateAt W VL VR t ω) := by
  obtain ⟨r, hr, hrm⟩ := coe_cmpStop (ρL := ρL) (ρL' := ρL') (ρR := ρR) (ρR' := ρR') (Ψ := Ψ) (δ := δ) (ε := ε)
    (T := T) (ζ := ζ) (W := W) (VL := VL) (VR := VR) hω
  rw [hr] at ht
  have htr : (t : WithTop ℝ≥0) < r := WithTop.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 ht)
  rw [hrm] at htr
  constructor
  · by_contra hlt
    push Not at hlt
    have := hitBelow_le (f := fun s => chGap ρL ρL' ρR ρR' (Coupling.stateAt W VL VR s ω)) htζ hlt
    exact absurd htr (not_lt.2 ((min_le_left _ _).trans ((min_le_left _ _).trans this)))
  · by_contra hlt
    push Not at hlt
    have := hitBelow_le (f := fun s => Ψ (Coupling.stateAt W VL VR s ω)) htζ hlt
    exact absurd htr (not_lt.2 ((min_le_left _ _).trans ((min_le_right _ _).trans this)))

/-- **The stop is before the lifetime** when `Ψ` gets below `ε` before every finite lifetime. -/
theorem cmpStop_le_zeta (hGΨ : ∀ ω ∈ G, ζ ω ≠ ⊤ → ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω ∧
      Ψ (Coupling.stateAt W VL VR t ω) < ε) (ω : Ω) :
    cmpStop G ρL ρL' ρR ρR' Ψ δ ε T ζ W VL VR ω ≤ ζ ω := by
  by_cases hω : ω ∈ G
  · by_cases hζ : ζ ω = ⊤
    · rw [hζ]; exact le_top
    obtain ⟨t, htζ, htΨ⟩ := hGΨ ω hω hζ
    obtain ⟨r, hr, hrm⟩ := coe_cmpStop (ρL := ρL) (ρL' := ρL') (ρR := ρR) (ρR' := ρR') (Ψ := Ψ) (δ := δ)
      (ε := ε) (T := T) (ζ := ζ) (W := W) (VL := VL) (VR := VR) hω
    have h1 := hitBelow_le (f := fun s => Ψ (Coupling.stateAt W VL VR s ω)) htζ htΨ
    have hrt : (r : WithTop ℝ≥0) ≤ t := by
      rw [hrm]; exact (min_le_left _ _).trans ((min_le_right _ _).trans h1)
    rw [hr]
    exact (ENNReal.coe_le_coe.2 (WithTop.coe_le_coe.1 hrt)).trans htζ.le
  · simp [cmpStop, hω]

/-- **The comparison stop is a stopping time** of a right-continuous filtration in which the state is adapted,
for a good event `G ∈ 𝓖₀` on which the state is continuous before `ζ`. -/
theorem measurableSet_cmpStop_le {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous]
    (hW : AdaptedBefore 𝓖 ζ W) (hVL : ∀ i, AdaptedBefore 𝓖 ζ (VL i))
    (hVR : ∀ i, AdaptedBefore 𝓖 ζ (VR i)) (hG : MeasurableSet[𝓖 0] G)
    (hGc : ∀ ω ∈ G, ContinuousOn (fun s => Coupling.stateAt W VL VR s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω})
    (hΨ : Continuous Ψ) (s : ℝ≥0) :
    MeasurableSet[𝓖 s] {ω | cmpStop G ρL ρL' ρR ρR' Ψ δ ε T ζ W VL VR ω ≤ s} := by
  have h1 : IsStoppingTime 𝓖 (hitOn G (chGap ρL ρL' ρR ρR') δ ζ W VL VR) := by
    classical
    exact isStoppingTime_hitBelow_state hW hVL hVR hG hGc continuous_chGap δ
  have h2 : IsStoppingTime 𝓖 (hitOn G Ψ ε ζ W VL VR) := by
    classical
    exact isStoppingTime_hitBelow_state hW hVL hVR hG hGc hΨ ε
  have hcap := (isStoppingTime_capTime (h1.min h2) T).measurableSet_le s
  have hGs : MeasurableSet[𝓖 s] G := 𝓖.mono (zero_le (a := s)) _ hG
  have e : {ω | cmpStop G ρL ρL' ρR ρR' Ψ δ ε T ζ W VL VR ω ≤ s} =
      (G ∩ {ω | (capTime (fun ω => min (hitOn G (chGap ρL ρL' ρR ρR') δ ζ W VL VR ω)
        (hitOn G Ψ ε ζ W VL VR ω)) T ω : WithTop ℝ≥0) ≤ s}) ∪ Gᶜ := by
    ext ω
    by_cases hω : ω ∈ G
    · simp only [cmpStop, hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_inter_iff, true_and,
        mem_compl_iff, not_true_eq_false, or_false, ENNReal.coe_le_coe, WithTop.coe_le_coe]
    · simp [cmpStop, hω]
  rw [e]
  exact (hGs.inter hcap).union hGs.compl

end Stop


/-! ### The proposed code set -/

section CodeSet

variable {nL nR : ℕ}

/-- The proposed codes at level `ε`: lifetime `≤ T`, or lifetime `> T` and `Ψ < 2ε` at a rational time `q ≤ T` with
the changed gaps `≥ δ` at every rational time up to `q`. -/
def codeSet (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ) (Ψ : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ) (δ ε : ℝ)
    (T : ℝ≥0) : Set (XCode nL nR) :=
  {x | cζ x ≤ T ∨ ((T : ℝ≥0∞) < cζ x ∧ ∃ q : ℚ, (q : ℝ).toNNReal ≤ T ∧
    Ψ (Assembly.stateAt x (q : ℝ).toNNReal) < 2 * ε ∧
    ∀ r : ℚ, (r : ℝ).toNNReal ≤ (q : ℝ).toNNReal →
      δ ≤ chGap ρL ρL' ρR ρR' (Assembly.stateAt x (r : ℝ).toNNReal))}

variable {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ} {Ψ : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ}

theorem measurableSet_codeSet (hΨ : Continuous Ψ) (δ ε : ℝ) (T : ℝ≥0) :
    MeasurableSet (codeSet ρL ρL' ρR ρR' Ψ δ ε T) := by
  refine measurableSet_setOfPred.2 ((measurableSet_setOfPred.1 (measurableSet_le measurable_cζ measurable_const)).or
    ((measurableSet_setOfPred.1 (measurableSet_lt measurable_const measurable_cζ)).and
      (Measurable.exists fun q => measurable_const.and (Measurable.and ?_
        (Measurable.forall fun r => measurable_const_imp _ ?_)))))
  · exact measurableSet_setOfPred.1 (measurableSet_lt (hΨ.measurable.comp (measurable_stateAt _)) measurable_const)
  · exact measurableSet_setOfPred.1 (measurableSet_le measurable_const
      (continuous_chGap.measurable.comp (measurable_stateAt _)))

end CodeSet


/-! ### Rational times -/

/-- A rational time strictly before a positive time `r`, in any neighbourhood of `r`. -/
theorem exists_rat_lt_mem_nhds {r : ℝ≥0} (hr : 0 < r) {U : Set ℝ≥0} (hU : U ∈ 𝓝 r) :
    ∃ q : ℚ, (q : ℝ).toNNReal ∈ U ∧ (q : ℝ).toNNReal < r := by
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt (sub_lt_self (r : ℝ) hη) (NNReal.coe_pos.2 hr) :
    max ((r : ℝ) - η) 0 < r)
  have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (le_max_right _ _) hq1
  have hqc : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0.le
  refine ⟨q, hball ?_, ?_⟩
  · rw [Metric.mem_ball, NNReal.dist_eq, hqc, abs_sub_lt_iff]
    constructor
    · linarith
    · linarith [le_max_left ((r : ℝ) - η) 0]
  · rw [← NNReal.coe_lt_coe, hqc]; exact hq2

/-! ### The comparison at level `ε` -/

section Compare

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω} {Ψ : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ}

/-- **The reference event**: on `G`, the reference lifetime is `< T` and the changed gaps are `≥ δ` before it. -/
def refEvent (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ) (G : Set Ω) (δ : ℝ) (T : ℝ≥0) (ζ : Ω → ℝ≥0∞)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) : Set Ω :=
  {ω | ω ∈ G ∧ ζ ω < T ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → δ ≤ chGap ρL ρL' ρR ρR' (Coupling.stateAt W VL VR t ω)}

/-- The energy bound of the change of weights at level `δ` on `[0, T + 1]`. -/
def cmpEnergy (κ δ : ℝ) (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ) (T : ℝ≥0) : ℝ :=
  (|1 / Real.sqrt κ| * ((∑ j, |weightDiff ρL ρL' ρR ρR' j|) * δ⁻¹)) ^ 2 * ((T + 1 : ℝ≥0) : ℝ)

/-- On the reference event, the stop is the first time `Ψ < ε`, it is before `T` and `ζ`, `Ψ ≤ ε` there, and the
changed gaps are `≥ δ` before `ζ`. -/
theorem refEvent_stop (hGc : ∀ ω ∈ G, ContinuousOn (fun s => Coupling.stateAt W VL VR s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hΨ : Continuous Ψ) {δ : ℝ} {T : ℝ≥0} {ε : ℝ} {ω : Ω} (hω : ω ∈ refEvent ρL ρL' ρR ρR' G δ T ζ W VL VR)
    {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ ω) (hΨt₀ : Ψ (Coupling.stateAt W VL VR t₀ ω) < ε) :
    ∃ r : ℝ≥0, cmpStop G ρL ρL' ρR ρR' Ψ δ ε T ζ W VL VR ω = r ∧ (r : ℝ≥0∞) < ζ ω ∧ r < T ∧
      Ψ (Coupling.stateAt W VL VR r ω) ≤ ε := by
  obtain ⟨hωG, hζT, hgω⟩ := hω
  obtain ⟨r, hr, hrm⟩ := coe_cmpStop (ρL := ρL) (ρL' := ρL') (ρR := ρR) (ρR' := ρR') (Ψ := Ψ) (δ := δ)
    (ε := ε) (T := T) (ζ := ζ) (W := W) (VL := VL) (VR := VR) hωG
  have hC : hitBelow (fun s => chGap ρL ρL' ρR ρR' (Coupling.stateAt W VL VR s ω)) (ζ ω) δ = ⊤ :=
    hitBelow_of_not_nonempty fun ⟨s, hs, hsδ⟩ => absurd (hgω s hs) (not_le.2 hsδ)
  set A := {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω ∧ Ψ (Coupling.stateAt W VL VR s ω) < ε} with hA
  have hAne : A.Nonempty := ⟨t₀, ht₀, hΨt₀⟩
  have hΨh : hitBelow (fun s => Ψ (Coupling.stateAt W VL VR s ω)) (ζ ω) ε = ((sInf A : ℝ≥0) : WithTop ℝ≥0) :=
    hitBelow_of_nonempty hAne
  have hinf : sInf A ≤ t₀ := csInf_le (OrderBot.bddBelow _) ⟨ht₀, hΨt₀⟩
  have ht₀T : t₀ < T := by
    have : (t₀ : ℝ≥0∞) < T := ht₀.trans hζT
    exact_mod_cast this
  have hreq : r = sInf A := by
    rw [hC, hΨh, top_le_iff.mp le_top, min_eq_right le_top] at hrm
    rw [min_eq_left (WithTop.coe_le_coe.2 (hinf.trans ht₀T.le))] at hrm
    exact WithTop.coe_injective hrm
  have hrζ : (r : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by rw [hreq]; exact_mod_cast hinf) ht₀
  refine ⟨r, hr, hrζ, hreq ▸ lt_of_le_of_lt hinf ht₀T, ?_⟩
  -- `r = inf A` is in the closure of `A`, and `Ψ ∘ state` is continuous at `r`
  have hrcl : r ∈ closure A := hreq ▸ csInf_mem_closure hAne (OrderBot.bddBelow _)
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hcont : ContinuousAt (fun s => Ψ (Coupling.stateAt W VL VR s ω)) r :=
    hΨ.continuousAt.comp ((hGc ω hωG).continuousAt (hopen.mem_nhds hrζ))
  by_contra hgt
  push Not at hgt
  obtain ⟨s, hs1, hs2⟩ := mem_closure_iff_nhds.1 hrcl _ (hcont.eventually (lt_mem_nhds hgt))
  exact absurd hs2.2 (not_lt.2 hs1.le)

/-- **Aux. lemma 108 in driver form, through a common threshold, at level `ε`.** Let `(W, V)` be an integrated
evolution of a separated ordered word with weights `ρ` (the reference) in a right-continuous filtration, `G ∈ 𝓖₀` a
good event on which the state is continuous before `ζ` and a continuous functional `Ψ` of the state gets below
every positive level before every finite lifetime. For proposed weights `ρ'`, `δ > 0`, `T` and `ε > 0`:
`P(refEvent) ≤ (e^m)^{1/2} · codeLaw ρ' (codeSet … ε T) (x)^{1/2}`, with `m = cmpEnergy` independent of `ε`. -/
theorem measure_refEvent_le (hκ : 0 < κ) [IsProbabilityMeasure P] [𝓖.IsRightContinuous]
    (hF : IsOrderedForceWord xL xR) (hsep : ∀ i j, xL i < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓖 W VL VR B ζ) (hG : MeasurableSet[𝓖 0] G)
    (hGc : ∀ ω ∈ G, ContinuousOn (fun s => Coupling.stateAt W VL VR s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hΨ : Continuous Ψ)
    (hGΨ : ∀ ω ∈ G, ζ ω ≠ ⊤ → ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω ∧ Ψ (Coupling.stateAt W VL VR t ω) < ε)
    {δ : ℝ} (hδ : 0 < δ) (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    P (refEvent ρL ρL' ρR ρR' G δ T ζ W VL VR) ≤
      ENNReal.ofReal (Real.exp (cmpEnergy κ δ ρL ρL' ρR ρR' T)) ^ (1 / 2 : ℝ) *
        codeLaw κ ρL' ρR' (codeSet ρL ρL' ρR ρR' Ψ δ ε T) (xL, xR) ^ (1 / 2 : ℝ) := by
  have href : codeLaw κ ρL' ρR' (univ : Set (XCode nL nR)) (xL, xR) = 1 := by
    obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE'⟩ :=
      exists_isIntegratedSLEEvolution_assembled hκ hF (ρL := ρL') (ρR := ρR')
    rw [← measure_eventOf_eq_codeLaw hκ hsep hE' (Φ := fun _ _ => True) MeasurableSet.univ
      (fun _ _ _ => iff_of_true (mem_univ _) trivial) (fun _ _ _ _ h => h)]
    simp
  set τ := cmpStop G ρL ρL' ρR ρR' Ψ δ ε T ζ W VL VR with hτdef
  have hτm : ∀ s : ℝ≥0, MeasurableSet[𝓖 s] {ω | τ ω ≤ s} :=
    measurableSet_cmpStop_le hE.2.1 hE.2.2.1 hE.2.2.2.1 hG hGc hΨ
  have hτζ : ∀ ω, τ ω ≤ ζ ω := cmpStop_le_zeta (fun ω hω hζ => hGΨ ω hω hζ ε hε)
  have hτT : ∀ ω, τ ω ≤ T := cmpStop_le
  have hτG : ∀ ω, ω ∉ G → τ ω = 0 := fun ω hω => by simp [hτdef, cmpStop, hω]
  have hgap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω →
      (∀ i, ρL' i ≠ ρL i → δ ≤ |W t ω - VL i t ω|) ∧ ∀ i, ρR' i ≠ ρR i → δ ≤ |W t ω - VR i t ω| :=
    Eventually.of_forall fun ω t ht => by
      by_cases hω : ω ∈ G
      · obtain ⟨-, hL, hR⟩ := le_chGap_iff.1 (le_of_lt_cmpStop hω ht (ht.trans_le (hτζ ω))).1
        exact ⟨hL, hR⟩
      · rw [hτG ω hω] at ht
        exact absurd ht (not_lt.2 zero_le)
  have hEU := hE.isSLEEvolutionUpTo
  obtain ⟨hQeq, hEQ⟩ := hEU.girsanov_changeWeights hκ ρL' ρR' hτm hτζ hτT hδ hgap
  obtain ⟨hθp, hθb, hθreg⟩ := hEU.weightDrift_props ρL' ρR' hτm hτζ hδ
  set θ := weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR with hθdef
  set Q := girsanovMeasure P 𝓖 B θ (T + 1) with hQdef
  have hQp : IsProbabilityMeasure Q := hQeq.isProb
  have hpath : Measurable fun ω (s : ℝ≥0) => girsanovProcess B θ s ω :=
    measurable_pi_iff.2 fun s => (hEQ.brownian.2.1 s).mono (𝓖.le s) le_rfl
  have hmap : Q.map (fun ω (s : ℝ≥0) => girsanovProcess B θ s ω) = wienerPath :=
    map_path_eq_wienerPath hEQ.brownian.1.toIsPreBrownianReal hpath
  have hstart : Measurable fun ω => (((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)),
      fun s : ℝ≥0 => girsanovProcess B θ s ω) := measurable_const.prodMk hpath
  set S := codeSet ρL ρL' ρR ρR' Ψ δ ε T with hSdef
  have hS : MeasurableSet S := measurableSet_codeSet hΨ δ ε T
  set F := (fun ω => (((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)), fun s : ℝ≥0 => girsanovProcess B θ s ω)) ⁻¹'
    restartSetS κ ρL' ρR' S with hFdef
  have hFm : MeasurableSet F := hstart (measurableSet_restartSetS hS)
  have hdens := measure_inter_le_girsanov (isFilteredPreBrownian_of_isFilteredBrownianReal hE.1)
    hθp.stronglyAdapted hθb hθreg (T + 1) hFm MeasurableSet.univ (A := univ)
    (m := cmpEnergy κ δ ρL ρL' ρR ρR' T) fun ω _ => LP.LP4S.quadInt_le_of_bound hθb (T + 1) ω
  have hQF : Q F = codeLaw κ ρL' ρR' S (xL, xR) := by
    rw [hFdef, show (fun ω => (((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)),
        fun s : ℝ≥0 => girsanovProcess B θ s ω)) =
        Prod.mk ((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)) ∘ fun ω (s : ℝ≥0) => girsanovProcess B θ s ω from rfl,
      Set.preimage_comp, ← Measure.map_apply hpath
        ((measurableSet_restartSetS hS).preimage measurable_prodMk_left), hmap]
    rfl
  have hcan : ∀ᵐ ω ∂Q, (((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)), fun s : ℝ≥0 => girsanovProcess B θ s ω) ∈
      restartSetS κ ρL' ρR' (univ : Set (XCode nL nR)) := by
    have hS : MeasurableSet (Prod.mk ((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)) ⁻¹'
        restartSetS κ ρL' ρR' (univ : Set (XCode nL nR))) :=
      (measurableSet_restartSetS MeasurableSet.univ).preimage measurable_prodMk_left
    have hW1 : ∀ᵐ f ∂wienerPath, f ∈ Prod.mk ((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)) ⁻¹'
        restartSetS κ ρL' ρR' (univ : Set (XCode nL nR)) := by
      have h1 : wienerPath (Prod.mk ((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)) ⁻¹'
          restartSetS κ ρL' ρR' (univ : Set (XCode nL nR))) = 1 := href
      exact (ae_mem_iff_measure_eq hS.nullMeasurableSet).2 (by rw [h1, measure_univ])
    rw [← hmap] at hW1
    exact ae_of_ae_map hpath.aemeasurable hW1
  have hsub : refEvent ρL ρL' ρR ρR' G δ T ζ W VL VR ≤ᵐ[P] F := by
    filter_upwards [hQeq.ac'.ae_le hEQ.ae_path, hQeq.ac'.ae_le hEQ.brownian.1.cont,
      hQeq.ac'.ae_le hcan] with ω hpω hcω hxω hω
    obtain ⟨hωG, hζT, hgω⟩ := hω
    have hζne : ζ ω ≠ ⊤ := ne_top_of_lt hζT
    obtain ⟨t₀, ht₀, hΨt₀⟩ := hGΨ ω hωG hζne ε hε
    obtain ⟨r, hr, hrζ, hrT, hΨr⟩ := refEvent_stop hGc hΨ ⟨hωG, hζT, hgω⟩ ht₀ hΨt₀
    obtain ⟨x, ⟨⟨hxF, hxS⟩, -⟩, hxeq⟩ := hxω
    have hxs : startOf x = (xL, xR) := (Prod.ext_iff.1 hxeq).1
    have hx1 : x.1 = enc (fun s => girsanovProcess B θ s ω) := (Prod.ext_iff.1 hxeq).2
    have hxC : x ∈ CRel κ xL xR ρL' ρR' := mem_cRelF_iff.1 ⟨hxF, hxs⟩
    have hpx : IsIntegratedSLEPath κ xL xR ρL' ρR' (cw x) (cvL x) (cvR x) (cb x) (cζ x) := hxC.1.2.2
    have hcb : cb x = fun s => girsanovProcess B θ s ω := by
      show dec x.1 = _
      rw [hx1]
      exact Sec2.Assembly2.dec_enc_of_continuous hcω
    rw [hcb] at hpx
    have hup := hpx.isSLEPathUpTo (le_refl (cζ x))
    refine ⟨x, ⟨⟨hxF, hxS⟩, ?_⟩, hxeq⟩
    show x ∈ codeSet ρL ρL' ρR ρR' Ψ δ ε T
    by_cases hxT : cζ x ≤ T
    · exact Or.inl hxT
    push Not at hxT
    -- the stop is `r`, before `T < ζ(x)`: the two states agree before `r`
    have hτω : τ ω = r := hr
    have hagree : ∀ t : ℝ≥0, t < r → Assembly.stateAt x t = Coupling.stateAt W VL VR t ω := by
      intro t ht
      have hA := UpTo.agree_of_lt_min hsep hpω hpω.driverEq hup hup.driverEq (t := t)
        (lt_min (by rw [hτω]; exact_mod_cast ht)
          (lt_trans (by exact_mod_cast ht.trans hrT) hxT))
      obtain ⟨h1, h2, h3⟩ := hA
      simp only [Assembly.stateAt, Coupling.stateAt, h1, h2, h3]
    have hinit : Assembly.stateAt x 0 = Coupling.stateAt W VL VR 0 ω := by
      have e1 : cw x 0 = W 0 ω := by rw [hpx.1, hpω.1]
      have e2 : ∀ i, cvL x i 0 = VL i 0 ω := fun i => by rw [hpx.2.1 i, hpω.vL_zero i]
      have e3 : ∀ j, cvR x j 0 = VR j 0 ω := fun j => by rw [hpx.2.2.1 j, hpω.vR_zero j]
      simp only [Assembly.stateAt, Coupling.stateAt, e1, e2, e3]
    have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} := isOpen_lt ENNReal.continuous_coe continuous_const
    -- a rational time `q ≤ r` with `Ψ < 2ε`, agreeing states up to it
    obtain ⟨q, hqr, hqΨ, hqag⟩ : ∃ q : ℚ, (q : ℝ).toNNReal ≤ r ∧
        Ψ (Coupling.stateAt W VL VR (q : ℝ).toNNReal ω) < 2 * ε ∧
        ∀ s : ℝ≥0, s ≤ (q : ℝ).toNNReal → Assembly.stateAt x s = Coupling.stateAt W VL VR s ω ∧
          (s : ℝ≥0∞) < ζ ω := by
      rcases eq_or_ne r 0 with hr0 | hr0
      · refine ⟨0, by simp, ?_, fun s hs => ?_⟩
        · simp only [Rat.cast_zero, Real.toNNReal_zero]
          rw [← hr0]; linarith
        · have hs0 : s = 0 := le_antisymm (by simpa using hs) zero_le
          subst hs0
          exact ⟨hinit, lt_of_le_of_lt zero_le hrζ⟩
      · have hcont : ContinuousAt (fun s => Ψ (Coupling.stateAt W VL VR s ω)) r :=
          hΨ.continuousAt.comp ((hGc ω hωG).continuousAt (hopen.mem_nhds hrζ))
        obtain ⟨q, hqU, hqr⟩ := exists_rat_lt_mem_nhds (pos_iff_ne_zero.2 hr0)
          (hcont.eventually (gt_mem_nhds (show Ψ (Coupling.stateAt W VL VR r ω) < 2 * ε by linarith)))
        refine ⟨q, hqr.le, hqU, fun s hs => ⟨?_, ?_⟩⟩
        · rcases eq_or_ne s 0 with hs0 | hs0
          · rw [hs0]; exact hinit
          · exact hagree s (lt_of_le_of_lt hs hqr)
        · exact lt_of_le_of_lt (by exact_mod_cast hs.trans hqr.le) hrζ
    refine Or.inr ⟨hxT, q, hqr.trans hrT.le, ?_, fun r' hr' => ?_⟩
    · rw [(hqag _ le_rfl).1]; exact hqΨ
    · obtain ⟨he, hlt⟩ := hqag _ hr'
      rw [he]
      exact hgω _ hlt
  calc P (refEvent ρL ρL' ρR ρR' G δ T ζ W VL VR) ≤ P (F ∩ univ) := by
        rw [inter_univ]; exact measure_mono_ae hsub
    _ ≤ _ := hdens
    _ = _ := by rw [hQF]

end Compare


/-! ### Letting `ε → 0` -/

section Limit

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ}
  {Ψ : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ}

/-- The hypothesis on the proposed weights: on a path of `ρ'`, a time before the lifetime where `Ψ ≤ 0`, with the
changed gaps `≥ δ` up to it, is a continuation threshold of `ρ'`. -/
def ThresholdAtZero (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ)
    (Ψ : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ) (δ : ℝ) : Prop :=
  ∀ (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ) (ζ : ℝ≥0∞),
    IsIntegratedSLEPath κ xL xR ρL' ρR' w vL vR b ζ → ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      Ψ (w t, fun i => vL i t, fun j => vR j t) ≤ 0 →
      (∀ s ≤ t, δ ≤ chGap ρL ρL' ρR ρR' (w s, fun i => vL i s, fun j => vR j s)) →
      ForceWord.ThresholdCondition ρL' ρR' (w t) (fun i => vL i t) (fun j => vR j t)

theorem codeSet_anti {δ : ℝ} {T : ℝ≥0} {ε ε' : ℝ} (h : ε ≤ ε') :
    codeSet ρL ρL' ρR ρR' Ψ δ ε T ⊆ codeSet ρL ρL' ρR ρR' Ψ δ ε' T := by
  rintro x (hx | ⟨hxT, q, hqT, hqΨ, hqg⟩)
  · exact Or.inl hx
  · exact Or.inr ⟨hxT, q, hqT, by linarith, hqg⟩

theorem restartSetS_mono {S S' : Set (XCode nL nR)} (h : S ⊆ S') :
    restartSetS κ ρL' ρR' S ⊆ restartSetS κ ρL' ρR' S' := by
  rintro p ⟨x, ⟨hx1, hxS⟩, hxe⟩
  exact ⟨x, ⟨hx1, h hxS⟩, hxe⟩

/-- **A proposed path in every level-`ε` code set dies by `T`.** -/
theorem cζ_le_of_forall_mem_codeSet {δ : ℝ} {T : ℝ≥0} (hΨ : Continuous Ψ)
    (hthr : ThresholdAtZero κ xL xR ρL ρL' ρR ρR' Ψ δ) {x : XCode nL nR} (hxC : x ∈ CRel κ xL xR ρL' ρR')
    (hmem : ∀ n : ℕ, x ∈ codeSet ρL ρL' ρR ρR' Ψ δ (1 / ((n : ℝ) + 1)) T) : cζ x ≤ T := by
  have hpx : IsIntegratedSLEPath κ xL xR ρL' ρR' (cw x) (cvL x) (cvR x) (cb x) (cζ x) := hxC.1.2.2
  by_contra hlt
  push Not at hlt
  have hq : ∀ n : ℕ, ∃ q : ℚ, (q : ℝ).toNNReal ≤ T ∧
      Ψ (Assembly.stateAt x (q : ℝ).toNNReal) < 2 * (1 / ((n : ℝ) + 1)) ∧
      ∀ r : ℚ, (r : ℝ).toNNReal ≤ (q : ℝ).toNNReal →
        δ ≤ chGap ρL ρL' ρR ρR' (Assembly.stateAt x (r : ℝ).toNNReal) :=
    fun n => ((hmem n).resolve_left (not_le.2 hlt)).2
  choose q hqT hqΨ hqg using hq
  set u : ℕ → ℝ≥0 := fun n => ((q n : ℚ) : ℝ).toNNReal with hu
  obtain ⟨-, -, -, hcw, hcvL, hcvR, -, -, -, -, -, -, -, -, -, -, -, hnot, -, -⟩ := hpx
  have hcon : ContinuousOn (Assembly.stateAt x) {t : ℝ≥0 | (t : ℝ≥0∞) < cζ x} :=
    hcw.prodMk ((continuousOn_pi.2 hcvL).prodMk (continuousOn_pi.2 hcvR))
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < cζ x} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hIcc : Icc 0 T ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < cζ x} := fun t ht =>
    lt_of_le_of_lt (by exact_mod_cast ht.2) hlt
  have hcat : ∀ t : ℝ≥0, t ≤ T → ContinuousAt (Assembly.stateAt x) t := fun t ht =>
    hcon.continuousAt (hopen.mem_nhds (hIcc ⟨zero_le, ht⟩))
  set D := Icc 0 T ∩ (fun t => chGap ρL ρL' ρR ρR' (Assembly.stateAt x t)) ⁻¹' Ici δ with hD
  have hDcl : IsClosed D :=
    (continuous_chGap.comp_continuousOn (hcon.mono hIcc)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hIccD : ∀ n, Icc 0 (u n) ⊆ D := by
    intro n t ht
    refine ⟨⟨zero_le, ht.2.trans (hqT n)⟩, ?_⟩
    show δ ≤ chGap ρL ρL' ρR ρR' (Assembly.stateAt x t)
    rcases eq_or_ne t 0 with ht0 | ht0
    · have := hqg n 0 (by simp)
      simpa [ht0] using this
    · by_contra hlt'
      push Not at hlt'
      have hct : ContinuousAt (fun s => chGap ρL ρL' ρR ρR' (Assembly.stateAt x s)) t :=
        continuous_chGap.continuousAt.comp (hcat t (ht.2.trans (hqT n)))
      obtain ⟨r, hrU, hrt⟩ := exists_rat_lt_mem_nhds (pos_iff_ne_zero.2 ht0) (hct.eventually (gt_mem_nhds hlt'))
      exact absurd (hqg n r (hrt.le.trans ht.2)) (not_le.2 hrU)
  obtain ⟨a, haI, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq (x := u) fun n => ⟨zero_le, hqT n⟩
  have haζ : (a : ℝ≥0∞) < cζ x := hIcc haI
  have hcontA := hcat a haI.2
  have hΨa : Ψ (Assembly.stateAt x a) ≤ 0 := by
    have h1 : Tendsto (fun n => Ψ (Assembly.stateAt x (u (φ n)))) atTop (𝓝 (Ψ (Assembly.stateAt x a))) :=
      hΨ.continuousAt.tendsto.comp (hcontA.tendsto.comp hlim)
    have h2 : Tendsto (fun n => 2 * (1 / ((φ n : ℝ) + 1))) atTop (𝓝 (2 * 0)) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop).const_mul 2
    rw [mul_zero] at h2
    exact le_of_tendsto_of_tendsto' h1 h2 fun n => (hqΨ (φ n)).le
  have haD : a ∈ D := hDcl.mem_of_tendsto hlim (Eventually.of_forall fun n => hIccD (φ n) ⟨zero_le, le_rfl⟩)
  have hgap : ∀ s ≤ a, δ ≤ chGap ρL ρL' ρR ρR' (Assembly.stateAt x s) := by
    intro s hs
    rcases hs.lt_or_eq with hs | rfl
    · obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds hs)).exists
      exact (hIccD (φ n) ⟨zero_le, hn.le⟩).2
    · exact haD.2
  exact hnot a haζ (hthr _ _ _ _ _ hxC.1.2.2 a haζ hΨa hgap)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω}

/-- **The transfer of a common threshold** (Aux. lemma 108 through a common threshold): under the hypotheses of
`measure_refEvent_le`, if `Ψ = 0` with the changed gaps `≥ δ` is a threshold of the proposed weights and the
reference event has positive probability, the canonical lifetime of the proposed weights is `≤ T` with positive
probability. -/
theorem codeLaw_lifetime_le_ne_zero (hκ : 0 < κ) [IsProbabilityMeasure P] [𝓖.IsRightContinuous]
    (hF : IsOrderedForceWord xL xR) (hsep : ∀ i j, xL i < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓖 W VL VR B ζ) (hG : MeasurableSet[𝓖 0] G)
    (hGc : ∀ ω ∈ G, ContinuousOn (fun s => Coupling.stateAt W VL VR s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hΨ : Continuous Ψ)
    (hGΨ : ∀ ω ∈ G, ζ ω ≠ ⊤ → ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω ∧ Ψ (Coupling.stateAt W VL VR t ω) < ε)
    {δ : ℝ} (hδ : 0 < δ) (T : ℝ≥0) (hthr : ThresholdAtZero κ xL xR ρL ρL' ρR ρR' Ψ δ)
    (hpos : P (refEvent ρL ρL' ρR ρR' G δ T ζ W VL VR) ≠ 0) :
    codeLaw κ ρL' ρR' {x | cζ x ≤ T} (xL, xR) ≠ 0 := by
  set A : ℕ → Set (ℝ≥0 → ℝ) := fun n => Prod.mk ((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)) ⁻¹'
    restartSetS κ ρL' ρR' (codeSet ρL ρL' ρR ρR' Ψ δ (1 / ((n : ℝ) + 1)) T) with hA
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    (measurableSet_restartSetS (measurableSet_codeSet hΨ δ _ T)).preimage measurable_prodMk_left
  have hanti : Antitone A := by
    intro n m hnm
    refine preimage_mono (restartSetS_mono (codeSet_anti ?_))
    have : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hnm
    exact one_div_le_one_div_of_le (by positivity) this
  have hsub : (⋂ n, A n) ⊆ Prod.mk ((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)) ⁻¹'
      restartSetS κ ρL' ρR' {x | cζ x ≤ T} := by
    intro f hf
    have hf0 := mem_iInter.1 hf 0
    obtain ⟨x, ⟨⟨hxF, hxS⟩, -⟩, hxe⟩ := hf0
    have hxs : startOf x = (xL, xR) := (Prod.ext_iff.1 hxe).1
    have hxC : x ∈ CRel κ xL xR ρL' ρR' := mem_cRelF_iff.1 ⟨hxF, hxs⟩
    have hx1 : x.1 = enc f := (Prod.ext_iff.1 hxe).2
    have hmem : ∀ n : ℕ, x ∈ codeSet ρL ρL' ρR ρR' Ψ δ (1 / ((n : ℝ) + 1)) T := fun n => by
      have h := mem_iInter.1 hf n
      have h' : ((xL, xR), x.1) ∈ lawSetS κ ρL' ρR' (codeSet ρL ρL' ρR ρR' Ψ δ (1 / ((n : ℝ) + 1)) T) := by
        rw [hx1]; exact h
      exact (mem_lawSetS_iff hsep hxC).1 h'
    exact ⟨x, ⟨⟨hxF, hxS⟩, cζ_le_of_forall_mem_codeSet hΨ hthr hxC hmem⟩, hxe⟩
  have hlim : Tendsto (fun n => wienerPath (A n)) atTop (𝓝 (wienerPath (⋂ n, A n))) :=
    tendsto_measure_iInter_atTop (fun n => (hAm n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  intro h0
  have hI0 : wienerPath (⋂ n, A n) = 0 := le_antisymm ((measure_mono hsub).trans h0.le) zero_le
  rw [hI0] at hlim
  set E : ℝ≥0∞ := ENNReal.ofReal (Real.exp (cmpEnergy κ δ ρL ρL' ρR ρR' T)) ^ (1 / 2 : ℝ) with hEdef
  have hEtop : E ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hlim2 : Tendsto (fun n => E * wienerPath (A n) ^ (1 / 2 : ℝ)) atTop (𝓝 (E * 0 ^ (1 / 2 : ℝ))) :=
    ENNReal.Tendsto.const_mul ((ENNReal.continuous_rpow_const.tendsto _).comp hlim) (Or.inr hEtop)
  rw [ENNReal.zero_rpow_of_pos (by norm_num), mul_zero] at hlim2
  have hle : ∀ n, P (refEvent ρL ρL' ρR ρR' G δ T ζ W VL VR) ≤ E * wienerPath (A n) ^ (1 / 2 : ℝ) := fun n =>
    measure_refEvent_le hκ hF hsep hE hG hGc hΨ hGΨ hδ T (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  exact hpos (le_antisymm (ge_of_tendsto' hlim2 hle) zero_le)

/-- **The transfer to every evolution of the proposed weights**: under the hypotheses of
`codeLaw_lifetime_le_ne_zero`, every integrated evolution of the proposed weights from the same separated start has
lifetime `≤ T` with positive probability. -/
theorem measure_lifetime_le_ne_zero (hκ : 0 < κ) [IsProbabilityMeasure P] [𝓖.IsRightContinuous]
    (hF : IsOrderedForceWord xL xR) (hsep : ∀ i j, xL i < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓖 W VL VR B ζ) (hG : MeasurableSet[𝓖 0] G)
    (hGc : ∀ ω ∈ G, ContinuousOn (fun s => Coupling.stateAt W VL VR s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hΨ : Continuous Ψ)
    (hGΨ : ∀ ω ∈ G, ζ ω ≠ ⊤ → ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω ∧ Ψ (Coupling.stateAt W VL VR t ω) < ε)
    {δ : ℝ} (hδ : 0 < δ) (T : ℝ≥0) (hthr : ThresholdAtZero κ xL xR ρL ρL' ρR ρR' Ψ δ)
    (hpos : P (refEvent ρL ρL' ρR ρR' G δ T ζ W VL VR) ≠ 0)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P'] {𝓕' : Filtration ℝ≥0 mΩ'}
    {W' : ℝ≥0 → Ω' → ℝ} {VL' : Fin nL → ℝ≥0 → Ω' → ℝ} {VR' : Fin nR → ℝ≥0 → Ω' → ℝ} {B' : ℝ≥0 → Ω' → ℝ}
    {ζ' : Ω' → ℝ≥0∞} (hE' : IsIntegratedSLEEvolution κ xL xR ρL' ρR' P' 𝓕' W' VL' VR' B' ζ') :
    P' {ω | ζ' ω ≤ T} ≠ 0 := by
  have h := measure_eventOf_eq_codeLaw hκ hsep hE' (S := {x | cζ x ≤ T}) (Φ := fun _ τ => τ ≤ T)
    (measurableSet_le measurable_cζ measurable_const) (fun _ _ _ => Iff.rfl) (fun _ _ _ _ h => h)
  rw [h]
  exact codeLaw_lifetime_le_ne_zero hκ hF hsep hE hG hGc hΨ hGΨ hδ T hthr hpos

end Limit

end GW0BadGroup

end Theorem14

end InteractingSLE
