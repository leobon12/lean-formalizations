/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TwoSeedLawPath
import InteractingSLE.Frozen.Spec.IsOrderedForceWord

/-!
# Theorem 2.2 for two seeds at `0⁻, 0⁺`: uniqueness in law

Packet PROVE-SEC2-JAC2. Specification, Theorem 2.2 and its proof (`source/spec/p001-048.md`, L481,
L512–L546), for the force word with one mark on each side, both at the origin.

* `measure_killedState_eq_twoSeed`: the frozen statement `IsIntegratedSLEEvolution.measure_killedState_eq`
  with `nL = nR = 1` and `x_{1,L} = x_{1,R} = 0`, for every `a > 0` and all weights. For weights `> −2` the
  angle process of each evolution is a solution of the Jacobi martingale problem
  (`exists_isJacobiMP_logAngle`), so the two angle paths have the same law on `CPathR`
  (`map_toCPathR_eq`), and the killed-state event is, up to a null set, the preimage of one measurable set of
  paths (`killedSet`) under the angle path (`lifetime_eq_iSup_clock`, `state_eq_phys`). If a weight is at
  most `−2`, the seed satisfies the continuation threshold (`thresholdCondition_seed_iff`), so both
  lifetimes vanish almost surely.
* `exists_isIntegratedSLEEvolution_twoSeed_of_le`: existence for the same shape when a weight is at most
  `−2` (lifetime `0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Real
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Sec2

namespace TwoSeed

/-- The threshold condition at the two-seed state `(0; 0⁻, 0⁺)`. -/
theorem thresholdCondition_seed_iff (ρL ρR : Fin 1 → ℝ) :
    ForceWord.ThresholdCondition ρL ρR 0 (fun _ => 0) (fun _ => 0) ↔ ρL 0 ≤ -2 ∨ ρR 0 ≤ -2 := by
  simp [ForceWord.ThresholdCondition]

/-- If a weight is at most `−2`, a two-seed path has lifetime `0`. -/
theorem lifetime_eq_zero_of_le {κ : ℝ} {ρL ρR : Fin 1 → ℝ} {w : ℝ≥0 → ℝ}
    {vL vR : Fin 1 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (h : IsIntegratedSLEPath κ (fun _ => 0) (fun _ => 0) ρL ρR w vL vR b ζ)
    (hdeg : ρL 0 ≤ -2 ∨ ρR 0 ≤ -2) : ζ = 0 := by
  by_contra hζ
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ := by simpa [pos_iff_ne_zero] using hζ
  have hl : (fun i => vL i 0) = fun _ => (0 : ℝ) := funext fun i => by
    fin_cases i; exact path_vL_zero h
  have hr : (fun i => vR i 0) = fun _ => (0 : ℝ) := funext fun i => by
    fin_cases i; exact path_vR_zero h
  obtain ⟨hw0, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnt, -⟩ := h
  apply hnt 0 h0
  rw [hw0, hl, hr]
  exact (thresholdCondition_seed_iff ρL ρR).2 hdeg

section Law

variable {κ : ℝ} {ρL ρR : Fin 1 → ℝ}

/-- **The killed-state probability is a path-law probability of the angle.** For an evolution with weights
`> −2`, the killed-state event of the frozen statement has the probability of `killedSet` under the law on
`CPathR` of the (modified) angle process. -/
theorem measure_killedState_eq_map {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ)
    (hκ : 0 < κ) (hρL : -2 < ρL 0) (hρR : -2 < ρR 0) {G : Set Ω} (hGm : MeasurableSet G)
    (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGoodTwoSeed κ ρL ρR W VL VR B ζ ω)
    (n : ℕ) (ts : Fin n → ℝ≥0) (A : Fin n → Set (ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ))
    (hA : ∀ j, MeasurableSet (A j)) :
    P {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
        (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω), B (ts j) ω) ∈ A j} =
      (P.map (toCPathR (angleG G W VL VR ζ)
        (isJacobiMP_angleG hE hρL hρR hGm hGc hgood hκ).continuous)) (killedSet κ ρL ρR ts A) := by
  have hU := isJacobiMP_angleG hE hρL hρR hGm hGc hgood hκ
  rw [Measure.map_apply (measurable_toCPathR hU.measurable hU.continuous)
    (measurableSet_killedSet κ ρL ρR ts hA)]
  refine measure_congr ?_
  filter_upwards [show ∀ᵐ ω ∂P, ω ∈ G from by rw [ae_iff]; exact hGc] with ω hω
  obtain ⟨hP, hBc, hB0⟩ := hgood ω hω
  set f := toCPathR (angleG G W VL VR ζ) hU.continuous ω
  have hfU : f.1 = logAngle (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (ζ ω) := by
    funext u; simp only [f, toCPathR, angleG, hω, ↓reduceIte]
  have hclamp : clampU f = logAngle (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (ζ ω) := by
    rw [clampU_eq fun v => hU.mem_Icc v ω, hfU]
  have hZ : totalClock f = ζ ω := by
    rw [totalClock, hclamp]
    exact (lifetime_eq_iSup_clock hP hBc hρL hρR).symm
  have hstate : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
      stateF κ ρL ρR f t = (W t ω, (fun i => VL i t ω), (fun i => VR i t ω), B t ω) := by
    intro t ht
    rw [stateF, hclamp]
    exact (state_eq_phys hP hBc hρL hρR hκ hB0 ht).symm
  change (∀ j, _) = (∀ j, (ts j : ℝ≥0∞) < totalClock f ∧ stateF κ ρL ρR f (ts j) ∈ A j)
  rw [hZ]
  refine propext (forall_congr' fun j => and_congr_right fun ht => ?_)
  rw [hstate (ts j) ht]

/-- **Uniqueness in law for weights `> −2`.** -/
theorem measure_killedState_eq_twoSeed_of_gt (hκ : 0 < κ) (hρL : -2 < ρL 0) (hρR : -2 < ρR 0)
    {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin 1 → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin 1 → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    (h₁ : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ}
    {VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (h₂ : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (n : ℕ) (ts : Fin n → ℝ≥0) (A : Fin n → Set (ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ))
    (hA : ∀ j, MeasurableSet (A j)) :
    P₁ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₁ ω ∧
        (W₁ (ts j) ω, (fun i => VL₁ i (ts j) ω), (fun i => VR₁ i (ts j) ω), B₁ (ts j) ω) ∈ A j} =
      P₂ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₂ ω ∧
        (W₂ (ts j) ω, (fun i => VL₂ i (ts j) ω), (fun i => VR₂ i (ts j) ω), B₂ (ts j) ω) ∈ A j} := by
  obtain ⟨G₁, hG₁m, hG₁c, hgood₁⟩ := exists_good h₁
  obtain ⟨G₂, hG₂m, hG₂c, hgood₂⟩ := exists_good h₂
  rw [measure_killedState_eq_map h₁ hκ hρL hρR hG₁m hG₁c hgood₁ n ts A hA,
    measure_killedState_eq_map h₂ hκ hρL hρR hG₂m hG₂c hgood₂ n ts A hA,
    map_toCPathR_eq (isJacobiMP_angleG h₁ hρL hρR hG₁m hG₁c hgood₁ hκ)
      (isJacobiMP_angleG h₂ hρL hρR hG₂m hG₂c hgood₂ hκ) hκ.le (by linarith)]

/-- If a weight is at most `−2`, a killed-state event at `n ≥ 1` times is null. -/
theorem measure_killedState_eq_zero_of_le (hdeg : ρL 0 ≤ -2 ∨ ρR 0 ≤ -2) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ) {n : ℕ}
    (hn : 0 < n) (ts : Fin n → ℝ≥0) (A : Fin n → Set (ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ)) :
    P {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
      (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω), B (ts j) ω) ∈ A j} = 0 := by
  refine measure_mono_null (fun ω hω => (hω ⟨0, hn⟩).1) (measure_eq_zero_iff_ae_notMem.2 ?_)
  filter_upwards [hE.2.2.2.2] with ω hω hlt
  have h0 : ζ ω = 0 := lifetime_eq_zero_of_le hω hdeg
  have : ((ts ⟨0, hn⟩ : ℝ≥0) : ℝ≥0∞) < ζ ω := hlt
  rw [h0] at this
  exact absurd this (not_lt.2 bot_le)

/-- **Uniqueness in law when a weight is at most `−2`**: both lifetimes vanish. -/
theorem measure_killedState_eq_twoSeed_of_le (hdeg : ρL 0 ≤ -2 ∨ ρR 0 ≤ -2)
    {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin 1 → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin 1 → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    (h₁ : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ}
    {VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (h₂ : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (n : ℕ) (ts : Fin n → ℝ≥0) (A : Fin n → Set (ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ)) :
    P₁ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₁ ω ∧
        (W₁ (ts j) ω, (fun i => VL₁ i (ts j) ω), (fun i => VR₁ i (ts j) ω), B₁ (ts j) ω) ∈ A j} =
      P₂ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₂ ω ∧
        (W₂ (ts j) ω, (fun i => VL₂ i (ts j) ω), (fun i => VR₂ i (ts j) ω), B₂ (ts j) ω) ∈ A j} := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have e₁ : {ω : Ω₁ | ∀ j : Fin 0, (ts j : ℝ≥0∞) < ζ₁ ω ∧
        (W₁ (ts j) ω, (fun i => VL₁ i (ts j) ω), (fun i => VR₁ i (ts j) ω), B₁ (ts j) ω) ∈ A j} =
        univ := eq_univ_of_forall fun ω j => j.elim0
    have e₂ : {ω : Ω₂ | ∀ j : Fin 0, (ts j : ℝ≥0∞) < ζ₂ ω ∧
        (W₂ (ts j) ω, (fun i => VL₂ i (ts j) ω), (fun i => VR₂ i (ts j) ω), B₂ (ts j) ω) ∈ A j} =
        univ := eq_univ_of_forall fun ω j => j.elim0
    rw [e₁, e₂, measure_univ, measure_univ]
  · rw [measure_killedState_eq_zero_of_le hdeg h₁ hn ts A,
      measure_killedState_eq_zero_of_le hdeg h₂ hn ts A]

end Law

/-- **Theorem 2.2, uniqueness in law, two seeds** (`IsIntegratedSLEEvolution.measure_killedState_eq` with
`nL = nR = 1` and both marks at the origin, `0⁻` and `0⁺`; every `a > 0`, all weights). -/
theorem measure_killedState_eq_twoSeed {a : ℝ} (ha : 0 < a) {xL xR : Fin 1 → ℝ}
    {ρL ρR : Fin 1 → ℝ} (hxL : ∀ i, xL i = 0) (hxR : ∀ i, xR i = 0)
    {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin 1 → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin 1 → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    (h₁ : IsIntegratedSLEEvolution a xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ}
    {VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (h₂ : IsIntegratedSLEEvolution a xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (n : ℕ) (ts : Fin n → ℝ≥0) (A : Fin n → Set (ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ))
    (hA : ∀ j, MeasurableSet (A j)) :
    P₁ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₁ ω ∧
        (W₁ (ts j) ω, (fun i => VL₁ i (ts j) ω), (fun i => VR₁ i (ts j) ω), B₁ (ts j) ω) ∈ A j} =
      P₂ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₂ ω ∧
        (W₂ (ts j) ω, (fun i => VL₂ i (ts j) ω), (fun i => VR₂ i (ts j) ω), B₂ (ts j) ω) ∈ A j} := by
  obtain rfl : xL = fun _ => 0 := funext hxL
  obtain rfl : xR = fun _ => 0 := funext hxR
  by_cases hρ : -2 < ρL 0 ∧ -2 < ρR 0
  · exact measure_killedState_eq_twoSeed_of_gt ha hρ.1 hρ.2 h₁ h₂ n ts A hA
  · have hdeg : ρL 0 ≤ -2 ∨ ρR 0 ≤ -2 := by
      rcases le_or_gt (ρL 0) (-2) with h | h
      · exact Or.inl h
      rcases le_or_gt (ρR 0) (-2) with h' | h'
      · exact Or.inr h'
      exact absurd ⟨h, h'⟩ hρ
    exact measure_killedState_eq_twoSeed_of_le hdeg h₁ h₂ n ts A

/-- The constant path with lifetime `0` is an integrated path when the seed is at the threshold. -/
theorem isIntegratedSLEPath_lifetime_zero {a : ℝ} {xL xR : Fin 1 → ℝ} {ρL ρR : Fin 1 → ℝ}
    (hxL : ∀ i, xL i = 0) (hxR : ∀ i, xR i = 0) (hdeg : ρL 0 ≤ -2 ∨ ρR 0 ≤ -2) (b : ℝ≥0 → ℝ) :
    IsIntegratedSLEPath a xL xR ρL ρR (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) b 0 := by
  have hno : ∀ t : ℝ≥0, ¬ ((t : ℝ≥0∞) < 0) := fun t => not_lt.2 bot_le
  refine ⟨rfl, fun i => (hxL i).symm, fun i => (hxR i).symm, continuousOn_const,
    fun _ => continuousOn_const, fun _ => continuousOn_const, fun t ht => absurd ht (hno t),
    fun t ht => absurd ht (hno t), fun t ht => absurd ht (hno t), fun t ht => absurd ht (hno t),
    fun t ht => absurd ht (hno t), fun t ht => absurd ht (hno t), fun t ht => absurd ht (hno t),
    fun t ht => absurd ht (hno t), fun t ht => absurd ht (hno t), fun i => ?_, fun i => ?_,
    fun t ht => absurd ht (hno t), fun _ => ?_, fun T hT hTe => ?_⟩
  · have : {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < 0 ∧ (0 : ℝ) = 0} = ∅ :=
      eq_empty_of_forall_notMem fun s hs => hno _ hs.2.1
    rw [this, measure_empty]
  · have : {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < 0 ∧ (0 : ℝ) = 0} = ∅ :=
      eq_empty_of_forall_notMem fun s hs => hno _ hs.2.1
    rw [this, measure_empty]
  · rw [show xL = fun _ => 0 from funext hxL, show xR = fun _ => 0 from funext hxR]
    exact (thresholdCondition_seed_iff ρL ρR).2 hdeg
  · exact absurd hTe (ENNReal.coe_ne_zero.2 hT.ne')

/-- **Theorem 2.2, existence, two seeds, a weight at most `−2`**: the evolution with lifetime `0`. -/
theorem exists_isIntegratedSLEEvolution_twoSeed_of_le {a : ℝ} {xL xR : Fin 1 → ℝ}
    (hxL : ∀ i, xL i = 0) (hxR : ∀ i, xR i = 0) (ρL ρR : Fin 1 → ℝ)
    (hdeg : ρL 0 ≤ -2 ∨ ρR 0 ≤ -2) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, B, hB, -, -⟩ := OneForce.exists_filteredBrownian
  have hadp : ∀ X : ℝ≥0 → Ω → ℝ, AdaptedBefore 𝓕 (fun _ => 0) X := fun X t A _ => by
    have : {ω : Ω | (t : ℝ≥0∞) < (fun _ => (0 : ℝ≥0∞)) ω ∧ X t ω ∈ A} = ∅ :=
      eq_empty_of_forall_notMem fun ω hω => (not_lt.2 bot_le) hω.1
    rw [this]
    exact @MeasurableSet.empty Ω (𝓕 t)
  exact ⟨Ω, mΩ, P, hP, 𝓕, fun _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0, B, fun _ => 0, hB,
    hadp _, fun _ => hadp _, fun _ => hadp _,
    ae_of_all _ fun ω => isIntegratedSLEPath_lifetime_zero hxL hxR hdeg (B · ω)⟩

end TwoSeed

end Sec2

end InteractingSLE
