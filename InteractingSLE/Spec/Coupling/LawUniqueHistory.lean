/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution
import InteractingSLE.Frozen.Spec.IsMeasurableKilledDriving
import InteractingSLE.Frozen.Spec.IsOrderedForceWord
import InteractingSLE.Spec.Sec2.OneForceLaw
import InteractingSLE.Spec.Sec2.OneForceNone
import InteractingSLE.Spec.Sec2.TwoSeedLaw

/-!
# The law of the killed driving history (ruling R33, the driving marginal)

Packet PROVE-OHC-UNIQ. Ruling R33 compares two couplings satisfying the frozen
`IsOptionalHullCoupling` through the joint law of the field and the *killed driving history*. This
file fixes that history as a random element of a standard Borel space and proves that its law is
the same in any two integrated `SLE_a(ρ)` evolutions of one force word, from Theorem 2.2's
uniqueness in law (Specification p. 21).

* `killedHistory W VL VR ζ : Ω → ℝ≥0∞ × (ℕ × ℕ → ℝ × ℝ^{nL} × ℝ^{nR})`: the lifetime `ζ` and the
  state `(W, V^L, V^R)` at the dyadic times `k / 2^n` before `ζ` (the value `0` from `ζ` on). The
  space is standard Borel (`HistorySpace`). By continuity of the state before `ζ` the dyadic
  values recover the whole killed path (used in `LawUniqueTransfer.lean`).
* `measurable_killedHistory`: measurable whenever the killed driving is (`IsMeasurableKilledDriving`,
  part of the frozen coupling predicate).
* `measure_eq_of_historyCylinders`: a law of a history that is invariant under the normalization
  `historyNormalize` (state reset to `0` from the lifetime on) is determined by its values on the
  cylinder events `{t_j < ζ, X_{t_j} ∈ A_j for all j}` at dyadic times — exactly the events of the
  frozen `IsIntegratedSLEEvolution.measure_killedState_eq`.
* `KilledStateLawUnique a xL xR ρL ρR`: the statement of the frozen Theorem 2.2 uniqueness in law
  for one force word (the frozen anchor is a `DRAFT_SORRY` and is not imported). It is proved here
  for the force words whose uniqueness has landed: no force point (`killedStateLawUnique_none`),
  one force point (`killedStateLawUnique_left`, `killedStateLawUnique_right`) and the two seeds at
  `0⁻, 0⁺` (`killedStateLawUnique_twoSeed`).
* `map_killedHistory_eq`: under `KilledStateLawUnique`, two evolutions with measurable killed driving
  have the same law of `killedHistory`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u v

namespace InteractingSLE

namespace LawUnique

/-! ### Dyadic times -/

/-- The dyadic time `k / 2^n` of the index `(n, k)`. -/
def dyadicTime (p : ℕ × ℕ) : ℝ≥0 := (p.2 : ℝ≥0) / 2 ^ p.1

/-- The dyadic time just above `r` at level `n`: `(⌊2^n r⌋ + 1) / 2^n`. -/
def upperDyadic (r : ℝ≥0) (n : ℕ) : ℕ × ℕ := (n, ⌊(2 : ℝ≥0) ^ n * r⌋₊ + 1)

/-- The dyadic time at or below `t` at level `n`: `⌊2^n t⌋ / 2^n`. -/
def lowerDyadic (t : ℝ≥0) (n : ℕ) : ℕ × ℕ := (n, ⌊(2 : ℝ≥0) ^ n * t⌋₊)

theorem lt_dyadicTime_upperDyadic (r : ℝ≥0) (n : ℕ) : r < dyadicTime (upperDyadic r n) := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  rw [dyadicTime, upperDyadic, lt_div_iff₀ h2, mul_comm]
  exact_mod_cast Nat.lt_floor_add_one ((2 : ℝ≥0) ^ n * r)

theorem dyadicTime_upperDyadic_le (r : ℝ≥0) (n : ℕ) :
    dyadicTime (upperDyadic r n) ≤ r + 1 / 2 ^ n := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  rw [dyadicTime, upperDyadic, div_le_iff₀ h2, add_mul, one_div, inv_mul_cancel₀ h2.ne', mul_comm]
  push_cast
  gcongr
  exact Nat.floor_le zero_le

theorem dyadicTime_lowerDyadic_le (t : ℝ≥0) (n : ℕ) : dyadicTime (lowerDyadic t n) ≤ t := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  rw [dyadicTime, lowerDyadic, div_le_iff₀ h2, mul_comm]
  exact Nat.floor_le zero_le

theorem le_dyadicTime_lowerDyadic_add (t : ℝ≥0) (n : ℕ) :
    t ≤ dyadicTime (lowerDyadic t n) + 1 / 2 ^ n := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  rw [dyadicTime, lowerDyadic, ← add_div, le_div_iff₀ h2, mul_comm]
  exact (Nat.lt_floor_add_one ((2 : ℝ≥0) ^ n * t)).le

theorem tendsto_one_div_two_pow : Tendsto (fun n : ℕ => (1 : ℝ≥0) / 2 ^ n) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ((1 : ℝ≥0) / 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one zero_le (by norm_num)
  simpa only [div_pow, one_pow] using h

theorem tendsto_dyadicTime_upperDyadic (r : ℝ≥0) :
    Tendsto (fun n => dyadicTime (upperDyadic r n)) atTop (𝓝 r) := by
  have hup : Tendsto (fun n : ℕ => r + 1 / 2 ^ n) atTop (𝓝 r) := by
    simpa only [add_zero] using tendsto_const_nhds.add tendsto_one_div_two_pow
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => (lt_dyadicTime_upperDyadic r n).le) (dyadicTime_upperDyadic_le r)

theorem tendsto_dyadicTime_lowerDyadic (t : ℝ≥0) :
    Tendsto (fun n => dyadicTime (lowerDyadic t n)) atTop (𝓝 t) := by
  have hlo : Tendsto (fun n : ℕ => t - 1 / 2 ^ n) atTop (𝓝 t) := by
    simpa only [tsub_zero] using tendsto_const_nhds.sub tendsto_one_div_two_pow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds (fun n => ?_)
    (dyadicTime_lowerDyadic_le t)
  exact tsub_le_iff_right.2 (le_dyadicTime_lowerDyadic_add t n)

/-- `r < a` iff some dyadic time above `r` is below `a`. -/
theorem coe_lt_iff_exists_upperDyadic (r : ℝ≥0) (a : ℝ≥0∞) :
    (r : ℝ≥0∞) < a ↔ ∃ n, (dyadicTime (upperDyadic r n) : ℝ≥0∞) < a := by
  constructor
  · intro hra
    induction a using ENNReal.recTopCoe with
    | top => exact ⟨0, ENNReal.coe_lt_top⟩
    | coe s =>
      have hrs : r < s := ENNReal.coe_lt_coe.1 hra
      obtain ⟨n, hn⟩ := ((tendsto_dyadicTime_upperDyadic r).eventually (gt_mem_nhds hrs)).exists
      exact ⟨n, ENNReal.coe_lt_coe.2 hn⟩
  · rintro ⟨n, hn⟩
    exact lt_trans (ENNReal.coe_lt_coe.2 (lt_dyadicTime_upperDyadic r n)) hn

/-! ### The killed history -/

/-- The state space `ℝ × ℝ^{nL} × ℝ^{nR}` of the driving process `(W, V^L, V^R)`. -/
abbrev DrivingValue (nL nR : ℕ) : Type := ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)

/-- The killed-history space: a lifetime in `[0, ∞]` and a state at every dyadic time. It is a
standard Borel space. -/
abbrev HistorySpace (nL nR : ℕ) : Type := ℝ≥0∞ × (ℕ × ℕ → DrivingValue nL nR)

/-- **The killed driving history** of `(W, V^L, V^R)` with lifetime `ζ`: the lifetime and the state
at every dyadic time before it (`0` from the lifetime on). -/
def killedHistory {Ω : Type*} {nL nR : ℕ} (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : HistorySpace nL nR :=
  (ζ ω, fun p => if (dyadicTime p : ℝ≥0∞) < ζ ω then
    (W (dyadicTime p) ω, (fun i => VL i (dyadicTime p) ω), fun i => VR i (dyadicTime p) ω) else 0)

/-- The normalization of a history: the state is reset to `0` from the lifetime on. -/
def historyNormalize {nL nR : ℕ} (x : HistorySpace nL nR) : HistorySpace nL nR :=
  (x.1, fun p => if (dyadicTime p : ℝ≥0∞) < x.1 then x.2 p else 0)

theorem historyNormalize_killedHistory {Ω : Type*} {nL nR : ℕ} (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) :
    historyNormalize (killedHistory W VL VR ζ ω) = killedHistory W VL VR ζ ω := by
  simp only [historyNormalize, killedHistory, Prod.mk.injEq, true_and]
  funext p
  split_ifs <;> rfl

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω] {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

theorem measurableSet_lt_lifetime (hX : IsMeasurableKilledDriving W VL VR ζ) (r : ℝ≥0) :
    MeasurableSet {ω | (r : ℝ≥0∞) < ζ ω} := by
  simpa only [mem_univ, and_true] using hX r univ MeasurableSet.univ

/-- The lifetime is measurable when the killed driving is. -/
theorem measurable_lifetime (hX : IsMeasurableKilledDriving W VL VR ζ) : Measurable ζ := by
  refine measurable_of_Ioi fun a => ?_
  induction a using ENNReal.recTopCoe with
  | top => simp
  | coe r => exact measurableSet_lt_lifetime hX r

/-- The killed history is measurable when the killed driving is. -/
theorem measurable_killedHistory (hX : IsMeasurableKilledDriving W VL VR ζ) :
    Measurable (killedHistory W VL VR ζ) := by
  refine (measurable_lifetime hX).prodMk (Measurable.of_eval fun p => ?_)
  intro S hS
  have hpre : (fun ω => if (dyadicTime p : ℝ≥0∞) < ζ ω then
      (W (dyadicTime p) ω, (fun i => VL i (dyadicTime p) ω), fun i => VR i (dyadicTime p) ω)
      else 0) ⁻¹' S =
      {ω | (dyadicTime p : ℝ≥0∞) < ζ ω ∧ (W (dyadicTime p) ω, (fun i => VL i (dyadicTime p) ω),
          fun i => VR i (dyadicTime p) ω) ∈ S} ∪
        ({ω | (dyadicTime p : ℝ≥0∞) < ζ ω}ᶜ ∩ {_ω | (0 : DrivingValue nL nR) ∈ S}) := by
    ext ω
    by_cases h : (dyadicTime p : ℝ≥0∞) < ζ ω <;> simp [h]
  rw [hpre]
  exact (hX _ S hS).union ((measurableSet_lt_lifetime hX _).compl.inter (MeasurableSet.const _))

end Measurability

/-! ### Cylinder events determine a normalized history law -/

/-- The cylinder events `{t_j < ζ and X_{t_j} ∈ A_j for all j}` at finitely many dyadic times. -/
def historyCylinders (nL nR : ℕ) : Set (Set (HistorySpace nL nR)) :=
  {S | ∃ (n : ℕ) (ts : Fin n → ℕ × ℕ) (A : Fin n → Set (DrivingValue nL nR)),
    (∀ j, MeasurableSet (A j)) ∧
      S = {x | ∀ j, (dyadicTime (ts j) : ℝ≥0∞) < x.1 ∧ x.2 (ts j) ∈ A j}}

theorem isPiSystem_historyCylinders (nL nR : ℕ) : IsPiSystem (historyCylinders nL nR) := by
  rintro _ ⟨n, ts, A, hA, rfl⟩ _ ⟨m, ts', A', hA', rfl⟩ -
  refine ⟨n + m, Fin.append ts ts', Fin.append A A', fun j => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa only [Fin.append_left] using hA j
    · simpa only [Fin.append_right] using hA' j
  · ext x
    simp only [mem_inter_iff, mem_ofPred_eq, Fin.forall_fin_add, Fin.append_left, Fin.append_right]

theorem measurableSet_of_mem_historyCylinders {nL nR : ℕ} {S : Set (HistorySpace nL nR)}
    (hS : S ∈ historyCylinders nL nR) : MeasurableSet S := by
  obtain ⟨n, ts, A, hA, rfl⟩ := hS
  have : {x : HistorySpace nL nR | ∀ j, (dyadicTime (ts j) : ℝ≥0∞) < x.1 ∧ x.2 (ts j) ∈ A j} =
      ⋂ j, ({x : HistorySpace nL nR | (dyadicTime (ts j) : ℝ≥0∞) < x.1} ∩
        (fun x : HistorySpace nL nR => x.2 (ts j)) ⁻¹' A j) := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, mem_inter_iff, mem_preimage]
  rw [this]
  exact MeasurableSet.iInter fun j =>
    (measurableSet_lt measurable_const measurable_fst).inter
      ((measurable_pi_apply (ts j)).comp measurable_snd (hA j))

theorem generateFrom_historyCylinders_le (nL nR : ℕ) :
    MeasurableSpace.generateFrom (historyCylinders nL nR) ≤
      (inferInstance : MeasurableSpace (HistorySpace nL nR)) :=
  MeasurableSpace.generateFrom_le fun _ hS => measurableSet_of_mem_historyCylinders hS

/-- The normalization is measurable from the `σ`-algebra generated by the cylinder events. -/
theorem measurable_historyNormalize_generateFrom (nL nR : ℕ) :
    Measurable[MeasurableSpace.generateFrom (historyCylinders nL nR)]
      (historyNormalize (nL := nL) (nR := nR)) := by
  have hcyl : ∀ S ∈ historyCylinders nL nR,
      MeasurableSet[MeasurableSpace.generateFrom (historyCylinders nL nR)] S :=
    fun S hS => MeasurableSpace.measurableSet_generateFrom hS
  have hlt : ∀ p, MeasurableSet[MeasurableSpace.generateFrom (historyCylinders nL nR)]
      {x : HistorySpace nL nR | (dyadicTime p : ℝ≥0∞) < x.1} := fun p =>
    hcyl _ ⟨1, fun _ => p, fun _ => univ, fun _ => MeasurableSet.univ, by ext; simp⟩
  have hfst : Measurable[MeasurableSpace.generateFrom (historyCylinders nL nR)]
      (fun x : HistorySpace nL nR => x.1) := by
    refine measurable_of_Ioi fun a => ?_
    induction a using ENNReal.recTopCoe with
    | top => simp
    | coe r =>
      have hpre : (fun x : HistorySpace nL nR => x.1) ⁻¹' Ioi (r : ℝ≥0∞) =
          ⋃ n : ℕ, {x : HistorySpace nL nR | (dyadicTime (upperDyadic r n) : ℝ≥0∞) < x.1} := by
        ext x
        simp only [mem_preimage, mem_Ioi, mem_iUnion, mem_ofPred_eq]
        exact coe_lt_iff_exists_upperDyadic r x.1
      rw [hpre]
      exact MeasurableSet.iUnion fun n => hlt _
  refine hfst.prodMk (@Measurable.of_eval (HistorySpace nL nR) (ℕ × ℕ) (fun _ => DrivingValue nL nR)
    (MeasurableSpace.generateFrom (historyCylinders nL nR)) _ _ fun p => ?_)
  intro S hS
  have hpre : (fun x : HistorySpace nL nR =>
      if (dyadicTime p : ℝ≥0∞) < x.1 then x.2 p else 0) ⁻¹' S =
      {x : HistorySpace nL nR | ∀ j : Fin 1, (dyadicTime ((fun _ => p) j) : ℝ≥0∞) < x.1 ∧
          x.2 ((fun _ => p) j) ∈ (fun _ => S) j} ∪
        ({x : HistorySpace nL nR | (dyadicTime p : ℝ≥0∞) < x.1}ᶜ ∩
          {_x | (0 : DrivingValue nL nR) ∈ S}) := by
    ext x
    by_cases h : (dyadicTime p : ℝ≥0∞) < x.1 <;> simp [h]
  rw [hpre]
  exact (hcyl _ ⟨1, fun _ => p, fun _ => S, fun _ => hS, rfl⟩).union
    ((hlt p).compl.inter (MeasurableSet.const _))

theorem measurable_historyNormalize (nL nR : ℕ) :
    Measurable (historyNormalize (nL := nL) (nR := nR)) :=
  (measurable_historyNormalize_generateFrom nL nR).mono (generateFrom_historyCylinders_le nL nR)
    le_rfl

/-- **A normalized history law is determined by the cylinder events.** Two finite measures on the
history space, each invariant under `historyNormalize`, that agree on the cylinder events and have
the same total mass, are equal. -/
theorem measure_eq_of_historyCylinders {nL nR : ℕ} {μ ν : Measure (HistorySpace nL nR)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : μ.map historyNormalize = μ)
    (hν : ν.map historyNormalize = ν) (h : ∀ S ∈ historyCylinders nL nR, μ S = ν S)
    (huniv : μ univ = ν univ) : μ = ν := by
  have hle := generateFrom_historyCylinders_le nL nR
  have htrim : μ.trim hle = ν.trim hle := by
    refine ext_of_generate_finite (historyCylinders nL nR) rfl (isPiSystem_historyCylinders nL nR)
      (fun S hS => ?_) ?_
    · rw [trim_measurableSet_eq hle (MeasurableSpace.measurableSet_generateFrom hS),
        trim_measurableSet_eq hle (MeasurableSpace.measurableSet_generateFrom hS), h S hS]
    · rw [trim_measurableSet_eq hle MeasurableSet.univ, trim_measurableSet_eq hle MeasurableSet.univ,
        huniv]
  ext T hT
  have hT' : MeasurableSet[MeasurableSpace.generateFrom (historyCylinders nL nR)]
      (historyNormalize ⁻¹' T) := measurable_historyNormalize_generateFrom nL nR hT
  rw [← hμ, ← hν, Measure.map_apply (measurable_historyNormalize nL nR) hT,
    Measure.map_apply (measurable_historyNormalize nL nR) hT, ← trim_measurableSet_eq hle hT',
    ← trim_measurableSet_eq hle hT', htrim]

/-! ### Theorem 2.2's uniqueness in law and the law of the killed history -/

/-- **Theorem 2.2, uniqueness in law, for one force word** (Specification p. 21): the statement of
the frozen `IsIntegratedSLEEvolution.measure_killedState_eq` with `a` and the force word fixed (its
remaining hypotheses `0 < a` and `IsOrderedForceWord xL xR` are premises of the frozen theorem, not
of this predicate). Any two integrated `SLE_a(ρ)` evolutions of the word, on probability spaces in
the universes `u` and `v`, have the same finite-dimensional laws of the state killed at the
continuation threshold. -/
def KilledStateLawUnique (a : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Prop :=
  ∀ {Ω₁ : Type u} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞},
    IsIntegratedSLEEvolution a xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
    ∀ {Ω₂ : Type v} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
      {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ}
      {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞},
      IsIntegratedSLEEvolution a xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ →
      ∀ (n : ℕ) (ts : Fin n → ℝ≥0) (A : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
        (∀ j, MeasurableSet (A j)) →
        P₁ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₁ ω ∧
            (W₁ (ts j) ω, (fun i => VL₁ i (ts j) ω), (fun i => VR₁ i (ts j) ω), B₁ (ts j) ω) ∈ A j} =
          P₂ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₂ ω ∧
            (W₂ (ts j) ω, (fun i => VL₂ i (ts j) ω), (fun i => VR₂ i (ts j) ω), B₂ (ts j) ω) ∈ A j}

/-- `KilledStateLawUnique` with no force point (landed: `OneForce.measure_killedState_eq_none`). -/
theorem killedStateLawUnique_none (a : ℝ) (xL xR ρL ρR : Fin 0 → ℝ) :
    KilledStateLawUnique.{u, v} a xL xR ρL ρR :=
  fun h₁ _ _ _ _ _ _ _ _ _ _ h₂ n ts A hA => OneForce.measure_killedState_eq_none h₁ h₂ n ts A hA

/-- `KilledStateLawUnique` with one force point on the left (landed:
`OneForce.measure_killedState_eq_left`). -/
theorem killedStateLawUnique_left {a : ℝ} (ha : 0 < a) {xL : Fin 1 → ℝ} {xR : Fin 0 → ℝ}
    (ρL : Fin 1 → ℝ) (ρR : Fin 0 → ℝ) (hF : IsOrderedForceWord xL xR) :
    KilledStateLawUnique.{u, v} a xL xR ρL ρR :=
  fun h₁ _ _ _ _ _ _ _ _ _ _ h₂ n ts A hA =>
    OneForce.measure_killedState_eq_left ha hF h₁ h₂ n ts A hA

/-- `KilledStateLawUnique` with one force point on the right (landed:
`OneForce.measure_killedState_eq_right`). -/
theorem killedStateLawUnique_right {a : ℝ} (ha : 0 < a) {xL : Fin 0 → ℝ} {xR : Fin 1 → ℝ}
    (ρL : Fin 0 → ℝ) (ρR : Fin 1 → ℝ) (hF : IsOrderedForceWord xL xR) :
    KilledStateLawUnique.{u, v} a xL xR ρL ρR :=
  fun h₁ _ _ _ _ _ _ _ _ _ _ h₂ n ts A hA =>
    OneForce.measure_killedState_eq_right ha hF h₁ h₂ n ts A hA

/-- `KilledStateLawUnique` for the two seeds at `0⁻, 0⁺`, all weights (landed:
`Sec2.TwoSeed.measure_killedState_eq_twoSeed`). -/
theorem killedStateLawUnique_twoSeed {a : ℝ} (ha : 0 < a) {xL xR : Fin 1 → ℝ}
    (ρL ρR : Fin 1 → ℝ) (hxL : ∀ i, xL i = 0) (hxR : ∀ i, xR i = 0) :
    KilledStateLawUnique.{u, v} a xL xR ρL ρR :=
  fun h₁ _ _ _ _ _ _ _ _ _ _ h₂ n ts A hA =>
    Sec2.TwoSeed.measure_killedState_eq_twoSeed ha hxL hxR h₁ h₂ n ts A hA

/-- The preimage of a cylinder event under the killed history is the frozen Theorem 2.2 event at
the corresponding dyadic times (the Brownian coordinate unconstrained). -/
theorem killedHistory_preimage_cylinder {Ω : Type*} {nL nR : ℕ} (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    {n : ℕ} (ts : Fin n → ℕ × ℕ) (A : Fin n → Set (DrivingValue nL nR)) :
    killedHistory W VL VR ζ ⁻¹' {x | ∀ j, (dyadicTime (ts j) : ℝ≥0∞) < x.1 ∧ x.2 (ts j) ∈ A j} =
      {ω | ∀ j, (dyadicTime (ts j) : ℝ≥0∞) < ζ ω ∧
        (W (dyadicTime (ts j)) ω, (fun i => VL i (dyadicTime (ts j)) ω),
          (fun i => VR i (dyadicTime (ts j)) ω), B (dyadicTime (ts j)) ω) ∈
          (fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ => (p.1, p.2.1, p.2.2.1)) ⁻¹' A j} := by
  ext ω
  simp only [mem_preimage, mem_ofPred_eq, killedHistory]
  exact forall_congr' fun j => and_congr_right fun hj => by simp only [hj, ite_true]

/-- **The killed driving history has a unique law** (Theorem 2.2's uniqueness in law): under
`KilledStateLawUnique`, any two integrated `SLE_a(ρ)` evolutions of the word whose killed driving is
measurable have the same law of `killedHistory`. -/
theorem map_killedHistory_eq {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hU : KilledStateLawUnique.{u, v} a xL xR ρL ρR)
    {Ω₁ : Type u} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    (h₁ : IsIntegratedSLEEvolution a xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hX₁ : IsMeasurableKilledDriving W₁ VL₁ VR₁ ζ₁)
    {Ω₂ : Type v} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ}
    {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (h₂ : IsIntegratedSLEEvolution a xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (hX₂ : IsMeasurableKilledDriving W₂ VL₂ VR₂ ζ₂) :
    P₁.map (killedHistory W₁ VL₁ VR₁ ζ₁) = P₂.map (killedHistory W₂ VL₂ VR₂ ζ₂) := by
  have hm₁ := measurable_killedHistory hX₁
  have hm₂ := measurable_killedHistory hX₂
  have hN := measurable_historyNormalize nL nR
  have hproj : Measurable fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ => (p.1, p.2.1, p.2.2.1) :=
    measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_snd.snd.fst)
  refine measure_eq_of_historyCylinders ?_ ?_ ?_ (by simp only [measure_univ])
  · rw [Measure.map_map hN hm₁]
    congr 1
    funext ω
    exact historyNormalize_killedHistory W₁ VL₁ VR₁ ζ₁ ω
  · rw [Measure.map_map hN hm₂]
    congr 1
    funext ω
    exact historyNormalize_killedHistory W₂ VL₂ VR₂ ζ₂ ω
  · rintro _ ⟨n, ts, A, hA, rfl⟩
    rw [Measure.map_apply hm₁ (measurableSet_of_mem_historyCylinders ⟨n, ts, A, hA, rfl⟩),
      Measure.map_apply hm₂ (measurableSet_of_mem_historyCylinders ⟨n, ts, A, hA, rfl⟩),
      killedHistory_preimage_cylinder W₁ VL₁ VR₁ B₁ ζ₁ ts A,
      killedHistory_preimage_cylinder W₂ VL₂ VR₂ B₂ ζ₂ ts A]
    exact hU h₁ h₂ n (fun j => dyadicTime (ts j)) _ fun j => hproj (hA j)

end LawUnique

end InteractingSLE
