/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootJ31Construction
import InteractingSLE.Spec.Supplement.GW2RootJ31Meas

/-!
# J32: J31 with a running-maximum inverse clock (ruling R110)

Packet PROVE-GW2-GEOM2. J31's capacity tip `RootI30.capacityTipRead x s v u p` inverts the capacity reader
`t ↦ forwardCapacity x s t p` over the whole horizon `v = T + cap`; past the physical buffer that reader can
drop (to `0` when the relative image is unbounded), which poisons the inverse clock. J32 inverts instead the
**running maximum of the capacity reader in the bounded scale `arctan`**,
`runMax x s t p = ⨆ q ∈ ℚ, q⁺ ≤ t, arctan (forwardCapacity x s q⁺ p)`, which is monotone in `t` at every
sample, causal (it reads the capacity reader only on `[0, t]`) and bounded (so the real supremum is honest).
Everything else is J31's: the increments (`RootJ31.capacityIncrement`), the clock (`RootJ31.sourceClock`), the
buffer and failure (`RootJ31.sourceBuffer`, `RootJ31.sourceFailure`), the records (`RootJ31.futurePair`).

This file gives the readers and their measurability:

* `runMax`, `clockInverse`, `capacityTipRead`, `capacityDriverRead`, `stageDriverRead`, `switchedSample`,
  `switchedEntry`, `jointDriverRead`, `jointTraceRead`, `jointTipRead`;
* `sourceSample`, `sourceDriver`, `sourceX`, `sourceTip`, `sourceEntry`;
* measurability at random times, as for J31.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ32

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 RootB23 RootD25 RootV7

/-! ### The readers -/

/-- **The running maximum of the capacity reader**, in the bounded scale `arctan`. -/
def runMax (x : ℝ) (s t : ℝ≥0) (p : RecData × RecData) : ℝ :=
  ⨆ q : ℚ, if ((q : ℝ)).toNNReal ≤ t then
    Real.arctan (RootH29.forwardCapacity x s ((q : ℝ)).toNNReal p) else 0

/-- The inverse of the running maximum: the time where the capacity first reaches the level `u`. -/
def clockInverse (x : ℝ) (s v u : ℝ≥0) (p : RecData × RecData) : ℝ≥0 :=
  invClock (fun t => runMax x s t p) (v : ℝ≥0∞) (Real.arctan u).toNNReal

/-- The centered tip in relative capacity time, read through the running-maximum clock. -/
def capacityTipRead (x : ℝ) (s v u : ℝ≥0) (p : RecData × RecData) : ℂ :=
  RootH29.rootTipRead x s (clockInverse x s v u p) p

/-- The driver read off the capacity-time tip. -/
def capacityDriverRead (x : ℝ) (s v u : ℝ≥0) (p : RecData × RecData) : ℝ :=
  traceDriverRead (fun t => capacityTipRead x s v t p) u

/-- The absolute stage driver (as `RootJ31.stageDriverRead`, with J32's capacity driver). -/
def stageDriverRead (a : ℝ≥0) (ε x : ℝ) (s v v₀ T u : ℝ≥0) (p : RecData × RecData) : ℝ :=
  ε * (a : ℝ) * (capacityDriverRead x s v
      ((RootH29.forwardCapacity x s T p).toNNReal + u / a ^ 2) p -
    capacityDriverRead x s v (RootH29.forwardCapacity x s v₀ p).toNNReal p)

/-- The future sample, killed at J31's capacity increment at the buffer. -/
def switchedSample (a : ℝ≥0) (ε x : ℝ) (s v v₀ T F : ℝ≥0)
    (p : RecData × RecData) : DriverRecord :=
  (RootJ31.capacityIncrement a x s T F p, fun q =>
    if ((q : ℝ≥0) : ℝ≥0∞) < (RootJ31.capacityIncrement a x s T F p : ℝ≥0∞) then
      stageDriverRead a ε x s v v₀ T q p else 0)

/-- The sample's first crossing pulled back to its own physical time (as `RootJ31.switchedEntry`). -/
def switchedEntry (a : ℝ≥0) (ε x : ℝ) (s v v₀ T F : ℝ≥0) (p : RecData × RecData) : ℝ≥0 :=
  open scoped Classical in
  if switchedSample a ε x s v v₀ T F p ∈ reachSet then
    invClock (fun t => (RootJ31.capacityIncrement a x s T t p : ℝ)) (F : ℝ≥0∞)
      (entryCapacity (switchedSample a ε x s v v₀ T F p)).toNNReal else F

/-- The root-normalized joint driver. -/
def jointDriverRead (a : ℝ≥0) (x : ℝ) (s v v₀ : ℝ≥0) (p : RecData × RecData) : ℝ≥0 → ℝ :=
  fun u => stageDriverRead a 1 x s v v₀ v₀ u p

/-- The trace of the joint driver, read with lifetime `⊤` (orchestrator-approved fix F3): at every capacity
time `w` it is `LP.traceAt w` of the joint driver, which reads the driver on `[0, w]` only. (Reading it with the
lifetime `RootJ31.capacityIncrement a x s v₀ (v - v₀) p` at the full horizon made the trace the constant
`endpointTrace 0 = 0` whenever that increment vanished, e.g. when the relative image at the horizon was
unbounded.) -/
def jointTraceRead (a : ℝ≥0) (x : ℝ) (s v v₀ : ℝ≥0) (p : RecData × RecData) : ℝ≥0 → ℂ :=
  (LP.drivingTrace (⊤, jointDriverRead a x s v v₀ p)).2

def jointTipRead (a : ℝ≥0) (x : ℝ) (s v v₀ u : ℝ≥0) (p : RecData × RecData) : ℂ :=
  endVal ((u : ℝ≥0∞), jointTraceRead a x s v v₀ p)

/-! ### Measurability -/

section Meas

variable {Ω : Type*} [MeasurableSpace Ω] {p : Ω → RecData × RecData} (hp : Measurable p)
include hp

theorem measurable_runMax_random (x : ℝ) (s : ℝ≥0) {t : Ω → ℝ≥0} (ht : Measurable t) :
    Measurable fun ω => runMax x s (t ω) (p ω) := by
  classical
  unfold runMax
  refine Measurable.iSup fun q : ℚ => Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_le measurable_const ht
  · exact Real.continuous_arctan.measurable.comp
      (RootH29.measurable_forwardCapacity_random x s hp measurable_const)

theorem measurable_clockInverse_random (x : ℝ) (s v : ℝ≥0) {u : Ω → ℝ≥0} (hu : Measurable u) :
    Measurable fun ω => clockInverse x s v (u ω) (p ω) := by
  classical
  unfold clockInverse invClock
  refine Measurable.iSup fun q : ℚ => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    (measurableSet_lt (measurable_runMax_random hp x s measurable_const)
      (NNReal.continuous_coe.measurable.comp
        (Real.continuous_arctan.measurable.comp
          (NNReal.continuous_coe.measurable.comp hu)).real_toNNReal)))

theorem measurable_capacityTipRead_random (x : ℝ) (s v : ℝ≥0) {u : Ω → ℝ≥0}
    (hu : Measurable u) : Measurable fun ω => capacityTipRead x s v (u ω) (p ω) :=
  RootH29.measurable_rootTipRead_random x s hp (measurable_clockInverse_random hp x s v hu)

theorem measurable_capacityTraceHull_random (x : ℝ) (s v : ℝ≥0) {u : Ω → ℝ≥0}
    (hu : Measurable u) :
    Measurable[_, hittingSigma] fun ω =>
      traceHullRead (fun t => capacityTipRead x s v t (p ω)) (u ω) := by
  have hc := Sec5.Aux61SlitW.measurable_closure_range
    (fun j : ℕ × ℕ => measurable_capacityTipRead_random hp x s v
      (measurable_const.min hu) (u := fun ω => min (LawUnique.dyadicTime j) (u ω)))
  apply Restart.FlowStopIdentCMI.measurable_hullFillReader.comp
  refine measurable_generateFrom ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have he : (fun ω =>
      closure (range fun j : ℕ × ℕ => capacityTipRead x s v
        (min (LawUnique.dyadicTime j) (u ω)) (p ω)) ∩ QuantumZipper.H) ⁻¹'
        {A : Set ℂ | (A ∩ U).Nonempty} =
      (fun ω => closure (range fun j : ℕ × ℕ => capacityTipRead x s v
        (min (LawUnique.dyadicTime j) (u ω)) (p ω))) ⁻¹'
          {A : Set ℂ | (A ∩ U).Nonempty} := by
    ext ω
    constructor
    · rintro ⟨z, ⟨hz, _⟩, hzU⟩
      exact ⟨z, hz, hzU⟩
    · rintro ⟨z, hz, hzU⟩
      exact ⟨z, ⟨hz, hUH hzU⟩, hzU⟩
  rw [he]
  exact hc (LocalSets.measurableSet_hitting hU hUH)

theorem measurable_capacityDriverRead_random (x : ℝ) (s v : ℝ≥0) {u : Ω → ℝ≥0}
    (hu : Measurable u) : Measurable fun ω => capacityDriverRead x s v (u ω) (p ω) := by
  classical
  unfold capacityDriverRead traceDriverRead GW2JDetR4.hullDriverRead
  refine Measurable.ite (hu (measurableSet_singleton 0)) measurable_const ?_
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.limUnder
  intro N
  apply StronglyMeasurable.limUnder
  intro k
  have h1 := (GW2JDetR4.measurable_hullMapRead (Sec7.Lemma71C.zPt N)).comp
    (measurable_capacityTraceHull_random hp x s v hu)
  have ht : Measurable fun ω => ((u ω : ℝ) - 1 / ((k : ℝ) + 1)).toNNReal :=
    ((NNReal.continuous_coe.measurable.comp hu).sub_const _).real_toNNReal
  have h2 := (GW2JDetR4.measurable_hullMapRead (Sec7.Lemma71C.zPt N)).comp
    (measurable_capacityTraceHull_random hp x s v ht)
  exact (Complex.measurable_re.comp (h1.sub
    (measurable_const.div (measurable_const.mul (h1.sub h2))))).stronglyMeasurable

theorem measurable_stageDriverRead_random (a : ℝ≥0) (ε x : ℝ) (s v v₀ T : ℝ≥0)
    {u : Ω → ℝ≥0} (hu : Measurable u) :
    Measurable fun ω => stageDriverRead a ε x s v v₀ T (u ω) (p ω) := by
  have hT := (RootH29.measurable_forwardCapacity_random x s hp
    (measurable_const : Measurable (fun _ : Ω => T))).real_toNNReal
  have h₀ := (RootH29.measurable_forwardCapacity_random x s hp
    (measurable_const : Measurable (fun _ : Ω => v₀))).real_toNNReal
  exact measurable_const.mul
    ((measurable_capacityDriverRead_random hp x s v (hT.add (hu.div_const _))).sub
      (measurable_capacityDriverRead_random hp x s v h₀))

theorem measurable_switchedSample_random (a : ℝ≥0) (ε x : ℝ) (s v v₀ T : ℝ≥0)
    {F : Ω → ℝ≥0} (hF : Measurable F) :
    Measurable fun ω => switchedSample a ε x s v v₀ T (F ω) (p ω) := by
  have hlife := measurable_coe_nnreal_ennreal.comp
    (RootJ31.measurable_capacityIncrement_random hp hF a x s T)
  exact hlife.prodMk (measurable_pi_iff.mpr fun q => Measurable.ite
    (measurableSet_lt measurable_const hlife)
    (measurable_stageDriverRead_random hp a ε x s v v₀ T measurable_const)
    measurable_const)

theorem measurable_switchedEntry_random {F : Ω → ℝ≥0} (hF : Measurable F)
    (a : ℝ≥0) (ε x : ℝ) (s v v₀ T : ℝ≥0) :
    Measurable fun ω => switchedEntry a ε x s v v₀ T (F ω) (p ω) := by
  classical
  have hz := measurable_switchedSample_random hp a ε x s v v₀ T hF
  have hτ := (measurable_entryCapacity.comp hz).ennreal_toNNReal
  have hi : Measurable fun ω => invClock
      (fun t => (RootJ31.capacityIncrement a x s T t (p ω) : ℝ)) (F ω : ℝ≥0∞)
      (entryCapacity (switchedSample a ε x s v v₀ T (F ω) (p ω))).toNNReal := by
    unfold invClock
    refine Measurable.iSup fun q : ℚ => Measurable.ite ?_ measurable_const measurable_const
    exact (MeasurableSet.const _).inter
      ((measurableSet_le measurable_const (measurable_coe_nnreal_ennreal.comp hF)).inter
        (measurableSet_lt (NNReal.continuous_coe.measurable.comp
          (RootJ31.measurable_capacityIncrement_random hp measurable_const a x s T))
          (NNReal.continuous_coe.measurable.comp hτ)))
  exact Measurable.ite (hz measurableSet_reachSet) hi hF

theorem measurable_jointTipRead_random (a : ℝ≥0) (x : ℝ) (s v v₀ : ℝ≥0) {u : Ω → ℝ≥0}
    (hu : Measurable u) : Measurable fun ω => jointTipRead a x s v v₀ (u ω) (p ω) := by
  have hJ : Measurable (jointDriverRead a x s v v₀) :=
    measurable_pi_iff.mpr fun _ =>
      measurable_stageDriverRead_random measurable_id a 1 x s v v₀ v₀ measurable_const
  have hT : Measurable (jointTraceRead a x s v v₀) :=
    (measurable_snd.comp LP.measurable_drivingTrace).comp (measurable_const.prodMk hJ)
  exact measurable_endVal.comp ((measurable_coe_nnreal_ennreal.comp hu).prodMk (hT.comp hp))

end Meas

/-! ### The source readers of a candidate -/

variable {Ω : Type u} [MeasurableSpace Ω]

def sourceSample (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) : DriverRecord :=
  switchedSample (2 ^ r.2) ((-1) ^ l.length) (rootPt r.1) c.s
    (RootJ31.historyTime c r l + RootJ31.candidateCap c r a) (rootEntry r.1).2
    (RootJ31.historyTime c r l) (RootJ31.sourceBuffer c r l a ω) (RootJ31.futurePair c r l a ω)

def sourceDriver (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) (u : ℝ≥0) : ℝ :=
  stageDriverRead (2 ^ r.2) ((-1) ^ l.length) (rootPt r.1) c.s
    (RootJ31.historyTime c r l + RootJ31.candidateCap c r a) (rootEntry r.1).2
    (RootJ31.historyTime c r l) u (RootJ31.futurePair c r l a ω)

def sourceX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) (q : ℝ) : ℝ :=
  sourceDriver c r l a ω (RootJ31.sourceClock c r l a q.toNNReal ω)

def sourceTip (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) (q : ℝ) : ℂ :=
  RootJ31.orientTip l.length (jointTipRead (2 ^ r.2) (rootPt r.1) c.s
    (RootJ31.historyTime c r l + RootJ31.candidateCap c r a) (rootEntry r.1).2
    (RootJ31.capacityIncrement (2 ^ r.2) (rootPt r.1) c.s (rootEntry r.1).2
      ((RootJ31.historyTime c r l + (q.toNNReal - RootJ31.historyTime c r l)) - (rootEntry r.1).2)
      (RootJ31.futurePair c r l a ω)) (RootJ31.futurePair c r l a ω))

def sourceEntry (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) : ℝ :=
  (RootJ31.historyTime c r l + switchedEntry (2 ^ r.2) ((-1) ^ l.length) (rootPt r.1) c.s
    (RootJ31.historyTime c r l + RootJ31.candidateCap c r a) (rootEntry r.1).2
    (RootJ31.historyTime c r l) (RootJ31.sourceBuffer c r l a ω)
    (RootJ31.futurePair c r l a ω) : ℝ≥0)

theorem measurable_sourceSample (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) : Measurable (sourceSample c r l a) :=
  measurable_switchedSample_random (RootJ31.measurable_futurePair c r l a) _ _ _ _ _ _ _
    (RootJ31.measurable_sourceBuffer c r l a)

theorem measurable_sourceX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : ℝ) : Measurable fun ω => sourceX c r l a ω q :=
  measurable_stageDriverRead_random (RootJ31.measurable_futurePair c r l a) _ _ _ _ _ _ _
    (RootJ31.measurable_sourceClock c r l a q.toNNReal)

theorem measurable_sourceTip (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : ℝ) : Measurable fun ω => sourceTip c r l a ω q :=
  (RootJ31.measurable_orientTip l.length).comp
    (measurable_jointTipRead_random (RootJ31.measurable_futurePair c r l a) _ _ _ _ _
      (RootJ31.measurable_capacityIncrement_random (RootJ31.measurable_futurePair c r l a)
        measurable_const _ _ _ _))

theorem measurable_sourceEntry (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) : Measurable (sourceEntry c r l a) :=
  NNReal.continuous_coe.measurable.comp (measurable_const.add
    (measurable_switchedEntry_random (RootJ31.measurable_futurePair c r l a)
      (RootJ31.measurable_sourceBuffer c r l a) _ _ _ _ _ _ _))

theorem sourceSample_read (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) {q : ℚ≥0}
    (hq : ((q : ℝ≥0) : ℝ≥0∞) < (sourceSample c r l a ω).1) :
    (sourceSample c r l a ω).2 q = sourceDriver c r l a ω q :=
  ite_eq_left hq

end InteractingSLE.Theorem14.GW2TipSystem.RootJ32
