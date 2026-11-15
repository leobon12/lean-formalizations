/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.RestartMarkov
import InteractingSLE.Spec.Sec2.RestartPath
import InteractingSLE.Spec.Sec2.GirsanovCut
import InteractingSLE.Spec.Sec2.AssemblyUnique

/-!
# Restarting an integrated `SLE_a(ρ)` evolution at a stopping time

Packet PROVE-RESTART. Let `(W, V^{i,q}, B)` be an integrated `SLE_a(ρ)` evolution (frozen
`IsIntegratedSLEEvolution`) with lifetime `ζ`, `T` a finite stopping time of its filtration `𝓕`, and
`A ∈ 𝓕_T` an event of positive probability on which `T < ζ`. Under the conditional measure `P[·|A]`, the
process restarted at `T` and seen from the driver,

  `W'_t = W_{T+t} − W_T`, `V'^{i,q}_t = V^{i,q}_{T+t} − W_T`, `B'_t = B_{T+t} − B_T`, `ζ' = ζ − T`,

is an integrated evolution started from the random state `x' = V_T − W_T`, which is known at time `0`
of the restarted filtration `s ↦ 𝓕_{T+s}` (completed), and that filtration contains `𝓕_T`
(`exists_restart`). This is "conditionally on `𝓕_T`, the restarted process is an integrated evolution
from the state at `T`" in the event form: for every `A ∈ 𝓕_T` separately.

* `IsIntegratedSLEEvolutionFrom`: Definition 2.1 with an `𝓕_0`-measurable random start
  (`isIntegratedSLEEvolutionFrom_const_iff`: for a deterministic start it is the frozen definition);
* `progVersion`: a progressively measurable version of a process adapted before `ζ` (the `limsup` of its
  left dyadic values), equal to the process before `ζ` on every path that is continuous there;
* `exists_restart`: the restart.

The processes of the restart are versions: `W'` is built from `progVersion` (so that its values at the
random times `T + t` are measurable) and `B'` from a continuous version of `B` (QuantumZipper's strong
Markov property needs every path continuous); almost surely on `A` they are the shifted original
processes, as recorded in the conclusion.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

/-- **An integrated `SLE_a(ρ)` evolution from a random initial state** (Definition 2.1 with the force
positions `xL, xR` random and known at time `0`): `B` is a Brownian motion of `𝓕`, the initial positions
are `𝓕_0`-measurable, `W, V^{i,q}` are adapted before `ζ`, and almost surely the path satisfies
`IsIntegratedSLEPath` for the force word with positions `(xL ω; xR ω)`. -/
def IsIntegratedSLEEvolutionFrom (a : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  IsFilteredBrownianReal 𝓕 B P ∧
  (∀ i, Measurable[𝓕 0] fun ω => xL ω i) ∧ (∀ j, Measurable[𝓕 0] fun ω => xR ω j) ∧
  AdaptedBefore 𝓕 ζ W ∧ (∀ i, AdaptedBefore 𝓕 ζ (VL i)) ∧ (∀ j, AdaptedBefore 𝓕 ζ (VR j)) ∧
  ∀ᵐ ω ∂P, IsIntegratedSLEPath a (xL ω) (xR ω) ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
    (fun j t => VR j t ω) (fun t => B t ω) (ζ ω)

/-- With a deterministic start, `IsIntegratedSLEEvolutionFrom` is the frozen `IsIntegratedSLEEvolution`. -/
theorem isIntegratedSLEEvolutionFrom_const_iff {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} :
    IsIntegratedSLEEvolutionFrom a ρL ρR P 𝓕 (fun _ => xL) (fun _ => xR) W VL VR B ζ ↔
      IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by
  constructor
  · rintro ⟨h1, -, -, h4, h5, h6, h7⟩
    exact ⟨h1, h4, h5, h6, h7⟩
  · rintro ⟨h1, h4, h5, h6, h7⟩
    exact ⟨h1, fun _ => measurable_const, fun _ => measurable_const, h4, h5, h6, h7⟩

namespace Sec2

namespace Restart

open Girsanov QuantumZipper.StrongMarkov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-! ### A progressive version of a process adapted before `ζ` -/

/-- The `limsup` of the left dyadic values of the process killed at `ζ`: a progressive version of a
process that is adapted before `ζ`. -/
def progVersion (ζ : Ω → ℝ≥0∞) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limsup (fun n => killed ζ X (grid n (stepIdx n (t : ℝ))) ω) atTop

theorem isStronglyProgressive_progVersion {ζ : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ}
    (hX : AdaptedBefore 𝓕 ζ X) : IsStronglyProgressive 𝓕 (progVersion ζ X) := fun t =>
  (@measurable_limsup_gridEval_aux Ω (𝓕 t) t (killed ζ X)
    (fun s hs => (measurable_killed hX s).mono (𝓕.mono hs) le_rfl)).stronglyMeasurable

/-- On a path continuous before `ζ`, the version agrees with the process before `ζ`. -/
theorem progVersion_eq {ζ : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : ContinuousOn (fun s => X s ω) {s | (s : ℝ≥0∞) < ζ ω}) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ ω) : progVersion ζ X t ω = X t ω := by
  have hle : ∀ n, ((grid n (stepIdx n (t : ℝ)) : ℝ≥0) : ℝ≥0∞) < ζ ω := fun n =>
    (ENNReal.coe_le_coe.2 (grid_stepIdx_le n t)).trans_lt ht
  have heq : ∀ n, killed ζ X (grid n (stepIdx n (t : ℝ))) ω = X (grid n (stepIdx n (t : ℝ))) ω :=
    fun n => killed_of_lt (hle n)
  have hlim := (tendsto_of_continuousOn_lt hc ht).tendsto.comp (tendsto_grid_stepIdx t)
  rw [progVersion, (hlim.congr fun n => (heq n).symm).limsup_eq]

/-! ### Adaptedness of the restarted processes -/

variable {T : Ω → ℝ≥0}

/-- `{T + t < ζ}` belongs to `𝓕_{T+t}`. -/
theorem measurableSet_add_lt (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    {ζ : Ω → ℝ≥0∞} (hζ : IsStoppingTime 𝓕 fun ω => (ζ ω : WithTop ℝ≥0)) (t : ℝ≥0) :
    MeasurableSet[restartFiltration 𝓕 T hT t] {ω | ((T ω + t : ℝ≥0) : ℝ≥0∞) < ζ ω} := by
  have h := (IsStoppingTime.measurableSet_stopping_time_le hζ (isStoppingTime_add_const hT t)).compl
  have e : {ω | ((T ω + t : ℝ≥0) : ℝ≥0∞) < ζ ω} =
      {ω | (ζ ω : WithTop ℝ≥0) ≤ ((T ω + t : ℝ≥0) : WithTop ℝ≥0)}ᶜ := by
    ext ω
    exact (not_le (α := ℝ≥0∞)).symm
  rw [e]
  exact h

/-- The restarted difference `X_{T+t} − Y_T` of progressive processes is adapted before `ζ − T` in the
restarted filtration. -/
theorem adaptedBefore_restart (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    {ζ : Ω → ℝ≥0∞} (hζ : IsStoppingTime 𝓕 fun ω => (ζ ω : WithTop ℝ≥0)) {X Y : ℝ≥0 → Ω → ℝ}
    (hX : IsStronglyProgressive 𝓕 X) (hY : IsStronglyProgressive 𝓕 Y) :
    AdaptedBefore (restartFiltration 𝓕 T hT) (fun ω => ζ ω - T ω)
      (fun t ω => X (T ω + t) ω - Y (T ω) ω) := by
  intro t D hD
  have e : {ω | (t : ℝ≥0∞) < ζ ω - T ω ∧ X (T ω + t) ω - Y (T ω) ω ∈ D} =
      {ω | ((T ω + t : ℝ≥0) : ℝ≥0∞) < ζ ω} ∩
        (fun ω => X (T ω + t) ω - Y (T ω) ω) ⁻¹' D := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, coe_lt_sub_iff]
  rw [e]
  exact (measurableSet_add_lt hT hζ t).inter
    (((measurable_restart_eval hX hT t).sub (measurable_restart_eval_zero hY hT t)) hD)

theorem AdaptedBefore.mono_filtration {𝓖 : Filtration ℝ≥0 mΩ} (h : 𝓕 ≤ 𝓖) {ζ : Ω → ℝ≥0∞}
    {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓕 ζ X) : AdaptedBefore 𝓖 ζ X := fun t D hD =>
  h t _ (hX t D hD)

/-! ### The restart -/

section Main

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- On a path satisfying the frozen predicate, the progressive versions agree with the processes
before `ζ`. -/
theorem restart_values {ω : Ω}
    (hp : IsIntegratedSLEPath a xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ ω)) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) :
    progVersion ζ W s ω = W s ω ∧ (∀ i, progVersion ζ (VL i) s ω = VL i s ω) ∧
      ∀ j, progVersion ζ (VR j) s ω = VR j s ω :=
  ⟨progVersion_eq hp.isForcePath.continuousOn_w hs,
    fun i => progVersion_eq (hp.isForcePath.continuousOn_vL i) hs,
    fun j => progVersion_eq (hp.isForcePath.continuousOn_vR j) hs⟩

/-- **Restart of an integrated evolution at a stopping time** (strong Markov property, event form).
Let `(W, V, B)` be an integrated `SLE_a(ρ)` evolution with lifetime `ζ`, `T` a finite stopping time of
its filtration, and `A ∈ 𝓕_T` with `P A ≠ 0` and `T < ζ` on `A`. Then under `P[·|A]` there is an
integrated evolution `(W', V', B')` from a random initial state `(xL', xR')`, with lifetime `ζ − T`, in a
filtration `𝓕'` with `𝓕_T ≤ 𝓕'_0`, such that almost surely on `A`:
`x' = V_T − W_T`, `W'_t = W_{T+t} − W_T`, `V'_t = V_{T+t} − W_T` for `t < ζ − T`, and
`B'_t = B_{T+t} − B_T` for all `t`. -/
theorem exists_restart (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A) (hAζ : ∀ ω ∈ A, (T ω : ℝ≥0∞) < ζ ω)
    (hPA : P A ≠ 0) :
    ∃ (𝓕' : Filtration ℝ≥0 mΩ) (xL' : Ω → Fin nL → ℝ) (xR' : Ω → Fin nR → ℝ)
      (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ) (VR' : Fin nR → ℝ≥0 → Ω → ℝ)
      (B' : ℝ≥0 → Ω → ℝ),
      IsIntegratedSLEEvolutionFrom a ρL ρR (P[|A]) 𝓕' xL' xR' W' VL' VR' B'
        (fun ω => ζ ω - T ω) ∧
      hT.measurableSpace ≤ 𝓕' 0 ∧
      ∀ᵐ ω ∂P, ω ∈ A →
        (∀ i, xL' ω i = VL i (T ω) ω - W (T ω) ω) ∧ (∀ j, xR' ω j = VR j (T ω) ω - W (T ω) ω) ∧
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω - T ω →
          W' t ω = W (T ω + t) ω - W (T ω) ω ∧
          (∀ i, VL' i t ω = VL i (T ω + t) ω - W (T ω) ω) ∧
          ∀ j, VR' j t ω = VR j (T ω + t) ω - W (T ω) ω) ∧
        ∀ t : ℝ≥0, B' t ω = B (T ω + t) ω - B (T ω) ω := by
  obtain ⟨hBF, hWad, hVLad, hVRad, hpath⟩ := hE
  obtain ⟨Bv, -, hBvc, hBvF, hBvae⟩ := exists_continuous_version hBF
  have h𝓕𝓖 : 𝓕 ≤ usualAugmentation 𝓕 P := Ito.le_usualAugmentation 𝓕 P
  have hT𝓖 : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T ω : WithTop ℝ≥0) :=
    fun u => h𝓕𝓖 u _ (hT u)
  have hA𝓖 : MeasurableSet[hT𝓖.measurableSpace] A :=
    Ito.measurableSpace_le_of_filtration_le h𝓕𝓖 hT hT𝓖 _ hA
  have hζ := Ito.isStoppingTime_lifetime hWad
  have hle := restartFiltration_mono h𝓕𝓖 hT hT𝓖
  have hWp := isStronglyProgressive_progVersion hWad
  have hLp := fun i => isStronglyProgressive_progVersion (hVLad i)
  have hRp := fun j => isStronglyProgressive_progVersion (hVRad j)
  have hAm : MeasurableSet A := hT.measurableSpace_le _ hA
  refine ⟨restartFiltration (usualAugmentation 𝓕 P) T hT𝓖,
    fun ω i => progVersion ζ (VL i) (T ω) ω - progVersion ζ W (T ω) ω,
    fun ω j => progVersion ζ (VR j) (T ω) ω - progVersion ζ W (T ω) ω,
    fun t ω => progVersion ζ W (T ω + t) ω - progVersion ζ W (T ω) ω,
    fun i t ω => progVersion ζ (VL i) (T ω + t) ω - progVersion ζ W (T ω) ω,
    fun j t ω => progVersion ζ (VR j) (T ω + t) ω - progVersion ζ W (T ω) ω,
    smShift Bv T, ⟨isFilteredBrownianReal_restart_cond hBvF hBvc hT𝓖 hA𝓖 hPA, fun i => ?_,
      fun j => ?_, AdaptedBefore.mono_filtration hle (adaptedBefore_restart hT hζ hWp hWp),
      fun i => AdaptedBefore.mono_filtration hle (adaptedBefore_restart hT hζ (hLp i) hWp),
      fun j => AdaptedBefore.mono_filtration hle (adaptedBefore_restart hT hζ (hRp j) hWp), ?_⟩,
    ?_, ?_⟩
  · exact ((measurable_restart_eval_zero (hLp i) hT 0).sub
      (measurable_restart_eval_zero hWp hT 0)).mono (hle 0) le_rfl
  · exact ((measurable_restart_eval_zero (hRp j) hT 0).sub
      (measurable_restart_eval_zero hWp hT 0)).mono (hle 0) le_rfl
  · filter_upwards [cond_absolutelyContinuous.ae_le hpath, cond_absolutelyContinuous.ae_le hBvae,
      ae_cond_mem hAm] with ω hp hb hωA
    have hTζ := hAζ ω hωA
    have h0 := restart_values hp hTζ
    have hr := hp.restart hTζ
    have e1 : (fun i => progVersion ζ (VL i) (T ω) ω - progVersion ζ W (T ω) ω) =
        fun i => VL i (T ω) ω - W (T ω) ω := by
      funext i; rw [h0.2.1 i, h0.1]
    have e2 : (fun j => progVersion ζ (VR j) (T ω) ω - progVersion ζ W (T ω) ω) =
        fun j => VR j (T ω) ω - W (T ω) ω := by
      funext j; rw [h0.2.2 j, h0.1]
    show IsIntegratedSLEPath a
      (fun i => progVersion ζ (VL i) (T ω) ω - progVersion ζ W (T ω) ω)
      (fun j => progVersion ζ (VR j) (T ω) ω - progVersion ζ W (T ω) ω) ρL ρR
      (fun t => progVersion ζ W (T ω + t) ω - progVersion ζ W (T ω) ω)
      (fun i t => progVersion ζ (VL i) (T ω + t) ω - progVersion ζ W (T ω) ω)
      (fun j t => progVersion ζ (VR j) (T ω + t) ω - progVersion ζ W (T ω) ω)
      (fun t => smShift Bv T t ω) (ζ ω - T ω)
    rw [e1, e2]
    refine Sec2.Assembly.isIntegratedSLEPath_congr hr ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [add_zero, h0.1]
    · intro i; simp only [add_zero, h0.1, h0.2.1 i]
    · intro j; simp only [add_zero, h0.1, h0.2.2 j]
    · intro t ht
      have h1 := restart_values hp ((coe_lt_sub_iff _ _).1 ht)
      simp only [h0.1, h1.1]
    · intro t ht i
      have h1 := restart_values hp ((coe_lt_sub_iff _ _).1 ht)
      simp only [h0.1, h1.2.1 i]
    · intro t ht j
      have h1 := restart_values hp ((coe_lt_sub_iff _ _).1 ht)
      simp only [h0.1, h1.2.2 j]
    · intro t _
      simp only [smShift, hb]
  · rw [restartFiltration_zero]
    exact Ito.measurableSpace_le_of_filtration_le h𝓕𝓖 hT hT𝓖
  · filter_upwards [hpath, hBvae] with ω hp hb hωA
    have hTζ := hAζ ω hωA
    have h0 := restart_values hp hTζ
    refine ⟨fun i => by simp only [h0.1, h0.2.1 i], fun j => by simp only [h0.1, h0.2.2 j],
      fun t ht => ?_, fun t => by simp only [smShift, hb]⟩
    have h1 := restart_values hp ((coe_lt_sub_iff _ _).1 ht)
    exact ⟨by simp only [h0.1, h1.1], fun i => by simp only [h0.1, h1.2.1 i],
      fun j => by simp only [h0.1, h1.2.2 j]⟩

end Main

end Restart

end Sec2

end InteractingSLE
