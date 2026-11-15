/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkMarkedLocal
import InteractingSLE.Spec.Exist.StagedLaw2Run
import InteractingSLE.Spec.Supplement.GW2LaterMeas
import InteractingSLE.Spec.Sec7.FanTipFiberSimul

/-!
# Theorem 1.4: the explored set of a staged history is recorded by its past, up to null sets (R58)

Packet PROVE-T14-WALKLAW3. Part D.5 of the follow-up note (`source/external/AstraIG1/ig1_followup_a_e_audited.txt`
L866–L901: "the classified word is measurable in the past history") gives clause (i) of
`WalkLaw.WalkMarkedLocalRegStatement`: the avoidance events of the explored set are events of the retained past. The
traces of the pieces exist only almost surely, so (ruling R58) the clause is proved up to null sets:

* **`exists_measurable_runChart_inv`**: on a measurable event on which the launched pieces are regular, the inverse
  chart of the run after `n` instructions, at a measurable point of `ℍ`, agrees with a measurable function (the run
  analogue of GW2Later's `exists_measurable_succChart_inv`; the chart changes only by recentrings and Loewner maps of
  stopped drivers, measurable through `RunMeasStatement`, the joint continuity of `t ↦ f_t⁻¹(z)`, and Carathéodory);
* **`ae_avoid_iff_tipPoints`**: on that event, the explored set after `k` instructions avoids an open `U ⊆ ℍ` iff no
  physical tip point at a dyadic-rational time `m / (n + 1)` lies in `U` (the physical path is continuous,
  `CounterflowRange.tipSet_stopped_eq_of_tendsto`, GW1P's good charts);
* **`mem_aeSigma_of_frozen`**: a null-measurable event determined by a quantity frozen under the regular conditional
  laws given `𝒢` is an event of `𝒢` up to null sets;
* **`measurableSet_aeSigma_stageSet_avoid`** and **`walkStageAvoidMeasAEStatement`**: the R58 form of
  `WalkStageAvoidMeasStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace WalkLaw

open LocalSets Exist.Staged Exist.StagedLaw

/-! ### The inverse chart of a run at a random point -/

section RunInv

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- For a driver regular at its lifetime, stopping at `min t ζ` is stopping at `t` (the driver is constant from its
lifetime on). -/
theorem stopped_min_lifetime {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) (t : ℝ≥0∞) {r : ℝ≥0∞}
    (hr : r ≠ ⊤) : e.1 (min r (min t e.2)).toNNReal = e.1 (min r t).toNNReal := by
  rcases le_or_gt (min r t) e.2 with h | h
  · rw [← min_assoc, min_eq_left h]
  · have h1 : min r (min t e.2) = e.2 := by
      rw [← min_assoc]; exact min_eq_right h.le
    rw [h1]
    have hfin : min r t ≠ ⊤ := ne_top_of_le_ne_top hr (min_le_left _ _)
    have h2 : e.2 ≤ (((min r t).toNNReal : ℝ≥0) : ℝ≥0∞) := by rw [ENNReal.coe_toNNReal hfin]; exact h.le
    exact (he.2.2.1 _ h2).symm

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The inverse Loewner map at a random time and a random point is measurable** (continuous measurable drivers
from `0`; Carathéodory in the time, through the continuity of `t ↦ f_t⁻¹(z)`). -/
theorem measurable_fwdMapInv_randomTime {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (hB0 : ∀ ω, B 0 ω = 0) {T : Ω → ℝ≥0} (hT : Measurable T)
    {Z : Ω → ℂ} (hZ : Measurable Z) (hZH : ∀ ω, Z ω ∈ H) :
    Measurable fun ω => fwdMapInv (fun x : ℝ => B x.toNNReal ω) (T ω : ℝ) (Z ω) := by
  set u : ℝ≥0 → Ω → ℂ := fun (S : ℝ≥0) (ω : Ω) => fwdMapInv (fun x : ℝ => B x.toNNReal ω) (S : ℝ) (Z ω)
    with hu
  have h1 : ∀ ω, Continuous fun S => u S ω := fun ω =>
    Sec7.continuous_fwdMapInv_time ((hBc ω).comp continuous_real_toNNReal) (by simpa using hB0 ω) (hZH ω)
  have h2 : ∀ S, Measurable (u S) := fun S =>
    GW2Later.measurable_fwdMapInv_of_continuous hBm hBc hB0 S.coe_nonneg hZ hZH
  have hUm : Measurable (Function.uncurry u) := measurable_uncurry_of_continuous_of_measurable h1 h2
  have e : (fun ω => fwdMapInv (fun x : ℝ => B x.toNNReal ω) (T ω : ℝ) (Z ω)) =
      Function.uncurry u ∘ fun ω => (T ω, ω) := rfl
  rw [e]
  exact hUm.comp (hT.prodMk measurable_id)

/-- The stopped launch driver of instruction `n` on the event `M ∩ {n launches}` (`0` elsewhere). -/
def launchDrv (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (M : Set Ω) (n : ℕ) : ℝ≥0 → Ω → ℝ :=
  GW2Later.regDrv (M ∩ {ω | (ExplState.run κ b jumps spec (fun i => E i ω) (n + 1)).2.2.2.1 n ≠ none})
    (instrTime spec n) (E n)

section LaunchDrv

variable {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {M : Set Ω}

omit [MeasurableSpace Ω] in
theorem launchDrv_eq (hreg : ∀ j ω, IsRegularDriver (E j ω)) {n : ℕ} {ω : Ω} (hω : ω ∈ M)
    (hl : (ExplState.run κ b jumps spec (fun i => E i ω) (n + 1)).2.2.2.1 n ≠ none) (t : ℝ≥0) :
    launchDrv κ b jumps spec E M n t ω = (E n ω).1 (min (t : ℝ≥0∞) (min (instrTime spec n) (E n ω).2)).toNNReal := by
  have hω' : ω ∈ M ∩ {ω | (ExplState.run κ b jumps spec (fun i => E i ω) (n + 1)).2.2.2.1 n ≠ none} := ⟨hω, hl⟩
  simp only [launchDrv, GW2Later.regDrv, hω', ↓reduceIte]
  exact (stopped_min_lifetime (hreg n ω) _ ENNReal.coe_ne_top).symm

omit [MeasurableSpace Ω] in
theorem launchDrv_of_not {n : ℕ} {ω : Ω}
    (hω : ¬ (ω ∈ M ∧ (ExplState.run κ b jumps spec (fun i => E i ω) (n + 1)).2.2.2.1 n ≠ none)) (t : ℝ≥0) :
    launchDrv κ b jumps spec E M n t ω = 0 := by
  have hω' : ω ∉ M ∩ {ω | (ExplState.run κ b jumps spec (fun i => E i ω) (n + 1)).2.2.2.1 n ≠ none} := hω
  simp only [launchDrv, GW2Later.regDrv, hω', ↓reduceIte]

variable (hreg : ∀ j ω, IsRegularDriver (E j ω))
  (hMreg : ∀ ω ∈ M, ∀ (j : ℕ) (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = some (c, θ) →
      GW1P.PieceRegular (E j ω).1 (min (instrTime spec j) (E j ω).2))
include hreg hMreg

omit [MeasurableSpace Ω] in
theorem continuous_launchDrv (n : ℕ) (ω : Ω) : Continuous fun t => launchDrv κ b jumps spec E M n t ω := by
  by_cases hω : ω ∈ M ∧ (ExplState.run κ b jumps spec (fun i => E i ω) (n + 1)).2.2.2.1 n ≠ none
  · obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 hω.2
    have hpr := hMreg ω hω.1 n x.1 x.2 (by rw [hx])
    have e : (fun t => launchDrv κ b jumps spec E M n t ω) =
        fun t : ℝ≥0 => (E n ω).1 (min (t : ℝ≥0∞) (min (instrTime spec n) (E n ω).2)).toNNReal :=
      funext (launchDrv_eq hreg hω.1 hω.2)
    rw [e]
    exact CounterflowRange.continuous_stopped hpr.2.1
  · have e : (fun t => launchDrv κ b jumps spec E M n t ω) = fun _ => 0 := funext (launchDrv_of_not hω)
    rw [e]
    exact continuous_const

omit [MeasurableSpace Ω] hMreg in
theorem launchDrv_zero (n : ℕ) (ω : Ω) : launchDrv κ b jumps spec E M n 0 ω = 0 := by
  by_cases hω : ω ∈ M ∧ (ExplState.run κ b jumps spec (fun i => E i ω) (n + 1)).2.2.2.1 n ≠ none
  · rw [launchDrv_eq hreg hω.1 hω.2, CounterflowRange.stopped_eq_of_lt (W := (E n ω).1) (t := 0) (by simp)]
    exact (hreg n ω).2.1
  · exact launchDrv_of_not hω 0

end LaunchDrv

/-- **One instruction of the inverse chart at a random point.** On the event `M` of regular launched pieces, the
inverse chart after `n + 1` instructions at `Z ω ∈ ℍ` is the inverse chart after `n` instructions at a measurable
point `Z' ω ∈ ℍ` (unchanged, recentred, or moved by the inverse Loewner map of the launched piece). -/
theorem exists_runChart_inv_succ (hb : IsPiecewiseConstantBoundaryData b jumps) (spec : ExplSpec)
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {M : Set Ω} (hM : MeasurableSet M)
    (hMreg : ∀ ω ∈ M, ∀ (j : ℕ) (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = some (c, θ) →
      GW1P.PieceRegular (E j ω).1 (min (instrTime spec j) (E j ω).2)) (n : ℕ) {Z : Ω → ℂ}
    (hZ : Measurable Z) (hZH : ∀ ω, Z ω ∈ H) :
    ∃ Z' : Ω → ℂ, Measurable Z' ∧ (∀ ω, Z' ω ∈ H) ∧ ∀ ω ∈ M,
      (ExplState.run κ b jumps spec (fun i => E i ω) (n + 1)).2.2.2.2.1.2.1 (Z ω) =
        (ExplState.run κ b jumps spec (fun i => E i ω) n).2.2.2.2.1.2.1 (Z' ω) := by
  classical
  have hRM := runMeasStatement κ b jumps hb spec E hEm hreg
  obtain ⟨L, hLdef⟩ : ∃ L : Set Ω,
      L = {ω | (ExplState.run κ b jumps spec (fun i => E i ω) (n + 1)).2.2.2.1 n ≠ none} := ⟨_, rfl⟩
  have hL : MeasurableSet L := hLdef ▸ (hRM n).1
  obtain ⟨T, hTdef⟩ : ∃ T : Ω → ℝ≥0∞, T = fun ω => min (instrTime spec n) (E n ω).2 := ⟨_, rfl⟩
  have hTm : Measurable T := hTdef ▸ measurable_const.min (measurable_snd.comp (hEm n))
  have hTop : MeasurableSet {ω | T ω = ⊤} := hTm (measurableSet_singleton ⊤)
  have hBm : ∀ t, Measurable (launchDrv κ b jumps spec E M n t) :=
    GW2Later.measurable_regDrv (hM.inter (hRM n).1) _ (hEm n)
  have hBc : ∀ ω, Continuous fun t => launchDrv κ b jumps spec E M n t ω := continuous_launchDrv hreg hMreg n
  have hB0 : ∀ ω, launchDrv κ b jumps spec E M n 0 ω = 0 := launchDrv_zero hreg n
  obtain ⟨V, hVdef⟩ : ∃ V : Ω → ℂ, V = fun ω =>
      fwdMapInv (fun x : ℝ => launchDrv κ b jumps spec E M n x.toNNReal ω) ((T ω).toNNReal : ℝ) (Z ω) :=
    ⟨_, rfl⟩
  have hVm : Measurable V := hVdef ▸
    measurable_fwdMapInv_randomTime hBm hBc hB0 (ENNReal.measurable_toNNReal.comp hTm) hZ hZH
  have hVH : ∀ ω, V ω ∈ H := fun ω => by
    rw [hVdef]
    exact QuantumZipper.RS.fwdMapInv_mem_H ((hBc ω).comp continuous_real_toNNReal) (by simpa using hB0 ω)
      (NNReal.coe_nonneg _) (hZH ω)
  obtain ⟨a, hadef⟩ : ∃ a : Ω → ℝ, a = fun ω => ((ExplState.run κ b jumps spec (fun i => E i ω) n).2.2.2.2.1.1 0 -
      (ExplState.run κ b jumps spec (fun i => E i ω) (n + 1)).2.2.2.2.1.1 0).re := ⟨_, rfl⟩
  have ham : Measurable a := hadef ▸ Complex.measurable_re.comp (((hRM n).2 0).sub ((hRM (n + 1)).2 0))
  refine ⟨fun ω => if ω ∈ L then (if T ω = ⊤ then Z ω else V ω) else Z ω + (a ω : ℂ),
    Measurable.ite hL (Measurable.ite hTop hZ hVm) (hZ.add (Complex.measurable_ofReal.comp ham)),
    fun ω => ?_, fun ω hω => ?_⟩
  · dsimp only
    split_ifs
    · exact hZH ω
    · exact hVH ω
    · have h0 : 0 < (Z ω).im := hZH ω
      show 0 < (Z ω + (a ω : ℂ)).im
      simpa using h0
  · rcases hl : (ExplState.run κ b jumps spec (fun i => E i ω) (n + 1)).2.2.2.1 n with _ | ⟨c, θ⟩
    · have hnL : ω ∉ L := by rw [hLdef]; simp [hl]
      obtain ⟨a', ha'⟩ := chart_run_succ_of_noLaunch (κ := κ) (b := b) (jumps := jumps) spec
        (fun i => E i ω) hl
      have haa : a ω = a' := by
        rw [hadef]
        simp only [ha', Chart.recenter]
        simp
      simp only [hnL, ↓reduceIte, haa]
      rw [ha']
      rfl
    · have hLω : ω ∈ L := by rw [hLdef]; simp [hl]
      have hne : (ExplState.run κ b jumps spec (fun i => E i ω) (n + 1)).2.2.2.1 n ≠ none := by
        rw [hl]; exact Option.some_ne_none _
      obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec (fun i => E i ω) hl
      by_cases hT : T ω = ⊤
      · simp only [hLω, hT, ↓reduceIte]
        rw [he, GW1P.chart_launch_of_top _ _ _ _ _ (by rw [hTdef] at hT; exact hT)]
      · simp only [hLω, hT, ↓reduceIte]
        have hT' : min (instrTime spec n) (E n ω).2 ≠ ⊤ := by rw [hTdef] at hT; exact hT
        have hfun : (fun x : ℝ => launchDrv κ b jumps spec E M n x.toNNReal ω) =
            fun x : ℝ => (E n ω).1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (instrTime spec n) (E n ω).2)).toNNReal :=
          funext fun x => launchDrv_eq hreg hω hne x.toNNReal
        rw [he, chart_launch _ _ _ _ _ hT', hVdef, hTdef]
        simp only [hfun]
        rfl

/-- **The inverse chart of a run, at a measurable point of `ℍ`, is measurable on an event of regular pieces.** For
measurable drivers that are regular at every sample, and a measurable event `M` on which every launched piece has
regular data (`GW1P.PieceRegular`), the inverse chart after `n` instructions at a measurable point `Z ω ∈ ℍ` agrees
on `M` with a measurable function. -/
theorem exists_measurable_runChart_inv (hb : IsPiecewiseConstantBoundaryData b jumps) (spec : ExplSpec)
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {M : Set Ω} (hM : MeasurableSet M)
    (hMreg : ∀ ω ∈ M, ∀ (j : ℕ) (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = some (c, θ) →
      GW1P.PieceRegular (E j ω).1 (min (instrTime spec j) (E j ω).2)) (n : ℕ) :
    ∀ {Z : Ω → ℂ}, Measurable Z → (∀ ω, Z ω ∈ H) →
      ∃ Y : Ω → ℂ, Measurable Y ∧
        ∀ ω ∈ M, (ExplState.run κ b jumps spec (fun i => E i ω) n).2.2.2.2.1.2.1 (Z ω) = Y ω := by
  induction n with
  | zero =>
    intro Z hZ _
    refine ⟨fun ω => Z ω + (spec.1 : ℂ), hZ.add_const _, fun ω _ => ?_⟩
    simp [ExplState.run, ExplState.init, Chart.recenter, Chart.id]
  | succ n ih =>
    intro Z hZ hZH
    obtain ⟨Z', hZ'm, hZ'H, hZ'⟩ := exists_runChart_inv_succ hb spec hEm hreg hM hMreg n hZ hZH
    obtain ⟨Y, hYm, hY⟩ := ih hZ'm hZ'H
    exact ⟨Y, hYm, fun ω hω => (hZ' ω hω).trans (hY ω hω)⟩

end RunInv

/-! ### Avoidance through countably many tip points -/

section TipPoints

/-- The times `m / (N + 1)`. -/
def qTime (m N : ℕ) : ℝ≥0 := (m : ℝ≥0) / ((N : ℝ≥0) + 1)

/-- Every time is a limit from below of times `m / (N + 1)`. -/
theorem exists_qTime_tendsto (t : ℝ≥0) :
    ∃ m : ℕ → ℕ, (∀ N, qTime (m N) N ≤ t) ∧ Tendsto (fun N => qTime (m N) N) atTop (𝓝 t) := by
  refine ⟨fun N => ⌊(t : ℝ) * ((N : ℝ) + 1)⌋₊, fun N => ?_, ?_⟩
  · rw [← NNReal.coe_le_coe]
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    simp only [qTime, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_add, NNReal.coe_one]
    rw [div_le_iff₀ hN]
    exact Nat.floor_le (by positivity)
  · rw [← NNReal.tendsto_coe]
    have h := (tendsto_nat_floor_mul_div_atTop (R := ℝ) t.coe_nonneg).comp
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    refine h.congr fun N => ?_
    simp [qTime, Function.comp]

/-- A limit point lies in an open set iff the sequence eventually keeps a fixed distance from its complement. -/
theorem mem_open_iff_eventually_infDist {U : Set ℂ} (hU : IsOpen U) (hne : Uᶜ.Nonempty) {g : ℕ → ℂ} {z : ℂ}
    (hg : Tendsto g atTop (𝓝 z)) :
    z ∈ U ↔ ∃ p : ℕ, ∀ᶠ n in atTop, 1 / ((p : ℝ) + 1) ≤ infDist (g n) Uᶜ := by
  have hcl : IsClosed Uᶜ := hU.isClosed_compl
  have hd : Tendsto (fun n => infDist (g n) Uᶜ) atTop (𝓝 (infDist z Uᶜ)) :=
    (continuous_infDist_pt Uᶜ).continuousAt.tendsto.comp hg
  constructor
  · intro hz
    have hpos : 0 < infDist z Uᶜ := by
      rw [← infDist_pos_iff_notMem_closure hne, hcl.closure_eq]
      exact fun h => h hz
    obtain ⟨p, hp⟩ := exists_nat_one_div_lt hpos
    exact ⟨p, (hd.eventually (lt_mem_nhds hp)).mono fun _ h => h.le⟩
  · rintro ⟨p, hp⟩
    have hle : 1 / ((p : ℝ) + 1) ≤ infDist z Uᶜ := ge_of_tendsto hd hp
    have hpos : 0 < infDist z Uᶜ := lt_of_lt_of_le (by positivity) hle
    rw [← infDist_pos_iff_notMem_closure hne, hcl.closure_eq] at hpos
    exact not_not.1 hpos

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec)

/-- The approximating point, at height `1 / (n + 1)`, of the tip at own time `τ` of the piece launched by instruction
`j`, read in the physical domain through the chart of the run before that instruction. -/
def tipApprox (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (j : ℕ) (τ : ℝ≥0) (n : ℕ) : ℂ :=
  (ExplState.run κ b jumps spec D j).2.2.2.2.1.2.1
    (fwdMapInv (fun r : ℝ => (D j).1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (min (instrTime spec j) (D j).2)).toNNReal)
      (τ : ℝ) (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I))

/-- The countable avoidance condition for the piece of instruction `j`. -/
def PieceAvoids (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (U : Set ℂ) (j : ℕ) : Prop :=
  ∀ m N : ℕ, (qTime m N : ℝ≥0∞) ≤ min (instrTime spec j) (D j).2 →
    ∀ p : ℕ, ¬ ∀ᶠ n in atTop, 1 / ((p : ℝ) + 1) ≤ infDist (tipApprox κ b jumps spec D j (qTime m N) n) Uᶜ

variable {κ b jumps spec}

/-- **The piece of a launching instruction avoids an open `U ⊆ ℍ` iff the countable condition holds** (regular
pieces: the physical path `f ∘ α` is continuous on `[0, S]`). -/
theorem disjoint_pieceSet_iff {Ω : Type*} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω}
    (hD : ∀ (j : ℕ) (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = some (c, θ) →
      GW1P.PieceRegular (E j ω).1 (min (instrTime spec j) (E j ω).2))
    {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) {j : ℕ}
    (hl : (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j ≠ none) :
    Disjoint (pieceSet κ b jumps spec E j ω) U ↔ PieceAvoids κ b jumps spec (fun i => E i ω) U j := by
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 hl
  have hpr := hD j x.1 x.2 (by rw [hx])
  obtain ⟨f, C, hf, -⟩ := (GW1P.isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) spec
    (fun i => E i ω) hD j).1
  set S : ℝ≥0∞ := min (instrTime spec j) (E j ω).2 with hS
  obtain ⟨hW0, hWc, α, hα, -⟩ := hpr
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα (hWc.mono fun _ (hs : _ < S) => (le_of_lt hs : _ ≤ S)) hW0 ht
  have hpiece : pieceSet κ b jumps spec E j ω = (f '' (α '' {t | (t : ℝ≥0∞) ≤ S})) ∩ H := by
    simp only [pieceSet, hl, ↓reduceIte]
    rw [← hS, CounterflowRange.tipSet_stopped_eq_of_tendsto hα hWc hW0 fun t ht => hf _ (hαH t ht)]
  -- the approximants converge to the physical tip points
  have hy : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))⟩
  have htend : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S →
      Tendsto (fun n => tipApprox κ b jumps spec (fun i => E i ω) j t n) atTop (𝓝 (f (α t))) := fun t ht =>
    (CounterflowRange.tendsto_tip_stopped_of_tendsto hα hWc hW0 ht (hf _ (hαH t ht))).comp hy
  have hFc : ContinuousOn (fun t => f (α t)) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S} :=
    (GW1P.continuousOn_of_tendsto hf).comp hα.2.1 fun t ht => hαH t ht
  have hne : Uᶜ.Nonempty := ⟨0, fun h => absurd (hUH h) (by simp [QuantumZipper.H])⟩
  have hdisj : Disjoint ((f '' (α '' {t | (t : ℝ≥0∞) ≤ S})) ∩ H) U ↔
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → f (α t) ∉ U := by
    constructor
    · intro hd t ht hU'
      exact Set.disjoint_left.1 hd ⟨⟨α t, ⟨t, ht, rfl⟩, rfl⟩, hUH hU'⟩ hU'
    · intro h
      refine Set.disjoint_left.2 ?_
      rintro _ ⟨⟨_, ⟨t, ht, rfl⟩, rfl⟩, -⟩
      exact h t ht
  rw [hpiece, hdisj]
  constructor
  · intro h m N hmN p hev
    exact h _ hmN ((mem_open_iff_eventually_infDist hU hne (htend _ hmN)).2 ⟨p, hev⟩)
  · intro h t ht hmem
    obtain ⟨m, hm, hmt⟩ := exists_qTime_tendsto t
    have hmS : ∀ N, (qTime (m N) N : ℝ≥0∞) ≤ S := fun N => (ENNReal.coe_le_coe.2 (hm N)).trans ht
    have hcw : Tendsto (fun N => f (α (qTime (m N) N))) atTop (𝓝 (f (α t))) :=
      (hFc t ht).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hmt, Eventually.of_forall hmS⟩)
    obtain ⟨N, hN⟩ := (hcw.eventually (hU.mem_nhds hmem)).exists
    obtain ⟨p, hp⟩ := (mem_open_iff_eventually_infDist hU hne (htend _ (hmS N))).1 hN
    exact h (m N) N (hmS N) p hp

/-- **The explored set avoids an open `U ⊆ ℍ` iff every launched piece satisfies the countable condition.** -/
theorem disjoint_stageSet_iff {Ω : Type*} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω}
    (hD : ∀ (j : ℕ) (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = some (c, θ) →
      GW1P.PieceRegular (E j ω).1 (min (instrTime spec j) (E j ω).2))
    {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) (k : ℕ) :
    Disjoint (stageSet κ b jumps spec E k ω) U ↔ ∀ j < k,
      (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j ≠ none →
        PieceAvoids κ b jumps spec (fun i => E i ω) U j := by
  induction k with
  | zero => simp [stageSet_zero]
  | succ k ih =>
    rw [stageSet_succ, Set.disjoint_union_left, ih]
    by_cases hl : (ExplState.run κ b jumps spec (fun i => E i ω) (k + 1)).2.2.2.1 k = none
    · have he : pieceSet κ b jumps spec E k ω = ∅ := by simp only [pieceSet, hl, ↓reduceIte]
      rw [he]
      simp only [Set.empty_disjoint, and_true]
      constructor
      · intro h j hj hlj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact h j hj hlj
        · exact absurd hl hlj
      · exact fun h j hj => h j (Nat.lt_succ_of_lt hj)
    · rw [disjoint_pieceSet_iff hD hU hUH hl]
      constructor
      · rintro ⟨h, hk⟩ j hj hlj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact h j hj hlj
        · exact hk
      · exact fun h => ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h k (Nat.lt_succ_self k) hl⟩

end TipPoints

/-! ### Events of the past up to null sets -/

section Frozen

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **A null-measurable event frozen under the regular conditional laws given `𝒢` is an event of `𝒢` up to null
sets.** If `E` agrees with a measurable `S` on a measurable conull `M`, and for almost every `ω₀`, under the regular
conditional law given `𝒢` at `ω₀`, almost surely `ω ∈ E ↔ ω₀ ∈ E`, then `E` is in `aeSigma 𝒢 P`. -/
theorem mem_aeSigma_of_frozen (h𝒢 : 𝒢 ≤ mΩ) {E S M : Set Ω} (hS : MeasurableSet S)
    (hMP : ∀ᵐ ω ∂P, ω ∈ M) (hEM : ∀ ω ∈ M, ω ∈ E ↔ ω ∈ S)
    (hfr : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ E ↔ ω₀ ∈ E) :
    MeasurableSet[aeSigma 𝒢 P] E := by
  refine ⟨{ω₀ | condExpKernel P 𝒢 ω₀ S = 1}, ?_, ?_⟩
  · exact (Kernel.measurable_coe (condExpKernel P 𝒢) hS) (measurableSet_singleton 1)
  · have hMk := KernelTower.ae_ae_condExpKernel_of_ae (P := P) h𝒢 hMP
    filter_upwards [hfr, hMk, hMP] with ω₀ hfrω hMω hω₀
    have hiff : ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ S ↔ ω₀ ∈ E := by
      filter_upwards [hfrω, hMω] with ω h1 h2
      exact (hEM ω h2).symm.trans h1
    show (ω₀ ∈ E) = (condExpKernel P 𝒢 ω₀ S = 1)
    refine propext ⟨fun hE => ?_, fun h1 => ?_⟩
    · have hae : ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ S := hiff.mono fun ω h => h.2 hE
      rw [← prob_compl_eq_zero_iff hS]
      exact ae_iff.1 hae
    · by_contra hE
      have hae : ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∉ S := hiff.mono fun ω h hS' => hE (h.1 hS')
      have h0 : condExpKernel P 𝒢 ω₀ S = 0 := by
        rw [ae_iff] at hae
        simpa using hae
      rw [h0] at h1
      exact zero_ne_one h1

end Frozen

/-! ### The explored set is recorded by the past, up to null sets -/

section Avoid

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **The approximating tip points are measurable on an event of regular pieces.** -/
theorem exists_measurable_tipApprox (hb : IsPiecewiseConstantBoundaryData b jumps) (spec : ExplSpec)
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {M : Set Ω} (hM : MeasurableSet M)
    (hMreg : ∀ ω ∈ M, ∀ (j : ℕ) (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = some (c, θ) →
      GW1P.PieceRegular (E j ω).1 (min (instrTime spec j) (E j ω).2)) (j : ℕ) (τ : ℝ≥0) (n : ℕ) :
    ∃ Y : Ω → ℂ, Measurable Y ∧ ∀ ω ∈ M,
      (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j ≠ none →
        tipApprox κ b jumps spec (fun i => E i ω) j τ n = Y ω := by
  have hpt : (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) ∈ H := by
    show 0 < ((((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I)).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re,
      mul_zero, add_zero]
    positivity
  have hBm : ∀ t, Measurable (launchDrv κ b jumps spec E M j t) :=
    GW2Later.measurable_regDrv (hM.inter ((runMeasStatement κ b jumps hb spec E hEm hreg) j).1) _ (hEm j)
  have hBc : ∀ ω, Continuous fun t => launchDrv κ b jumps spec E M j t ω := continuous_launchDrv hreg hMreg j
  have hB0 : ∀ ω, launchDrv κ b jumps spec E M j 0 ω = 0 := launchDrv_zero hreg j
  have hZm : Measurable fun ω => fwdMapInv (fun x : ℝ => launchDrv κ b jumps spec E M j x.toNNReal ω) (τ : ℝ)
      (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) :=
    GW2Later.measurable_fwdMapInv_of_continuous hBm hBc hB0 τ.coe_nonneg measurable_const fun _ => hpt
  have hZH : ∀ ω, fwdMapInv (fun x : ℝ => launchDrv κ b jumps spec E M j x.toNNReal ω) (τ : ℝ)
      (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) ∈ H := fun ω =>
    QuantumZipper.RS.fwdMapInv_mem_H ((hBc ω).comp continuous_real_toNNReal) (by simpa using hB0 ω)
      τ.coe_nonneg hpt
  obtain ⟨Y, hYm, hY⟩ := exists_measurable_runChart_inv hb spec hEm hreg hM hMreg j hZm hZH
  refine ⟨Y, hYm, fun ω hω hl => ?_⟩
  rw [← hY ω hω]
  have hfun : (fun x : ℝ => launchDrv κ b jumps spec E M j x.toNNReal ω) =
      fun r : ℝ => (E j ω).1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (min (instrTime spec j) (E j ω).2)).toNNReal :=
    funext fun x => launchDrv_eq hreg hω hl x.toNNReal
  simp only [tipApprox, hfun]

variable [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The avoidance events of the explored set are events of the retained past up to null sets** (ruling R58; Part
D.5). For a staged family with measurable drivers that are regular at every sample, whose launched pieces are almost
surely regular (`StagedPiecesRegular`), and whose retained pasts are events of `Ω`, the event that the explored set
after `k` instructions avoids an open `U ⊆ ℍ` lies in the null completion `aeSigma (pastSigma k) P`. -/
theorem measurableSet_aeSigma_stageSet_avoid (hb : IsPiecewiseConstantBoundaryData b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hR : StagedPiecesRegular κ b jumps P spec E) (hle : ∀ k, pastSigma κ b jumps spec E k ≤ mΩ) (k : ℕ)
    {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) :
    MeasurableSet[aeSigma (pastSigma κ b jumps spec E k) P] {ω | Disjoint (stageSet κ b jumps spec E k ω) U} := by
  classical
  -- a measurable conull event of regular pieces
  set Good : Set Ω := {ω | ∀ (j : ℕ) (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = some (c, θ) →
      GW1P.PieceRegular (E j ω).1 (min (instrTime spec j) (E j ω).2)} with hGood
  set M : Set Ω := (toMeasurable P Goodᶜ)ᶜ with hMdef
  have hM : MeasurableSet M := (measurableSet_toMeasurable P _).compl
  have hMG : ∀ ω ∈ M, ω ∈ Good := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable P _ h)
  have hMP : ∀ᵐ ω ∂P, ω ∈ M := by
    rw [ae_iff]
    have e : {a | ¬ a ∈ M} = toMeasurable P Goodᶜ := by ext ω; simp [hMdef]
    rw [e, measure_toMeasurable]
    exact ae_iff.1 hR.ae_pieceRegular
  have hMreg : ∀ ω ∈ M, ∀ (j : ℕ) (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = some (c, θ) →
      GW1P.PieceRegular (E j ω).1 (min (instrTime spec j) (E j ω).2) := fun ω hω => hMG ω hω
  have hRM := runMeasStatement κ b jumps hb spec E hEm hreg
  -- measurable versions of the approximating tip points
  choose Y hYm hY using fun (j m N n : ℕ) =>
    exists_measurable_tipApprox hb spec hEm hreg hM hMreg j (qTime m N) n
  set S : Set Ω := {ω | ∀ j : ℕ, j < k →
      (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j ≠ none →
      ∀ m N : ℕ, (qTime m N : ℝ≥0∞) ≤ min (instrTime spec j) (E j ω).2 →
        ∀ p : ℕ, ¬ ∃ n₀ : ℕ, ∀ n ≥ n₀, 1 / ((p : ℝ) + 1) ≤ infDist (Y j m N n ω) Uᶜ} with hSdef
  have hSm : MeasurableSet S := by
    refine measurableSet_setOfPred.2 (Measurable.forall fun j => Measurable.imp measurable_const <|
      Measurable.imp (measurableSet_setOfPred.1 (hRM j).1) <| Measurable.forall fun m => Measurable.forall fun N =>
        Measurable.imp ?_ <| Measurable.forall fun p => Measurable.not <| Measurable.exists fun n₀ =>
          Measurable.forall fun n => Measurable.imp measurable_const ?_)
    · exact measurableSet_setOfPred.1
        (measurableSet_le measurable_const (measurable_const.min (measurable_snd.comp (hEm j))))
    · exact measurableSet_setOfPred.1
        (measurableSet_le measurable_const ((continuous_infDist_pt _).measurable.comp (hYm j m N n)))
  refine mem_aeSigma_of_frozen (hle k) hSm hMP (fun ω hω => ?_) ?_
  · show Disjoint (stageSet κ b jumps spec E k ω) U ↔ ω ∈ S
    rw [disjoint_stageSet_iff (hMreg ω hω) hU hUH k]
    simp only [hSdef, Set.mem_ofPred_eq, PieceAvoids, Filter.eventually_atTop]
    refine forall_congr' fun j => imp_congr_right fun _ => imp_congr_right fun hl =>
      forall_congr' fun m => forall_congr' fun N => imp_congr_right fun _ => forall_congr' fun p => ?_
    simp only [hY j m N _ ω hω hl]
  · filter_upwards [CondDriverBridge.ae_ae_run_eq_of_le (P := P) (κ := κ) (b := b) (jumps := jumps) spec
      (fun j _ ω => hreg j ω) (hle k) le_rfl] with ω₀ hω₀
    filter_upwards [hω₀] with ω hω
    simp only [stageSet, hω]

end Avoid

/-! ### The R58 form of the stage input for the boundary walks -/

/-- **`WalkStageAvoidMeasStatement` up to null sets (ruling R58).** For the setting of `WalkMarkedLocalRegStatement`
(drivers regular at every sample), every instruction count `k` and open `U ⊆ ℍ`, the avoidance event of the explored
set of the walk `w = boundaryWalkSpec b jumps θ right` after `k` instructions is an event of `pastSigma k` up to
`P`-null sets. -/
def WalkStageAvoidMeasAEStatement (θ : ℝ) (right : Bool) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
    ∀ (k : ℕ) (U : Opens ℂ), (U : Set ℂ) ⊆ H →
      MeasurableSet[aeSigma (pastSigma κ b jumps (boundaryWalkSpec b jumps θ right)
          (E (boundaryWalkSpec b jumps θ right)) k) P]
        {ω | Disjoint (stageSet κ b jumps (boundaryWalkSpec b jumps θ right)
          (E (boundaryWalkSpec b jumps θ right)) k ω) U}

/-- **The R58 stage input holds for every boundary walk with an angle in `[−π/2, π/2]`.** -/
theorem walkStageAvoidMeasAEStatement {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (right : Bool) :
    WalkStageAvoidMeasAEStatement.{u} θ right := by
  intro κ _ _ b jumps hb Ω _ _ P _ h _ E hE hR hreg k U hUH
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ right
  exact measurableSet_aeSigma_stageSet_avoid hb (hE _ hw).1 (fun j ω => hreg _ j ω) (hR _ hw) (hE _ hw).2.1 k
    U.isOpen hUH

/-- The right walk. -/
theorem walkStageAvoidMeasAEStatement_right : WalkStageAvoidMeasAEStatement.{u} (-(Real.pi / 2)) true :=
  walkStageAvoidMeasAEStatement ⟨le_rfl, by linarith [Real.pi_pos]⟩ true

/-- The left walk. -/
theorem walkStageAvoidMeasAEStatement_left : WalkStageAvoidMeasAEStatement.{u} (Real.pi / 2) false :=
  walkStageAvoidMeasAEStatement ⟨by linarith [Real.pi_pos], le_rfl⟩ false

end WalkLaw

end Theorem14

end InteractingSLE
