/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartExit
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# The counterflow in its restart chart, from the frozen trace: clock, chart path and continuation

Packet PROVE-SEC5-G (item (ii)(a) of `planning/handoffs/PROVE-SEC5-F.md`, "What remains" 1). The coordinate change
`CrossRestartTrace.exists_loewner_restartMap_trace` is stated for `ℝ`-indexed drivers continuous on `ℝ` and traces
`γ : ℝ → ℂ` on a horizon `[0, T]`. The counterflow of the carrier `Sec5.CounterflowSegmentRestartStatement` is given
by the frozen `ℝ≥0`-indexed `IsGeneratingTrace w′ ζ′ γ′`, with a driver continuous only before its lifetime. This
file passes between the two (through `TraceBridge.frozenDrive`, the driver frozen after a time before `ζ′`, and the
congruence `TraceBridge.fwdHull_eq_of_eqOn`) and assembles, before the exit time `T` of the counterflow from the
remaining domain:

* the **chart capacity clock** `restartClock t = hcap(Φ(K′_t))/2` (`Φ = restartMap q U σ x₁`), which equals the clock
  of `exists_loewner_restartMap` on every horizon (`hcap(K̃_s) = 2s`), hence is `0` at `0`, continuous and strictly
  increasing before `T`;
* the **chart path** `restartPath t = Φ(γ′ t)` (`0` at `t = 0`), continuous before `T`;
* the chart path in chart capacity time, `restartChartPath = restartPath ∘ a⁻¹`.

The exit time `T` is any time before which the counterflow is **alive in the restart chart** (`IsRestartAlive`): its
hulls in the chart `M_q` stay away from `−1` (the strip end `+∞`), their `E`-images stay away from the segment hull
and the counterflow start, their `g_A`-images stay away from the tip image `U_σ`, and the trace stays in `ℍ`.

**Main result** (`IsRestartData.isCounterflowChartContinuation`): if moreover the chart capacity is exhausted before
`T` (the counterflow leaves the remaining domain through the tip), the counterflow restart holds pathwise,
`IsCounterflowChartContinuation A (η σ) ξ Q (restartChartPath …) ∞`, with the inverse chart `restartInv`, and the
chart path in capacity time is continuous.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE

namespace Sec5

namespace CrossRestart

open ConformalImage ConformalImageFull

/-! ### Definitions -/

/-- The counterflow hull at time `t` (driver `w′` read on `ℝ`). -/
abbrev cfHull (w' : ℝ≥0 → ℝ) (t : ℝ) : Set ℂ := QuantumZipper.fwdHull (fun s : ℝ => w' s.toNNReal) t

/-- **The chart capacity clock**: half the capacity of the restart-chart image of the counterflow hull. -/
def restartClock (q : ℝ) (U : ℝ → ℝ) (σ x₁ : ℝ) (w' : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  hcapSet (restartMap q U σ x₁ '' cfHull w' t) / 2

/-- **The chart path in counterflow time**: `Φ(γ′ t)`, and the start `0` at `t = 0`. -/
def restartPath (q : ℝ) (U : ℝ → ℝ) (σ x₁ : ℝ) (γ' : ℝ≥0 → ℂ) (t : ℝ≥0) : ℂ :=
  open scoped Classical in if t = 0 then 0 else restartMap q U σ x₁ (γ' t)

/-- **The chart path in chart capacity time**: `restartPath ∘ a⁻¹`. -/
def restartChartPath (q : ℝ) (U : ℝ → ℝ) (σ x₁ : ℝ) (w' : ℝ≥0 → ℝ) (γ' : ℝ≥0 → ℂ) (T : ℝ≥0∞)
    (u : ℝ≥0) : ℂ :=
  restartPath q U σ x₁ γ' (clockInv (restartClock q U σ x₁ w') T u)

/-- **The counterflow is alive in the restart chart at time `T`** (the hypotheses of
`exists_loewner_restartMap_trace` at the horizon `T`). -/
structure IsRestartAlive (q : ℝ) (U : ℝ → ℝ) (σ : ℝ) (w' : ℝ≥0 → ℝ) (γ' : ℝ≥0 → ℂ) (T : ℝ≥0) : Prop where
  far₁ : ∃ r > 0, Disjoint (ball (-1 : ℂ) r) (cfHull w' T)
  far₂ : Disjoint (closure (QuantumZipper.fwdHull U σ))
    (insert ((-1 - q : ℝ) : ℂ) (closure (realMobius 0 (-(1 + q)) 1 1 '' cfHull w' T)))
  far₃ : ∃ r > 0, Disjoint (ball (U σ : ℂ) r) (gmap U σ '' (realMobius 0 (-(1 + q)) 1 1 '' cfHull w' T))
  mem : ∀ t : ℝ≥0, 0 < t → t ≤ T → γ' t ∈ H

/-- **The deterministic data of the counterflow restart** before the exit time `T`: the segment hull `K^U_σ`
(continuous `U`, `U 0 = 0`), the boundary value `x₁ = g_A(−1 − q)`, the counterflow (frozen generating trace `γ′` of
`w′`, `w′` continuous before `ζ′`, `w′ 0 = 0`), and `0 < T ≤ ζ′` with the counterflow alive at every time before
`T`. -/
structure IsRestartData (q : ℝ) (U : ℝ → ℝ) (σ x₁ : ℝ) (w' : ℝ≥0 → ℝ) (ζ' : ℝ≥0∞) (γ' : ℝ≥0 → ℂ)
    (T : ℝ≥0∞) : Prop where
  q_pos : 0 < q
  U_cont : Continuous U
  U_zero : U 0 = 0
  σ_nonneg : 0 ≤ σ
  x₁_eq : (x₁ : ℂ) = bdryVal U (-1 - q) σ
  trace : IsGeneratingTrace w' ζ' γ'
  drv_cont : ContinuousOn w' {t | (t : ℝ≥0∞) < ζ'}
  drv_zero : w' 0 = 0
  exit_le : T ≤ ζ'
  exit_pos : 0 < T
  alive : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → IsRestartAlive q U σ w' γ' t

namespace IsRestartData

variable {q : ℝ} {U : ℝ → ℝ} {σ x₁ : ℝ} {w' : ℝ≥0 → ℝ} {ζ' : ℝ≥0∞} {γ' : ℝ≥0 → ℂ} {T : ℝ≥0∞}
  (hd : IsRestartData q U σ x₁ w' ζ' γ' T)
include hd

/-- The counterflow start `E(z₀) = −1 − q` is off the closed segment hull. -/
theorem notMem_closure_start : ((-1 - q : ℝ) : ℂ) ∉ closure (QuantumZipper.fwdHull U σ) := fun h =>
  Set.disjoint_left.1 (hd.alive 0 (by simpa using hd.exit_pos)).far₂ h (mem_insert _ _)

/-- `x₁ < U_σ`: the image of the counterflow start lies left of the tip image. -/
theorem x₁_lt : x₁ < U σ := by
  obtain ⟨r', hr', hr'd⟩ := Metric.mem_nhds_iff.1 (isOpen_compl_iff.2 isClosed_closure
    |>.mem_nhds hd.notMem_closure_start)
  have hball : Disjoint (ball ((-1 - q : ℝ) : ℂ) r') (QuantumZipper.fwdHull U σ) :=
    Set.disjoint_left.2 fun z hz hzA => hr'd hz (subset_closure hzA)
  have := bdryVal_re_lt hd.U_cont hd.U_zero hd.σ_nonneg hr' hball (by linarith [hd.q_pos])
  have hre : (bdryVal U (-1 - q) σ).re = x₁ := by rw [← hd.x₁_eq]; simp
  linarith

/-- **The restart on a horizon `t₀ < T`**: the clock of `exists_loewner_restartMap_trace` agrees with the chart
capacity clock on `[0, t₀]`, and the chart path is continuous on `(0, t₀]` with limit `0` at `0⁺`. -/
theorem exists_on {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < T) :
    ∃ τ : ℝ → ℝ, τ 0 = 0 ∧ StrictMonoOn τ (Icc 0 (t₀ : ℝ)) ∧ ContinuousOn τ (Icc 0 (t₀ : ℝ)) ∧
      (∀ t : ℝ≥0, t ≤ t₀ → restartClock q U σ x₁ w' t = τ t) ∧
      ContinuousOn (fun t : ℝ => restartMap q U σ x₁ (γ' t.toNNReal)) (Ioc 0 (t₀ : ℝ)) ∧
      Tendsto (fun t : ℝ => restartMap q U σ x₁ (γ' t.toNNReal)) (𝓝[Ioc 0 (t₀ : ℝ)] 0) (𝓝 0) := by
  obtain ⟨t₂, ht₀t₂, ht₂T⟩ := exists_real_btwn_of_lt ht₀
  have ht₂ζ : ENNReal.ofReal t₂ < ζ' := lt_of_lt_of_le ht₂T hd.exit_le
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg t₀).trans ht₀t₂.le
  set W : ℝ → ℝ := frozenDrive w' t₂ with hWdef
  have hW : Continuous W := continuous_frozenDrive_of_lt hd.drv_cont ht₂ζ
  have hW0 : W 0 = 0 := by rw [hWdef, frozenDrive_zero ht₂, hd.drv_zero]
  have hK : ∀ t : ℝ, 0 ≤ t → t ≤ t₀ → QuantumZipper.fwdHull W t = cfHull w' t := fun t ht htt₀ =>
    fwdHull_eq_of_eqOn ht (lt_of_le_of_lt htt₀ ht₀t₂) fun r hr => frozenDrive_eq hr
  have hal := hd.alive t₀ ht₀
  obtain ⟨r, hr, hd1⟩ := hal.far₁
  obtain ⟨r₃, hr₃, hd3⟩ := hal.far₃
  rw [← hK t₀ t₀.2 le_rfl] at hd1 hd3
  have hd2 := hal.far₂
  rw [← hK t₀ t₀.2 le_rfl] at hd2
  -- the trace read on `ℝ`
  have hγc : ContinuousOn (fun s : ℝ => γ' s.toNNReal) (Icc 0 (t₀ : ℝ)) := by
    refine hd.trace.2.1.comp continuous_real_toNNReal.continuousOn fun s hs => ?_
    show ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζ'
    refine le_trans (ENNReal.coe_le_coe.2 ?_) (ht₀.le.trans hd.exit_le)
    exact Real.toNNReal_le_iff_le_coe.2 hs.2
  have hγH : ∀ t ∈ Ioc (0 : ℝ) t₀, γ' t.toNNReal ∈ H := fun t ht =>
    hal.mem _ (Real.toNNReal_pos.2 ht.1) (Real.toNNReal_le_iff_le_coe.2 ht.2)
  have hγK : ∀ t ∈ Ioc (0 : ℝ) t₀, IsFilling (QuantumZipper.fwdHull W t)
      ((fun s : ℝ => γ' s.toNNReal) '' Icc 0 t) := by
    intro t ht
    have htT : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ' := by
      refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 ht.2))
        (lt_of_lt_of_le ht₀ hd.exit_le)
    have hfill := hd.trace.2.2 t.toNNReal htT
    rw [Real.coe_toNNReal _ ht.1.le] at hfill
    rw [hK t ht.1.le ht.2, image_toNNReal_Icc γ' ht.1.le]
    exact hfill
  have hγ0 : (fun s : ℝ => γ' s.toNNReal) 0 = 0 := by simpa using hd.trace.1
  obtain ⟨τ, W', hW'c, hW'0, hτ0, hτm, hτc, hKτ, -, hcont, hlim⟩ :=
    exists_loewner_restartMap_trace hW hW0 t₀.2 hd.q_pos hr hd1 hd.U_cont hd.U_zero hd.σ_nonneg hd2
      hd.x₁_eq hr₃ hd3 hγ0 hγc hγH hγK
  refine ⟨τ, hτ0, hτm, hτc, fun t htt₀ => ?_, hcont, hlim⟩
  have htI : (t : ℝ) ∈ Icc (0 : ℝ) t₀ := ⟨t.2, htt₀⟩
  have hτnn : 0 ≤ τ t := by
    rw [← hτ0]; exact hτm.monotoneOn ⟨le_rfl, t₀.2⟩ htI htI.1
  rw [restartClock, ← hK t t.2 htt₀, ← hKτ t htI, hcapSet_eq (isHPHull_fwdHull hW'c hτnn),
    hcap_fwdHull hW'c hW'0 hτnn]
  ring

/-- **The chart capacity clock is an exhausting clock** before `T`, once the chart capacity is unbounded there. -/
theorem isExhaustingClock (hexh : ∀ u : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < T ∧ u ≤ restartClock q U σ x₁ w' t) :
    IsExhaustingClock (restartClock q U σ x₁ w') T := by
  refine ⟨hd.exit_pos, ?_, ?_, ?_, hexh⟩
  · obtain ⟨τ, hτ0, -, -, hτ, -⟩ := hd.exists_on (t₀ := 0) (by simpa using hd.exit_pos)
    rw [hτ 0 le_rfl]; simpa using hτ0
  · intro t ht t' ht' htt'
    obtain ⟨τ, -, hτm, -, hτ, -⟩ := hd.exists_on ht'
    rw [hτ t htt'.le, hτ t' le_rfl]
    exact hτm ⟨t.2, by exact_mod_cast htt'.le⟩ ⟨t'.2, le_rfl⟩ (by exact_mod_cast htt')
  · intro t ht
    obtain ⟨t₀, htt₀, ht₀T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    have htt₀' : t < t₀ := ENNReal.coe_lt_coe.1 htt₀
    obtain ⟨τ, -, -, hτc, hτ, -⟩ := hd.exists_on ht₀T
    have hnhds : Iic t₀ ∈ 𝓝 t := Iic_mem_nhds htt₀'
    have hca : ContinuousOn (restartClock q U σ x₁ w') (Iic t₀) := by
      have : EqOn (restartClock q U σ x₁ w') (fun s : ℝ≥0 => τ s) (Iic t₀) := fun s hs => hτ s hs
      refine ContinuousOn.congr ?_ this
      exact hτc.comp NNReal.continuous_coe.continuousOn fun s hs => ⟨s.2, by exact_mod_cast hs⟩
    exact (hca.continuousAt hnhds).continuousWithinAt

/-- **The chart path is continuous before `T`.** -/
theorem continuousOn_restartPath :
    ContinuousOn (restartPath q U σ x₁ γ') {t | (t : ℝ≥0∞) < T} := by
  intro t ht
  obtain ⟨t₀, htt₀, ht₀T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htt₀' : t < t₀ := ENNReal.coe_lt_coe.1 htt₀
  obtain ⟨-, -, -, -, -, hcont, hlim⟩ := hd.exists_on ht₀T
  -- continuity on `Iic t₀`
  have hc : ContinuousOn (restartPath q U σ x₁ γ') (Iic t₀) := by
    intro s hs
    rcases eq_or_lt_of_le (zero_le (a := s)) with h0 | hpos
    · -- at `0`
      subst h0
      have hval : restartPath q U σ x₁ γ' 0 = 0 := by simp [restartPath]
      rw [ContinuousWithinAt, hval]
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hl := Metric.tendsto_nhds.1 hlim ε hε
      rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at hl
      obtain ⟨δ, hδ, hδε⟩ := hl
      rw [Filter.Eventually, Metric.mem_nhdsWithin_iff]
      refine ⟨δ, hδ, fun s' hs' => ?_⟩
      rcases eq_or_lt_of_le (zero_le (a := s')) with h0' | hpos'
      · subst h0'; simp [restartPath, hε]
      · have hne : s' ≠ 0 := hpos'.ne'
        show dist (restartPath q U σ x₁ γ' s') 0 < ε
        rw [restartPath, ite_eq_right hne]
        have hmem : (s' : ℝ) ∈ ball (0 : ℝ) δ ∩ Ioc 0 (t₀ : ℝ) := by
          refine ⟨?_, by exact_mod_cast hpos', by exact_mod_cast hs'.2⟩
          have := hs'.1
          rw [mem_ball, NNReal.dist_eq] at this
          rw [mem_ball, Real.dist_eq]; simpa using this
        have := hδε hmem
        simpa using this
    · -- at a positive time
      have hne : ∀ᶠ s' in 𝓝[Iic t₀] s, s' ≠ 0 :=
        nhdsWithin_le_nhds (isOpen_ne.mem_nhds hpos.ne')
      have hrm : ContinuousWithinAt (fun s' : ℝ≥0 => restartMap q U σ x₁ (γ' s')) (Iic t₀) s := by
        have h1 := hcont (s : ℝ) ⟨by exact_mod_cast hpos, by exact_mod_cast hs⟩
        have h2 : ContinuousWithinAt (fun t : ℝ => restartMap q U σ x₁ (γ' t.toNNReal))
            (Ioc 0 (t₀ : ℝ)) ((fun s' : ℝ≥0 => (s' : ℝ)) s) := h1
        have h3 := h2.comp NNReal.continuous_coe.continuousWithinAt
          (s := Ioi 0 ∩ Iic t₀) fun s' hs' => ⟨by exact_mod_cast hs'.1, by exact_mod_cast hs'.2⟩
        have h4 : ContinuousWithinAt (fun s' : ℝ≥0 => restartMap q U σ x₁ (γ' s')) (Ioi 0 ∩ Iic t₀) s := by
          refine h3.congr (fun s' _ => ?_) ?_ <;> simp
        exact h4.mono_of_mem_nhdsWithin (by rw [inter_comm]; exact inter_mem_nhdsWithin _ (Ioi_mem_nhds hpos))
      refine hrm.congr_of_eventuallyEq ?_ (by rw [restartPath, ite_eq_right hpos.ne'])
      filter_upwards [hne] with s' hs'
      rw [restartPath, ite_eq_right hs']
  exact ((hc t (show t ≤ t₀ from htt₀'.le)).continuousAt (Iic_mem_nhds htt₀')).continuousWithinAt

/-- A counterflow point at a positive time before `T` has its `E`-image in the remaining domain `ℍ \ K^U_σ`. -/
theorem realMobius_mem_H_diff {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) (ht0 : 0 < t) :
    realMobius 0 (-(1 + q)) 1 1 (γ' t) ∈ H \ QuantumZipper.fwdHull U σ := by
  have hal := hd.alive t ht
  have hγH : γ' t ∈ H := hal.mem t ht0 le_rfl
  have hdet : (0 : ℝ) < 0 * 1 - (-(1 + q)) * 1 := by linarith [hd.q_pos]
  refine ⟨QuantumZipper.CA.realMobius_mem_H hdet hγH, fun hK => ?_⟩
  have hfill := hd.trace.2.2 t (lt_of_lt_of_le ht hd.exit_le)
  have hγK : γ' t ∈ cfHull w' t :=
    inter_H_subset_of_isFilling hfill ⟨⟨t, ⟨zero_le, le_rfl⟩, rfl⟩, hγH⟩
  exact Set.disjoint_left.1 hal.far₂ (subset_closure hK)
    (mem_insert_of_mem _ (subset_closure ⟨_, hγK, rfl⟩))

/-- **The counterflow restart, pathwise** (`IsCounterflowChartContinuation` with `U′ = ∞`). Let the segment `A`
meet `ℍ` inside the hull `K^U_σ` and miss the counterflow start, let `f_σ⁻¹ → z` at `0` (the tip), and let the chart
capacity be exhausted before the exit time `T`. Then the completed counterflow is `ψ ∘ γ` in a clock, with the
inverse chart `ψ = restartInv` and the chart path in capacity time `γ = restartChartPath`, which is continuous. -/
theorem isCounterflowChartContinuation {A : Set ℂ} {z : ℂ} {Q : ℝ}
    (hA : A ∩ H ⊆ QuantumZipper.fwdHull U σ) (hA₁ : ((-1 - q : ℝ) : ℂ) ∉ A)
    (htip : Tendsto (QuantumZipper.fwdMapInv U σ) (𝓝[H] 0) (𝓝 z))
    (hexh : ∀ u : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < T ∧ u ≤ restartClock q U σ x₁ w' t) :
    MarkovOther.IsCounterflowChartContinuation A z (Sec4.stripCounterflowPath q γ') Q
        (restartChartPath q U σ x₁ w' γ' T) ⊤ ∧
      Continuous (restartChartPath q U σ x₁ w' γ' T) := by
  have ha := hd.isExhaustingClock hexh
  have hP : 0 < U σ - x₁ := sub_pos.2 hd.x₁_lt
  refine ⟨isCounterflowChartContinuation_of_clock (ψ := restartInv q (U σ - x₁) Q U σ z)
    (fun w hw => restartInv_notMem_of_mem_H hd.U_cont hd.U_zero hd.σ_nonneg hP hA hw)
    (fun x hx hxQ => restartInv_ofReal_notMem hd.q_pos hA₁ hx hxQ)
    (fun f hf hfi => tendsto_restartInv hP htip f hf hfi) ha (fun t ht => ?_), ?_⟩
  · rw [restartChartPath, ha.clockInv_apply ht]
    rcases eq_or_lt_of_le (zero_le (a := t)) with h0 | hpos
    · subst h0
      have h1 : restartPath q U σ x₁ γ' 0 = 0 := by simp [restartPath]
      rw [h1, restartInv_zero, hd.trace.1, Sec4.stripCounterflowChart_inv_zero]
      push_cast
      ring
    · rw [restartPath, ite_eq_right hpos.ne', stripCounterflowChart_inv_eq_realMobius]
      exact restartInv_restartMap hd.U_cont hd.U_zero hd.σ_nonneg rfl hd.x₁_lt (hd.realMobius_mem_H_diff ht hpos)
  · exact hd.continuousOn_restartPath.comp_continuous ha.continuous_clockInv fun u => (ha.clockInv_spec u).1

end IsRestartData

end CrossRestart

end Sec5

end InteractingSLE
