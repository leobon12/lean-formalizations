/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartPack
import InteractingSLE.Spec.Sec6.DrivingCriterion
import InteractingSLE.Spec.Sec5.CrossRestartLawPath

/-!
# The image Loewner chain of the counterflow in the restart chart, for all times before the exit

Packet PROVE-CFRESTART (Lemma 4.7's proof, p. 118: "Proposition 6.12 consequently applies after a half-plane
coordinate change and gives a continuous driver up to the first contact in question").

PROVE-SEC5-F's `exists_loewner_restartMap_trace` gives, on each horizon `t₀` before the exit, a continuous driver
whose hulls are the restart-chart images `Φ(K′_t)` of the counterflow hulls at the chart capacity clock. PROVE-SEC5-G's
`IsRestartData.exists_on` keeps only the clock. This file keeps the drivers and glues them: **one** driver `W''` of
the counterflow's image in the restart chart for all chart capacities before the exit (the process-level image hull
chain that Lemma 4.7's direction of the cross-conditioning needs; PROVE-GLUECOND10 "What remains" 1).

* `IsRestartData.exists_drv_on`: the driver of one horizon, with the hull and filling identities at the clock;
* `IsRestartData.exists_clock_eq`: every chart capacity up to the horizon is attained by the clock;
* `IsRestartData.eqOn_drv`: drivers of two horizons agree up to the smaller one (hulls determine continuous drivers,
  `Sec6.eqOn_of_fwdHull_eq`);
* **`IsRestartData.exists_imageDriver`**: one driver `W''` (`W'' 0 = 0`) that on every horizon `t₀ < T` agrees, on
  `[0, a(t₀)]`, with a continuous driver whose hull at `a(t)` is `Φ(K′_t)` and is the filling of `Φ(γ′((0, t]))`;
* **`IsRestartData.isGeneratingTrace_restartChartPath`**: when the chart capacity is exhausted before the exit, the
  chart path in chart capacity time `restartChartPath` is a generating trace, of infinite lifetime, of every such
  glued driver (the pathwise content of "the restart variable is the trace of the image driver").
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE.Sec5.CrossRestart

open ConformalImage ConformalImageFull

namespace IsRestartData

variable {q : ℝ} {U : ℝ → ℝ} {σ x₁ : ℝ} {w' : ℝ≥0 → ℝ} {ζ' : ℝ≥0∞} {γ' : ℝ≥0 → ℂ} {T : ℝ≥0∞}
  (hd : IsRestartData q U σ x₁ w' ζ' γ' T)
include hd

/-- **The image chain on one horizon `t₀` before the exit**, with its driver: a continuous `W''`, `W'' 0 = 0`, whose
hull at the chart capacity `a(t)` is the restart-chart image `Φ(K′_t)` for `t ≤ t₀`, and is the filling of
`Φ(γ′([0, t]) ∩ ℍ)` for `0 < t ≤ t₀`; the clock `a` is continuous on `[0, t₀]` (read on `ℝ`) with `a 0 = 0`. -/
theorem exists_drv_on {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < T) :
    ∃ (τ W'' : ℝ → ℝ), Continuous W'' ∧ W'' 0 = 0 ∧ τ 0 = 0 ∧ StrictMonoOn τ (Icc 0 (t₀ : ℝ)) ∧
      ContinuousOn τ (Icc 0 (t₀ : ℝ)) ∧ (∀ t : ℝ≥0, t ≤ t₀ → restartClock q U σ x₁ w' t = τ t) ∧
      (∀ t : ℝ≥0, t ≤ t₀ →
        QuantumZipper.fwdHull W'' (restartClock q U σ x₁ w' t) = restartMap q U σ x₁ '' cfHull w' t) ∧
      ∀ t : ℝ≥0, 0 < t → t ≤ t₀ → IsFilling (QuantumZipper.fwdHull W'' (restartClock q U σ x₁ w' t))
        (restartMap q U σ x₁ '' ((fun s : ℝ => γ' s.toNNReal) '' Icc 0 (t : ℝ) ∩ H)) := by
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
  obtain ⟨τ, W'', hW''c, hW''0, hτ0, hτm, hτc, hKτ, hfill, -, -⟩ :=
    exists_loewner_restartMap_trace hW hW0 t₀.2 hd.q_pos hr hd1 hd.U_cont hd.U_zero hd.σ_nonneg hd2
      hd.x₁_eq hr₃ hd3 hγ0 hγc hγH hγK
  have hclock : ∀ t : ℝ≥0, t ≤ t₀ → restartClock q U σ x₁ w' t = τ t := by
    intro t htt₀
    have htI : (t : ℝ) ∈ Icc (0 : ℝ) t₀ := ⟨t.2, htt₀⟩
    have hτnn : 0 ≤ τ t := by
      rw [← hτ0]; exact hτm.monotoneOn ⟨le_rfl, t₀.2⟩ htI htI.1
    rw [restartClock, ← hK t t.2 htt₀, ← hKτ t htI, hcapSet_eq (isHPHull_fwdHull hW''c hτnn),
      hcap_fwdHull hW''c hW''0 hτnn]
    ring
  refine ⟨τ, W'', hW''c, hW''0, hτ0, hτm, hτc, hclock, fun t htt₀ => ?_, fun t ht htt₀ => ?_⟩
  · rw [hclock t htt₀, hKτ t ⟨t.2, htt₀⟩, hK t t.2 htt₀]
  · rw [hclock t htt₀]
    exact hfill t ⟨by exact_mod_cast ht, htt₀⟩

/-- The chart capacity clock vanishes at `0`. -/
theorem restartClock_zero : restartClock q U σ x₁ w' 0 = 0 := by
  obtain ⟨τ, -, -, -, hτ0, -, -, hτ, -⟩ := hd.exists_drv_on (t₀ := 0) (by simpa using hd.exit_pos)
  rw [hτ 0 le_rfl]; simpa using hτ0

/-- **Every chart capacity up to the horizon is attained by the clock.** -/
theorem exists_clock_eq {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < T) {u : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ restartClock q U σ x₁ w' t₀) : ∃ t : ℝ≥0, t ≤ t₀ ∧ restartClock q U σ x₁ w' t = u := by
  obtain ⟨τ, -, -, -, hτ0, -, hτc, hτ, -⟩ := hd.exists_drv_on ht₀
  rw [hτ t₀ le_rfl] at hu
  obtain ⟨r, hr, hru⟩ := isPreconnected_Icc.intermediate_value (left_mem_Icc.2 t₀.2)
    (right_mem_Icc.2 t₀.2) hτc ⟨by rw [hτ0]; exact hu0, hu⟩
  refine ⟨r.toNNReal, Real.toNNReal_le_iff_le_coe.2 hr.2, ?_⟩
  rw [hτ _ (Real.toNNReal_le_iff_le_coe.2 hr.2), Real.coe_toNNReal _ hr.1, hru]

/-- The chart capacity clock is nonnegative before the exit. -/
theorem restartClock_nonneg {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < T) : 0 ≤ restartClock q U σ x₁ w' t₀ := by
  obtain ⟨τ, -, -, -, hτ0, hτm, -, hτ, -⟩ := hd.exists_drv_on ht₀
  rw [hτ t₀ le_rfl, ← hτ0]
  exact hτm.monotoneOn ⟨le_rfl, t₀.2⟩ ⟨t₀.2, le_rfl⟩ t₀.2

/-- The chart capacity clock is monotone before the exit. -/
theorem restartClock_mono {t t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < T) (htt₀ : t ≤ t₀) :
    restartClock q U σ x₁ w' t ≤ restartClock q U σ x₁ w' t₀ := by
  obtain ⟨τ, -, -, -, -, hτm, -, hτ, -⟩ := hd.exists_drv_on ht₀
  rw [hτ t htt₀, hτ t₀ le_rfl]
  exact hτm.monotoneOn ⟨t.2, htt₀⟩ ⟨t₀.2, le_rfl⟩ htt₀

/-- **Drivers of the image chain on two horizons agree up to the smaller horizon** (hulls determine continuous
drivers). -/
theorem eqOn_drv {t₀ t₁ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < T) (h01 : t₀ ≤ t₁) {V₀ V₁ : ℝ → ℝ} (hV₀ : Continuous V₀)
    (hV₀0 : V₀ 0 = 0) (hV₁ : Continuous V₁) (hV₁0 : V₁ 0 = 0)
    (hK₀ : ∀ t : ℝ≥0, t ≤ t₀ →
      QuantumZipper.fwdHull V₀ (restartClock q U σ x₁ w' t) = restartMap q U σ x₁ '' cfHull w' t)
    (hK₁ : ∀ t : ℝ≥0, t ≤ t₁ →
      QuantumZipper.fwdHull V₁ (restartClock q U σ x₁ w' t) = restartMap q U σ x₁ '' cfHull w' t) :
    EqOn V₀ V₁ (Icc 0 (restartClock q U σ x₁ w' t₀)) := by
  refine Sec6.eqOn_of_fwdHull_eq hV₀ hV₁ hV₀0 hV₁0 (hd.restartClock_nonneg ht₀) fun s hs => ?_
  obtain ⟨t, htt₀, rfl⟩ := hd.exists_clock_eq ht₀ hs.1 hs.2
  rw [hK₀ t htt₀, hK₁ t (htt₀.trans h01)]

/-- **The image driver of the counterflow in the restart chart, for all chart capacities before the exit.** There is
one driver `W''` with `W'' 0 = 0` such that on every horizon `t₀ < T` it agrees on `[0, a(t₀)]` with a continuous
driver `V` (`V 0 = 0`) whose hull at the chart capacity `a(t)` is `Φ(K′_t)` for `t ≤ t₀`, and is the filling of
`Φ(γ′([0, t]) ∩ ℍ)` for `0 < t ≤ t₀`. -/
theorem exists_imageDriver :
    ∃ W'' : ℝ → ℝ, W'' 0 = 0 ∧ ∀ t₀ : ℝ≥0, (t₀ : ℝ≥0∞) < T →
      ∃ V : ℝ → ℝ, Continuous V ∧ V 0 = 0 ∧ EqOn W'' V (Icc 0 (restartClock q U σ x₁ w' t₀)) ∧
        (∀ t : ℝ≥0, t ≤ t₀ →
          QuantumZipper.fwdHull V (restartClock q U σ x₁ w' t) = restartMap q U σ x₁ '' cfHull w' t) ∧
        ∀ t : ℝ≥0, 0 < t → t ≤ t₀ → IsFilling (QuantumZipper.fwdHull V (restartClock q U σ x₁ w' t))
          (restartMap q U σ x₁ '' ((fun s : ℝ => γ' s.toNNReal) '' Icc 0 (t : ℝ) ∩ H)) := by
  classical
  -- the driver of each horizon
  have hex : ∀ t₀ : {t₀ : ℝ≥0 // (t₀ : ℝ≥0∞) < T}, ∃ V : ℝ → ℝ, Continuous V ∧ V 0 = 0 ∧
      (∀ t : ℝ≥0, t ≤ t₀.1 →
        QuantumZipper.fwdHull V (restartClock q U σ x₁ w' t) = restartMap q U σ x₁ '' cfHull w' t) ∧
      ∀ t : ℝ≥0, 0 < t → t ≤ t₀.1 → IsFilling (QuantumZipper.fwdHull V (restartClock q U σ x₁ w' t))
        (restartMap q U σ x₁ '' ((fun s : ℝ => γ' s.toNNReal) '' Icc 0 (t : ℝ) ∩ H)) := fun t₀ => by
    obtain ⟨-, V, hVc, hV0, -, -, -, -, hK, hfill⟩ := hd.exists_drv_on t₀.2
    exact ⟨V, hVc, hV0, hK, hfill⟩
  choose D hDc hD0 hDK hDfill using hex
  -- `W''(u)` is read from any horizon whose clock reaches `u`
  set W'' : ℝ → ℝ := fun u =>
    if h : ∃ t₀ : {t₀ : ℝ≥0 // (t₀ : ℝ≥0∞) < T}, u ≤ restartClock q U σ x₁ w' t₀.1 then D h.choose u else 0
    with hW''
  have hagree : ∀ (t₀ : {t₀ : ℝ≥0 // (t₀ : ℝ≥0∞) < T}) (u : ℝ), u ∈ Icc 0 (restartClock q U σ x₁ w' t₀.1) →
      W'' u = D t₀ u := by
    intro t₀ u hu
    have h : ∃ t₀ : {t₀ : ℝ≥0 // (t₀ : ℝ≥0∞) < T}, u ≤ restartClock q U σ x₁ w' t₀.1 := ⟨t₀, hu.2⟩
    have e : W'' u = D h.choose u := by
      simp only [hW'']
      exact dite_eq_left h
    rw [e]
    set t₂ := h.choose with ht₂
    have hu₂ : u ≤ restartClock q U σ x₁ w' t₂.1 := h.choose_spec
    rcases le_total t₂.1 t₀.1 with h20 | h02
    · exact hd.eqOn_drv t₂.2 h20 (hDc t₂) (hD0 t₂) (hDc t₀) (hD0 t₀) (hDK t₂) (hDK t₀) ⟨hu.1, hu₂⟩
    · exact (hd.eqOn_drv t₀.2 h02 (hDc t₀) (hD0 t₀) (hDc t₂) (hD0 t₂) (hDK t₀) (hDK t₂) hu).symm
  have hT0 : ((0 : ℝ≥0) : ℝ≥0∞) < T := by simpa using hd.exit_pos
  refine ⟨W'', ?_, fun t₀ ht₀ => ⟨D ⟨t₀, ht₀⟩, hDc _, hD0 _, fun u hu => hagree ⟨t₀, ht₀⟩ u hu,
    hDK ⟨t₀, ht₀⟩, hDfill ⟨t₀, ht₀⟩⟩⟩
  rw [hagree ⟨0, hT0⟩ 0 ⟨le_rfl, by rw [hd.restartClock_zero]⟩, hD0]

/-- **The chart path in chart capacity time generates the image driver** when the chart capacity is exhausted before
the exit: for a driver `W''` as in `exists_imageDriver`, `restartChartPath` is a generating trace of `W''` (read on
`ℝ≥0`) with infinite lifetime. -/
theorem isGeneratingTrace_restartChartPath
    (hexh : ∀ u : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < T ∧ u ≤ restartClock q U σ x₁ w' t) {W'' : ℝ → ℝ}
    (hW'' : ∀ t₀ : ℝ≥0, (t₀ : ℝ≥0∞) < T →
      ∃ V : ℝ → ℝ, Continuous V ∧ V 0 = 0 ∧ EqOn W'' V (Icc 0 (restartClock q U σ x₁ w' t₀)) ∧
        ∀ t : ℝ≥0, t ≤ t₀ →
          QuantumZipper.fwdHull V (restartClock q U σ x₁ w' t) = restartMap q U σ x₁ '' cfHull w' t) :
    IsGeneratingTrace (fun u : ℝ≥0 => W'' u) ⊤ (restartChartPath q U σ x₁ w' γ' T) := by
  have ha := hd.isExhaustingClock hexh
  have hT0 : ((0 : ℝ≥0) : ℝ≥0∞) < T := by simpa using hd.exit_pos
  have hinv0 : clockInv (restartClock q U σ x₁ w') T 0 = 0 := by
    have := ha.clockInv_apply hT0
    rwa [ha.zero, Real.toNNReal_zero] at this
  refine ⟨?_, ?_, fun u _ => ?_⟩
  · rw [restartChartPath, hinv0, restartPath_zero]
  · exact (hd.continuousOn_restartPath.comp_continuous ha.continuous_clockInv
      fun u => (ha.clockInv_spec u).1).continuousOn
  -- the counterflow time of the capacity `u`, and a later horizon
  set t := clockInv (restartClock q U σ x₁ w') T u with ht
  obtain ⟨htT, hat⟩ := ha.clockInv_spec u
  rw [← ht] at htT hat
  obtain ⟨t₀, htt₀, ht₀T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 htT
  have htt₀' : t < t₀ := ENNReal.coe_lt_coe.1 htt₀
  obtain ⟨V, -, -, hWV, hVK⟩ := hW'' t₀ ht₀T
  have hlt : restartClock q U σ x₁ w' t < restartClock q U σ x₁ w' t₀ := ha.mono htT ht₀T htt₀'
  -- the hull of the glued driver at `u` is the image hull at `t`
  have hK : QuantumZipper.fwdHull (fun s : ℝ => W'' (s.toNNReal : ℝ)) (u : ℝ) =
      restartMap q U σ x₁ '' cfHull w' t := by
    rw [← hat]
    have e := fwdHull_eq_of_eqOn (W := fun s : ℝ => W'' (s.toNNReal : ℝ)) (W' := V)
      (hd.restartClock_nonneg htT) hlt fun r hr => by
        simp only [Real.coe_toNNReal _ hr.1]
        exact hWV hr
    rw [e, hVK t htt₀'.le]
  -- the chart path on `[0, u]` traces the chart path on `[0, t]`
  have himg : restartChartPath q U σ x₁ w' γ' T '' Icc 0 u = restartPath q U σ x₁ γ' '' Icc 0 t := by
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨clockInv (restartClock q U σ x₁ w') T v, ⟨zero_le, ha.strictMono_clockInv.monotone hv.2⟩, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      have hrT : (r : ℝ≥0∞) < T := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr.2) htT
      refine ⟨(restartClock q U σ x₁ w' r).toNNReal, ⟨zero_le, ?_⟩, ?_⟩
      · have hmono : restartClock q U σ x₁ w' r ≤ restartClock q U σ x₁ w' t :=
          (ha.mono.le_iff_le hrT htT).2 hr.2
        rw [← Real.toNNReal_coe (r := u), ← hat]
        exact Real.toNNReal_le_toNNReal hmono
      · rw [restartChartPath, ha.clockInv_apply hrT]
  rw [hK, himg, hd.restartMap_image_cfHull htT]
  have hpc : ContinuousOn (restartPath q U σ x₁ γ') (Icc 0 t) :=
    hd.continuousOn_restartPath.mono fun r hr => lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr.2) htT
  exact isFilling_fillH (isCompact_Icc.image_of_continuousOn hpc)

end IsRestartData

end InteractingSLE.Sec5.CrossRestart
