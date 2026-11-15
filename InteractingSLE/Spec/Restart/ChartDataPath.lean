/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ChartDataChart
import InteractingSLE.Spec.Theorem15D5Inputs

/-!
# Continuations written in the first-contact chart

Packet PROVE-RESTART-CPL3 (the pathwise chart continuations of `Restart.FirstContactChartDataStatement`; (W8.1),
supplement p. 541; the chart limits of D.5, interface 2, which `Theorem15D5.IsChartContinuationLim` records). Given
the chart `IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift` (`ChartDataChart.lean`) and a continuous path `ρ` on `[0, U]`
(a physical continuation read through a clock) whose points before `U` are regular points of `closure D`, the chart
path `γ` with `ρ = ψ ∘ γ` exists, is continuous on `[0, U]`, and is the forward limit of `φ` along `D` at every
`ρ(u)`, `u < U` (`exists_chartPath`). The terminal value at a finite `U` (where `ρ(U)` may be a non-regular point,
e.g. a seed) is the left limit of `γ`, by the cluster-set lemma
`YuanCharacterisation.exists_tendsto_of_tendsto_comp_filter`.

## Main results

* `continuousOn_of_unique_preimage`: unique `ψ`-preimages in `ℍ̄` of a continuous path form a continuous path;
* **`exists_chartPath`**: the chart path of a continuation;
* `isChartRegularPoint_of_injOn`: for simple prefixes every point is regular;
* **`isChartContinuationLim_of_isFirstContactChart`**: the chart, a chart field with the frozen `IsChartTransport`,
  clocks and chart paths give the landed `Theorem15D5.IsChartContinuationLim`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Restart

/-! ### Unique preimages along a path -/

/-- **Unique preimages along a path.** If `ψ` is continuous on `ℍ̄` with bounded displacement, and every point
`ρ u` (`u ∈ T`) of a path continuous on `T` has exactly one `ψ`-preimage `γ u` in `ℍ̄`, then `γ` is continuous on
`T`. -/
theorem continuousOn_of_unique_preimage {ψ : ℂ → ℂ} (hψc : ContinuousOn ψ Hbar) {M : ℝ}
    (hM : ∀ w ∈ Hbar, ‖ψ w - w‖ ≤ M) {T : Set ℝ≥0} {ρ γ : ℝ≥0 → ℂ} (hρ : ContinuousOn ρ T)
    (hγH : ∀ u ∈ T, γ u ∈ Hbar) (hψγ : ∀ u ∈ T, ψ (γ u) = ρ u)
    (huniq : ∀ u ∈ T, ∀ w ∈ Hbar, ψ w = ρ u → w = γ u) : ContinuousOn γ T := by
  intro u₀ hu₀
  set s : Set ℂ := closedBall 0 (‖ρ u₀‖ + 1 + M) ∩ Hbar with hs
  have hsc : IsCompact s := (isCompact_closedBall 0 _).inter_right isClosed_Hbar
  have hρt : Tendsto ρ (𝓝[T] u₀) (𝓝 (ρ u₀)) := hρ u₀ hu₀
  have hmem : ∀ᶠ u in 𝓝[T] u₀, γ u ∈ s := by
    filter_upwards [self_mem_nhdsWithin, hρt (ball_mem_nhds _ one_pos)] with u hu hb
    refine ⟨mem_closedBall_zero_iff.2 ?_, hγH u hu⟩
    have h1 := hM (γ u) (hγH u hu)
    rw [hψγ u hu] at h1
    have h2 : ‖ρ u‖ ≤ ‖ρ u₀‖ + 1 := by
      have := norm_le_norm_add_norm_sub' (ρ u) (ρ u₀)
      rw [mem_preimage, mem_ball, dist_eq_norm] at hb
      linarith
    calc ‖γ u‖ = ‖ρ u - (ρ u - γ u)‖ := by ring_nf
      _ ≤ ‖ρ u‖ + ‖ρ u - γ u‖ := norm_sub_le _ _
      _ ≤ ‖ρ u₀‖ + 1 + M := by linarith
  have hFG : Tendsto (fun u => ψ (γ u)) (𝓝[T] u₀) (𝓝 (ρ u₀)) := by
    refine hρt.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact (hψγ u hu).symm
  have hGl : ∀ᶠ u in 𝓝[T] u₀, γ u ∈ Hbar := hmem.mono fun u hu => hu.2
  exact hsc.tendsto_nhds_of_unique_mapClusterPt hmem fun ξ hξ hcl =>
    huniq u₀ hu₀ ξ hξ.2 (eq_of_mapClusterPt hψc hGl hFG hξ.2 hcl)

/-! ### The chart path of a continuation -/

section Path

variable {η₁ η₂ : ℝ≥0 → ℂ} {s₀ t₀ : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}

/-- **Every point is regular for simple prefixes** meeting only at their common final point. -/
theorem isChartRegularPoint_of_injOn (hc₁ : ContinuousOn η₁ (Icc 0 s₀)) (hc₂ : ContinuousOn η₂ (Icc 0 t₀))
    (h0₁ : (η₁ 0).im = 0) (h0₂ : (η₂ 0).im = 0) (hp : η₁ s₀ = η₂ t₀) (hi₁ : InjOn η₁ (Icc 0 s₀))
    (hi₂ : InjOn η₂ (Icc 0 t₀)) (hmeet : ∀ s t : ℝ≥0, s ≤ s₀ → t ≤ t₀ → η₁ s = η₂ t → s = s₀ ∧ t = t₀)
    (z : ℂ) : IsChartRegularPoint η₁ s₀ η₂ t₀ z :=
  Or.inr (isUnboundedLinked_of_injOn hc₁ hc₂ h0₁ h0₂ hp (injOn_joinPath hi₁ hi₂ hmeet) z)

/-- **The chart path of a continuation** ((W8.1); D.5, interface 2). Let `ρ` be continuous on `[0, U]`, `0 < U`,
with `ρ(u)` a regular point of `closure D` for `u < U`. Then there is a chart path `γ`, continuous on `[0, U]`, with
`ρ = ψ ∘ γ` on `[0, U]` and `φ → γ(u)` along `D` at `ρ(u)` for `u < U`. -/
theorem exists_chartPath (hC : IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift) {ρ : ℝ≥0 → ℂ} {U : ℝ≥0∞}
    (hρ : ContinuousOn ρ {u | (u : ℝ≥0∞) ≤ U}) (hU : 0 < U)
    (hreg : ∀ u : ℝ≥0, (u : ℝ≥0∞) < U →
      ρ u ∈ closure (activeDomain η₁ s₀ η₂ t₀) ∧ IsChartRegularPoint η₁ s₀ η₂ t₀ (ρ u)) :
    ∃ γ : ℝ≥0 → ℂ, ContinuousOn γ {u | (u : ℝ≥0∞) ≤ U} ∧
      (∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U → ρ u = ψ (γ u)) ∧
      ∀ u : ℝ≥0, (u : ℝ≥0∞) < U → Tendsto φ (𝓝[activeDomain η₁ s₀ η₂ t₀] (ρ u)) (𝓝 (γ u)) := by
  obtain ⟨-, hbij, -, hoff, -, -, hψd, hψc, -, ⟨M, hM⟩, hlim⟩ := hC
  have hw : ∀ u : ℝ≥0, (u : ℝ≥0∞) < U → ∃ w ∈ Hbar,
      Tendsto φ (𝓝[activeDomain η₁ s₀ η₂ t₀] (ρ u)) (𝓝 w) ∧ ψ w = ρ u ∧
        ∀ w' ∈ Hbar, ψ w' = ρ u → w' = w := fun u hu => hlim _ (hreg u hu).1 (hreg u hu).2
  choose! w hwH hwt hwψ hwu using hw
  set T : Set ℝ≥0 := {u | (u : ℝ≥0∞) < U} with hT
  have hwc : ContinuousOn w T :=
    continuousOn_of_unique_preimage hψc hM
      (hρ.mono fun u (hu : (u : ℝ≥0∞) < U) => (le_of_lt hu : (u : ℝ≥0∞) ≤ U)) hwH hwψ hwu
  rcases eq_or_ne U ⊤ with hUt | hUt
  · -- infinite horizon: every time is before `U`
    have hall : ∀ u : ℝ≥0, (u : ℝ≥0∞) < U := fun u => hUt ▸ ENNReal.coe_lt_top
    have hTeq : {u : ℝ≥0 | (u : ℝ≥0∞) ≤ U} = T := by
      ext u; exact ⟨fun _ => hall u, fun (h : (u : ℝ≥0∞) < U) => (le_of_lt h : (u : ℝ≥0∞) ≤ U)⟩
    exact ⟨w, hTeq ▸ hwc, fun u _ => (hwψ u (hall u)).symm, fun u hu => hwt u hu⟩
  -- finite horizon `U = T₀`: the terminal value is a left limit
  lift U to ℝ≥0 using hUt with T₀
  have hT₀ : 0 < T₀ := by exact_mod_cast hU
  have hIic : {u : ℝ≥0 | (u : ℝ≥0∞) ≤ T₀} = Iic T₀ := by ext u; simp
  have hIio : T = Iio T₀ := by ext u; simp [hT]
  rw [hIio] at hwc
  have hne : (𝓝[<] T₀).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT₀⟩
  have hconn : ∀ V ∈ 𝓝[<] T₀, ∃ S ∈ 𝓝[<] T₀, S ⊆ V ∧ IsPreconnected S ∧ ContinuousOn w S := by
    intro V hV
    obtain ⟨l, hl, hlV⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hT₀).1 hV
    exact ⟨Ioo l T₀, Ioo_mem_nhdsLT hl, hlV, isPreconnected_Ioo, hwc.mono fun u hu => hu.2⟩
  have hGH : ∀ᶠ u in 𝓝[<] T₀, w u ∈ Hbar := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hwH u (by simpa using hu)
  have hρc : ContinuousOn ρ (Iic T₀) := hIic ▸ hρ
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T₀)).exists_bound_of_continuousOn
    (hρc.mono fun u hu => hu.2)
  have hGR : ∀ᶠ u in 𝓝[<] T₀, ‖w u‖ ≤ B + M := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu' : (u : ℝ≥0∞) < T₀ := by simpa using hu
    have h1 := hM (w u) (hwH u hu')
    rw [hwψ u hu'] at h1
    have h2 := hB u ⟨zero_le, le_of_lt hu⟩
    calc ‖w u‖ = ‖ρ u - (ρ u - w u)‖ := by ring_nf
      _ ≤ ‖ρ u‖ + ‖ρ u - w u‖ := norm_sub_le _ _
      _ ≤ B + M := by linarith
  have hFG : Tendsto (fun u => ψ (w u)) (𝓝[<] T₀) (𝓝 (ρ T₀)) := by
    have h1 : Tendsto ρ (𝓝[<] T₀) (𝓝 (ρ T₀)) :=
      ((hρc T₀ (mem_Iic.2 le_rfl)).mono Iio_subset_Iic_self).tendsto
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact (hwψ u (by simpa using hu)).symm
  have hR : ∀ x : ℂ, x.im = 0 → ψ x ∉ ψ '' H := by
    intro x hx hxD
    rw [hbij.image_eq] at hxD
    exact hoff x (fun h => (ne_of_gt (show 0 < x.im from h)) hx) hxD
  obtain ⟨ξ, hξH, hψξ, hξlim⟩ := YuanCharacterisation.exists_tendsto_of_tendsto_comp_filter hψd hψc
    hbij.injOn hR hconn hGH hGR hFG
  set γ : ℝ≥0 → ℂ := fun u => if u < T₀ then w u else ξ with hγ
  have hγw : ∀ u, u < T₀ → γ u = w u := fun u hu => by simp only [hγ, hu, ↓reduceIte]
  have hγT : γ T₀ = ξ := by simp only [hγ, lt_irrefl, ↓reduceIte]
  refine ⟨γ, ?_, ?_, ?_⟩
  · rw [hIic]
    intro u hu
    rcases (show u ≤ T₀ from hu).lt_or_eq with hlt | rfl
    · have hcw : ContinuousAt w u := (hwc u hlt).continuousAt (Iio_mem_nhds hlt)
      have heq : γ =ᶠ[𝓝 u] w := by
        filter_upwards [Iio_mem_nhds hlt] with v hv
        exact hγw v hv
      exact (hcw.congr heq.symm).continuousWithinAt
    · refine continuousWithinAt_Iio_iff_Iic.1 ?_
      show Tendsto γ (𝓝[<] u) (𝓝 (γ u))
      rw [hγT]
      refine hξlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with v hv
      exact (hγw v hv).symm
  · intro u hu
    rcases (show u ≤ T₀ by exact_mod_cast hu).lt_or_eq with hlt | rfl
    · rw [hγw u hlt]; exact (hwψ u (by exact_mod_cast hlt)).symm
    · rw [hγT, hψξ]
  · intro u hu
    have hlt : u < T₀ := by exact_mod_cast hu
    rw [hγw u hlt]
    exact hwt u hu

end Path

/-! ### Clocks -/

section Clock

variable {c : ℝ≥0 → ℝ≥0} {U ζ : ℝ≥0∞} {s₀ : ℝ≥0}

/-- A clock mapping `[0, U]` strictly increasingly onto `[s₀, ζ]` with `s₀ < ζ`: `U > 0`, `c 0 = s₀`, and every
`u < U` is sent into `[s₀, ζ)`, strictly after `s₀` when `u > 0`. -/
theorem clock_facts (hm : StrictMonoOn c {u | (u : ℝ≥0∞) ≤ U})
    (hi : c '' {u | (u : ℝ≥0∞) ≤ U} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ}) (hs₀ : (s₀ : ℝ≥0∞) < ζ) :
    0 < U ∧ c 0 = s₀ ∧ ∀ u : ℝ≥0, (u : ℝ≥0∞) < U → s₀ ≤ c u ∧ ((c u : ℝ≥0) : ℝ≥0∞) < ζ ∧ (0 < u → s₀ < c u) := by
  have hmem : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U → s₀ ≤ c u ∧ ((c u : ℝ≥0) : ℝ≥0∞) ≤ ζ := fun u hu => by
    have : c u ∈ c '' {u | (u : ℝ≥0∞) ≤ U} := ⟨u, hu, rfl⟩
    rw [hi] at this; exact this
  obtain ⟨u₀, hu₀, hcu₀⟩ : s₀ ∈ c '' {u | (u : ℝ≥0∞) ≤ U} := by rw [hi]; exact ⟨le_rfl, hs₀.le⟩
  have h0U : ((0 : ℝ≥0) : ℝ≥0∞) ≤ U := by simp
  have hc0 : c 0 = s₀ := le_antisymm (hcu₀ ▸ hm.monotoneOn h0U hu₀ zero_le) (hmem 0 h0U).1
  -- a time strictly after `s₀` within `[s₀, ζ]`
  obtain ⟨s₁, hs₁, hs₁ζ⟩ : ∃ s₁ : ℝ≥0, s₀ < s₁ ∧ (s₁ : ℝ≥0∞) ≤ ζ := by
    rcases eq_or_ne ζ ⊤ with h | h
    · exact ⟨s₀ + 1, lt_add_one s₀, h ▸ le_top⟩
    · refine ⟨ζ.toNNReal, ?_, ENNReal.coe_toNNReal_le_self⟩
      rwa [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal h]
  obtain ⟨u₁, hu₁, hcu₁⟩ : s₁ ∈ c '' {u | (u : ℝ≥0∞) ≤ U} := by rw [hi]; exact ⟨hs₁.le, hs₁ζ⟩
  have hU : 0 < U := by
    rcases eq_or_ne U 0 with h | h
    · exfalso
      have hu1 : u₁ = 0 := by have : (u₁ : ℝ≥0∞) ≤ 0 := h ▸ hu₁; exact_mod_cast le_antisymm this bot_le
      rw [hu1, hc0] at hcu₁
      exact (ne_of_lt hs₁) hcu₁
    · exact pos_iff_ne_zero.2 h
  refine ⟨hU, hc0, fun u hu => ⟨(hmem u hu.le).1, ?_, fun hu0 => ?_⟩⟩
  · -- a later time `u' ∈ (u, U]`
    obtain ⟨u', huu', hu'U⟩ : ∃ u' : ℝ≥0, u < u' ∧ (u' : ℝ≥0∞) ≤ U := by
      rcases eq_or_ne U ⊤ with h | h
      · exact ⟨u + 1, lt_add_one u, h ▸ le_top⟩
      · refine ⟨U.toNNReal, ?_, ENNReal.coe_toNNReal_le_self⟩
        rwa [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal h]
    have hlt : c u < c u' := hm hu.le hu'U huu'
    exact lt_of_lt_of_le (by exact_mod_cast hlt) (hmem u' hu'U).2
  · rw [← hc0]; exact hm h0U hu.le hu0

end Clock

/-! ### The chart continuation with chart limits -/

section Continuation

variable {κ : ℝ} {h : LQGMetric.DistOn upperHalfPlaneOpens} {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}
  {s₀ t₀ : ℝ≥0}

/-- The prefixes of continuous paths are closed. -/
theorem isClosed_prefixSet (hc₁ : ContinuousOn η₁ (Icc 0 s₀)) (hc₂ : ContinuousOn η₂ (Icc 0 t₀)) :
    IsClosed (prefixSet η₁ s₀ η₂ t₀) :=
  ((isCompact_Icc.image_of_continuousOn hc₁).union (isCompact_Icc.image_of_continuousOn hc₂)).isClosed

/-- **The pathwise first-contact restart with chart limits** (Lemma 7.8, p. 290; Theorem W8 and (W8.1), pp. 538–541;
Aux. 80; D.5, interface 2). Let `η₁`, `η₂` be continuous on their closed available intervals, in `ℍ̄`, from real
points, with a first contact `(s₀, t₀)` before both lifetimes; suppose both continuations stay in the closure of the
active domain `D` (Lemma 7.7's confinement) and both prefixes are simple (Aux. 25). Then `D` has a chart
`IsFirstContactChart`, and for every chart field `H` of `h` in it (frozen
`IsChartTransport` with `σ = 1`, `a = 0`, `k = χ`) and all continuous clocks `cᵢ` mapping `[0, Uᵢ]` strictly
increasingly onto the available continuations, there are continuous chart paths `γᵢ` with the landed
`Theorem15D5.IsChartContinuationLim`. -/
theorem exists_isChartContinuationLim (hc₁ : ContinuousOn η₁ {s | (s : ℝ≥0∞) ≤ ζ₁})
    (hc₂ : ContinuousOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂}) (hH₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ → η₁ s ∈ Hbar)
    (hH₂ : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ → η₂ t ∈ Hbar) (h0₁ : (η₁ 0).im = 0) (h0₂ : (η₂ 0).im = 0)
    (hfc : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀) (hs₀ : (s₀ : ℝ≥0∞) < ζ₁) (ht₀ : (t₀ : ℝ≥0∞) < ζ₂)
    (hconf₁ : ∀ s : ℝ≥0, s₀ ≤ s → (s : ℝ≥0∞) ≤ ζ₁ → η₁ s ∈ closure (activeDomain η₁ s₀ η₂ t₀))
    (hconf₂ : ∀ t : ℝ≥0, t₀ ≤ t → (t : ℝ≥0∞) ≤ ζ₂ → η₂ t ∈ closure (activeDomain η₁ s₀ η₂ t₀))
    (hinj₁ : InjOn η₁ (Icc 0 s₀)) (hinj₂ : InjOn η₂ (Icc 0 t₀)) :
    ∃ (φ ψ : ℂ → ℂ) (lift : ℂ → ℝ), IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift ∧
      ∀ (H : LQGMetric.DistOn upperHalfPlaneOpens) (c₁ c₂ : ℝ≥0 → ℝ≥0) (U₁ U₂ : ℝ≥0∞),
        IsChartTransport (φ, ψ, lift) 1 0 (QuantumZipper.chiC κ) h H →
        StrictMonoOn c₁ {u | (u : ℝ≥0∞) ≤ U₁} → ContinuousOn c₁ {u | (u : ℝ≥0∞) ≤ U₁} →
        c₁ '' {u | (u : ℝ≥0∞) ≤ U₁} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ₁} →
        StrictMonoOn c₂ {u | (u : ℝ≥0∞) ≤ U₂} → ContinuousOn c₂ {u | (u : ℝ≥0∞) ≤ U₂} →
        c₂ '' {u | (u : ℝ≥0∞) ≤ U₂} = {t | t₀ ≤ t ∧ (t : ℝ≥0∞) ≤ ζ₂} →
        ∃ γ₁ γ₂ : ℝ≥0 → ℂ, ContinuousOn γ₁ {u | (u : ℝ≥0∞) ≤ U₁} ∧ ContinuousOn γ₂ {u | (u : ℝ≥0∞) ≤ U₂} ∧
          Theorem15D5.IsChartContinuationLim κ h H η₁ ζ₁ s₀ η₂ ζ₂ t₀ γ₁ γ₂ U₁ U₂ := by
  obtain ⟨hs₀ζ, ht₀ζ, hp, hfirst⟩ := hfc
  have hI₁ : Icc 0 s₀ ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) ≤ ζ₁} := fun s hs =>
    (ENNReal.coe_le_coe.2 hs.2).trans hs₀ζ
  have hI₂ : Icc 0 t₀ ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ₂} := fun t ht =>
    (ENNReal.coe_le_coe.2 ht.2).trans ht₀ζ
  have hne₁ : ∀ s < s₀, η₁ s ≠ η₁ s₀ := fun s hs he =>
    not_le.2 hs (hfirst s t₀ ((ENNReal.coe_le_coe.2 hs.le).trans hs₀ζ) ht₀ζ (he.trans hp)).1
  have hne₂ : ∀ t < t₀, η₂ t ≠ η₁ s₀ := fun t ht he =>
    not_le.2 ht (hfirst s₀ t hs₀ζ ((ENNReal.coe_le_coe.2 ht.le).trans ht₀ζ) (he.symm)).2
  obtain ⟨φ, ψ, lift, hC⟩ := exists_isFirstContactChart (hc₁.mono hI₁) (hc₂.mono hI₂)
    (fun s hs => hH₁ s (hI₁ hs)) (fun t ht => hH₂ t (hI₂ ht)) h0₁ h0₂ hp hne₁ hne₂
    (hconf₁ s₀ le_rfl hs₀ζ)
  refine ⟨φ, ψ, lift, hC, fun H c₁ c₂ U₁ U₂ hT hm₁ hcc₁ hi₁ hm₂ hcc₂ hi₂ => ?_⟩
  obtain ⟨hU₁, hc0₁, hcl₁⟩ := clock_facts hm₁ hi₁ hs₀
  obtain ⟨hU₂, hc0₂, hcl₂⟩ := clock_facts hm₂ hi₂ ht₀
  have hmaps₁ : MapsTo c₁ {u | (u : ℝ≥0∞) ≤ U₁} {s | (s : ℝ≥0∞) ≤ ζ₁} := fun u hu => by
    have : c₁ u ∈ c₁ '' {u | (u : ℝ≥0∞) ≤ U₁} := ⟨u, hu, rfl⟩
    rw [hi₁] at this; exact this.2
  have hmaps₂ : MapsTo c₂ {u | (u : ℝ≥0∞) ≤ U₂} {t | (t : ℝ≥0∞) ≤ ζ₂} := fun u hu => by
    have : c₂ u ∈ c₂ '' {u | (u : ℝ≥0∞) ≤ U₂} := ⟨u, hu, rfl⟩
    rw [hi₂] at this; exact this.2
  -- every point is regular (simple prefixes meeting only at the contact)
  have hmeet : ∀ s t : ℝ≥0, s ≤ s₀ → t ≤ t₀ → η₁ s = η₂ t → s = s₀ ∧ t = t₀ := fun s t hs ht he => by
    have := hfirst s t ((ENNReal.coe_le_coe.2 hs).trans hs₀ζ) ((ENNReal.coe_le_coe.2 ht).trans ht₀ζ) he
    exact ⟨le_antisymm hs this.1, le_antisymm ht this.2⟩
  have hreg := isChartRegularPoint_of_injOn (hc₁.mono hI₁) (hc₂.mono hI₂) h0₁ h0₂ hp hinj₁ hinj₂ hmeet
  have hreg₁ : ∀ u : ℝ≥0, (u : ℝ≥0∞) < U₁ → η₁ (c₁ u) ∈ closure (activeDomain η₁ s₀ η₂ t₀) ∧
      IsChartRegularPoint η₁ s₀ η₂ t₀ (η₁ (c₁ u)) := fun u hu =>
    ⟨hconf₁ _ (hcl₁ u hu).1 (hcl₁ u hu).2.1.le, hreg _⟩
  have hreg₂ : ∀ u : ℝ≥0, (u : ℝ≥0∞) < U₂ → η₂ (c₂ u) ∈ closure (activeDomain η₁ s₀ η₂ t₀) ∧
      IsChartRegularPoint η₁ s₀ η₂ t₀ (η₂ (c₂ u)) := fun u hu =>
    ⟨hconf₂ _ (hcl₂ u hu).1 (hcl₂ u hu).2.1.le, hreg _⟩
  obtain ⟨γ₁, hγ₁c, he₁, hl₁⟩ := exists_chartPath hC (hc₁.comp hcc₁ hmaps₁) hU₁ hreg₁
  obtain ⟨γ₂, hγ₂c, he₂, hl₂⟩ := exists_chartPath hC (hc₂.comp hcc₂ hmaps₂) hU₂ hreg₂
  obtain ⟨hact, hbij, hφψ, hoff, hlc, hderiv, -⟩ := hC
  exact ⟨γ₁, γ₂, hγ₁c, hγ₂c, φ, ψ, lift, c₁, c₂, hact, hbij, hφψ, hoff, hlc, hderiv, hT, hm₁, hi₁, hm₂,
    hi₂, he₁, he₂, hl₁, hl₂⟩

end Continuation

end Restart

end InteractingSLE
