/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetLeafAnnounce
import InteractingSLE.Spec.Restart.RetLeafTraceBorel

/-!
# The canonical killed driving lifetime is predictable

Packet PROVE-T15-RET. PROVE-RETPLUMB's model constructor needs the lifetime of the canonical stopped
model to be announced in its own killed driving filtration (`RetAux79.RetDrivingLifetimePredictable`).
This file proves it from four almost-sure facts about the canonical trace under the model law
(`retDrivingLifetimePredictable_of_trace`): the decoded trace generates the decoded driver through the
lifetime, the lifetime is positive, the trace is in `ℍ` at positive times before the lifetime, and it is
real at a finite lifetime.

The blow-up process is `1 / Im γ(t)`, modified on a null set so that it is continuous at all positive
times before the lifetime. It is observable in the killed driving filtration: before the lifetime the
trace is the tip reader `LP.traceAt t` of the driver (generating property), and the tip reader of the
driver frozen at `t` (`frozenDrv`) is a measurable function of the killed history up to `t`
(`measurable_frozenDrv_apply`). The general announcement `exists_isAnnouncingSeq_of_blowup` then applies;
no continuity at time `0` is needed, which is why PROVE-RETPLUMB's `RetBoundaryApproachObservable` is
not used.

The pushforward of the four facts from the source is in `RetLeafModelCtor.lean`; the measurability of
the corresponding events on the carrier is proved here (`measurableSet_retCanonical_interior`,
`measurable_retCanonical_terminal`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal NNRat

namespace InteractingSLE.Restart.RetLeaf

open RetAux79 Sec7.Coding

/-! ### The frozen driver is observable in the killed driving σ-algebra -/

section Frozen

variable {α : Type*} {nL nR : ℕ} {W : ℝ≥0 → α → ℝ} {VL : Fin nL → ℝ≥0 → α → ℝ}
  {VR : Fin nR → ℝ≥0 → α → ℝ} {ζ : α → ℝ≥0∞}

/-- The driver frozen at `t`, set to `0` when dead at `t`. -/
def frozenDrv (W : ℝ≥0 → α → ℝ) (ζ : α → ℝ≥0∞) (t : ℝ≥0) (a : α) : ℝ≥0 → ℝ :=
  fun r => if (t : ℝ≥0∞) < ζ a then W (min r t) a else 0

theorem measurableSet_live_killedDrivingSigma (t : ℝ≥0) :
    MeasurableSet[killedDrivingSigma W VL VR ζ t] {a | (t : ℝ≥0∞) < ζ a} := by
  apply MeasurableSpace.measurableSet_generateFrom
  refine ⟨t, le_rfl, univ, MeasurableSet.univ, ?_⟩
  ext a
  simp

theorem measurable_frozenDrv_apply (t r : ℝ≥0) :
    Measurable[killedDrivingSigma W VL VR ζ t] fun a => frozenDrv W ζ t a r := by
  intro B hB
  have hgen : MeasurableSet[killedDrivingSigma W VL VR ζ t]
      {a | ((min r t : ℝ≥0) : ℝ≥0∞) < ζ a ∧ (W (min r t) a, fun i => VL i (min r t) a,
        fun i => VR i (min r t) a) ∈ B ×ˢ (univ : Set ((Fin nL → ℝ) × (Fin nR → ℝ)))} :=
    MeasurableSpace.measurableSet_generateFrom
      ⟨min r t, min_le_right _ _, _, hB.prod MeasurableSet.univ, rfl⟩
  have e : (fun a => frozenDrv W ζ t a r) ⁻¹' B =
      ({a | (t : ℝ≥0∞) < ζ a} ∩ {a | ((min r t : ℝ≥0) : ℝ≥0∞) < ζ a ∧ (W (min r t) a,
        fun i => VL i (min r t) a, fun i => VR i (min r t) a) ∈
          B ×ˢ (univ : Set ((Fin nL → ℝ) × (Fin nR → ℝ)))}) ∪
        ({a | (t : ℝ≥0∞) < ζ a}ᶜ ∩ {_a | (0 : ℝ) ∈ B}) := by
    ext a
    simp only [frozenDrv, mem_preimage, mem_union, mem_inter_iff, mem_ofPred_eq, mem_compl_iff,
      mem_prod, mem_univ, and_true]
    by_cases h : (t : ℝ≥0∞) < ζ a
    · have h' : ((min r t : ℝ≥0) : ℝ≥0∞) < ζ a :=
        lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right r t)) h
      simp only [h, h', true_and, ↓reduceIte, not_true_eq_false, false_and, or_false]
    · simp only [h, ↓reduceIte, false_and, not_false_eq_true, true_and, false_or]
  rw [e]
  exact ((measurableSet_live_killedDrivingSigma t).inter hgen).union
    ((measurableSet_live_killedDrivingSigma t).compl.inter (MeasurableSet.const _))

theorem measurable_traceAt_frozenDrv (t : ℝ≥0) :
    Measurable[killedDrivingSigma W VL VR ζ t] fun a => LP.traceAt t (frozenDrv W ζ t a) := by
  let _ : MeasurableSpace α := killedDrivingSigma W VL VR ζ t
  exact (LP.measurable_traceAt t).comp (measurable_pi_iff.2 (measurable_frozenDrv_apply t))

theorem traceAt_frozenDrv {t : ℝ≥0} {a : α} (ht : (t : ℝ≥0∞) < ζ a) :
    LP.traceAt t (frozenDrv W ζ t a) = LP.traceAt t (W · a) :=
  LP.traceAt_congr fun r hr => by simp only [frozenDrv, ht, ↓reduceIte, min_eq_left hr]

end Frozen

/-! ### The canonical lifetime is announced -/

/-- The four almost-sure trace facts used for the announcement. -/
def RetTraceGood (s : RetCanonSpace) : Prop :=
  IsGeneratingTrace (RetCanonSpace.driver · s) (RetCanonSpace.life s) (RetCanonSpace.trace s) ∧
    0 < RetCanonSpace.life s ∧
    (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < RetCanonSpace.life s → 0 < (RetCanonSpace.trace s t).im) ∧
    (RetCanonSpace.life s ≠ ⊤ → (RetCanonSpace.trace s (RetCanonSpace.life s).toNNReal).im = 0)

/-- On a good sample, `1 / Im γ(t)` tends to `+∞` as `t` increases to a finite lifetime. -/
theorem RetTraceGood.blowup {s : RetCanonSpace} (hs : RetTraceGood s) :
    RetCanonSpace.life s ≠ ⊤ → ∀ M : ℝ, ∃ s₀ : ℝ≥0, (s₀ : ℝ≥0∞) < RetCanonSpace.life s ∧
      ∀ t : ℝ≥0, s₀ ≤ t → (t : ℝ≥0∞) < RetCanonSpace.life s →
        M < 1 / (RetCanonSpace.trace s t).im := by
  intro htop M
  set L : ℝ≥0 := (RetCanonSpace.life s).toNNReal with hL
  have hLe : RetCanonSpace.life s = (L : ℝ≥0∞) := (ENNReal.coe_toNNReal htop).symm
  have hL0 : 0 < L := by
    have := hs.2.1
    rw [hLe] at this
    exact_mod_cast this
  set ε : ℝ := 1 / (|M| + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hcont : Tendsto (fun t => (RetCanonSpace.trace s t).im) (𝓝 L) (𝓝 0) := by
    have h := (Complex.continuous_im.comp (RetCanonSpace.continuous_trace s)).tendsto L
    rwa [Function.comp_apply, hs.2.2.2 htop] at h
  have hev : {t : ℝ≥0 | |(RetCanonSpace.trace s t).im| < ε} ∈ 𝓝 L := by
    have h := (Metric.tendsto_nhds.1 hcont) ε hε0
    filter_upwards [h] with t ht
    simpa only [Real.dist_eq, sub_zero] using ht
  obtain ⟨l, hlL, hsub⟩ := exists_Ioc_subset_of_mem_nhds hev ⟨0, hL0⟩
  obtain ⟨s₀, hs₀1, hs₀2⟩ := exists_between (max_lt hlL (half_lt_self hL0))
  refine ⟨s₀, by rw [hLe]; exact_mod_cast hs₀2, fun t ht htL => ?_⟩
  have htL' : t < L := by
    rw [hLe] at htL
    exact_mod_cast htL
  have hlt : l < t := lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hs₀1) ht
  have ht0 : 0 < t := lt_of_le_of_lt zero_le (lt_of_lt_of_le
    (lt_of_le_of_lt (le_max_right _ _) hs₀1) ht)
  have hpos := hs.2.2.1 t ht0 htL
  have habs : |(RetCanonSpace.trace s t).im| < ε := hsub ⟨hlt, htL'.le⟩
  rw [abs_of_pos hpos] at habs
  have h1 : 1 / ε < 1 / (RetCanonSpace.trace s t).im := one_div_lt_one_div_of_lt hpos habs
  rw [hε, one_div_one_div] at h1
  linarith [le_abs_self M]

/-- **The canonical killed driving lifetime is predictable** under any model law for which the canonical
trace almost surely generates the driver, starts a positive-lifetime continuation in `ℍ`, and ends on
`ℝ` at a finite lifetime. -/
theorem retDrivingLifetimePredictable_of_trace {Q : Measure RetCanonSpace} [IsProbabilityMeasure Q]
    {nL nR : ℕ} {VL : Fin nL → ℝ≥0 → RetCanonSpace → ℝ} {VR : Fin nR → ℝ≥0 → RetCanonSpace → ℝ}
    (hXP : IsMeasurableKilledDriving RetCanonSpace.driver VL VR RetCanonSpace.life)
    (hgood : ∀ᵐ s ∂Q, RetTraceGood s) :
    RetDrivingLifetimePredictable Q hXP := by
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hG : ∀ s, s ∉ N → RetTraceGood s := fun s hs => by
    by_contra h
    exact hs (hNsub h)
  set X : ℝ≥0 → RetCanonSpace → ℝ := fun t => Nᶜ.indicator fun s => 1 / (RetCanonSpace.trace s t).im
    with hX
  let 𝓖 := drivingFiltration Q hXP
  have hRC : 𝓖.IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  have hN𝓖 : ∀ (t : ℝ≥0) {S : Set RetCanonSpace}, MeasurableSet S → S ⊆ N → MeasurableSet[𝓖 t] S :=
    fun t S hS hSN => Ito.measurableSet_usualAugmentation_of_null hS (measure_mono_null hSN hN0) t
  have hlive : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {s | (t : ℝ≥0∞) < RetCanonSpace.life s} := fun t =>
    Ito.le_usualAugmentation _ Q t _ (measurableSet_live_killedDrivingSigma t)
  have hζ : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {s | RetCanonSpace.life s ≤ t} := fun t => by
    have e : {s | RetCanonSpace.life s ≤ t} = {s | (t : ℝ≥0∞) < RetCanonSpace.life s}ᶜ := by
      ext s
      simp only [mem_ofPred_eq, mem_compl_iff, not_lt]
    rw [e]
    exact (hlive t).compl
  have hXa : ∀ (t : ℝ≥0) (c : ℝ), MeasurableSet[𝓖 t]
      {s | (t : ℝ≥0∞) < RetCanonSpace.life s ∧ c < X t s} := by
    intro t c
    set f : RetCanonSpace → ℝ := fun s => 1 / (LP.traceAt t (frozenDrv RetCanonSpace.driver
      RetCanonSpace.life t s)).im with hf
    have hfm : MeasurableSet[𝓖 t] {s | c < f s} := by
      refine Ito.le_usualAugmentation _ Q t _ ?_
      let _ : MeasurableSpace RetCanonSpace :=
        killedDrivingSigma RetCanonSpace.driver VL VR RetCanonSpace.life t
      have hm : Measurable f := measurable_const.div (Complex.measurable_im.comp
        (measurable_traceAt_frozenDrv (W := RetCanonSpace.driver) (VL := VL) (VR := VR)
          (ζ := RetCanonSpace.life) t))
      exact measurableSet_lt measurable_const hm
    have hlm : MeasurableSet {s | (t : ℝ≥0∞) < RetCanonSpace.life s} :=
      measurableSet_lt measurable_const RetCanonSpace.measurable_life
    have e : {s | (t : ℝ≥0∞) < RetCanonSpace.life s ∧ c < X t s} =
        (({s | (t : ℝ≥0∞) < RetCanonSpace.life s} ∩ Nᶜ) ∩ {s | c < f s}) ∪
          (({s | (t : ℝ≥0∞) < RetCanonSpace.life s} ∩ N) ∩ {_s | c < 0}) := by
      ext s
      simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff, hX]
      by_cases hsN : s ∈ N
      · rw [indicator_of_notMem (show s ∉ Nᶜ from fun h => h hsN)]
        exact ⟨fun h => Or.inr ⟨⟨h.1, hsN⟩, h.2⟩, fun h => h.elim (fun h => absurd hsN h.1.2)
          fun h => ⟨h.1.1, h.2⟩⟩
      · rw [indicator_of_mem (show s ∈ Nᶜ from hsN)]
        constructor
        · rintro ⟨ht, hc⟩
          refine Or.inl ⟨⟨ht, hsN⟩, ?_⟩
          have heq : LP.traceAt t (frozenDrv RetCanonSpace.driver RetCanonSpace.life t s) =
              RetCanonSpace.trace s t := by
            rw [traceAt_frozenDrv ht]
            exact LP.traceAt_eq_of_isGeneratingTrace (hG s hsN).1
              (RetCanonSpace.continuous_driver s).continuousOn (RetCanonSpace.driver_zero s) ht
          simp only [hf, heq]
          exact hc
        · rintro (⟨⟨ht, -⟩, hc⟩ | ⟨⟨-, h⟩, -⟩)
          · refine ⟨ht, ?_⟩
            have heq : LP.traceAt t (frozenDrv RetCanonSpace.driver RetCanonSpace.life t s) =
                RetCanonSpace.trace s t := by
              rw [traceAt_frozenDrv ht]
              exact LP.traceAt_eq_of_isGeneratingTrace (hG s hsN).1
                (RetCanonSpace.continuous_driver s).continuousOn (RetCanonSpace.driver_zero s) ht
            simpa only [hf, heq] using hc
          · exact absurd h hsN
    rw [e]
    exact ((hlive t).inter (hN𝓖 t hNm subset_rfl).compl).inter hfm |>.union
      (hN𝓖 t ((hlm.inter hNm).inter (MeasurableSet.const _)) fun s hs => hs.1.2)
  have hXc : ∀ s, ContinuousOn (X · s) {t | 0 < t ∧ (t : ℝ≥0∞) < RetCanonSpace.life s} := by
    intro s
    by_cases hsN : s ∈ N
    · have e : (X · s) = fun _ => 0 := funext fun t => by
        simp only [hX]
        exact indicator_of_notMem (show s ∉ Nᶜ from fun h => h hsN) _
      rw [e]
      exact continuousOn_const
    · have e : (X · s) = fun t => 1 / (RetCanonSpace.trace s t).im := funext fun t => by
        simp only [hX]
        exact indicator_of_mem (show s ∈ Nᶜ from hsN) _
      rw [e]
      exact continuousOn_const.div (Complex.continuous_im.comp
        (RetCanonSpace.continuous_trace s)).continuousOn fun t ht => ((hG s hsN).2.2.1 t ht.1 ht.2).ne'
  have hpos : ∀ᵐ s ∂Q, 0 < RetCanonSpace.life s := hgood.mono fun s hs => hs.2.1
  have hblow : ∀ᵐ s ∂Q, RetCanonSpace.life s ≠ ⊤ → ∀ M : ℝ, ∃ s₀ : ℝ≥0,
      (s₀ : ℝ≥0∞) < RetCanonSpace.life s ∧
      ∀ t : ℝ≥0, s₀ ≤ t → (t : ℝ≥0∞) < RetCanonSpace.life s → M < X t s := by
    filter_upwards [hgood, measure_eq_zero_iff_ae_notMem.1 hN0] with s hs hsN htop M
    obtain ⟨s₀, hs₀, h⟩ := hs.blowup htop M
    refine ⟨s₀, hs₀, fun t ht htL => ?_⟩
    simp only [hX]
    rw [indicator_of_mem (show s ∈ Nᶜ from hsN)]
    exact h t ht htL
  exact exists_isAnnouncingSeq_of_blowup (𝓖 := 𝓖) hζ hXa hXc hpos hblow

end InteractingSLE.Restart.RetLeaf
