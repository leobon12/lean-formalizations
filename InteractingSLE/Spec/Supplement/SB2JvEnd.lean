/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JvReg
import InteractingSLE.Spec.Restart.RetEndLimit
import InteractingSLE.Spec.Sec7.R7Aux131Good
import InteractingSLE.Foundations.Loewner.CapacityEstimates
import InteractingSLE.Foundations.Loewner.YuanTrace

/-!
# SB2(2): a stage's relative facts from the stage curve's end behaviour (`StageRelP`, generic part)

Packet PROVE-SB2-LIFTSET (round 18). `StageRelP` (the relative facts of a stage) asks for the relative chart's
continuity and right inverse, the lifted good points in its domain, and an extension `α` of the generated capacity
trace through the relative lifetime with the inverse chart's boundary limits `f` along it. Everything but the domain
clause and the chart facts is a property of the stage curve `ρ`'s **end**:

* finite piece: `ρ` converges at `∞` (then its capacity lifetime is finite, `capLife_ne_top_of_subset_closedBall`, the
  capacity trace converges at it, `tendsto_capTrace_left`, and `capExt` extends it continuously,
  `continuousOn_capExt`; the relative driver is continuous through its lifetime, `continuousOn_driver_of_gen`):
  **`stageRelFinP_of`**;
* infinite piece: `ρ` is transient with infinite capacity lifetime and the inverse chart's boundary map stays within
  bounded distance of the identity (the traced boundary points form a closed set, a proper image):
  **`stageRelInfP_of`**, with the transient capacity trace `tendsto_norm_capTrace` (`PieceRegular` at an infinite
  relative lifetime).

Deterministic; the geometric inputs (drivenness, the end behaviour, the domain clause) are the per-stage facts.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

section Cap

variable {ρ : ℝ → ℂ}

/-- **A curve staying in a closed disc has a finite capacity lifetime.** -/
theorem capLife_ne_top_of_subset_closedBall {x r : ℝ} (hb : ∀ u, 0 ≤ u → ρ u ∈ closedBall (x : ℂ) r) :
    capLife ρ ≠ ⊤ := by
  have hle : ∀ n : ℕ, ENNReal.ofReal (capClock ρ n) ≤ ENNReal.ofReal (r ^ 2 / 2) := fun n => by
    refine ENNReal.ofReal_le_ofReal ?_
    unfold capClock
    have hsub : fillH (ρ '' Icc 0 (n : ℝ)) ⊆ closedBall (x : ℂ) r :=
      fillH_subset_closedBall (closure_minimal (fun z hz => by
        obtain ⟨u, hu, rfl⟩ := hz
        exact hb u hu.1) isClosed_closedBall)
    by_cases hh : IsHPHull (fillH (ρ '' Icc 0 (n : ℝ)))
    · rw [ConformalImage.hcapSet_eq hh]
      have := HPHull.hcap_le_rad_sq ⟨_, hh⟩ hsub
      linarith
    · unfold ConformalImage.hcapSet
      simp only [hh, ↓reduceDIte, zero_div]
      positivity
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le hle)

/-- A driven curve has a positive capacity lifetime. -/
theorem capLife_pos_of_driven {γ : ℝ → ℂ} (hγ : IsDrivenCurve γ) : 0 < capLife γ := by
  have h1 : 0 < capClock γ 1 := by
    have := hγ.strictMonoOn_capClock (mem_Ici.2 le_rfl) (mem_Ici.2 zero_le_one) zero_lt_one
    rwa [hγ.capClock_zero] at this
  calc (0 : ℝ≥0∞) < ENNReal.ofReal (capClock γ (1 : ℕ)) := by
        rw [Nat.cast_one]
        exact ENNReal.ofReal_pos.2 h1
    _ ≤ capLife γ := le_iSup (fun n : ℕ => ENNReal.ofReal (capClock γ n)) 1

/-- A curve continuous on `[0, ∞)` and converging at `∞` stays in a closed disc. -/
theorem exists_closedBall_of_tendsto (hc : ContinuousOn ρ (Ici 0)) {z : ℂ} (hz : Tendsto ρ atTop (𝓝 z)) :
    ∃ r : ℝ, ∀ u, 0 ≤ u → ρ u ∈ closedBall ((0 : ℝ) : ℂ) r := by
  obtain ⟨U, hU⟩ := (Metric.tendsto_atTop.1 hz) 1 one_pos
  obtain ⟨R₁, hR₁⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := max U 0)).image_of_continuousOn
    (hc.mono Icc_subset_Ici_self)).isBounded.subset_closedBall 0
  refine ⟨max R₁ (‖z‖ + 1), fun u hu => ?_⟩
  rw [Complex.ofReal_zero]
  by_cases huU : u ≤ max U 0
  · exact closedBall_subset_closedBall (le_max_left _ _) (hR₁ ⟨u, ⟨hu, huU⟩, rfl⟩)
  · push Not at huU
    have h1 := hU u (le_of_lt (lt_of_le_of_lt (le_max_left U 0) huU))
    rw [mem_closedBall, dist_zero_right]
    have h2 : ‖ρ u‖ ≤ ‖z‖ + dist (ρ u) z := by
      have := norm_le_norm_add_norm_sub' (ρ u) z
      rw [dist_eq_norm]; linarith [norm_sub_rev (ρ u) z]
    exact (h2.trans (by linarith)).trans (le_max_right _ _)

variable (hρ : IsDrivenCurve ρ)
include hρ

/-- The capacity clock is nonnegative. -/
theorem capClock_nonneg' {u : ℝ} (hu : 0 ≤ u) : 0 ≤ capClock ρ u := by
  have h := hρ.strictMonoOn_capClock.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hu) hu
  rwa [hρ.capClock_zero] at h

/-- **The capacity inverse tends to `∞` at a finite capacity lifetime.** -/
theorem tendsto_capInv_left (hfin : capLife ρ ≠ ⊤) :
    Tendsto (fun s : ℝ≥0 => capInv ρ s) (𝓝[<] (capLife ρ).toNNReal) atTop := by
  rw [Filter.tendsto_atTop]
  intro U
  have hU0 : (0 : ℝ) ≤ max U 0 := le_max_right U 0
  have hlt := hρ.ofReal_capClock_lt hU0
  have hc0 := capClock_nonneg' hρ hU0
  have hcT : (capClock ρ (max U 0)).toNNReal < (capLife ρ).toNNReal := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal hc0 hfin] at hlt
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hc0, ENNReal.coe_toNNReal_eq_toReal]
    exact hlt
  filter_upwards [Ioo_mem_nhdsLT hcT] with s hs
  by_contra hlt'
  push Not at hlt'
  have hsT : ENNReal.ofReal (s : ℝ) < capLife ρ := by
    rw [ENNReal.ofReal_coe_nnreal, ← ENNReal.coe_toNNReal hfin]
    exact ENNReal.coe_lt_coe.2 hs.2
  obtain ⟨h0, heq⟩ := hρ.capInv_spec s.coe_nonneg hsT
  have hmono := hρ.strictMonoOn_capClock.monotoneOn (mem_Ici.2 h0) (mem_Ici.2 hU0)
    (hlt'.le.trans (le_max_left U 0))
  rw [heq] at hmono
  have h1 := hs.1
  rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hc0] at h1
  linarith

/-- **The capacity trace converges at a finite capacity lifetime** when the curve converges at `∞`. -/
theorem tendsto_capTrace_left (hfin : capLife ρ ≠ ⊤) {z : ℂ} (hz : Tendsto ρ atTop (𝓝 z)) :
    Tendsto (capTrace ρ) (𝓝[<] (capLife ρ).toNNReal) (𝓝 z) :=
  hz.comp (tendsto_capInv_left hρ hfin)

/-- The capacity trace starts at `0`. -/
theorem capTrace_zero' : capTrace ρ 0 = 0 := by
  have h := hρ.capInv_eq (le_refl (0 : ℝ))
  rw [hρ.capClock_zero] at h
  show ρ (capInv ρ ((0 : ℝ≥0) : ℝ)) = 0
  rw [NNReal.coe_zero, h]
  exact hρ.zero

/-- **The capacity trace is transient at an infinite capacity lifetime** when the curve is. -/
theorem tendsto_norm_capTrace (htop : capLife ρ = ⊤) (htr : Tendsto (fun u => ‖ρ u‖) atTop atTop) :
    Tendsto (fun s => ‖capTrace ρ s‖) atTop atTop :=
  htr.comp (Sec7.R7Aux131.tendsto_capInv_of_capLife_eq_top hρ htop)

end Cap

section Ext

variable {ρ : ℝ → ℂ}

open Classical in
/-- **The capacity trace extended by the end point `z`** at and beyond the capacity lifetime. -/
def capExt (ρ : ℝ → ℂ) (z : ℂ) (s : ℝ≥0) : ℂ := if (s : ℝ≥0∞) < capLife ρ then capTrace ρ s else z

theorem capExt_of_lt {z : ℂ} {s : ℝ≥0} (hs : (s : ℝ≥0∞) < capLife ρ) : capExt ρ z s = capTrace ρ s := by
  unfold capExt; simp only [hs, ↓reduceIte]

theorem coe_le_capLife_iff (hfin : capLife ρ ≠ ⊤) (s : ℝ≥0) :
    (s : ℝ≥0∞) ≤ capLife ρ ↔ s ≤ (capLife ρ).toNNReal := by
  rw [← ENNReal.coe_toNNReal hfin, ENNReal.coe_le_coe, ENNReal.toNNReal_coe]

theorem coe_lt_capLife_iff (hfin : capLife ρ ≠ ⊤) (s : ℝ≥0) :
    (s : ℝ≥0∞) < capLife ρ ↔ s < (capLife ρ).toNNReal := by
  rw [← ENNReal.coe_toNNReal hfin, ENNReal.coe_lt_coe, ENNReal.toNNReal_coe]

/-- **The extended capacity trace is continuous through a finite capacity lifetime.** -/
theorem continuousOn_capExt (hρ : IsDrivenCurve ρ) (hfin : capLife ρ ≠ ⊤) {z : ℂ}
    (hz : Tendsto ρ atTop (𝓝 z)) : ContinuousOn (capExt ρ z) {s | (s : ℝ≥0∞) ≤ capLife ρ} := by
  set T := (capLife ρ).toNNReal with hTdef
  have hset : {s : ℝ≥0 | (s : ℝ≥0∞) ≤ capLife ρ} = Iic T := by
    ext s; exact coe_le_capLife_iff hfin s
  rw [hset]
  intro s hs
  rcases (mem_Iic.1 hs).lt_or_eq with hlt | rfl
  · have hlt' : (s : ℝ≥0∞) < capLife ρ := (coe_lt_capLife_iff hfin s).2 hlt
    have heq : capExt ρ z =ᶠ[𝓝 s] capTrace ρ := by
      filter_upwards [Iio_mem_nhds hlt] with s' hs'
      exact capExt_of_lt ((coe_lt_capLife_iff hfin s').2 hs')
    exact ((hρ.continuousAt_capTrace hlt').congr heq.symm).continuousWithinAt
  · rw [← continuousWithinAt_Iio_iff_Iic]
    have hval : capExt ρ z T = z := by
      unfold capExt
      have : ¬ ((T : ℝ≥0∞) < capLife ρ) := fun h => lt_irrefl _ ((coe_lt_capLife_iff hfin T).1 h)
      simp only [this, ↓reduceIte]
    rw [ContinuousWithinAt, hval]
    refine (tendsto_capTrace_left hρ hfin hz).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s' hs'
    exact (capExt_of_lt ((coe_lt_capLife_iff hfin s').2 hs')).symm

end Ext

/-- **A regular driver generating a continuous trace through its finite positive lifetime is continuous there.** -/
theorem continuousOn_driver_of_gen {e₂ : Drv} (hreg : IsRegularDriver e₂) (hfin : e₂.2 ≠ ⊤) (hpos : 0 < e₂.2)
    {α : ℝ≥0 → ℂ} (hg : IsGeneratingTrace e₂.1 e₂.2 α) : ContinuousOn e₂.1 {t | (t : ℝ≥0∞) ≤ e₂.2} := by
  set T := e₂.2.toNNReal with hTdef
  have hT : (T : ℝ≥0∞) = e₂.2 := ENNReal.coe_toNNReal hfin
  have hg' : IsGeneratingTrace e₂.1 (T : ℝ≥0∞) α := by rw [hT]; exact hg
  have hw : ContinuousOn e₂.1 {t | (t : ℝ≥0∞) < (T : ℝ≥0∞)} := by rw [hT]; exact hreg.1
  have hT0 : 0 < T := by
    rw [← ENNReal.coe_lt_coe, hT]; exact hpos
  obtain ⟨c, hc⟩ := Restart.RetEnd.exists_tendsto_driver_of_isGeneratingTrace hg' hw hreg.2.1 hT0
  have hval : e₂.1 T = c := hreg.2.2.2 hfin hpos c hc
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e₂.2} = Iic T := by
    ext t; rw [mem_ofPred_eq, mem_Iic, ← hT, ENNReal.coe_le_coe]
  rw [hset]
  intro t ht
  rcases (mem_Iic.1 ht).lt_or_eq with hlt | rfl
  · have hopen : {s : ℝ≥0 | (s : ℝ≥0∞) < (T : ℝ≥0∞)} ∈ 𝓝 t := by
      have : {s : ℝ≥0 | (s : ℝ≥0∞) < (T : ℝ≥0∞)} = Iio T := by ext s; simp
      rw [this]; exact Iio_mem_nhds hlt
    exact ((hw t (by simpa using hlt)).continuousAt hopen).continuousWithinAt
  · rw [← continuousWithinAt_Iio_iff_Iic, ContinuousWithinAt, hval]
    exact hc

variable {c : Chart} {m : ℝ} {p : ℝ≥0 → ℂ} {L : ℝ≥0∞} {s₂ : ExplState} {e₂ : Drv}

/-- **The relative facts at a finite piece from the stage curve's convergence at `∞`.** -/
theorem stageRelFinP_of (hρ : IsDrivenCurve (stCurvep c m p L s₂))
    (he₂ : e₂.2 = capLife (stCurvep c m p L s₂))
    (hgen : ∀ T < capLife (stCurvep c m p L s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m p L s₂)))
    (hreg : IsRegularDriver e₂) {z : ℂ} (hz : Tendsto (stCurvep c m p L s₂) atTop (𝓝 z))
    (hHbar : ∀ u, 0 ≤ u → stCurvep c m p L s₂ u ∈ Hbar) (hB : HasBdryLimits (stChart s₂).2.1)
    (hcH : ContinuousOn (stChart s₂).2.1 H) (hc1 : ∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w)
    (hdom : ∀ t ∈ goodTp c p L, liftPt c m (p t) ∈ (stChart s₂).2.1 '' H) :
    StageRelFinP c m p L s₂ e₂ := by
  set ρ := stCurvep c m p L s₂ with hρdef
  obtain ⟨r, hr⟩ := exists_closedBall_of_tendsto hρ.continuousOn hz
  have hfin : capLife ρ ≠ ⊤ := capLife_ne_top_of_subset_closedBall hr
  have hpos : 0 < e₂.2 := by rw [he₂]; exact capLife_pos_of_driven hρ
  have hHb : IsClosed Hbar := isClosed_le continuous_const Complex.continuous_im
  have hzH : z ∈ Hbar := hHb.mem_of_tendsto hz ((eventually_ge_atTop 0).mono fun u hu => hHbar u hu)
  have hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → capExt ρ z τ = capTrace ρ τ := fun τ hτ =>
    capExt_of_lt (by rw [← he₂]; exact hτ)
  have hα0 : capExt ρ z 0 = 0 := by
    rw [capExt_of_lt (by rw [ENNReal.coe_zero]; exact capLife_pos_of_driven hρ)]
    exact capTrace_zero' hρ
  have hαc : ContinuousOn (capExt ρ z) {τ | (τ : ℝ≥0∞) ≤ e₂.2} := by
    rw [he₂]; exact continuousOn_capExt hρ hfin hz
  have hαH : ∀ τ : ℝ≥0, capExt ρ z τ ∈ Hbar := fun τ => by
    unfold capExt
    split_ifs
    · exact hHbar _ (capInv_nonneg ρ τ)
    · exact hzH
  have hg := isGeneratingTrace_of_ext he₂ hgen hαeq hα0 hαc
  refine ⟨by rw [he₂]; exact hfin, continuousOn_driver_of_gen hreg (by rw [he₂]; exact hfin) hpos hg,
    ⟨capExt ρ z, extendFrom H (stChart s₂).2.1, hαeq, hα0, hαc, fun τ _ => hB.tendsto (hαH τ),
      hB.continuousOn.comp hαc fun τ _ => hαH τ⟩, hcH, hc1, hdom⟩

/-- A continuous map from `[0, ∞)` to `ℂ` tending to `∞` has a closed range. -/
theorem isClosed_range_of_tendsto_norm {F : ℝ≥0 → ℂ} (hF : Continuous F)
    (htr : Tendsto (fun τ => ‖F τ‖) atTop atTop) : IsClosed (range F) := by
  have hp : IsProperMap F := by
    refine isProperMap_iff_tendsto_cocompact.2 ⟨hF, ?_⟩
    rw [cocompact_eq_atTop, ← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    exact htr
  rw [← image_univ]
  exact hp.isClosedMap _ isClosed_univ

/-- **The relative facts at an infinite piece** from the transience of the stage curve, its infinite capacity
lifetime, and an inverse-chart boundary map within bounded distance of the identity. -/
theorem stageRelInfP_of (hρ : IsDrivenCurve (stCurvep c m p L s₂))
    (he₂ : e₂.2 = capLife (stCurvep c m p L s₂))
    (hreg : IsRegularDriver e₂) (htop : capLife (stCurvep c m p L s₂) = ⊤)
    (htr : Tendsto (fun u => ‖stCurvep c m p L s₂ u‖) atTop atTop)
    (hHbar : ∀ u, 0 ≤ u → stCurvep c m p L s₂ u ∈ Hbar) (hB : HasBdryLimits (stChart s₂).2.1) {C : ℝ}
    (hC : ∀ q ∈ Hbar, ‖extendFrom H (stChart s₂).2.1 q - q‖ ≤ C)
    (hcH : ContinuousOn (stChart s₂).2.1 H) (hc1 : ∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w)
    (hdom : ∀ t ∈ goodTp c p L, liftPt c m (p t) ∈ (stChart s₂).2.1 '' H) :
    StageRelInfP c m p L s₂ e₂ := by
  set ρ := stCurvep c m p L s₂ with hρdef
  have hall : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 := fun τ => by rw [he₂, htop]; exact ENNReal.coe_lt_top
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e₂.2} = univ := eq_univ_of_forall fun t => (hall t).le
  have hset' : {t : ℝ≥0 | (t : ℝ≥0∞) < e₂.2} = univ := eq_univ_of_forall hall
  have hcont : Continuous (capTrace ρ) := continuous_iff_continuousAt.2 fun τ =>
    hρ.continuousAt_capTrace (by rw [htop]; exact ENNReal.coe_lt_top)
  have hαH : ∀ τ : ℝ≥0, capTrace ρ τ ∈ Hbar := fun τ => hHbar _ (capInv_nonneg ρ τ)
  have hfc : Continuous fun τ => extendFrom H (stChart s₂).2.1 (capTrace ρ τ) :=
    continuousOn_univ.1 (hB.continuousOn.comp hcont.continuousOn fun τ _ => hαH τ)
  have htrα := tendsto_norm_capTrace hρ htop htr
  have htrf : Tendsto (fun τ => ‖extendFrom H (stChart s₂).2.1 (capTrace ρ τ)‖) atTop atTop := by
    refine tendsto_atTop_mono (fun τ => ?_) (tendsto_atTop_add_const_right _ (-C) htrα)
    have h1 := hC _ (hαH τ)
    have h2 := norm_sub_norm_le (capTrace ρ τ) (extendFrom H (stChart s₂).2.1 (capTrace ρ τ))
    rw [norm_sub_rev] at h2
    linarith
  refine ⟨by rw [hset, ← hset']; exact hreg.1, ⟨capTrace ρ, extendFrom H (stChart s₂).2.1, fun _ _ => rfl,
    capTrace_zero' hρ, hcont.continuousOn, fun τ _ => hB.tendsto (hαH τ), hfc.continuousOn, ?_⟩, hcH, hc1, hdom⟩
  rw [hset, image_univ]
  exact isClosed_range_of_tendsto_norm hfc htrf

end InteractingSLE.Theorem14.SB.Lk
