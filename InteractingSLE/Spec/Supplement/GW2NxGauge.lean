/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TpRoot

/-!
# The stop gauge: the launch gauge cut off at the candidate's cap

Packet PROVE-GW2-NOTHR (round 6, decision D54: D49 (A)). RELDET's launch gauge (`GW2Rd.launchGaugeC`) dies at the
candidate's death before the cap; it never dies if the candidate outlives its cap. The **stop gauge** is the
minimum of the launch gauge and the remaining own time before the cap, so it dies at the candidate's STOP
`min(cap, life)`:

* `capRestC`: the remaining own time `cap − min(cap, t' − T)` at the physical time `t'` of the relative time `t`;
  `capLife`: its life `a (T + cap)` (before the contact; `⊤` otherwise);
* **`capRestC_sample`**: along one sample, the remaining own time is continuous, positive before `capLife`, zero at
  it, and `0 < capLife` (positive cap);
* **`min_gauge_sample`**: the minimum of two cap gauges is a cap gauge with the minimum life;
* `stopGaugeC`, **`stopGaugeC_sample`**; at a root `x`: `stopGaugeX`, `capLifeX`, `stopLifeX`,
  **`ae_stopGaugeX_coord`** (the cap-gauge hypothesis of ROOTX's `GW2Rv.exists_versionsXA_of_capGauge_strict`);
* **`exists_versionsXA_stopGauge`**: the capped root-`x` family strictly below the stop gauge's life, exhausting the
  root-`x` clock below it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Nx

open Exist Staged StagedLaw Restart Supp8 Supp8.GB6 Supp8.GB6.CoordB Supp8.GB6.ReadD Supp8.GB6.SourceC
  Supp8.GB6.RelDrv Supp8.GB6.RelDrv.Version GW2TipSystem GW2Rz GW2Rd

/-! ### The remaining own time before the cap -/

section Defs

variable (κ θ : ℝ) (B : (ℝ≥0 → ℝ) → BoundaryWord) (T cap : ℝ≥0) (X : ℝ≥0 → RecData × (ℝ≥0 → ℝ) → ℂ)

/-- **The remaining own time before the cap**, read from a read-back physical curve. -/
def capRestC : GaugeReadout := fun t p => ((cap - ownTimeC T cap X t (GW2Rd.frz t p) : ℝ≥0) : ℝ)

/-- **The stop gauge**: the launch gauge cut off at the cap. -/
def stopGaugeC : GaugeReadout := fun t p => min (launchGaugeC κ θ B T cap X t p) (capRestC T cap X t p)

/-- The life of the remaining own time along a clock `a` with contact `Tc`. -/
def capLife (a : ℝ≥0 → ℝ) (Tc : ℝ≥0∞) : ℝ≥0∞ :=
  open scoped Classical in
  if ((T + cap : ℝ≥0) : ℝ≥0∞) < Tc then ENNReal.ofReal (a (T + cap)) else ⊤

end Defs

variable {κ θ : ℝ} {B : (ℝ≥0 → ℝ) → BoundaryWord} {T cap : ℝ≥0} {X : ℝ≥0 → RecData × (ℝ≥0 → ℝ) → ℂ}

theorem measurable_capRestC (hX : ∀ u, Measurable (X u)) (t : ℝ≥0) : Measurable (capRestC T cap X t) :=
  measurable_coe_nnreal_real.comp (measurable_const.sub ((measurable_ownTimeC hX t).comp (measurable_frz t)))

theorem isCausal_capRestC : IsCausal (capRestC T cap X) := by
  intro t r w w' h
  simp only [capRestC, GW2Rd.frz, LP.freezeAt_congr h]

theorem capRestC_nonneg (t : ℝ≥0) (p : RecData × (ℝ≥0 → ℝ)) : 0 ≤ capRestC T cap X t p := NNReal.coe_nonneg _

/-- **The stop gauge is Borel.** -/
theorem measurable_stopGaugeC (hB : Measurable B) (hX : ∀ u, Measurable (X u)) (t : ℝ≥0) :
    Measurable (stopGaugeC κ θ B T cap X t) :=
  (measurable_launchGaugeC hB hX t).min (measurable_capRestC hX t)

/-- **The stop gauge is causal.** -/
theorem isCausal_stopGaugeC : IsCausal (stopGaugeC κ θ B T cap X) := by
  intro t r w w' h
  show min (launchGaugeC κ θ B T cap X t (r, w)) (capRestC T cap X t (r, w)) =
    min (launchGaugeC κ θ B T cap X t (r, w')) (capRestC T cap X t (r, w'))
  rw [isCausal_launchGaugeC t r w w' h, isCausal_capRestC t r w w' h]

theorem stopGaugeC_nonneg (t : ℝ≥0) (p : RecData × (ℝ≥0 → ℝ)) : 0 ≤ stopGaugeC κ θ B T cap X t p :=
  le_min (launchGaugeC_nonneg t p) (capRestC_nonneg t p)

/-! ### Along one sample -/

section Sample

variable {p : RecData × (ℝ≥0 → ℝ)} {a : ℝ≥0 → ℝ} {Tc L : ℝ≥0∞} {γ : ℝ≥0 → ℂ} {W : ℝ≥0 → ℝ}
  (hXcaus : ∀ u r w w', (∀ v ≤ u, w v = w' v) → X u (r, w) = X u (r, w'))

/-- **The minimum of two cap gauges** is a cap gauge with the minimum life. -/
theorem min_gauge_sample {g₁ g₂ : ℝ≥0 → ℝ} {L₁ L₂ : ℝ≥0∞} (hg₁ : ∀ t, 0 ≤ g₁ t) (hg₂ : ∀ t, 0 ≤ g₂ t)
    (h₁ : 0 < L₁ ∧ ContinuousOn g₁ {t | (t : ℝ≥0∞) < L} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < L → (t : ℝ≥0∞) < L₁ → 0 < g₁ t) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < L → (t : ℝ≥0∞) = L₁ → g₁ t = 0)
    (h₂ : 0 < L₂ ∧ ContinuousOn g₂ {t | (t : ℝ≥0∞) < L} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < L → (t : ℝ≥0∞) < L₂ → 0 < g₂ t) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < L → (t : ℝ≥0∞) = L₂ → g₂ t = 0) :
    0 < min L₁ L₂ ∧ ContinuousOn (fun t => min (g₁ t) (g₂ t)) {t | (t : ℝ≥0∞) < L} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < L → (t : ℝ≥0∞) < min L₁ L₂ → 0 < min (g₁ t) (g₂ t)) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < L → (t : ℝ≥0∞) = min L₁ L₂ → min (g₁ t) (g₂ t) = 0 := by
  obtain ⟨hp₁, hc₁, hpos₁, hz₁⟩ := h₁
  obtain ⟨hp₂, hc₂, hpos₂, hz₂⟩ := h₂
  refine ⟨lt_min hp₁ hp₂, hc₁.inf hc₂, fun t ht hlt => ?_, fun t ht heq => ?_⟩
  · exact lt_min (hpos₁ t ht (hlt.trans_le (min_le_left _ _))) (hpos₂ t ht (hlt.trans_le (min_le_right _ _)))
  · rcases min_choice L₁ L₂ with h | h
    · rw [h] at heq
      exact le_antisymm ((min_le_left _ _).trans (hz₁ t ht heq).le) (le_min (hg₁ t) (hg₂ t))
    · rw [h] at heq
      exact le_antisymm ((min_le_right _ _).trans (hz₂ t ht heq).le) (le_min (hg₁ t) (hg₂ t))

include hXcaus in
/-- **The remaining own time along one sample of relative coordinates**: continuous before the life, positive before
`capLife` and zero at it, and `0 < capLife` (for a positive cap). -/
theorem capRestC_sample (hcap : 0 < cap)
    (hγ : IsGeneratingTrace W ⊤ γ) (hW : Continuous W) (hW0 : W 0 = 0) (ha0 : a 0 = 0)
    (ham : StrictMonoOn a {t | (t : ℝ≥0∞) < Tc})
    (haL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ a t ∧ ENNReal.ofReal (a t) < L)
    (hback : ∀ u : ℝ≥0, (u : ℝ≥0∞) < L → ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ a t = u)
    (hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → X (a t).toNNReal p = γ t)
    (hXc : ContinuousOn (fun u => X u p) {u | (u : ℝ≥0∞) < L}) :
    0 < capLife T cap a Tc ∧
      ContinuousOn (fun t => capRestC T cap X t p) {t | (t : ℝ≥0∞) < L} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < L → (t : ℝ≥0∞) < capLife T cap a Tc → 0 < capRestC T cap X t p) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < L → (t : ℝ≥0∞) = capLife T cap a Tc → capRestC T cap X t p = 0 := by
  classical
  obtain ⟨r, w⟩ := p
  set ψ : ℝ≥0 → ℝ≥0 := fun t => (capT X t (r, w)).toNNReal with hψdef
  have hψ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < L → (ψ t : ℝ≥0∞) < Tc ∧ a (ψ t) = t := by
    intro t ht
    obtain ⟨t', ht', hat⟩ := hback t ht
    have he : ψ t = t' := by
      simp only [hψdef, capT_eq hW hW0 hγ ham hback hread hXc ht ht' hat, Real.toNNReal_coe]
    rw [he]
    exact ⟨ht', hat⟩
  have hrep : ∀ t : ℝ≥0, capRestC T cap X t (r, w) = ((cap - min cap (ψ t - T) : ℝ≥0) : ℝ) := by
    intro t
    simp only [capRestC, ownTimeC, GW2Rd.frz, hψdef]
    rw [capT_freeze hXcaus r w t le_rfl]
  have hTc0 : 0 < T + cap := lt_of_lt_of_le hcap le_add_self
  -- the remaining own time is positive iff the physical time is before `T + cap`
  have hposiff : ∀ t : ℝ≥0, ψ t < T + cap → 0 < ((cap - min cap (ψ t - T) : ℝ≥0) : ℝ) := by
    intro t hlt
    have h1 : ψ t - T < cap := by
      by_cases hT : T ≤ ψ t
      · rw [tsub_lt_iff_left hT]
        exact hlt
      · rw [tsub_eq_zero_of_le (le_of_lt (not_le.1 hT))]
        exact hcap
    rw [min_eq_right h1.le]
    exact NNReal.coe_pos.2 (tsub_pos_of_lt h1)
  refine ⟨?_, ?_, fun t ht hlt => ?_, fun t ht heq => ?_⟩
  · -- the life is positive
    unfold capLife
    split_ifs with hc
    · have h0Tc : ((0 : ℝ≥0) : ℝ≥0∞) < Tc := (ENNReal.coe_le_coe.2 zero_le).trans_lt hc
      have := ham h0Tc hc hTc0
      rw [ha0] at this
      exact ENNReal.ofReal_pos.2 this
    · exact ENNReal.zero_lt_top
  · -- continuity
    have hψc := continuousOn_invClock ham haL hψ
    have hσc : ContinuousOn (fun t => ((cap - min cap (ψ t - T) : ℝ≥0) : ℝ)) {t | (t : ℝ≥0∞) < L} :=
      NNReal.continuous_coe.comp_continuousOn
        ((continuous_const.sub (continuous_const.min (continuous_id.sub continuous_const))).comp_continuousOn hψc)
    exact hσc.congr fun t _ => hrep t
  · -- positivity before the life
    rw [hrep t]
    refine hposiff t ?_
    unfold capLife at hlt
    split_ifs at hlt with hc
    · by_contra hge
      have h1 : a (T + cap) ≤ a (ψ t) := ham.monotoneOn hc (hψ t ht).1 (not_lt.1 hge)
      rw [(hψ t ht).2] at h1
      have h2 : ENNReal.ofReal (a (T + cap)) ≤ (t : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal h1
      exact absurd hlt (not_lt.2 h2)
    · have h1 : (ψ t : ℝ≥0∞) < ((T + cap : ℝ≥0) : ℝ≥0∞) := (hψ t ht).1.trans_le (not_lt.1 hc)
      exact ENNReal.coe_lt_coe.1 h1
  · -- zero at the life
    have hne : capLife T cap a Tc ≠ ⊤ := heq ▸ ENNReal.coe_ne_top
    have hc : ((T + cap : ℝ≥0) : ℝ≥0∞) < Tc := by
      by_contra hc
      unfold capLife at hne
      rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at hne
      exact hne rfl
    unfold capLife at heq
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at heq
    have hat : a (T + cap) = t := by
      have h0 := (haL _ hc).1
      have h1 : ENNReal.ofReal (a (T + cap)) = ENNReal.ofReal (t : ℝ) := by
        rw [ENNReal.ofReal_coe_nnreal]; exact heq.symm
      exact (ENNReal.ofReal_eq_ofReal_iff h0 t.coe_nonneg).1 h1
    have hψt : ψ t = T + cap := by
      refine ham.injOn (hψ t ht).1 hc ?_
      rw [(hψ t ht).2, hat]
    rw [hrep t, hψt, add_tsub_cancel_left, min_self, tsub_self, NNReal.coe_zero]

include hXcaus in
/-- **The stop gauge along one sample of relative coordinates** (any root): continuous before the life, positive
before `min (launchLife) (capLife)` and zero at it, with a positive life. -/
theorem stopGaugeC_sample (hcap : 0 < cap) (hBc : ∀ w : ℝ≥0 → ℝ, (∀ u ≤ T, w u = W u) → B w = B W)
    (hγ : IsGeneratingTrace W ⊤ γ) (hW : Continuous W) (hW0 : W 0 = 0) (ha0 : a 0 = 0)
    (ham : StrictMonoOn a {t | (t : ℝ≥0∞) < Tc})
    (haL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ a t ∧ ENNReal.ofReal (a t) < L)
    (hback : ∀ u : ℝ≥0, (u : ℝ≥0∞) < L → ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ a t = u)
    (hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → X (a t).toNNReal p = γ t)
    (hXc : ContinuousOn (fun u => X u p) {u | (u : ℝ≥0∞) < L}) :
    0 < min (launchLife κ θ B T cap W a Tc) (capLife T cap a Tc) ∧
      ContinuousOn (fun t => stopGaugeC κ θ B T cap X t p) {t | (t : ℝ≥0∞) < L} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < L → (t : ℝ≥0∞) < min (launchLife κ θ B T cap W a Tc) (capLife T cap a Tc) →
        0 < stopGaugeC κ θ B T cap X t p) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < L → (t : ℝ≥0∞) = min (launchLife κ θ B T cap W a Tc) (capLife T cap a Tc) →
        stopGaugeC κ θ B T cap X t p = 0 :=
  min_gauge_sample (fun t => launchGaugeC_nonneg t p) (fun t => capRestC_nonneg t p)
    (launchGaugeC_sample hXcaus hBc hγ hW hW0 ha0 ham haL hback hread hXc)
    (capRestC_sample hXcaus hcap hγ hW hW0 ha0 ham haL hback hread hXc)

end Sample

/-! ### At a root `x` -/

section Root

variable (κ θ : ℝ) (B : (ℝ≥0 → ℝ) → BoundaryWord) (T cap : ℝ≥0) (x : ℝ) (s : ℝ≥0)

/-- **The stop gauge at the root `x`.** -/
abbrev stopGaugeX : GaugeReadout := stopGaugeC κ θ B T cap (launchReadX x s)

/-- The life of the remaining own time along the root-`x` clock. -/
abbrev capLifeX {Ω : Type*} (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (w : ℝ≥0 → Ω → ℝ) (γ α : Ω → ℝ≥0 → ℂ)
    (ω : Ω) : ℝ≥0∞ :=
  capLife T cap (fun t => clockX x s W' ζ' w t ω) (contactX x s γ α ω)

/-- **The life of the stop gauge along the root-`x` clock**: the launch gauge's life cut off at the cap. -/
abbrev stopLifeX {Ω : Type*} (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (w : ℝ≥0 → Ω → ℝ) (γ α : Ω → ℝ≥0 → ℂ)
    (ω : Ω) : ℝ≥0∞ :=
  min (launchLifeX κ θ B T cap x s W' ζ' w γ α ω) (capLifeX T cap x s W' ζ' w γ α ω)

variable {κ θ B T cap x s}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κc θc : ℝ} {bc : ℝ → ℝ} {Jc : Finset ℝ} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
  {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ} {w : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ}

/-- **The root-`x` stop gauge along every root-`x` coordinate process** (the cap-gauge hypothesis of
`GW2Rv.exists_versionsXA_of_capGauge_strict`). -/
theorem ae_stopGaugeX_coord (hF : IsFlowLineDriver κc bc Jc θc P h W' ζ')
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (W' · ω) (ζ' ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζ' ω → α' v ≠ 0)
    (hcf : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ Continuous (W' · ω) ∧ W' 0 ω = 0)
    (hwc : ∀ ω, Continuous (w · ω)) (hw0 : ∀ ω, w 0 ω = 0)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (w · ω) ⊤ (γ ω)) (hs : 0 < s) (hx : 0 ≤ x) (hcap : 0 < cap)
    (hBc : ∀ ω, ∀ v : ℝ≥0 → ℝ, (∀ u ≤ T, v u = w u ω) → B v = B (w · ω))
    {D : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞} (hC : CoordX x s P W' ζ' w γ α D L) :
    ∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → 0 < stopLifeX κ θ B T cap x s W' ζ' w γ α ω ∧
      ContinuousOn (fun t => stopGaugeX κ θ B T cap x s t (cfRec s W' ζ' ω, fun u => D u ω))
        {t | (t : ℝ≥0∞) < L ω} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (t : ℝ≥0∞) < stopLifeX κ θ B T cap x s W' ζ' w γ α ω →
        0 < stopGaugeX κ θ B T cap x s t (cfRec s W' ζ' ω, fun u => D u ω)) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (t : ℝ≥0∞) = stopLifeX κ θ B T cap x s W' ζ' w γ α ω →
        stopGaugeX κ θ B T cap x s t (cfRec s W' ζ' ω, fun u => D u ω) = 0 := by
  filter_upwards [ae_readbackX hF hα hNR hcf hwc hw0 hγ hs hx hC, hγ] with ω hrb hγω hm
  obtain ⟨h0, hmono, -, haL, hread, hback, hXc⟩ := hrb hm
  refine stopGaugeC_sample (launchReadX_congr x s) hcap (hBc ω) hγω (hwc ω) (hw0 ω) h0 hmono haL hback
    (fun t ht => ?_) ?_
  · unfold launchReadX
    rw [hread t ht, add_sub_cancel_left]
  · change ContinuousOn (fun u => physicalTraceX x s u (cfRec s W' ζ' ω, fun v => D v ω) - (x : ℂ)) _
    exact hXc.sub continuousOn_const

/-- **The capped root-`x` family below the stop gauge's life** (any root-`x` instance, positive cap). -/
theorem exists_versionsXA_stopGauge (hF : IsFlowLineDriver κc bc Jc θc P h W' ζ')
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (W' · ω) (ζ' ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζ' ω → α' v ≠ 0)
    (hcf : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ Continuous (W' · ω) ∧ W' 0 ω = 0)
    (hwm : ∀ t, Measurable (w t)) (hwc : ∀ ω, Continuous (w · ω)) (hw0 : ∀ ω, w 0 ω = 0)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (w · ω) ⊤ (γ ω) ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (hs : 0 < s) (hx : 0 ≤ x) (hB : Measurable B) (hcap : 0 < cap)
    (hBc : ∀ ω, ∀ v : ℝ≥0 → ℝ, (∀ u ≤ T, v u = w u ω) → B v = B (w · ω)) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, IsRelVersionXA x s P W' ζ' w γ α (R n) (V n)) ∧ (∀ n ω, V n ω ≤ V (n + 1) ω) ∧
      (∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → ∀ n, V n ω < V (n + 1) ω) ∧ (∀ n ω, V n ω ≠ ⊤) ∧
      (∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → ∀ n, V n ω < stopLifeX κ θ B T cap x s W' ζ' w γ α ω) ∧
      ∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ α ω →
        ENNReal.ofReal (clockX x s W' ζ' w t ω) < stopLifeX κ θ B T cap x s W' ζ' w γ α ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX x s W' ζ' w t ω) < V n ω := by
  obtain ⟨R₀, V₀, hRV₀, hst₀, hlt₀, hex₀⟩ := GW2Rv.exists_versionsXA_of_capGauge_strict hF hα hNR hcf hwm hwc hw0
    hγ hs hx (Gζ := stopGaugeX κ θ B T cap x s) (measurable_stopGaugeC hB (measurable_launchReadX x s))
    isCausal_stopGaugeC stopGaugeC_nonneg (Lζ := stopLifeX κ θ B T cap x s W' ζ' w γ α)
    fun _ _ hC => ae_stopGaugeX_coord hF hα hNR hcf hwc hw0 (hγ.mono fun _ h => h.1) hs hx hcap hBc hC
  obtain ⟨R, V, hRV, hmono, hstrict, hle, hfin, hex⟩ := GW2Rv.exists_finite_family_strictX hRV₀
    (fun ω => (hst₀ ω).monotone) (ae_of_all _ fun ω _ => hst₀ ω) (measurable_recOf_cfE hF s).2
  refine ⟨R, V, hRV, fun n ω => hmono ω (Nat.le_succ n), hstrict.mono fun ω hω hm n => hω hm (Nat.lt_succ_self n),
    hfin, ?_, ?_⟩
  · filter_upwards [hlt₀] with ω hω hm n
    exact (hle n ω).trans_lt (hω hm n)
  · filter_upwards [hex₀] with ω hω hm t ht htl
    obtain ⟨m, hm'⟩ := hω hm t ht htl
    exact hex ω _ ENNReal.ofReal_ne_top m hm'

end Root

end InteractingSLE.Theorem14.GW2Nx
