/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactBdryLimit
import InteractingSLE.WangWu.MeanIdentChamber

/-!
# The orientation of the two-slit chart: a separating arc

Packet PROVE-WW-B14 (the deterministic half of the contact step's N3). Setting of `ReverseContactBdryLimit`: the
forward slit `A = α((0, t])`, the reflected reverse slit `G = R(β((0, s]))`, the chart `Ψ` of `ℍ \ G`, the image trace
`η'` of `Ψ(A)` and the two-slit chart `Φ = Ψ⁻¹ ∘ F'_T : ℍ → C = ℍ \ (A ∪ G)`.

In the `f_t`-plane of the forward slit (`f_t = g^α_t − W^α_t`), the map `Θ⁻¹ = f_t ∘ Φ` sends `ℍ` onto `ℍ \ f_t(G)`.
The **separating arc** `Γ = Θ⁻¹(iℝ₊) ∪ f_t(G)` (`sepArc`: `Θ⁻¹(i u/(1−u))` for `u ∈ (0, 1)`, then `f_t(R(β(s/u)))`
for `u ≥ 1`) is a simple proper arc from `0` (the image of the tip `α(t)`) to `∞`, through the image of the tip `R(β(s))`
of `G`. The left quadrant `{Re y < 0}` is connected and avoids `iℝ₊`, so its image lies on one side of `Γ`; near the
image of a negative real point it is on the left. Hence (`fwdMap_twoSlitChart_mem_leftSideOf`) `f_t(Φ(y))` lies on the
left of `Γ` when `Re y < 0`, and (mirror) on the right when `Re y > 0`.

* `tendsto_fwdMap_tip`: `f_t(z) → 0` as `z → α(t)` in `ℍ \ A` (the tip is a single prime end,
  `eq_zero_of_extendFrom_eq_tip`).
* `tendsto_twoSlitChart_I_zero`, `tendsto_twoSlitChart_I_atTop`: `Φ(iy) → α(t)` as `y ↓ 0` and `Φ(iy) → R(β(s))` as
  `y → ∞`.
* **`isProperArc_sepArc`**.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.WangWu

variable {Wα Wβ W' : ℝ → ℝ} {α β η' : ℝ → ℂ} {t s T : ℝ}

/-! ### Three limits -/

/-- **The tip of a simple trace is a single prime end**: `f_t(z) → 0` as `z → α(t)` in `ℍ \ K_t`. -/
theorem tendsto_fwdMap_tip (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α) (hWα : Continuous Wα)
    (hWα0 : Wα 0 = 0) (ht : 0 < t) : Tendsto (fwdMap Wα t) (𝓝[H \ fwdHull Wα t] (α t)) (𝓝 0) := by
  rw [Filter.tendsto_iff_ultrafilter]
  intro U hU
  obtain ⟨y, hyH, hy, hFy⟩ := exists_tendsto_fwdMap_ultrafilter hα hWα hWα0 ht.le subset_rfl U hU
  have htK : α t ∈ fwdHull Wα t := by
    rw [fwdHull_eq_image_Ioc hα hαp ht.le]; exact ⟨t, ⟨ht, le_rfl⟩, rfl⟩
  have hyim : y.im = 0 := by
    refine le_antisymm (not_lt.1 fun hpos => ?_) hyH
    have := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWα hWα0 ht.le (show y ∈ H from hpos)
    rw [← extendFrom_fwdMapInv_eq hWα hWα0 ht.le hpos, hFy] at this
    exact this.2 htK
  have hyeq : y = ((y.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hyim])
  rw [hyeq] at hFy
  have h0 := eq_zero_of_extendFrom_eq_tip hα hαp hWα hWα0 ht hFy
  rw [hyeq, h0, Complex.ofReal_zero] at hy
  exact hy

/-- `Φ(iy) → α(t)` as `y ↓ 0`: the imaginary axis starts at the tip. -/
theorem tendsto_twoSlitChart_I_zero (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hη' : IsLoewnerTrace W' η') (hT : 0 ≤ T)
    (htip : η' T = revChart Wβ s (α t)) (hαt : α t ∈ H \ negInv '' fwdHull Wβ s) :
    Tendsto (fun y : ℝ => twoSlitChart Wβ s W' T ((y : ℂ) * I)) (𝓝[>] 0) (𝓝 (α t)) := by
  have h1 : Tendsto (fun y : ℝ => fwdMapInv W' T ((y : ℂ) * I)) (𝓝[>] 0) (𝓝 (η' T)) := by
    have h := ((hη'.hasBdryLimits hW' hW'0 hT).tendsto zero_mem_Hbar).comp tendsto_ofReal_mul_I_nhdsWithin_H
    rwa [extendFrom_zero hη' hW' hW'0 hT] at h
  rw [htip] at h1
  have hRH : revChart Wβ s (α t) ∈ H := revChart_mem_H hWβ hs hαt
  have h2 : ContinuousAt (revChartInv Wβ s) (revChart Wβ s (α t)) :=
    (continuousOn_revChartInv hWβ hWβ0 hs).continuousAt (QuantumZipper.isOpen_H.mem_nhds hRH)
  have h3 := h2.tendsto.comp h1
  rwa [revChartInv_revChart hWβ hWβ0 hs hαt] at h3

/-- `Φ(iy) → R(β(s))` as `y → ∞`: the imaginary axis ends at the tip of the reversed slit. -/
theorem tendsto_twoSlitChart_I_atTop (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hβ : IsLoewnerTrace Wβ β)
    (hβp : IsProperArc β) (hs : 0 < s) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hT : 0 ≤ T) :
    Tendsto (fun y : ℝ => twoSlitChart Wβ s W' T ((y : ℂ) * I)) atTop (𝓝 (negInv (β s))) := by
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW' hW'0 hT
  -- `F'(iy) → ∞`, so `R(F'(iy)) → 0` in `ℍ`
  have hR : Tendsto (fun y : ℝ => negInv (fwdMapInv W' T ((y : ℂ) * I))) atTop (𝓝[H] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [eventually_gt_atTop (|C| + 1 / ε + 1)] with y hy
      have hy0 : 0 < y := by linarith [abs_nonneg C, (by positivity : (0 : ℝ) < 1 / ε)]
      have hw : (y : ℂ) * I ∈ H := show (0 : ℝ) < ((y : ℂ) * I).im by simpa using hy0
      have h1 := hC _ hw
      have hn : ‖(y : ℂ) * I‖ = y := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
      have h2 : y - C ≤ ‖fwdMapInv W' T ((y : ℂ) * I)‖ := by
        have := norm_sub_norm_le ((y : ℂ) * I) ((y : ℂ) * I - fwdMapInv W' T ((y : ℂ) * I))
        rw [sub_sub_cancel, norm_sub_rev, hn] at this
        linarith
      have h3 : 1 / ε < ‖fwdMapInv W' T ((y : ℂ) * I)‖ := by linarith [le_abs_self C]
      rw [dist_zero_right, negInv, norm_neg, norm_inv]
      calc ‖fwdMapInv W' T ((y : ℂ) * I)‖⁻¹ < (1 / ε)⁻¹ := inv_strictAnti₀ (by positivity) h3
        _ = ε := by rw [one_div, inv_inv]
    · filter_upwards [eventually_gt_atTop 0] with y hy
      have hw : (y : ℂ) * I ∈ H := show (0 : ℝ) < ((y : ℂ) * I).im by simpa using hy
      exact negInv_mem_H (QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT hw)
  have h1 : Tendsto (fun y : ℝ => fwdMapInv Wβ s (negInv (fwdMapInv W' T ((y : ℂ) * I)))) atTop (𝓝 (β s)) := by
    have h := ((hβ.hasBdryLimits hWβ hWβ0 hs.le).tendsto zero_mem_Hbar).comp hR
    rwa [extendFrom_zero hβ hWβ hWβ0 hs.le] at h
  have hβs : β s ≠ 0 := fun h => by
    have := hβp.mem_H s hs; rw [h] at this
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
  exact (continuousAt_negInv hβs).tendsto.comp h1

/-! ### The separating arc -/

/-- The **separating arc** `Γ` in the `f_t`-plane: `f_t(Φ(i u/(1 − u)))` for `u ∈ (0, 1)`, then `f_t(R(β(s/u)))` for
`u ≥ 1`. -/
def sepArc (Wα : ℝ → ℝ) (t : ℝ) (Wβ : ℝ → ℝ) (s : ℝ) (β : ℝ → ℂ) (W' : ℝ → ℝ) (T : ℝ) (u : ℝ) : ℂ :=
  if u ≤ 0 then 0
  else if u < 1 then fwdMap Wα t (twoSlitChart Wβ s W' T (((u / (1 - u) : ℝ) : ℂ) * I))
  else fwdMap Wα t (negInv (β (s / u)))

theorem ofReal_mul_I_mem_H {y : ℝ} (hy : 0 < y) : (y : ℂ) * I ∈ H :=
  show (0 : ℝ) < ((y : ℂ) * I).im by simpa using hy

theorem injOn_twoSlitChart (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hW' : Continuous W')
    (hW'0 : W' 0 = 0) (hT : 0 ≤ T) : InjOn (twoSlitChart Wβ s W' T) H := by
  intro y hy y' hy' e
  have h1 := (isConformalBijection_revChartInv hWβ hWβ0 hs).2.injOn
    (QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT hy) (QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT hy') e
  rw [← QuantumZipper.RS.fwdMap_fwdMapInv hW' hW'0 hT hy, h1, QuantumZipper.RS.fwdMap_fwdMapInv hW' hW'0 hT hy']

theorem injOn_fwdMap (hW : Continuous Wα) (hW0 : Wα 0 = 0) (ht : 0 ≤ t) : InjOn (fwdMap Wα t) (H \ fwdHull Wα t) :=
  fun z hz z' hz' e => by
    rw [← QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 ht hz, e, QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 ht hz']

theorem continuousAt_fwdMap {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ H \ fwdHull W t) : ContinuousAt (fwdMap W t) z :=
  (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ht).continuousOn.continuousAt
    ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW ht).mem_nhds hz)

theorem continuousAt_twoSlitChart (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hW' : Continuous W')
    (hW'0 : W' 0 = 0) (hT : 0 ≤ T) {y : ℂ} (hy : y ∈ H) : ContinuousAt (twoSlitChart Wβ s W' T) y := by
  have hF := QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT hy
  have h1 : ContinuousAt (fwdMapInv W' T) y :=
    (continuousOn_fwdMapInv hW' hW'0 hT).continuousAt (QuantumZipper.isOpen_H.mem_nhds hy)
  have h2 : ContinuousAt (revChartInv Wβ s) (fwdMapInv W' T y) :=
    (continuousOn_revChartInv hWβ hWβ0 hs).continuousAt (QuantumZipper.isOpen_H.mem_nhds hF)
  exact h2.comp h1

theorem tendsto_div_one_sub_nhdsGT : Tendsto (fun u : ℝ => u / (1 - u)) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h : ContinuousAt (fun u : ℝ => u / (1 - u)) 0 :=
      continuousAt_id.div (continuousAt_const.sub continuousAt_id) (by norm_num)
    have h2 := h.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using h2
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
    exact div_pos hu.1 (by linarith [hu.2])

theorem tendsto_div_one_sub_atTop : Tendsto (fun u : ℝ => u / (1 - u)) (𝓝[<] 1) atTop := by
  have h1 : Tendsto (fun v : ℝ => 1 - v) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : Continuous (fun v : ℝ => 1 - v) := continuous_const.sub continuous_id
      have h := (hc.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
      rwa [sub_self] at h
    · filter_upwards [self_mem_nhdsWithin] with v hv
      exact sub_pos.2 (show v < 1 from hv)
  have h3 := tendsto_atTop_add_const_right _ (-1) (tendsto_inv_nhdsGT_zero.comp h1)
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  have : 1 - v ≠ 0 := (sub_pos.2 hv).ne'
  simp only [Function.comp_apply]
  field_simp
  ring

/-- **The separating arc is a simple proper arc** from `0` to `∞`. -/
theorem isProperArc_sepArc (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α) (hWα : Continuous Wα)
    (hWα0 : Wα 0 = 0) (ht : 0 < t) (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hβ : IsLoewnerTrace Wβ β)
    (hβp : IsProperArc β) (hs : 0 < s) (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hη' : IsLoewnerTrace W' η') (hT : 0 < T)
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) (htip : η' T = revChart Wβ s (α t)) :
    IsProperArc (sepArc Wα t Wβ s β W' T) := by
  set Γ := sepArc Wα t Wβ s β W' T with hΓ
  set ι : ℝ → ℂ := fun u => (((u / (1 - u) : ℝ) : ℂ) * I) with hιdef
  have hι : ∀ u ∈ Ioo (0 : ℝ) 1, ι u ∈ H := fun u hu =>
    ofReal_mul_I_mem_H (div_pos hu.1 (by linarith [hu.2]))
  have hΦC : ∀ y ∈ H, twoSlitChart Wβ s W' T y ∈ H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s) :=
    fun y hy => twoSlitChart_mem hWβ hWβ0 hs.le hW' hW'0 hT.le hK' hy
  have hCA : ∀ z ∈ H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s), z ∈ H \ fwdHull Wα t :=
    fun z hz => ⟨hz.1, fun h => hz.2 (Or.inl h)⟩
  have hGH : negInv '' fwdHull Wβ s ⊆ H := fun z ⟨w, hw, e⟩ => e ▸ negInv_mem_H hw.1
  have hGA : ∀ g ∈ negInv '' fwdHull Wβ s, g ∈ H \ fwdHull Wα t :=
    fun g hg => ⟨hGH hg, fun h => disjoint_left.1 hdisj h hg⟩
  have hβG : ∀ u, 1 ≤ u → negInv (β (s / u)) ∈ negInv '' fwdHull Wβ s := fun u hu => by
    refine ⟨β (s / u), ?_, rfl⟩
    rw [fwdHull_eq_image_Ioc hβ hβp hs.le]
    exact ⟨s / u, ⟨div_pos hs (by linarith), div_le_self hs.le hu⟩, rfl⟩
  have hαt : α t ∈ H \ negInv '' fwdHull Wβ s := ⟨hαp.mem_H t ht, fun h => disjoint_left.1 hdisj
    (by rw [fwdHull_eq_image_Ioc hα hαp ht.le]; exact ⟨t, ⟨ht, le_rfl⟩, rfl⟩) h⟩
  have hΓ0 : Γ 0 = 0 := by simp [hΓ, sepArc]
  have hΓ1 : ∀ u ∈ Ioo (0 : ℝ) 1, Γ u = fwdMap Wα t (twoSlitChart Wβ s W' T (ι u)) := fun u hu => by
    simp only [hΓ, sepArc, not_le.2 hu.1, hu.2, ↓reduceIte, hιdef]
  have hΓ2 : ∀ u, 1 ≤ u → Γ u = fwdMap Wα t (negInv (β (s / u))) := fun u hu => by
    simp only [hΓ, sepArc, show ¬ u ≤ 0 by linarith, not_lt.2 hu, ↓reduceIte]
  have hιc : ∀ u, u ≠ 1 → ContinuousAt ι u := fun u hu =>
    ((Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_id.div (continuousAt_const.sub continuousAt_id) (sub_ne_zero.2 hu.symm))).mul
      continuousAt_const)
  have hβc : ∀ u, 1 ≤ u → ContinuousAt (fun v => fwdMap Wα t (negInv (β (s / v)))) u := by
    intro u hu
    have hsu : 0 < s / u := div_pos hs (by linarith)
    have h1 : ContinuousAt (fun v : ℝ => s / v) u := continuousAt_const.div continuousAt_id (by linarith)
    have h2 : ContinuousAt β (s / u) := hβp.cont.continuousAt (Ici_mem_nhds hsu)
    have hne : β (s / u) ≠ 0 := fun h => by
      have := hβp.mem_H _ hsu; rw [h] at this
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
    have h3 := continuousAt_negInv hne
    have h4 := continuousAt_fwdMap hWα ht.le (hGA _ (hβG u hu))
    have h21 : ContinuousAt (fun v : ℝ => β (s / v)) u := h2.comp h1
    have h321 : ContinuousAt (fun v : ℝ => negInv (β (s / v))) u :=
      ContinuousAt.comp (g := negInv) (f := fun v : ℝ => β (s / v)) h3 h21
    exact ContinuousAt.comp (g := fwdMap Wα t) (f := fun v : ℝ => negInv (β (s / v))) h4 h321
  refine ⟨?_, ?_, hΓ0, ?_, ?_⟩
  · -- continuity
    intro u hu
    rcases (mem_Ici.1 hu).eq_or_lt with h0 | hpos
    · rw [← h0]
      refine continuousWithinAt_Ioi_iff_Ici.1 ?_
      show Tendsto Γ (𝓝[>] 0) (𝓝 (Γ 0))
      rw [hΓ0]
      have h2 := (tendsto_twoSlitChart_I_zero hWβ hWβ0 hs.le hW' hW'0 hη' hT.le htip hαt).comp
        tendsto_div_one_sub_nhdsGT
      have h3 : Tendsto (fun u => twoSlitChart Wβ s W' T (ι u)) (𝓝[>] 0) (𝓝[H \ fwdHull Wα t] (α t)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨h2, ?_⟩
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with v hv
        exact hCA _ (hΦC _ (hι v hv))
      refine ((tendsto_fwdMap_tip hα hαp hWα hWα0 ht).comp h3).congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with v hv
      exact (hΓ1 v hv).symm
    · rcases lt_trichotomy u 1 with h1 | h1 | h1
      · have hc1 : ContinuousAt (fun v => twoSlitChart Wβ s W' T (ι v)) u :=
          ContinuousAt.comp (g := twoSlitChart Wβ s W' T) (f := ι)
            (continuousAt_twoSlitChart hWβ hWβ0 hs.le hW' hW'0 hT.le (hι u ⟨hpos, h1⟩)) (hιc u h1.ne)
        have hc : ContinuousAt (fun v => fwdMap Wα t (twoSlitChart Wβ s W' T (ι v))) u :=
          ContinuousAt.comp (g := fwdMap Wα t) (f := fun v => twoSlitChart Wβ s W' T (ι v))
            (continuousAt_fwdMap hWα ht.le (hCA _ (hΦC _ (hι u ⟨hpos, h1⟩)))) hc1
        refine (hc.congr ?_).continuousWithinAt
        filter_upwards [Ioo_mem_nhds hpos h1] with v hv
        exact (hΓ1 v hv).symm
      · subst h1
        have hcR : ContinuousWithinAt Γ (Ici 1) 1 :=
          ((hβc 1 le_rfl).continuousWithinAt).congr (fun v hv => hΓ2 v hv) (hΓ2 1 le_rfl)
        have hcL : ContinuousWithinAt Γ (Iic 1) 1 := by
          refine continuousWithinAt_Iio_iff_Iic.1 ?_
          show Tendsto Γ (𝓝[<] 1) (𝓝 (Γ 1))
          rw [hΓ2 1 le_rfl, div_one]
          have h2 := (tendsto_twoSlitChart_I_atTop hWβ hWβ0 hβ hβp hs hW' hW'0 hT.le).comp
            tendsto_div_one_sub_atTop
          have h3 := (continuousAt_fwdMap hWα ht.le (hGA _ (by simpa using hβG 1 le_rfl))).tendsto.comp h2
          refine h3.congr' ?_
          filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with v hv
          exact (hΓ1 v hv).symm
        exact (continuousAt_iff_continuous_left_right.2 ⟨hcL, hcR⟩).continuousWithinAt
      · refine ((hβc u h1.le).congr ?_).continuousWithinAt
        filter_upwards [Ioi_mem_nhds h1] with v hv
        exact (hΓ2 v hv.le).symm
  · -- injectivity
    have hval : ∀ u, 0 < u → (u < 1 ∧ Γ u ∈ fwdMap Wα t '' (H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s))) ∨
        (1 ≤ u ∧ Γ u ∈ fwdMap Wα t '' negInv '' fwdHull Wβ s) := fun u hu => by
      rcases lt_or_ge u 1 with h1 | h1
      · exact Or.inl ⟨h1, _, hΦC _ (hι u ⟨hu, h1⟩), (hΓ1 u ⟨hu, h1⟩).symm⟩
      · exact Or.inr ⟨h1, _, hβG u h1, (hΓ2 u h1).symm⟩
    have hΓH : ∀ u, 0 < u → Γ u ∈ H := fun u hu => by
      rcases hval u hu with ⟨-, z, hz, e⟩ | ⟨-, z, hz, e⟩
      · rw [← e]; exact QuantumZipper.FwdHolo.mapsTo_fwdMap hWα ht.le (hCA _ hz)
      · rw [← e]; exact QuantumZipper.FwdHolo.mapsTo_fwdMap hWα ht.le (hGA _ hz)
    intro a ha b hb e
    rcases (mem_Ici.1 ha).eq_or_lt with ha0 | ha0 <;> rcases (mem_Ici.1 hb).eq_or_lt with hb0 | hb0
    · rw [← ha0, ← hb0]
    · exfalso; have := hΓH b hb0; rw [← e, ← ha0, hΓ0] at this
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
    · exfalso; have := hΓH a ha0; rw [e, ← hb0, hΓ0] at this
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
    · have hinj := injOn_fwdMap hWα hWα0 ht.le
      rcases lt_or_ge a 1 with ha1 | ha1 <;> rcases lt_or_ge b 1 with hb1 | hb1
      · rw [hΓ1 a ⟨ha0, ha1⟩, hΓ1 b ⟨hb0, hb1⟩] at e
        have e1 := hinj (hCA _ (hΦC _ (hι a ⟨ha0, ha1⟩))) (hCA _ (hΦC _ (hι b ⟨hb0, hb1⟩))) e
        have e2 := injOn_twoSlitChart hWβ hWβ0 hs.le hW' hW'0 hT.le (hι a ⟨ha0, ha1⟩) (hι b ⟨hb0, hb1⟩) e1
        have e3 := congrArg Complex.im e2
        simp only [hιdef, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero] at e3
        have h1a : 1 - a ≠ 0 := by linarith
        have h1b : 1 - b ≠ 0 := by linarith
        field_simp at e3
        linarith
      · exfalso
        rw [hΓ1 a ⟨ha0, ha1⟩, hΓ2 b hb1] at e
        have e1 := hinj (hCA _ (hΦC _ (hι a ⟨ha0, ha1⟩))) (hGA _ (hβG b hb1)) e
        exact (hΦC _ (hι a ⟨ha0, ha1⟩)).2 (Or.inr (e1 ▸ hβG b hb1))
      · exfalso
        rw [hΓ2 a ha1, hΓ1 b ⟨hb0, hb1⟩] at e
        have e1 := hinj (hGA _ (hβG a ha1)) (hCA _ (hΦC _ (hι b ⟨hb0, hb1⟩))) e
        exact (hΦC _ (hι b ⟨hb0, hb1⟩)).2 (Or.inr (e1 ▸ hβG a ha1))
      · rw [hΓ2 a ha1, hΓ2 b hb1] at e
        have e1 := hinj (hGA _ (hβG a ha1)) (hGA _ (hβG b hb1)) e
        have e2 : β (s / a) = β (s / b) := by
          have := congrArg negInv e1; rwa [negInv_negInv', negInv_negInv'] at this
        have e3 := hβp.inj (mem_Ici.2 (div_pos hs (by linarith)).le) (mem_Ici.2 (div_pos hs (by linarith)).le) e2
        have : s / a * a = s / b * a := by rw [e3]
        field_simp at this
        nlinarith
  · -- in `ℍ` at positive times
    intro u hu
    rcases lt_or_ge u 1 with h1 | h1
    · rw [hΓ1 u ⟨hu, h1⟩]
      exact QuantumZipper.FwdHolo.mapsTo_fwdMap hWα ht.le (hCA _ (hΦC _ (hι u ⟨hu, h1⟩)))
    · rw [hΓ2 u h1]
      exact QuantumZipper.FwdHolo.mapsTo_fwdMap hWα ht.le (hGA _ (hβG u h1))
  · -- tends to `∞`
    obtain ⟨C, -, hC⟩ := exists_norm_fwdMap_sub_le hWα hWα0 ht.le
    have hsu : Tendsto (fun u : ℝ => s / u) atTop (𝓝[≥] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.div_atTop tendsto_id, ?_⟩
      filter_upwards [eventually_gt_atTop 0] with u hu
      exact (div_pos hs hu).le
    have hb : Tendsto (fun u : ℝ => β (s / u)) atTop (𝓝 0) := by
      have h2 := (hβp.cont 0 self_mem_Ici).tendsto.comp hsu
      rwa [hβp.zero] at h2
    have hbn : Tendsto (fun u : ℝ => ‖β (s / u)‖) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨by simpa using hb.norm, ?_⟩
      filter_upwards [eventually_ge_atTop 1] with u hu
      have := hβp.mem_H _ (div_pos hs (by linarith : (0 : ℝ) < u))
      exact norm_pos_iff.2 fun h => by
        rw [h] at this; exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
    have hinv := tendsto_atTop_add_const_right _ (-C) (tendsto_inv_nhdsGT_zero.comp hbn)
    refine tendsto_atTop_mono' _ ?_ hinv
    filter_upwards [eventually_ge_atTop 1] with u hu
    rw [hΓ2 u hu]
    have h1 := hC _ (hGA _ (hβG u hu))
    have h2 := norm_sub_norm_le (negInv (β (s / u))) (negInv (β (s / u)) - fwdMap Wα t (negInv (β (s / u))))
    rw [sub_sub_cancel, norm_sub_rev] at h2
    have h3 : ‖negInv (β (s / u))‖ = ‖β (s / u)‖⁻¹ := by rw [negInv, norm_neg, norm_inv]
    simp only [Function.comp_apply]
    linarith

/-! ### The anchor near a real point -/

/-- `Θ = f'_T ∘ Ψ ∘ F_t`, the inverse of `f_t ∘ Φ`. -/
def chartTheta (Wα : ℝ → ℝ) (t : ℝ) (Wβ : ℝ → ℝ) (s : ℝ) (W' : ℝ → ℝ) (T : ℝ) (ξ : ℂ) : ℂ :=
  fwdMap W' T (revChart Wβ s (fwdMapInv Wα t ξ))

/-- **The anchor**: near the image `f_t(r₀)` of a real point `r₀ ≠ 0`, the points `ξ ∈ ℍ` are of the form `f_t(Φ(y))`
with `y = Θ(ξ) ∈ ℍ`, and `Θ(ξ)` tends to the real point `f'_T(R(f_s(R(r₀))))`. -/
theorem anchor_of_real (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α) (hWα : Continuous Wα)
    (hWα0 : Wα 0 = 0) (ht : 0 < t) (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hβ : IsLoewnerTrace Wβ β)
    (hβp : IsProperArc β) (hs : 0 < s) (hG : IsClosed (negInv '' fwdHull Wβ s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hT : 0 < T)
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) {r₀ : ℝ} (hr₀ : r₀ ≠ 0) :
    ∃ r₁ : ℝ, r₁ ≠ 0 ∧ (0 < r₀ ↔ 0 < r₁) ∧ (fwdMap Wα t r₀).im = 0 ∧
      Tendsto (chartTheta Wα t Wβ s W' T) (𝓝[H] (fwdMap Wα t r₀)) (𝓝 (fwdMap W' T r₁)) ∧
      ∀ᶠ ξ in 𝓝[H] (fwdMap Wα t r₀), chartTheta Wα t Wβ s W' T ξ ∈ H ∧
        fwdMap Wα t (twoSlitChart Wβ s W' T (chartTheta Wα t Wβ s W' T ξ)) = ξ := by
  obtain ⟨v₀, hv₀⟩ := exists_isForwardSol_of_isProperArc hα hαp hWα hWα0 hr₀ ht.le
  have hx₀ : fwdMap Wα t r₀ = v₀ t := fwdMap_eq_of_isForwardSol hWα hv₀ ⟨ht.le, le_rfl⟩
  have hx₀im : (fwdMap Wα t r₀).im = 0 := by
    rw [hx₀]; exact im_eq_zero_of_isForwardSol_real hWα hv₀ ⟨ht.le, le_rfl⟩
  have hx₀H : fwdMap Wα t r₀ ∈ Hbar := show 0 ≤ (fwdMap Wα t r₀).im by rw [hx₀im]
  have hF₀ : extendFrom H (fwdMapInv Wα t) (fwdMap Wα t r₀) = r₀ := by
    rw [hx₀]
    exact extendFrom_eq_of_isForwardSol hα hWα hWα0 ht.le (show (0 : ℝ) ≤ ((r₀ : ℝ) : ℂ).im by simp) hv₀
  -- `F_t(ξ) → r₀` in `ℍ`
  have h1 : Tendsto (fwdMapInv Wα t) (𝓝[H] (fwdMap Wα t r₀)) (𝓝[H] (r₀ : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun ξ hξ =>
      QuantumZipper.RS.fwdMapInv_mem_H hWα hWα0 ht.le hξ⟩
    have := (hα.hasBdryLimits hWα hWα0 ht.le).tendsto hx₀H
    rwa [hF₀] at this
  -- the reverse side: `R(r₀) = −1/r₀` is alive for `β`
  have hq : (-r₀⁻¹ : ℝ) ≠ 0 := neg_ne_zero.2 (inv_ne_zero hr₀)
  obtain ⟨v₁, hv₁⟩ := exists_isForwardSol_of_isProperArc hβ hβp hWβ hWβ0 hq hs.le
  have hp₁ex : ∃ p₁ : ℝ, fwdMap Wβ s ((-r₀⁻¹ : ℝ) : ℂ) = (p₁ : ℂ) := by
    refine ⟨(fwdMap Wβ s ((-r₀⁻¹ : ℝ) : ℂ)).re, Complex.ext (Complex.ofReal_re _).symm ?_⟩
    rw [fwdMap_eq_of_isForwardSol hWβ hv₁ ⟨hs.le, le_rfl⟩]
    simpa using im_eq_zero_of_isForwardSol_real hWβ hv₁ ⟨hs.le, le_rfl⟩
  obtain ⟨p₁, hp₁eq⟩ := hp₁ex
  have hp₁ : p₁ = (fwdMap Wβ s ((-r₀⁻¹ : ℝ) : ℂ)).re := by rw [hp₁eq, Complex.ofReal_re]
  have hp₁sign : (0 < r₀ → p₁ < 0) ∧ (r₀ < 0 → 0 < p₁) := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hneg : -r₀⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 h)
      obtain ⟨u, hu⟩ := (exists_isForwardSol_neg_iff (W := Wβ) (x := -r₀⁻¹) (T := s)).2 ⟨v₁, hv₁⟩
      have := re_fwdMap_pos (W := fun t => -Wβ t) hWβ.neg (by simp [hWβ0]) (neg_pos.2 hneg) hu
        ⟨hs.le, le_rfl⟩
      rw [fwdMap_neg_real hWβ hv₁ ⟨hs.le, le_rfl⟩, neg_re] at this
      rw [hp₁]; linarith
    · rw [hp₁]; exact re_fwdMap_pos hWβ hWβ0 (neg_pos.2 (inv_lt_zero.2 h)) hv₁ ⟨hs.le, le_rfl⟩
  have hp₁0 : p₁ ≠ 0 := by
    rcases lt_or_gt_of_ne hr₀ with h | h
    · exact (hp₁sign.2 h).ne'
    · exact (hp₁sign.1 h).ne
  set r₁ : ℝ := -p₁⁻¹ with hr₁
  have hr₁0 : r₁ ≠ 0 := neg_ne_zero.2 (inv_ne_zero hp₁0)
  have hRr₀ : negInv (r₀ : ℂ) = ((-r₀⁻¹ : ℝ) : ℂ) := by rw [negInv]; push_cast; ring
  have hRp₁ : negInv (p₁ : ℂ) = (r₁ : ℂ) := by rw [negInv, hr₁]; push_cast; ring
  -- `Ψ(F_t(ξ)) → r₁` in `ℍ`
  have h2 : Tendsto (fun ξ => negInv (fwdMapInv Wα t ξ)) (𝓝[H] (fwdMap Wα t r₀)) (𝓝[H] ((-r₀⁻¹ : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · rw [← hRr₀]
      exact (continuousAt_negInv (by exact_mod_cast hr₀)).tendsto.comp (tendsto_nhdsWithin_iff.1 h1).1
    · filter_upwards [self_mem_nhdsWithin] with ξ hξ
      exact negInv_mem_H (QuantumZipper.RS.fwdMapInv_mem_H hWα hWα0 ht.le hξ)
  have h3 : Tendsto (fun ξ => revChart Wβ s (fwdMapInv Wα t ξ)) (𝓝[H] (fwdMap Wα t r₀)) (𝓝 (r₁ : ℂ)) := by
    have h := (tendsto_fwdMap_of_isForwardSol hWβ hs.le hv₁).comp h2
    rw [← fwdMap_eq_of_isForwardSol hWβ hv₁ ⟨hs.le, le_rfl⟩, hp₁eq] at h
    have h' := (continuousAt_negInv (by exact_mod_cast hp₁0)).tendsto.comp h
    rwa [hRp₁] at h'
  -- eventually `F_t(ξ) ∉ A ∪ G`
  have hGc : (r₀ : ℂ) ∈ (negInv '' fwdHull Wβ s)ᶜ := fun ⟨w, hw, e⟩ => by
    have := negInv_mem_H hw.1; rw [e] at this
    exact absurd (show (0 : ℝ) < ((r₀ : ℝ) : ℂ).im from this) (by simp)
  have hev1 : ∀ᶠ ξ in 𝓝[H] (fwdMap Wα t r₀), fwdMapInv Wα t ξ ∈ (negInv '' fwdHull Wβ s)ᶜ :=
    (tendsto_nhdsWithin_iff.1 h1).1 (hG.isOpen_compl.mem_nhds hGc)
  have hgood : ∀ᶠ ξ in 𝓝[H] (fwdMap Wα t r₀), fwdMapInv Wα t ξ ∈ H \ fwdHull Wα t ∧
      fwdMapInv Wα t ξ ∈ H \ negInv '' fwdHull Wβ s := by
    filter_upwards [hev1, self_mem_nhdsWithin] with ξ hξG hξ
    have hm := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWα hWα0 ht.le hξ
    exact ⟨hm, hm.1, hξG⟩
  have h4 : Tendsto (fun ξ => revChart Wβ s (fwdMapInv Wα t ξ)) (𝓝[H] (fwdMap Wα t r₀)) (𝓝[H] (r₁ : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨h3, ?_⟩
    filter_upwards [hgood] with ξ hξ
    exact revChart_mem_H hWβ hs.le hξ.2
  obtain ⟨v₂, hv₂⟩ := exists_isForwardSol_of_isProperArc hη' hη'p hW' hW'0 hr₁0 hT.le
  have h5 := (tendsto_fwdMap_of_isForwardSol hW' hT.le hv₂).comp h4
  rw [← fwdMap_eq_of_isForwardSol hW' hv₂ ⟨hT.le, le_rfl⟩] at h5
  refine ⟨r₁, hr₁0, ?_, hx₀im, h5, ?_⟩
  · rw [hr₁]
    constructor
    · intro h; exact neg_pos.2 (inv_lt_zero.2 (hp₁sign.1 h))
    · intro h
      by_contra hle
      have h0 : r₀ < 0 := lt_of_le_of_ne (not_lt.1 hle) hr₀
      have := hp₁sign.2 h0
      have : -p₁⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 this)
      linarith
  · filter_upwards [hgood, self_mem_nhdsWithin] with ξ hξ hξH
    have hΨ : revChart Wβ s (fwdMapInv Wα t ξ) ∈ H \ fwdHull W' T := by
      refine ⟨revChart_mem_H hWβ hs.le hξ.2, ?_⟩
      rw [hK']
      rintro ⟨a, ha, e⟩
      have := injOn_revChart hWβ hWβ0 hs.le (⟨ha.1, fun h => disjoint_left.1 hdisj ha h⟩) hξ.2 e
      exact hξ.1.2 (this ▸ ha)
    refine ⟨QuantumZipper.FwdHolo.mapsTo_fwdMap hW' hT.le hΨ, ?_⟩
    simp only [chartTheta, twoSlitChart]
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hW' hW'0 hT.le hΨ, revChartInv_revChart hWβ hWβ0 hs.le hξ.2,
      QuantumZipper.RS.fwdMap_fwdMapInv hWα hWα0 ht.le hξH]

/-! ### The two quadrants lie on the two sides of the separating arc -/

theorem re_fwdMap_neg {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T y : ℝ} (hT : 0 ≤ T) (hy : y < 0)
    {v : ℝ → ℂ} (hv : QuantumZipper.IsForwardSol W (y : ℂ) T v) : (fwdMap W T y).re < 0 := by
  obtain ⟨u, hu⟩ := (exists_isForwardSol_neg_iff (W := W) (x := y) (T := T)).2 ⟨v, hv⟩
  have := re_fwdMap_pos (W := fun t => -W t) hW.neg (by simp [hW0]) (neg_pos.2 hy) hu ⟨hT, le_rfl⟩
  rw [fwdMap_neg_real hW hv ⟨hT, le_rfl⟩, neg_re] at this
  linarith

/-- The image under `f_t ∘ Φ` of a connected set of `ℍ` off the imaginary axis lies in one component of the
complement of the separating arc. -/
theorem image_subset_connectedComponentIn_sepArc
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t) (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0)
    (hβ : IsLoewnerTrace Wβ β) (hβp : IsProperArc β) (hs : 0 < s)
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s)) (hW' : Continuous W') (hW'0 : W' 0 = 0)
    (hT : 0 < T) (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) {Q : Set ℂ} (hQ : IsPreconnected Q)
    (hQH : Q ⊆ H) (hQre : ∀ y ∈ Q, y.re ≠ 0) {y₀ : ℂ} (hy₀ : y₀ ∈ Q) :
    (fun y => fwdMap Wα t (twoSlitChart Wβ s W' T y)) '' Q ⊆
      connectedComponentIn (H \ arcRange (sepArc Wα t Wβ s β W' T))
        (fwdMap Wα t (twoSlitChart Wβ s W' T y₀)) := by
  have hΦC : ∀ y ∈ H, twoSlitChart Wβ s W' T y ∈ H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s) :=
    fun y hy => twoSlitChart_mem hWβ hWβ0 hs.le hW' hW'0 hT.le hK' hy
  have hCA : ∀ z ∈ H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s), z ∈ H \ fwdHull Wα t :=
    fun z hz => ⟨hz.1, fun h => hz.2 (Or.inl h)⟩
  have hGH : negInv '' fwdHull Wβ s ⊆ H := fun z ⟨w, hw, e⟩ => e ▸ negInv_mem_H hw.1
  have hcont : ContinuousOn (fun y => fwdMap Wα t (twoSlitChart Wβ s W' T y)) Q := fun y hy =>
    (ContinuousAt.comp (g := fwdMap Wα t) (f := twoSlitChart Wβ s W' T)
      (continuousAt_fwdMap hWα ht.le (hCA _ (hΦC _ (hQH hy))))
      (continuousAt_twoSlitChart hWβ hWβ0 hs.le hW' hW'0 hT.le (hQH hy))).continuousWithinAt
  refine (hQ.image _ hcont).subset_connectedComponentIn (mem_image_of_mem _ hy₀) ?_
  rintro _ ⟨y, hy, rfl⟩
  have hyH := hQH hy
  refine ⟨QuantumZipper.FwdHolo.mapsTo_fwdMap hWα ht.le (hCA _ (hΦC _ hyH)), ?_⟩
  rintro ⟨u, hu, e⟩
  have hinj := injOn_fwdMap hWα hWα0 ht.le
  simp only [sepArc] at e
  split_ifs at e with h0 h1
  · have := QuantumZipper.FwdHolo.mapsTo_fwdMap hWα ht.le (hCA _ (hΦC _ hyH))
    rw [← e] at this
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
  · have hu0 : 0 < u := lt_of_not_ge h0
    have hιH : (((u / (1 - u) : ℝ) : ℂ) * I) ∈ H := ofReal_mul_I_mem_H (div_pos hu0 (by linarith))
    have e1 := hinj (hCA _ (hΦC _ hιH)) (hCA _ (hΦC _ hyH)) e
    have e2 := injOn_twoSlitChart hWβ hWβ0 hs.le hW' hW'0 hT.le hιH hyH e1
    apply hQre y hy
    rw [← e2, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
    ring
  · have hu1 : 1 ≤ u := not_lt.1 h1
    have hβG : negInv (β (s / u)) ∈ negInv '' fwdHull Wβ s := by
      refine ⟨β (s / u), ?_, rfl⟩
      rw [fwdHull_eq_image_Ioc hβ hβp hs.le]
      exact ⟨s / u, ⟨div_pos hs (by linarith), div_le_self hs.le hu1⟩, rfl⟩
    have e1 := hinj ⟨hGH hβG, fun h => disjoint_left.1 hdisj h hβG⟩ (hCA _ (hΦC _ hyH)) e
    exact (hΦC _ hyH).2 (Or.inr (e1 ▸ hβG))

/-- **The quadrants and the sides of the separating arc**: `f_t(Φ(y))` lies on the left of `Γ` when `Re y < 0`, and on
the right of `Γ` when `Re y > 0`. -/
theorem fwdMap_twoSlitChart_mem_sides (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α) (hWα : Continuous Wα)
    (hWα0 : Wα 0 = 0) (ht : 0 < t) (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hβ : IsLoewnerTrace Wβ β)
    (hβp : IsProperArc β) (hs : 0 < s) (hG : IsClosed (negInv '' fwdHull Wβ s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hT : 0 < T)
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) (htip : η' T = revChart Wβ s (α t)) {y : ℂ}
    (hy : y ∈ H) :
    (y.re < 0 → fwdMap Wα t (twoSlitChart Wβ s W' T y) ∈ leftSideOf (arcRange (sepArc Wα t Wβ s β W' T))) ∧
    (0 < y.re → fwdMap Wα t (twoSlitChart Wβ s W' T y) ∈ rightSideOf (arcRange (sepArc Wα t Wβ s β W' T))) := by
  have hΓ := isProperArc_sepArc hα hαp hWα hWα0 ht hWβ hWβ0 hβ hβp hs hdisj hW' hW'0 hη' hT hK' htip
  have key : ∀ r₀ : ℝ, r₀ ≠ 0 → ∀ (side : Set ℂ),
      (∀ r : ℝ, (r : ℂ) ∈ Hbar → (0 < r₀ ↔ 0 < r) → r ≠ 0 →
        ∃ ρ > 0, ball (r : ℂ) ρ ∩ H ⊆ side) →
      ∀ Q : Set ℂ, IsPreconnected Q → Q ⊆ H → (∀ y ∈ Q, y.re ≠ 0) →
      (∀ z : ℂ, z ∈ H → (0 < r₀ ↔ 0 < z.re) → z.re ≠ 0 → z ∈ Q) →
      (∀ z w : ℂ, z ∈ side → w ∈ connectedComponentIn (H \ arcRange (sepArc Wα t Wβ s β W' T)) z → w ∈ side) →
      ∀ y ∈ Q, fwdMap Wα t (twoSlitChart Wβ s W' T y) ∈ side := by
    intro r₀ hr₀ side hball Q hQ hQH hQre hQmem hcomp y hyQ
    obtain ⟨r₁, hr₁0, hr₁s, hx₀im, hlim, hev⟩ :=
      anchor_of_real hα hαp hWα hWα0 ht hWβ hWβ0 hβ hβp hs hG hdisj hW' hW'0 hη' hη'p hT hK' hr₀
    obtain ⟨v₀, hv₀⟩ := exists_isForwardSol_of_isProperArc hα hαp hWα hWα0 hr₀ ht.le
    obtain ⟨v₁, hv₁⟩ := exists_isForwardSol_of_isProperArc hη' hη'p hW' hW'0 hr₁0 hT.le
    set x₀ : ℝ := (fwdMap Wα t r₀).re with hx₀
    have hx₀eq : fwdMap Wα t r₀ = (x₀ : ℂ) := Complex.ext (by simp [hx₀]) (by simp [hx₀im])
    have hsign0 : (0 < r₀ ↔ 0 < x₀) := by
      constructor
      · intro h; exact re_fwdMap_pos hWα hWα0 h hv₀ ⟨ht.le, le_rfl⟩
      · intro h; by_contra hle
        have := re_fwdMap_neg hWα hWα0 ht.le (lt_of_le_of_ne (not_lt.1 hle) hr₀) hv₀
        linarith
    have hx₀0 : x₀ ≠ 0 := by
      rcases lt_or_gt_of_ne hr₀ with h | h
      · exact (re_fwdMap_neg hWα hWα0 ht.le h hv₀).ne
      · exact (re_fwdMap_pos hWα hWα0 h hv₀ ⟨ht.le, le_rfl⟩).ne'
    obtain ⟨ρ, hρ, hball'⟩ := hball x₀ (show (0 : ℝ) ≤ ((x₀ : ℝ) : ℂ).im by simp) hsign0 hx₀0
    -- the limit point of `Θ` has the sign of `r₀`
    have hlimre : (0 < r₀ → 0 < (fwdMap W' T r₁).re) ∧ (r₀ < 0 → (fwdMap W' T r₁).re < 0) := by
      refine ⟨fun h => re_fwdMap_pos hW' hW'0 (hr₁s.1 h) hv₁ ⟨hT.le, le_rfl⟩, fun h => ?_⟩
      have : r₁ < 0 := lt_of_le_of_ne (not_lt.1 fun h' => absurd (hr₁s.2 h') (not_lt.2 h.le)) hr₁0
      exact re_fwdMap_neg hW' hW'0 hT.le this hv₁
    have hNe : (𝓝[H] (fwdMap Wα t r₀)).NeBot := by
      rw [hx₀eq]
      exact mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ show (0 : ℝ) ≤ ((x₀ : ℝ) : ℂ).im by simp)
    have hre := (Complex.continuous_re.tendsto _).comp hlim
    have hevQ : ∀ᶠ ξ in 𝓝[H] (fwdMap Wα t r₀), (0 < r₀ ↔ 0 < (chartTheta Wα t Wβ s W' T ξ).re) ∧
        (chartTheta Wα t Wβ s W' T ξ).re ≠ 0 := by
      rcases lt_or_gt_of_ne hr₀ with h | h
      · filter_upwards [hre.eventually (gt_mem_nhds (hlimre.2 h))] with ξ hξ
        exact ⟨⟨fun h' => absurd h' (not_lt.2 h.le), fun h' => absurd h' (not_lt.2 hξ.le)⟩, hξ.ne⟩
      · filter_upwards [hre.eventually (lt_mem_nhds (hlimre.1 h))] with ξ hξ
        exact ⟨⟨fun _ => hξ, fun _ => h⟩, hξ.ne'⟩
    have hevB : ∀ᶠ ξ in 𝓝[H] (fwdMap Wα t r₀), ξ ∈ ball (x₀ : ℂ) ρ ∩ H := by
      rw [hx₀eq]
      filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds ((x₀ : ℝ) : ℂ) hρ)] with ξ hξ
      exact ⟨hξ.2, hξ.1⟩
    obtain ⟨ξ, ⟨hΘH, hΘ⟩, hΘs, hξB⟩ := (hev.and (hevQ.and hevB)).exists
    have hy₀Q : chartTheta Wα t Wβ s W' T ξ ∈ Q := hQmem _ hΘH hΘs.1 hΘs.2
    have hsub := image_subset_connectedComponentIn_sepArc hWα hWα0 ht hWβ hWβ0 hβ hβp hs hdisj
      hW' hW'0 hT hK' hQ hQH hQre hy₀Q
    rw [hΘ] at hsub
    exact hcomp ξ _ (hball' hξB) (hsub (mem_image_of_mem _ hyQ))
  refine ⟨fun hre => ?_, fun hre => ?_⟩
  · refine key (-1) (by norm_num) _ (fun r _ hrs hr0 => ?_) {z | z ∈ H ∧ z.re < 0} ?_ (fun z hz => hz.1)
      (fun z hz => hz.2.ne) (fun z hz hs' h0 => ⟨hz, ?_⟩)
      (fun z w hz hw => mem_leftSideOf_of_mem_connectedComponentIn hz hw) y ⟨hy, hre⟩
    · have hrneg : r < 0 := lt_of_le_of_ne (not_lt.1 fun h => absurd (hrs.2 h) (by norm_num)) hr0
      exact hΓ.exists_ball_inter_H_subset_leftSideOf hrneg
    · exact ((convex_halfSpace_im_gt 0).inter (convex_halfSpace_re_lt 0)).isPreconnected
    · exact lt_of_le_of_ne (not_lt.1 fun h => absurd (hs'.2 h) (by norm_num)) h0
  · refine key 1 one_ne_zero _ (fun r _ hrs hr0 => ?_) {z | z ∈ H ∧ 0 < z.re} ?_ (fun z hz => hz.1)
      (fun z hz => hz.2.ne') (fun z hz hs' h0 => ⟨hz, hs'.1 one_pos⟩)
      (fun z w hz hw => mem_rightSideOf_of_mem_connectedComponentIn hz hw) y ⟨hy, hre⟩
    · exact hΓ.exists_ball_inter_H_subset_rightSideOf (hrs.1 one_pos)
    · exact ((convex_halfSpace_im_gt 0).inter (convex_halfSpace_re_gt 0)).isPreconnected

end InteractingSLE.WangWu
