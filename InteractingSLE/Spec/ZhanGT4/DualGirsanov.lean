/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MTildeMart
import InteractingSLE.Spec.Sec2.GirsanovDensity
import InteractingSLE.Stochastic.Martingale.OptionalSampling

/-!
# Girsanov with the other curve frozen, I: the tilted log-field

Packet PROVE-ZHAN-GT4-A9. Source: Astra, *Follow-up proofs*, §A.1.2–A.1.3 (`ig1_followup_proofs.txt` L292–L351, R38):
"`d_j M / M = √κ_j (q_j − b_j/κ_j) dB_j`" (D8) and "By (D8) and Girsanov, with the other curve stopped, the new drift
of `W_j` is `κ_j q_j`". With the other curve frozen and zero drift (ordinary `SLE_κ`, `W = σB`), `M = exp ℓ(t, W_t)` and
the drift rate is `θ_t = σ ∂_xℓ(t, W_t)`.

The proof avoids stochastic integrals (PROVE-ZHAN-GT4-A8's route): for `a ∈ ℝ` the process
`N^a_t = exp(ℓ(t, σB_t) − ℓ(0, σB_0) + a(B_t − B_0) − a I_t − a²t/2)`, `I_t = ∫₀ᵗ θ`, is again the exponential of a
log-field along the driver, the **tilt** `ℓ^a(t, x) = ℓ(t, x) + (a/σ)x + β(t)`; its generator vanishes along the driver
exactly because `θ = σ ℓ_x` there:
`ℓ^a_t + σ²/2(ℓ^a_xx + (ℓ^a_x)²) = [ℓ_t + σ²/2(ℓ_xx + ℓ_x²)] − aθ + aσℓ_x = 0`.
The tilt is unbounded in `x`, so it is a log-field only up to the localization `S_N = S ∧ inf{u : |B_u − B_0| ≥ N}`.

## Main results

* `IsLogField.add_affine`: adding `αx + β(t)` (with `β` differentiable in time) to a log-field;
* `drvRate`, `drvTheta`, `drvInt`: the drift rate `θ` along the driver, cut at `S`, and its integral `I`;
  continuity, bounds, the derivative of `I` on `[0, S]`, adaptedness (`measurable_drvInt`);
* `tiltL`, `stopN`, **`IsDriverLogField.tilt`**: the tilt is a driver log-field up to `S_N`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open Sec6.Prop65 (hitLe)

/-! ### Adding an affine field -/

namespace IsLogField

variable {ℓ ℓx ℓxx ℓxxx ℓt : ℝ → ℝ → ℝ} {b c y ρ K : ℝ}

/-- **Adding `αx + β(t)` to a log-field** keeps it a log-field, with the bound `K + K'` when `K'` bounds the added
field on the box, `|α|` and `|β'|`. -/
theorem add_affine (hL : IsLogField ℓ ℓx ℓxx ℓxxx ℓt b c y ρ K) {α : ℝ} {β β' : ℝ → ℝ}
    (hβ : ∀ t ∈ Icc b c, HasDerivWithinAt β (β' t) (Icc b c) t) (hβc : ContinuousOn β' (Icc b c)) {K' : ℝ}
    (hK' : 0 ≤ K') (hb : ∀ t ∈ Icc b c, ∀ x, |x - y| < 3 * ρ → |α * x + β t| ≤ K') (hα : |α| ≤ K')
    (hβ'b : ∀ t ∈ Icc b c, |β' t| ≤ K') :
    IsLogField (fun t x => ℓ t x + (α * x + β t)) (fun t x => ℓx t x + α) ℓxx ℓxxx
      (fun t x => ℓt t x + β' t) b c y ρ (K + K') where
  pos := hL.pos
  Knonneg := add_nonneg hL.Knonneg hK'
  dx t ht x hx := by
    have h1 : HasDerivAt (fun x => α * x + β t) α x := by
      simpa using ((hasDerivAt_id x).const_mul α).add_const (β t)
    exact (hL.dx t ht x hx).add h1
  dxx t ht x hx := by simpa using (hL.dxx t ht x hx).add_const α
  dxxx t ht x hx := hL.dxxx t ht x hx
  dt t ht x hx := (hL.dt t ht x hx).add ((hβ t ht).const_add (α * x))
  cont := by
    have hβcont : ContinuousOn β (Icc b c) := fun t ht => (hβ t ht).continuousWithinAt
    refine hL.cont.add ((continuousOn_const.mul continuous_snd.continuousOn).add ?_)
    exact hβcont.comp continuous_fst.continuousOn fun p hp => hp.1
  contX := hL.contX.add continuousOn_const
  contXX := hL.contXX
  contT := hL.contT.add (hβc.comp continuous_fst.continuousOn fun p hp => hp.1)
  bound t ht x hx := by
    obtain ⟨h0, h1, h2, h3, h4⟩ := hL.bound t ht x hx
    refine ⟨(abs_add_le _ _).trans (add_le_add h0 (hb t ht x hx)), (abs_add_le _ _).trans (add_le_add h1 hα),
      h2.trans (le_add_of_nonneg_right hK'), h3.trans (le_add_of_nonneg_right hK'),
      (abs_add_le _ _).trans (add_le_add h4 (hβ'b t ht))⟩

end IsLogField

/-! ### The drift rate along the driver -/

section Drift

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The drift rate along the driver**, `g_r = σ ℓ_x(r, σB_r)` (the source's `√κ_j q_j` with zero driver drift). -/
def drvRate (σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ℓx : Ω → ℝ → ℝ → ℝ) (ω : Ω) (r : ℝ) : ℝ :=
  σ * ℓx ω r (σ * B r.toNNReal ω)

open scoped Classical in
/-- **The drift rate cut at `S`**, right-continuous: `θ_r = g_r` for `r < S`, `0` afterwards. -/
def drvTheta (σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (ℓx : Ω → ℝ → ℝ → ℝ) (r : ℝ≥0) (ω : Ω) : ℝ :=
  if r < S ω then drvRate σ B ℓx ω r else 0

/-- **The accumulated drift** `I_t = ∫₀ᵗ θ_u du`. -/
def drvInt (σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (ℓx : Ω → ℝ → ℝ → ℝ) (ω : Ω) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, drvTheta σ B S ℓx u.toNNReal ω

variable {𝓕 : Filtration ℝ≥0 mΩ} {σ ρ K : ℝ} {B : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0}
  {ℓ ℓx ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ}

namespace IsDriverLogField

variable (hL : IsDriverLogField 𝓕 σ ρ K B S ℓ ℓx ℓxx ℓxxx ℓt)
include hL

/-- `ℓ_x` along the driver is continuous on `[0, S]`. -/
theorem continuousOn_driverX (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ) (ω : Ω) :
    ContinuousOn (fun r : ℝ => ℓx ω r (σ * B r.toNNReal ω)) (Icc 0 (S ω)) := by
  intro r₀ hr₀
  have hf := continuous_driver (σ := σ) hBc ω
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousAt_iff.1 hf.continuousAt ρ hρ
  set b := max 0 (r₀ - δ / 2)
  set c := min (S ω : ℝ) (r₀ + δ / 2)
  have hb0 : 0 ≤ b := le_max_left _ _
  have hbr : b ≤ r₀ := max_le hr₀.1 (by linarith)
  have hrc : r₀ ≤ c := le_min hr₀.2 (by linarith)
  have hcS : c ≤ S ω := min_le_left _ _
  have hdr : ∀ r ∈ Icc b c, |σ * B r.toNNReal ω - σ * B r₀.toNNReal ω| < ρ := fun r hr => by
    have h1 : r₀ - δ / 2 ≤ r := (le_max_right _ _).trans hr.1
    have h2 : r ≤ r₀ + δ / 2 := hr.2.trans (min_le_right _ _)
    have := hfδ (x := r) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rwa [Real.dist_eq] at this
  have hLF := hL.loc ω b c _ hb0 (hbr.trans hrc) hcS hdr
  have hmaps : MapsTo (fun r : ℝ => (r, σ * B r.toNNReal ω)) (Icc b c)
      (Icc b c ×ˢ {x | |x - σ * B r₀.toNNReal ω| < 3 * ρ}) := fun r hr =>
    ⟨hr, show |σ * B r.toNNReal ω - σ * B r₀.toNNReal ω| < 3 * ρ by have := hdr r hr; linarith⟩
  have hcomp := hLF.contX.comp (continuousOn_id.prodMk hf.continuousOn) hmaps
  have hmem : Icc b c ∈ 𝓝[Icc 0 (S ω : ℝ)] r₀ := by
    refine mem_nhdsWithin.2 ⟨Ioo (r₀ - δ / 2) (r₀ + δ / 2), isOpen_Ioo, ⟨by linarith, by linarith⟩, ?_⟩
    rintro r ⟨⟨hr1, hr2⟩, hr3, hr4⟩
    exact ⟨max_le hr3 hr1.le, le_min hr4 hr2.le⟩
  exact (hcomp r₀ ⟨hbr, hrc⟩).mono_of_mem_nhdsWithin hmem

/-- `ℓ_x` along the driver is bounded by `K` on `[0, S]`. -/
theorem abs_X_le (hρ : 0 < ρ) (ω : Ω) {r : ℝ} (hr : r ∈ Icc 0 (S ω : ℝ)) :
    |ℓx ω r (σ * B r.toNNReal ω)| ≤ K := by
  have hLF := hL.loc ω r r (σ * B r.toNNReal ω) hr.1 le_rfl hr.2 fun u hu => by
    rw [show u = r from le_antisymm hu.2 hu.1, sub_self, abs_zero]; exact hρ
  exact (hLF.bound r ⟨le_rfl, le_rfl⟩ _ (by rw [sub_self, abs_zero]; linarith)).2.1

/-- The drift rate is continuous on `[0, S]`. -/
theorem continuousOn_drvRate (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ) (ω : Ω) :
    ContinuousOn (drvRate σ B ℓx ω) (Icc 0 (S ω)) :=
  continuousOn_const.mul (hL.continuousOn_driverX hBc hρ ω)

/-- The drift rate is bounded by `|σ| K` on `[0, S]`. -/
theorem abs_drvRate_le (hρ : 0 < ρ) (ω : Ω) {r : ℝ} (hr : r ∈ Icc 0 (S ω : ℝ)) :
    |drvRate σ B ℓx ω r| ≤ |σ| * K := by
  rw [drvRate, abs_mul]; exact mul_le_mul_of_nonneg_left (hL.abs_X_le hρ ω hr) (abs_nonneg σ)

/-- The cut drift rate is bounded by `|σ| K`. -/
theorem abs_drvTheta_le (hρ : 0 < ρ) (r : ℝ≥0) (ω : Ω) : |drvTheta σ B S ℓx r ω| ≤ |σ| * K := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hL.abs_X_le hρ ω ⟨le_rfl, (S ω).coe_nonneg⟩)
  unfold drvTheta
  split_ifs with h
  · exact hL.abs_drvRate_le hρ ω ⟨r.coe_nonneg, NNReal.coe_le_coe.2 h.le⟩
  · rw [abs_zero]; positivity

/-- The cut drift rate is right-continuous in time. -/
theorem continuousWithinAt_drvTheta (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ) (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt (drvTheta σ B S ℓx · ω) (Ici t) t := by
  by_cases ht : t < S ω
  · -- near `t` on the right, `θ = g`, continuous on `[0, S]`
    have hg := hL.continuousOn_drvRate hBc hρ ω
    have hgt : ContinuousWithinAt (fun u : ℝ≥0 => drvRate σ B ℓx ω (u : ℝ)) (Icc t (S ω)) t := by
      have h1 : ContinuousWithinAt (drvRate σ B ℓx ω) (Icc 0 (S ω : ℝ)) (t : ℝ) :=
        hg _ ⟨t.coe_nonneg, NNReal.coe_le_coe.2 ht.le⟩
      exact h1.comp NNReal.continuous_coe.continuousWithinAt fun u hu =>
        ⟨u.coe_nonneg, NNReal.coe_le_coe.2 hu.2⟩
    have hev : ∀ᶠ u in 𝓝[Ici t] t, drvTheta σ B S ℓx u ω = drvRate σ B ℓx ω (u : ℝ) := by
      have : Iio (S ω) ∈ 𝓝 t := isOpen_Iio.mem_nhds ht
      filter_upwards [nhdsWithin_le_nhds this] with u hu
      simp only [drvTheta, mem_Iio.1 hu, ↓reduceIte, drvRate, Real.toNNReal_coe]
    have hmem : Icc t (S ω) ∈ 𝓝[Ici t] t := by
      refine mem_nhdsWithin.2 ⟨Iio (S ω), isOpen_Iio, ht, fun u hu => ⟨hu.2, (mem_Iio.1 hu.1).le⟩⟩
    have hgt' := hgt.mono_of_mem_nhdsWithin hmem
    have e : drvTheta σ B S ℓx t ω = drvRate σ B ℓx ω (t : ℝ) := by
      simp only [drvTheta, ht, ↓reduceIte, drvRate, Real.toNNReal_coe]
    rw [ContinuousWithinAt, e]
    exact hgt'.congr' (hev.mono fun u hu => hu.symm)
  · -- at and after `S`, `θ = 0` on `[t, ∞)`
    push Not at ht
    have hz : ∀ u ∈ Ici t, drvTheta σ B S ℓx u ω = 0 := fun u hu => by
      simp only [drvTheta, not_lt.2 (ht.trans hu), ↓reduceIte]
    exact (continuousWithinAt_const (b := (0 : ℝ))).congr hz (hz t (mem_Ici.2 le_rfl))

/-- The cut drift rate is adapted. -/
theorem measurable_drvTheta (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (r : ℝ≥0) :
    Measurable[𝓕 r] (drvTheta σ B S ℓx r) := by
  have hlt : MeasurableSet[𝓕 r] {ω | r < S ω} := by
    have h := (measurableSet_le_of_isStoppingTime hS r).compl
    have he : {ω | S ω ≤ r}ᶜ = {ω | r < S ω} := by ext ω; simp
    rwa [he] at h
  have hm : Measurable[𝓕 r] fun ω => σ * ({ω | r ≤ S ω}.indicator (fun ω => ℓx ω r (σ * B r ω)) ω) :=
    measurable_const.mul (hL.meas1 r)
  have e : drvTheta σ B S ℓx r = {ω | r < S ω}.indicator
      fun ω => σ * ({ω | r ≤ S ω}.indicator (fun ω => ℓx ω r (σ * B r ω)) ω) := by
    funext ω
    by_cases hω : r < S ω
    · rw [indicator_of_mem (show ω ∈ {ω | r < S ω} from hω),
        indicator_of_mem (show ω ∈ {ω | r ≤ S ω} from hω.le)]
      simp only [drvTheta, hω, ↓reduceIte, drvRate, Real.toNNReal_coe]
    · rw [indicator_of_notMem (show ω ∉ {ω | r < S ω} from hω)]
      simp only [drvTheta, hω, ↓reduceIte]
  rw [e]
  exact hm.indicator hlt

/-- The cut drift rate is progressively measurable. -/
theorem isStronglyProgressive_drvTheta (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) :
    IsStronglyProgressive 𝓕 (drvTheta σ B S ℓx) :=
  isStronglyProgressive_of_rightContinuous (fun r => (hL.measurable_drvTheta hS r).stronglyMeasurable)
    fun ω t => hL.continuousWithinAt_drvTheta hBc hρ ω t

/-- **The accumulated drift is adapted**: `I_t` is `𝓕_t`-measurable. -/
theorem measurable_drvInt (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (t : ℝ≥0) :
    Measurable[𝓕 t] fun ω => drvInt σ B S ℓx ω t := by
  have h := Girsanov.stronglyMeasurable_integral_comp (hL.isStronglyProgressive_drvTheta hBc hρ hS)
    measurable_id t
  exact h.measurable

omit hL in
/-- On `[0, S]` the accumulated drift is the integral of the (uncut) drift rate. -/
theorem drvInt_eq (ω : Ω) {t : ℝ} (ht : t ∈ Icc 0 (S ω : ℝ)) :
    drvInt σ B S ℓx ω t = ∫ u in (0 : ℝ)..t, drvRate σ B ℓx ω u := by
  unfold drvInt
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ (S ω : ℝ) := by
    rw [ae_iff]; simp
  filter_upwards [hne] with u hu hmem
  rw [uIoc_of_le ht.1] at hmem
  have hlt : u.toNNReal < S ω := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hmem.1.le]
    exact lt_of_le_of_ne (hmem.2.trans ht.2) hu
  simp only [drvTheta, hlt, ↓reduceIte, drvRate, Real.coe_toNNReal _ hmem.1.le]

/-- **`∂_t I = g` on `[0, S]`**, within every `[b, c] ⊆ [0, S]`. -/
theorem hasDerivWithinAt_drvInt (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ) (ω : Ω) {b c t : ℝ}
    (hb : 0 ≤ b) (hcS : c ≤ S ω) (ht : t ∈ Icc b c) :
    HasDerivWithinAt (drvInt σ B S ℓx ω) (drvRate σ B ℓx ω t) (Icc b c) t := by
  have hg := hL.continuousOn_drvRate hBc hρ ω
  have htS : t ∈ Icc (0 : ℝ) (S ω) := ⟨hb.trans ht.1, ht.2.trans hcS⟩
  have : Fact (t ∈ Icc (0 : ℝ) (S ω)) := ⟨htS⟩
  have hint : IntervalIntegrable (drvRate σ B ℓx ω) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le htS.1]
    exact hg.mono (Icc_subset_Icc_right htS.2)
  have hJ : HasDerivWithinAt (fun u => ∫ x in (0 : ℝ)..u, drvRate σ B ℓx ω x) (drvRate σ B ℓx ω t)
      (Icc 0 (S ω : ℝ)) t := intervalIntegral.integral_hasDerivWithinAt_right hint
    (hg.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hg t htS)
  exact (hJ.congr (fun u hu => drvInt_eq ω hu) (drvInt_eq ω htS)).mono (Icc_subset_Icc hb hcS)

/-- `|I_t| ≤ |σ| K t`. -/
theorem abs_drvInt_le (hρ : 0 < ρ) (ω : Ω) {t : ℝ} (ht : 0 ≤ t) : |drvInt σ B S ℓx ω t| ≤ |σ| * K * t := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := |σ| * K)
    (f := fun u : ℝ => drvTheta σ B S ℓx u.toNNReal ω) fun u _ => by
      rw [Real.norm_eq_abs]; exact hL.abs_drvTheta_le hρ _ ω
  rwa [sub_zero, abs_of_nonneg ht] at h

end IsDriverLogField

/-! ### The tilt and its localization -/

/-- The time part `β(t) = −ℓ(0, σB_0) − aB_0 − a I_t − a²t/2` of the tilt. -/
def tiltB (σ a : ℝ) (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (ℓ ℓx : Ω → ℝ → ℝ → ℝ) (ω : Ω) (t : ℝ) : ℝ :=
  -ℓ ω 0 (σ * B 0 ω) - a * B 0 ω - a * drvInt σ B S ℓx ω t - a ^ 2 / 2 * t

/-- **The Girsanov tilt** `ℓ^a(t, x) = ℓ(t, x) + ((a/σ)x + β(t))`; along the driver
`exp ℓ^a(t, σB_t) = (M_t/M_0) exp(a(B_t − B_0) − aI_t − a²t/2)`. -/
def tiltL (σ a : ℝ) (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (ℓ ℓx : Ω → ℝ → ℝ → ℝ) (ω : Ω) (t x : ℝ) : ℝ :=
  ℓ ω t x + (a / σ * x + tiltB σ a B S ℓ ℓx ω t)

/-- `∂_x ℓ^a = ℓ_x + a/σ`. -/
def tiltLx (σ a : ℝ) (ℓx : Ω → ℝ → ℝ → ℝ) (ω : Ω) (t x : ℝ) : ℝ := ℓx ω t x + a / σ

/-- `∂_t ℓ^a = ℓ_t − a g_t − a²/2`. -/
def tiltLt (σ a : ℝ) (B : ℝ≥0 → Ω → ℝ) (ℓx ℓt : Ω → ℝ → ℝ → ℝ) (ω : Ω) (t x : ℝ) : ℝ :=
  ℓt ω t x + (-(a * drvRate σ B ℓx ω t) - a ^ 2 / 2)

/-- The level process of the localization, `N − |B_u − B_0|`. -/
def stopY (B : ℝ≥0 → Ω → ℝ) (N : ℝ) (u : ℝ≥0) (ω : Ω) : ℝ := N - |B u ω - B 0 ω|

/-- **The localization** `S_N = S ∧ inf{u : |B_u − B_0| ≥ N}` (the hitting time capped at `R ≥ S`). -/
def stopN (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (R : ℝ≥0) (N : ℝ) (ω : Ω) : ℝ≥0 :=
  min (S ω) (hitLe (stopY B N) 0 R ω)

/-- The bound added by the tilt on the localized boxes. -/
def tiltBound (σ ρ K R a N : ℝ) : ℝ :=
  |a| / σ * (4 * ρ + σ * N) + K + |a| * (σ * K * R) + a ^ 2 / 2 * R + |a| / σ + (|a| * (σ * K) + a ^ 2 / 2)

theorem stopN_le (R : ℝ≥0) (N : ℝ) (ω : Ω) : stopN B S R N ω ≤ S ω := min_le_left _ _

theorem continuous_stopY (hBc : ∀ ω, Continuous (B · ω)) (N : ℝ) (ω : Ω) :
    Continuous fun u => stopY B N u ω :=
  continuous_const.sub (((hBc ω).sub continuous_const).abs)

theorem isStoppingTime_stopN (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ u, Measurable[𝓕 u] (B u))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (R : ℝ≥0) (N : ℝ) :
    IsStoppingTime 𝓕 fun ω => (stopN B S R N ω : WithTop ℝ≥0) := by
  have hYm : ∀ u, Measurable[𝓕 u] (stopY B N u) := fun u => by
    have h1 := hBm u
    have h0 : Measurable[𝓕 u] (B 0) := (hBm 0).mono (𝓕.mono zero_le) le_rfl
    unfold stopY; fun_prop
  have h := hS.min (Sec6.Prop65.isStoppingTime_hitLe (continuous_stopY hBc N) hYm 0 R)
  simpa only [stopN, WithTop.coe_min] using h

/-- Up to `S_N` the Brownian path stays within `N` of its start. -/
theorem abs_sub_le_of_le_stopN (hBc : ∀ ω, Continuous (B · ω)) {R : ℝ≥0} {N : ℝ} (hN : 0 < N) {ω : Ω}
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ stopN B S R N ω) : |B r.toNNReal ω - B 0 ω| ≤ N := by
  have h0 : (0 : ℝ) < stopY B N 0 ω := by simp [stopY, hN]
  have hr' : r.toNNReal ≤ hitLe (stopY B N) 0 R ω := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]; exact hr.trans (NNReal.coe_le_coe.2 (min_le_right _ _))
  have := Sec6.Prop65.le_of_le_hitLe (continuous_stopY hBc N) h0 hr'
  simp only [stopY] at this
  linarith

omit mΩ in
/-- An indicator on a smaller event of an adapted indicator is adapted. -/
theorem measurable_indicator_of_subset {m : MeasurableSpace Ω} {E F : Set Ω} (hE : MeasurableSet[m] E) (hEF : E ⊆ F)
    {f : Ω → ℝ} (hf : Measurable[m] (F.indicator f)) : Measurable[m] (E.indicator f) := by
  have e : E.indicator f = E.indicator (F.indicator f) := by
    rw [indicator_indicator, inter_eq_left.2 hEF]
  rw [e]; exact hf.indicator hE

namespace IsDriverLogField

variable (hL : IsDriverLogField 𝓕 σ ρ K B S ℓ ℓx ℓxx ℓxxx ℓt)
include hL

/-- **The tilt is a driver log-field up to `S_N`** (§A.1.3, the Girsanov step without stochastic integrals): on every
box near the driver before `S_N` the tilt is a log-field with the bound `K + tiltBound`, and its generator vanishes
along the driver because `θ = σℓ_x` there. -/
theorem tilt (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hσ : 0 < σ) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) {R : ℝ≥0} (hSR : ∀ ω, S ω ≤ R) (a : ℝ) {N : ℝ}
    (hN : 0 < N) :
    IsDriverLogField 𝓕 σ ρ (K + tiltBound σ ρ K R a N) B (stopN B S R N) (tiltL σ a B S ℓ ℓx) (tiltLx σ a ℓx)
      ℓxx ℓxxx (tiltLt σ a B ℓx ℓt) where
  loc ω b c y hb hbc hcN hpath := by
    have hcS : c ≤ S ω := hcN.trans (NNReal.coe_le_coe.2 (stopN_le R N ω))
    have hLF := hL.loc ω b c y hb hbc hcS hpath
    have hK : 0 ≤ K := (abs_nonneg _).trans (hL.abs_le hρ ω ⟨le_rfl, (S ω).coe_nonneg⟩)
    have hσa : |a / σ| = |a| / σ := by rw [abs_div, abs_of_pos hσ]
    have hRS : (S ω : ℝ) ≤ R := NNReal.coe_le_coe.2 (hSR ω)
    refine hLF.add_affine (α := a / σ) (β := tiltB σ a B S ℓ ℓx ω)
      (β' := fun t => -(a * drvRate σ B ℓx ω t) - a ^ 2 / 2) (fun t ht => ?_) ?_ (by unfold tiltBound; positivity)
      (fun t ht x hx => ?_) ?_ (fun t ht => ?_)
    · -- the time derivative of `β`
      have hI := hL.hasDerivWithinAt_drvInt hBc hρ ω hb hcS ht
      have h1 : HasDerivWithinAt (fun u => -ℓ ω 0 (σ * B 0 ω) - a * B 0 ω - a * drvInt σ B S ℓx ω u - a ^ 2 / 2 * u)
          (0 - a * drvRate σ B ℓx ω t - a ^ 2 / 2 * 1) (Icc b c) t :=
        ((hasDerivWithinAt_const t _ _).sub (hI.const_mul a)).sub ((hasDerivWithinAt_id t _).const_mul (a ^ 2 / 2))
      show HasDerivWithinAt (fun u => -ℓ ω 0 (σ * B 0 ω) - a * B 0 ω - a * drvInt σ B S ℓx ω u - a ^ 2 / 2 * u) _ _ _
      exact h1.congr_deriv (by ring)
    · exact (continuousOn_const.mul (hL.continuousOn_drvRate hBc hρ ω |>.mono
        (Icc_subset_Icc hb hcS))).neg.sub continuousOn_const
    · -- the affine part on the box
      have hpb := hpath b ⟨le_rfl, hbc⟩
      have hBN := abs_sub_le_of_le_stopN hBc hN hb (hbc.trans hcN)
      have hx0 : |x - σ * B 0 ω| ≤ 4 * ρ + σ * N := by
        have e : x - σ * B 0 ω = (x - y) + (y - σ * B b.toNNReal ω) + σ * (B b.toNNReal ω - B 0 ω) := by ring
        rw [e]
        calc |(x - y) + (y - σ * B b.toNNReal ω) + σ * (B b.toNNReal ω - B 0 ω)|
            ≤ |x - y| + |y - σ * B b.toNNReal ω| + |σ * (B b.toNNReal ω - B 0 ω)| := abs_add_three _ _ _
          _ ≤ 3 * ρ + ρ + σ * N := by
              rw [abs_sub_comm y, abs_mul, abs_of_pos hσ]
              gcongr
          _ = 4 * ρ + σ * N := by ring
      have hc0 : |ℓ ω 0 (σ * B 0 ω)| ≤ K := by
        have := hL.abs_le hρ ω ⟨le_rfl, (S ω).coe_nonneg⟩
        simpa using this
      have ht0 : 0 ≤ t := hb.trans ht.1
      have htR : t ≤ R := ht.2.trans (hcS.trans hRS)
      have hI := hL.abs_drvInt_le hρ ω ht0
      rw [abs_of_pos hσ] at hI
      have e : a / σ * x + tiltB σ a B S ℓ ℓx ω t =
          a / σ * (x - σ * B 0 ω) + (-ℓ ω 0 (σ * B 0 ω)) + (-(a * drvInt σ B S ℓx ω t)) + (-(a ^ 2 / 2 * t)) := by
        unfold tiltB; field_simp; ring
      rw [e]
      refine (abs_add_le _ _).trans ((add_le_add_left (abs_add_three _ _ _) _).trans ?_)
      rw [abs_mul, hσa, abs_neg, abs_neg, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ a ^ 2 / 2 * t)]
      unfold tiltBound
      have h1 : |a| / σ * |x - σ * B 0 ω| ≤ |a| / σ * (4 * ρ + σ * N) :=
        mul_le_mul_of_nonneg_left hx0 (by positivity)
      have h2 : |a| * |drvInt σ B S ℓx ω t| ≤ |a| * (σ * K * R) :=
        mul_le_mul_of_nonneg_left (hI.trans (mul_le_mul_of_nonneg_left htR (by positivity))) (abs_nonneg a)
      have h3 : a ^ 2 / 2 * t ≤ a ^ 2 / 2 * R := mul_le_mul_of_nonneg_left htR (by positivity)
      have h4 : 0 ≤ |a| / σ := by positivity
      have h5 : 0 ≤ |a| * (σ * K) + a ^ 2 / 2 := by positivity
      linarith
    · rw [hσa]; unfold tiltBound
      have h1 : 0 ≤ |a| / σ * (4 * ρ + σ * N) := by positivity
      have h2 : 0 ≤ |a| * (σ * K * R) := by positivity
      have h3 : 0 ≤ a ^ 2 / 2 * R := by positivity
      have h5 : 0 ≤ |a| * (σ * K) + a ^ 2 / 2 := by positivity
      linarith
    · have hg := hL.abs_drvRate_le hρ ω ⟨hb.trans ht.1, ht.2.trans hcS⟩
      rw [abs_of_pos hσ] at hg
      have h : |-(a * drvRate σ B ℓx ω t) - a ^ 2 / 2| ≤ |a| * (σ * K) + a ^ 2 / 2 := by
        calc |-(a * drvRate σ B ℓx ω t) - a ^ 2 / 2| ≤ |-(a * drvRate σ B ℓx ω t)| + |a ^ 2 / 2| := abs_sub _ _
          _ ≤ |a| * (σ * K) + a ^ 2 / 2 := by
              rw [abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ a ^ 2 / 2)]
              gcongr
      unfold tiltBound
      have h1 : 0 ≤ |a| / σ * (4 * ρ + σ * N) := by positivity
      have h2 : 0 ≤ |a| * (σ * K * R) := by positivity
      have h3 : 0 ≤ a ^ 2 / 2 * R := by positivity
      have h4 : 0 ≤ |a| / σ := by positivity
      linarith
  gen ω r hr0 hrN := by
    have hrS : r ≤ S ω := hrN.trans (NNReal.coe_le_coe.2 (stopN_le R N ω))
    have h := hL.gen ω r hr0 hrS
    have hσ0 : σ ≠ 0 := hσ.ne'
    simp only [tiltLt, tiltLx, drvRate]
    have e : σ ^ 2 / 2 * (ℓxx ω r (σ * B r.toNNReal ω) + (ℓx ω r (σ * B r.toNNReal ω) + a / σ) ^ 2) =
        σ ^ 2 / 2 * (ℓxx ω r (σ * B r.toNNReal ω) + ℓx ω r (σ * B r.toNNReal ω) ^ 2) +
          a * (σ * ℓx ω r (σ * B r.toNNReal ω)) + a ^ 2 / 2 := by
      field_simp; ring
    rw [e]; linarith
  meas0 r := by
    have hE := measurableSet_ge_of_isStoppingTime (isStoppingTime_stopN hBc hBm hS R N) r
    have hsub : {ω | r ≤ stopN B S R N ω} ⊆ {ω | r ≤ S ω} := fun ω hω => le_trans hω (stopN_le R N ω)
    have hc : Measurable[𝓕 r] fun ω => ℓ ω 0 (σ * B 0 ω) := by
      have h := hL.meas0 0
      have e : {ω | (0 : ℝ≥0) ≤ S ω}.indicator (fun ω => ℓ ω ((0 : ℝ≥0) : ℝ) (σ * B 0 ω)) =
          fun ω => ℓ ω 0 (σ * B 0 ω) := by
        funext ω; rw [indicator_of_mem (by simp : ω ∈ {ω | (0 : ℝ≥0) ≤ S ω})]; rfl
      rw [e] at h
      exact h.mono (𝓕.mono zero_le) le_rfl
    have hB0 : Measurable[𝓕 r] (B 0) := (hBm 0).mono (𝓕.mono zero_le) le_rfl
    have hI := hL.measurable_drvInt hBc hρ hS r
    have hG : Measurable[𝓕 r] fun ω => {ω | r ≤ S ω}.indicator (fun ω => ℓ ω r (σ * B r ω)) ω +
        (a / σ * (σ * B r ω) + (-ℓ ω 0 (σ * B 0 ω) - a * B 0 ω - a * drvInt σ B S ℓx ω r - a ^ 2 / 2 * r)) := by
      have h0 := hL.meas0 r
      have hF : Continuous fun p : ℝ × ℝ × ℝ × ℝ × ℝ => p.1 + (a / σ * (σ * p.2.1) +
          (-p.2.2.1 - a * p.2.2.2.1 - a * p.2.2.2.2 - a ^ 2 / 2 * (r : ℝ))) := by fun_prop
      exact hF.measurable.comp (h0.prodMk ((hBm r).prodMk (hc.prodMk (hB0.prodMk hI))))
    have e : {ω | r ≤ stopN B S R N ω}.indicator (fun ω => tiltL σ a B S ℓ ℓx ω r (σ * B r ω)) =
        {ω | r ≤ stopN B S R N ω}.indicator fun ω => {ω | r ≤ S ω}.indicator (fun ω => ℓ ω r (σ * B r ω)) ω +
          (a / σ * (σ * B r ω) + (-ℓ ω 0 (σ * B 0 ω) - a * B 0 ω - a * drvInt σ B S ℓx ω r - a ^ 2 / 2 * r)) := by
      refine indicator_congr fun ω hω => ?_
      rw [indicator_of_mem (hsub hω)]; rfl
    rw [e]; exact hG.indicator hE
  meas1 r := by
    have hE := measurableSet_ge_of_isStoppingTime (isStoppingTime_stopN hBc hBm hS R N) r
    have hsub : {ω | r ≤ stopN B S R N ω} ⊆ {ω | r ≤ S ω} := fun ω hω => le_trans hω (stopN_le R N ω)
    have hG : Measurable[𝓕 r] fun ω => {ω | r ≤ S ω}.indicator (fun ω => ℓx ω r (σ * B r ω)) ω + a / σ := by
      exact ((continuous_id.add continuous_const : Continuous fun x : ℝ => x + a / σ)).measurable.comp (hL.meas1 r)
    have e : {ω | r ≤ stopN B S R N ω}.indicator (fun ω => tiltLx σ a ℓx ω r (σ * B r ω)) =
        {ω | r ≤ stopN B S R N ω}.indicator fun ω => {ω | r ≤ S ω}.indicator (fun ω => ℓx ω r (σ * B r ω)) ω + a / σ := by
      refine indicator_congr fun ω hω => ?_
      rw [indicator_of_mem (hsub hω)]; rfl
    rw [e]; exact hG.indicator hE
  meas2 r := measurable_indicator_of_subset
    (measurableSet_ge_of_isStoppingTime (isStoppingTime_stopN hBc hBm hS R N) r)
    (fun ω hω => le_trans hω (stopN_le R N ω)) (hL.meas2 r)

end IsDriverLogField

end Drift

end InteractingSLE.ZhanGT4
