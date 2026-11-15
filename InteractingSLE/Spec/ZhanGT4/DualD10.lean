/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualGirsanovFrozen

/-!
# (D10), I: cut integrals, sums of log-fields, exponential martingales under the tilted measure

Packet PROVE-ZHAN-GT4-A10. Source: Astra, *Follow-up proofs*, §A.1.3 (`ig1_followup_proofs.txt` L341–L353, R38):
"By (D8) and Girsanov, with the other curve stopped, the new drift of `W_j` is `κ_j q_j` … Apply (D3) to the mapped
driver `A_{j,0}`. Its `A_{j,2}`-drift cancels, leaving (D10)."

The stochastic form of (D10) is proved without stochastic integrals, by the same device as the Girsanov step of
`DualGirsanov*`: an exponential `exp ψ` of a second field along the driver is a martingale under the tilted measure
`Q = (M_S/M_0) · P` as soon as `ℓ + ψ` is again a driver log-field (`ℓ = log M̃`). This file supplies the generic tools:

* `cutRate`, `cutInt`: a rate process `g` (continuous on `[0, S]`, bounded, adapted on `{r ≤ S}`) cut at `S`, and its
  integral, which is adapted (`measurable_cutInt`) and has derivative `g` on `[0, S]` (`hasDerivWithinAt_cutInt`);
* `IsLogField.add`: the sum of two regular log-fields;
* **`IsDriverLogField.martingale_addExp`**: if `ℓ` and `ℓ + ψ` are driver log-fields up to `S ≤ R`, then
  `t ↦ exp ψ(t∧S, σB_{t∧S})` is a martingale of `𝓕` under `Q = girsMeasure P σ B S ℓ` (Bayes' formula
  `IsDriverLogField.integral_mul_girsDensity` and the `P`-martingale of `exp(ℓ + ψ)`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

/-! ### Sums of log-fields -/

namespace IsLogField

variable {ℓ ℓx ℓxx ℓxxx ℓt ψ ψx ψxx ψxxx ψt : ℝ → ℝ → ℝ} {b c y ρ K K' : ℝ}

/-- **The sum of two regular log-fields** on the same box is a regular log-field, with the sum of the bounds. -/
theorem add (hL : IsLogField ℓ ℓx ℓxx ℓxxx ℓt b c y ρ K) (hψ : IsLogField ψ ψx ψxx ψxxx ψt b c y ρ K') :
    IsLogField (fun t x => ℓ t x + ψ t x) (fun t x => ℓx t x + ψx t x) (fun t x => ℓxx t x + ψxx t x)
      (fun t x => ℓxxx t x + ψxxx t x) (fun t x => ℓt t x + ψt t x) b c y ρ (K + K') where
  pos := hL.pos
  Knonneg := add_nonneg hL.Knonneg hψ.Knonneg
  dx t ht x hx := (hL.dx t ht x hx).add (hψ.dx t ht x hx)
  dxx t ht x hx := (hL.dxx t ht x hx).add (hψ.dxx t ht x hx)
  dxxx t ht x hx := (hL.dxxx t ht x hx).add (hψ.dxxx t ht x hx)
  dt t ht x hx := (hL.dt t ht x hx).add (hψ.dt t ht x hx)
  cont := hL.cont.add hψ.cont
  contX := hL.contX.add hψ.contX
  contXX := hL.contXX.add hψ.contXX
  contT := hL.contT.add hψ.contT
  bound t ht x hx := by
    obtain ⟨a0, a1, a2, a3, a4⟩ := hL.bound t ht x hx
    obtain ⟨b0, b1, b2, b3, b4⟩ := hψ.bound t ht x hx
    exact ⟨(abs_add_le _ _).trans (add_le_add a0 b0), (abs_add_le _ _).trans (add_le_add a1 b1),
      (abs_add_le _ _).trans (add_le_add a2 b2), (abs_add_le _ _).trans (add_le_add a3 b3),
      (abs_add_le _ _).trans (add_le_add a4 b4)⟩

end IsLogField

/-! ### Rates cut at a stopping time and their integrals -/

section Cut

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

open scoped Classical in
/-- **A rate cut at `S`**, right-continuous in time: `g_r` for `r < S`, `0` afterwards. -/
def cutRate (S : Ω → ℝ≥0) (g : Ω → ℝ → ℝ) (r : ℝ≥0) (ω : Ω) : ℝ :=
  if r < S ω then g ω r else 0

/-- **Its integral** `∫₀ᵗ g_{u} 1_{u < S} du`. -/
def cutInt (S : Ω → ℝ≥0) (g : Ω → ℝ → ℝ) (ω : Ω) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, cutRate S g u.toNNReal ω

variable {𝓕 : Filtration ℝ≥0 mΩ} {S : Ω → ℝ≥0} {g : Ω → ℝ → ℝ} {C : ℝ}

theorem abs_cutRate_le (hgb : ∀ ω r, r ∈ Icc 0 (S ω : ℝ) → |g ω r| ≤ C) (hC : 0 ≤ C) (r : ℝ≥0) (ω : Ω) :
    |cutRate S g r ω| ≤ C := by
  unfold cutRate
  split_ifs with h
  · exact hgb ω r ⟨r.coe_nonneg, NNReal.coe_le_coe.2 h.le⟩
  · rw [abs_zero]; exact hC

/-- The cut rate is right-continuous in time. -/
theorem continuousWithinAt_cutRate (hgc : ∀ ω, ContinuousOn (g ω) (Icc 0 (S ω : ℝ))) (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt (cutRate S g · ω) (Ici t) t := by
  by_cases ht : t < S ω
  · have hgt : ContinuousWithinAt (fun u : ℝ≥0 => g ω (u : ℝ)) (Icc t (S ω)) t := by
      have h1 : ContinuousWithinAt (g ω) (Icc 0 (S ω : ℝ)) (t : ℝ) :=
        hgc ω _ ⟨t.coe_nonneg, NNReal.coe_le_coe.2 ht.le⟩
      exact h1.comp NNReal.continuous_coe.continuousWithinAt fun u hu =>
        ⟨u.coe_nonneg, NNReal.coe_le_coe.2 hu.2⟩
    have hev : ∀ᶠ u in 𝓝[Ici t] t, cutRate S g u ω = g ω (u : ℝ) := by
      have : Iio (S ω) ∈ 𝓝 t := isOpen_Iio.mem_nhds ht
      filter_upwards [nhdsWithin_le_nhds this] with u hu
      simp only [cutRate, mem_Iio.1 hu, ↓reduceIte]
    have hmem : Icc t (S ω) ∈ 𝓝[Ici t] t :=
      mem_nhdsWithin.2 ⟨Iio (S ω), isOpen_Iio, ht, fun u hu => ⟨hu.2, (mem_Iio.1 hu.1).le⟩⟩
    have hgt' := hgt.mono_of_mem_nhdsWithin hmem
    have e : cutRate S g t ω = g ω (t : ℝ) := by simp only [cutRate, ht, ↓reduceIte]
    rw [ContinuousWithinAt, e]
    exact hgt'.congr' (hev.mono fun u hu => hu.symm)
  · push Not at ht
    have hz : ∀ u ∈ Ici t, cutRate S g u ω = 0 := fun u hu => by
      simp only [cutRate, not_lt.2 (ht.trans hu), ↓reduceIte]
    exact (continuousWithinAt_const (b := (0 : ℝ))).congr hz (hz t (mem_Ici.2 le_rfl))

/-- The cut rate is adapted. -/
theorem measurable_cutRate (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hgm : ∀ r : ℝ≥0, Measurable[𝓕 r] ({ω | r ≤ S ω}.indicator fun ω => g ω r)) (r : ℝ≥0) :
    Measurable[𝓕 r] (cutRate S g r) := by
  have hlt : MeasurableSet[𝓕 r] {ω | r < S ω} := by
    have h := (measurableSet_le_of_isStoppingTime hS r).compl
    have he : {ω | S ω ≤ r}ᶜ = {ω | r < S ω} := by ext ω; simp
    rwa [he] at h
  have e : cutRate S g r = {ω | r < S ω}.indicator ({ω | r ≤ S ω}.indicator fun ω => g ω r) := by
    funext ω
    by_cases hω : r < S ω
    · rw [indicator_of_mem (show ω ∈ {ω | r < S ω} from hω),
        indicator_of_mem (show ω ∈ {ω | r ≤ S ω} from hω.le)]
      simp only [cutRate, hω, ↓reduceIte]
    · rw [indicator_of_notMem (show ω ∉ {ω | r < S ω} from hω)]
      simp only [cutRate, hω, ↓reduceIte]
  rw [e]
  exact (hgm r).indicator hlt

/-- The cut rate is progressively measurable. -/
theorem isStronglyProgressive_cutRate (hgc : ∀ ω, ContinuousOn (g ω) (Icc 0 (S ω : ℝ)))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hgm : ∀ r : ℝ≥0, Measurable[𝓕 r] ({ω | r ≤ S ω}.indicator fun ω => g ω r)) :
    IsStronglyProgressive 𝓕 (cutRate S g) :=
  isStronglyProgressive_of_rightContinuous (fun r => (measurable_cutRate hS hgm r).stronglyMeasurable)
    fun ω t => continuousWithinAt_cutRate hgc ω t

/-- **The integral of a cut rate is adapted.** -/
theorem measurable_cutInt (hgc : ∀ ω, ContinuousOn (g ω) (Icc 0 (S ω : ℝ)))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hgm : ∀ r : ℝ≥0, Measurable[𝓕 r] ({ω | r ≤ S ω}.indicator fun ω => g ω r)) (t : ℝ≥0) :
    Measurable[𝓕 t] fun ω => cutInt S g ω t :=
  (Girsanov.stronglyMeasurable_integral_comp (isStronglyProgressive_cutRate hgc hS hgm) measurable_id t).measurable

/-- On `[0, S]` the cut integral is the integral of the rate. -/
theorem cutInt_eq (ω : Ω) {t : ℝ} (ht : t ∈ Icc 0 (S ω : ℝ)) :
    cutInt S g ω t = ∫ u in (0 : ℝ)..t, g ω u := by
  unfold cutInt
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ (S ω : ℝ) := by
    rw [ae_iff]; simp
  filter_upwards [hne] with u hu hmem
  rw [uIoc_of_le ht.1] at hmem
  have hlt : u.toNNReal < S ω := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hmem.1.le]
    exact lt_of_le_of_ne (hmem.2.trans ht.2) hu
  simp only [cutRate, hlt, ↓reduceIte, Real.coe_toNNReal _ hmem.1.le]

/-- **`∂_t ∫₀ᵗ g = g` on `[0, S]`**, within every `[b, c] ⊆ [0, S]`. -/
theorem hasDerivWithinAt_cutInt (hgc : ∀ ω, ContinuousOn (g ω) (Icc 0 (S ω : ℝ))) (ω : Ω) {b c t : ℝ}
    (hb : 0 ≤ b) (hcS : c ≤ S ω) (ht : t ∈ Icc b c) :
    HasDerivWithinAt (cutInt S g ω) (g ω t) (Icc b c) t := by
  have hg := hgc ω
  have htS : t ∈ Icc (0 : ℝ) (S ω) := ⟨hb.trans ht.1, ht.2.trans hcS⟩
  have : Fact (t ∈ Icc (0 : ℝ) (S ω)) := ⟨htS⟩
  have hint : IntervalIntegrable (g ω) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le htS.1]
    exact hg.mono (Icc_subset_Icc_right htS.2)
  have hJ : HasDerivWithinAt (fun u => ∫ x in (0 : ℝ)..u, g ω x) (g ω t) (Icc 0 (S ω : ℝ)) t :=
    intervalIntegral.integral_hasDerivWithinAt_right hint
      (hg.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hg t htS)
  exact (hJ.congr (fun u hu => cutInt_eq ω hu) (cutInt_eq ω htS)).mono (Icc_subset_Icc hb hcS)

/-- `|∫₀ᵗ g 1_{· < S}| ≤ C t`. -/
theorem abs_cutInt_le (hgb : ∀ ω r, r ∈ Icc 0 (S ω : ℝ) → |g ω r| ≤ C) (hC : 0 ≤ C) (ω : Ω) {t : ℝ}
    (ht : 0 ≤ t) : |cutInt S g ω t| ≤ C * t := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := C)
    (f := fun u : ℝ => cutRate S g u.toNNReal ω) fun u _ => by
      rw [Real.norm_eq_abs]; exact abs_cutRate_le hgb hC _ ω
  rwa [sub_zero, abs_of_nonneg ht] at h

/-- The cut integral vanishes at time `0`. -/
theorem cutInt_zero (ω : Ω) : cutInt S g ω 0 = 0 := by simp [cutInt]

end Cut

/-! ### Exponential martingales under the tilted measure -/

section Bayes

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {σ ρ K K' : ℝ} {B : ℝ≥0 → Ω → ℝ}
  {S : Ω → ℝ≥0} {ℓ ℓx ℓxx ℓxxx ℓt ψ ℓx' ℓxx' ℓxxx' ℓt' : Ω → ℝ → ℝ → ℝ}

/-- **The added exponential along the stopped driver**, `exp ψ(t∧S, σB_{t∧S})`. -/
def addExp (σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (ψ : Ω → ℝ → ℝ → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  logFieldExp σ B ψ (min t (S ω)) ω

omit mΩ in
theorem logFieldExp_add (σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ℓ ψ : Ω → ℝ → ℝ → ℝ) (r : ℝ≥0) (ω : Ω) :
    logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) r ω = logFieldExp σ B ℓ r ω * logFieldExp σ B ψ r ω := by
  simp only [logFieldExp, Real.exp_add]

omit mΩ in
theorem addExp_eq_div (t : ℝ≥0) (ω : Ω) :
    addExp σ B S ψ t ω = logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min t (S ω)) ω /
      logFieldExp σ B ℓ (min t (S ω)) ω := by
  have h0 : logFieldExp σ B ℓ (min t (S ω)) ω ≠ 0 := (Real.exp_pos _).ne'
  rw [logFieldExp_add, mul_div_cancel_left₀ _ h0, addExp]

namespace IsDriverLogField

variable (hL : IsDriverLogField 𝓕 σ ρ K B S ℓ ℓx ℓxx ℓxxx ℓt)
  (hL' : IsDriverLogField 𝓕 σ ρ K' B S (fun ω t x => ℓ ω t x + ψ ω t x) ℓx' ℓxx' ℓxxx' ℓt')
include hL hL'

/-- `|ψ| ≤ K + K'` along the stopped driver. -/
theorem abs_addExp_le (hρ : 0 < ρ) (t : ℝ≥0) (ω : Ω) : |addExp σ B S ψ t ω| ≤ Real.exp (K + K') := by
  have hτ : ((min t (S ω) : ℝ≥0) : ℝ) ∈ Icc 0 (S ω : ℝ) :=
    ⟨(min t (S ω)).coe_nonneg, NNReal.coe_le_coe.2 (min_le_right _ _)⟩
  have h1 := hL.abs_le hρ ω hτ
  have h2 := hL'.abs_le hρ ω hτ
  simp only [Real.toNNReal_coe] at h1 h2
  rw [addExp, logFieldExp, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  linarith [(_root_.abs_le.1 h1).1, (_root_.abs_le.1 h2).2]

/-- The added exponential is adapted. -/
theorem measurable_addExp (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (t : ℝ≥0) :
    Measurable[𝓕 t] (addExp σ B S ψ t) := by
  have h1 := hL.measurable_logFieldExp_stopped hBc hρ hS (fun ω => le_rfl) t
  have h2 := hL'.measurable_logFieldExp_stopped hBc hρ hS (fun ω => le_rfl) t
  have e : addExp σ B S ψ t = fun ω => logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min t (S ω)) ω /
      logFieldExp σ B ℓ (min t (S ω)) ω := funext fun ω => addExp_eq_div t ω
  rw [e]
  exact h2.div h1

/-- **The martingale step under `Q`**: for `s ≤ t` and `A ∈ 𝓕_s`, `∫_A exp ψ_{t∧S} dQ = ∫_A exp ψ_{s∧S} dQ`. -/
theorem setIntegral_addExp_eq {P : Measure Ω} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hσ : 0 < σ) (hρ : 0 < ρ) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    {R : ℝ≥0} (hSR : ∀ ω, S ω ≤ R) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) :
    ∫ ω in A, addExp σ B S ψ t ω ∂(girsMeasure P σ B S ℓ) =
      ∫ ω in A, addExp σ B S ψ s ω ∂(girsMeasure P σ B S ℓ) := by
  have hP := hB.isProbabilityMeasure'
  have hAm : MeasurableSet A := 𝓕.le s A hA
  have hDm : AEStronglyMeasurable (girsDensity σ B S ℓ) P := by
    have hmR := (hL.measurable_girsN_zero hBc hσ.ne' hρ hS R).mono (𝓕.le R) le_rfl
    have e : girsDensity σ B S ℓ = girsN σ 0 B S ℓ ℓx R :=
      funext fun ω => girsDensity_eq_girsN hσ.ne' (hSR ω)
    rw [e]; exact hmR.aestronglyMeasurable
  have hDpos : ∀ ω, 0 ≤ girsDensity σ B S ℓ ω := fun ω => (Real.exp_pos _).le
  -- the initial factor `e^{−ℓ(0, σB_0) − K}`
  have hℓ0m : Measurable[𝓕 s] fun ω => ℓ ω 0 (σ * B 0 ω) := by
    have h := hL.meas0 0
    have e : {ω | (0 : ℝ≥0) ≤ S ω}.indicator (fun ω => ℓ ω ((0 : ℝ≥0) : ℝ) (σ * B 0 ω)) =
        fun ω => ℓ ω 0 (σ * B 0 ω) := by
      funext ω; rw [indicator_of_mem (by simp : ω ∈ {ω | (0 : ℝ≥0) ≤ S ω})]; rfl
    rw [e] at h
    exact h.mono (𝓕.mono zero_le) le_rfl
  have hℓ0b : ∀ ω, |ℓ ω 0 (σ * B 0 ω)| ≤ K := fun ω => by
    have h := hL.abs_le hρ ω ⟨le_rfl, (S ω).coe_nonneg⟩
    simpa only [Real.toNNReal_zero] using h
  set ξ : Ω → ℝ := A.indicator fun ω => Real.exp (-ℓ ω 0 (σ * B 0 ω) - K) with hξ
  have hξm : Measurable[𝓕 s] ξ :=
    (Real.continuous_exp.measurable.comp (hℓ0m.neg.sub_const K)).indicator hA
  have hξb : ∀ ω, |ξ ω| ≤ 1 := fun ω => by
    by_cases hω : ω ∈ A
    · rw [hξ, indicator_of_mem hω, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.2
      linarith [(_root_.abs_le.1 (hℓ0b ω)).1]
    · rw [hξ, indicator_of_notMem hω, abs_zero]; exact zero_le_one
  have hM'm : ∀ u : ℝ≥0, Measurable[𝓕 u] fun ω =>
      logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min u (S ω)) ω := fun u =>
    hL'.measurable_logFieldExp_stopped hBc hρ hS (fun ω => le_rfl) u
  have hint : ∀ u : ℝ≥0, Integrable (fun ω => ξ ω *
      logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min u (S ω)) ω) P := fun u =>
    ((integrable_const (Real.exp K')).mono' ((hM'm u).mono (𝓕.le u) le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact hL'.abs_logFieldExp_le hρ (min_le_right _ _))).bdd_mul
      ((hξm.mono (𝓕.le s) le_rfl).aestronglyMeasurable)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hξb ω)
  have key : ∀ u : ℝ≥0, s ≤ u → ∫ ω in A, addExp σ B S ψ u ω ∂(girsMeasure P σ B S ℓ) =
      Real.exp K * ∫ ω, ξ ω * logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min u (S ω)) ω ∂P :=
    fun u hsu => by
    have hf := hL.measurable_addExp hL' hBc hρ hS u
    have hY : Measurable[𝓕 u] (A.indicator (addExp σ B S ψ u)) := hf.indicator (𝓕.mono hsu _ hA)
    have hYi : Integrable (A.indicator (addExp σ B S ψ u)) P := by
      refine ((integrable_const (Real.exp (K + K'))).mono' (hf.mono (𝓕.le u) le_rfl).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)).indicator hAm
      rw [Real.norm_eq_abs]; exact hL.abs_addExp_le hL' hρ u ω
    have hb := hL.integral_mul_girsDensity hB hBc hσ hρ hS hSR u hY hYi
    rw [girsMeasure, MathFin.setIntegral_withDensity_ofReal hDm hDpos _ hAm, ← integral_indicator hAm]
    have e1 : (A.indicator fun ω => addExp σ B S ψ u ω * girsDensity σ B S ℓ ω) =
        fun ω => A.indicator (addExp σ B S ψ u) ω * girsDensity σ B S ℓ ω := by
      funext ω; by_cases hω : ω ∈ A <;> simp [hω]
    rw [e1, hb, ← integral_const_mul]
    congr 1; funext ω
    by_cases hω : ω ∈ A
    · rw [indicator_of_mem hω, hξ, indicator_of_mem hω, girsN_zero_eq hσ.ne', addExp]
      simp only [logFieldExp]
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    · rw [indicator_of_notMem hω, hξ, indicator_of_notMem hω]; ring
  have h0 := hL'.integral_mul_logField_stopped_sub_eq_zero hB hBc hσ.le hρ hS hst hξm hξb
  rw [key t hst, key s le_rfl]
  congr 1
  have hsub : (fun ω => ξ ω * logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min t (S ω)) ω -
      ξ ω * logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min s (S ω)) ω) =
      fun ω => ξ ω * (logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min t (S ω)) ω -
        logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min s (S ω)) ω) := by
    funext ω; ring
  have h1 : (∫ ω, ξ ω * logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min t (S ω)) ω ∂P) -
      ∫ ω, ξ ω * logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min s (S ω)) ω ∂P = 0 := by
    rw [← integral_sub (hint t) (hint s), hsub]; exact h0
  linarith

/-- **`exp ψ` along the stopped driver is a `Q`-martingale**, `Q = (M_S/M_0) · P`, whenever `ℓ` and `ℓ + ψ` are
driver log-fields up to `S ≤ R`. -/
theorem martingale_addExp {P : Measure Ω} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hσ : 0 < σ) (hρ : 0 < ρ) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    {R : ℝ≥0} (hSR : ∀ ω, S ω ≤ R) :
    Martingale (addExp σ B S ψ) 𝓕 (girsMeasure P σ B S ℓ) := by
  have hQ := hL.isProbabilityMeasure_girsMeasure hB hBc hσ hρ hS hSR
  have hm := fun t => hL.measurable_addExp hL' hBc hρ hS t
  have hi : ∀ t, Integrable (addExp σ B S ψ t) (girsMeasure P σ B S ℓ) := fun t =>
    (integrable_const (Real.exp (K + K'))).mono' ((hm t).mono (𝓕.le t) le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hL.abs_addExp_le hL' hρ t ω)
  refine ⟨fun t => (hm t).stronglyMeasurable, fun s t hst => ?_⟩
  exact (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hi t) (fun A _ _ => (hi s).integrableOn)
    (fun A hA _ => (hL.setIntegral_addExp_eq hL' hB hBc hσ hρ hS hSR hst hA).symm)
    ((hm s).stronglyMeasurable.aestronglyMeasurable)).symm

end IsDriverLogField

end Bayes

end InteractingSLE.ZhanGT4
