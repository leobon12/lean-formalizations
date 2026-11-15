/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MixtureA33ChordalForced
import InteractingSLE.Spec.Zhan.StripNoncollision

/-!
# Brownian scaling of integrated `SLE_κ(ρ)` evolutions

Packet PROVE-ZHAN-A33. For `c > 0` and `a = (√c)⁻¹`, the scaled paths `w'(t) = a w(c t)`, `v'(t) = a v(c t)`,
`b'(t) = a b(c t)` with lifetime `ζ/c` satisfy the frozen `IsIntegratedSLEPath` of the scaled word `(a xL, a xR)`
with the same weights (`isIntegratedSLEPath_scale`), and the scaled processes, with the time-scaled filtration
`t ↦ 𝓕(c t)`, form an integrated evolution (`isIntegratedSLEEvolution_scale`; Brownian scaling is Mathlib's
`IsBrownianReal.smul`). The strip life and the strip clock are scale invariant (`isStripLife_scale_iff`,
`stripClock_scale`), so an unbounded strip clock transfers back (`hasUnboundedStripClock_of_scale`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.UpMark

open Zhan

/-! ### Real-variable helpers -/

theorem nnreal_mul_toNNReal (c : ℝ≥0) (s : ℝ) : c * s.toNNReal = ((c : ℝ) * s).toNNReal := by
  rw [Real.toNNReal_mul c.coe_nonneg, Real.toNNReal_coe]

/-- `∫₀ᵗ g(c s) ds = c⁻¹ ∫₀^{ct} g`. -/
theorem integral_scale (c : ℝ≥0) (hc : c ≠ 0) (g : ℝ≥0 → ℝ) (t : ℝ≥0) :
    ∫ s in (0 : ℝ)..t, g (c * s.toNNReal) = (c : ℝ)⁻¹ * ∫ r in (0 : ℝ)..((c * t : ℝ≥0) : ℝ), g r.toNNReal := by
  have hc' : (c : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hc
  simp_rw [nnreal_mul_toNNReal]
  rw [intervalIntegral.integral_comp_mul_left (fun r => g r.toNNReal) hc', smul_eq_mul, mul_zero,
    NNReal.coe_mul]

theorem intervalIntegrable_scale (c : ℝ≥0) (hc : c ≠ 0) {g : ℝ≥0 → ℝ} {t : ℝ≥0}
    (hg : IntervalIntegrable (fun r : ℝ => g r.toNNReal) volume 0 ((c * t : ℝ≥0) : ℝ)) :
    IntervalIntegrable (fun s : ℝ => g (c * s.toNNReal)) volume 0 t := by
  have hc' : (c : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hc
  simp_rw [nnreal_mul_toNNReal]
  have h := hg.comp_mul_left (c := (c : ℝ))
  rw [zero_div, NNReal.coe_mul, mul_div_cancel_left₀ _ hc'] at h
  exact h

theorem coe_lt_div_iff {c : ℝ≥0} (hc : c ≠ 0) {t : ℝ≥0} {ζ : ℝ≥0∞} :
    (t : ℝ≥0∞) < ζ / c ↔ ((c * t : ℝ≥0) : ℝ≥0∞) < ζ := by
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by exact_mod_cast hc)) (Or.inl ENNReal.coe_ne_top), mul_comm,
    ENNReal.coe_mul]

/-! ### Scaled paths -/

/-- The scaled path `t ↦ a f(c t)`. -/
def scalePath (a : ℝ) (c : ℝ≥0) (f : ℝ≥0 → ℝ) : ℝ≥0 → ℝ := fun t => a * f (c * t)

/-- `∫₀ᵗ ρ/(a f(cs) − a g(cs)) = a ∫₀^{ct} ρ/(f − g)` when `a² c = 1`. -/
theorem integral_scale_div (c : ℝ≥0) (hc : c ≠ 0) {a : ℝ} (ha : a ≠ 0) (hac : a ^ 2 * c = 1) (ρ : ℝ)
    (f g : ℝ≥0 → ℝ) (t : ℝ≥0) :
    ∫ s in (0 : ℝ)..t, ρ / (scalePath a c f s.toNNReal - scalePath a c g s.toNNReal) =
      a * ∫ r in (0 : ℝ)..((c * t : ℝ≥0) : ℝ), ρ / (f r.toNNReal - g r.toNNReal) := by
  have e : ∀ s : ℝ, ρ / (scalePath a c f s.toNNReal - scalePath a c g s.toNNReal) =
      a⁻¹ * (fun r : ℝ≥0 => ρ / (f r - g r)) (c * s.toNNReal) := fun s => by
    simp only [scalePath]
    rw [← mul_sub]
    by_cases h : f (c * s.toNNReal) - g (c * s.toNNReal) = 0
    · rw [h]; simp
    · field_simp
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, integral_scale c hc (fun r => ρ / (f r - g r)) t, ← mul_assoc]
  congr 1
  have hc' : (c : ℝ) = (a ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right hac
  rw [hc', inv_inv]
  field_simp

theorem intervalIntegrable_scale_inv (c : ℝ≥0) (hc : c ≠ 0) {a : ℝ} (f g : ℝ≥0 → ℝ) {t : ℝ≥0}
    (h : IntervalIntegrable (fun r : ℝ => (f r.toNNReal - g r.toNNReal)⁻¹) volume 0 ((c * t : ℝ≥0) : ℝ)) :
    IntervalIntegrable (fun s : ℝ => (scalePath a c f s.toNNReal - scalePath a c g s.toNNReal)⁻¹) volume 0 t := by
  have h' := (intervalIntegrable_scale c hc (g := fun r => (f r - g r)⁻¹) h).const_mul a⁻¹
  refine h'.congr fun s _ => ?_
  simp only [scalePath]
  rw [← mul_sub, mul_inv]

theorem continuousOn_scalePath {c : ℝ≥0} (hc : c ≠ 0) (a : ℝ) {f : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hf : ContinuousOn f {t | (t : ℝ≥0∞) < ζ}) :
    ContinuousOn (scalePath a c f) {t | (t : ℝ≥0∞) < ζ / c} :=
  continuousOn_const.mul (hf.comp (continuous_const.mul continuous_id).continuousOn
    fun _ ht => (coe_lt_div_iff hc).1 ht)

theorem thresholdCondition_smul {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {a : ℝ} (ha : a ≠ 0)
    (w : ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) :
    ForceWord.ThresholdCondition ρL ρR (a * w) (fun i => a * vL i) (fun j => a * vR j) ↔
      ForceWord.ThresholdCondition ρL ρR w vL vR := by
  simp only [ForceWord.ThresholdCondition, mul_right_inj' ha]

/-- **Brownian scaling of the frozen path conditions.** -/
theorem isIntegratedSLEPath_scale {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {c : ℝ≥0} (hc : c ≠ 0) {a : ℝ} (ha : 0 < a) (hac : a ^ 2 * c = 1)
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) :
    IsIntegratedSLEPath κ (fun i => a * xL i) (fun j => a * xR j) ρL ρR (scalePath a c w)
      (fun i => scalePath a c (vL i)) (fun j => scalePath a c (vR j)) (scalePath a c b) (ζ / c) := by
  obtain ⟨hw0, hvL0, hvR0, hcw, hcvL, hcvR, hantiL, hleL, hleR, hmonoR, hintL, hintR, hweq, hvLeq, hvReq,
    hcolL, hcolR, hnth, hth0, hthT⟩ := hp
  have hlt : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ / c → ((c * t : ℝ≥0) : ℝ≥0∞) < ζ := fun ht => (coe_lt_div_iff hc).1 ht
  have hcolset : ∀ f g : ℝ≥0 → ℝ, volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ f s.toNNReal = g s.toNNReal} = 0 →
      volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ / c ∧
        scalePath a c f s.toNNReal = scalePath a c g s.toNNReal} = 0 := by
    intro f g h0
    have hc' : (c : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hc
    refine measure_mono_null (fun s hs => ?_) ((Real.volume_preimage_mul_left hc' _).trans (by rw [h0, mul_zero]))
    obtain ⟨hs0, hsζ, hfg⟩ := hs
    simp only [scalePath, mul_right_inj' ha.ne'] at hfg
    refine ⟨mul_nonneg c.coe_nonneg hs0, ?_, ?_⟩
    · rw [← nnreal_mul_toNNReal]; exact hlt hsζ
    · rw [← nnreal_mul_toNNReal]; exact hfg
  refine ⟨by simp [scalePath, hw0], fun i => by simp [scalePath, hvL0], fun j => by simp [scalePath, hvR0],
    continuousOn_scalePath hc a hcw, fun i => continuousOn_scalePath hc a (hcvL i),
    fun j => continuousOn_scalePath hc a (hcvR j),
    fun t ht i j hij => mul_le_mul_of_nonneg_left (hantiL _ (hlt ht) hij) ha.le,
    fun t ht i => mul_le_mul_of_nonneg_left (hleL _ (hlt ht) i) ha.le,
    fun t ht i => mul_le_mul_of_nonneg_left (hleR _ (hlt ht) i) ha.le,
    fun t ht i j hij => mul_le_mul_of_nonneg_left (hmonoR _ (hlt ht) hij) ha.le,
    fun t ht i => intervalIntegrable_scale_inv c hc w (vL i) (hintL _ (hlt ht) i),
    fun t ht j => intervalIntegrable_scale_inv c hc w (vR j) (hintR _ (hlt ht) j),
    fun t ht => ?_, fun t ht i => ?_, fun t ht j => ?_, fun i => hcolset w (vL i) (hcolL i),
    fun j => hcolset w (vR j) (hcolR j), fun t ht => ?_, fun h0 => ?_, fun T hT hTζ w₀ vL₀ vR₀ hlim => ?_⟩
  · simp_rw [integral_scale_div c hc ha.ne' hac]
    simp only [scalePath]
    rw [hweq _ (hlt ht), ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  · rw [integral_scale_div c hc ha.ne' hac]
    simp only [scalePath]
    rw [hvLeq _ (hlt ht) i]
    ring
  · rw [integral_scale_div c hc ha.ne' hac]
    simp only [scalePath]
    rw [hvReq _ (hlt ht) j]
    ring
  · simp only [scalePath]
    rw [thresholdCondition_smul ρL ρR ha.ne']
    exact hnth _ (hlt ht)
  · have hζ : ζ = 0 := by
      rcases ENNReal.div_eq_zero_iff.1 h0 with h | h
      · exact h
      · exact absurd h ENNReal.coe_ne_top
    have h := (thresholdCondition_smul ρL ρR ha.ne' 0 xL xR).2 (hth0 hζ)
    simpa using h
  · -- the limit at `c T` of the original paths
    have hcT : (0 : ℝ≥0) < c * T := mul_pos (pos_iff_ne_zero.2 hc) hT
    have hcTζ : ((c * T : ℝ≥0) : ℝ≥0∞) = ζ := by
      rw [ENNReal.coe_mul, mul_comm, hTζ, ENNReal.div_mul_cancel (by exact_mod_cast hc) ENNReal.coe_ne_top]
    have hmap : Tendsto (fun s : ℝ≥0 => s / c) (𝓝[<] (c * T)) (𝓝[<] T) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Continuous fun s : ℝ≥0 => s / c := continuous_id.div_const c
        have h := (this.tendsto (c * T)).mono_left (nhdsWithin_le_nhds (s := Iio (c * T)))
        rwa [mul_div_cancel_left₀ T hc] at h
      · filter_upwards [self_mem_nhdsWithin] with s hs
        rw [mem_Iio, div_lt_iff₀ (pos_iff_ne_zero.2 hc), mul_comm]
        exact hs
    have hlim' := (hlim.comp hmap)
    have hcont : Continuous fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) =>
        (a⁻¹ * p.1, fun i => a⁻¹ * p.2.1 i, fun j => a⁻¹ * p.2.2 j) := by fun_prop
    have hlim'' := (hcont.tendsto _).comp hlim'
    have heq : (fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) =>
        (a⁻¹ * p.1, fun i => a⁻¹ * p.2.1 i, fun j => a⁻¹ * p.2.2 j)) ∘
        ((fun t => (scalePath a c w t, fun i => scalePath a c (vL i) t, fun j => scalePath a c (vR j) t)) ∘
          fun s : ℝ≥0 => s / c) = fun s => (w s, fun i => vL i s, fun j => vR j s) := by
      funext s
      simp only [Function.comp_apply, scalePath, mul_div_cancel₀ s hc, ← mul_assoc, inv_mul_cancel₀ ha.ne',
        one_mul]
    rw [heq] at hlim''
    have h := hthT (c * T) hcT hcTζ _ _ _ hlim''
    rw [← thresholdCondition_smul ρL ρR ha.ne'] at h
    simpa only [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] using h

/-! ### Scaled evolutions -/

section Evolution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The time-scaled filtration `t ↦ 𝓕(c t)`. -/
def scaleFilt (𝓕 : Filtration ℝ≥0 mΩ) (c : ℝ≥0) : Filtration ℝ≥0 mΩ where
  seq t := 𝓕 (c * t)
  mono' _ _ h := 𝓕.mono (mul_le_mul_of_nonneg_left h (zero_le (a := c)))
  le' _ := 𝓕.le _

/-- The scaled process `t ↦ (√c)⁻¹ X(c t)` (Mathlib's Brownian scaling). -/
def scaleProc (c : ℝ≥0) (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t ω => (Real.sqrt c)⁻¹ * X (c * t) ω

theorem scaleFactor_pos {c : ℝ≥0} (hc : c ≠ 0) : 0 < (Real.sqrt c)⁻¹ :=
  inv_pos.2 (Real.sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)))

theorem scaleFactor_sq_mul {c : ℝ≥0} (hc : c ≠ 0) : ((Real.sqrt c)⁻¹) ^ 2 * c = 1 := by
  rw [inv_pow, Real.sq_sqrt c.coe_nonneg, inv_mul_cancel₀ (NNReal.coe_ne_zero.2 hc)]

/-- **Brownian scaling with the filtration.** -/
theorem isFilteredBrownianReal_scale {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} {c : ℝ≥0}
    (hc : c ≠ 0) (hB : IsFilteredBrownianReal 𝓕 B P) :
    IsFilteredBrownianReal (scaleFilt 𝓕 c) (scaleProc c B) P := by
  refine ⟨hB.1.smul hc, fun t => (hB.2.1 (c * t)).const_mul _, fun s t hst => ?_⟩
  have h := hB.2.2 (c * s) (c * t) (mul_le_mul_of_nonneg_left hst (zero_le (a := c)))
  refine indep_of_indep_of_le_left h ?_
  have h1 : Measurable[MeasurableSpace.comap (fun ω => B (c * t) ω - B (c * s) ω) inferInstance]
      (fun ω => B (c * t) ω - B (c * s) ω) := comap_measurable _
  have e : (fun ω => scaleProc c B t ω - scaleProc c B s ω) =
      (fun x => (Real.sqrt c)⁻¹ * x) ∘ fun ω => B (c * t) ω - B (c * s) ω := by
    funext ω; simp only [scaleProc, Function.comp_apply]; ring
  have hm : Measurable[MeasurableSpace.comap (fun ω => B (c * t) ω - B (c * s) ω) inferInstance]
      (fun ω => scaleProc c B t ω - scaleProc c B s ω) := by
    rw [e]; exact (measurable_const_mul _).comp h1
  exact hm.comap_le

theorem adaptedBefore_scale {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ} {c : ℝ≥0}
    (hc : c ≠ 0) (hX : AdaptedBefore 𝓕 ζ X) :
    AdaptedBefore (scaleFilt 𝓕 c) (fun ω => ζ ω / c) (scaleProc c X) := by
  intro t A hA
  have e : {ω | (t : ℝ≥0∞) < ζ ω / c ∧ scaleProc c X t ω ∈ A} =
      {ω | ((c * t : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ X (c * t) ω ∈ (fun x => (Real.sqrt c)⁻¹ * x) ⁻¹' A} := by
    ext ω
    simp only [mem_ofPred_eq, coe_lt_div_iff hc, scaleProc, mem_preimage]
  rw [e]
  exact hX (c * t) _ ((measurable_const_mul _) hA)

/-- **Brownian scaling of integrated `SLE_κ(ρ)` evolutions**: `t ↦ (√c)⁻¹ (W, V, B)(c t)` with the lifetime `ζ/c`
and the filtration `𝓕(c ·)` is an integrated evolution of the word `(√c)⁻¹ (x^L, x^R)` with the same weights. -/
theorem isIntegratedSLEEvolution_scale {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {c : ℝ≥0}
    (hc : c ≠ 0) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    IsIntegratedSLEEvolution κ (fun i => (Real.sqrt c)⁻¹ * xL i) (fun j => (Real.sqrt c)⁻¹ * xR j) ρL ρR P
      (scaleFilt 𝓕 c) (scaleProc c W) (fun i => scaleProc c (VL i)) (fun j => scaleProc c (VR j))
      (scaleProc c B) (fun ω => ζ ω / c) := by
  obtain ⟨hB, hW, hVL, hVR, hp⟩ := hE
  refine ⟨isFilteredBrownianReal_scale hc hB, adaptedBefore_scale hc hW, fun i => adaptedBefore_scale hc (hVL i),
    fun j => adaptedBefore_scale hc (hVR j), ?_⟩
  filter_upwards [hp] with ω hω
  exact isIntegratedSLEPath_scale hc (scaleFactor_pos hc) (scaleFactor_sq_mul hc) hω

end Evolution

/-! ### Strip life and strip clock under scaling -/

theorem stripClock_scalePath {c : ℝ≥0} (hc : c ≠ 0) {a : ℝ} (ha : a ≠ 0) (hac : a ^ 2 * c = 1)
    (w v : ℝ≥0 → ℝ) (s : ℝ≥0) :
    Strip.stripClock (Strip.extPath (scalePath a c w)) (Strip.extPath (scalePath a c v)) s =
      Strip.stripClock (Strip.extPath w) (Strip.extPath v) (c * s : ℝ≥0) := by
  have e : ∀ u : ℝ, ((Strip.extPath (scalePath a c w) u - Strip.extPath (scalePath a c v) u) ^ 2)⁻¹ =
      (a ^ 2)⁻¹ * (fun r : ℝ≥0 => ((w r - v r) ^ 2)⁻¹) (c * u.toNNReal) := fun u => by
    simp only [Strip.extPath, scalePath]
    rw [← mul_sub, mul_pow, mul_inv]
  simp only [Strip.stripClock]
  simp_rw [e]
  have hI := integral_scale c hc (fun r => ((w r - v r) ^ 2)⁻¹) s
  rw [intervalIntegral.integral_const_mul, hI, ← mul_assoc]
  have hc' : (c : ℝ) = (a ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right hac
  rw [hc', inv_inv, inv_mul_cancel₀ (pow_ne_zero 2 ha), one_mul]
  rfl

theorem isStripLife_scalePath_iff {c : ℝ≥0} (hc : c ≠ 0) {a : ℝ} (ha : 0 < a) {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    {s : ℝ≥0} :
    Strip.IsStripLife (scalePath a c w) (scalePath a c v) (ζ / c) s ↔ Strip.IsStripLife w v ζ (c * s) := by
  constructor
  · rintro ⟨hs, hlt⟩
    refine ⟨(coe_lt_div_iff hc).1 hs, fun r hr => ?_⟩
    have hr' : r / c ≤ s := by rw [div_le_iff₀ (pos_iff_ne_zero.2 hc), mul_comm]; exact hr
    have h := hlt (r / c) hr'
    simp only [scalePath, mul_div_cancel₀ r hc] at h
    exact lt_of_mul_lt_mul_left h ha.le
  · rintro ⟨hs, hlt⟩
    refine ⟨(coe_lt_div_iff hc).2 hs, fun r hr => ?_⟩
    simp only [scalePath]
    exact mul_lt_mul_of_pos_left (hlt (c * r) (mul_le_mul_of_nonneg_left hr (zero_le (a := c)))) ha

/-- **An unbounded strip clock transfers back from the scaled paths.** -/
theorem hasUnboundedStripClock_of_scale {c : ℝ≥0} (hc : c ≠ 0) {a : ℝ} (ha : 0 < a) (hac : a ^ 2 * c = 1)
    {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (h : HasUnboundedStripClock (scalePath a c w) (scalePath a c v) (ζ / c)) :
    HasUnboundedStripClock w v ζ := fun T => by
  obtain ⟨s, hs, hT⟩ := h T
  exact ⟨c * s, (isStripLife_scalePath_iff hc ha).1 hs, by rwa [stripClock_scalePath hc ha.ne' hac] at hT⟩

end InteractingSLE.ZhanGT4.UpMark
