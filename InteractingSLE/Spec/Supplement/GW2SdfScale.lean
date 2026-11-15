/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdeStage
import InteractingSLE.Spec.ZhanGT4.MixtureA33ChordalScale
import InteractingSLE.Spec.Sec2.Assembly2UpTo

/-!
# GW2's retained stopped SDE: Brownian scaling and reflection of stopped local dynamics

Packet PROVE-GW2-SDE (round 3). ROOT2's actual samples (`RootJ31.sourceSample`) read the future driver in a DILATED
and ORIENTED frame: `stageDriverRead a ε … u = ε · a · (D(F_T + u/a²) − D(F_{v₀}))` with `a = 2^{r.2}` and
`ε = (−1)^{|l|}`. The SDE half produces stopped local dynamics for the stage relative driver in GB6's joint-chart
frame. This file transports `GW2JDetR11.LocalDynamics.IsStopped` through the two frame changes:

* `isSLEPathUpTo_scale`: Brownian scaling of the local path conditions (`IsIntegratedSLEPath` scaling of
  `ZhanGT4.UpMark.isIntegratedSLEPath_scale`, restricted to the stopped conditions);
* `LocalDynamics.scale`, **`LocalDynamics.IsStopped.scale`**: `t ↦ (√c)⁻¹ (W, V, B)(c t)`, stop `τ/c`, filtration
  `𝓕(c ·)`, word `(√c)⁻¹ x`, same weights;
* `LocalDynamics.reflect`, **`LocalDynamics.IsStopped.reflect`**: `x ↦ −x` with the sides exchanged (`W ↦ −W`,
  left marks `−V^R`, right marks `−V^L`, `B ↦ −B`), word `(−x^R, ρ^R; −x^L, ρ^L)`;
* **`exists_isStopped_scale`**, **`exists_isStopped_reflect`**: the existence forms used by `chooseDyn`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdf

open ZhanGT4.UpMark GW2JDetR11

/-! ### Scaling of the local path conditions -/

theorem volume_collision_scale {c : ℝ≥0} (hc : c ≠ 0) {a : ℝ} (ha : 0 < a) {τ : ℝ≥0∞} (f g : ℝ≥0 → ℝ)
    (h0 : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < τ ∧ f s.toNNReal = g s.toNNReal} = 0) :
    volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < τ / c ∧
      scalePath a c f s.toNNReal = scalePath a c g s.toNNReal} = 0 := by
  have hc' : (c : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hc
  refine measure_mono_null (fun s hs => ?_) ((Real.volume_preimage_mul_left hc' _).trans (by rw [h0, mul_zero]))
  obtain ⟨hs0, hsζ, hfg⟩ := hs
  simp only [scalePath, mul_right_inj' ha.ne'] at hfg
  refine ⟨mul_nonneg c.coe_nonneg hs0, ?_, ?_⟩
  · rw [← nnreal_mul_toNNReal]; exact (coe_lt_div_iff hc).1 hsζ
  · rw [← nnreal_mul_toNNReal]; exact hfg

/-- **Brownian scaling of the local path conditions.** -/
theorem isSLEPathUpTo_scale {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {τ : ℝ≥0∞}
    {c : ℝ≥0} (hc : c ≠ 0) {a : ℝ} (ha : 0 < a) (hac : a ^ 2 * c = 1)
    (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b τ) :
    Sec2.IsSLEPathUpTo κ (fun i => a * xL i) (fun j => a * xR j) ρL ρR (scalePath a c w)
      (fun i => scalePath a c (vL i)) (fun j => scalePath a c (vR j)) (scalePath a c b) (τ / c) where
  w_zero := by simp [scalePath, hp.w_zero]
  vL_zero i := by simp [scalePath, hp.vL_zero i]
  vR_zero j := by simp [scalePath, hp.vR_zero j]
  continuousOn_w := continuousOn_scalePath hc a hp.continuousOn_w
  continuousOn_vL i := continuousOn_scalePath hc a (hp.continuousOn_vL i)
  continuousOn_vR j := continuousOn_scalePath hc a (hp.continuousOn_vR j)
  antitone_vL ht := fun _ _ hij =>
    mul_le_mul_of_nonneg_left (hp.antitone_vL ((coe_lt_div_iff hc).1 ht) hij) ha.le
  vL_le_w ht i := mul_le_mul_of_nonneg_left (hp.vL_le_w ((coe_lt_div_iff hc).1 ht) i) ha.le
  w_le_vR ht j := mul_le_mul_of_nonneg_left (hp.w_le_vR ((coe_lt_div_iff hc).1 ht) j) ha.le
  monotone_vR ht := fun _ _ hij =>
    mul_le_mul_of_nonneg_left (hp.monotone_vR ((coe_lt_div_iff hc).1 ht) hij) ha.le
  integrable_gapL ht i := intervalIntegrable_scale_inv c hc w (vL i)
    (hp.integrable_gapL ((coe_lt_div_iff hc).1 ht) i)
  integrable_gapR ht j := intervalIntegrable_scale_inv c hc w (vR j)
    (hp.integrable_gapR ((coe_lt_div_iff hc).1 ht) j)
  w_eq {t} ht := by
    simp_rw [integral_scale_div c hc ha.ne' hac]
    simp only [scalePath]
    rw [hp.w_eq ((coe_lt_div_iff hc).1 ht), ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  vL_eq {t} ht i := by
    rw [integral_scale_div c hc ha.ne' hac]
    simp only [scalePath]
    rw [hp.vL_eq ((coe_lt_div_iff hc).1 ht) i]
    ring
  vR_eq {t} ht j := by
    rw [integral_scale_div c hc ha.ne' hac]
    simp only [scalePath]
    rw [hp.vR_eq ((coe_lt_div_iff hc).1 ht) j]
    ring
  volume_collisionL i := volume_collision_scale hc ha w (vL i) (hp.volume_collisionL i)
  volume_collisionR j := volume_collision_scale hc ha w (vR j) (hp.volume_collisionR j)
  not_threshold {t} ht := by
    simp only [scalePath]
    rw [thresholdCondition_smul ρL ρR ha.ne']
    exact hp.not_threshold ((coe_lt_div_iff hc).1 ht)

/-! ### Scaling of stopped local dynamics -/

section Dyn

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {nL nR : ℕ} {μ : Measure Ω} {κ : ℝ} {xL ρL : Fin nL → ℝ}
  {xR ρR : Fin nR → ℝ}

/-- **Brownian scaling of local dynamics**: `t ↦ (√c)⁻¹ (W, V, B)(c t)`, the filtration `𝓕(c ·)`, the stop `τ/c`. -/
def _root_.InteractingSLE.Theorem14.GW2JDetR11.LocalDynamics.scale (d : LocalDynamics Ω nL nR) (c : ℝ≥0) :
    LocalDynamics Ω nL nR where
  filtration := scaleFilt d.filtration c
  W := scaleProc c d.W
  VL i := scaleProc c (d.VL i)
  VR j := scaleProc c (d.VR j)
  B := scaleProc c d.B
  stop ω := d.stop ω / c

/-- **Stopped local dynamics are preserved by Brownian scaling** (word `(√c)⁻¹ x`, same weights). -/
theorem _root_.InteractingSLE.Theorem14.GW2JDetR11.LocalDynamics.IsStopped.scale {d : LocalDynamics Ω nL nR}
    {c : ℝ≥0} (hc : c ≠ 0) (h : d.IsStopped μ κ xL ρL xR ρR) :
    (d.scale c).IsStopped μ κ (fun i => (Real.sqrt c)⁻¹ * xL i) ρL (fun j => (Real.sqrt c)⁻¹ * xR j) ρR := by
  obtain ⟨hE, hcont⟩ := h
  refine ⟨⟨isFilteredBrownianReal_scale hc hE.brownian, adaptedBefore_scale hc hE.adapted_W,
    fun i => adaptedBefore_scale hc (hE.adapted_VL i), fun j => adaptedBefore_scale hc (hE.adapted_VR j),
    hE.ae_path.mono fun ω hp => isSLEPathUpTo_scale hc (scaleFactor_pos hc) (scaleFactor_sq_mul hc) hp⟩, ?_⟩
  filter_upwards [hcont] with ξ hξ t ht
  have hct : ((c * t : ℝ≥0) : ℝ≥0∞) = d.stop ξ := by
    change (t : ℝ≥0∞) = d.stop ξ / c at ht
    rw [ENNReal.coe_mul, mul_comm, ht, ENNReal.div_mul_cancel (by exact_mod_cast hc) ENNReal.coe_ne_top]
  have h1 := hξ (c * t) hct
  have hmaps : MapsTo (fun v : ℝ≥0 => c * v) (Iic t) (Iic (c * t)) := fun v hv =>
    mul_le_mul_of_nonneg_left (show v ≤ t from hv) (zero_le (a := c))
  have h2 := h1.comp (continuous_const.mul continuous_id).continuousOn hmaps
  have hlin : Continuous fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) =>
      ((Real.sqrt c)⁻¹ * p.1, fun i => (Real.sqrt c)⁻¹ * p.2.1 i, fun j => (Real.sqrt c)⁻¹ * p.2.2 j) := by
    fun_prop
  exact hlin.comp_continuousOn h2

/-- **Scaled stopped dynamics exist** when stopped dynamics with the original driver and stop exist. -/
theorem exists_isStopped_scale {R : ℝ≥0 → Ω → ℝ} {τ : Ω → ℝ≥0∞} {c : ℝ≥0} (hc : c ≠ 0)
    (h : ∃ d : LocalDynamics Ω nL nR, d.W = R ∧ d.stop = τ ∧ d.IsStopped μ κ xL ρL xR ρR) :
    ∃ d : LocalDynamics Ω nL nR, d.W = scaleProc c R ∧ d.stop = (fun ω => τ ω / c) ∧
      d.IsStopped μ κ (fun i => (Real.sqrt c)⁻¹ * xL i) ρL (fun j => (Real.sqrt c)⁻¹ * xR j) ρR := by
  obtain ⟨d, hW, hs, hd⟩ := h
  refine ⟨d.scale c, ?_, ?_, hd.scale hc⟩
  · change scaleProc c d.W = scaleProc c R
    rw [hW]
  · change (fun ω => d.stop ω / c) = fun ω => τ ω / c
    rw [hs]

/-! ### Reflection of stopped local dynamics -/

/-- A Brownian motion of a filtration stays one after reflection. -/
theorem isFilteredBrownianReal_neg {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
    (hB : IsFilteredBrownianReal 𝓕 B P) : IsFilteredBrownianReal 𝓕 (fun t ω => -B t ω) P := by
  refine ⟨hB.1.neg, fun t => (hB.2.1 t).neg, fun s t hst => ?_⟩
  refine indep_of_indep_of_le_left (hB.2.2 s t hst) ?_
  have e : (fun ω => -B t ω - -B s ω) = (fun x : ℝ => -x) ∘ fun ω => B t ω - B s ω := by
    funext ω
    simp only [Function.comp_apply]
    ring
  rw [e, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono measurable_neg.comap_le

/-- Adaptedness before a time is preserved by reflection. -/
theorem adaptedBefore_neg {𝓕 : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ}
    (hX : AdaptedBefore 𝓕 τ X) : AdaptedBefore 𝓕 τ (fun t ω => -X t ω) := fun t A hA =>
  hX t ((fun x : ℝ => -x) ⁻¹' A) (measurable_neg hA)

/-- **Reflection of local dynamics** `x ↦ −x`, the sides exchanged. -/
def _root_.InteractingSLE.Theorem14.GW2JDetR11.LocalDynamics.reflect (d : LocalDynamics Ω nL nR) :
    LocalDynamics Ω nR nL where
  filtration := d.filtration
  W t ω := -d.W t ω
  VL j t ω := -d.VR j t ω
  VR i t ω := -d.VL i t ω
  B t ω := -d.B t ω
  stop := d.stop

/-- **Stopped local dynamics are preserved by reflection** (word `(−x^R, ρ^R; −x^L, ρ^L)`). -/
theorem _root_.InteractingSLE.Theorem14.GW2JDetR11.LocalDynamics.IsStopped.reflect {d : LocalDynamics Ω nL nR}
    (h : d.IsStopped μ κ xL ρL xR ρR) : d.reflect.IsStopped μ κ (-xR) ρR (-xL) ρL := by
  obtain ⟨hE, hcont⟩ := h
  refine ⟨⟨isFilteredBrownianReal_neg hE.brownian, adaptedBefore_neg hE.adapted_W,
    fun j => adaptedBefore_neg (hE.adapted_VR j), fun i => adaptedBefore_neg (hE.adapted_VL i),
    hE.ae_path.mono fun ω hp => hp.reflect⟩, ?_⟩
  filter_upwards [hcont] with ξ hξ t ht
  have hlin : Continuous fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) =>
      (-p.1, fun j => -p.2.2 j, fun i => -p.2.1 i) := by
    fun_prop
  exact hlin.comp_continuousOn (hξ t ht)

/-- **Reflected stopped dynamics exist** when stopped dynamics with the original driver and stop exist. -/
theorem exists_isStopped_reflect {R : ℝ≥0 → Ω → ℝ} {τ : Ω → ℝ≥0∞}
    (h : ∃ d : LocalDynamics Ω nL nR, d.W = R ∧ d.stop = τ ∧ d.IsStopped μ κ xL ρL xR ρR) :
    ∃ d : LocalDynamics Ω nR nL, d.W = (fun t ω => -R t ω) ∧ d.stop = τ ∧
      d.IsStopped μ κ (-xR) ρR (-xL) ρL := by
  obtain ⟨d, hW, hs, hd⟩ := h
  refine ⟨d.reflect, ?_, hs, hd.reflect⟩
  change (fun t ω => -d.W t ω) = _
  rw [hW]

end Dyn

end InteractingSLE.Theorem14.GW2Sdf
