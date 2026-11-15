/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59PiecesImage
import InteractingSLE.Spec.ZhanGT4.CrosscutA3Scale
import InteractingSLE.Spec.Sec7.Lemma71Capacity
import InteractingSLE.Spec.Sec6.DrivingCriterion
import InteractingSLE.Spec.ZhanGT4.MixtureA33ChordalScale

/-!
# Loewner scaling of killed arcs and of the real flow

Packet PROVE-STAGED-REP2. PROVE-PROP59-PIECES' root candidates are the killed chains of the joint-chart image
**dilated** by `λ > 0`. The killed driver, terminal capacity and mark images of `λγ` are the Brownian-scaled ones of
`γ` (deterministic Loewner scaling):

* real flow: `isPosSol_scale`, `alive_scale_iff`, `cflow_scale`, `gImg_scale`, `imgSet_scale`, **`rightImg_scale`**
  (`rightImg (λ w(·/λ²)) (λx) (λ² t) = λ rightImg w x t`);
* killed arcs: `capClock_smul` (`σ_{λγ} = λ² σ_γ`, by the hull identity of the scaled driver and the capacity of
  Loewner hulls), `lt_kLife_smul_iff`, `chainDrv_smul` (uniqueness of drivers with equal hulls), **`kW_smul`**,
  **`kPath_smul`**, **`kVR_smul`**, **`kVL_smul`**.

R48: nothing here uses Theorem 1.2/1.3 or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal Pointwise

namespace InteractingSLE.Sec5.CrossCond.StagedRepLater

open MartChar MartChar.RealFlow

/-! ### Scaling of the real Loewner flow -/

section Real

/-- The scaled driver `s ↦ c w(s/c²)`. -/
def scD (c : ℝ) (w : ℝ → ℝ) : ℝ → ℝ := fun s => c * w (s / c ^ 2)

variable {w : ℝ → ℝ} {c : ℝ}

theorem scD_scD_inv (hc : 0 < c) (w : ℝ → ℝ) : scD c⁻¹ (scD c w) = w := by
  funext s
  simp only [scD]
  have hc0 : c ≠ 0 := hc.ne'
  have e : s / c⁻¹ ^ 2 / c ^ 2 = s := by field_simp
  rw [e, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]

theorem continuous_scD (hw : Continuous w) (c : ℝ) : Continuous (scD c w) :=
  continuous_const.mul (hw.comp (continuous_id.div_const _))

/-- **Scaling of positive solutions of the real Loewner flow.** -/
theorem isPosSol_scale (hc : 0 < c) {y t : ℝ} {X : ℝ → ℝ} (hX : IsPosSol w y t X) :
    IsPosSol (scD c w) (c * y) (c ^ 2 * t) (fun s => c * X (s / c ^ 2)) := by
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  have hmaps : MapsTo (fun s : ℝ => s / c ^ 2) (Icc 0 (c ^ 2 * t)) (Icc 0 t) := fun s hs =>
    ⟨div_nonneg hs.1 hc2.le, (div_le_iff₀ hc2).2 (by linarith [hs.2])⟩
  refine ⟨continuousOn_const.mul (hX.1.comp (continuous_id.div_const _).continuousOn hmaps), fun s hs => ?_⟩
  obtain ⟨hpos, heq⟩ := hX.2 (s / c ^ 2) (hmaps hs)
  refine ⟨mul_pos hc hpos, ?_⟩
  have hint : ∫ r in (0 : ℝ)..s, 2 / (c * X (r / c ^ 2)) =
      c * ∫ r in (0 : ℝ)..s / c ^ 2, 2 / X r := by
    have h1 := intervalIntegral.integral_comp_div (a := 0) (b := s) (fun v => 2 / (c * X v)) hc2.ne'
    rw [h1, zero_div, smul_eq_mul]
    have h2 : (fun v => 2 / (c * X v)) = fun v => c⁻¹ * (2 / X v) := by
      funext v; field_simp
    rw [h2, intervalIntegral.integral_const_mul]
    field_simp
  rw [hint]
  show c * X (s / c ^ 2) = _
  rw [heq, scD]
  ring

theorem alive_scale (hc : 0 < c) {y t : ℝ} (h : Alive w y t) : Alive (scD c w) (c * y) (c ^ 2 * t) :=
  ⟨_, isPosSol_scale hc h.choose_spec⟩

theorem alive_scale_iff (hc : 0 < c) {y t : ℝ} : Alive (scD c w) (c * y) (c ^ 2 * t) ↔ Alive w y t := by
  refine ⟨fun h => ?_, alive_scale hc⟩
  have h' := alive_scale (inv_pos.2 hc) h
  rw [scD_scD_inv hc, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul, ← mul_assoc, ← mul_pow,
    inv_mul_cancel₀ hc.ne', one_pow, one_mul] at h'
  exact h'

theorem cflow_scale (hw : Continuous w) (hc : 0 < c) {y t : ℝ} (ht : 0 ≤ t) :
    cflow (scD c w) (c * y) (c ^ 2 * t) = c * cflow w y t := by
  classical
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  by_cases h : Alive w y t
  · have hX := isPosSol_scale hc (h.isPosSol hw)
    rw [cflow_eq_of_isPosSol (continuous_scD hw c) hX ⟨mul_nonneg hc2.le ht, le_rfl⟩]
    simp only [mul_div_cancel_left₀ t hc2.ne']
  · have h' : ¬ Alive (scD c w) (c * y) (c ^ 2 * t) := fun h'' => h ((alive_scale_iff hc).1 h'')
    simp only [cflow, h, h', ↓reduceDIte, mul_zero]

theorem gImg_scale (hw : Continuous w) (hc : 0 < c) {y t : ℝ} (ht : 0 ≤ t) :
    gImg (scD c w) (c * y) (c ^ 2 * t) = c * gImg w y t := by
  rw [gImg, gImg, cflow_scale hw hc ht, scD, mul_div_cancel_left₀ t (pow_pos hc 2).ne']
  ring

theorem imgSet_scale (hw : Continuous w) (hc : 0 < c) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    imgSet (scD c w) (c * x) (c ^ 2 * t) = c • imgSet w x t := by
  ext g
  simp only [imgSet, mem_ofPred_eq, Set.mem_smul_set, smul_eq_mul]
  constructor
  · rintro ⟨y', hxy, hal, rfl⟩
    have hy' : y' = c * (y' / c) := by field_simp
    rw [hy'] at hal ⊢
    refine ⟨gImg w (y' / c) t, ⟨y' / c, ?_, (alive_scale_iff hc).1 hal, rfl⟩, (gImg_scale hw hc ht).symm⟩
    rw [lt_div_iff₀ hc, mul_comm]
    exact hxy
  · rintro ⟨g', ⟨y, hxy, hal, rfl⟩, rfl⟩
    exact ⟨c * y, mul_lt_mul_of_pos_left hxy hc, (alive_scale_iff hc).2 hal, gImg_scale hw hc ht⟩

/-- **Scaling of the right image of a real point.** -/
theorem rightImg_scale (hw : Continuous w) (hc : 0 < c) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    rightImg (scD c w) (c * x) (c ^ 2 * t) = c * rightImg w x t := by
  rw [rightImg, imgSet_scale hw hc x ht, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul, rightImg]

end Real

/-! ### Scaling of killed arcs -/

section Arc

open WangWu WangWu.ImgWord
open Sec7.Lemma71C (capClock)

variable {γ : ℝ → ℂ} {P : Set ℝ} {c : ℝ}

/-- The time factor `c⁻²` of a dilation by `c`. -/
def tf (c : ℝ) : ℝ≥0 := (c⁻¹ ^ 2).toNNReal

theorem coe_tf_mul (hc : 0 < c) (t : ℝ≥0) : ((tf c * t : ℝ≥0) : ℝ) = t / c ^ 2 := by
  rw [NNReal.coe_mul, tf, Real.coe_toNNReal _ (by positivity), inv_pow, inv_mul_eq_div]

theorem tf_ne_zero (hc : 0 < c) : tf c ≠ 0 := by
  rw [tf, Ne, Real.toNNReal_eq_zero, not_le]; positivity

theorem sqrt_tf_inv (hc : 0 < c) : (√(tf c : ℝ))⁻¹ = c := by
  rw [tf, Real.coe_toNNReal _ (by positivity), Real.sqrt_sq (inv_pos.2 hc).le, inv_inv]

/-- **The hull of a scaled driver** is the dilated hull. -/
theorem fwdHull_scD {W : ℝ → ℝ} (hc : 0 < c) {σ : ℝ} (hσ : 0 ≤ σ) :
    fwdHull (scD c W) (c ^ 2 * σ) = (fun z => (c : ℂ) * z) '' fwdHull W σ := by
  rw [ZhanGT4.A34.fwdHull_eq_image_of_scale hc hσ]
  have e : (fun s => scD c W (c ^ 2 * s) / c) = W := by
    funext s
    simp only [scD]
    rw [mul_div_cancel_left₀ s (pow_pos hc 2).ne', mul_div_cancel_left₀ _ hc.ne']
  rw [e]
  rfl

/-- **The capacity clock of a dilated killed arc.** -/
theorem capClock_smul (hγ : IsKilledArc γ P) (hc : 0 < c) {u : ℝ} (hu : u ∈ P) :
    capClock (fun v => (c : ℂ) * γ v) u = c ^ 2 * capClock γ u := by
  obtain ⟨S, hS, huS⟩ := hγ.exists_gt u hu
  have hS0 : 0 < S := lt_of_le_of_lt (hγ.nonneg u hu) huS
  obtain ⟨W, hW, hW0, -, -, -, hK⟩ := hγ.exists_localDriver hS hS0
  obtain ⟨hσ0, hK'⟩ := hK u ⟨hγ.nonneg u hu, huS.le⟩
  have hγ' := Prop59Pieces.isKilledArc_smul hγ hc
  have h1 : fwdHull (scD c W) (c ^ 2 * capClock γ u) = fillH ((fun v => (c : ℂ) * γ v) '' Icc 0 u) := by
    rw [fwdHull_scD hc hσ0, hK', hγ'.fillH_eq hu, image_image]
  have h2 := Sec7.Lemma71.hcapSet_eq_of_fwdHull_eq (continuous_scD hW c) (by simp [scD, hW0])
    (mul_nonneg (sq_nonneg c) hσ0) h1
  simp only [capClock, h2]
  ring

theorem lt_kLife_smul_iff (hγ : IsKilledArc γ P) (hc : 0 < c) {t : ℝ≥0} :
    (t : WithTop ℝ≥0) < kLife (fun v => (c : ℂ) * γ v) P ↔ ((tf c * t : ℝ≥0) : WithTop ℝ≥0) < kLife γ P := by
  rw [lt_kLife_iff, lt_kLife_iff]
  refine exists_congr fun S => and_congr_right fun hS => ?_
  rw [capClock_smul hγ hc hS, coe_tf_mul hc, div_lt_iff₀ (pow_pos hc 2), mul_comm]

/-- **The local drivers of a dilated killed arc** are the scaled local drivers. -/
theorem locDrv_smul (hγ : IsKilledArc γ P) (hc : 0 < c) {S : ℝ} (hS : S ∈ P) (hS0 : 0 < S) :
    EqOn (locDrv (fun v => (c : ℂ) * γ v) S) (scD c (locDrv γ S))
      (Icc 0 (capClock (fun v => (c : ℂ) * γ v) S)) := by
  have hγ' := Prop59Pieces.isKilledArc_smul hγ hc
  obtain ⟨hc₁, h0₁, hK₁⟩ := hγ'.locDrv_spec hS hS0
  obtain ⟨hc₂, h0₂, hK₂⟩ := hγ.locDrv_spec hS hS0
  obtain ⟨-, -, -, -, -, hcc, -⟩ := hγ'.exists_localDriver hS hS0
  refine Sec6.eqOn_of_fwdHull_eq hc₁ (continuous_scD hc₂ c) h0₁ (by simp [scD, h0₂])
    (hγ'.capClock_nonneg hS) fun r hr => ?_
  obtain ⟨u, hu, rfl⟩ := intermediate_value_Icc hS0.le hcc (by rw [hγ'.capClock_zero]; exact hr)
  have huP : u ∈ P := hγ.icc S hS hu
  rw [hK₁ u hu, capClock_smul hγ hc huP, fwdHull_scD hc (hγ.capClock_nonneg huP), hK₂ u hu, image_image]

/-- **The glued driver of a dilated killed arc.** -/
theorem chainDrv_smul (hγ : IsKilledArc γ P) (hc : 0 < c) {S : ℝ} (hS : S ∈ P) (hS0 : 0 < S) {r : ℝ}
    (hr : r ∈ Icc 0 (capClock (fun v => (c : ℂ) * γ v) S)) :
    chainDrv (fun v => (c : ℂ) * γ v) P r = c * chainDrv γ P (r / c ^ 2) := by
  have hγ' := Prop59Pieces.isKilledArc_smul hγ hc
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  have hr' : r / c ^ 2 ∈ Icc 0 (capClock γ S) := by
    refine ⟨div_nonneg hr.1 hc2.le, (div_le_iff₀ hc2).2 ?_⟩
    have := hr.2
    rw [capClock_smul hγ hc hS] at this
    linarith
  rw [hγ'.chainDrv_eq hS hS0 hr, locDrv_smul hγ hc hS hS0 hr, scD, hγ.chainDrv_eq hS hS0 hr']

/-- **The killed driver of a dilated killed arc**: `kW (cγ) t = c · kW γ (t / c²)`. -/
theorem kW_smul (hγ : IsKilledArc γ P) (hc : 0 < c) (t : ℝ≥0) :
    kW (fun v => (c : ℂ) * γ v) P t = c * kW γ P (tf c * t) := by
  by_cases ht : (t : WithTop ℝ≥0) < kLife (fun v => (c : ℂ) * γ v) P
  · rw [kW_of_lt ht, kW_of_lt ((lt_kLife_smul_iff hγ hc).1 ht)]
    obtain ⟨S, hS, hlt⟩ := lt_kLife_iff.1 ht
    have hS0 : 0 < S := by
      by_contra hn
      have hS0' : S = 0 := le_antisymm (not_lt.1 hn) (hγ.nonneg S hS)
      rw [hS0', (Prop59Pieces.isKilledArc_smul hγ hc).capClock_zero] at hlt
      exact absurd hlt (not_lt.2 t.coe_nonneg)
    rw [chainDrv_smul hγ hc hS hS0 ⟨t.coe_nonneg, hlt.le⟩, coe_tf_mul hc]
  · have ht' : ¬ ((tf c * t : ℝ≥0) : WithTop ℝ≥0) < kLife γ P := fun h => ht ((lt_kLife_smul_iff hγ hc).2 h)
    simp only [kW, ht, ht', ↓reduceIte, mul_zero]

/-- **The killed driver path of a dilated killed arc** is the scaled path. -/
theorem kPath_smul (hγ : IsKilledArc γ P) (hc : 0 < c) :
    kPath (fun v => (c : ℂ) * γ v) P = scD c (kPath γ P) := by
  funext r
  simp only [kPath, scD]
  rw [kW_smul hγ hc]
  congr 2
  apply NNReal.coe_injective
  rw [coe_tf_mul hc, Real.coe_toNNReal', Real.coe_toNNReal']
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  rcases le_total r 0 with h | h
  · rw [max_eq_right h, max_eq_right (div_nonpos_of_nonpos_of_nonneg h hc2.le), zero_div]
  · rw [max_eq_left h, max_eq_left (div_nonneg h hc2.le)]

/-- The right image of a scaled driver that agrees on `[0, u]` with a continuous driver. -/
theorem rightImg_scD_of_eqOn {f g : ℝ → ℝ} (hg : Continuous g) (hc : 0 < c) {u : ℝ} (hu : 0 ≤ u)
    (hfg : EqOn f g (Icc 0 u)) (x : ℝ) : rightImg (scD c f) (c * x) (c ^ 2 * u) = c * rightImg f x u := by
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  have h1 : EqOn (scD c f) (scD c g) (Icc 0 (c ^ 2 * u)) := fun r hr => by
    simp only [scD]
    rw [hfg ⟨div_nonneg hr.1 hc2.le, (div_le_iff₀ hc2).2 (by linarith [hr.2])⟩]
  rw [Sec7.Lemma71B.rightImg_congr (continuous_scD hg c) (mul_nonneg hc2.le hu) h1, rightImg_scale hg hc x hu,
    Sec7.Lemma71B.rightImg_congr hg hu hfg]

/-- On `[0, u]`, `u < σ(S)`, the killed driver path is the local driver of `S`. -/
theorem kPath_eqOn_locDrv (hγ : IsKilledArc γ P) {S : ℝ} (hS : S ∈ P) (hS0 : 0 < S) {u : ℝ}
    (hu : u < capClock γ S) : EqOn (kPath γ P) (locDrv γ S) (Icc 0 u) := by
  intro v hv
  have hvt : ((v.toNNReal : ℝ≥0) : WithTop ℝ≥0) < kLife γ P :=
    lt_kLife_iff.2 ⟨S, hS, by rw [Real.coe_toNNReal _ hv.1]; exact lt_of_le_of_lt hv.2 hu⟩
  simp only [kPath]
  rw [kW_of_lt hvt, Real.coe_toNNReal _ hv.1, hγ.chainDrv_eq hS hS0 ⟨hv.1, (hv.2.trans hu.le)⟩]

/-- **The right mark images of a dilated killed arc.** -/
theorem kVR_smul (hγ : IsKilledArc γ P) (hc : 0 < c) {n : ℕ} (xR : Fin n → ℝ) (j : Fin n) (t : ℝ≥0) :
    kVR (fun v => (c : ℂ) * γ v) P (fun j => c * xR j) j t = c * kVR γ P xR j (tf c * t) := by
  by_cases ht : (t : WithTop ℝ≥0) < kLife (fun v => (c : ℂ) * γ v) P
  · have ht' := (lt_kLife_smul_iff hγ hc).1 ht
    rw [kVR_of_lt _ _ ht, kVR_of_lt _ _ ht']
    obtain ⟨S, hS, hlt⟩ := lt_kLife_iff.1 ht'
    have hS0 : 0 < S := by
      by_contra hn
      have hS0' : S = 0 := le_antisymm (not_lt.1 hn) (hγ.nonneg S hS)
      rw [hS0', hγ.capClock_zero] at hlt
      exact absurd hlt (not_lt.2 (NNReal.coe_nonneg _))
    have hu : (0 : ℝ) ≤ ((tf c * t : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    have e : ((t : ℝ≥0) : ℝ) = c ^ 2 * ((tf c * t : ℝ≥0) : ℝ) := by
      rw [coe_tf_mul hc]; field_simp
    simp only [kVRr, kImg]
    rw [kPath_smul hγ hc, e, rightImg_scD_of_eqOn (hγ.locDrv_spec hS hS0).1 hc hu
      (kPath_eqOn_locDrv hγ hS hS0 hlt)]
  · have ht' : ¬ ((tf c * t : ℝ≥0) : WithTop ℝ≥0) < kLife γ P := fun h => ht ((lt_kLife_smul_iff hγ hc).2 h)
    simp only [kVR, ht, ht', ↓reduceIte, mul_zero]

/-- **The left mark images of a dilated killed arc.** -/
theorem kVL_smul (hγ : IsKilledArc γ P) (hc : 0 < c) {n : ℕ} (xL : Fin n → ℝ) (i : Fin n) (t : ℝ≥0) :
    kVL (fun v => (c : ℂ) * γ v) P (fun i => c * xL i) i t = c * kVL γ P xL i (tf c * t) := by
  by_cases ht : (t : WithTop ℝ≥0) < kLife (fun v => (c : ℂ) * γ v) P
  · have ht' := (lt_kLife_smul_iff hγ hc).1 ht
    rw [kVL_of_lt _ _ ht, kVL_of_lt _ _ ht']
    obtain ⟨S, hS, hlt⟩ := lt_kLife_iff.1 ht'
    have hS0 : 0 < S := by
      by_contra hn
      have hS0' : S = 0 := le_antisymm (not_lt.1 hn) (hγ.nonneg S hS)
      rw [hS0', hγ.capClock_zero] at hlt
      exact absurd hlt (not_lt.2 (NNReal.coe_nonneg _))
    have hu : (0 : ℝ) ≤ ((tf c * t : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    have e : ((t : ℝ≥0) : ℝ) = c ^ 2 * ((tf c * t : ℝ≥0) : ℝ) := by
      rw [coe_tf_mul hc]; field_simp
    have hneg : (fun r => -kPath (fun v => (c : ℂ) * γ v) P r) = scD c fun r => -kPath γ P r := by
      rw [kPath_smul hγ hc]; funext r; simp only [scD]; ring
    have hfg : EqOn (fun r => -kPath γ P r) (fun r => -locDrv γ S r) (Icc 0 ((tf c * t : ℝ≥0) : ℝ)) :=
      fun v hv => by simp only [kPath_eqOn_locDrv hγ hS hS0 hlt hv]
    have hx : -(c * xL i) = c * -xL i := by ring
    simp only [kVLr, kImg]
    rw [hneg, e, hx, rightImg_scD_of_eqOn (hγ.locDrv_spec hS hS0).1.neg hc hu hfg]
    ring
  · have ht' : ¬ ((tf c * t : ℝ≥0) : WithTop ℝ≥0) < kLife γ P := fun h => ht ((lt_kLife_smul_iff hγ hc).2 h)
    simp only [kVL, ht, ht', ↓reduceIte, mul_zero]

/-- **The terminal capacity of a dilated killed arc**: `kLife (cγ) = kLife γ / c⁻²`. -/
theorem kLife_smul (hγ : IsKilledArc γ P) (hc : 0 < c) :
    (show ℝ≥0∞ from kLife (fun v => (c : ℂ) * γ v) P) = (show ℝ≥0∞ from kLife γ P) / (tf c : ℝ≥0∞) := by
  have key : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (show ℝ≥0∞ from kLife (fun v => (c : ℂ) * γ v) P) ↔
      (t : ℝ≥0∞) < (show ℝ≥0∞ from kLife γ P) / (tf c : ℝ≥0∞) := fun t => by
    rw [ZhanGT4.UpMark.coe_lt_div_iff (tf_ne_zero hc)]
    exact lt_kLife_smul_iff hγ hc
  refine le_antisymm (le_of_forall_lt fun x hx => ?_) (le_of_forall_lt fun x hx => ?_)
  · obtain ⟨t, hxt, htk⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hx
    exact lt_trans hxt ((key t).1 htk)
  · obtain ⟨t, hxt, htk⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hx
    exact lt_trans hxt ((key t).2 htk)

end Arc

end InteractingSLE.Sec5.CrossCond.StagedRepLater
