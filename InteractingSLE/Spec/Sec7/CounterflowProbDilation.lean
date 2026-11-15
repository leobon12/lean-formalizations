/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LPTrace
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution
import QuantumZipper.Proofs.Loewner.Algebra

/-!
# §7.4, Aux. lemma 126: dilation of integrated evolutions and of their traces

Packet PROVE-SEC7-D2. Specification §7.4.1, Aux. lemma 126 (`source/spec/p385-432.md` L251–L316, pp. 399–402),
"Finite-time continuity by dilation of the driving law": "For any `a > 0` its dilation
`W^{(a)}_t = a W_{t/a²}`, `V^{(a),q}_t = a V^q_{t/a²}` has the same canonical two-seed driving law."

This file proves the pathwise form of that dilation for **every** integrated evolution (any force word), on the same
probability space: with `c > 0` and `s = c^{-1/2}` (Mathlib's Brownian scaling convention
`ProbabilityTheory.IsBrownianReal.smul`, `t ↦ (√c)⁻¹ B(ct)`; the source's `a` is `(√c)⁻¹`),

* `IsIntegratedSLEPath.dilate`: the dilated path `t ↦ s w(ct)` (and force coordinates, Brownian path) with lifetime
  `ζ / c` satisfies every pathwise condition of Definition 2.1 for the force word with positions `s x`;
* `IsIntegratedSLEEvolution.dilate`: the dilated processes are an integrated evolution for the time-changed
  filtration `t ↦ 𝓕_{ct}` (`dilFiltration`);
* `IsGeneratingTrace.dilate`: if `η` generates the Loewner chain of `w` on `[0, T]`, then `t ↦ s η(ct)` generates the
  chain of the dilated driver on `[0, T/c]` (QuantumZipper's hull scaling `mem_fwdHull_scale_iff`).

The source applies dilation through equality of laws; on the same space the dilated processes are themselves an
evolution, so no measurability of a trace event is needed for this step.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace Dilation

/-! ### Dilated paths, processes, lifetimes and filtrations -/

/-- The dilation `t ↦ (√c)⁻¹ w(ct)` of a real path. -/
def dilPath (c : ℝ≥0) (w : ℝ≥0 → ℝ) : ℝ≥0 → ℝ := fun t => (√(c : ℝ))⁻¹ * w (c * t)

/-- The dilation `t ↦ (√c)⁻¹ X_{ct}` of a real process. -/
def dilProc {Ω : Type*} (c : ℝ≥0) (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => (√(c : ℝ))⁻¹ * X (c * t) ω

/-- The time-changed filtration `t ↦ 𝓕_{ct}`. -/
def dilFiltration {Ω : Type*} {mΩ : MeasurableSpace Ω} (c : ℝ≥0) (𝓕 : Filtration ℝ≥0 mΩ) :
    Filtration ℝ≥0 mΩ where
  seq t := 𝓕 (c * t)
  mono' _ _ h := 𝓕.mono (mul_le_mul_of_nonneg_left h c.2)
  le' _ := 𝓕.le _

theorem dilProc_apply {Ω : Type*} (c : ℝ≥0) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    dilProc c X t ω = dilPath c (fun s => X s ω) t := rfl

variable {c : ℝ≥0}

theorem sqrt_pos_of_ne (hc : c ≠ 0) : 0 < √(c : ℝ) :=
  Real.sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc))

theorem sqrt_ne_zero_of_ne (hc : c ≠ 0) : √(c : ℝ) ≠ 0 := (sqrt_pos_of_ne hc).ne'

theorem inv_sqrt_ne_zero (hc : c ≠ 0) : (√(c : ℝ))⁻¹ ≠ 0 := inv_ne_zero (sqrt_ne_zero_of_ne hc)

/-- `t < ζ / c ↔ ct < ζ`. -/
theorem coe_lt_div_iff (hc : c ≠ 0) {t : ℝ≥0} {ζ : ℝ≥0∞} :
    (t : ℝ≥0∞) < ζ / c ↔ ((c * t : ℝ≥0) : ℝ≥0∞) < ζ := by
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl (ENNReal.coe_ne_zero.2 hc)) (Or.inl ENNReal.coe_ne_top),
    ENNReal.coe_mul, mul_comm]

/-- `c * t.toNNReal = (ct).toNNReal` for real `t`. -/
theorem mul_toNNReal (c : ℝ≥0) (u : ℝ) : c * u.toNNReal = ((c : ℝ) * u).toNNReal := by
  rw [Real.toNNReal_mul (NNReal.coe_nonneg c), Real.toNNReal_coe]

/-- The dilated path read through `toNNReal`. -/
theorem dilPath_toNNReal (c : ℝ≥0) (w : ℝ≥0 → ℝ) (u : ℝ) :
    dilPath c w u.toNNReal = (√(c : ℝ))⁻¹ * w ((c : ℝ) * u).toNNReal := by
  rw [dilPath, mul_toNNReal]

/-! ### The threshold condition is invariant under scaling -/

theorem thresholdCondition_mul_iff {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {s : ℝ}
    (hs : s ≠ 0) (w : ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) :
    ForceWord.ThresholdCondition ρL ρR (s * w) (fun i => s * vL i) (fun i => s * vR i) ↔
      ForceWord.ThresholdCondition ρL ρR w vL vR := by
  simp only [ForceWord.ThresholdCondition, mul_right_inj' hs]

/-! ### Change of variables in the integrated equations -/

/-- `∫₀ᵗ √c F(cu) du = (√c)⁻¹ ∫₀^{ct} F`. -/
theorem integral_sqrt_mul_comp (hc : c ≠ 0) (F : ℝ → ℝ) (t : ℝ) :
    ∫ u in (0 : ℝ)..t, √(c : ℝ) * F ((c : ℝ) * u) =
      (√(c : ℝ))⁻¹ * ∫ x in (0 : ℝ)..((c : ℝ) * t), F x := by
  have hc' : (c : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hc
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left F hc', mul_zero,
    smul_eq_mul, ← mul_assoc]
  congr 1
  have hs := sqrt_ne_zero_of_ne hc
  field_simp
  exact Real.sq_sqrt (NNReal.coe_nonneg c)

/-- The dilated reciprocal-gap integrand. -/
theorem div_dil_sub (hc : c ≠ 0) (ρ x y : ℝ) :
    ρ / ((√(c : ℝ))⁻¹ * x - (√(c : ℝ))⁻¹ * y) = √(c : ℝ) * (ρ / (x - y)) := by
  have hs := sqrt_ne_zero_of_ne hc
  rw [← mul_sub]
  by_cases hxy : x - y = 0
  · simp [hxy]
  field_simp

theorem inv_dil_sub (hc : c ≠ 0) (x y : ℝ) :
    ((√(c : ℝ))⁻¹ * x - (√(c : ℝ))⁻¹ * y)⁻¹ = √(c : ℝ) * (x - y)⁻¹ := by
  have h := div_dil_sub hc 1 x y
  simpa [one_div] using h

/-- Interval integrability is preserved by the dilation of the time variable. -/
theorem intervalIntegrable_comp_mul (hc : c ≠ 0) {F : ℝ → ℝ} {t : ℝ}
    (hF : IntervalIntegrable F volume 0 ((c : ℝ) * t)) :
    IntervalIntegrable (fun u => √(c : ℝ) * F ((c : ℝ) * u)) volume 0 t := by
  have hc' : (c : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hc
  have h := hF.comp_mul_left (c := (c : ℝ))
  rw [zero_div, mul_div_cancel_left₀ _ hc'] at h
  exact h.const_mul _

/-! ### The pathwise conditions of Definition 2.1 under dilation -/

theorem continuousOn_dilPath (hc : c ≠ 0) {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) :
    ContinuousOn (dilPath c w) {t | (t : ℝ≥0∞) < ζ / c} := by
  have h : ContinuousOn (fun t : ℝ≥0 => w (c * t)) {t | (t : ℝ≥0∞) < ζ / c} :=
    hw.comp (continuous_const.mul continuous_id).continuousOn fun t ht => (coe_lt_div_iff hc).1 ht
  exact continuousOn_const.mul h

/-- `t ↦ c⁻¹ t` maps left neighbourhoods of `cT` to left neighbourhoods of `T`. -/
theorem tendsto_inv_mul_nhdsLT (hc : c ≠ 0) (T : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => c⁻¹ * t) (𝓝[<] (c * T)) (𝓝[<] T) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t ht => ?_⟩
  · have hcont : Continuous fun t : ℝ≥0 => c⁻¹ * t := continuous_const.mul continuous_id
    have h := (hcont.tendsto (c * T)).mono_left (nhdsWithin_le_nhds (s := Iio (c * T)))
    rwa [inv_mul_cancel_left₀ hc] at h
  · have hc0 : (0 : ℝ≥0) < c := pos_iff_ne_zero.2 hc
    show c⁻¹ * t < T
    rw [inv_mul_lt_iff₀ hc0]
    exact ht

/-- **Dilation of the pathwise conditions** (Aux. lemma 126, p. 401, "its dilation `W^{(a)}_t = a W_{t/a²}`,
`V^{(a),q}_t = a V^q_{t/a²}`", with `a = (√c)⁻¹`): the dilated driver, force coordinates and Brownian path, with
lifetime `ζ / c`, satisfy Definition 2.1 for the dilated positions. -/
theorem _root_.InteractingSLE.IsIntegratedSLEPath.dilate {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hc : c ≠ 0)
    (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) :
    IsIntegratedSLEPath a (fun i => (√(c : ℝ))⁻¹ * xL i) (fun i => (√(c : ℝ))⁻¹ * xR i) ρL ρR
      (dilPath c w) (fun i => dilPath c (vL i)) (fun i => dilPath c (vR i)) (dilPath c b) (ζ / c) := by
  obtain ⟨hw0, hvL0, hvR0, hcw, hcvL, hcvR, hantiL, hLw, hwR, hmonoR, hintL, hintR, hweq, hvLeq,
    hvReq, hcolL, hcolR, hnt, hthr0, hthrT⟩ := h
  have hs : 0 < (√(c : ℝ))⁻¹ := inv_pos.2 (sqrt_pos_of_ne hc)
  have hc' : (c : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hc
  have hlt : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ / c → ((c * t : ℝ≥0) : ℝ≥0∞) < ζ :=
    fun ht => (coe_lt_div_iff hc).1 ht
  -- the reciprocal-gap integrals
  have hint : ∀ (ρ : ℝ) (x y : ℝ≥0 → ℝ) (t : ℝ≥0),
      ∫ u in (0 : ℝ)..t, ρ / (dilPath c x u.toNNReal - dilPath c y u.toNNReal) =
        (√(c : ℝ))⁻¹ * ∫ u in (0 : ℝ)..((c * t : ℝ≥0) : ℝ), ρ / (x u.toNNReal - y u.toNNReal) := by
    intro ρ x y t
    simp_rw [dilPath_toNNReal, div_dil_sub hc]
    rw [NNReal.coe_mul]
    exact integral_sqrt_mul_comp hc (fun u => ρ / (x u.toNNReal - y u.toNNReal)) t
  have hii : ∀ (x y : ℝ≥0 → ℝ) (t : ℝ≥0),
      IntervalIntegrable (fun u : ℝ => (x u.toNNReal - y u.toNNReal)⁻¹) volume 0 ((c * t : ℝ≥0) : ℝ) →
      IntervalIntegrable (fun u : ℝ => (dilPath c x u.toNNReal - dilPath c y u.toNNReal)⁻¹) volume 0 t := by
    intro x y t hxy
    simp_rw [dilPath_toNNReal, inv_dil_sub hc]
    rw [NNReal.coe_mul] at hxy
    exact intervalIntegrable_comp_mul hc (F := fun u => (x u.toNNReal - y u.toNNReal)⁻¹) hxy
  -- the collision sets
  have hcol : ∀ (x y : ℝ≥0 → ℝ),
      volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ x s.toNNReal = y s.toNNReal} = 0 →
      volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ / c ∧
        dilPath c x s.toNNReal = dilPath c y s.toNNReal} = 0 := by
    intro x y hxy
    have hset : {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ / c ∧
        dilPath c x s.toNNReal = dilPath c y s.toNNReal} =
        (fun u => (c : ℝ) * u) ⁻¹' {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ x s.toNNReal = y s.toNNReal} := by
      ext u
      simp only [mem_ofPred_eq, mem_preimage, coe_lt_div_iff hc, mul_toNNReal, dilPath_toNNReal,
        mul_right_inj' (inv_sqrt_ne_zero hc)]
      have hcpos : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
      rw [mul_nonneg_iff_of_pos_left hcpos]
    rw [hset, Real.volume_preimage_mul_left hc', hxy, mul_zero]
  refine ⟨by simp [dilPath, hw0], fun i => by simp [dilPath, hvL0 i], fun i => by simp [dilPath, hvR0 i],
    continuousOn_dilPath hc hcw, fun i => continuousOn_dilPath hc (hcvL i),
    fun i => continuousOn_dilPath hc (hcvR i),
    fun t ht i j hij => mul_le_mul_of_nonneg_left (hantiL _ (hlt ht) hij) hs.le,
    fun t ht i => mul_le_mul_of_nonneg_left (hLw _ (hlt ht) i) hs.le,
    fun t ht i => mul_le_mul_of_nonneg_left (hwR _ (hlt ht) i) hs.le,
    fun t ht i j hij => mul_le_mul_of_nonneg_left (hmonoR _ (hlt ht) hij) hs.le,
    fun t ht i => hii w (vL i) t (hintL _ (hlt ht) i), fun t ht i => hii w (vR i) t (hintR _ (hlt ht) i),
    fun t ht => ?_, fun t ht i => ?_, fun t ht i => ?_, fun i => hcol w (vL i) (hcolL i),
    fun i => hcol w (vR i) (hcolR i), fun t ht => ?_, fun hζ => ?_, fun T hT hTζ w₀ vL₀ vR₀ hlim => ?_⟩
  · -- the driving equation
    simp_rw [hint, ← Finset.mul_sum]
    rw [dilPath, dilPath, hweq _ (hlt ht)]
    ring
  · beta_reduce
    rw [hint]
    simp only [dilPath]
    rw [hvLeq _ (hlt ht) i]
    ring
  · beta_reduce
    rw [hint]
    simp only [dilPath]
    rw [hvReq _ (hlt ht) i]
    ring
  · exact (thresholdCondition_mul_iff (inv_sqrt_ne_zero hc) _ _ _).not.2 (hnt _ (hlt ht))
  · have hζ0 : ζ = 0 := by
      rcases ENNReal.div_eq_zero_iff.1 hζ with h0 | h0
      · exact h0
      · exact absurd h0 ENNReal.coe_ne_top
    have h0 := hthr0 hζ0
    rw [← thresholdCondition_mul_iff (inv_sqrt_ne_zero hc)] at h0
    simpa using h0
  · have hζT : ((c * T : ℝ≥0) : ℝ≥0∞) = ζ := by
      rw [ENNReal.coe_mul, mul_comm, hTζ, ENNReal.div_mul_cancel (ENNReal.coe_ne_zero.2 hc)
        ENNReal.coe_ne_top]
    have hcT : 0 < c * T := mul_pos (pos_iff_ne_zero.2 hc) hT
    rw [← thresholdCondition_mul_iff (sqrt_ne_zero_of_ne hc)]
    refine hthrT (c * T) hcT hζT _ _ _ ?_
    have hΨ : Continuous fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) =>
        ((√(c : ℝ)) * p.1, (fun i => √(c : ℝ) * p.2.1 i), fun i => √(c : ℝ) * p.2.2 i) := by
      fun_prop
    have h2 := (hΨ.tendsto _).comp (hlim.comp (tendsto_inv_mul_nhdsLT hc T))
    refine h2.congr fun t => ?_
    have hsq : √(c : ℝ) * (√(c : ℝ))⁻¹ = 1 := mul_inv_cancel₀ (sqrt_ne_zero_of_ne hc)
    simp only [Function.comp_apply, dilPath, mul_inv_cancel_left₀ hc, ← mul_assoc, hsq, one_mul]

/-! ### The evolution under dilation -/

/-- Brownian scaling in a filtration (Mathlib's `IsBrownianReal.smul`, with the time-changed filtration). -/
theorem _root_.InteractingSLE.IsFilteredBrownianReal.dilate {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hc : c ≠ 0)
    (hB : IsFilteredBrownianReal 𝓕 B P) : IsFilteredBrownianReal (dilFiltration c 𝓕) (dilProc c B) P := by
  obtain ⟨hBM, hadapt, hind⟩ := hB
  refine ⟨hBM.smul hc, fun t => (hadapt (c * t)).const_mul _, fun s t hst => ?_⟩
  have hfun : (fun ω => dilProc c B t ω - dilProc c B s ω) =
      (fun x => (√(c : ℝ))⁻¹ * x) ∘ fun ω => B (c * t) ω - B (c * s) ω := by
    funext ω
    simp [dilProc, mul_sub]
  have hle : MeasurableSpace.comap (fun ω => dilProc c B t ω - dilProc c B s ω) inferInstance ≤
      MeasurableSpace.comap (fun ω => B (c * t) ω - B (c * s) ω) inferInstance := by
    rw [hfun, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_const_mul _).comap_le
  exact indep_of_indep_of_le_left (hind (c * s) (c * t) (mul_le_mul_of_nonneg_left hst c.2)) hle

theorem adaptedBefore_dilate {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {ζ : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ} (hc : c ≠ 0) (hX : AdaptedBefore 𝓕 ζ X) :
    AdaptedBefore (dilFiltration c 𝓕) (fun ω => ζ ω / c) (dilProc c X) := by
  intro t A hA
  have hset : {ω | (t : ℝ≥0∞) < ζ ω / c ∧ dilProc c X t ω ∈ A} =
      {ω | ((c * t : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ X (c * t) ω ∈ (fun x => (√(c : ℝ))⁻¹ * x) ⁻¹' A} := by
    ext ω
    simp only [mem_ofPred_eq, coe_lt_div_iff hc, dilProc, mem_preimage]
  rw [hset]
  exact hX (c * t) _ (measurable_const_mul _ hA)

/-- **Dilation of an integrated evolution** (Aux. lemma 126, p. 401), on the same probability space, for the
time-changed filtration `t ↦ 𝓕_{ct}` and lifetime `ζ / c`. -/
theorem _root_.InteractingSLE.IsIntegratedSLEEvolution.dilate {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hc : c ≠ 0)
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    IsIntegratedSLEEvolution a (fun i => (√(c : ℝ))⁻¹ * xL i) (fun i => (√(c : ℝ))⁻¹ * xR i) ρL ρR P
      (dilFiltration c 𝓕) (dilProc c W) (fun i => dilProc c (VL i)) (fun i => dilProc c (VR i))
      (dilProc c B) (fun ω => ζ ω / c) := by
  obtain ⟨hB, hW, hVL, hVR, hpath⟩ := hE
  exact ⟨hB.dilate hc, adaptedBefore_dilate hc hW, fun i => adaptedBefore_dilate hc (hVL i),
    fun i => adaptedBefore_dilate hc (hVR i), hpath.mono fun ω h => h.dilate hc⟩

/-- **Dilation of an evolution whose force points all sit at the origin** (the two-seed word `0⁻, 0⁺`): the
force word is unchanged. -/
theorem _root_.InteractingSLE.IsIntegratedSLEEvolution.dilate_zero {a : ℝ} {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hc : c ≠ 0)
    (hE : IsIntegratedSLEEvolution a (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ) :
    IsIntegratedSLEEvolution a (fun _ => 0) (fun _ => 0) ρL ρR P
      (dilFiltration c 𝓕) (dilProc c W) (fun i => dilProc c (VL i)) (fun i => dilProc c (VR i))
      (dilProc c B) (fun ω => ζ ω / c) := by
  simpa using hE.dilate hc

/-! ### Traces under dilation -/

/-- Fillings are preserved by a real dilation of the plane. -/
theorem isFilling_image_mul {K A : Set ℂ} {s : ℝ} (hs : 0 < s) (h : IsFilling K A) :
    IsFilling ((fun z => (s : ℂ) * z) '' K) ((fun z => (s : ℂ) * z) '' A) := by
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  set e : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ (s : ℂ) hs0 with he
  have heq : ∀ S : Set ℂ, (fun z => (s : ℂ) * z) '' S = e '' S := fun S => rfl
  have hH : e '' QuantumZipper.H = QuantumZipper.H := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      show 0 < ((s : ℂ) * z).im
      simpa [Complex.mul_im] using mul_pos hs hz
    · intro hw
      refine ⟨(s : ℂ)⁻¹ * w, ?_, by simp [he, hs0]⟩
      show 0 < ((s : ℂ)⁻¹ * w).im
      have : ((s : ℂ)⁻¹ * w).im = s⁻¹ * w.im := by
        rw [← Complex.ofReal_inv, Complex.im_ofReal_mul]
      rw [this]
      exact mul_pos (inv_pos.2 hs) hw
  have hdiff : ∀ S : Set ℂ, QuantumZipper.H \ e '' S = e '' (QuantumZipper.H \ S) := fun S => by
    rw [image_sdiff e.injective, hH]
  obtain ⟨⟨z, hz, hcc⟩, hunb⟩ := h
  have hzA : z ∈ QuantumZipper.H \ A :=
    connectedComponentIn_nonempty_iff.1 ⟨z, hcc ▸ hz⟩
  rw [heq, heq]
  refine ⟨⟨e z, ?_, ?_⟩, ?_⟩
  · rw [hdiff]
    exact mem_image_of_mem e hz
  · rw [hdiff, hdiff, ← e.image_connectedComponentIn hzA, hcc]
  · rw [hdiff]
    intro hb
    apply hunb
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hb
    refine isBounded_iff_forall_norm_le.2 ⟨s⁻¹ * C, fun x hx => ?_⟩
    have h1 := hC (e x) (mem_image_of_mem e hx)
    have h2 : ‖e x‖ = s * ‖x‖ := by
      simp [he, abs_of_pos hs]
    rw [h2] at h1
    rw [le_inv_mul_iff₀ hs]
    exact h1

/-- **Dilation of a generating trace.** If `η` generates the Loewner chain driven by `w` on `[0, T]`, then
`t ↦ (√c)⁻¹ η(ct)` generates the chain driven by `t ↦ (√c)⁻¹ w(ct)` on `[0, T/c]`. -/
theorem _root_.InteractingSLE.IsGeneratingTrace.dilate (hc : c ≠ 0) {w : ℝ≥0 → ℝ} {T : ℝ≥0∞}
    {η : ℝ≥0 → ℂ} (h : IsGeneratingTrace w T η) :
    IsGeneratingTrace (dilPath c w) (T / c) (fun t => (((√(c : ℝ))⁻¹ : ℝ) : ℂ) * η (c * t)) := by
  obtain ⟨h0, hcont, hfill⟩ := h
  have hsc := sqrt_pos_of_ne hc
  have hs : 0 < (√(c : ℝ))⁻¹ := inv_pos.2 hsc
  refine ⟨by simp [h0], ?_, fun t ht => ?_⟩
  · have hmaps : MapsTo (fun t : ℝ≥0 => c * t) {t | (t : ℝ≥0∞) ≤ T / c} {t | (t : ℝ≥0∞) ≤ T} := by
      intro t ht
      have ht' : (t : ℝ≥0∞) ≤ T / c := ht
      rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.coe_ne_zero.2 hc)) (Or.inl ENNReal.coe_ne_top)]
        at ht'
      show ((c * t : ℝ≥0) : ℝ≥0∞) ≤ T
      rwa [ENNReal.coe_mul, mul_comm]
    exact continuousOn_const.mul (hcont.comp (continuous_const.mul continuous_id).continuousOn hmaps)
  · have hfc := hfill (c * t) ((coe_lt_div_iff hc).1 ht)
    set W' : ℝ → ℝ := fun u => w u.toNNReal with hW'
    have hdrv : (fun u : ℝ => dilPath c w u.toNNReal) = fun u => W' (√(c : ℝ) ^ 2 * u) / √(c : ℝ) := by
      funext u
      rw [Real.sq_sqrt (NNReal.coe_nonneg c), dilPath_toNNReal, div_eq_inv_mul]
    have hhull : QuantumZipper.fwdHull (fun u : ℝ => dilPath c w u.toNNReal) t =
        (fun z => (((√(c : ℝ))⁻¹ : ℝ) : ℂ) * z) '' QuantumZipper.fwdHull W' ((c * t : ℝ≥0) : ℝ) := by
      have hsc0 : ((√(c : ℝ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hsc.ne'
      ext z
      rw [hdrv, QuantumZipper.LoewnerAlgebra.mem_fwdHull_scale_iff W' hsc (NNReal.coe_nonneg t),
        Real.sq_sqrt (NNReal.coe_nonneg c), ← NNReal.coe_mul]
      constructor
      · intro hz
        refine ⟨_, hz, ?_⟩
        show (((√(c : ℝ))⁻¹ : ℝ) : ℂ) * ((√(c : ℝ) : ℂ) * z) = z
        rw [Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hsc0, one_mul]
      · rintro ⟨y, hy, rfl⟩
        show (√(c : ℝ) : ℂ) * ((((√(c : ℝ))⁻¹ : ℝ) : ℂ) * y) ∈ _
        rwa [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hsc0, one_mul]
    have himg : (fun u : ℝ≥0 => c * u) '' Icc 0 t = Icc 0 (c * t) := by
      ext u
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨zero_le, mul_le_mul_of_nonneg_left hv.2 c.2⟩
      · intro hu
        refine ⟨c⁻¹ * u, ⟨zero_le, ?_⟩, mul_inv_cancel_left₀ hc u⟩
        rw [inv_mul_le_iff₀ (pos_iff_ne_zero.2 hc)]
        exact hu.2
    have htr : (fun t => (((√(c : ℝ))⁻¹ : ℝ) : ℂ) * η (c * t)) '' Icc 0 t =
        (fun z => (((√(c : ℝ))⁻¹ : ℝ) : ℂ) * z) '' (η '' Icc 0 (c * t)) := by
      rw [← himg, image_image, image_image]
    rw [hhull, htr]
    exact isFilling_image_mul hs hfc

/-- Undoing a dilation. -/
theorem dilPath_inv_dilPath (hc : c ≠ 0) (w : ℝ≥0 → ℝ) : dilPath c⁻¹ (dilPath c w) = w := by
  funext t
  have hs := sqrt_ne_zero_of_ne hc
  simp only [dilPath, NNReal.coe_inv, Real.sqrt_inv, inv_inv, mul_inv_cancel_left₀ hc, ← mul_assoc,
    mul_inv_cancel₀ hs, one_mul]

theorem div_inv_coe (hc : c ≠ 0) (T : ℝ≥0∞) : T / ((c⁻¹ : ℝ≥0) : ℝ≥0∞) = T * c := by
  rw [ENNReal.coe_inv hc, div_eq_mul_inv, inv_inv]

/-- Restricting a generating trace to a shorter horizon. -/
theorem _root_.InteractingSLE.IsGeneratingTrace.mono {w : ℝ≥0 → ℝ} {T T' : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (h : IsGeneratingTrace w T η) (hT : T' ≤ T) : IsGeneratingTrace w T' η :=
  ⟨h.1, h.2.1.mono fun _ ht => le_trans ht hT, fun t ht => h.2.2 t (lt_of_lt_of_le ht hT)⟩

/-! ### The buffered stop (FS11.1) -/

/-- The first time `|w|` reaches `R/4` (`⊤` if it never does). -/
def exitTime (R : ℝ) (w : ℝ≥0 → ℝ) : ℝ≥0∞ := ⨅ (t : ℝ≥0) (_ : R / 4 ≤ |w t|), (t : ℝ≥0∞)

/-- **The buffered stop (FS11.1)**, `S_R = R²/64 ∧ inf{t ≥ 0 : |W_t| ≥ R/4}` (Aux. lemma 126, p. 399). -/
def bufferedStop (R : ℝ) (w : ℝ≥0 → ℝ) : ℝ≥0∞ := min (ENNReal.ofReal (R ^ 2 / 64)) (exitTime R w)

/-- **The dilation identity (FS11.5), lower-bound form.** If `T ≤ c R²/64` and `|w| < √c R/4` on `[0, T]`, then
`T ≤ c S_R(w^{(c)})` for the dilated path `w^{(c)} = (√c)⁻¹ w(c ·)`: in the source's notation (`a = (√c)⁻¹`),
`S_{aR'}(W^{(a)}) = a² S_{R'}(W)` with `R' = √c R`. -/
theorem le_bufferedStop_dilPath_mul (hc : c ≠ 0) {R : ℝ} {w : ℝ≥0 → ℝ} {T : ℝ≥0}
    (hT : (T : ℝ) ≤ c * (R ^ 2 / 64)) (hbd : ∀ t ≤ T, |w t| < √(c : ℝ) * R / 4) :
    (T : ℝ≥0∞) ≤ bufferedStop R (dilPath c w) * c := by
  have hc0 : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hc
  have h1 : (T : ℝ≥0∞) ≤ ENNReal.ofReal (R ^ 2 / 64) * c := by
    rw [← ENNReal.ofReal_coe_nnreal (p := c), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_coe_nnreal (p := T)]
    exact ENNReal.ofReal_le_ofReal (by rw [mul_comm]; exact hT)
  have h2 : (T : ℝ≥0∞) ≤ exitTime R (dilPath c w) * c := by
    have hle : (T : ℝ≥0∞) / c ≤ exitTime R (dilPath c w) := by
      refine le_iInf₂ fun t ht => ?_
      have hsc := sqrt_pos_of_ne hc
      have ht' : √(c : ℝ) * R / 4 ≤ |w (c * t)| := by
        have h' : R / 4 ≤ (√(c : ℝ))⁻¹ * |w (c * t)| := by
          simpa [dilPath, abs_mul, abs_of_pos (inv_pos.2 hsc)] using ht
        rw [le_inv_mul_iff₀ hsc] at h'
        linarith
      have hlt : T < c * t := by
        by_contra hge
        exact absurd (hbd _ (not_lt.1 hge)) (not_lt.2 ht')
      rw [ENNReal.div_le_iff_le_mul (Or.inl hc0) (Or.inl ENNReal.coe_ne_top), mul_comm,
        ← ENNReal.coe_mul]
      exact ENNReal.coe_le_coe.2 hlt.le
    calc (T : ℝ≥0∞) = (T : ℝ≥0∞) / c * c := (ENNReal.div_mul_cancel hc0 ENNReal.coe_ne_top).symm
      _ ≤ exitTime R (dilPath c w) * c := mul_le_mul_left hle _
  rcases min_choice (ENNReal.ofReal (R ^ 2 / 64)) (exitTime R (dilPath c w)) with h | h <;>
    · rwa [bufferedStop, h]

/-! ### Gluing stopped traces -/

/-- **Gluing.** A continuous driver (`w 0 = 0`) that has a generating trace on `[0, S]` for arbitrarily large
horizons `S` has a generating trace on `[0, ∞)`: "The vertical tip limits from the stopped traces coincide on their
overlaps. Their union is the unique continuous Loewner trace on every finite interval" (Aux. lemma 126, p. 401).
The glued trace is the measurable tip selector `LP.traceAt`. -/
theorem exists_isGeneratingTrace_top {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    (h : ∀ T : ℝ≥0, ∃ S : ℝ≥0∞, (T : ℝ≥0∞) < S ∧ ∃ η, IsGeneratingTrace w S η) :
    IsGeneratingTrace w ⊤ fun t => LP.traceAt t w := by
  have heq : ∀ {S : ℝ≥0∞} {η : ℝ≥0 → ℂ}, IsGeneratingTrace w S η → ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < S →
      LP.traceAt t w = η t := fun hη _ ht =>
    LP.traceAt_eq_of_isGeneratingTrace hη hw.continuousOn hw0 ht
  refine ⟨?_, ?_, fun t _ => ?_⟩
  · obtain ⟨S, hS, η, hη⟩ := h 0
    show LP.traceAt 0 w = 0
    rw [heq hη hS, hη.1]
  · refine continuousOn_of_forall_continuousAt fun t _ => ?_
    obtain ⟨S, hS, η, hη⟩ := h t
    have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < S} := isOpen_lt ENNReal.continuous_coe continuous_const
    have hnhds : {s : ℝ≥0 | (s : ℝ≥0∞) < S} ∈ 𝓝 t := hopen.mem_nhds hS
    have hcont : ContinuousAt η t :=
      hη.2.1.continuousAt (Filter.mem_of_superset hnhds fun s (hs : (s : ℝ≥0∞) < S) => show (s : ℝ≥0∞) ≤ S from le_of_lt hs)
    exact hcont.congr (Filter.eventuallyEq_of_mem hnhds fun s hs => (heq hη hs).symm)
  · obtain ⟨S, hS, η, hη⟩ := h t
    have himg : (fun t => LP.traceAt t w) '' Icc 0 t = η '' Icc 0 t :=
      Set.EqOn.image_eq fun s hs => heq hη (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) hS)
    rw [himg]
    exact hη.2.2 t hS

/-! ### Finite-time continuity by dilation -/

/-- **Aux. lemma 126, "finite-time continuity by dilation of the driving law"** (p. 401). Fix a force word whose
marks all sit at the origin (the two-seed word `0⁻, 0⁺`) and a radius `r > 0`. Suppose every integrated evolution
of this word, on every probability space, almost surely has a generating trace through its buffered stop `S_r`
(FS11.1). Then every such evolution with infinite lifetime almost surely has a generating trace on `[0, ∞)`, namely
the measurable tip selector `LP.traceAt`.

The source dilates the driving law; here each dilation `(√c)⁻¹ W_{c·}` of the given evolution is itself an evolution
of the same word on the same space (`IsIntegratedSLEEvolution.dilate_zero`), so the hypothesis applies to it, and
undoing the dilation (`IsGeneratingTrace.dilate`) gives a trace of `W` through `c S_r(W^{(c)})`. Along `c = n + 1`
these horizons exceed every finite time (`le_bufferedStop_dilPath_mul`), and the stopped traces glue
(`exists_isGeneratingTrace_top`). -/
theorem ae_isGeneratingTrace_top_of_bufferedStop {a : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {r : ℝ} (hr : 0 < r)
    (hstop : ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution a (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∃ η, IsGeneratingTrace (fun t => W t ω) (bufferedStop r fun t => W t ω) η)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ fun t => LP.traceAt t fun s => W s ω := by
  have hcn0 : ∀ n : ℕ, ((n : ℝ≥0) + 1) ≠ 0 := fun n => (add_pos_of_nonneg_of_pos (zero_le) one_pos).ne'
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ η, IsGeneratingTrace (dilPath ((n : ℝ≥0) + 1) fun t => W t ω)
      (bufferedStop r (dilPath ((n : ℝ≥0) + 1) fun t => W t ω)) η := by
    rw [ae_all_iff]
    intro n
    exact hstop P _ _ _ _ _ _ (hE.dilate_zero (hcn0 n))
  filter_upwards [hall, hζ, hE.2.2.2.2] with ω hω hζω hpath
  have hw : Continuous fun t => W t ω := by
    have h := hpath.2.2.2.1
    rw [hζω] at h
    exact continuousOn_univ.1 (by simpa using h)
  have hw0 : W 0 ω = 0 := hpath.1
  refine exists_isGeneratingTrace_top hw hw0 fun T => ?_
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T + 1)).exists_bound_of_continuousOn
    hw.continuousOn
  obtain ⟨n, hn⟩ := exists_nat_gt (max (64 * ((T : ℝ) + 1) / r ^ 2) ((4 * |M| / r) ^ 2 + 1))
  set c : ℝ≥0 := (n : ℝ≥0) + 1 with hc
  have hc0 : c ≠ 0 := hcn0 n
  have hcR : ((c : ℝ≥0) : ℝ) = (n : ℝ) + 1 := by simp [hc]
  have hr2 : 0 < r ^ 2 := by positivity
  have h1 : ((T + 1 : ℝ≥0) : ℝ) ≤ c * (r ^ 2 / 64) := by
    have h := (le_max_left _ _).trans_lt hn
    rw [div_lt_iff₀ hr2] at h
    rw [hcR, NNReal.coe_add, NNReal.coe_one]
    nlinarith
  have h2 : ∀ t ≤ T + 1, |W t ω| < √(c : ℝ) * r / 4 := by
    intro t ht
    have hMt : |W t ω| ≤ |M| := ((Real.norm_eq_abs _).symm.le.trans (hM t ⟨zero_le, ht⟩)).trans
      (le_abs_self M)
    have h := (le_max_right _ _).trans_lt hn
    have hsq : 4 * |M| / r < √(c : ℝ) := by
      rw [Real.lt_sqrt (by positivity), hcR]
      linarith
    have : |M| < √(c : ℝ) * r / 4 := by
      rw [div_lt_iff₀ hr] at hsq
      linarith
    linarith
  have hle := le_bufferedStop_dilPath_mul hc0 h1 h2
  obtain ⟨η, hη⟩ := hω n
  have hη' := hη.dilate (inv_ne_zero hc0)
  rw [dilPath_inv_dilPath hc0, div_inv_coe hc0] at hη'
  refine ⟨_, lt_of_lt_of_le ?_ hle, _, hη'⟩
  exact ENNReal.coe_lt_coe.2 (lt_add_one T)

/-- The same conclusion with the lifetime as horizon (the form of the frozen trace statements). -/
theorem ae_isGeneratingTrace_of_bufferedStop {a : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {r : ℝ} (hr : 0 < r)
    (hstop : ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution a (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∃ η, IsGeneratingTrace (fun t => W t ω) (bufferedStop r fun t => W t ω) η)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    ∀ᵐ ω ∂P, ∃ η, IsGeneratingTrace (fun t => W t ω) (ζ ω) η := by
  filter_upwards [ae_isGeneratingTrace_top_of_bufferedStop hr hstop hE hζ, hζ] with ω h1 h2
  exact ⟨_, h2 ▸ h1⟩

end Dilation

end Sec7

end InteractingSLE
