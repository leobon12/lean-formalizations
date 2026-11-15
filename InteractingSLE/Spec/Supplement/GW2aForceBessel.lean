/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Stochastic.Bessel.Existence
import QuantumZipper.Proofs.RS.TransienceCanon

/-!
# A Bessel process started at `0` is almost surely nonzero at every fixed positive time

Packet PROVE-GW2A-FORCE (input of `FlowFixedTimeInteriorStatement`, "a fixed own time is almost surely not a boundary
time of a flow line"). For `c > 0` (dimension `δ = 1 + 2c > 1`) and a pre-Brownian motion `β` with continuous paths,

  `P[X_r = 0] = 0` for every `r > 0`, where `X = besselProc c 0 β` (`measure_besselProc_zero_eq_zero`).

No transition density is used. The argument:

* **law invariance** (`measure_besselProc_eq_of_isPreBrownianReal`): the event `{X_r = 0}` is the preimage of one
  measurable set of continuous paths (`measurable_besselProc`), and all pre-Brownian motions with continuous paths have
  the same law on `CPath` (QuantumZipper's `RS.map_toCPath_eq`);
* **Brownian scaling** (`IsBesselPath.dilate`, pathwise uniqueness `IsBesselPath.eq`): `t ↦ (√k)⁻¹ X(kt)` is the Bessel
  process from `0` driven by the scaled Brownian motion `t ↦ (√k)⁻¹ β(kt)` (Mathlib's `IsPreBrownianReal.smul`), so
  `r ↦ P[X_r = 0]` is constant on `(0, ∞)`;
* **Fubini** (`measurable_besselProc_uncurry`): `∫₀¹ P[X_r = 0] dr = E |{r ∈ (0, 1] : X_r = 0}| = 0`, since the zero set
  of a Bessel path is Lebesgue-null.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Bessel

/-! ### Time scaling of Bessel paths -/

section Scaling

variable {c x : ℝ} {b X : ℝ≥0 → ℝ}

/-- `k · u.toNNReal = (k u).toNNReal` for real `u`. -/
theorem nnreal_mul_toNNReal (k : ℝ≥0) (u : ℝ) : k * u.toNNReal = ((k : ℝ) * u).toNNReal := by
  rw [Real.toNNReal_mul (NNReal.coe_nonneg k), Real.toNNReal_coe]

/-- **Time scaling of Bessel paths**: if `X` is a Bessel path with `(c, x, b)` and `k > 0`, then `t ↦ X(kt)` is a
Bessel path with `(kc, x, t ↦ b(kt))`. -/
theorem IsBesselPath.time_scale {k : ℝ≥0} (hk : k ≠ 0) (h : IsBesselPath c x b X) :
    IsBesselPath ((k : ℝ) * c) x (fun t => b (k * t)) (fun t => X (k * t)) := by
  have hk' : (k : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hk
  have hkpos : (0 : ℝ) < k := lt_of_le_of_ne (NNReal.coe_nonneg k) (Ne.symm hk')
  have hcomp : ∀ u : ℝ, X (k * u.toNNReal) = X ((k : ℝ) * u).toNNReal := fun u => by
    rw [nnreal_mul_toNNReal]
  refine ⟨h.1.comp (continuous_const.mul continuous_id), fun t => h.2.1 _, ?_, fun t => ?_, fun t => ?_⟩
  · have hset : {s : ℝ | 0 ≤ s ∧ X (k * s.toNNReal) = 0} =
        ((k : ℝ) * ·) ⁻¹' {s : ℝ | 0 ≤ s ∧ X s.toNNReal = 0} := by
      ext s
      simp only [mem_ofPred_eq, mem_preimage, hcomp]
      constructor
      · rintro ⟨hs, h0⟩; exact ⟨mul_nonneg hkpos.le hs, h0⟩
      · rintro ⟨hs, h0⟩; exact ⟨nonneg_of_mul_nonneg_right (by linarith) hkpos, h0⟩
    rw [hset, Real.volume_preimage_mul_left hk', h.2.2.1, mul_zero]
  · have hI := h.2.2.2.1 (k * t)
    have h2 := hI.comp_mul_left (c := (k : ℝ))
    rw [NNReal.coe_mul, zero_div, mul_div_cancel_left₀ _ hk'] at h2
    refine h2.congr fun u _ => ?_
    simp only [hcomp]
  · show X (k * t) = x + b (k * t) + ∫ s in (0 : ℝ)..t, (k : ℝ) * c / X (k * s.toNNReal)
    rw [h.2.2.2.2 (k * t)]
    congr 1
    have hsub := intervalIntegral.integral_comp_mul_left (fun s : ℝ => c / X s.toNNReal) hk' (a := 0) (b := t)
    rw [mul_zero] at hsub
    simp only [NNReal.coe_mul]
    have : ∫ u in (0 : ℝ)..t, (k : ℝ) * c / X (k * u.toNNReal) =
        (k : ℝ) * ∫ u in (0 : ℝ)..t, c / X ((k : ℝ) * u).toNNReal := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun u _ => ?_
      simp only [hcomp, mul_div_assoc]
    rw [this, hsub, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hk', one_mul]

/-- **Brownian scaling of Bessel paths**: if `X` is a Bessel path with `(c, x, b)` and `k > 0`, then
`t ↦ (√k)⁻¹ X(kt)` is a Bessel path with `(c, (√k)⁻¹ x, t ↦ (√k)⁻¹ b(kt))`. -/
theorem IsBesselPath.dilate {k : ℝ≥0} (hk : k ≠ 0) (h : IsBesselPath c x b X) :
    IsBesselPath c ((√(k : ℝ))⁻¹ * x) (fun t => (√(k : ℝ))⁻¹ * b (k * t))
      (fun t => (√(k : ℝ))⁻¹ * X (k * t)) := by
  have hk' : (k : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hk
  have hkpos : (0 : ℝ) < k := lt_of_le_of_ne (NNReal.coe_nonneg k) (Ne.symm hk')
  have hs : 0 < (√(k : ℝ))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hkpos)
  have h2 := (h.time_scale hk).const_mul hs
  have hc : (√(k : ℝ))⁻¹ ^ 2 * ((k : ℝ) * c) = c := by
    rw [inv_pow, Real.sq_sqrt hkpos.le, ← mul_assoc, inv_mul_cancel₀ hk', one_mul]
  rwa [hc] at h2

end Scaling

/-! ### Measurability of the Bessel functional -/

section Meas

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} {c x : ℝ}

omit mΩ in
/-- The Bessel process is the supremum of the regularized processes (definitionally). -/
theorem besselProc_eq_iSup (t : ℝ≥0) (ω : Ω) :
    besselProc c x B t ω = ⨆ n, regProc c (besselEps c n) x B t ω := rfl

/-- The Bessel process at a fixed time is measurable. -/
theorem measurable_besselProc (hBm : ∀ r, Measurable (B r)) (hBc : ∀ ω, Continuous (B · ω)) (hc : 0 < c)
    (t : ℝ≥0) : Measurable (besselProc c x B t) :=
  Measurable.iSup fun n => regProc_measurable' hBm hBc hc.le (besselEps_pos c n) t

/-- The Bessel process is jointly measurable in a real time variable and the sample. -/
theorem measurable_besselProc_uncurry (hBm : ∀ r, Measurable (B r)) (hBc : ∀ ω, Continuous (B · ω))
    (hc : 0 < c) : Measurable (fun p : ℝ × Ω => besselProc c x B p.1.toNNReal p.2) := by
  have hn : ∀ n : ℕ, Measurable (fun p : ℝ × Ω => regProc c (besselEps c n) x B p.1.toNNReal p.2) := by
    intro n
    have := measurable_uncurry_of_continuous_of_measurable
      (u := fun (r : ℝ) (ω : Ω) => regProc c (besselEps c n) x B r.toNNReal ω)
      (fun ω => (continuous_regProc hBc hc.le (besselEps_pos c n) ω).comp continuous_real_toNNReal)
      (fun r => regProc_measurable' hBm hBc hc.le (besselEps_pos c n) r.toNNReal)
    exact this
  exact Measurable.iSup hn

end Meas

/-! ### Law invariance -/

section Law

open QuantumZipper.RS

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {β : ℝ≥0 → Ω → ℝ} {c x : ℝ}

omit [MeasurableSpace Ω] in
/-- The Bessel process of a path-valued process is that of the coordinate process at the path. -/
theorem besselProc_eq_canon (hβc : ∀ ω, Continuous (β · ω)) (t : ℝ≥0) (ω : Ω) :
    besselProc c x β t ω = besselProc c x canonBM t (toCPath β hβc ω) := rfl

/-- **Law invariance**: the probability that the Bessel process vanishes at time `t` is the same for every
pre-Brownian motion with measurable coordinates and continuous paths. -/
theorem measure_besselProc_eq_of_isPreBrownianReal {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {β' : ℝ≥0 → Ω' → ℝ}
    (hβ : IsPreBrownianReal β P) (hβ' : IsPreBrownianReal β' P') (hβm : ∀ t, Measurable (β t))
    (hβm' : ∀ t, Measurable (β' t)) (hβc : ∀ ω, Continuous (β · ω)) (hβc' : ∀ ω, Continuous (β' · ω))
    (hc : 0 < c) (t : ℝ≥0) :
    P {ω | besselProc c x β t ω = 0} = P' {ω | besselProc c x β' t ω = 0} := by
  have hS : MeasurableSet {f : CPath | besselProc c x canonBM t f = 0} :=
    measurable_besselProc measurable_canonBM continuous_canonBM hc t (measurableSet_singleton 0)
  have h1 : {ω | besselProc c x β t ω = 0} = toCPath β hβc ⁻¹' {f | besselProc c x canonBM t f = 0} := rfl
  have h2 : {ω | besselProc c x β' t ω = 0} = toCPath β' hβc' ⁻¹' {f | besselProc c x canonBM t f = 0} := rfl
  rw [h1, h2, ← Measure.map_apply (measurable_toCPath hβm hβc) hS,
    ← Measure.map_apply (measurable_toCPath hβm' hβc') hS, map_toCPath_eq hβ hβ' hβm hβm' hβc hβc']

end Law

/-! ### The fixed-time statement -/

section Fixed

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {β : ℝ≥0 → Ω → ℝ} {c : ℝ}

/-- **Scaling of the zero probability**: `P[X_{kr} = 0] = P[X_r = 0]` for the Bessel process from `0`. -/
theorem measure_besselProc_zero_mul (hβ : IsPreBrownianReal β P) (hβm : ∀ t, Measurable (β t))
    (hβc : ∀ ω, Continuous (β · ω)) (hc : 0 < c) {k : ℝ≥0} (hk : k ≠ 0) (r : ℝ≥0) :
    P {ω | besselProc c 0 β (k * r) ω = 0} = P {ω | besselProc c 0 β r ω = 0} := by
  set β' : ℝ≥0 → Ω → ℝ := fun t ω => (√(k : ℝ))⁻¹ * β (k * t) ω with hβ'def
  have hβ' : IsPreBrownianReal β' P := hβ.smul hk
  have hβm' : ∀ t, Measurable (β' t) := fun t => (hβm (k * t)).const_mul _
  have hβc' : ∀ ω, Continuous (β' · ω) := fun ω =>
    continuous_const.mul ((hβc ω).comp (continuous_const.mul continuous_id))
  have hlaw := measure_besselProc_eq_of_isPreBrownianReal (x := 0) hβ' hβ hβm' hβm hβc' hβc hc r
  have hk' : (k : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hk
  have hkpos : (0 : ℝ) < k := lt_of_le_of_ne (NNReal.coe_nonneg k) (Ne.symm hk')
  have hs : (√(k : ℝ))⁻¹ ≠ 0 := (inv_pos.2 (Real.sqrt_pos.2 hkpos)).ne'
  have hae : ∀ᵐ ω ∂P, besselProc c 0 β' r ω = (√(k : ℝ))⁻¹ * besselProc c 0 β (k * r) ω := by
    filter_upwards [ae_isBesselPath hβ hβc hβm hc le_rfl, ae_isBesselPath hβ' hβc' hβm' hc le_rfl]
      with ω h1 h2
    have h1' := h1.dilate hk
    rw [mul_zero] at h1'
    exact congrFun (h2.eq hc h1') r
  have hset : {ω | besselProc c 0 β' r ω = 0} =ᵐ[P] {ω | besselProc c 0 β (k * r) ω = 0} := by
    filter_upwards [hae] with ω hω
    simp only [hω, mul_eq_zero, hs, false_or]
  rw [← measure_congr hset, hlaw]

/-- **A Bessel process started at `0` is almost surely nonzero at every fixed positive time.** -/
theorem measure_besselProc_zero_eq_zero (hβ : IsPreBrownianReal β P) (hβm : ∀ t, Measurable (β t))
    (hβc : ∀ ω, Continuous (β · ω)) (hc : 0 < c) {r : ℝ≥0} (hr : r ≠ 0) :
    P {ω | besselProc c 0 β r ω = 0} = 0 := by
  -- the probability is the same at every positive time
  have hconst : ∀ s : ℝ≥0, s ≠ 0 → P {ω | besselProc c 0 β s ω = 0} = P {ω | besselProc c 0 β 1 ω = 0} :=
    fun s hs => by simpa using measure_besselProc_zero_mul hβ hβm hβc hc hs 1
  -- Fubini over `(0, 1] × Ω`
  set S : Set (ℝ × Ω) := {p | besselProc c 0 β p.1.toNNReal p.2 = 0} with hSdef
  have hSm : MeasurableSet S := measurable_besselProc_uncurry hβm hβc hc (measurableSet_singleton 0)
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hμ
  have hzero : (μ.prod P) S = 0 := by
    rw [Measure.prod_apply_symm hSm]
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [ae_isBesselPath hβ hβc hβm hc le_rfl] with ω hω
    have hsub : (fun r : ℝ => (r, ω)) ⁻¹' S ∩ Ioc 0 1 ⊆
        {s : ℝ | 0 ≤ s ∧ besselProc c 0 β s.toNNReal ω = 0} := fun s hs => ⟨hs.2.1.le, hs.1⟩
    simp only [Pi.zero_apply]
    rw [hμ, Measure.restrict_apply' measurableSet_Ioc]
    exact measure_mono_null hsub hω.2.2.1
  have hpos : (μ.prod P) S = P {ω | besselProc c 0 β 1 ω = 0} := by
    rw [Measure.prod_apply hSm]
    have hcongr : ∀ r ∈ Ioc (0 : ℝ) 1, P (Prod.mk r ⁻¹' S) = P {ω | besselProc c 0 β 1 ω = 0} :=
      fun r hr => hconst r.toNNReal (Real.toNNReal_pos.2 hr.1).ne'
    rw [hμ, setLIntegral_congr_fun measurableSet_Ioc hcongr, setLIntegral_const, Real.volume_Ioc,
      sub_zero, ENNReal.ofReal_one, mul_one]
  rw [hconst r hr, ← hpos, hzero]

end Fixed

end Bessel

end InteractingSLE
