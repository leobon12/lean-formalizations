/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TerminalPath
import Mathlib.Analysis.ODE.Gronwall

/-!
# Theorem 2.2 assembly: local pathwise uniqueness of integrated `SLE_a(ρ)` paths

Packet PROVE-SEC2-PATCH. Two solutions of the integrated equations of Definition 2.1 (Specification
p. 20; the frozen `IsIntegratedSLEPath`, split as `Sec2.IsForcePath` + `Sec2.DriverEq`) for the
same force word and the **same driving path `b`** that agree at a time `t₀` agree on `[t₀, t₁]`
whenever, on `[t₀, t₁]`, all marks except one group `A` of right marks that sits at the driver at
time `t₀` stay at distance `≥ ε` from the driver (for both solutions), and the total weight of `A`
is `> −2`. This is the deterministic content of the source's "For a stopping time `τ` at which the
driving point is separated from all force points, the process up to its next collision … is the
unique strong solution" (p. 21, property 1, `source/spec/p001-048.md` L468–L476), extended to one
group in contact with the driver (the Bessel-type stage of the proof of Theorem 2.2).

Mathematical argument (added here; nothing is probabilistic):

* the marks of `A` coincide after `t₀` (`IsForcePath.vR_eq_of_eq`: `|V^j − V^k|` cannot grow);
* with `g = V^A − W ≥ 0` and `σ = 1/g − 1/g'`, the gap difference `u = g − g'` satisfies
  `u = ∫ ((2 + ρ_A) σ − ΔF)`, where `ΔF` is the difference of the drifts of the separated marks;
  since `σ` has the sign of `−u` almost everywhere (collision sets are null), `|u| ≤ ∫ |ΔF|`
  (`le_integral_of_sign`);
* `V^A − V'^A = 2 ∫ σ = 2 (u + ∫ ΔF)/(2 + ρ_A)`, so `|W − W'| ≤ C ∫ |ΔF|`;
* `ΔF` and the separated force-point equations are Lipschitz (gaps `≥ ε`), so the total error
  `N` satisfies `N ≤ K ∫ N`, and Grönwall (`eq_zero_of_le_mul_integral`) gives `N = 0`.

The left-group case follows by the reflection `x ↦ −x` (`IsForcePath.reflect`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Assembly

/-! ### Real-variable lemmas -/

/-- **Grönwall, integral form, on `[t₀, t₁]`.** A nonnegative continuous `g` with
`g t ≤ K ∫_{t₀}^t g` vanishes on `[t₀, t₁]`. -/
theorem eq_zero_of_le_mul_integral {g : ℝ → ℝ} {K t₀ t₁ : ℝ}
    (hg0 : ∀ t ∈ Icc t₀ t₁, 0 ≤ g t) (hgc : ContinuousOn g (Icc t₀ t₁))
    (hle : ∀ t ∈ Icc t₀ t₁, g t ≤ K * ∫ s in t₀..t, g s) :
    ∀ t ∈ Icc t₀ t₁, g t = 0 := by
  intro t ht
  set G : ℝ → ℝ := fun u => ∫ s in t₀..u, g s with hGdef
  have hgii : ∀ u ∈ Icc t₀ t₁, IntervalIntegrable g volume t₀ u := fun u hu =>
    (hgc.mono (by rw [uIcc_of_le hu.1]; exact Icc_subset_Icc le_rfl hu.2)).intervalIntegrable
  have hGnonneg : ∀ u ∈ Icc t₀ t₁, 0 ≤ G u := fun u hu =>
    intervalIntegral.integral_nonneg hu.1 fun s hs => hg0 s ⟨hs.1, hs.2.trans hu.2⟩
  have hGcont : ContinuousOn G (Icc t₀ t) := by
    have hInt : IntegrableOn g (uIcc t₀ t) volume := by
      apply ContinuousOn.integrableOn_uIcc
      rw [uIcc_of_le ht.1]
      exact hgc.mono (Icc_subset_Icc le_rfl ht.2)
    have hc := intervalIntegral.continuousOn_primitive_interval hInt
    rwa [uIcc_of_le ht.1] at hc
  have hGderiv : ∀ x ∈ Ico t₀ t, HasDerivWithinAt G (g x) (Ici x) x := by
    intro x hx
    have hxI : x ∈ Icc t₀ t₁ := ⟨hx.1, hx.2.le.trans ht.2⟩
    have hmem : Icc t₀ t₁ ∈ 𝓝[Ioi x] x := by
      refine mem_nhdsWithin.2 ⟨Iio t₁, isOpen_Iio, lt_of_lt_of_le hx.2 ht.2, ?_⟩
      intro y hy
      exact ⟨hx.1.trans (le_of_lt hy.2), le_of_lt hy.1⟩
    have hcont : ContinuousWithinAt g (Ioi x) x :=
      (hgc x hxI).mono_of_mem_nhdsWithin hmem
    have hmeas : StronglyMeasurableAtFilter g (𝓝[Ioi x] x) volume :=
      (hgc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x).filter_mono
        (nhdsWithin_le_of_mem hmem)
    exact intervalIntegral.integral_hasDerivWithinAt_right (hgii x hxI) hmeas hcont
  have hG0 : G t₀ = 0 := by simp [hGdef]
  have hbound : ∀ x ∈ Ico t₀ t, ‖g x‖ ≤ K * ‖G x‖ := by
    intro x hx
    have hxI : x ∈ Icc t₀ t₁ := ⟨hx.1, hx.2.le.trans ht.2⟩
    rw [Real.norm_of_nonneg (hg0 x hxI), Real.norm_of_nonneg (hGnonneg x hxI)]
    exact hle x hxI
  have hGzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hGcont hGderiv hG0 hbound
  have hGt : G t = 0 := hGzero t (right_mem_Icc.mpr ht.1)
  have hlt := hle t ht
  have hint0 : (∫ s in t₀..t, g s) = 0 := hGt
  rw [hint0, mul_zero] at hlt
  exact le_antisymm hlt (hg0 t ht)

/-- A continuous function with `D t₀ ≥ 0` whose increments are integrals of a density that is
nonnegative wherever `D < 0` stays nonnegative (the shifted form of
`Sec2.nonneg_of_integral_eq`). -/
theorem nonneg_of_integral_eq_Icc {D φ : ℝ → ℝ} {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    (hD : ContinuousOn D (Icc t₀ t₁)) (hD0 : 0 ≤ D t₀) (hφ : IntervalIntegrable φ volume t₀ t₁)
    (hinc : ∀ s ∈ Icc t₀ t₁, D s = D t₀ + ∫ r in t₀..s, φ r)
    (hpos : ∀ᵐ r ∂volume, r ∈ Icc t₀ t₁ → D r < 0 → 0 ≤ φ r) : 0 ≤ D t₁ := by
  by_contra hneg0
  have hneg : D t₁ < 0 := lt_of_not_ge hneg0
  set S : Set ℝ := Icc t₀ t₁ ∩ D ⁻¹' Ici 0 with hS
  have hSc : IsClosed S := hD.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have h0S : t₀ ∈ S := ⟨⟨le_rfl, h01⟩, hD0⟩
  have hSb : BddAbove S := ⟨t₁, fun s hs => hs.1.2⟩
  set s₁ := sSup S with hs₁
  have hs₁S : s₁ ∈ S := hSc.csSup_mem ⟨t₀, h0S⟩ hSb
  have hs₁T : s₁ < t₁ := by
    refine lt_of_le_of_ne hs₁S.1.2 fun h => ?_
    have := hs₁S.2
    rw [h] at this
    exact (not_le.2 hneg) this
  have hneg' : ∀ r ∈ Ioc s₁ t₁, D r < 0 := by
    intro r hr
    by_contra hr0
    have hr' : 0 ≤ D r := le_of_not_gt hr0
    have hrS : r ∈ S := ⟨⟨(hs₁S.1.1).trans hr.1.le, hr.2⟩, hr'⟩
    exact (not_le.2 hr.1) (le_csSup hSb hrS)
  have hφ₁ : IntervalIntegrable φ volume t₀ s₁ :=
    hφ.mono_set (by
      rw [uIcc_of_le hs₁S.1.1, uIcc_of_le h01]; exact Icc_subset_Icc le_rfl hs₁T.le)
  have hdiff : D t₁ - D s₁ = ∫ r in s₁..t₁, φ r := by
    rw [hinc t₁ ⟨h01, le_rfl⟩, hinc s₁ hs₁S.1,
      ← intervalIntegral.integral_interval_sub_left hφ hφ₁]
    ring
  have hint : 0 ≤ ∫ r in s₁..t₁, φ r := by
    rw [intervalIntegral.integral_of_le hs₁T.le]
    refine setIntegral_nonneg_of_ae_restrict ?_
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hpos] with r hr hrI
    exact hr ⟨(hs₁S.1.1).trans hrI.1.le, hrI.2⟩ (hneg' r hrI)
  have := hs₁S.2
  simp only [mem_preimage, mem_Ici] at this
  linarith

/-- **Sign comparison.** If `D t₀ = 0`, `D = ∫_{t₀} φ`, and `φ ≤ ψ` almost everywhere where
`D > 0`, with `ψ ≥ 0`, then `D t₁ ≤ ∫_{t₀}^{t₁} ψ`. -/
theorem le_integral_of_sign {D φ ψ : ℝ → ℝ} {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    (hD : ContinuousOn D (Icc t₀ t₁)) (hD0 : D t₀ = 0) (hφ : IntervalIntegrable φ volume t₀ t₁)
    (hψ : IntervalIntegrable ψ volume t₀ t₁) (hψ0 : ∀ r ∈ Icc t₀ t₁, 0 ≤ ψ r)
    (hinc : ∀ s ∈ Icc t₀ t₁, D s = ∫ r in t₀..s, φ r)
    (hsgn : ∀ᵐ r ∂volume, r ∈ Icc t₀ t₁ → 0 < D r → φ r ≤ ψ r) :
    D t₁ ≤ ∫ r in t₀..t₁, ψ r := by
  have hsub : ∀ s ∈ Icc t₀ t₁, uIcc t₀ s ⊆ uIcc t₀ t₁ := fun s hs => by
    rw [uIcc_of_le hs.1, uIcc_of_le h01]; exact Icc_subset_Icc le_rfl hs.2
  have hJc : ContinuousOn (fun s => ∫ r in t₀..s, ψ r) (Icc t₀ t₁) := by
    have hI : IntegrableOn ψ (uIcc t₀ t₁) volume := by
      rw [uIcc_of_le h01]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le h01).1 hψ
    have hc := intervalIntegral.continuousOn_primitive_interval hI
    rwa [uIcc_of_le h01] at hc
  have key := nonneg_of_integral_eq_Icc (D := fun s => (∫ r in t₀..s, ψ r) - D s)
    (φ := fun r => ψ r - φ r) h01 (hJc.sub hD) (by simp [hD0]) (hψ.sub hφ) ?_ ?_
  · simpa [sub_nonneg] using key
  · intro s hs
    show (∫ r in t₀..s, ψ r) - D s = ((∫ r in t₀..t₀, ψ r) - D t₀) + ∫ r in t₀..s, (ψ r - φ r)
    rw [intervalIntegral.integral_same, hD0, sub_zero, zero_add,
      intervalIntegral.integral_sub (hψ.mono_set (hsub s hs)) (hφ.mono_set (hsub s hs)),
      ← hinc s hs]
  · filter_upwards [hsgn] with r hr hrI hneg
    have hJ0 : 0 ≤ ∫ u in t₀..r, ψ u :=
      intervalIntegral.integral_nonneg hrI.1 fun u hu => hψ0 u ⟨hu.1, hu.2.trans hrI.2⟩
    have hneg' : (∫ u in t₀..r, ψ u) - D r < 0 := hneg
    have hDpos : 0 < D r := by linarith
    simpa [sub_nonneg] using hr hrI hDpos

/-- `|c/x − c/y| ≤ |c| |x − y| / ε²` when `|x|, |y| ≥ ε > 0`. -/
theorem abs_div_sub_div_le {c x y ε : ℝ} (hε : 0 < ε) (hx : ε ≤ |x|) (hy : ε ≤ |y|) :
    |c / x - c / y| ≤ |c| / ε ^ 2 * |x - y| := by
  have hx0 : x ≠ 0 := fun h => by simp [h] at hx; linarith
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy; linarith
  have e : c / x - c / y = c * (y - x) / (x * y) := by field_simp
  rw [e, abs_div, abs_mul, abs_mul, abs_sub_comm y x]
  have hxy : ε ^ 2 ≤ |x| * |y| := by
    rw [sq]; exact mul_le_mul hx hy hε.le (abs_nonneg x)
  have hpos : 0 < |x| * |y| := lt_of_lt_of_le (by positivity) hxy
  rw [div_le_iff₀ hpos]
  calc |c| * |x - y| = |c| / ε ^ 2 * |x - y| * ε ^ 2 := by field_simp
    _ ≤ |c| / ε ^ 2 * |x - y| * (|x| * |y|) := by gcongr

/-! ### Real times inside `[t₀, t₁]` -/

theorem toNNReal_mem_Icc {t₀ t₁ : ℝ≥0} {s : ℝ} (hs : s ∈ Icc (t₀ : ℝ) t₁) :
    s.toNNReal ∈ Icc t₀ t₁ :=
  ⟨(Real.le_toNNReal_iff_coe_le (t₀.coe_nonneg.trans hs.1)).2 hs.1,
    Real.toNNReal_le_iff_le_coe.2 hs.2⟩

theorem coe_toNNReal_of_mem_Icc {t₀ t₁ : ℝ≥0} {s : ℝ} (hs : s ∈ Icc (t₀ : ℝ) t₁) :
    ((s.toNNReal : ℝ≥0) : ℝ) = s :=
  Real.coe_toNNReal s (t₀.coe_nonneg.trans hs.1)

theorem toNNReal_lt_of_mem_Icc' {ζ : ℝ≥0∞} {t₀ t₁ : ℝ≥0} (ht₁ : (t₁ : ℝ≥0∞) < ζ) {s : ℝ}
    (hs : s ∈ Icc (t₀ : ℝ) t₁) : (s.toNNReal : ℝ≥0∞) < ζ :=
  lt_of_le_of_lt (by exact_mod_cast (toNNReal_mem_Icc hs).2) ht₁

/-- A path continuous before `ζ` is continuous in real time on `[t₀, t₁]`, `t₁ < ζ`. -/
theorem continuousOn_real {f : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hf : ContinuousOn f {s | (s : ℝ≥0∞) < ζ})
    {t₀ t₁ : ℝ≥0} (ht₁ : (t₁ : ℝ≥0∞) < ζ) :
    ContinuousOn (fun r : ℝ => f r.toNNReal) (Icc (t₀ : ℝ) t₁) :=
  hf.comp continuous_real_toNNReal.continuousOn fun _ hr => toNNReal_lt_of_mem_Icc' ht₁ hr

/-- Restriction of interval integrability from `[0, t₁]` to `[t₀, t]`. -/
theorem intervalIntegrable_mono_Icc {f : ℝ → ℝ} {t₀ t t₁ : ℝ≥0}
    (hf : IntervalIntegrable f volume 0 t₁) (h0 : t₀ ≤ t) (h1 : t ≤ t₁) :
    IntervalIntegrable f volume t₀ t :=
  hf.mono_set (by
    rw [uIcc_of_le (by exact_mod_cast h0 : (t₀ : ℝ) ≤ t), uIcc_of_le t₁.coe_nonneg]
    exact Icc_subset_Icc t₀.coe_nonneg (by exact_mod_cast h1))

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w w' : ℝ≥0 → ℝ} {vL vL' : Fin nL → ℝ≥0 → ℝ} {vR vR' : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ ζ' : ℝ≥0∞}

/-! ### Coincident marks stay together -/

/-- Two right marks that coincide at `t₀` satisfy `vR j ≤ vR k` afterwards. -/
theorem vR_le_of_eq (h : IsForcePath xL xR ρL ρR w vL vR ζ) {t₀ t₁ : ℝ≥0}
    (ht₁ : (t₁ : ℝ≥0∞) < ζ) {j k : Fin nR} (hjk : vR j t₀ = vR k t₀) {t : ℝ≥0}
    (ht : t ∈ Icc t₀ t₁) : vR j t ≤ vR k t := by
  have htζ : (t : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast ht.2) ht₁
  have key := le_integral_of_sign (D := fun r : ℝ => vR j r.toNNReal - vR k r.toNNReal)
    (φ := fun r : ℝ =>
      2 / (vR j r.toNNReal - w r.toNNReal) - 2 / (vR k r.toNNReal - w r.toNNReal))
    (ψ := fun _ => 0) (t₀ := t₀) (t₁ := t) (by exact_mod_cast ht.1)
    ((continuousOn_real (h.continuousOn_vR j) htζ).sub
      (continuousOn_real (h.continuousOn_vR k) htζ))
    (by simp [hjk])
    (intervalIntegrable_mono_Icc ((h.intervalIntegrable_forceR htζ j).sub
      (h.intervalIntegrable_forceR htζ k)) ht.1 le_rfl)
    intervalIntegrable_const (fun _ _ => le_rfl) ?_ ?_
  · simpa using key
  · intro s hs
    have hsN := toNNReal_mem_Icc hs
    have hsl : (s.toNNReal : ℝ≥0∞) < ζ := toNNReal_lt_of_mem_Icc' htζ hs
    have e1 := h.vR_sub hsN.1 hsl j
    have e2 := h.vR_sub hsN.1 hsl k
    rw [coe_toNNReal_of_mem_Icc hs] at e1 e2
    have hsub : uIcc (t₀ : ℝ) s ⊆ uIcc 0 t := by
      rw [uIcc_of_le hs.1, uIcc_of_le t.coe_nonneg]
      exact Icc_subset_Icc t₀.coe_nonneg hs.2
    rw [intervalIntegral.integral_sub ((h.intervalIntegrable_forceR htζ j).mono_set hsub)
      ((h.intervalIntegrable_forceR htζ k).mono_set hsub), ← e1, ← e2, hjk]
    ring
  · have hnull := measure_eq_zero_iff_ae_notMem.1 (h.volume_collisionR k)
    filter_upwards [hnull] with r hr hrI hD
    have hr0 : 0 ≤ r := t₀.coe_nonneg.trans hrI.1
    have hrl : (r.toNNReal : ℝ≥0∞) < ζ := toNNReal_lt_of_mem_Icc' htζ hrI
    have hne : w r.toNNReal ≠ vR k r.toNNReal := fun he => hr ⟨hr0, hrl, he⟩
    have hpos : 0 < vR k r.toNNReal - w r.toNNReal :=
      sub_pos.2 (lt_of_le_of_ne (h.w_le_vR hrl k) hne)
    have hD' : 0 < vR j r.toNNReal - vR k r.toNNReal := hD
    have hle : vR k r.toNNReal - w r.toNNReal ≤ vR j r.toNNReal - w r.toNNReal := by linarith
    have := div_le_div_of_nonneg_left (a := (2 : ℝ)) (by norm_num) hpos hle
    show 2 / (vR j r.toNNReal - w r.toNNReal) - 2 / (vR k r.toNNReal - w r.toNNReal) ≤ 0
    linarith

/-- **Coincident right marks stay together**: if `vR j t₀ = vR k t₀` then `vR j = vR k` on
`[t₀, t₁]`, `t₁ < ζ`. -/
theorem vR_eq_of_eq (h : IsForcePath xL xR ρL ρR w vL vR ζ) {t₀ t₁ : ℝ≥0}
    (ht₁ : (t₁ : ℝ≥0∞) < ζ) {j k : Fin nR} (hjk : vR j t₀ = vR k t₀) {t : ℝ≥0}
    (ht : t ∈ Icc t₀ t₁) : vR j t = vR k t :=
  le_antisymm (vR_le_of_eq h ht₁ hjk ht) (vR_le_of_eq h ht₁ hjk.symm ht)

/-! ### Two solutions driven by the same path -/

/-- Two solutions of the integrated equations for the same force word and the same driving path
`b`, both alive on `[t₀, t₁]` and equal at `t₀`. -/
structure LocalPair (a : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ)
    (w' : ℝ≥0 → ℝ) (vL' : Fin nL → ℝ≥0 → ℝ) (vR' : Fin nR → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ)
    (ζ ζ' : ℝ≥0∞) (t₀ t₁ : ℝ≥0) : Prop where
  path : IsForcePath xL xR ρL ρR w vL vR ζ
  drv : DriverEq a ρL ρR w vL vR b ζ
  path' : IsForcePath xL xR ρL ρR w' vL' vR' ζ'
  drv' : DriverEq a ρL ρR w' vL' vR' b ζ'
  le : t₀ ≤ t₁
  lt : (t₁ : ℝ≥0∞) < ζ
  lt' : (t₁ : ℝ≥0∞) < ζ'
  w₀ : w t₀ = w' t₀
  vL₀ : ∀ i, vL i t₀ = vL' i t₀
  vR₀ : ∀ j, vR j t₀ = vR' j t₀

namespace LocalPair

variable {t₀ t₁ : ℝ≥0}
  (hP : LocalPair a xL xR ρL ρR w vL vR w' vL' vR' b ζ ζ' t₀ t₁)
include hP

theorem lt_of_mem {t : ℝ≥0} (ht : t ∈ Icc t₀ t₁) : (t : ℝ≥0∞) < ζ :=
  lt_of_le_of_lt (by exact_mod_cast ht.2) hP.lt

theorem lt'_of_mem {t : ℝ≥0} (ht : t ∈ Icc t₀ t₁) : (t : ℝ≥0∞) < ζ' :=
  lt_of_le_of_lt (by exact_mod_cast ht.2) hP.lt'

/-- The driver difference is the integral of the drift difference. -/
theorem w_sub_w' {t : ℝ≥0} (ht : t ∈ Icc t₀ t₁) :
    w t - w' t = ∫ r in (t₀ : ℝ)..t,
      (driverDrift ρL ρR w vL vR r - driverDrift ρL ρR w' vL' vR' r) := by
  have e1 := hP.path.w_sub hP.drv ht.1 (hP.lt_of_mem ht)
  have e2 := hP.path'.w_sub hP.drv' ht.1 (hP.lt'_of_mem ht)
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_mono_Icc (hP.path.intervalIntegrable_driverDrift (hP.lt_of_mem ht))
      ht.1 le_rfl)
    (intervalIntegrable_mono_Icc (hP.path'.intervalIntegrable_driverDrift (hP.lt'_of_mem ht))
      ht.1 le_rfl)]
  linarith [hP.w₀]

/-- A left force difference is the integral of the force-integrand difference. -/
theorem vL_sub_vL' {t : ℝ≥0} (ht : t ∈ Icc t₀ t₁) (i : Fin nL) :
    vL i t - vL' i t = ∫ r in (t₀ : ℝ)..t,
      (2 / (vL i r.toNNReal - w r.toNNReal) - 2 / (vL' i r.toNNReal - w' r.toNNReal)) := by
  have e1 := hP.path.vL_sub ht.1 (hP.lt_of_mem ht) i
  have e2 := hP.path'.vL_sub ht.1 (hP.lt'_of_mem ht) i
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_mono_Icc (hP.path.intervalIntegrable_forceL (hP.lt_of_mem ht) i)
      ht.1 le_rfl)
    (intervalIntegrable_mono_Icc (hP.path'.intervalIntegrable_forceL (hP.lt'_of_mem ht) i)
      ht.1 le_rfl)]
  linarith [hP.vL₀ i]

/-- A right force difference is the integral of the force-integrand difference. -/
theorem vR_sub_vR' {t : ℝ≥0} (ht : t ∈ Icc t₀ t₁) (j : Fin nR) :
    vR j t - vR' j t = ∫ r in (t₀ : ℝ)..t,
      (2 / (vR j r.toNNReal - w r.toNNReal) - 2 / (vR' j r.toNNReal - w' r.toNNReal)) := by
  have e1 := hP.path.vR_sub ht.1 (hP.lt_of_mem ht) j
  have e2 := hP.path'.vR_sub ht.1 (hP.lt'_of_mem ht) j
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_mono_Icc (hP.path.intervalIntegrable_forceR (hP.lt_of_mem ht) j)
      ht.1 le_rfl)
    (intervalIntegrable_mono_Icc (hP.path'.intervalIntegrable_forceR (hP.lt'_of_mem ht) j)
      ht.1 le_rfl)]
  linarith [hP.vR₀ j]

end LocalPair

/-! ### Separated marks and the contact group -/

/-- Drift from the left marks and from the right marks outside `A`, at real time `r`. -/
def sepDrift (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (A : Finset (Fin nR)) (w : ℝ≥0 → ℝ)
    (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (r : ℝ) : ℝ :=
  ∑ i, ρL i / (w r.toNNReal - vL i r.toNNReal) +
    ∑ j ∈ Aᶜ, ρR j / (w r.toNNReal - vR j r.toNNReal)

/-- Drift from the right marks in `A`, at real time `r`. -/
def grpDrift (ρR : Fin nR → ℝ) (A : Finset (Fin nR)) (w : ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ)
    (r : ℝ) : ℝ :=
  ∑ j ∈ A, ρR j / (w r.toNNReal - vR j r.toNNReal)

theorem driverDrift_eq_sep_add_grp (A : Finset (Fin nR)) (r : ℝ) :
    driverDrift ρL ρR w vL vR r = sepDrift ρL ρR A w vL vR r + grpDrift ρR A w vR r := by
  unfold driverDrift sepDrift grpDrift
  rw [add_assoc, Finset.sum_compl_add_sum]

theorem intervalIntegrable_sepDrift (h : IsForcePath xL xR ρL ρR w vL vR ζ) (A : Finset (Fin nR))
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    IntervalIntegrable (sepDrift ρL ρR A w vL vR) volume 0 t := by
  have hR := IntervalIntegrable.sum Aᶜ fun j _ => h.intervalIntegrable_driftR ht j
  rw [Finset.sum_fn] at hR
  exact (h.intervalIntegrable_sum_driftL ht).add hR

/-- The total error of the separated coordinates at real time `r`. -/
def errN (A : Finset (Fin nR)) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ)
    (w' : ℝ≥0 → ℝ) (vL' : Fin nL → ℝ≥0 → ℝ) (vR' : Fin nR → ℝ≥0 → ℝ) (r : ℝ) : ℝ :=
  |w r.toNNReal - w' r.toNNReal| + ∑ i, |vL i r.toNNReal - vL' i r.toNNReal| +
    ∑ j ∈ Aᶜ, |vR j r.toNNReal - vR' j r.toNNReal|

theorem errN_nonneg (A : Finset (Fin nR)) (r : ℝ) : 0 ≤ errN A w vL vR w' vL' vR' r := by
  unfold errN; positivity

theorem abs_w_le_errN (A : Finset (Fin nR)) (r : ℝ) :
    |w r.toNNReal - w' r.toNNReal| ≤ errN A w vL vR w' vL' vR' r := by
  unfold errN
  have h1 : 0 ≤ ∑ i, |vL i r.toNNReal - vL' i r.toNNReal| := by positivity
  have h2 : 0 ≤ ∑ j ∈ Aᶜ, |vR j r.toNNReal - vR' j r.toNNReal| := by positivity
  linarith

theorem abs_vL_le_errN (A : Finset (Fin nR)) (r : ℝ) (i : Fin nL) :
    |vL i r.toNNReal - vL' i r.toNNReal| ≤ errN A w vL vR w' vL' vR' r := by
  unfold errN
  have h1 : |vL i r.toNNReal - vL' i r.toNNReal| ≤ ∑ i, |vL i r.toNNReal - vL' i r.toNNReal| :=
    Finset.single_le_sum (f := fun i => |vL i r.toNNReal - vL' i r.toNNReal|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have h2 : 0 ≤ ∑ j ∈ Aᶜ, |vR j r.toNNReal - vR' j r.toNNReal| := by positivity
  have h3 : 0 ≤ |w r.toNNReal - w' r.toNNReal| := abs_nonneg _
  linarith

theorem abs_vR_le_errN {A : Finset (Fin nR)} (r : ℝ) {j : Fin nR} (hj : j ∈ Aᶜ) :
    |vR j r.toNNReal - vR' j r.toNNReal| ≤ errN A w vL vR w' vL' vR' r := by
  unfold errN
  have h1 : |vR j r.toNNReal - vR' j r.toNNReal| ≤ ∑ j ∈ Aᶜ, |vR j r.toNNReal - vR' j r.toNNReal| :=
    Finset.single_le_sum (f := fun j => |vR j r.toNNReal - vR' j r.toNNReal|)
      (fun _ _ => abs_nonneg _) hj
  have h2 : 0 ≤ ∑ i, |vL i r.toNNReal - vL' i r.toNNReal| := by positivity
  have h3 : 0 ≤ |w r.toNNReal - w' r.toNNReal| := abs_nonneg _
  linarith

theorem abs_add_vL_le_errN (A : Finset (Fin nR)) (r : ℝ) (i : Fin nL) :
    |w r.toNNReal - w' r.toNNReal| + |vL i r.toNNReal - vL' i r.toNNReal| ≤
      errN A w vL vR w' vL' vR' r := by
  unfold errN
  have h3 : 0 ≤ ∑ j ∈ Aᶜ, |vR j r.toNNReal - vR' j r.toNNReal| := by positivity
  have h4 : |vL i r.toNNReal - vL' i r.toNNReal| ≤ ∑ i, |vL i r.toNNReal - vL' i r.toNNReal| :=
    Finset.single_le_sum (f := fun i => |vL i r.toNNReal - vL' i r.toNNReal|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  linarith

theorem abs_add_vR_le_errN {A : Finset (Fin nR)} (r : ℝ) {j : Fin nR} (hj : j ∈ Aᶜ) :
    |w r.toNNReal - w' r.toNNReal| + |vR j r.toNNReal - vR' j r.toNNReal| ≤
      errN A w vL vR w' vL' vR' r := by
  unfold errN
  have h3 : 0 ≤ ∑ i, |vL i r.toNNReal - vL' i r.toNNReal| := by positivity
  have h4 : |vR j r.toNNReal - vR' j r.toNNReal| ≤
      ∑ j ∈ Aᶜ, |vR j r.toNNReal - vR' j r.toNNReal| :=
    Finset.single_le_sum (f := fun j => |vR j r.toNNReal - vR' j r.toNNReal|)
      (fun _ _ => abs_nonneg _) hj
  linarith

/-- On `[t₀, t₁]` every left mark and every right mark outside `A` is at distance `≥ ε` from the
driver. -/
def Separated (A : Finset (Fin nR)) (ε : ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (t₀ t₁ : ℝ≥0) : Prop :=
  ∀ s ∈ Icc t₀ t₁, (∀ i, ε ≤ w s - vL i s) ∧ ∀ j ∈ Aᶜ, ε ≤ vR j s - w s

section Lipschitz

variable {A : Finset (Fin nR)} {ε : ℝ} {t₀ t₁ : ℝ≥0}

theorem abs_sepDrift_sub_le (hε : 0 < ε) (hS : Separated A ε w vL vR t₀ t₁)
    (hS' : Separated A ε w' vL' vR' t₀ t₁) {r : ℝ} (hr : r ∈ Icc (t₀ : ℝ) t₁) :
    |sepDrift ρL ρR A w vL vR r - sepDrift ρL ρR A w' vL' vR' r| ≤
      (∑ i, |ρL i| + ∑ j, |ρR j|) / ε ^ 2 * errN A w vL vR w' vL' vR' r := by
  set s := r.toNNReal
  have hs := toNNReal_mem_Icc hr
  obtain ⟨hL, hR⟩ := hS s hs
  obtain ⟨hL', hR'⟩ := hS' s hs
  set E := errN A w vL vR w' vL' vR' r
  have hLi : ∀ i, |ρL i / (w s - vL i s) - ρL i / (w' s - vL' i s)| ≤ |ρL i| / ε ^ 2 * E := by
    intro i
    refine (abs_div_sub_div_le hε ?_ ?_).trans ?_
    · exact (hL i).trans (le_abs_self _)
    · exact (hL' i).trans (le_abs_self _)
    · gcongr
      calc |w s - vL i s - (w' s - vL' i s)| = |(w s - w' s) - (vL i s - vL' i s)| := by ring_nf
        _ ≤ |w s - w' s| + |vL i s - vL' i s| := abs_sub _ _
        _ ≤ E := abs_add_vL_le_errN A r i
  have hRj : ∀ j ∈ Aᶜ, |ρR j / (w s - vR j s) - ρR j / (w' s - vR' j s)| ≤
      |ρR j| / ε ^ 2 * E := by
    intro j hj
    refine (abs_div_sub_div_le hε ?_ ?_).trans ?_
    · rw [abs_sub_comm]; exact (hR j hj).trans (le_abs_self _)
    · rw [abs_sub_comm]; exact (hR' j hj).trans (le_abs_self _)
    · gcongr
      calc |w s - vR j s - (w' s - vR' j s)| = |(w s - w' s) - (vR j s - vR' j s)| := by ring_nf
        _ ≤ |w s - w' s| + |vR j s - vR' j s| := abs_sub _ _
        _ ≤ E := abs_add_vR_le_errN r hj
  have hE : 0 ≤ E := errN_nonneg A r
  unfold sepDrift
  calc |∑ i, ρL i / (w s - vL i s) + ∑ j ∈ Aᶜ, ρR j / (w s - vR j s) -
        (∑ i, ρL i / (w' s - vL' i s) + ∑ j ∈ Aᶜ, ρR j / (w' s - vR' j s))|
      = |∑ i, (ρL i / (w s - vL i s) - ρL i / (w' s - vL' i s)) +
          ∑ j ∈ Aᶜ, (ρR j / (w s - vR j s) - ρR j / (w' s - vR' j s))| := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]; ring_nf
    _ ≤ ∑ i, |ρL i / (w s - vL i s) - ρL i / (w' s - vL' i s)| +
          ∑ j ∈ Aᶜ, |ρR j / (w s - vR j s) - ρR j / (w' s - vR' j s)| :=
        (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _)
          (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i, |ρL i| / ε ^ 2 * E + ∑ j ∈ Aᶜ, |ρR j| / ε ^ 2 * E :=
        add_le_add (Finset.sum_le_sum fun i _ => hLi i) (Finset.sum_le_sum fun j hj => hRj j hj)
    _ ≤ ∑ i, |ρL i| / ε ^ 2 * E + ∑ j, |ρR j| / ε ^ 2 * E := by
        gcongr
        exact Finset.subset_univ _
    _ = (∑ i, |ρL i| + ∑ j, |ρR j|) / ε ^ 2 * E := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_div, ← Finset.sum_div, ← add_mul,
          add_div]

theorem abs_forceL_sub_le (hε : 0 < ε) (hS : Separated A ε w vL vR t₀ t₁)
    (hS' : Separated A ε w' vL' vR' t₀ t₁) {r : ℝ} (hr : r ∈ Icc (t₀ : ℝ) t₁) (i : Fin nL) :
    |2 / (vL i r.toNNReal - w r.toNNReal) - 2 / (vL' i r.toNNReal - w' r.toNNReal)| ≤
      2 / ε ^ 2 * errN A w vL vR w' vL' vR' r := by
  set s := r.toNNReal
  have hs := toNNReal_mem_Icc hr
  refine (abs_div_sub_div_le hε ?_ ?_).trans ?_
  · rw [abs_sub_comm]; exact ((hS s hs).1 i).trans (le_abs_self _)
  · rw [abs_sub_comm]; exact ((hS' s hs).1 i).trans (le_abs_self _)
  · rw [abs_two]
    gcongr
    calc |vL i s - w s - (vL' i s - w' s)| = |(vL i s - vL' i s) - (w s - w' s)| := by ring_nf
      _ ≤ |vL i s - vL' i s| + |w s - w' s| := abs_sub _ _
      _ ≤ errN A w vL vR w' vL' vR' r := by
        rw [add_comm]; exact abs_add_vL_le_errN A r i

theorem abs_forceR_sub_le (hε : 0 < ε) (hS : Separated A ε w vL vR t₀ t₁)
    (hS' : Separated A ε w' vL' vR' t₀ t₁) {r : ℝ} (hr : r ∈ Icc (t₀ : ℝ) t₁) {j : Fin nR}
    (hj : j ∈ Aᶜ) :
    |2 / (vR j r.toNNReal - w r.toNNReal) - 2 / (vR' j r.toNNReal - w' r.toNNReal)| ≤
      2 / ε ^ 2 * errN A w vL vR w' vL' vR' r := by
  set s := r.toNNReal
  have hs := toNNReal_mem_Icc hr
  refine (abs_div_sub_div_le hε ?_ ?_).trans ?_
  · exact ((hS s hs).2 j hj).trans (le_abs_self _)
  · exact ((hS' s hs).2 j hj).trans (le_abs_self _)
  · rw [abs_two]
    gcongr
    calc |vR j s - w s - (vR' j s - w' s)| = |(vR j s - vR' j s) - (w s - w' s)| := by ring_nf
      _ ≤ |vR j s - vR' j s| + |w s - w' s| := abs_sub _ _
      _ ≤ errN A w vL vR w' vL' vR' r := by
        rw [add_comm]; exact abs_add_vR_le_errN r hj

end Lipschitz

/-! ### The contact group -/

namespace LocalPair

variable {t₀ t₁ : ℝ≥0} (hP : LocalPair a xL xR ρL ρR w vL vR w' vL' vR' b ζ ζ' t₀ t₁)
include hP

theorem intervalIntegrable_dSep (A : Finset (Fin nR)) {t : ℝ≥0} (ht : t ∈ Icc t₀ t₁) :
    IntervalIntegrable
      (fun r => sepDrift ρL ρR A w vL vR r - sepDrift ρL ρR A w' vL' vR' r) volume t₀ t :=
  intervalIntegrable_mono_Icc ((intervalIntegrable_sepDrift hP.path A (hP.lt_of_mem ht)).sub
    (intervalIntegrable_sepDrift hP.path' A (hP.lt'_of_mem ht))) ht.1 le_rfl

/-- **The contact group bound.** If the right marks of `A` sit at the driver at `t₀` and their
total weight is `> −2`, then the driver difference and the differences of the marks of `A` are
bounded by `C ∫ |ΔF|`, where `ΔF` is the difference of the separated drifts. -/
theorem group_bound (A : Finset (Fin nR)) (hA : ∀ j ∈ A, vR j t₀ = w t₀)
    (hρA : -2 < ∑ j ∈ A, ρR j) {t : ℝ≥0} (ht : t ∈ Icc t₀ t₁) :
    |w t - w' t| ≤ (4 / (2 + ∑ j ∈ A, ρR j) + 1) *
        ∫ r in (t₀ : ℝ)..t, |sepDrift ρL ρR A w vL vR r - sepDrift ρL ρR A w' vL' vR' r| ∧
      ∀ j ∈ A, |vR j t - vR' j t| ≤ 4 / (2 + ∑ j ∈ A, ρR j) *
        ∫ r in (t₀ : ℝ)..t, |sepDrift ρL ρR A w vL vR r - sepDrift ρL ρR A w' vL' vR' r| := by
  set ρA := ∑ j ∈ A, ρR j with hρAdef
  set ΔF : ℝ → ℝ := fun r => sepDrift ρL ρR A w vL vR r - sepDrift ρL ρR A w' vL' vR' r
    with hΔF
  have ht0 : (t₀ : ℝ) ≤ t := by exact_mod_cast ht.1
  have hΔFi : IntervalIntegrable ΔF volume t₀ t := hP.intervalIntegrable_dSep A ht
  set I := ∫ r in (t₀ : ℝ)..t, |ΔF r| with hIdef
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg ht0 fun _ _ => abs_nonneg _
  have hIabs : |∫ r in (t₀ : ℝ)..t, ΔF r| ≤ I := intervalIntegral.abs_integral_le_integral_abs ht0
  have h2ρ : 0 < 2 + ρA := by linarith
  have hC4 : 0 ≤ 4 / (2 + ρA) := by positivity
  rcases A.eq_empty_or_nonempty with hAe | ⟨j₀, hj₀⟩
  · have hw := hP.w_sub_w' ht
    have hint : (∫ r in (t₀ : ℝ)..t,
        (driverDrift ρL ρR w vL vR r - driverDrift ρL ρR w' vL' vR' r)) =
        ∫ r in (t₀ : ℝ)..t, ΔF r := by
      congr 1
      funext r
      simp only [hΔF, driverDrift_eq_sep_add_grp A, grpDrift, hAe, Finset.sum_empty, add_zero]
    refine ⟨?_, fun j hj => by simp [hAe] at hj⟩
    rw [hw, hint]
    calc |∫ r in (t₀ : ℝ)..t, ΔF r| ≤ I := hIabs
      _ ≤ (4 / (2 + ρA) + 1) * I := le_mul_of_one_le_left hI0 (by linarith)
  · have hA' : ∀ j ∈ A, vR' j t₀ = w' t₀ := fun j hj => by
      rw [← hP.vR₀ j, ← hP.w₀]; exact hA j hj
    have hm : ∀ j ∈ A, ∀ s ∈ Icc t₀ t₁, vR j s = vR j₀ s := fun j hj s hs =>
      vR_eq_of_eq hP.path hP.lt ((hA j hj).trans (hA j₀ hj₀).symm) hs
    have hm' : ∀ j ∈ A, ∀ s ∈ Icc t₀ t₁, vR' j s = vR' j₀ s := fun j hj s hs =>
      vR_eq_of_eq hP.path' hP.lt' ((hA' j hj).trans (hA' j₀ hj₀).symm) hs
    set σ : ℝ → ℝ := fun r =>
      2 / (vR j₀ r.toNNReal - w r.toNNReal) - 2 / (vR' j₀ r.toNNReal - w' r.toNNReal) with hσ
    have hgrp : ∀ r ∈ Icc (t₀ : ℝ) t₁,
        grpDrift ρR A w vR r - grpDrift ρR A w' vR' r = -(ρA / 2) * σ r := by
      intro r hr
      have hs := toNNReal_mem_Icc hr
      have e1 : grpDrift ρR A w vR r = ρA / (w r.toNNReal - vR j₀ r.toNNReal) := by
        unfold grpDrift
        rw [hρAdef, Finset.sum_div]
        exact Finset.sum_congr rfl fun j hj => by rw [hm j hj _ hs]
      have e2 : grpDrift ρR A w' vR' r = ρA / (w' r.toNNReal - vR' j₀ r.toNNReal) := by
        unfold grpDrift
        rw [hρAdef, Finset.sum_div]
        exact Finset.sum_congr rfl fun j hj => by rw [hm' j hj _ hs]
      rw [e1, e2]
      simp only [hσ]
      rw [show w r.toNNReal - vR j₀ r.toNNReal = -(vR j₀ r.toNNReal - w r.toNNReal) by ring,
        show w' r.toNNReal - vR' j₀ r.toNNReal = -(vR' j₀ r.toNNReal - w' r.toNNReal) by ring,
        div_neg, div_neg]
      ring
    have hσi : ∀ s ∈ Icc t₀ t₁, IntervalIntegrable σ volume t₀ s := fun s hs =>
      intervalIntegrable_mono_Icc ((hP.path.intervalIntegrable_forceR (hP.lt_of_mem hs) j₀).sub
        (hP.path'.intervalIntegrable_forceR (hP.lt'_of_mem hs) j₀)) hs.1 le_rfl
    have hew : ∀ s ∈ Icc t₀ t₁, w s - w' s =
        (∫ r in (t₀ : ℝ)..s, ΔF r) - ρA / 2 * ∫ r in (t₀ : ℝ)..s, σ r := by
      intro s hs
      have hs0 : (t₀ : ℝ) ≤ s := by exact_mod_cast hs.1
      rw [hP.w_sub_w' hs]
      have hcongr : EqOn
          (fun r => driverDrift ρL ρR w vL vR r - driverDrift ρL ρR w' vL' vR' r)
          (fun r => ΔF r + -(ρA / 2) * σ r) (uIcc (t₀ : ℝ) s) := by
        intro r hr
        rw [uIcc_of_le hs0] at hr
        have hr' : r ∈ Icc (t₀ : ℝ) t₁ := ⟨hr.1, hr.2.trans (by exact_mod_cast hs.2)⟩
        simp only [driverDrift_eq_sep_add_grp A, hΔF]
        rw [← hgrp r hr']
        ring
      rw [intervalIntegral.integral_congr hcongr,
        intervalIntegral.integral_add (hP.intervalIntegrable_dSep A hs)
          ((hσi s hs).const_mul _), intervalIntegral.integral_const_mul]
      ring
    set u : ℝ → ℝ := fun r =>
      (vR j₀ r.toNNReal - w r.toNNReal) - (vR' j₀ r.toNNReal - w' r.toNNReal) with hu
    set k := 1 + ρA / 2 with hkdef
    have hk : 0 < k := by linarith
    set φ : ℝ → ℝ := fun r => k * σ r - ΔF r with hφ
    have htt : (t : ℝ) ∈ Icc (t₀ : ℝ) t₁ := ⟨ht0, by exact_mod_cast ht.2⟩
    have hu_eq : ∀ s ∈ Icc (t₀ : ℝ) t, u s = ∫ r in (t₀ : ℝ)..s, φ r := by
      intro s hs
      have hs' : s ∈ Icc (t₀ : ℝ) t₁ := ⟨hs.1, hs.2.trans htt.2⟩
      have hsN : s.toNNReal ∈ Icc t₀ t₁ := toNNReal_mem_Icc hs'
      have h1 := hP.vR_sub_vR' hsN j₀
      have h2 := hew _ hsN
      rw [coe_toNNReal_of_mem_Icc hs'] at h1 h2
      have hsub : s.toNNReal ∈ Icc t₀ t := toNNReal_mem_Icc hs
      rw [intervalIntegral.integral_sub ((hσi _ hsN).const_mul k |>.mono_set (by
          rw [coe_toNNReal_of_mem_Icc hs'])) (hP.intervalIntegrable_dSep A hsN |>.mono_set (by
          rw [coe_toNNReal_of_mem_Icc hs'])), intervalIntegral.integral_const_mul]
      have h1' : vR j₀ s.toNNReal - vR' j₀ s.toNNReal = ∫ r in (t₀ : ℝ)..s, σ r := h1
      simp only [hu, hkdef]
      linarith
    have hcu : ContinuousOn u (Icc (t₀ : ℝ) t) :=
      ((continuousOn_real (hP.path.continuousOn_vR j₀) (hP.lt_of_mem ht)).sub
        (continuousOn_real hP.path.continuousOn_w (hP.lt_of_mem ht))).sub
        ((continuousOn_real (hP.path'.continuousOn_vR j₀) (hP.lt'_of_mem ht)).sub
        (continuousOn_real hP.path'.continuousOn_w (hP.lt'_of_mem ht)))
    have hu0 : u t₀ = 0 := by
      simp only [hu, Real.toNNReal_coe, hP.vR₀ j₀, hP.w₀, sub_self]
    have hφi : IntervalIntegrable φ volume t₀ t := ((hσi t ht).const_mul k).sub hΔFi
    have hnull := measure_eq_zero_iff_ae_notMem.1 (hP.path.volume_collisionR j₀)
    have hnull' := measure_eq_zero_iff_ae_notMem.1 (hP.path'.volume_collisionR j₀)
    have hgpos : ∀ᵐ r ∂volume, r ∈ Icc (t₀ : ℝ) t →
        0 < vR j₀ r.toNNReal - w r.toNNReal ∧ 0 < vR' j₀ r.toNNReal - w' r.toNNReal := by
      filter_upwards [hnull, hnull'] with r h1 h2 hr
      have hr' : r ∈ Icc (t₀ : ℝ) t₁ := ⟨hr.1, hr.2.trans htt.2⟩
      have hr0 : 0 ≤ r := t₀.coe_nonneg.trans hr.1
      have hl := toNNReal_lt_of_mem_Icc' hP.lt hr'
      have hl' := toNNReal_lt_of_mem_Icc' hP.lt' hr'
      exact ⟨sub_pos.2 (lt_of_le_of_ne (hP.path.w_le_vR hl j₀) fun he => h1 ⟨hr0, hl, he⟩),
        sub_pos.2 (lt_of_le_of_ne (hP.path'.w_le_vR hl' j₀) fun he => h2 ⟨hr0, hl', he⟩)⟩
    have hup := le_integral_of_sign ht0 hcu hu0 hφi hΔFi.abs (fun _ _ => abs_nonneg _) hu_eq
      (by
        filter_upwards [hgpos] with r hr hrI hpos
        obtain ⟨hg, hg'⟩ := hr hrI
        have hle : vR' j₀ r.toNNReal - w' r.toNNReal ≤ vR j₀ r.toNNReal - w r.toNNReal := by
          have : 0 < u r := hpos
          simp only [hu] at this
          linarith
        have hσ0 : σ r ≤ 0 := by
          have := div_le_div_of_nonneg_left (a := (2 : ℝ)) (by norm_num) hg' hle
          simp only [hσ]
          linarith
        have : k * σ r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk.le hσ0
        show k * σ r - ΔF r ≤ |ΔF r|
        linarith [neg_le_abs (ΔF r)])
    have hun := le_integral_of_sign (D := fun r => -u r) (φ := fun r => -φ r) ht0 hcu.neg
      (by simp [hu0]) hφi.neg hΔFi.abs (fun _ _ => abs_nonneg _)
      (fun s hs => by rw [hu_eq s hs, intervalIntegral.integral_neg])
      (by
        filter_upwards [hgpos] with r hr hrI hpos
        obtain ⟨hg, hg'⟩ := hr hrI
        have hle : vR j₀ r.toNNReal - w r.toNNReal ≤ vR' j₀ r.toNNReal - w' r.toNNReal := by
          have : 0 < -u r := hpos
          simp only [hu] at this
          linarith
        have hσ0 : 0 ≤ σ r := by
          have := div_le_div_of_nonneg_left (a := (2 : ℝ)) (by norm_num) hg hle
          simp only [hσ]
          linarith
        have : 0 ≤ k * σ r := mul_nonneg hk.le hσ0
        show -(k * σ r - ΔF r) ≤ |ΔF r|
        linarith [le_abs_self (ΔF r)])
    have hun' : -u t ≤ I := hun
    have hUabs : |u t| ≤ I := abs_le.2 ⟨by linarith, hup⟩
    have h1 := hP.vR_sub_vR' ht j₀
    have h2 := hew t ht
    have hut : u t = (vR j₀ t - w t) - (vR' j₀ t - w' t) := by simp [hu]
    set S := ∫ r in (t₀ : ℝ)..t, σ r
    set F := ∫ r in (t₀ : ℝ)..t, ΔF r
    have hkS : k * S = u t + F := by
      rw [hut]; simp only [hkdef]; linarith
    have hSabs : |S| ≤ 4 / (2 + ρA) * I := by
      have hS : S = (u t + F) / k := by rw [← hkS]; field_simp
      rw [hS, abs_div, abs_of_pos hk, div_le_iff₀ hk]
      have hk4 : 4 / (2 + ρA) * I * k = 2 * I := by
        rw [hkdef]; field_simp; ring
      rw [hk4]
      calc |u t + F| ≤ |u t| + |F| := abs_add_le _ _
        _ ≤ I + I := add_le_add hUabs hIabs
        _ = 2 * I := by ring
    have hwt : w t - w' t = S - u t := by rw [hut]; linarith
    refine ⟨?_, fun j hj => ?_⟩
    · rw [hwt]
      calc |S - u t| ≤ |S| + |u t| := abs_sub _ _
        _ ≤ 4 / (2 + ρA) * I + I := add_le_add hSabs hUabs
        _ = (4 / (2 + ρA) + 1) * I := by ring
    · rw [hm j hj t ht, hm' j hj t ht, h1]
      exact hSabs

end LocalPair

/-! ### Local uniqueness -/

namespace LocalPair

variable {t₀ t₁ : ℝ≥0} (hP : LocalPair a xL xR ρL ρR w vL vR w' vL' vR' b ζ ζ' t₀ t₁)
include hP

theorem continuousOn_errN (A : Finset (Fin nR)) :
    ContinuousOn (errN A w vL vR w' vL' vR') (Icc (t₀ : ℝ) t₁) := by
  have cw := continuousOn_real (t₀ := t₀) hP.path.continuousOn_w hP.lt
  have cw' := continuousOn_real (t₀ := t₀) hP.path'.continuousOn_w hP.lt'
  unfold errN
  refine ((cw.sub cw').abs.add ?_).add ?_
  · exact continuousOn_finsetSum _ fun i _ =>
      ((continuousOn_real (hP.path.continuousOn_vL i) hP.lt).sub
        (continuousOn_real (hP.path'.continuousOn_vL i) hP.lt')).abs
  · exact continuousOn_finsetSum _ fun j _ =>
      ((continuousOn_real (hP.path.continuousOn_vR j) hP.lt).sub
        (continuousOn_real (hP.path'.continuousOn_vR j) hP.lt')).abs

/-- **Local pathwise uniqueness, right contact group.** Two solutions for the same word and the
same driving path `b` that agree at `t₀` agree on `[t₀, t₁]` if, on `[t₀, t₁]`, every left mark
and every right mark outside `A` stays at distance `≥ ε` from the driver (for both solutions),
the marks of `A` sit at the driver at `t₀`, and the total weight of `A` is `> −2`. `A = ∅` is
allowed (all marks separated). -/
theorem eq_of_rightGroup (A : Finset (Fin nR)) (hA : ∀ j ∈ A, vR j t₀ = w t₀)
    (hρA : -2 < ∑ j ∈ A, ρR j) {ε : ℝ} (hε : 0 < ε) (hS : Separated A ε w vL vR t₀ t₁)
    (hS' : Separated A ε w' vL' vR' t₀ t₁) {t : ℝ≥0} (ht : t ∈ Icc t₀ t₁) :
    w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t := by
  set N := errN A w vL vR w' vL' vR' with hNdef
  set ΔF : ℝ → ℝ := fun r => sepDrift ρL ρR A w vL vR r - sepDrift ρL ρR A w' vL' vR' r
    with hΔF
  set L := (∑ i, |ρL i| + ∑ j, |ρR j|) / ε ^ 2 with hLdef
  set C := 4 / (2 + ∑ j ∈ A, ρR j) + 1 with hCdef
  have hL0 : 0 ≤ L := by positivity
  have h2ρ : 0 < 2 + ∑ j ∈ A, ρR j := by linarith
  have hC0 : 0 ≤ C := by positivity
  set K := C * L + ((nL : ℝ) + nR) * (2 / ε ^ 2) with hKdef
  have hNc := hP.continuousOn_errN A
  have hΔFle : ∀ r ∈ Icc (t₀ : ℝ) t₁, |ΔF r| ≤ L * N r := fun r hr =>
    abs_sepDrift_sub_le hε hS hS' hr
  have hint : ∀ s ∈ Icc (t₀ : ℝ) t₁, IntervalIntegrable N volume t₀ s := fun s hs =>
    (hNc.mono (Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc hs.1
  have hFI : ∀ s ∈ Icc (t₀ : ℝ) t₁, ∫ r in (t₀ : ℝ)..s, |ΔF r| ≤ L * ∫ r in (t₀ : ℝ)..s, N r := by
    intro s hs
    have hsN := toNNReal_mem_Icc hs
    have hΔFi := hP.intervalIntegrable_dSep A hsN
    rw [coe_toNNReal_of_mem_Icc hs] at hΔFi
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hs.1 hΔFi.abs ((hint s hs).const_mul L)
      fun r hr => hΔFle r ⟨hr.1, hr.2.trans hs.2⟩
  have hNle : ∀ s ∈ Icc (t₀ : ℝ) t₁, N s ≤ K * ∫ r in (t₀ : ℝ)..s, N r := by
    intro s hs
    have hsN := toNNReal_mem_Icc hs
    have hcoe := coe_toNNReal_of_mem_Icc hs
    have hJ0 : 0 ≤ ∫ r in (t₀ : ℝ)..s, N r :=
      intervalIntegral.integral_nonneg hs.1 fun r _ => errN_nonneg A r
    have hw := (hP.group_bound A hA hρA hsN).1
    rw [hcoe] at hw
    have hw' : |w s.toNNReal - w' s.toNNReal| ≤ C * L * ∫ r in (t₀ : ℝ)..s, N r := by
      calc _ ≤ C * ∫ r in (t₀ : ℝ)..s, |ΔF r| := hw
        _ ≤ C * (L * ∫ r in (t₀ : ℝ)..s, N r) := mul_le_mul_of_nonneg_left (hFI s hs) hC0
        _ = C * L * ∫ r in (t₀ : ℝ)..s, N r := by ring
    have hLi : ∀ i, |vL i s.toNNReal - vL' i s.toNNReal| ≤
        2 / ε ^ 2 * ∫ r in (t₀ : ℝ)..s, N r := by
      intro i
      rw [hP.vL_sub_vL' hsN i, hcoe]
      refine (intervalIntegral.abs_integral_le_integral_abs hs.1).trans ?_
      rw [← intervalIntegral.integral_const_mul]
      have hfi := intervalIntegrable_mono_Icc
        ((hP.path.intervalIntegrable_forceL (hP.lt_of_mem hsN) i).sub
          (hP.path'.intervalIntegrable_forceL (hP.lt'_of_mem hsN) i)) hsN.1 le_rfl
      rw [hcoe] at hfi
      exact intervalIntegral.integral_mono_on hs.1 hfi.abs ((hint s hs).const_mul _)
        fun r hr => abs_forceL_sub_le hε hS hS' ⟨hr.1, hr.2.trans hs.2⟩ i
    have hRj : ∀ j ∈ Aᶜ, |vR j s.toNNReal - vR' j s.toNNReal| ≤
        2 / ε ^ 2 * ∫ r in (t₀ : ℝ)..s, N r := by
      intro j hj
      rw [hP.vR_sub_vR' hsN j, hcoe]
      refine (intervalIntegral.abs_integral_le_integral_abs hs.1).trans ?_
      rw [← intervalIntegral.integral_const_mul]
      have hfi := intervalIntegrable_mono_Icc
        ((hP.path.intervalIntegrable_forceR (hP.lt_of_mem hsN) j).sub
          (hP.path'.intervalIntegrable_forceR (hP.lt'_of_mem hsN) j)) hsN.1 le_rfl
      rw [hcoe] at hfi
      exact intervalIntegral.integral_mono_on hs.1 hfi.abs ((hint s hs).const_mul _)
        fun r hr => abs_forceR_sub_le hε hS hS' ⟨hr.1, hr.2.trans hs.2⟩ hj
    set J := ∫ r in (t₀ : ℝ)..s, N r
    have hsumL : ∑ i, |vL i s.toNNReal - vL' i s.toNNReal| ≤ (nL : ℝ) * (2 / ε ^ 2 * J) := by
      calc _ ≤ ∑ _i : Fin nL, 2 / ε ^ 2 * J := Finset.sum_le_sum fun i _ => hLi i
        _ = (nL : ℝ) * (2 / ε ^ 2 * J) := by simp
    have hsumR : ∑ j ∈ Aᶜ, |vR j s.toNNReal - vR' j s.toNNReal| ≤ (nR : ℝ) * (2 / ε ^ 2 * J) := by
      calc _ ≤ ∑ _j ∈ Aᶜ, 2 / ε ^ 2 * J := Finset.sum_le_sum fun j hj => hRj j hj
        _ = (Aᶜ.card : ℝ) * (2 / ε ^ 2 * J) := by simp
        _ ≤ (nR : ℝ) * (2 / ε ^ 2 * J) := by
          gcongr
          have := Finset.card_le_univ Aᶜ
          simpa using this
    show |w s.toNNReal - w' s.toNNReal| + ∑ i, |vL i s.toNNReal - vL' i s.toNNReal| +
        ∑ j ∈ Aᶜ, |vR j s.toNNReal - vR' j s.toNNReal| ≤ K * J
    rw [hKdef]
    nlinarith
  have hN0 := eq_zero_of_le_mul_integral (fun r _ => errN_nonneg A r) hNc hNle
  have htt : (t : ℝ) ∈ Icc (t₀ : ℝ) t₁ := ⟨by exact_mod_cast ht.1, by exact_mod_cast ht.2⟩
  have hNt : N t = 0 := hN0 t htt
  have hJ : ∫ r in (t₀ : ℝ)..t, N r = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun r hr => by
      rw [uIcc_of_le htt.1] at hr; exact hN0 r ⟨hr.1, hr.2.trans htt.2⟩]
    simp
  have hzero : ∀ {x : ℝ}, 0 ≤ x → x ≤ 0 → x = 0 := fun h1 h2 => le_antisymm h2 h1
  refine ⟨?_, fun i => ?_, fun j => ?_⟩
  · have := abs_w_le_errN (w := w) (vL := vL) (vR := vR) (w' := w') (vL' := vL') (vR' := vR')
      A (t : ℝ)
    rw [Real.toNNReal_coe] at this
    rw [← sub_eq_zero, ← abs_eq_zero]
    exact hzero (abs_nonneg _) (this.trans hNt.le)
  · have := abs_vL_le_errN (w := w) (vL := vL) (vR := vR) (w' := w') (vL' := vL') (vR' := vR')
      A (t : ℝ) i
    rw [Real.toNNReal_coe] at this
    rw [← sub_eq_zero, ← abs_eq_zero]
    exact hzero (abs_nonneg _) (this.trans hNt.le)
  · by_cases hj : j ∈ A
    · have h := (hP.group_bound A hA hρA ht).2 j hj
      have hF := hFI t htt
      rw [hJ, mul_zero] at hF
      have hpos : 0 ≤ 4 / (2 + ∑ j ∈ A, ρR j) := by positivity
      rw [← sub_eq_zero, ← abs_eq_zero]
      refine hzero (abs_nonneg _) (h.trans ?_)
      exact mul_nonpos_of_nonneg_of_nonpos hpos hF
    · have := abs_vR_le_errN (w := w) (vL := vL) (vR := vR) (w' := w') (vL' := vL') (vR' := vR')
        (A := A) (t : ℝ) (Finset.mem_compl.2 hj)
      rw [Real.toNNReal_coe] at this
      rw [← sub_eq_zero, ← abs_eq_zero]
      exact hzero (abs_nonneg _) (this.trans hNt.le)

end LocalPair

/-! ### Left contact group (by reflection) -/

namespace LocalPair

variable {t₀ t₁ : ℝ≥0}

/-- The reflection `x ↦ −x` (sides exchanged) of a pair of solutions. -/
theorem reflect (hP : LocalPair a xL xR ρL ρR w vL vR w' vL' vR' b ζ ζ' t₀ t₁) :
    LocalPair a (-xR) (-xL) ρR ρL (-w) (fun i => -vR i) (fun i => -vL i) (-w')
      (fun i => -vR' i) (fun i => -vL' i) (-b) ζ ζ' t₀ t₁ where
  path := hP.path.reflect
  drv := hP.drv.reflect
  path' := hP.path'.reflect
  drv' := hP.drv'.reflect
  le := hP.le
  lt := hP.lt
  lt' := hP.lt'
  w₀ := by simp [hP.w₀]
  vL₀ i := by simp [hP.vR₀ i]
  vR₀ j := by simp [hP.vL₀ j]

/-- **Local pathwise uniqueness, left contact group** (the reflection of `eq_of_rightGroup`). -/
theorem eq_of_leftGroup (hP : LocalPair a xL xR ρL ρR w vL vR w' vL' vR' b ζ ζ' t₀ t₁)
    (A : Finset (Fin nL)) (hA : ∀ i ∈ A, vL i t₀ = w t₀) (hρA : -2 < ∑ i ∈ A, ρL i) {ε : ℝ}
    (hε : 0 < ε)
    (hS : ∀ s ∈ Icc t₀ t₁, (∀ i ∈ Aᶜ, ε ≤ w s - vL i s) ∧ ∀ j, ε ≤ vR j s - w s)
    (hS' : ∀ s ∈ Icc t₀ t₁, (∀ i ∈ Aᶜ, ε ≤ w' s - vL' i s) ∧ ∀ j, ε ≤ vR' j s - w' s)
    {t : ℝ≥0} (ht : t ∈ Icc t₀ t₁) :
    w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t := by
  have key := hP.reflect.eq_of_rightGroup A (fun i hi => by simp [hA i hi]) hρA hε
    (fun s hs => ⟨fun j => by have := (hS s hs).2 j; simp only [Pi.neg_apply]; linarith,
      fun i hi => by have := (hS s hs).1 i hi; simp only [Pi.neg_apply]; linarith⟩)
    (fun s hs => ⟨fun j => by have := (hS' s hs).2 j; simp only [Pi.neg_apply]; linarith,
      fun i hi => by have := (hS' s hs).1 i hi; simp only [Pi.neg_apply]; linarith⟩) ht
  obtain ⟨h1, h2, h3⟩ := key
  refine ⟨by simpa using h1, fun i => by simpa using h3 i, fun j => by simpa using h2 j⟩

end LocalPair

end Assembly

end Sec2

end InteractingSLE
