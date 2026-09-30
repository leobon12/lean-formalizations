import QuantumZipper.Proofs.Loewner.Algebra
import QuantumZipper.Zipper.Maps
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# F1d input (b): reflection of the forward map, and of the side images

E-branch node F1d (`blueprint/E_BRANCH_BLUEPRINT.md` §F1): the reflection `z ↦ −z̄` of a
configuration `c = (h, W)` is `(h(−·̄), −W)` and exchanges the two sides of the curve, hence the
two unzipped lengths (Sheffield, arXiv:1012.4797, §5.4, proof of Theorem 1.3, p. 72, "by
symmetry"). `QuantumZipper/Proofs/Zipper/F1Reflect.lean` reduces that statement to the
**side-image identity**

`sideImages (−W) t = (−(sideImages W t).2, −(sideImages W t).1)`,

where `sideImages W t` (`Zipper/Maps.lean`) is the pair of one-sided limits of
`x ↦ (fwdMap W t x).re` as `x → 0∓` (junk if a limit fails to exist). This file proves:

* `isForwardSol_unique_gronwall`: uniqueness of solutions of the forward flow from *any* starting
  point `z : ℂ`, with **no hypothesis on the driver**. The existing `isForwardSol_unique` needs
  `0 < z.im` (it reads existence and monotonicity of `Im`); the Grönwall argument below uses only
  that a solution never vanishes on the compact interval `[0,T]`. In particular the identity
  delivers the solution value outside the hull but also where `fwdMap` is junk (both sides `0`);
* `fwdMap_reflect_of`: `fwdMap (−W) t (−z̄) = −conj (fwdMap W t z)` for *every* `z : ℂ`, with no
  hypothesis on the driver or on the starting point — A1(e) `LoewnerAlgebra.fwdMap_reflect`
  without its `0 < z.im` hypothesis, and without its `Continuous W` hypothesis;
* `fwdMap_reflect_ofReal`: the real-point form `fwdMap (−W) t (−x) = −(fwdMap W t x)`;
* `sideImages_reflect_of_tendsto`, `sideImages_reflect_swap`: the side-image identity, under the
  minimal hypothesis that the two one-sided limits of `x ↦ (fwdMap W t x).re` exist (plus
  `0 ≤ t`), and its almost-sure form `ae_sideImages_reflect`, where the existence hypothesis is
  stated explicitly.

The Grönwall step is mathlib's `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right`
(`Analysis/ODE/Gronwall.lean`), applied to the difference of two solutions, which satisfies
`v t = ∫_0^t (2/u₁ s − 2/u₂ s) ds` and `‖2/u₁ s − 2/u₂ s‖ ≤ (2/(c₁c₂)) ‖v s‖` for
`cᵢ = min_{[0,T]} ‖uᵢ‖ > 0`. The rest is "own elementary proof" (the paper only says
"by symmetry").
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology ENNReal ComplexConjugate

namespace QuantumZipper
namespace F1

/-! ## Uniqueness of forward solutions from an arbitrary starting point -/

/-- A solution of the forward flow on `[0,T]` is bounded away from `0` on `[0,T]`. -/
theorem exists_pos_le_norm_of_isForwardSol {W : ℝ → ℝ} {z : ℂ} {T : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W z T u) (hT : 0 ≤ T) :
    ∃ c > 0, ∀ t ∈ Icc (0 : ℝ) T, c ≤ ‖u t‖ := by
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT)
    (continuous_norm.comp_continuousOn hu.1)
  exact ⟨‖u t₀‖, norm_pos_iff.2 (hu.2 t₀ ht₀).1, fun t ht => isMinOn_iff.1 hmin t ht⟩

/-- `u 0 = z − W 0` for a solution of the forward flow on `[0,T]`, `0 ≤ T`. -/
theorem isForwardSol_zero {W : ℝ → ℝ} {z : ℂ} {T : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W z T u) (hT : 0 ≤ T) : u 0 = z - (W 0 : ℂ) := by
  have h := (hu.2 0 ⟨le_rfl, hT⟩).2
  simpa using h

/-- **Uniqueness of solutions of the centered forward flow on `[0,T]`, from any starting point.**
Two solutions with the same driver and the same starting point `z : ℂ` agree on `[0,T]`. Unlike
`isForwardSol_unique` (A1, `ForwardODE.lean`), there is no hypothesis on `z.im` — and none on the
driver either: the difference `v = u₁ − u₂` satisfies the integral equation
`v t = ∫_0^t (2/u₁ s − 2/u₂ s) ds`, and since both solutions are bounded away from `0` on the
compact interval, Grönwall forces `v = 0`. -/
theorem isForwardSol_unique_gronwall {W : ℝ → ℝ} {z : ℂ} {T : ℝ}
    {u₁ u₂ : ℝ → ℂ} (h1 : IsForwardSol W z T u₁) (h2 : IsForwardSol W z T u₂) :
    EqOn u₁ u₂ (Icc 0 T) := by
  by_cases hT : T ≤ 0
  · intro t ht
    have hT0 : 0 ≤ T := ht.1.trans ht.2
    have ht0 : t = 0 := le_antisymm (ht.2.trans hT) ht.1
    rw [ht0, isForwardSol_zero h1 hT0, isForwardSol_zero h2 hT0]
  · simp only [not_le] at hT
    obtain ⟨c₁, hc₁, hb₁⟩ := exists_pos_le_norm_of_isForwardSol h1 hT.le
    obtain ⟨c₂, hc₂, hb₂⟩ := exists_pos_le_norm_of_isForwardSol h2 hT.le
    have hpos : 0 < c₁ * c₂ := mul_pos hc₁ hc₂
    have hcont1 : ContinuousOn (fun s => (2 : ℂ) / u₁ s) (Icc 0 T) :=
      ContinuousOn.div continuousOn_const h1.1 fun s hs => (h1.2 s hs).1
    have hcont2 : ContinuousOn (fun s => (2 : ℂ) / u₂ s) (Icc 0 T) :=
      ContinuousOn.div continuousOn_const h2.1 fun s hs => (h2.2 s hs).1
    -- the difference solves the integral equation of the difference of the integrands
    have hEq : ∀ y ∈ Icc (0 : ℝ) T, u₁ y - u₂ y =
        ∫ s in (0 : ℝ)..y, ((2 : ℂ) / u₁ s - (2 : ℂ) / u₂ s) := by
      intro y hy
      have hi1 : IntervalIntegrable (fun s => (2 : ℂ) / u₁ s) volume 0 y := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hy.1]
        exact hcont1.mono (Icc_subset_Icc_right hy.2)
      have hi2 : IntervalIntegrable (fun s => (2 : ℂ) / u₂ s) volume 0 y := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hy.1]
        exact hcont2.mono (Icc_subset_Icc_right hy.2)
      have hrearr : (z - (W y : ℂ) + ∫ s in (0 : ℝ)..y, (2 : ℂ) / u₁ s)
            - (z - (W y : ℂ) + ∫ s in (0 : ℝ)..y, (2 : ℂ) / u₂ s)
          = (∫ s in (0 : ℝ)..y, (2 : ℂ) / u₁ s) - ∫ s in (0 : ℝ)..y, (2 : ℂ) / u₂ s := by
        ring
      rw [(h1.2 y hy).2, (h2.2 y hy).2, hrearr, ← intervalIntegral.integral_sub hi1 hi2]
    have hderiv : ∀ t ∈ Ico (0 : ℝ) T,
        HasDerivWithinAt (fun s => u₁ s - u₂ s) ((2 : ℂ) / u₁ t - 2 / u₂ t) (Ici t) t := by
      intro t ht
      have htIcc : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
      have hg : ContinuousOn (fun s => (2 : ℂ) / u₁ s - (2 : ℂ) / u₂ s) (Icc 0 T) :=
        hcont1.sub hcont2
      have hint : IntervalIntegrable (fun s => (2 : ℂ) / u₁ s - (2 : ℂ) / u₂ s) volume 0 t := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le ht.1]
        exact hg.mono (Icc_subset_Icc_right ht.2.le)
      have hfact : Fact (t ∈ Icc (0 : ℝ) T) := ⟨htIcc⟩
      have hFTC : HasDerivWithinAt
          (fun τ => ∫ s in (0 : ℝ)..τ, ((2 : ℂ) / u₁ s - (2 : ℂ) / u₂ s))
          ((2 : ℂ) / u₁ t - 2 / u₂ t) (Icc 0 T) t :=
        intervalIntegral.integral_hasDerivWithinAt_right hint
          (hg.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hg t htIcc)
      have hev : (fun s => u₁ s - u₂ s) =ᶠ[𝓝[Icc (0 : ℝ) T] t]
          fun τ => ∫ s in (0 : ℝ)..τ, ((2 : ℂ) / u₁ s - (2 : ℂ) / u₂ s) :=
        eventually_nhdsWithin_of_forall fun y hy => hEq y hy
      exact (hFTC.congr_of_eventuallyEq hev (hEq t htIcc)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht)
    have hzero : (fun s => u₁ s - u₂ s) 0 = 0 := by
      show u₁ 0 - u₂ 0 = 0
      rw [isForwardSol_zero h1 hT.le, isForwardSol_zero h2 hT.le, sub_self]
    refine fun t ht => sub_eq_zero.1
      (eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := 2 / (c₁ * c₂))
        (h1.1.sub h2.1) hderiv hzero ?_ t ht)
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
    have hne1 : u₁ t ≠ 0 := (h1.2 t htIcc).1
    have hne2 : u₂ t ≠ 0 := (h2.2 t htIcc).1
    have hprod : c₁ * c₂ ≤ ‖u₁ t‖ * ‖u₂ t‖ :=
      mul_le_mul (hb₁ t htIcc) (hb₂ t htIcc) hc₂.le (norm_nonneg _)
    have hprodpos : 0 < ‖u₁ t‖ * ‖u₂ t‖ := lt_of_lt_of_le hpos hprod
    show ‖(2 : ℂ) / u₁ t - 2 / u₂ t‖ ≤ 2 / (c₁ * c₂) * ‖u₁ t - u₂ t‖
    have hsplit : (2 : ℂ) / u₁ t - 2 / u₂ t = (2 * u₂ t - u₁ t * 2) / (u₁ t * u₂ t) :=
      div_sub_div _ _ hne1 hne2
    have hnum : ‖(2 : ℂ) * u₂ t - u₁ t * 2‖ = 2 * ‖u₁ t - u₂ t‖ := by
      rw [show (2 : ℂ) * u₂ t - u₁ t * 2 = -(2 * (u₁ t - u₂ t)) by ring, norm_neg, norm_mul,
        Complex.norm_two]
    rw [hsplit, norm_div, hnum, norm_mul, div_le_iff₀ hprodpos]
    have heq : (2 / (c₁ * c₂) * ‖u₁ t - u₂ t‖) * (c₁ * c₂) = 2 * ‖u₁ t - u₂ t‖ := by
      field_simp
    rw [← heq]
    exact mul_le_mul_of_nonneg_left hprod (by positivity)

/-- `fwdMap W t z` agrees with any solution of the forward flow on `[0,T]`, `t ∈ [0,T]`, with no
hypothesis on `z.im` (`isForwardSol_unique_gronwall`). -/
theorem fwdMap_eq_of_isForwardSol {W : ℝ → ℝ} {z : ℂ} {T : ℝ}
    {u : ℝ → ℂ} (hu : IsForwardSol W z T u) {t : ℝ} (ht : t ∈ Icc 0 T) :
    fwdMap W t z = u t := by
  have hut : IsForwardSol W z t u := isForwardSol_restrict hu ht.1 ht.2
  have hex : ∃ u', IsForwardSol W z t u' := ⟨u, hut⟩
  simp only [fwdMap, dif_pos hex]
  exact isForwardSol_unique_gronwall hex.choose_spec hut (right_mem_Icc.mpr ht.1)

/-! ## Reflection of the forward map -/

private theorem negconj_negconj_side (z : ℂ) : -conj (-conj z) = z := by simp

/-- The conjugate of a solution of the forward flow driven by a *real-valued* `W` is again a
solution (from the conjugate starting point). -/
theorem isForwardSol_conj {W : ℝ → ℝ} {z : ℂ} {S : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W z S u) : IsForwardSol W (conj z) S (fun t => conj (u t)) := by
  refine ⟨Complex.continuous_conj.comp_continuousOn hu.1, fun t ht => ⟨?_, ?_⟩⟩
  · simpa using (hu.2 t ht).1
  · have hconj : conj (u t)
        = conj z - (W t : ℂ) + conj (∫ s in (0 : ℝ)..t, (2 : ℂ) / u s) := by
      rw [(hu.2 t ht).2, map_add, map_sub, Complex.conj_ofReal]
    have hint : conj (∫ s in (0 : ℝ)..t, (2 : ℂ) / u s)
        = ∫ s in (0 : ℝ)..t, (2 : ℂ) / conj (u s) := by
      rw [← intervalIntegral.intervalIntegral_conj]
      congr 1
      funext s
      rw [map_div₀, map_ofNat]
    change conj (u t) = conj z - (W t : ℂ) + ∫ s in (0 : ℝ)..t, (2 : ℂ) / conj (u s)
    rw [hconj, hint]

/-- For real `x`, `fwdMap W t x` is fixed by conjugation (it is real): the conjugate of a
solution is a solution from the same starting point, so uniqueness applies. -/
theorem fwdMap_conj_self_ofReal (W : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    conj (fwdMap W t (x : ℂ)) = fwdMap W t (x : ℂ) := by
  by_cases h : ∃ u, IsForwardSol W (x : ℂ) t u
  · have hu : IsForwardSol W (x : ℂ) t h.choose := h.choose_spec
    have huc : IsForwardSol W (x : ℂ) t fun s => conj (h.choose s) := by
      simpa using isForwardSol_conj hu
    rw [fwdMap_eq_of_isForwardSol hu ⟨ht, le_rfl⟩]
    exact isForwardSol_unique_gronwall huc hu ⟨ht, le_rfl⟩
  · simp only [fwdMap, dif_neg h, map_zero]

/-- **Reflection of the forward map, arbitrary driver and starting point.** For `t ≥ 0` and every
`z : ℂ` (junk values included), `fwdMap (−W) t (−z̄) = −conj (fwdMap W t z)`. This is A1(e)
`LoewnerAlgebra.fwdMap_reflect` with both of its hypotheses dropped: the existence of a solution
on one side is equivalent to existence on the other (`isForwardSol_reflect`, which needs nothing
on `W`), and uniqueness is `isForwardSol_unique_gronwall`. In particular, for `z ∈ H` outside the
hull the two values are the honest forward-flow images of the reflected configuration. -/
theorem fwdMap_reflect_of (W : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    fwdMap (-W) t (-conj z) = -conj (fwdMap W t z) := by
  by_cases h : ∃ u, IsForwardSol W z t u
  · obtain ⟨u, hu⟩ := h
    have hsol : IsForwardSol (-W) (-conj z) t fun s => -conj (u s) :=
      LoewnerAlgebra.isForwardSol_reflect hu
    have hex : ∃ v, IsForwardSol (-W) (-conj z) t v := ⟨_, hsol⟩
    rw [fwdMap_eq_of_isForwardSol hex.choose_spec ⟨ht, le_rfl⟩,
      fwdMap_eq_of_isForwardSol hu ⟨ht, le_rfl⟩]
    exact isForwardSol_unique_gronwall hex.choose_spec hsol ⟨ht, le_rfl⟩
  · have h' : ¬ ∃ v, IsForwardSol (-W) (-conj z) t v := by
      rintro ⟨v, hv⟩
      exact h ⟨_, by
        have := LoewnerAlgebra.isForwardSol_reflect hv
        rwa [neg_neg, negconj_negconj_side] at this⟩
    simp only [fwdMap, dif_neg h, dif_neg h', map_zero, neg_zero]

/-- **Reflection of the forward map at real points.** `fwdMap (−W) t (−x) = −(fwdMap W t x)` for
real `x` (no condition on `x`, no condition on the driver, and no condition on whether `x` is
swallowed: the junk values agree). -/
theorem fwdMap_reflect_ofReal (W : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    fwdMap (-W) t ((-x : ℝ) : ℂ) = -(fwdMap W t (x : ℂ)) := by
  have h := fwdMap_reflect_of W ht (x : ℂ)
  rw [Complex.conj_ofReal, ← Complex.ofReal_neg] at h
  rw [h, fwdMap_conj_self_ofReal W ht x]

/-! ## The side images of the reflected driver -/

/-- Negation maps the left neighbourhood filter of `0` to the right one. -/
theorem tendsto_neg_nhdsLT :
    Tendsto (fun x : ℝ => -x) (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  exact ⟨by simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_of_forall fun x hx => mem_Ioi.mpr (neg_pos.mpr hx)⟩

/-- Negation maps the right neighbourhood filter of `0` to the left one. -/
theorem tendsto_neg_nhdsGT :
    Tendsto (fun x : ℝ => -x) (𝓝[>] (0 : ℝ)) (𝓝[<] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  exact ⟨by simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_of_forall fun x hx => mem_Iio.mpr (neg_lt_zero.mpr (mem_Ioi.mp hx))⟩

/-- The left limit of the reflected driver is minus the right limit of the driver. -/
theorem tendsto_fwdMap_re_nhdsLT {W : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) {b : ℝ}
    (hb : Tendsto (fun x : ℝ => (fwdMap W t x).re) (𝓝[>] (0 : ℝ)) (𝓝 b)) :
    Tendsto (fun x : ℝ => (fwdMap (-W) t x).re) (𝓝[<] (0 : ℝ)) (𝓝 (-b)) := by
  have h1 : Tendsto (fun x : ℝ => (fwdMap W t ((-x : ℝ) : ℂ)).re) (𝓝[<] (0 : ℝ)) (𝓝 b) :=
    hb.comp tendsto_neg_nhdsLT
  refine ((continuous_neg.tendsto b).comp h1).congr fun x => ?_
  have hx := fwdMap_reflect_ofReal W ht (-x)
  rw [neg_neg] at hx
  show -((fwdMap W t ((-x : ℝ) : ℂ)).re) = (fwdMap (-W) t (x : ℂ)).re
  rw [hx, Complex.neg_re]

/-- The right limit of the reflected driver is minus the left limit of the driver. -/
theorem tendsto_fwdMap_re_nhdsGT {W : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) {a : ℝ}
    (ha : Tendsto (fun x : ℝ => (fwdMap W t x).re) (𝓝[<] (0 : ℝ)) (𝓝 a)) :
    Tendsto (fun x : ℝ => (fwdMap (-W) t x).re) (𝓝[>] (0 : ℝ)) (𝓝 (-a)) := by
  have h1 : Tendsto (fun x : ℝ => (fwdMap W t ((-x : ℝ) : ℂ)).re) (𝓝[>] (0 : ℝ)) (𝓝 a) :=
    ha.comp tendsto_neg_nhdsGT
  refine ((continuous_neg.tendsto a).comp h1).congr fun x => ?_
  have hx := fwdMap_reflect_ofReal W ht (-x)
  rw [neg_neg] at hx
  show -((fwdMap W t ((-x : ℝ) : ℂ)).re) = (fwdMap (-W) t (x : ℂ)).re
  rw [hx, Complex.neg_re]

/-- **Side images of the reflected driver, limit form.** If the one-sided limits
`a = lim_{x→0⁻} Re f_t(x)` and `b = lim_{x→0⁺} Re f_t(x)` of the driver `W` exist, then the side
images of `−W` at time `t` are `(−b, −a)`: the two sides are exchanged and the images are
reflected. -/
theorem sideImages_reflect_of_tendsto {W : ℝ → ℝ} {t a b : ℝ} (ht : 0 ≤ t)
    (hL : Tendsto (fun x : ℝ => (fwdMap W t x).re) (𝓝[<] (0 : ℝ)) (𝓝 a))
    (hR : Tendsto (fun x : ℝ => (fwdMap W t x).re) (𝓝[>] (0 : ℝ)) (𝓝 b)) :
    sideImages (-W) t = (-b, -a) :=
  Prod.ext (Filter.Tendsto.limUnder_eq (tendsto_fwdMap_re_nhdsLT ht hR))
    (Filter.Tendsto.limUnder_eq (tendsto_fwdMap_re_nhdsGT ht hL))

/-- **The side-image identity (F1d input (b)).** For `t ≥ 0` and a driver `W` such that the two
one-sided limits of `x ↦ (fwdMap W t x).re` at `0` exist,
`sideImages (−W) t = (−(sideImages W t).2, −(sideImages W t).1)`. This is exactly the `hside`
hypothesis of `F1.unzipLengths_reflect_of`: the existence of the two one-sided limits is the only
input, and it also guarantees that the `limUnder`s in `sideImages` are not junk. -/
theorem sideImages_reflect_swap {W : ℝ → ℝ} {t a b : ℝ} (ht : 0 ≤ t)
    (hL : Tendsto (fun x : ℝ => (fwdMap W t x).re) (𝓝[<] (0 : ℝ)) (𝓝 a))
    (hR : Tendsto (fun x : ℝ => (fwdMap W t x).re) (𝓝[>] (0 : ℝ)) (𝓝 b)) :
    sideImages (-W) t = (-(sideImages W t).2, -(sideImages W t).1) := by
  have h1 : (sideImages W t).1 = a := Filter.Tendsto.limUnder_eq hL
  have h2 : (sideImages W t).2 = b := Filter.Tendsto.limUnder_eq hR
  rw [sideImages_reflect_of_tendsto ht hL hR, h1, h2]

section Ae

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Almost-sure side-image identity.** For a random driver whose one-sided limits at `0` exist
almost surely (the only input not proved here), the side-image identity of the reflected driver
holds almost surely. For `W = drive κ B`, `0 < κ ≤ 4`, `RS.ae_real_alive` shows a.s. that every
real `x ≠ 0` is alive (a forward solution from `x` exists for all times, so `fwdMap` is not junk
there by `fwdMap_eq_of_isForwardSol`); what is missing for the hypothesis below is the continuity
of `x ↦ fwdMap W t x` at `0∓` on the real axis. -/
theorem ae_sideImages_reflect (W : Ω → ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hex : ∀ᵐ ω ∂P, ∃ a b : ℝ,
      Tendsto (fun x : ℝ => (fwdMap (W ω) t x).re) (𝓝[<] (0 : ℝ)) (𝓝 a) ∧
      Tendsto (fun x : ℝ => (fwdMap (W ω) t x).re) (𝓝[>] (0 : ℝ)) (𝓝 b)) :
    ∀ᵐ ω ∂P, sideImages (-(W ω)) t = (-(sideImages (W ω) t).2, -(sideImages (W ω) t).1) := by
  filter_upwards [hex] with ω ⟨a, b, hL, hR⟩
  exact sideImages_reflect_swap ht hL hR

end Ae

end F1
end QuantumZipper
