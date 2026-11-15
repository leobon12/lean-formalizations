/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.GlueCond
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane
import InteractingSLE.Spec.Sec4.Prob41Avoid
import InteractingSLE.Foundations.Loewner.Capacity

/-!
# The reflected counterflow hull is closed once its trace stays in `ℍ` (G3 (i) and G6 (c′) of PROVE-GLUECOND)

Packet PROVE-GLUECOND2. Specification §4.2, proof of Proposition 4.9 (`source/spec/p097-144.md#prop-4.9-proof`,
pp. 119–120): "conformally map the picture back to `𝒮`" — the chart `Ψ = R ∘ f_s ∘ R` of `ℍ ∖ R(K′_s)`. WangWu's
`exists_imageTrace` (the image of the flow prefix under `Ψ` is a Loewner trace) needs `R(K′_s)` closed in `ℂ`; for the
**non-simple** counterflow (`κ′ = 16/κ > 4`) `K′_s` is the filled hull, so this is not automatic. This file proves it
deterministically, for every filled hull whose generating set meets `ℝ` only at `0`:

* `exists_real_nhd_subset_closure_of_isFilling`: if `ℍ ∖ K` is a component of `ℍ ∖ A` and a real point `y ∉ A` lies
  in `closure K`, then a whole half-disc at `y` lies in `K` (a half-disc missing `A` either lies in the component or
  misses it), so a real neighbourhood of `y` lies in `closure K`;
* **`ofReal_notMem_closure_of_isFilling`**: hence (real induction, `K` bounded) no real `y ≠ 0` outside `A` is in
  `closure K`;
* **`isClosed_image_negInv_of_closure`**: a bounded, relatively closed `K ⊆ ℍ` whose closure meets `ℝ` only at `0` has
  `R(K)` closed in `ℂ`;
* **`isClosed_image_negInv_fwdHull`**, **`isClosed_cfHullQ_cfHistory`**: for a generating trace that stays in `ℍ` at
  positive times (PROVE-SEC5-R's `CfAvoidLeftQ.ae_trace_im_ne_zero_of_seed` with `Sec4.im_nonneg_of_isGeneratingTrace`),
  `R(K′_s)` and the reflected counterflow hull read from the history are closed in `ℂ`; also `closure K′_s ∩ ℝ = {0}`
  (`eq_zero_of_mem_closure_fwdHull`), the boundary fact Proposition 4.9's boundary correspondence uses.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Sec5.GlueCond

open WangWu hiding ratPt exists_ratPt_dist_lt continuousAt_negInv
open Cond44Ref

/-! ### Filled sets do not reach the real line away from their generating set -/

section Filling

variable {K A : Set ℂ}

/-- **A real point of `closure K` off `A` has a real neighbourhood in `closure K`**, when `ℍ ∖ K` is a component of
`ℍ ∖ A` (`IsFilling`) and `K ⊆ ℍ`: the half-disc at the point misses `A`, meets `K`, and so cannot meet the
component `ℍ ∖ K`. -/
theorem exists_real_nhd_subset_closure_of_isFilling (hfill : IsFilling K A) (hKH : K ⊆ H) (hA : IsClosed A)
    {y : ℝ} (hyA : (y : ℂ) ∉ A) (hy : (y : ℂ) ∈ closure K) :
    ∃ r > 0, ∀ y' : ℝ, |y' - y| < r → (y' : ℂ) ∈ closure K := by
  obtain ⟨⟨z₀, -, hcomp⟩, -⟩ := hfill
  obtain ⟨r, hr, hrA⟩ := Metric.isOpen_iff.1 hA.isOpen_compl (y : ℂ) hyA
  set D := ball (y : ℂ) r ∩ H with hD
  have hDA : D ⊆ H \ A := fun z hz => ⟨hz.2, hrA hz.1⟩
  have hDc : IsPreconnected D := HalfPlaneSep.isPreconnected_ball_inter_H (y : ℂ) r
  -- `D` meets `K`
  obtain ⟨z, hzK, hzy⟩ := Metric.mem_closure_iff.1 hy r hr
  have hzD : z ∈ D := ⟨by rw [mem_ball, dist_comm]; exact hzy, hKH hzK⟩
  -- so `D ⊆ K`
  have hDK : D ⊆ K := by
    intro z₁ hz₁
    by_contra hz₁K
    have hz₁C : z₁ ∈ connectedComponentIn (H \ A) z₀ := by rw [hcomp]; exact ⟨hz₁.2, hz₁K⟩
    have hsub : D ⊆ connectedComponentIn (H \ A) z₀ := by
      rw [connectedComponentIn_eq hz₁C]
      exact hDc.subset_connectedComponentIn hz₁ hDA
    have := hsub hzD
    rw [hcomp] at this
    exact this.2 hzK
  refine ⟨r, hr, fun y' hy' => ?_⟩
  refine closure_mono hDK (Metric.mem_closure_iff.2 fun ε hε => ?_)
  set δ : ℝ := min ε (r - |y' - y|) / 2 with hδ
  have hrpos : 0 < r - |y' - y| := sub_pos.2 hy'
  have hδpos : 0 < δ := by positivity
  have hδε : δ < ε := by
    have := min_le_left ε (r - |y' - y|)
    linarith
  have hδr : δ < r - |y' - y| := by
    have := min_le_right ε (r - |y' - y|)
    linarith
  refine ⟨(y' : ℂ) + δ * Complex.I, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_ball, dist_eq_norm]
    calc ‖(y' : ℂ) + δ * Complex.I - y‖ ≤ ‖((y' - y : ℝ) : ℂ)‖ + ‖(δ : ℂ) * Complex.I‖ := by
          rw [show (y' : ℂ) + δ * Complex.I - y = ((y' - y : ℝ) : ℂ) + (δ : ℂ) * Complex.I by push_cast; ring]
          exact norm_add_le _ _
      _ = |y' - y| + δ := by
          rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_pos hδpos]
      _ < r := by linarith
  · show 0 < ((y' : ℂ) + δ * Complex.I).im
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
      mul_zero, zero_add, mul_one]
    linarith
  · rw [dist_eq_norm, show (y' : ℂ) - ((y' : ℂ) + δ * Complex.I) = -((δ : ℂ) * Complex.I) by ring, norm_neg,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos]
    exact hδε

/-- Real induction to the right: if `y₀` is in the closed set `s` and every point of `s` has a real neighbourhood in
`s`, then `[y₀, b] ⊆ s`. -/
theorem Icc_subset_of_real_nhd {s : Set ℝ} (hs : IsClosed s) {y₀ b : ℝ} (h₀ : y₀ ∈ s)
    (hnhd : ∀ x ∈ s, y₀ ≤ x → ∃ r > 0, ∀ x' : ℝ, |x' - x| < r → x' ∈ s) : Icc y₀ b ⊆ s := by
  refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin (hs.inter isClosed_Icc) h₀ fun x hx => ?_
  obtain ⟨r, hr, hxr⟩ := hnhd x hx.1 hx.2.1
  refine mem_nhdsWithin_of_mem_nhds (Filter.mem_of_superset (Ioo_mem_nhds (by linarith : x - r < x)
    (by linarith : x < x + r)) fun x' hx' => hxr x' ?_)
  rw [abs_lt]
  constructor <;> linarith [hx'.1, hx'.2]

/-- **A bounded filled set does not reach the real line away from its generating set**: if `ℍ ∖ K` is a component of
`ℍ ∖ A`, `K ⊆ ℍ` is bounded and `A` is closed and meets `ℝ` at most at `0`, then no real `y ≠ 0` lies in
`closure K`. -/
theorem ofReal_notMem_closure_of_isFilling (hfill : IsFilling K A) (hKH : K ⊆ H)
    (hKb : Bornology.IsBounded K) (hA : IsClosed A) (hAr : ∀ y : ℝ, y ≠ 0 → (y : ℂ) ∉ A) {y : ℝ} (hy0 : y ≠ 0) :
    (y : ℂ) ∉ closure K := by
  intro hy
  obtain ⟨M, hM⟩ := hKb.closure.subset_closedBall 0
  have hfar : ∀ b : ℝ, |M| < |b| → (b : ℂ) ∉ closure K := fun b hb hbK => by
    have h1 := hM hbK
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at h1
    linarith [le_abs_self M]
  rcases lt_or_gt_of_ne hy0 with hneg | hpos
  · -- to the left: real induction on `x ↦ −x`
    set s : Set ℝ := {x | ((-x : ℝ) : ℂ) ∈ closure K} with hs
    have hsc : IsClosed s := isClosed_closure.preimage (Complex.continuous_ofReal.comp continuous_neg)
    have hsub := Icc_subset_of_real_nhd (b := -y + |M| + 1) hsc (y₀ := -y) (by simpa [hs] using hy)
      fun x hx hxy => by
        have hxA : ((-x : ℝ) : ℂ) ∉ A := hAr (-x) (by linarith)
        obtain ⟨r, hr, hr'⟩ := exists_real_nhd_subset_closure_of_isFilling hfill hKH hA hxA hx
        refine ⟨r, hr, fun x' hx' => hr' (-x') ?_⟩
        rw [show -x' - -x = -(x' - x) by ring, abs_neg]
        exact hx'
    have hb := hsub ⟨by linarith [abs_nonneg M], le_rfl⟩
    refine hfar (-(-y + |M| + 1)) ?_ hb
    rw [abs_neg, abs_of_pos (show (0 : ℝ) < -y + |M| + 1 by linarith [abs_nonneg M])]
    linarith
  · set s : Set ℝ := {x | (x : ℂ) ∈ closure K} with hs
    have hsc : IsClosed s := isClosed_closure.preimage Complex.continuous_ofReal
    have hsub := Icc_subset_of_real_nhd (b := y + |M| + 1) hsc (y₀ := y) hy fun x hx hxy =>
      exists_real_nhd_subset_closure_of_isFilling hfill hKH hA (hAr x (by linarith)) hx
    have hb := hsub ⟨by linarith [abs_nonneg M], le_rfl⟩
    refine hfar (y + |M| + 1) ?_ hb
    rw [abs_of_pos (show (0 : ℝ) < y + |M| + 1 by linarith [abs_nonneg M])]
    linarith

end Filling

/-! ### The reflection of such a hull is closed in `ℂ` -/

section Reflect

/-- **A bounded, relatively closed `K ⊆ ℍ` whose closure meets `ℝ` only at `0` has `R(K)` closed in `ℂ`**
(`R(z) = −1/z`): a limit of `R(z_n)` is not `0` (`K` is bounded), so it is `R` of a point of `closure K`, which is in
`ℍ` (hence in `K`) or real (hence `0`, impossible). -/
theorem isClosed_image_negInv_of_closure {K : Set ℂ} (hKH : K ⊆ H) (hKb : Bornology.IsBounded K)
    (hrel : closure K ∩ H ⊆ K) (hreal : ∀ y : ℝ, y ≠ 0 → (y : ℂ) ∉ closure K) : IsClosed (negInv '' K) := by
  refine isClosed_of_closure_subset fun ζ hζ => ?_
  obtain ⟨M, hM⟩ := hKb.subset_closedBall 0
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    obtain ⟨b, ⟨z, hzK, rfl⟩, hb⟩ := Metric.mem_closure_iff.1 hζ (1 / (|M| + 1)) (by positivity)
    have hz0 : z ≠ 0 := fun h => by
      have h1 := hKH hzK
      rw [h] at h1
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h1)
    have h1 := hM hzK
    rw [mem_closedBall, dist_zero_right] at h1
    rw [dist_zero_left, negInv, norm_neg, norm_inv, one_div] at hb
    have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have h2 : |M| + 1 < ‖z‖ := (inv_lt_inv₀ hzpos (by positivity)).1 hb
    linarith [le_abs_self M]
  have hc : negInv ζ ∈ closure K := by
    have h1 := mem_closure_image (WangWu.continuousAt_negInv hζ0) hζ
    rwa [image_image, show (fun z => negInv (negInv z)) = id from funext Sec7.StripSysField.negInv_negInv,
      image_id] at h1
  by_cases hH : negInv ζ ∈ H
  · exact ⟨negInv ζ, hrel ⟨hc, hH⟩, Sec7.StripSysField.negInv_negInv ζ⟩
  · exfalso
    have hcl : closure K ⊆ {z : ℂ | 0 ≤ z.im} :=
      closure_minimal (fun z hz => (show (0 : ℝ) < z.im from hKH hz).le)
        (isClosed_le continuous_const Complex.continuous_im)
    have him : (negInv ζ).im = 0 := le_antisymm (not_lt.1 hH) (hcl hc)
    have hre : (((negInv ζ).re : ℝ) : ℂ) = negInv ζ := Complex.ext rfl (by rw [Complex.ofReal_im, him])
    have hne : (negInv ζ).re ≠ 0 := by
      intro h0
      have h2 : negInv ζ = 0 := by rw [← hre, h0, Complex.ofReal_zero]
      rw [negInv, neg_eq_zero, inv_eq_zero] at h2
      exact hζ0 h2
    exact hreal _ hne (hre ▸ hc)

end Reflect

/-! ### Loewner hulls of traces that stay in `ℍ` -/

section Hull

variable {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- **The filled hull of a trace that stays in `ℍ` at positive times reaches `ℝ` only at `0`.** -/
theorem ofReal_notMem_closure_fwdHull (hw : Continuous fun s : ℝ => w s.toNNReal) (hη : IsGeneratingTrace w T η)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) (hH : ∀ r : ℝ≥0, 0 < r → r ≤ t → η r ∈ H) {y : ℝ} (hy0 : y ≠ 0) :
    (y : ℂ) ∉ closure (fwdHull (fun s : ℝ => w s.toNNReal) t) := by
  have hcont : ContinuousOn η (Icc 0 t) :=
    hη.2.1.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans ht.le
  refine ofReal_notMem_closure_of_isFilling (hη.2.2 t ht) (fun _ hz => hz.1)
    (InteractingSLE.isBounded_fwdHull hw t) (isCompact_Icc.image_of_continuousOn hcont).isClosed ?_ hy0
  rintro x hx ⟨r, hr, hrx⟩
  by_cases h0 : r = 0
  · rw [h0, hη.1] at hrx
    exact hx (by exact_mod_cast hrx.symm)
  · have hpos : 0 < r := pos_iff_ne_zero.2 h0
    have h2 : (0 : ℝ) < (η r).im := hH r hpos hr.2
    rw [hrx, Complex.ofReal_im] at h2
    exact lt_irrefl _ h2

/-- The same, for complex points: a real point of the closure of the hull is `0`. -/
theorem eq_zero_of_mem_closure_fwdHull (hw : Continuous fun s : ℝ => w s.toNNReal) (hη : IsGeneratingTrace w T η)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) (hH : ∀ r : ℝ≥0, 0 < r → r ≤ t → η r ∈ H) {z : ℂ}
    (hz : z ∈ closure (fwdHull (fun s : ℝ => w s.toNNReal) t)) (him : z.im = 0) : z = 0 := by
  have hre : ((z.re : ℝ) : ℂ) = z := Complex.ext rfl (by rw [Complex.ofReal_im, him])
  by_contra hz0
  have hne : z.re ≠ 0 := fun h0 => hz0 (by rw [← hre, h0, Complex.ofReal_zero])
  exact ofReal_notMem_closure_fwdHull hw hη ht hH hne (hre ▸ hz)

/-- **`R(K_t)` is closed in `ℂ`** for the filled hull of a trace that stays in `ℍ` at positive times. -/
theorem isClosed_image_negInv_fwdHull (hw : Continuous fun s : ℝ => w s.toNNReal) (hη : IsGeneratingTrace w T η)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) (hH : ∀ r : ℝ≥0, 0 < r → r ≤ t → η r ∈ H) :
    IsClosed (negInv '' fwdHull (fun s : ℝ => w s.toNNReal) t) :=
  isClosed_image_negInv_of_closure (fun _ hz => hz.1) (InteractingSLE.isBounded_fwdHull hw t)
    (Aux50Hit.closure_fwdHull_inter_H hw t.coe_nonneg).le fun _ hy => ofReal_notMem_closure_fwdHull hw hη ht hH hy

end Hull

/-- **The reflected counterflow hull read from the history is closed in `ℂ`** on a good counterflow sample whose
generating trace (chart `R`) is never real at positive times (PROVE-SEC5-R's
`CfAvoidLeftQ.ae_trace_im_ne_zero_of_seed`). This is the closedness WangWu's `exists_imageTrace` needs for the chart
`Ψ = revChart` of `ℍ ∖ R(K′_t)` (Proposition 4.9). -/
theorem isClosed_cfHullQ_cfHistory {Ω₂ : Type*} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞} {ω : Ω₂} (hζ : ζ₂ ω = ⊤)
    (hw0 : W₂ 0 ω = 0) (hw : Continuous fun t => W₂ t ω) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (fun t => W₂ t ω) ⊤ η) (him : ∀ r : ℝ≥0, 0 < r → (η r).im ≠ 0) (t : ℝ≥0) :
    IsClosed (cfHullQ t (cfHistory W₂ ζ₂ ω)) := by
  have hwc : Continuous fun s : ℝ => W₂ s.toNNReal ω := hw.comp continuous_real_toNNReal
  rw [cfHullQ, hullAt_cfHistory hζ hw0 hw t]
  exact isClosed_image_negInv_fwdHull (w := fun t => W₂ t ω) hwc hη ENNReal.coe_lt_top fun r hr _ =>
    lt_of_le_of_ne (Sec4.im_nonneg_of_isGeneratingTrace hwc hw0 hη r) (him r hr).symm

end InteractingSLE.Sec5.GlueCond
