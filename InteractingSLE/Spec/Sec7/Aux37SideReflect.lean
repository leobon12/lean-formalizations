/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37SideChart
import InteractingSLE.Spec.Supplement.GB8EnergyKoebe
import InteractingSLE.Foundations.Loewner.RealPoints

/-!
# Aux. lemma 37's side germ: consequences of Schwarz reflection

Packet PROVE-STRIPSYS42. Generic lemmas for a map `φ` that is conformal on an upper half-disc `ℍ ∩ B(x, ρ)` with real
boundary values on the diameter (`R16.IsRealBoundaryConformal`), and for the real Loewner flow:

* `strictMonoOn_re`: the boundary values `t ↦ φ(t)` increase strictly on the diameter (the reflected map has positive
  derivative there, `R16.IsRealBoundaryConformal.deriv_schwarzReflect_pos`);
* `exists_ball_image`: the open mapping theorem at a real point: a closed upper half-neighbourhood of `φ(y)` is the
  image of closed upper half-disc points, with `ℍ` from `ℍ` and `ℝ` from `ℝ`;
* **`exists_int_tendsto_im_sub_of_transition'`**: the branch relation (BR) of `Aux37Germ` for a transition that only
  agrees with `φ_c ∘ g` on the open half-disc (`φ_c` takes junk values on the hull, so its composite is not continuous
  up to the diameter; the reflected extension is a different function there);
* `re_pos_of_isForwardSol_real`: the real Loewner flow keeps a positive real point positive.

No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param` (R43, R48).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Function Complex
open QuantumZipper (H Hbar fwdHull fwdMap)
open QuantumZipper.CA (schwarzReflect)
open scoped Real

namespace InteractingSLE.Sec7.Aux37Side

/-! ### Reflection -/

section Reflect

variable {φ : ℂ → ℂ} {x ρ : ℝ}

theorem ofReal_mem_ball_iff {t : ℝ} : ((t : ℝ) : ℂ) ∈ ball (x : ℂ) ρ ↔ t ∈ Ioo (x - ρ) (x + ρ) := by
  rw [mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_lt_iff,
    mem_Ioo]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

theorem schwarzReflect_of_im_nonneg {z : ℂ} (hz : 0 ≤ z.im) : schwarzReflect φ z = φ z := by
  simp only [schwarzReflect, hz, ↓reduceIte]

/-- **The real boundary values increase strictly** on the diameter. -/
theorem strictMonoOn_re (h : R16.IsRealBoundaryConformal φ x ρ) :
    StrictMonoOn (fun t : ℝ => (φ t).re) (Ioo (x - ρ) (x + ρ)) := by
  have hR := h.differentiableOn_schwarzReflect
  have heq : (fun t : ℝ => (φ t).re) = fun t : ℝ => (schwarzReflect φ t).re := by
    funext t
    rw [schwarzReflect_of_im_nonneg (by simp)]
  rw [heq]
  have hder : ∀ t ∈ Ioo (x - ρ) (x + ρ),
      HasDerivAt (fun s : ℝ => (schwarzReflect φ s).re) (deriv (schwarzReflect φ) t).re t := fun t ht =>
    ((hR.differentiableAt (isOpen_ball.mem_nhds (ofReal_mem_ball_iff.2 ht))).hasDerivAt).real_of_complex
  refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
    fun t ht => ?_
  rw [interior_Ioo] at ht
  rw [(hder t ht).deriv]
  exact (h.deriv_schwarzReflect_pos (ofReal_mem_ball_iff.2 ht)).2

/-- **The open mapping theorem at a real point of the diameter**, read on the closed upper half-plane. -/
theorem exists_ball_image (h : R16.IsRealBoundaryConformal φ x ρ) {y : ℝ} (hy : ((y : ℝ) : ℂ) ∈ ball (x : ℂ) ρ) :
    ∃ ε > 0, ∀ w ∈ ball (φ y) ε, 0 ≤ w.im → ∃ u ∈ ball (x : ℂ) ρ, 0 ≤ u.im ∧ φ u = w ∧
      (0 < w.im → 0 < u.im) ∧ (w.im = 0 → u.im = 0) := by
  have hR := h.differentiableOn_schwarzReflect
  have hA : AnalyticAt ℂ (schwarzReflect φ) (y : ℂ) := hR.analyticAt (isOpen_ball.mem_nhds hy)
  have hy0 : schwarzReflect φ (y : ℂ) = φ y := schwarzReflect_of_im_nonneg (by simp)
  have hnhds : 𝓝 (schwarzReflect φ (y : ℂ)) ≤ map (schwarzReflect φ) (𝓝 (y : ℂ)) := by
    rcases hA.eventually_constant_or_nhds_le_map_nhds with hc | hc
    · exfalso
      obtain ⟨δ, hδ, hδb⟩ := Metric.mem_nhds_iff.1 (hc.and (isOpen_ball.mem_nhds hy))
      set z : ℂ := (y : ℂ) + ((δ / 2 : ℝ) : ℂ) * I with hz
      have hzb : z ∈ ball (y : ℂ) δ := by
        rw [mem_ball, dist_eq_norm, hz, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (half_pos hδ)]
        linarith
      obtain ⟨h1, h2⟩ := hδb hzb
      have hne : z ≠ (y : ℂ) := by
        intro he
        have := congrArg Complex.im he
        simp [hz] at this
        linarith
      exact hne (h.injOn_schwarzReflect h2 hy h1)
    · exact hc
  have hmem : schwarzReflect φ '' ball (x : ℂ) ρ ∈ 𝓝 (schwarzReflect φ (y : ℂ)) :=
    hnhds (image_mem_map (isOpen_ball.mem_nhds hy))
  rw [hy0] at hmem
  obtain ⟨ε, hε, hεb⟩ := Metric.mem_nhds_iff.1 hmem
  refine ⟨ε, hε, fun w hw hw0 => ?_⟩
  obtain ⟨u, hu, rfl⟩ := hεb hw
  obtain ⟨hpos, hzero, hneg⟩ := h.im_schwarzReflect hu
  have hu0 : 0 ≤ u.im := by
    by_contra hlt
    push Not at hlt
    have := hneg hlt
    linarith
  refine ⟨u, hu, hu0, (schwarzReflect_of_im_nonneg hu0).symm, fun hwp => ?_, fun hwz => ?_⟩
  · rcases eq_or_lt_of_le hu0 with he | hlt
    · have := hzero he.symm; linarith
    · exact hlt
  · rcases eq_or_lt_of_le hu0 with he | hlt
    · exact he.symm
    · have := hpos hlt; linarith

end Reflect

/-! ### The branch relation with a transition agreeing on the half-disc -/

section Branch

variable {φf φc Lf Lc g ψ : ℂ → ℂ} {D : Set ℂ} {x ρ : ℝ}

/-- **(BR) for a transition that agrees with `φ_c ∘ g` on the open half-disc** (as
`Aux37Germ.exists_int_tendsto_im_sub_of_transition`). -/
theorem exists_int_tendsto_im_sub_of_transition' (hD : IsOpen D) (hLf : IsDerivLog φf Lf D)
    (hLc : IsDerivLog φc Lc D) (hρ : 0 < ρ) (hg : MapsTo g (H ∩ ball (x : ℂ) ρ) D)
    (hgc : ContinuousOn g (H ∩ ball (x : ℂ) ρ)) (hfg : ∀ w ∈ H ∩ ball (x : ℂ) ρ, φf (g w) = w)
    (hgf : ∀ z ∈ D, φf z ∈ H ∩ ball (x : ℂ) ρ → g (φf z) = z)
    (hψ : R16.IsRealBoundaryConformal ψ x ρ) (hψeq : EqOn ψ (φc ∘ g) (H ∩ ball (x : ℂ) ρ))
    {F : Filter ℂ} (hF : Tendsto φf F (𝓝[H] (x : ℂ))) (hFD : ∀ᶠ z in F, z ∈ D) :
    ∃ k : ℤ, Tendsto (fun z => (Lc z - Lf z).im) F (𝓝 (2 * π * k)) := by
  have hB : IsOpen (H ∩ ball (x : ℂ) ρ) := QuantumZipper.isOpen_H.inter isOpen_ball
  set Φ : ℂ → ℂ := deriv (schwarzReflect ψ) with hΦdef
  have hR := hψ.differentiableOn_schwarzReflect
  have hΦc : ContinuousOn Φ (ball (x : ℂ) ρ) := (hR.deriv isOpen_ball).continuousOn
  have hxb : ((x : ℝ) : ℂ) ∈ ball (x : ℂ) ρ := mem_ball_self hρ
  obtain ⟨hΦim, hΦre⟩ := hψ.deriv_schwarzReflect_pos hxb
  have hdiff : DifferentiableOn ℂ (φc ∘ g) (H ∩ ball (x : ℂ) ρ) := hψ.1.congr fun w hw => (hψeq hw).symm
  have hΦeq : ∀ w ∈ H ∩ ball (x : ℂ) ρ, Φ w = deriv (φc ∘ g) w := by
    intro w hw
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hB.mem_nhds hw] with w' hw'
    rw [schwarzReflect_of_im_nonneg (le_of_lt hw'.1)]
    exact hψeq hw'
  set Λ : ℂ → ℂ := fun w => Lc (g w) - Lf (g w) with hΛdef
  have hΛc : ContinuousOn Λ (ball (x : ℂ) ρ ∩ H) := by
    rw [inter_comm]
    exact (hLc.1.continuousOn.comp hgc hg).sub (hLf.1.continuousOn.comp hgc hg)
  have hexp : ∀ w ∈ ball (x : ℂ) ρ ∩ H, exp (Λ w) = Φ w := by
    intro w hw
    have hw' : w ∈ H ∩ ball (x : ℂ) ρ := ⟨hw.2, hw.1⟩
    rw [hΦeq w hw']
    exact Aux37Germ.exp_sub_eq_deriv_transition hD hLf hLc hB hg hfg hgf hdiff hw'
  obtain ⟨k, hk⟩ := Aux119.exists_int_tendsto_im_of_reflect hρ hΦc hΦre hΦim hΛc hexp
  refine ⟨k, (hk.comp hF).congr' ?_⟩
  have hFB : ∀ᶠ z in F, φf z ∈ H ∩ ball (x : ℂ) ρ := by
    have h1 : ∀ᶠ z in F, φf z ∈ H := hF (self_mem_nhdsWithin)
    have h2 : ∀ᶠ z in F, φf z ∈ ball (x : ℂ) ρ :=
      hF (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hρ))
    exact h1.and h2
  filter_upwards [hFB, hFD] with z hzB hzD
  simp only [Function.comp_apply, hΛdef, hgf z hzD hzB]

end Branch

/-! ### The real Loewner flow keeps positive points positive -/

section Flow

variable {W : ℝ → ℝ}

/-- A solution of the centred flow from a positive real point (driver from `0`) is real and positive. -/
theorem re_pos_of_isForwardSol_real (hW : Continuous W) (hW0 : W 0 = 0) {y T : ℝ} (hy : 0 < y) (hT : 0 ≤ T)
    {u : ℝ → ℂ} (hu : QuantumZipper.IsForwardSol W (y : ℂ) T u) : (u T).im = 0 ∧ 0 < (u T).re := by
  have him : ∀ t ∈ Icc (0 : ℝ) T, (u t).im = 0 := fun t ht => im_eq_zero_of_isForwardSol_real hW hu ht
  refine ⟨him T ⟨hT, le_rfl⟩, ?_⟩
  have hu0 : u 0 = (y : ℂ) := by
    have h := (hu.2 0 ⟨le_rfl, hT⟩).2
    rw [h, hW0, intervalIntegral.integral_same]
    simp
  have hc : ContinuousOn (fun t => (u t).re) (Icc 0 T) := Complex.continuous_re.comp_continuousOn hu.1
  by_contra hle
  push Not at hle
  obtain ⟨t, ht, ht0⟩ := intermediate_value_Icc' hT hc
    (show (0 : ℝ) ∈ Icc (u T).re (u 0).re from ⟨hle, by rw [hu0]; simp [hy.le]⟩)
  exact (hu.2 t ht).1 (Complex.ext (by simpa using ht0) (by simpa using him t ht))

end Flow

end InteractingSLE.Sec7.Aux37Side
