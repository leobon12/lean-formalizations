import QuantumZipper.Proofs.Thm18.G1ProfileParts
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.DiscreteSubset
import QuantumZipper.Proofs.Complex.KernelChordRight

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-PROFILE: the gap part (`G1ProfileGapStmt`)

For a map `ψ` holomorphic on `ℍ` (here the inverse of a normalized uniformizer of a side
component), the pushed folded circle `ψ_* fc(d, r)` does not charge the circle `{‖w‖ = 2^{-k}}`
for all large `k`.

Own elementary argument (no published source; standard identity-theorem reasoning). The folded
circle is the image of the uniform angle on `[0, 2π)`. Up to the (null) angles where the circle
meets `ℝ`, the angle lies — after a shift by `± 2π` — in one of two order-connected sets
`J₁ ⊆ [-π/2, 3π/2]` (the circle is in `ℍ`) and `J₂ ⊆ [π/2, 5π/2]` (the circle is in the lower
half-plane and is folded by conjugation); order-connectedness is the unimodality of `sin` on
these windows. On `Jᵢ` the function `gᵢ θ = ‖ψ(point)‖²` is real-analytic, so by the identity
theorem each level set `{gᵢ = ρ²}` is either countable (null) or all of `Jᵢ`; the latter can
happen for at most one `ρ > 0`, hence for at most one `k` per piece.
-/

noncomputable section

open MeasureTheory Filter Set Function Real
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

/-- A subset of `ℝ` none of whose points is an accumulation point of it is countable. -/
theorem countable_of_forall_not_accPt {S : Set ℝ} (h : ∀ x ∈ S, ¬AccPt x (𝓟 S)) :
    S.Countable := by
  have : DiscreteTopology S := discreteTopology_subtype_iff.2 fun x hx => not_neBot.1 (h x hx)
  exact Set.countable_coe_iff.1 (TopologicalSpace.separableSpace_iff_countable.1 inferInstance)

/-- **Level sets of a real-analytic function** on a preconnected set: null, or everything. -/
theorem volume_level_eq_zero_or_eqOn {g : ℝ → ℝ} {J : Set ℝ} (hg : AnalyticOnNhd ℝ g J)
    (hJ : IsPreconnected J) (c : ℝ) :
    volume {θ | θ ∈ J ∧ g θ = c} = 0 ∨ (J.Nonempty ∧ EqOn g (fun _ => c) J) := by
  by_cases h : ∀ x ∈ {θ | θ ∈ J ∧ g θ = c}, ¬AccPt x (𝓟 {θ | θ ∈ J ∧ g θ = c})
  · exact Or.inl ((countable_of_forall_not_accPt h).measure_zero volume)
  · push Not at h
    obtain ⟨x, ⟨hxJ, -⟩, hx⟩ := h
    refine Or.inr ⟨⟨x, hxJ⟩, hg.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const hJ hxJ ?_⟩
    exact (accPt_iff_frequently_nhdsNE.1 hx).mono fun θ hθ => hθ.2

theorem radius_ne_of_lt {k₁ k₂ : ℕ} (h : k₁ < k₂) : radius k₁ ≠ radius k₂ := by
  unfold radius
  exact (pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) h).ne'

/-- For a real-analytic `g` on a preconnected `J`, the level sets `{g = (2^{-k})²}` are null for
all large `k`. -/
theorem eventually_volume_level_radius {g : ℝ → ℝ} {J : Set ℝ} (hg : AnalyticOnNhd ℝ g J)
    (hJ : IsPreconnected J) :
    ∀ᶠ k : ℕ in atTop, volume {θ | θ ∈ J ∧ g θ = radius k ^ 2} = 0 := by
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨k₁, -, h₁⟩ := Filter.frequently_atTop.1 hcon 0
  obtain ⟨k₂, hk₂, h₂⟩ := Filter.frequently_atTop.1 hcon (k₁ + 1)
  obtain ⟨⟨x, hx⟩, e₁⟩ := (volume_level_eq_zero_or_eqOn hg hJ _).resolve_left h₁
  obtain ⟨-, e₂⟩ := (volume_level_eq_zero_or_eqOn hg hJ _).resolve_left h₂
  have h12 : radius k₁ ^ 2 = radius k₂ ^ 2 := (e₁ hx).symm.trans (e₂ hx)
  exact radius_ne_of_lt (show k₁ < k₂ by omega)
    ((sq_eq_sq₀ (radius_pos k₁).le (radius_pos k₂).le).1 h12)

theorem circleMap_im' (d : ℂ) (r θ : ℝ) : (circleMap d r θ).im = d.im + r * Real.sin θ := by
  rw [circleMap, Complex.add_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-- `sin` is quasi-concave on `[-π/2, 3π/2]`. -/
theorem sin_ge_min_upper {x y z : ℝ} (hx : -(π / 2) ≤ x) (hy : y ≤ 3 * π / 2) (hxz : x ≤ z)
    (hzy : z ≤ y) : min (Real.sin x) (Real.sin y) ≤ Real.sin z := by
  rcases le_total z (π / 2) with h | h
  · exact (min_le_left _ _).trans (Real.sin_le_sin_of_le_of_le_pi_div_two hx h hxz)
  · refine (min_le_right _ _).trans ?_
    rw [← Real.sin_pi_sub y, ← Real.sin_pi_sub z]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

/-- `sin` is quasi-convex on `[π/2, 5π/2]`. -/
theorem sin_le_max_lower {x y z : ℝ} (hx : π / 2 ≤ x) (hy : y ≤ 5 * π / 2) (hxz : x ≤ z)
    (hzy : z ≤ y) : Real.sin z ≤ max (Real.sin x) (Real.sin y) := by
  rcases le_total z (3 * π / 2) with h | h
  · refine le_trans ?_ (le_max_left _ _)
    rw [← Real.sin_pi_sub x, ← Real.sin_pi_sub z]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  · refine le_trans ?_ (le_max_right _ _)
    rw [← Real.sin_sub_two_pi z, ← Real.sin_sub_two_pi y]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

/-- The upper piece: angles in `[-π/2, 3π/2]` whose circle point lies in `ℍ`. -/
def gapJ₁ (d : ℂ) (r : ℝ) : Set ℝ :=
  {θ | θ ∈ Icc (-(π / 2)) (3 * π / 2) ∧ 0 < (circleMap d r θ).im}

/-- The lower piece: angles in `[π/2, 5π/2]` whose circle point lies below `ℝ`. -/
def gapJ₂ (d : ℂ) (r : ℝ) : Set ℝ :=
  {θ | θ ∈ Icc (π / 2) (5 * π / 2) ∧ (circleMap d r θ).im < 0}

theorem ordConnected_gapJ₁ (d : ℂ) {r : ℝ} (hr : 0 < r) : (gapJ₁ d r).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ⟨⟨hx.1.1.trans hz.1, hz.2.trans hy.1.2⟩, ?_⟩⟩
  have hx2 := hx.2; have hy2 := hy.2
  rw [circleMap_im'] at hx2 hy2 ⊢
  have hm := sin_ge_min_upper hx.1.1 hy.1.2 hz.1 hz.2
  rcases min_choice (Real.sin x) (Real.sin y) with h | h <;> rw [h] at hm <;> nlinarith

theorem ordConnected_gapJ₂ (d : ℂ) {r : ℝ} (hr : 0 < r) : (gapJ₂ d r).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ⟨⟨hx.1.1.trans hz.1, hz.2.trans hy.1.2⟩, ?_⟩⟩
  have hx2 := hx.2; have hy2 := hy.2
  rw [circleMap_im'] at hx2 hy2 ⊢
  have hm := sin_le_max_lower hx.1.1 hy.1.2 hz.1 hz.2
  rcases max_choice (Real.sin x) (Real.sin y) with h | h <;> rw [h] at hm <;> nlinarith

/-- `θ ↦ ‖F θ‖²` written with real and imaginary parts, real-analytic when `F` is. -/
theorem analyticAt_normSq_comp {F : ℝ → ℂ} {θ : ℝ} (hF : AnalyticAt ℝ F θ) :
    AnalyticAt ℝ (fun t => (F t).re * (F t).re + (F t).im * (F t).im) θ := by
  have hre : AnalyticAt ℝ (fun t => (F t).re) θ := by
    have := (Complex.reCLM.analyticAt (F θ)).comp hF
    simpa [Function.comp_def] using this
  have him : AnalyticAt ℝ (fun t => (F t).im) θ := by
    have := (Complex.imCLM.analyticAt (F θ)).comp hF
    simpa [Function.comp_def] using this
  exact (hre.mul hre).add (him.mul him)

theorem re_sq_add_im_sq_of_norm_eq {w : ℂ} {ρ : ℝ} (h : ‖w‖ = ρ) :
    w.re * w.re + w.im * w.im = ρ ^ 2 := by
  rw [← h, Complex.sq_norm, Complex.normSq_apply]

/-- **Gap lemma.** For `ψ` measurable and holomorphic on `ℍ`, and any folded circle of positive
radius, the pushed circle does not charge `{‖w‖ = 2^{-k}}` for all large `k`. -/
theorem eventually_ae_norm_ne_radius {ψ : ℂ → ℂ} (hψm : Measurable ψ)
    (hψ : DifferentiableOn ℂ ψ H) (d : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ k : ℕ in atTop, ∀ᵐ w ∂((foldedCircle d r).map ψ), ‖w‖ ≠ radius k := by
  have hψA : AnalyticOnNhd ℂ ψ H := hψ.analyticOnNhd isOpen_H
  set g₁ : ℝ → ℝ := fun θ => (ψ (circleMap d r θ)).re * (ψ (circleMap d r θ)).re +
    (ψ (circleMap d r θ)).im * (ψ (circleMap d r θ)).im
  set g₂ : ℝ → ℝ := fun θ => (ψ ((starRingEnd ℂ) (circleMap d r θ))).re *
      (ψ ((starRingEnd ℂ) (circleMap d r θ))).re +
    (ψ ((starRingEnd ℂ) (circleMap d r θ))).im * (ψ ((starRingEnd ℂ) (circleMap d r θ))).im
  have hA₁ : AnalyticOnNhd ℝ g₁ (gapJ₁ d r) := fun θ hθ =>
    analyticAt_normSq_comp (F := fun t => ψ (circleMap d r t))
      (AnalyticAt.comp (f := circleMap d r) (x := θ) ((hψA _ hθ.2).restrictScalars (𝕜 := ℝ))
        (analyticOnNhd_circleMap d r θ (mem_univ θ)))
  have hA₂ : AnalyticOnNhd ℝ g₂ (gapJ₂ d r) := fun θ hθ => by
    have hH : (starRingEnd ℂ) (circleMap d r θ) ∈ H := by
      show 0 < ((starRingEnd ℂ) (circleMap d r θ)).im
      rw [Complex.conj_im]; linarith [hθ.2]
    have hc : AnalyticAt ℝ (fun t => (starRingEnd ℂ) (circleMap d r t)) θ := by
      have := ((Complex.conjCLE : ℂ →L[ℝ] ℂ).analyticAt (circleMap d r θ)).comp
        (analyticOnNhd_circleMap d r θ (mem_univ θ))
      simpa [Function.comp_def] using this
    exact analyticAt_normSq_comp (F := fun t => ψ ((starRingEnd ℂ) (circleMap d r t)))
      (AnalyticAt.comp (f := fun t => (starRingEnd ℂ) (circleMap d r t)) (x := θ)
        ((hψA _ hH).restrictScalars (𝕜 := ℝ)) hc)
  -- the angles where the circle meets `ℝ` are null
  have hZ : volume {θ : ℝ | (circleMap d r θ).im = 0} = 0 := by
    have hAi : AnalyticOnNhd ℝ (fun θ => (circleMap d r θ).im) univ := fun θ _ => by
      have := (Complex.imCLM.analyticAt (circleMap d r θ)).comp
        (analyticOnNhd_circleMap d r θ (mem_univ θ))
      simpa [Function.comp_def] using this
    rcases volume_level_eq_zero_or_eqOn hAi isPreconnected_univ 0 with h | ⟨-, h⟩
    · simpa using h
    · have h0 := h (mem_univ 0)
      have h1 := h (mem_univ (π / 2))
      simp only [circleMap_im', Real.sin_zero, Real.sin_pi_div_two] at h0 h1
      linarith
  filter_upwards [eventually_volume_level_radius hA₁ (ordConnected_gapJ₁ d hr).isPreconnected,
    eventually_volume_level_radius hA₂ (ordConnected_gapJ₂ d hr).isPreconnected] with k h1 h2
  set L₁ := {θ | θ ∈ gapJ₁ d r ∧ g₁ θ = radius k ^ 2}
  set L₂ := {θ | θ ∈ gapJ₂ d r ∧ g₂ θ = radius k ^ 2}
  have hmeas : MeasurableSet {w : ℂ | ‖w‖ ≠ radius k} :=
    (measurableSet_eq_fun measurable_norm measurable_const).compl
  refine (ae_map_iff hψm.aemeasurable hmeas).2 ?_
  rw [foldedCircle]
  refine (ae_map_iff (p := fun z => ‖ψ z‖ ≠ radius k) measurable_foldH.aemeasurable
    (hψm hmeas)).2 ?_
  rw [circleUnif]
  refine Measure.ae_smul_measure ?_ _
  refine (ae_map_iff (p := fun ζ => ‖ψ (foldH ζ)‖ ≠ radius k)
    (continuous_circleMap d r).measurable.aemeasurable ((hψm.comp measurable_foldH) hmeas)).2 ?_
  rw [ae_restrict_iff' measurableSet_Ico, ae_iff]
  refine measure_mono_null (t := {θ : ℝ | (circleMap d r θ).im = 0} ∪ L₁ ∪
    ((fun θ => θ + -(2 * π)) ⁻¹' L₁) ∪ L₂ ∪ ((fun θ => θ + 2 * π) ⁻¹' L₂)) ?_ ?_
  · intro θ hθ
    simp only [Set.mem_ofPred_eq, not_imp, not_not] at hθ
    obtain ⟨⟨h0, h2π⟩, heq⟩ := hθ
    have hper : ∀ t, circleMap d r (t + 2 * π) = circleMap d r t := periodic_circleMap d r
    have hper' : circleMap d r (θ + -(2 * π)) = circleMap d r θ := by
      rw [← hper (θ + -(2 * π))]; ring_nf
    rcases lt_trichotomy (circleMap d r θ).im 0 with hneg | hzero | hpos
    · have hf : foldH (circleMap d r θ) = (starRingEnd ℂ) (circleMap d r θ) := by
        simp [foldH, not_le.2 hneg]
      have hg : g₂ θ = radius k ^ 2 := by
        simp only [g₂]; rw [← hf]; exact re_sq_add_im_sq_of_norm_eq heq
      rcases le_or_gt (π / 2) θ with hθ | hθ
      · exact Or.inl (Or.inr ⟨⟨⟨hθ, by linarith [Real.pi_pos]⟩, hneg⟩, hg⟩)
      · refine Or.inr ⟨⟨⟨by linarith, by linarith⟩, ?_⟩, ?_⟩
        · show (circleMap d r (θ + 2 * π)).im < 0
          rw [hper]; exact hneg
        · show g₂ (θ + 2 * π) = _
          simp only [g₂, hper]; exact hg
    · exact Or.inl (Or.inl (Or.inl (Or.inl hzero)))
    · have hf : foldH (circleMap d r θ) = circleMap d r θ := by
        simp [foldH, hpos.le]
      have hg : g₁ θ = radius k ^ 2 := by
        simp only [g₁]; rw [← hf]; exact re_sq_add_im_sq_of_norm_eq heq
      rcases le_or_gt θ (3 * π / 2) with hθ | hθ
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨⟨by linarith [Real.pi_pos], hθ⟩, hpos⟩, hg⟩)))
      · refine Or.inl (Or.inl (Or.inr ⟨⟨⟨by linarith, by linarith⟩, ?_⟩, ?_⟩))
        · show 0 < (circleMap d r (θ + -(2 * π))).im
          rw [hper']; exact hpos
        · show g₁ (θ + -(2 * π)) = _
          simp only [g₁, hper']; exact hg
  · refine measure_union_null (measure_union_null (measure_union_null
      (measure_union_null hZ h1) ?_) h2) ?_
    · rw [measure_preimage_add_right]; exact h1
    · rw [measure_preimage_add_right]; exact h2

/-- **`G1ProfileGapStmt` holds.** The selected map `Ψ left a` is, on a continuous simple-chord
path, the inverse of a normalized uniformizer of the (open) side component, hence holomorphic on
`ℍ` (`G1Rescale.invFunOn_props`); apply `eventually_ae_norm_ne_radius`. -/
theorem g1ProfileGapStmt : G1ProfileGapStmt := by
  intro γ _ _ Ω _ P _ B _ Ω' _ P' _ X A _ _ _ Ψ hΨ a hc hs left G _ d _ r hr
  obtain ⟨φ, hφ, hΨa⟩ := hΨ.2.2 a hc hs left
  have hopen : IsOpen (sideDom (pathTrace (γ ^ 2) a) left) := by
    cases left
    · exact CA.Kernel.isOpen_rightComponent_qz hs
    · exact CA.Uniformizer.isOpen_leftComponent hs
  have hψm : Measurable (Ψ left a) :=
    (hΨ.1 left).comp (measurable_const.prodMk measurable_id)
  have hd : DifferentiableOn ℂ (Ψ left a) H := by
    rw [hΨa]; exact (G1.invFunOn_props hopen hφ).1
  exact eventually_ae_norm_ne_radius hψm hd d hr

end G1RC
end Thm18Asm
end QuantumZipper
