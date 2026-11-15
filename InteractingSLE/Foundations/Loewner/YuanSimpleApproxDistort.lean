import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Thickening
import QuantumZipper.Proofs.Complex.BasicsUnivalent

/-!
# Simple approximations of Loewner traces, II: small vertical shifts barely distort

[Yua22] Lemma `small_distance_perturbation` (`source/external/Yua22/arxiv-latex/TraceTopology.tex`
L545–L576): if `f` is holomorphic and injective on an open set `U` and `A ⊆ U` is compact, then for
every `ε > 0` there is `δ > 0` with

  `(1 − ε) |f(z₁) − f(z₂)| ≤ |f(z₁ + ih) − f(z₂ + ih)|`  for `z₁, z₂ ∈ A`, `0 ≤ h ≤ δ`.

The source proves it for a conformal map of `ℍ` through the Koebe distortion theorem; here only
the continuity and non-vanishing of `f'` on a compact neighbourhood of `A` are used:

* close pairs: `|f(z₂) − f(z₁)| ≥ (m/2) |z₂ − z₁|` with `m = min |f'|`, and the difference of the
  two increments is at most `ω(h) |z₂ − z₁|` by the mean value inequality, `ω` the modulus of
  continuity of `f'`;
* distant pairs: `|f(z₁) − f(z₂)| ≥ μ > 0` by compactness and injectivity, and each point moves by
  at most `ω_f(h)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

namespace InteractingSLE

namespace YuanSimpleApprox

/-- **Small vertical shifts barely distort an injective holomorphic map** ([Yua22] Lemma
`small_distance_perturbation`). -/
theorem exists_le_norm_sub_add_I {f : ℂ → ℂ} {U A : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) (hA : IsCompact A) (hAU : A ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h ∈ Icc (0 : ℝ) δ, ∀ z₁ ∈ A, ∀ z₂ ∈ A,
      (1 - ε) * ‖f z₁ - f z₂‖ ≤ ‖f (z₁ + h * I) - f (z₂ + h * I)‖ := by
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · exact ⟨1, one_pos, fun _ _ z hz => by rw [hAe] at hz; exact absurd hz (notMem_empty z)⟩
  obtain ⟨r₀, hr₀, hr₀U⟩ := hA.exists_cthickening_subset_open hU hAU
  set r := r₀ / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  set K := cthickening r₀ A with hK
  have hKc : IsCompact K := hA.cthickening
  have hKU : K ⊆ U := hr₀U
  -- points within `2r` of `A` lie in `K`
  have hmemK : ∀ z ∈ A, ∀ w : ℂ, dist w z ≤ 2 * r → w ∈ K := fun z hz w hw =>
    mem_cthickening_of_dist_le w z r₀ A hz (by rw [hr] at hw; linarith)
  have hd' : DifferentiableOn ℂ (deriv f) U := hf.deriv hU
  have hcont' : ContinuousOn (deriv f) K := (hd'.continuousOn).mono hKU
  have hcont : ContinuousOn f K := hf.continuousOn.mono hKU
  have hne : ∀ z ∈ K, deriv f z ≠ 0 := fun z hz =>
    QuantumZipper.CA.deriv_ne_zero_of_injOn hU hf hinj (hKU hz)
  -- the minimum `m` of `‖f'‖` on `K`
  have hKne : K.Nonempty := hAne.mono (self_subset_cthickening A)
  obtain ⟨z₀, hz₀K, hz₀min⟩ :=
    hKc.exists_isMinOn hKne (continuous_norm.comp_continuousOn hcont')
  set m := ‖deriv f z₀‖ with hm
  have hm0 : 0 < m := norm_pos_iff.2 (hne z₀ hz₀K)
  have hmle : ∀ z ∈ K, m ≤ ‖deriv f z‖ := fun z hz => hz₀min hz
  -- uniform continuity of `f'` and `f` on `K`
  set η₀ := min (m / 2) (ε * m / 2) with hη₀
  have hη₀0 : 0 < η₀ := lt_min (by linarith) (by positivity)
  obtain ⟨ρ, hρ, hρc⟩ := Metric.uniformContinuousOn_iff.1
    (hKc.uniformContinuousOn_of_continuous hcont') η₀ hη₀0
  set ρ' := min ρ r with hρ'
  have hρ'0 : 0 < ρ' := lt_min hρ hr0
  -- distant pairs: a positive lower bound `μ`
  obtain ⟨μ, hμ, hμle⟩ : ∃ μ > 0, ∀ z₁ ∈ A, ∀ z₂ ∈ A, ρ' ≤ dist z₁ z₂ → μ ≤ ‖f z₁ - f z₂‖ := by
    set P : Set (ℂ × ℂ) := (A ×ˢ A) ∩ {p | ρ' ≤ dist p.1 p.2} with hP
    have hPc : IsCompact P :=
      (hA.prod hA).inter_right (isClosed_le continuous_const (continuous_fst.dist continuous_snd))
    rcases P.eq_empty_or_nonempty with hPe | hPne
    · refine ⟨1, one_pos, fun z₁ hz₁ z₂ hz₂ hd => ?_⟩
      have : (z₁, z₂) ∈ P := ⟨⟨hz₁, hz₂⟩, hd⟩
      rw [hPe] at this; exact absurd this (notMem_empty _)
    have hgc : ContinuousOn (fun p : ℂ × ℂ => ‖f p.1 - f p.2‖) P := by
      have hAK : A ⊆ K := self_subset_cthickening A
      refine continuous_norm.comp_continuousOn (ContinuousOn.sub ?_ ?_)
      · exact (hcont.mono hAK).comp continuousOn_fst fun p hp => hp.1.1
      · exact (hcont.mono hAK).comp continuousOn_snd fun p hp => hp.1.2
    obtain ⟨p₀, hp₀P, hp₀min⟩ := hPc.exists_isMinOn hPne hgc
    refine ⟨‖f p₀.1 - f p₀.2‖, ?_, fun z₁ hz₁ z₂ hz₂ hd =>
      isMinOn_iff.1 hp₀min (z₁, z₂) ⟨⟨hz₁, hz₂⟩, hd⟩⟩
    refine norm_pos_iff.2 (sub_ne_zero.2 fun heq => ?_)
    have h12 := hinj (hAU hp₀P.1.1) (hAU hp₀P.1.2) heq
    have h2 : ρ' ≤ dist p₀.1 p₀.2 := hp₀P.2
    rw [h12, dist_self] at h2
    linarith
  obtain ⟨δ₂, hδ₂, hδ₂c⟩ := Metric.uniformContinuousOn_iff.1
    (hKc.uniformContinuousOn_of_continuous hcont) (ε * μ / 2) (by positivity)
  refine ⟨min r (min (ρ / 2) (δ₂ / 2)), lt_min hr0 (lt_min (by linarith) (by linarith)), ?_⟩
  intro h hh z₁ hz₁ z₂ hz₂
  have hh0 : 0 ≤ h := hh.1
  have hhr : h ≤ r := hh.2.trans (min_le_left _ _)
  have hhρ : h < ρ := lt_of_le_of_lt (hh.2.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (by linarith)
  have hhδ : h < δ₂ := lt_of_le_of_lt (hh.2.trans ((min_le_right _ _).trans (min_le_right _ _)))
    (by linarith)
  have hnormh : ‖(h : ℂ) * I‖ = h := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hh0]
  have hdist_shift : ∀ w : ℂ, dist (w + h * I) w = h := fun w => by
    rw [dist_eq_norm, add_sub_cancel_left, hnormh]
  rcases lt_or_ge (dist z₁ z₂) ρ' with hclose | hfar
  · -- close pairs
    set B := ball z₁ ρ' with hB
    have hBK : ∀ w ∈ B, w ∈ K := fun w hw =>
      hmemK z₁ hz₁ w (by
        have := mem_ball.1 hw
        have : ρ' ≤ r := min_le_right _ _
        linarith)
    have hBK' : ∀ w ∈ B, w + h * I ∈ K := fun w hw =>
      hmemK z₁ hz₁ _ (by
        have h1 := mem_ball.1 hw
        have h2 : ρ' ≤ r := min_le_right _ _
        calc dist (w + h * I) z₁ ≤ dist (w + h * I) w + dist w z₁ := dist_triangle _ _ _
          _ ≤ 2 * r := by rw [hdist_shift]; linarith)
    have hz₂B : z₂ ∈ B := by rw [mem_ball, dist_comm]; exact hclose
    have hz₁B : z₁ ∈ B := mem_ball_self hρ'0
    have hdiffAt : ∀ w ∈ K, DifferentiableAt ℂ f w := fun w hw =>
      hf.differentiableAt (hU.mem_nhds (hKU hw))
    -- lower bound `‖f z₂ − f z₁‖ ≥ (m/2) ‖z₂ − z₁‖`
    have hlow : m / 2 * ‖z₂ - z₁‖ ≤ ‖f z₂ - f z₁‖ := by
      set g : ℂ → ℂ := fun w => f w - deriv f z₁ * w with hg
      have hgd : ∀ w ∈ B, DifferentiableAt ℂ g w := fun w hw =>
        (hdiffAt w (hBK w hw)).sub ((differentiableAt_id.const_mul _))
      have hgb : ∀ w ∈ B, ‖deriv g w‖ ≤ m / 2 := by
        intro w hw
        have hgw : HasDerivAt g (deriv f w - deriv f z₁ * 1) w :=
          (hdiffAt w (hBK w hw)).hasDerivAt.sub ((hasDerivAt_id w).const_mul (deriv f z₁))
        rw [hgw.deriv, mul_one]
        have hdw : dist w z₁ < ρ := lt_of_lt_of_le (mem_ball.1 hw) (min_le_left _ _)
        have := hρc w (hBK w hw) z₁ (hBK z₁ hz₁B) hdw
        rw [dist_eq_norm] at this
        exact this.le.trans (min_le_left _ _)
      have hmv := (convex_ball z₁ ρ').norm_image_sub_le_of_norm_deriv_le hgd hgb hz₁B hz₂B
      have hgg : g z₂ - g z₁ = (f z₂ - f z₁) - deriv f z₁ * (z₂ - z₁) := by
        simp only [hg]; ring
      rw [hgg] at hmv
      have hm1 : m * ‖z₂ - z₁‖ ≤ ‖deriv f z₁ * (z₂ - z₁)‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hmle z₁ (hBK z₁ hz₁B)) (norm_nonneg _)
      have := norm_sub_norm_le (deriv f z₁ * (z₂ - z₁)) (f z₂ - f z₁)
      rw [norm_sub_rev] at hmv
      linarith [norm_sub_rev (deriv f z₁ * (z₂ - z₁)) (f z₂ - f z₁)]
    -- the difference of the two increments
    have hdiff : ‖(f (z₂ + h * I) - f (z₁ + h * I)) - (f z₂ - f z₁)‖ ≤ η₀ * ‖z₂ - z₁‖ := by
      set D : ℂ → ℂ := fun w => f (w + h * I) - f w with hD
      have hDd : ∀ w ∈ B, DifferentiableAt ℂ D w := fun w hw =>
        ((hdiffAt _ (hBK' w hw)).comp w (differentiableAt_id.add_const _)).sub
          (hdiffAt w (hBK w hw))
      have hDb : ∀ w ∈ B, ‖deriv D w‖ ≤ η₀ := by
        intro w hw
        have hderiv : deriv D w = deriv f (w + h * I) - deriv f w := by
          have h1 : HasDerivAt (fun w => f (w + h * I)) (deriv f (w + h * I) * 1) w :=
            (hdiffAt _ (hBK' w hw)).hasDerivAt.comp w ((hasDerivAt_id w).add_const ((h : ℂ) * I))
          rw [mul_one] at h1
          exact (h1.sub (hdiffAt w (hBK w hw)).hasDerivAt).deriv
        rw [hderiv]
        have := hρc (w + h * I) (hBK' w hw) w (hBK w hw) (by rw [hdist_shift]; exact hhρ)
        rw [dist_eq_norm] at this
        exact this.le
      have hmv := (convex_ball z₁ ρ').norm_image_sub_le_of_norm_deriv_le hDd hDb hz₁B hz₂B
      have : D z₂ - D z₁ = (f (z₂ + h * I) - f (z₁ + h * I)) - (f z₂ - f z₁) := by
        simp only [hD]; ring
      rwa [this] at hmv
    -- combine
    have hη₀le : η₀ ≤ ε * m / 2 := min_le_right _ _
    have hkey : η₀ * ‖z₂ - z₁‖ ≤ ε * ‖f z₂ - f z₁‖ := by
      have h1 : η₀ * ‖z₂ - z₁‖ ≤ ε * m / 2 * ‖z₂ - z₁‖ :=
        mul_le_mul_of_nonneg_right hη₀le (norm_nonneg _)
      have h2 : ε * m / 2 * ‖z₂ - z₁‖ = ε * (m / 2 * ‖z₂ - z₁‖) := by ring
      rw [h2] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hlow hε.le)
    have htri : ‖f z₂ - f z₁‖ ≤ ‖f (z₁ + h * I) - f (z₂ + h * I)‖ +
        ‖(f (z₂ + h * I) - f (z₁ + h * I)) - (f z₂ - f z₁)‖ := by
      calc ‖f z₂ - f z₁‖ = ‖(f (z₂ + h * I) - f (z₁ + h * I)) -
            ((f (z₂ + h * I) - f (z₁ + h * I)) - (f z₂ - f z₁))‖ := by congr 1; ring
        _ ≤ ‖f (z₂ + h * I) - f (z₁ + h * I)‖ +
            ‖(f (z₂ + h * I) - f (z₁ + h * I)) - (f z₂ - f z₁)‖ := norm_sub_le _ _
        _ = _ := by rw [norm_sub_rev (f (z₂ + h * I))]
    rw [norm_sub_rev (f z₁) (f z₂)]
    nlinarith [norm_nonneg (f z₂ - f z₁)]
  · -- distant pairs
    have hμ12 := hμle z₁ hz₁ z₂ hz₂ hfar
    have hAK : A ⊆ K := self_subset_cthickening A
    have hmove : ∀ z ∈ A, ‖f (z + h * I) - f z‖ < ε * μ / 2 := fun z hz => by
      have := hδ₂c (z + h * I) (hmemK z hz _ (by rw [hdist_shift]; linarith)) z (hAK hz)
        (by rw [hdist_shift]; exact hhδ)
      rwa [dist_eq_norm] at this
    have h1 := hmove z₁ hz₁
    have h2 := hmove z₂ hz₂
    have hsplit : f z₁ - f z₂ = (f (z₁ + h * I) - f (z₂ + h * I)) - (f (z₁ + h * I) - f z₁) +
        (f (z₂ + h * I) - f z₂) := by ring
    have htri : ‖f z₁ - f z₂‖ ≤ ‖f (z₁ + h * I) - f (z₂ + h * I)‖ + ε * μ := by
      rw [hsplit]
      calc ‖(f (z₁ + h * I) - f (z₂ + h * I)) - (f (z₁ + h * I) - f z₁) +
            (f (z₂ + h * I) - f z₂)‖
          ≤ ‖(f (z₁ + h * I) - f (z₂ + h * I)) - (f (z₁ + h * I) - f z₁)‖ +
            ‖f (z₂ + h * I) - f z₂‖ := norm_add_le _ _
        _ ≤ ‖f (z₁ + h * I) - f (z₂ + h * I)‖ + ‖f (z₁ + h * I) - f z₁‖ +
            ‖f (z₂ + h * I) - f z₂‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ ‖f (z₁ + h * I) - f (z₂ + h * I)‖ + ε * μ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hμ12 hε.le]

end YuanSimpleApprox

end InteractingSLE
