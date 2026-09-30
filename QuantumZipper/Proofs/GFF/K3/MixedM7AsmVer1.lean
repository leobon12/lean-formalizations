import QuantumZipper.Proofs.GFF.K3.MixedM7AsmLip

/-!
# K3-mixed M7-b, part 4: weakly harmonic Hilbert curves are bounded and Lipschitz

For a curve `u : ℂ → E` in a Hilbert space whose even extension is weakly harmonic on `ball t r`
(every `z ↦ ⟪u (foldH z), e⟫` is harmonic there, the hypothesis of `PoissonHarmonicVersionStmt`):

* `exists_norm_le_of_weakHarmonic`: `u` is bounded on `closedBall t ρ₂ ∩ Hbar`, `ρ₂ < r`
  (continuity of each `⟪u ·, e⟫` on a compact set and the uniform boundedness principle,
  `banach_steinhaus`; Rudin, *Functional Analysis*, Thm 2.5);
* `exists_lip_of_weakHarmonic`: `u` is Lipschitz on `closedBall t ρ₁ ∩ Hbar`, `ρ₁ < r`
  (Poisson reproduction of `⟪u ·, e⟫` on a larger half-disc and the Lipschitz bound of the
  Poisson density, `abs_integral_halfDiscPoisson_sub_le`; the interior gradient estimate,
  Axler–Bourdon–Ramey, *Harmonic Function Theory*, 2nd ed., Thm 1.17 and §2).

These give the Kolmogorov moment bound for the Gaussian process of M7-b. Own elementary assembly.
-/

noncomputable section

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem continuousOn_inner_of_weakHarmonic {u : ℂ → E} {t r : ℝ} (e : E)
    (hw : InnerProductSpace.HarmonicOnNhd (fun z => ⟪u (foldH z), e⟫) (ball (t : ℂ) r)) :
    ContinuousOn (fun z => ⟪u (foldH z), e⟫) (ball (t : ℂ) r) := fun z hz =>
  (hw z hz).1.continuousAt.continuousWithinAt

/-- **Uniform bound** (Banach–Steinhaus). -/
theorem exists_norm_le_of_weakHarmonic [CompleteSpace E] {u : ℂ → E} {t r ρ₂ : ℝ}
    (hρ₂r : ρ₂ < r)
    (hw : ∀ e : E, InnerProductSpace.HarmonicOnNhd (fun z => ⟪u (foldH z), e⟫) (ball (t : ℂ) r)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ closedBall (t : ℂ) ρ₂ ∩ Hbar, ‖u x‖ ≤ B := by
  set K := closedBall (t : ℂ) ρ₂ ∩ Hbar with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hKb : K ⊆ ball (t : ℂ) r := fun x hx => closedBall_subset_ball hρ₂r hx.1
  have hfold : ∀ x ∈ K, foldH x = x := fun x hx => CircleFubini.foldH_of_mem' hx.2
  have hpt : ∀ e : E, ∃ C, ∀ i : K, ‖innerSL ℝ (u i.1) e‖ ≤ C := by
    intro e
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn
      ((continuousOn_inner_of_weakHarmonic e (hw e)).mono hKb)
    refine ⟨C, fun i => ?_⟩
    have := hC i.1 i.2
    rwa [hfold i.1 i.2] at this
  obtain ⟨C', hC'⟩ := banach_steinhaus hpt
  refine ⟨max C' 0, le_max_right _ _, fun x hx => ?_⟩
  have := hC' ⟨x, hx⟩
  rw [innerSL_apply_norm] at this
  exact this.trans (le_max_left _ _)

/-- **Lipschitz bound** for a weakly harmonic curve. -/
theorem exists_lip_of_weakHarmonic [CompleteSpace E] {u : ℂ → E} {t r ρ₁ : ℝ} (hρ₁ : 0 < ρ₁)
    (hρ₁r : ρ₁ < r)
    (hw : ∀ e : E, InnerProductSpace.HarmonicOnNhd (fun z => ⟪u (foldH z), e⟫) (ball (t : ℂ) r)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ z ∈ closedBall (t : ℂ) ρ₁ ∩ Hbar, ∀ w ∈ closedBall (t : ℂ) ρ₁ ∩ Hbar,
      ‖u z - u w‖ ≤ L * ‖z - w‖ := by
  set s : ℝ := (ρ₁ + r) / 2 with hs
  have hρ₁s : ρ₁ < s := by linarith
  have hsr : s < r := by linarith
  have hs0 : 0 < s := by linarith
  obtain ⟨B, hB0, hB⟩ := exists_norm_le_of_weakHarmonic hsr hw
  have hL0 : 0 ≤ poisLk s ρ₁ * B := mul_nonneg (poisLk_nonneg hρ₁.le hρ₁s) hB0
  refine ⟨poisLk s ρ₁ * B, hL0, fun z hz w hw' => ?_⟩
  -- the scalar estimate for a fixed direction `e`
  have key : ∀ e : E, ⟪u z - u w, e⟫ ≤ poisLk s ρ₁ * B * ‖e‖ * ‖z - w‖ := by
    intro e
    set f : ℂ → ℝ := fun y => ⟪u (foldH y), e⟫ with hf
    have hfc : ContinuousOn f (ball (t : ℂ) r) := continuousOn_inner_of_weakHarmonic e (hw e)
    set g : ℂ → ℝ := fun y => f (retr t s y) with hg
    have hgc : Continuous g := hfc.comp_continuous (continuous_retr_m7b t hs0) fun y =>
      closedBall_subset_ball hsr (mem_closedBall_iff_norm.2 (norm_retr_sub_le hs0 y))
    have hharm : InnerProductSpace.HarmonicOnNhd f (closedBall (t : ℂ) s) := fun x hx =>
      hw e x (closedBall_subset_ball hsr hx)
    have hev : ∀ x ∈ sphere (t : ℂ) s, f (conj x) = f x := fun x _ => by
      simp only [hf, foldH_conj_k3]
    have hrep : ∀ y ∈ closedBall (t : ℂ) ρ₁ ∩ Hbar,
        ⟪u y, e⟫ = ∫ x, g x ∂halfDiscPoisson t s y := by
      intro y hy
      have hy1 := mem_closedBall_iff_norm.1 hy.1
      have hyb : y ∈ ball (t : ℂ) s := mem_ball_iff_norm.2 (by linarith)
      have h1 := integral_halfDiscPoisson_of_harmonic hs0 hyb hharm hev
      have h2 : ∫ x, g x ∂halfDiscPoisson t s y = ∫ x, f x ∂halfDiscPoisson t s y := by
        refine integral_congr_ae ?_
        filter_upwards [ae_halfDiscPoisson_mem hs0 y] with x hx
        simp only [hg]
        rw [retr_eq_self hx.2 (mem_sphere_iff_norm.1 hx.1).le]
      rw [h2, h1, hf]
      simp only [CircleFubini.foldH_of_mem' hy.2]
    have hM : ∀ x ∈ sphere (t : ℂ) s, |g (foldH x)| ≤ B * ‖e‖ := by
      intro x _
      set y := retr t s (foldH x) with hy
      have hyH : y ∈ Hbar := retr_mem_Hbar hs0 _
      have hyK : y ∈ closedBall (t : ℂ) s ∩ Hbar :=
        ⟨mem_closedBall_iff_norm.2 (norm_retr_sub_le hs0 _), hyH⟩
      simp only [hg, hf, ← hy, CircleFubini.foldH_of_mem' hyH]
      calc |⟪u y, e⟫| ≤ ‖u y‖ * ‖e‖ := abs_real_inner_le_norm _ _
        _ ≤ B * ‖e‖ := mul_le_mul_of_nonneg_right (hB y hyK) (norm_nonneg _)
    have hd := abs_integral_halfDiscPoisson_sub_le hρ₁.le hρ₁s hgc hM
      (mem_closedBall_iff_norm.1 hz.1) (mem_closedBall_iff_norm.1 hw'.1)
    rw [inner_sub_left, hrep z hz, hrep w hw']
    calc _ ≤ |∫ x, g x ∂halfDiscPoisson t s z - ∫ x, g x ∂halfDiscPoisson t s w| := le_abs_self _
      _ ≤ poisLk s ρ₁ * (B * ‖e‖) * ‖z - w‖ := hd
      _ = _ := by ring
  have h := key (u z - u w)
  rw [real_inner_self_eq_norm_sq] at h
  rcases (norm_nonneg (u z - u w)).lt_or_eq with hp | h0
  · nlinarith [norm_nonneg (z - w)]
  · rw [← h0]; positivity

end QuantumZipper.K3
