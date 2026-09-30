import QuantumZipper.Proofs.GFF.K3.MixedM7AsmPois
import QuantumZipper.Proofs.GFF.K3.MixedM7D8

/-!
# K3-mixed M7-b, part 3: the mixed Poisson vectors are Lipschitz

`exists_lip_rieszVec_halfDiscPoisson`: for the mixed space `V = mixedSpace D (realSet (Icc c d))`
and a half-disc `ball t r ∩ H ⊆ D` on the free arc, `0 < ρ₁ < r`, the curve
`z ↦ v_{P_z} = rieszVec D V (halfDiscPoisson t r z)` is Lipschitz on `closedBall t ρ₁ ∩ Hbar`.
This is the moment bound needed for Kolmogorov's criterion for the harmonic part `Ξ(v_{P_z})` of
the mixed field (M7).

Proof (own elementary argument, the classical interior gradient estimate for harmonic functions
via the Poisson kernel, cf. Axler–Bourdon–Ramey, *Harmonic Function Theory*, 2nd ed., §1 and
Thm 1.17):

* the half-disc Poisson density `(s² − |z − t|²)/|x − z|²` is Lipschitz in `z ∈ closedBall t ρ`
  uniformly in `x ∈ sphere t s`, `ρ < s` (`abs_poissonDensity_sub_le`), so
  `|∫ h dP^s_z − ∫ h dP^s_w| ≤ Lk · sup_{sphere} |h ∘ foldH| · |z − w|`;
* for `f ∈ V`, `u = poisSm t r ρ₂ f` is harmonic and even on `ball t ρ₂` (`MixedM7AsmPois`) and
  equals `z ↦ ∫ f dP^r_z` on `closedBall t ρ₂ ∩ Hbar`; Poisson reproduction at a radius
  `s ∈ (ρ₁, ρ₂)` and the uniform trace bound `(∫ f dP^r_y)² ≤ C E(f)` (M7-a1,
  `mixedPoissonBound_holds`) give `|∫ f d(P_z − P_w)| ≤ Lk √(C E(f)) |z − w|`;
* a vector of the gradient closure whose pairings with all `∇f` are bounded by `M ‖∇f‖` has norm
  `≤ M` (`norm_le_of_pairing_le`, as in `dualNormSq_eq_of_pairing`).
-/

noncomputable section

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

/-- The Lipschitz constant of the half-disc Poisson density. -/
def poisLk (s ρ : ℝ) : ℝ := 2 * ρ / (s - ρ) ^ 2 + 4 * s ^ 3 / (s - ρ) ^ 4

theorem poisLk_nonneg {s ρ : ℝ} (hρ : 0 ≤ ρ) (hρs : ρ < s) : 0 ≤ poisLk s ρ := by
  have hs : 0 < s := lt_of_le_of_lt hρ hρs
  unfold poisLk; positivity

/-- **Lipschitz bound for the Poisson density.** -/
theorem abs_poissonDensity_sub_le {t s ρ : ℝ} (hρ : 0 ≤ ρ) (hρs : ρ < s) {z w x : ℂ}
    (hz : ‖z - t‖ ≤ ρ) (hw : ‖w - t‖ ≤ ρ) (hx : ‖x - t‖ = s) :
    |(s ^ 2 - ‖z - t‖ ^ 2) / ‖x - z‖ ^ 2 - (s ^ 2 - ‖w - t‖ ^ 2) / ‖x - w‖ ^ 2| ≤
      poisLk s ρ * ‖z - w‖ := by
  set A := ‖x - z‖ with hAdef
  set B := ‖x - w‖ with hBdef
  set d := s - ρ with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  have hs0 : 0 < s := by linarith
  have tri : ∀ y : ℂ, ‖x - t‖ ≤ ‖x - y‖ + ‖y - t‖ := fun y => by
    calc ‖x - t‖ = ‖(x - y) + (y - t)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  have tri' : ∀ y : ℂ, ‖x - y‖ ≤ ‖x - t‖ + ‖y - t‖ := fun y => by
    calc ‖x - y‖ = ‖(x - t) - (y - t)‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  have hA : d ≤ A := by have := tri z; rw [hd]; linarith
  have hB : d ≤ B := by have := tri w; rw [hd]; linarith
  have hA2 : A ≤ 2 * s := by have := tri' z; linarith
  have hB2 : B ≤ 2 * s := by have := tri' w; linarith
  have hA0 : 0 < A := hd0.trans_le hA
  have hB0 : 0 < B := hd0.trans_le hB
  have hAB : |A - B| ≤ ‖z - w‖ := by
    have := abs_norm_sub_norm_le (x - z) (x - w)
    rwa [show x - z - (x - w) = w - z by ring, norm_sub_rev w z] at this
  have hzw : |‖z - t‖ - ‖w - t‖| ≤ ‖z - w‖ := by
    have := abs_norm_sub_norm_le (z - t) (w - t)
    rwa [sub_sub_sub_cancel_right] at this
  set a := s ^ 2 - ‖z - t‖ ^ 2 with ha
  set b := s ^ 2 - ‖w - t‖ ^ 2 with hb
  have hb0 : 0 ≤ b := by rw [hb]; nlinarith [norm_nonneg (w - t)]
  have hbs : b ≤ s ^ 2 := by rw [hb]; nlinarith [norm_nonneg (w - t)]
  have hab : |a - b| ≤ 2 * ρ * ‖z - w‖ := by
    have e : a - b = (‖w - t‖ - ‖z - t‖) * (‖w - t‖ + ‖z - t‖) := by rw [ha, hb]; ring
    rw [e, abs_mul, abs_sub_comm]
    have h2 : |‖w - t‖ + ‖z - t‖| ≤ 2 * ρ := by
      rw [abs_of_nonneg (by positivity)]; linarith
    calc |‖z - t‖ - ‖w - t‖| * |‖w - t‖ + ‖z - t‖| ≤ ‖z - w‖ * (2 * ρ) :=
          mul_le_mul hzw h2 (abs_nonneg _) (norm_nonneg _)
      _ = 2 * ρ * ‖z - w‖ := by ring
  have hB2A2 : |B ^ 2 - A ^ 2| ≤ 4 * s * ‖z - w‖ := by
    have e : B ^ 2 - A ^ 2 = (B - A) * (B + A) := by ring
    rw [e, abs_mul, abs_sub_comm, abs_of_pos (by positivity : 0 < B + A)]
    calc |A - B| * (B + A) ≤ ‖z - w‖ * (4 * s) :=
          mul_le_mul hAB (by linarith) (by positivity) (norm_nonneg _)
      _ = 4 * s * ‖z - w‖ := by ring
  have e : a / A ^ 2 - b / B ^ 2 = (a - b) / A ^ 2 + b * (B ^ 2 - A ^ 2) / (A ^ 2 * B ^ 2) := by
    field_simp; ring
  have hd2 : d ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hd0.le hA 2
  have hd4 : d ^ 4 ≤ A ^ 2 * B ^ 2 := by
    have := mul_le_mul hd2 (pow_le_pow_left₀ hd0.le hB 2) (by positivity) (by positivity)
    nlinarith
  have t1 : |(a - b) / A ^ 2| ≤ 2 * ρ / d ^ 2 * ‖z - w‖ := by
    rw [abs_div, abs_of_pos (by positivity : 0 < A ^ 2), div_mul_eq_mul_div, div_le_div_iff₀
      (by positivity) (by positivity)]
    calc |a - b| * d ^ 2 ≤ 2 * ρ * ‖z - w‖ * A ^ 2 :=
          mul_le_mul hab hd2 (by positivity) (by positivity)
      _ = _ := by ring
  have t2 : |b * (B ^ 2 - A ^ 2) / (A ^ 2 * B ^ 2)| ≤ 4 * s ^ 3 / d ^ 4 * ‖z - w‖ := by
    rw [abs_div, abs_mul, abs_of_nonneg hb0, abs_of_pos (by positivity : 0 < A ^ 2 * B ^ 2),
      div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    calc b * |B ^ 2 - A ^ 2| * d ^ 4 ≤ s ^ 2 * (4 * s * ‖z - w‖) * (A ^ 2 * B ^ 2) :=
          mul_le_mul (mul_le_mul hbs hB2A2 (abs_nonneg _) (by positivity)) hd4
            (by positivity) (by positivity)
      _ = _ := by ring
  rw [e, poisLk, add_mul]
  exact (abs_add_le _ _).trans (add_le_add t1 t2)

/-- **Lipschitz bound for Poisson integrals.** -/
theorem abs_integral_halfDiscPoisson_sub_le {t s ρ : ℝ} (hρ : 0 ≤ ρ) (hρs : ρ < s)
    {h : ℂ → ℝ} (hh : Continuous h) {M : ℝ} (hM : ∀ x ∈ sphere (t : ℂ) s, |h (foldH x)| ≤ M)
    {z w : ℂ} (hz : ‖z - t‖ ≤ ρ) (hw : ‖w - t‖ ≤ ρ) :
    |∫ x, h x ∂halfDiscPoisson t s z - ∫ x, h x ∂halfDiscPoisson t s w| ≤
      poisLk s ρ * M * ‖z - w‖ := by
  have hs : 0 < s := lt_of_le_of_lt hρ hρs
  have hzb : z ∈ ball (t : ℂ) s := mem_ball_iff_norm.2 (by linarith)
  have hwb : w ∈ ball (t : ℂ) s := mem_ball_iff_norm.2 (by linarith)
  have hsph := ae_mem_sphere_circleUnif_k3 (t : ℂ) hs
  set k : ℂ → ℂ → ℝ := fun y x => (s ^ 2 - ‖y - t‖ ^ 2) / ‖x - y‖ ^ 2 with hk
  have hkm : ∀ y, Measurable (k y) := fun y => by
    simp only [hk]
    exact measurable_const.div ((measurable_id.sub measurable_const).norm.pow_const 2)
  have hkb : ∀ y : ℂ, ‖y - t‖ ≤ ρ → ∀ x ∈ sphere (t : ℂ) s, |k y x| ≤ s ^ 2 / (s - ρ) ^ 2 := by
    intro y hy x hx
    have hxt : ‖x - t‖ = s := mem_sphere_iff_norm.1 hx
    have h1 := halfDiscPoisson_density_le hρs hy hxt
    have h0 : 0 ≤ k y x := div_nonneg (by nlinarith [norm_nonneg (y - t)]) (sq_nonneg _)
    rw [abs_of_nonneg h0]; exact h1
  have hM0 : ∀ x ∈ sphere (t : ℂ) s, 0 ≤ M := fun x hx => (abs_nonneg _).trans (hM x hx)
  have hint : ∀ y : ℂ, ‖y - t‖ ≤ ρ →
      Integrable (fun x => k y x * h (foldH x)) (circleUnif (t : ℂ) s) := by
    intro y hy
    refine Integrable.of_bound ((hkm y).mul (hh.measurable.comp measurable_foldH)).aestronglyMeasurable
      (s ^ 2 / (s - ρ) ^ 2 * M) ?_
    filter_upwards [hsph] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hkb y hy x hx) (hM x hx) (abs_nonneg _) (by positivity)
  rw [integral_halfDiscPoisson_eq_circle' hzb hh.aestronglyMeasurable,
    integral_halfDiscPoisson_eq_circle' hwb hh.aestronglyMeasurable,
    ← integral_sub (hint z hz) (hint w hw)]
  have hb : ∀ᵐ x ∂circleUnif (t : ℂ) s,
      ‖k z x * h (foldH x) - k w x * h (foldH x)‖ ≤ poisLk s ρ * M * ‖z - w‖ := by
    filter_upwards [hsph] with x hx
    rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
    have h1 := abs_poissonDensity_sub_le hρ hρs hz hw (mem_sphere_iff_norm.1 hx)
    calc |k z x - k w x| * |h (foldH x)| ≤ (poisLk s ρ * ‖z - w‖) * M :=
          mul_le_mul h1 (hM x hx) (abs_nonneg _) (by
            have := poisLk_nonneg hρ hρs; positivity)
      _ = _ := by ring
  have := norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, probReal_univ, mul_one] at this
  exact this

/-- A vector of the gradient closure whose pairings with the gradients are bounded by
`M ‖∇f‖` has norm at most `M` (the argument of `dualNormSq_eq_of_pairing`). -/
theorem norm_le_of_pairing_le {D : Set ℂ} {V : Set (ℂ → ℝ)} (hV : IsDNSpace D V)
    {v : GradSpace D} (hv : v ∈ gradClosure D V) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ f ∈ V, ⟪v, gradFeat D f⟫ ≤ M * ‖gradFeat D f‖) : ‖v‖ ≤ M := by
  have hsub : (Submodule.span ℝ (gradFeat D '' V) : Set (GradSpace D)) ⊆
      {w | ⟪v, w⟫ ≤ M * ‖w‖} := by
    intro w hw
    obtain ⟨f, hf, rfl⟩ := mem_image_of_mem_span hV hw
    exact h f hf
  have hcl : IsClosed {w : GradSpace D | ⟪v, w⟫ ≤ M * ‖w‖} :=
    isClosed_le (continuous_const.inner continuous_id) (continuous_const.mul continuous_norm)
  have hv' : v ∈ closure (Submodule.span ℝ (gradFeat D '' V) : Set (GradSpace D)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hv
  have h1 := closure_minimal hsub hcl hv'
  simp only [Set.mem_ofPred_eq, real_inner_self_eq_norm_sq] at h1
  rcases (norm_nonneg v).lt_or_eq with hp | h0
  · nlinarith
  · rw [← h0]; exact hM

/-- **The mixed Poisson vectors are Lipschitz** on `closedBall t ρ₁ ∩ Hbar`, `ρ₁ < r`. -/
theorem exists_lip_rieszVec_halfDiscPoisson {D : Set ℂ} {c d t r ρ₁ : ℝ}
    (hgeom : Prop16Geometry D c d) (ht : t ∈ Set.Ioo c d) (hρ₁ : 0 < ρ₁) (hρ₁r : ρ₁ < r)
    (hsub : ball (t : ℂ) r ∩ H ⊆ D) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ z ∈ closedBall (t : ℂ) ρ₁ ∩ Hbar, ∀ w ∈ closedBall (t : ℂ) ρ₁ ∩ Hbar,
      ‖rieszVec D (mixedSpace D (realSet (Icc c d))) (halfDiscPoisson t r z) -
        rieszVec D (mixedSpace D (realSet (Icc c d))) (halfDiscPoisson t r w)‖ ≤
          L * ‖z - w‖ := by
  set V := mixedSpace D (realSet (Icc c d)) with hVdef
  have hV : IsDNSpace D V := isDNSpace_mixedSpace D _
  set δ : ℝ := (r - ρ₁) / 3 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set s : ℝ := ρ₁ + δ with hs
  set ρ₂ : ℝ := ρ₁ + 2 * δ with hρ₂
  have hρ₁s : ρ₁ < s := by linarith
  have hsρ₂ : s < ρ₂ := by linarith
  have hρ₂0 : 0 < ρ₂ := by linarith
  have hρ₂r : ρ₂ < r := by rw [hρ₂, hδ]; linarith
  obtain ⟨C, hC⟩ := mixedPoissonBound_holds D c d t r ρ₂ hgeom ht hρ₂0 hρ₂r hsub
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set L : ℝ := poisLk s ρ₁ * √C' with hL
  have hL0 : 0 ≤ L := mul_nonneg (poisLk_nonneg hρ₁.le hρ₁s) (Real.sqrt_nonneg _)
  refine ⟨L, hL0, fun z hz w hw => ?_⟩
  have hadm := (mixedHalfDiscMarkovCov_holds D c d t r ρ₁ hgeom ht hρ₁ hρ₁r hsub).1
  by_cases hpos : ∃ g ∈ V, 0 < dirichletEnergyOn D g
  swap
  · rw [eq_zero_of_mem_gradClosure_of_nopos hV hpos (rieszVec_mem (μ := halfDiscPoisson t r z)),
      eq_zero_of_mem_gradClosure_of_nopos hV hpos (rieszVec_mem (μ := halfDiscPoisson t r w)),
      sub_zero, norm_zero]
    positivity
  refine norm_le_of_pairing_le hV (sub_mem rieszVec_mem rieszVec_mem) (by positivity)
    fun f hf => ?_
  have hfc : Continuous f := (hV.smooth f hf).continuous
  set g := gradFeat D f with hg
  have hE : dirichletEnergyOn D f = ‖g‖ ^ 2 :=
    (norm_gradFeat_sq (hV.smooth f hf) (hV.energy f hf)).symm
  -- the trace bound
  have hT : ∀ y ∈ closedBall (t : ℂ) ρ₂ ∩ Hbar, |∫ x, f x ∂halfDiscPoisson t r y| ≤ √C' * ‖g‖ := by
    intro y hy
    have h1 := hC y hy f hf
    rw [hE] at h1
    have h2 : (∫ x, f x ∂halfDiscPoisson t r y) ^ 2 ≤ C' * ‖g‖ ^ 2 :=
      h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    calc |∫ x, f x ∂halfDiscPoisson t r y| ≤ √(C' * ‖g‖ ^ 2) := Real.abs_le_sqrt h2
      _ = √C' * ‖g‖ := by rw [Real.sqrt_mul hC'0, Real.sqrt_sq (norm_nonneg _)]
  set u := poisSm t r ρ₂ f with hu
  have hucont : Continuous u := continuous_poisSm hfc hρ₂0 hρ₂r
  have huharm : InnerProductSpace.HarmonicOnNhd u (closedBall (t : ℂ) s) := fun x hx =>
    harmonicOnNhd_poisSm hfc hρ₂0 hρ₂r x (closedBall_subset_ball hsρ₂ hx)
  have hrep : ∀ y ∈ closedBall (t : ℂ) ρ₁ ∩ Hbar,
      ∫ x, f x ∂halfDiscPoisson t r y = ∫ x, u x ∂halfDiscPoisson t s y := by
    intro y hy
    have hy1 := mem_closedBall_iff_norm.1 hy.1
    have e1 : ∫ x, f x ∂halfDiscPoisson t r y = u y := by
      rw [hu, poisSm, retr_eq_self hy.2 (by linarith)]
    have e2 := poisSm_eq_of_harmonic hρ₁s huharm (fun x _ => poisSm_conj t r ρ₂ f x) hy.2 hy1
    rw [poisSm, retr_eq_self hy.2 hy1] at e2
    rw [e1, e2]
  have hMu : ∀ x ∈ sphere (t : ℂ) s, |u (foldH x)| ≤ √C' * ‖g‖ := by
    intro x _
    rw [hu, poisSm_foldH, poisSm]
    exact hT _ ⟨mem_closedBall_iff_norm.2 (norm_retr_sub_le hρ₂0 x), retr_mem_Hbar hρ₂0 x⟩
  have hdiff := abs_integral_halfDiscPoisson_sub_le hρ₁.le hρ₁s hucont hMu
    (mem_closedBall_iff_norm.1 hz.1) (mem_closedBall_iff_norm.1 hw.1)
  rw [inner_sub_left, pair_rieszVec hV (hadm z hz) hpos f hf,
    pair_rieszVec hV (hadm w hw) hpos f hf, hrep z hz, hrep w hw]
  calc _ ≤ |∫ x, u x ∂halfDiscPoisson t s z - ∫ x, u x ∂halfDiscPoisson t s w| := le_abs_self _
    _ ≤ poisLk s ρ₁ * (√C' * ‖g‖) * ‖z - w‖ := hdiff
    _ = L * ‖z - w‖ * ‖g‖ := by rw [hL]; ring

end QuantumZipper.K3
