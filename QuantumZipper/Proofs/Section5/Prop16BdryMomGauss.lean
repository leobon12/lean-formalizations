import QuantumZipper.Proofs.Zipper.UnzipExpMomGauss
import QuantumZipper.Proofs.GFF.K3.MixedM7A3
import QuantumZipper.Proofs.Section5.Prop16LocalAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Exponential moments of the local harmonic part on a boundary circle (task P16-BDRYMOM-B)

`lintegral_expV_bdryMom_le`: in the local coupling of the mixed GFF `Y` on `D` with the free
field `Xf` near the free arc (M7, `K3.MixedFreeCouplingHalfDiscStmt`: a.s.
`Y μ = Xf μ − |μ| Xf ρ₀ + ∫ g dμ` for admissible `μ` carried by `closedBall t r'`), the random
function `V = g − Xf ρ₀ + Xf (fc(0,R))` has exponential moments on the folded circle
`foldedCircle t s0`: `ω ↦ ∫ exp(λ V) d(fc(t,s0))` is measurable and has finite expectation.

This is an input for the boundary masses of Proposition 1.6 (Sheffield, arXiv:1012.4797, p. 25).

Proof (own elementary assembly):
1. *Poisson reproduction* (the disc Poisson formula for the even harmonic function `g ∘ foldH`,
   `K3.integral_halfDiscPoisson_of_harmonic`): for `u ∈ closedBall t s0 ∩ Hbar`, `P_u :=
   halfDiscPoisson t s1 u` is an admissible probability measure carried by the semicircle
   with `∫ g dP_u = g u`; hence a.s.
   `V u = Y(P_u) + (Xf(P_t) − Xf(P_u)) + (Xf(fc(0,R)) − Xf(P_t))`.
2. Each summand is a centred Gaussian with variance bounded uniformly in `u`: `Y(P_u)` by the
   uniform trace bound `K3.mixedPoissonBound_holds` (M7-a1; the Markov/coupling input is
   Sheffield, *Gaussian free fields for mathematicians*, PTRF 2007, Thm 2.17), the second by the
   Lipschitz bound `K3.kernelCov2_halfDiscPoisson_le`, the third is a fixed pair. With
   `exp(a+b+c) ≤ exp 3a + exp 3b + exp 3c`, `E exp(λ V u) ≤ M` uniformly.
3. Measurability through the retraction `K3.retr` onto `closedBall t r' ∩ Hbar` (joint
   measurability of a Carathéodory function), then Tonelli.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set InnerProductSpace
open scoped Real ComplexConjugate ENNReal NNReal

namespace QuantumZipper

namespace Prop16Asm

/-- `exp(λ(a+b+c)) ≤ exp(3λa) + exp(3λb) + exp(3λc)`. -/
theorem exp_mul_add3_le_bdryMom (lam a b c : ℝ) :
    Real.exp (lam * (a + b + c)) ≤
      Real.exp (3 * lam * a) + Real.exp (3 * lam * b) + Real.exp (3 * lam * c) := by
  have ha := Real.exp_pos (3 * lam * a)
  have hb := Real.exp_pos (3 * lam * b)
  have hc := Real.exp_pos (3 * lam * c)
  rcases (show lam * (a + b + c) ≤ 3 * lam * a ∨ lam * (a + b + c) ≤ 3 * lam * b ∨
      lam * (a + b + c) ≤ 3 * lam * c by
    by_contra h
    push Not at h
    linarith [h.1, h.2.1, h.2.2]) with h | h | h
  · linarith [Real.exp_le_exp.2 h]
  · linarith [Real.exp_le_exp.2 h]
  · linarith [Real.exp_le_exp.2 h]

/-- Exponential moments of one coordinate of a mixed GFF from a trace bound. -/
theorem lintegral_exp_mixed_le_bdryMom {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    [IsProbabilityMeasure P₀] {D S : Set ℂ} {Y : Ω₀ → FieldSample}
    (hY : IsMixedGFF D S Y P₀) {μ : Measure ℂ} (hμ : IsAdmissibleDual D (mixedSpace D S) μ)
    {C : ℝ} (hC : ∀ f ∈ mixedSpace D S, (∫ x, f x ∂μ) ^ 2 ≤ C * dirichletEnergyOn D f)
    (s : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (s * Y ω μ)) ∂P₀ ≤
      ENNReal.ofReal (Real.exp (max (4 * C) 0 / 2 * s ^ 2 / 2)) := by
  have hG : HasGaussianLaw (fun ω => Y ω μ) P₀ :=
    hY.gaussian.hasGaussianLaw_eval (⟨μ, hμ⟩ : {μ // IsAdmissibleDual D (mixedSpace D S) μ})
  have hm : Measurable fun ω => Y ω μ := hY.measurable_coord μ
  have hlaw : P₀.map (fun ω => Y ω μ) =
      gaussianReal 0 (dualCov D (mixedSpace D S) μ μ).toNNReal := by
    rw [hG.map_eq_gaussianReal, hY.centered μ hμ, ← covariance_self hm.aemeasurable,
      hY.covariance_eq μ μ hμ hμ]
  rw [RegUnif.unzipExpMom_lintegral_exp_gauss hm hlaw s]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  -- the variance bound
  have h2 : (dualNormSq D (mixedSpace D S) (μ + μ)).toReal ≤ max (4 * C) 0 := by
    refine ENNReal.toReal_le_of_le_ofReal (le_max_right _ _) ?_
    unfold dualNormSq
    refine iSup₂_le fun f hf => ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hf.2]
    have hint : ∫ x, f x ∂(μ + μ) = 2 * ∫ x, f x ∂μ := by
      by_cases hi : Integrable f μ
      · rw [integral_add_measure hi hi]; ring
      · rw [integral_undef hi, integral_undef (by rwa [integrable_add_measure, and_self])]
        ring
    rw [hint]
    have h4 := mul_le_mul_of_nonneg_right (le_max_left (4 * C) 0) hf.2.le
    nlinarith [hC f hf.1]
  have hcov : dualCov D (mixedSpace D S) μ μ ≤ max (4 * C) 0 / 2 := by
    unfold dualCov
    have := (dualNormSq D (mixedSpace D S) μ).toReal_nonneg
    linarith
  have hv : ((dualCov D (mixedSpace D S) μ μ).toNNReal : ℝ) ≤ max (4 * C) 0 / 2 := by
    rw [Real.coe_toNNReal']
    exact max_le hcov (by positivity)
  have hs := sq_nonneg s
  have := mul_le_mul_of_nonneg_right hv hs
  linarith

/-- **Pointwise uniform bound**: `E exp(λ V u) ≤ M` for `u ∈ closedBall t s0 ∩ Hbar`. -/
theorem lintegral_expV_point_le_bdryMom {D : Set ℂ} {c d t r' s0 s1 R C : ℝ}
    (hs0 : 0 < s0) (hs01 : s0 < s1) (hs1 : s1 ≤ r') (hR : 0 < R)
    {ρ₀ : Measure ℂ} {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    {Y Xf : Ω₀ → FieldSample} {g : Ω₀ → ℂ → ℝ}
    (hY : IsMixedGFF D (realSet (Set.Icc c d)) Y P₀) (hXf : IsFreeGFFModConstH Xf P₀)
    (hgh : ∀ ω, HarmonicOnNhd (fun z => g ω (foldH z)) (closedBall (t : ℂ) r'))
    (hrep : ∀ μ : Measure ℂ, IsAdmissibleH μ → μ (closedBall (t : ℂ) r')ᶜ = 0 →
      ∀ᵐ ω ∂P₀, Y ω μ = Xf ω μ - (μ Set.univ).toReal * Xf ω ρ₀ + ∫ z, g ω z ∂μ)
    (hKD : sphere (t : ℂ) s1 ∩ Hbar ⊆ closure D)
    (hC : ∀ z ∈ closedBall (t : ℂ) s0 ∩ Hbar, ∀ f ∈ mixedSpace D (realSet (Icc c d)),
      (∫ x, f x ∂K3.halfDiscPoisson t s1 z) ^ 2 ≤ C * dirichletEnergyOn D f)
    (lam : ℝ) {u : ℂ} (hu : u ∈ closedBall (t : ℂ) s0 ∩ Hbar) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * (g ω u - Xf ω ρ₀ + Xf ω (foldedCircle 0 R)))) ∂P₀ ≤
      ENNReal.ofReal (Real.exp (max (4 * C) 0 / 2 * (3 * lam) ^ 2 / 2)) +
      ENNReal.ofReal (Real.exp (max (2 * (K3.lipρ s1 s0 * K3.Bv t s1 s0) * s0) 0 *
        (3 * lam) ^ 2 / 2)) +
      ENNReal.ofReal (Real.exp (|kernelCov2 neumannH
        (foldedCircle 0 R, K3.halfDiscPoisson t s1 (t : ℂ))
        (foldedCircle 0 R, K3.halfDiscPoisson t s1 (t : ℂ))| * (3 * lam) ^ 2 / 2)) := by
  have hs1p : 0 < s1 := hs0.trans hs01
  have hut : ‖u - t‖ ≤ s0 := mem_closedBall_iff_norm.1 hu.1
  have htt : ‖(t : ℂ) - t‖ ≤ s0 := by simp [hs0.le]
  set Pu := K3.halfDiscPoisson t s1 u with hPu_def
  set Pt := K3.halfDiscPoisson t s1 (t : ℂ) with hPt_def
  have hPu : IsProbabilityMeasure Pu :=
    K3.isProbabilityMeasure_halfDiscPoisson hs1p (mem_ball_iff_norm.2 (hut.trans_lt hs01))
  have hPt : IsProbabilityMeasure Pt :=
    K3.isProbabilityMeasure_halfDiscPoisson hs1p (mem_ball_self hs1p)
  have hPuA : IsAdmissibleH Pu := K3.isAdmissibleH_halfDiscPoisson hs1p hs01 hut
  have hPtA : IsAdmissibleH Pt := K3.isAdmissibleH_halfDiscPoisson hs1p hs01 htt
  have hfcA : IsAdmissibleH (foldedCircle 0 R) :=
    isAdmissibleH_foldedCircle (by simp [Hbar]) hR
  have hsupp : Pu (closedBall (t : ℂ) r')ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 fun x hx =>
      mem_closedBall_iff_norm.2 ((mem_sphere_iff_norm.1 hx.1).le.trans hs1))
      (K3.halfDiscPoisson_compl_eq_zero hs1p u)
  have hgint : ∀ ω, ∫ z, g ω z ∂Pu = g ω u := by
    intro ω
    have hh : HarmonicOnNhd (fun z => g ω (foldH z)) (closedBall (t : ℂ) s1) :=
      fun x hx => hgh ω x (closedBall_subset_closedBall hs1 hx)
    have h1 := K3.integral_halfDiscPoisson_of_harmonic hs1p
      (mem_ball_iff_norm.2 (hut.trans_lt hs01)) hh
      (fun x _ => by rw [CircleFubini.foldH_eq_mk, CircleFubini.foldH_eq_mk]; simp [abs_neg])
    rw [CircleFubini.foldH_of_mem' hu.2] at h1
    rw [← h1]
    refine integral_congr_ae ?_
    filter_upwards [K3.ae_halfDiscPoisson_mem hs1p u] with x hx
    simp only [CircleFubini.foldH_of_mem' hx.2]
  have hae : ∀ᵐ ω ∂P₀, Y ω Pu = Xf ω Pu - Xf ω ρ₀ + g ω u := by
    filter_upwards [hrep Pu hPuA hsupp] with ω hω
    rw [hω, measure_univ, ENNReal.toReal_one, one_mul, hgint]
  have hPuD : IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) Pu :=
    K3.isAdmissibleDual_of_sq_le_m7a ((isCompact_sphere _ _).inter_right isClosed_Hbar) hKD
      (K3.halfDiscPoisson_compl_eq_zero hs1p u) (hC u hu)
  have hmass : Pt univ = Pu univ := by rw [measure_univ, measure_univ]
  have hB0 : 0 ≤ kernelCov2 neumannH (Pt, Pu) (Pt, Pu) := by
    rw [← hXf.covariance_eq (Pt, Pu) (Pt, Pu) hPtA hPuA hmass hPtA hPuA hmass]
    show 0 ≤ cov[fun ω => Xf ω Pt - Xf ω Pu, fun ω => Xf ω Pt - Xf ω Pu; P₀]
    rw [covariance_self (X := fun ω => Xf ω Pt - Xf ω Pu)
      (((hXf.measurable_coord _).sub (hXf.measurable_coord _)).aemeasurable)]
    exact variance_nonneg _ _
  have hVB : |kernelCov2 neumannH (Pt, Pu) (Pt, Pu)| ≤
      max (2 * (K3.lipρ s1 s0 * K3.Bv t s1 s0) * s0) 0 := by
    rw [abs_of_nonneg hB0]
    refine (K3.kernelCov2_halfDiscPoisson_le hs1p hs0.le hs01 htt hut).trans ?_
    have hn : ‖(t : ℂ) - u‖ ≤ s0 := by rw [norm_sub_rev]; exact hut
    have hn0 := norm_nonneg ((t : ℂ) - u)
    rcases le_total 0 (K3.lipρ s1 s0 * K3.Bv t s1 s0) with h | h
    · exact le_max_of_le_left (by nlinarith)
    · exact le_max_of_le_right (by nlinarith)
  have hA := lintegral_exp_mixed_le_bdryMom hY hPuD (hC u hu) (3 * lam)
  have hBm := RegUnif.unzipExpMom_lintegral_exp_diff_le hXf hPtA hPuA hmass (3 * lam) hVB
  have hCm := RegUnif.unzipExpMom_lintegral_exp_diff_le hXf hfcA hPtA
    (by rw [measure_univ, measure_univ]) (3 * lam) le_rfl
  have m1 : Measurable fun ω => ENNReal.ofReal (Real.exp (3 * lam * Y ω Pu)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (hY.measurable_coord _)))
  have m2 : Measurable fun ω => ENNReal.ofReal (Real.exp (3 * lam * (Xf ω Pt - Xf ω Pu))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul ((hXf.measurable_coord _).sub (hXf.measurable_coord _))))
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * (g ω u - Xf ω ρ₀ + Xf ω (foldedCircle 0 R)))) ∂P₀
      ≤ ∫⁻ ω, (ENNReal.ofReal (Real.exp (3 * lam * Y ω Pu)) +
          ENNReal.ofReal (Real.exp (3 * lam * (Xf ω Pt - Xf ω Pu)))) +
          ENNReal.ofReal (Real.exp (3 * lam * (Xf ω (foldedCircle 0 R) - Xf ω Pt))) ∂P₀ := by
        refine lintegral_mono_ae (hae.mono fun ω hω => ?_)
        have key : g ω u - Xf ω ρ₀ + Xf ω (foldedCircle 0 R) =
            Y ω Pu + (Xf ω Pt - Xf ω Pu) + (Xf ω (foldedCircle 0 R) - Xf ω Pt) := by
          rw [hω]; ring
        rw [key]
        refine (ENNReal.ofReal_le_ofReal (exp_mul_add3_le_bdryMom _ _ _ _)).trans ?_
        exact ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (3 * lam * Y ω Pu)) ∂P₀ +
          ∫⁻ ω, ENNReal.ofReal (Real.exp (3 * lam * (Xf ω Pt - Xf ω Pu))) ∂P₀ +
          ∫⁻ ω, ENNReal.ofReal (Real.exp (3 * lam * (Xf ω (foldedCircle 0 R) - Xf ω Pt))) ∂P₀ := by
        rw [lintegral_add_left, lintegral_add_left m1]
        exact m1.add m2
    _ ≤ _ := add_le_add (add_le_add hA hBm) hCm

/-- **Exponential moments of the local harmonic part on a boundary circle** (task P16-BDRYMOM-B;
input for the boundary masses in Prop. 1.6 of Sheffield, arXiv:1012.4797, p. 25). -/
theorem lintegral_expV_bdryMom_le {D : Set ℂ} {c d t r r' s0 s1 R : ℝ}
    (hgeo : K3.Prop16Geometry D c d) (ht : t ∈ Set.Ioo c d) (hs0 : 0 < s0) (hs01 : s0 < s1)
    (hs1 : s1 ≤ r') (hr'r : r' < r) (hD : Metric.ball (t : ℂ) r ∩ H ⊆ D) (hR : 0 < R)
    {ρ₀ : Measure ℂ} {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    {Y Xf : Ω₀ → FieldSample} {g : Ω₀ → ℂ → ℝ}
    (hY : IsMixedGFF D (realSet (Set.Icc c d)) Y P₀) (hXf : IsFreeGFFModConstH Xf P₀)
    (hgh : ∀ ω, InnerProductSpace.HarmonicOnNhd (fun z => g ω (foldH z)) (Metric.closedBall (t : ℂ) r'))
    (hgm : ∀ z, Measurable fun ω => g ω z)
    (hrep : ∀ μ : Measure ℂ, IsAdmissibleH μ → μ (Metric.closedBall (t : ℂ) r')ᶜ = 0 →
      ∀ᵐ ω ∂P₀, Y ω μ = Xf ω μ - (μ Set.univ).toReal * Xf ω ρ₀ + ∫ z, g ω z ∂μ)
    (lam : ℝ) :
    Measurable (fun ω => ∫⁻ w, ENNReal.ofReal (Real.exp (lam * (g ω w - Xf ω ρ₀ +
        Xf ω (foldedCircle 0 R)))) ∂foldedCircle (t : ℂ) s0) ∧
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∫⁻ ω, ∫⁻ w, ENNReal.ofReal (Real.exp (lam * (g ω w - Xf ω ρ₀ +
        Xf ω (foldedCircle 0 R)))) ∂foldedCircle (t : ℂ) s0 ∂P₀ ≤ M := by
  have hs1p : 0 < s1 := hs0.trans hs01
  have hr'p : 0 < r' := hs1p.trans_le hs1
  have hsub : ball (t : ℂ) s1 ∩ H ⊆ D :=
    (inter_subset_inter_left _ (ball_subset_ball (hs1.trans hr'r.le))).trans hD
  obtain ⟨C, hC⟩ := K3.mixedPoissonBound_holds D c d t s1 s0 hgeo ht hs0 hs01 hsub
  have hKD : sphere (t : ℂ) s1 ∩ Hbar ⊆ closure D := fun x hx =>
    K3.halfDisc_subset_closure_m7a hs1p hsub ⟨sphere_subset_closedBall hx.1, hx.2⟩
  have hpt := fun u (hu : u ∈ closedBall (t : ℂ) s0 ∩ Hbar) =>
    lintegral_expV_point_le_bdryMom (ρ₀ := ρ₀) hs0 hs01 hs1 hR hY hXf hgh hrep hKD hC lam hu
  -- the retracted field `G`, jointly measurable
  set G : Ω₀ → ℂ → ℝ := fun ω w => g ω (K3.retr t r' w) with hG_def
  have hretr : Continuous (K3.retr t r') :=
    (LipschitzWith.of_dist_le_mul (K := 2) fun z w => by
      simpa [dist_eq_norm] using K3.norm_retr_sub_retr_le hr'p z w).continuous
  have hGc : ∀ ω, Continuous (G ω) := by
    intro ω
    have hco : ContinuousOn (g ω) (closedBall (t : ℂ) r' ∩ Hbar) := by
      have h := (hgh ω).continuousOn.mono (inter_subset_left (t := Hbar))
      refine h.congr fun x hx => ?_
      simp only [CircleFubini.foldH_of_mem' hx.2]
    exact hco.comp_continuous hretr fun w =>
      ⟨mem_closedBall_iff_norm.2 (K3.norm_retr_sub_le hr'p w), K3.retr_mem_Hbar hr'p w⟩
  have hGm : Measurable fun p : Ω₀ × ℂ => G p.1 p.2 :=
    (measurable_uncurry_of_continuous_of_measurable (u := fun w ω => G ω w)
      (fun ω => hGc ω) (fun w => hgm _)).comp measurable_swap
  set F : Ω₀ × ℂ → ℝ≥0∞ := fun p => ENNReal.ofReal (Real.exp (lam * (G p.1 p.2 - Xf p.1 ρ₀ +
    Xf p.1 (foldedCircle 0 R)))) with hF_def
  have hFm : Measurable F :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
      ((hGm.sub ((hXf.measurable_coord ρ₀).comp measurable_fst)).add
        ((hXf.measurable_coord _).comp measurable_fst))))
  have hae := Prop16Area.G.ae_fc_mem_ball_inter (d := (t : ℂ)) (by simp [Hbar]) hs0
  have hGg : ∀ᵐ w ∂foldedCircle (t : ℂ) s0, ∀ ω, G ω w = g ω w := by
    filter_upwards [hae] with w hw ω
    simp only [hG_def]
    rw [K3.retr_eq_self hw.2 ((mem_closedBall_iff_norm.1 hw.1).trans (hs01.le.trans hs1))]
  have heq : (fun ω => ∫⁻ w, ENNReal.ofReal (Real.exp (lam * (g ω w - Xf ω ρ₀ +
      Xf ω (foldedCircle 0 R)))) ∂foldedCircle (t : ℂ) s0) =
      fun ω => ∫⁻ w, F (ω, w) ∂foldedCircle (t : ℂ) s0 :=
    funext fun ω => lintegral_congr_ae (hGg.mono fun w hw => by simp only [hF_def, hw ω])
  obtain ⟨M, hMtop, hMle⟩ : ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ u ∈ closedBall (t : ℂ) s0 ∩ Hbar,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * (g ω u - Xf ω ρ₀ + Xf ω (foldedCircle 0 R)))) ∂P₀
        ≤ M := by
    refine ⟨_, ?_, hpt⟩
    exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
      ENNReal.ofReal_ne_top⟩, ENNReal.ofReal_ne_top⟩
  refine ⟨by rw [heq]; exact hFm.lintegral_prod_right', M, hMtop, ?_⟩
  have hswap := lintegral_lintegral_swap (μ := P₀) (ν := foldedCircle (t : ℂ) s0)
    (f := fun ω w => F (ω, w)) hFm.aemeasurable
  refine le_of_eq_of_le (lintegral_congr fun ω => congrFun heq ω) ?_
  rw [hswap]
  refine (lintegral_mono_ae ?_).trans (le_of_eq (by rw [lintegral_const, measure_univ, mul_one]))
  filter_upwards [hae, hGg] with w hw hw'
  simp only [hF_def, hw']
  exact hMle w hw

end Prop16Asm

end QuantumZipper
