import SupercriticalConformalCovariance.Markov.FullIndep
import LQGMetric.Field.MarkovVer2Riesz

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace SupercriticalConformalCovariance.Markov

open LQGMetric LQGMetric.GFFExist LQGMetric.MarkovZB LQGMetric.MarkovExt
  LQGMetric.MarkovNorm LQGMetric.MarkovVer2 QuantumZipper QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC} {V : Opens ℂ}

theorem inner_rieszFun_bddSupp (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β : TestOn V) (hβ : ∫ x, β x = 1)
    {ρ : ℂ → ℝ} {M R : ℝ} (hρ : BddSupp ρ M R)
    (hρ0 : ∀ x ∉ (V : Set ℂ), ρ x = 0)
    {f : ℂ → ℝ} (hf : f ∈ zeroSpace V) :
    ⟪rieszFun V ρ, gradFeat V f⟫ = ∫ x, ρ x * f x := by
  have hadm := admissible_bddSupp hh hV hpos β hβ hρ hρ0
  rw [rieszFun, inner_sub_left,
    pair_rieszVec (isDNSpace_zeroSpace (V : Set ℂ)) hadm.1 hpos f hf,
    pair_rieszVec (isDNSpace_zeroSpace (V : Set ℂ)) hadm.2 hpos f hf]
  exact integral_testMeas_sub hρ.meas hρ.bdd hf

theorem rieszFun_sub_bddSupp (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β : TestOn V) (hβ : ∫ x, β x = 1)
    {ρ σ : ℂ → ℝ} {M N R : ℝ}
    (hρ : BddSupp ρ M R) (hσ : BddSupp σ N R)
    (hρ0 : ∀ x ∉ (V : Set ℂ), ρ x = 0)
    (hσ0 : ∀ x ∉ (V : Set ℂ), σ x = 0) :
    rieszFun V (ρ - σ) = rieszFun V ρ - rieszFun V σ := by
  have hsub : BddSupp (ρ - σ) (M + N) R := by
    change BddSupp (fun u => ρ u - σ u) (M + N) R
    simpa only [max_self] using hρ.sub hσ
  have hsub0 : ∀ x ∉ (V : Set ℂ), (ρ - σ) x = 0 := by
    intro x hx
    simp [hρ0 x hx, hσ0 x hx]
  refine LQGMetric.eq_of_mem_gradClosure (rieszFun_mem V _)
    (sub_mem (rieszFun_mem V _) (rieszFun_mem V _)) fun f hf => ?_
  rw [inner_sub_left, inner_rieszFun_bddSupp hh hV hpos β hβ hsub hsub0 hf,
    inner_rieszFun_bddSupp hh hV hpos β hβ hρ hρ0 hf,
    inner_rieszFun_bddSupp hh hV hpos β hβ hσ hσ0 hf]
  have hiρ : Integrable fun x => ρ x * f x :=
    (hf.1.continuous.integrable_of_hasCompactSupport hf.2.1).bdd_mul
      hρ.meas.aestronglyMeasurable (c := M)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hρ.bdd x)
  have hiσ : Integrable fun x => σ x * f x :=
    (hf.1.continuous.integrable_of_hasCompactSupport hf.2.1).bdd_mul
      hσ.meas.aestronglyMeasurable (c := N)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hσ.bdd x)
  rw [← integral_sub hiρ hiσ]
  congr 1
  funext x
  simp [sub_mul]

/-- Uniform variance bound for bounded densities with a fixed compact support radius. -/
theorem norm_rieszFun_sq_le_general (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β : TestOn V) (hβ : ∫ x, β x = 1)
    {R : ℝ} (hR : 0 ≤ R) {ζ : ℂ → ℝ}
    (hζs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ)
    (hζ01 : ∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1)
    (hζR : ∀ x, R < ‖x‖ → ζ x = 0)
    (hζβ : ∀ x ∈ tsupport β, ζ x = 1)
    {ρ : ℂ → ℝ} {M Rρ : ℝ} (hρ : BddSupp ρ M Rρ)
    (hρ0 : ∀ x ∉ (V : Set ℂ), ρ x = 0)
    (hζρ : ∀ x, ρ x ≠ 0 → ζ x = 1) :
    ‖rieszFun V ρ‖ ^ 2 ≤
      2 * (∫ x, ρ x ^ 2) * schurLR R +
      2 * (2 * (∫ x, β x ^ 2) * schurLR R + 2 * ‖zbRiesz V β‖ ^ 2) *
        (∫ x, ρ x) ^ 2 := by
  let Q : ℝ := 2 * (∫ x, ρ x ^ 2) * schurLR R +
    2 * (2 * (∫ x, β x ^ 2) * schurLR R + 2 * ‖zbRiesz V β‖ ^ 2) *
      (∫ x, ρ x) ^ 2
  have hQ0 : 0 ≤ Q := by
    have hρ2 : 0 ≤ ∫ x, ρ x ^ 2 := integral_nonneg fun x => sq_nonneg _
    have hβ2 : 0 ≤ ∫ x, β x ^ 2 := integral_nonneg fun x => sq_nonneg _
    have hs : 0 ≤ schurLR R := schurLR_nonneg hR
    dsimp [Q]
    positivity
  have hfeat : ∀ f ∈ zeroSpace (V : Set ℂ),
      ⟪rieszFun V ρ, gradFeat V f⟫ ≤ √Q * ‖gradFeat V f‖ := by
    intro f hf
    rw [inner_rieszFun_bddSupp hh hV hpos β hβ hρ hρ0 hf]
    have hsq := integral_density_sq_le_dirichlet hh hV hpos β hβ hR hζs
      hζ01 hζR hζβ hρ hζρ hf
    have he : dirichletEnergyOn V f = ‖gradFeat V f‖ ^ 2 := by
      rw [norm_gradFeat_sq ((isDNSpace_zeroSpace _).smooth f hf)
        ((isDNSpace_zeroSpace _).energy f hf)]
    rw [he] at hsq
    calc
      (∫ x, ρ x * f x) ≤ |∫ x, ρ x * f x| := le_abs_self _
      _ = √((∫ x, ρ x * f x) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ √(Q * ‖gradFeat V f‖ ^ 2) := Real.sqrt_le_sqrt hsq
      _ = √Q * ‖gradFeat V f‖ := by
        rw [Real.sqrt_mul hQ0, Real.sqrt_sq (norm_nonneg _)]
  have hsub : (Submodule.span ℝ (gradFeat V '' zeroSpace (V : Set ℂ)) :
      Set (GradSpace V)) ⊆
      {w | ⟪rieszFun V ρ, w⟫ ≤ √Q * ‖w‖} := by
    intro w hw
    obtain ⟨f, hf, rfl⟩ := mem_image_of_mem_span (isDNSpace_zeroSpace (V : Set ℂ)) hw
    exact hfeat f hf
  have hcl : IsClosed {w : GradSpace V | ⟪rieszFun V ρ, w⟫ ≤ √Q * ‖w‖} :=
    isClosed_le (continuous_const.inner continuous_id) (continuous_const.mul continuous_norm)
  have hv' : rieszFun V ρ ∈
      closure (Submodule.span ℝ (gradFeat V '' zeroSpace (V : Set ℂ)) :
        Set (GradSpace V)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact rieszFun_mem V ρ
  have hh' := closure_minimal hsub hcl hv'
  simp only [Set.mem_ofPred_eq, real_inner_self_eq_norm_sq] at hh'
  have hv2 : ‖rieszFun V ρ‖ ≤ √Q := by
    rcases (norm_nonneg (rieszFun V ρ)).lt_or_eq with hp | h0
    · nlinarith [Real.sqrt_nonneg Q]
    · rw [← h0]
      exact Real.sqrt_nonneg _
  calc
    ‖rieszFun V ρ‖ ^ 2 ≤ (√Q) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hv2 2
    _ = Q := Real.sq_sqrt hQ0

/-- Fixed-cutoff (L^2) estimate; its constant is uniform over all bounded densities
supported where the cutoff is one. -/
theorem norm_rieszFun_sq_le_uniform (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β : TestOn V) (hβ : ∫ x, β x = 1)
    {R : ℝ} (hR : 0 ≤ R) {ζ : ℂ → ℝ}
    (hζs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ)
    (hζ01 : ∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1)
    (hζR : ∀ x, R < ‖x‖ → ζ x = 0)
    (hζβ : ∀ x ∈ tsupport β, ζ x = 1)
    {ρ : ℂ → ℝ} {M Rρ : ℝ} (hρ : BddSupp ρ M Rρ)
    (hρ0 : ∀ x ∉ (V : Set ℂ), ρ x = 0)
    (hζρ : ∀ x, ρ x ≠ 0 → ζ x = 1) :
    ‖rieszFun V ρ‖ ^ 2 ≤
      (2 * schurLR R +
        2 * (2 * (∫ x, β x ^ 2) * schurLR R + 2 * ‖zbRiesz V β‖ ^ 2) *
          (∫ x, ζ x ^ 2)) * (∫ x, ρ x ^ 2) := by
  have hζc : HasCompactSupport ζ := hasCompactSupport_of_ball hR hζR
  have hζ2 : MemLp ζ 2 (volume : Measure ℂ) :=
    memLp_two_of_continuous_compact hζs.continuous hζc
  have hρ2i : Integrable (fun x => ρ x ^ 2) := by
    have hi := hρ.integrable_mul_bdd (f := ρ) hρ.meas (K := M)
      (fun x _ => hρ.bdd x)
    exact hi.congr (Eventually.of_forall fun x => by simp [pow_two])
  have hρ2 : MemLp ρ 2 (volume : Measure ℂ) := by
    rw [memLp_two_iff_integrable_sq hρ.meas.aestronglyMeasurable]
    exact hρ2i
  have hm : (∫ x, ρ x) = ∫ x, ρ x * ζ x := by
    congr 1
    funext x
    by_cases hx : ρ x = 0
    · simp [hx]
    · rw [hζρ x hx, mul_one]
  have hmass : (∫ x, ρ x) ^ 2 ≤
      (∫ x, ρ x ^ 2) * (∫ x, ζ x ^ 2) := by
    rw [hm]
    exact integral_mul_sq_le hρ2 hζ2
  have hq := norm_rieszFun_sq_le_general hh hV hpos β hβ hR hζs hζ01
    hζR hζβ hρ hρ0 hζρ
  have hC : 0 ≤ 2 * (2 * (∫ x, β x ^ 2) * schurLR R +
      2 * ‖zbRiesz V β‖ ^ 2) := by
    have hβ2 : 0 ≤ ∫ x, β x ^ 2 := integral_nonneg fun x => sq_nonneg _
    have hs : 0 ≤ schurLR R := schurLR_nonneg hR
    positivity
  calc
    ‖rieszFun V ρ‖ ^ 2 ≤
        2 * (∫ x, ρ x ^ 2) * schurLR R +
          2 * (2 * (∫ x, β x ^ 2) * schurLR R +
            2 * ‖zbRiesz V β‖ ^ 2) * (∫ x, ρ x) ^ 2 := hq
    _ ≤ 2 * (∫ x, ρ x ^ 2) * schurLR R +
          2 * (2 * (∫ x, β x ^ 2) * schurLR R +
            2 * ‖zbRiesz V β‖ ^ 2) *
              ((∫ x, ρ x ^ 2) * (∫ x, ζ x ^ 2)) := by
        gcongr
    _ = _ := by ring

end SupercriticalConformalCovariance.Markov
