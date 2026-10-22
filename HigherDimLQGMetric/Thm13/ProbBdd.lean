import HigherDimLQGMetric.Thm13.ProbConvergence
import HigherDimLQGMetric.LfppTight.LawInput

/-! Lemma 3.6 gives the full-kernel convergence for bounded random
continuous perturbations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The exact current statement of the full-kernel half of L6c Lemma 3.6. -/
def L8Lemma36FullInput : Prop :=
  ∀ {d : ℕ} (_hd : 2 ≤ d) (κ : Rd d → ℝ)
    (_hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (_hεs : ∀ n, 0 < εs n)
    (_hεt : Tendsto εs atTop (𝓝 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (Dh : Ω → ContMetric d) (_hh : IsNormalizedLGF h P)
    (_hlim : ∀ᵐ ω ∂P, (Dh ω).IsLength ∧ IsProperFn (Dh ω).1 ∧
      ∀ R : ℝ, 0 < R → TendstoUniformlyOn
        (fun n => ⇑(lfppSeq κ ξ εs (h ω) n))
        ⇑(Dh ω).1 atTop
        (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R)),
    ∀ᵐ ω ∂P,
      ∀ (fn : ℕ → C(Rd d, ℝ)) (f : C(Rd d, ℝ)) (M : ℝ),
        (∀ n z, |fn n z| ≤ M) →
        (∀ R : ℝ, 0 < R →
          TendstoUniformlyOn (fun n => ⇑(fn n)) ⇑f atTop
            (closedBall 0 R)) →
        ∀ R : ℝ, 0 < R →
          TendstoUniformlyOn
            (fun n (p : Rd d × Rd d) =>
              (aEps κ ξ (εs n))⁻¹ *
                lfppDist κ ξ (εs n) (addFun (h ω) (fn n)) p)
            (fun p => (weylScale ξ f (Dh ω) p.1 p.2).toReal)
            atTop (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R)

theorem l8_ae_bdd_lfppSeq_conv
    (h36 : L8Lemma36FullInput)
    {d : ℕ} (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h₀ : Ω → DistRd d)
    (D₀ : Ω → ContMetric d) (hh₀ : IsNormalizedLGF h₀ P)
    (g : Ω → C(Rd d, ℝ)) (hgm : Measurable g)
    (hgb : ∀ ω, ∃ M : ℝ, ∀ z, |g ω z| ≤ M)
    (hgood : ∀ᵐ ω ∂P, (D₀ ω).IsLength ∧ IsProperFn (D₀ ω).1)
    (hconv : ∀ᵐ ω ∂P,
      Tendsto (fun n => lfppSeq κ ξ εs (h₀ ω) n) atTop (𝓝 (D₀ ω).1))
    (hW : ∀ᵐ ω ∂P, ∃ hD : (D₀ ω).IsLength,
      ∀ f : C(Rd d, ℝ),
        l8_patch hd hκ ξ εs hεs (addFun (h₀ ω) f) =
          weylMetric ξ f (D₀ ω) hD) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n => lfppSeq κ ξ εs (addFun (h₀ ω) (g ω)) n)
      atTop (𝓝 (l8_patch hd hκ ξ εs hεs
        (addFun (h₀ ω) (g ω))).1) := by
  have hlim : ∀ᵐ ω ∂P, (D₀ ω).IsLength ∧ IsProperFn (D₀ ω).1 ∧
      ∀ R : ℝ, 0 < R → TendstoUniformlyOn
        (fun n => ⇑(lfppSeq κ ξ εs (h₀ ω) n))
        ⇑(D₀ ω).1 atTop
        (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) := by
    filter_upwards [hgood, hconv] with ω hω ht
    refine ⟨hω.1, hω.2, fun R _ => ?_⟩
    exact (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp ht) _
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hfull := h36 hd κ hκ ξ εs hεs hεt P h₀ D₀ hh₀ hlim
  have hhplus : IsLGFPlusBddCont
      (fun ω => addFun (h₀ ω) (g ω)) P :=
    hh₀.1.isLGFPlusBddCont.addFun hgm hgb
  have hc : ∀ᵐ ω ∂P, ∀ n,
      Continuous (convMollify κ (εs n) (addFun (h₀ ω) (g ω))) :=
    ae_all_iff.2 fun n =>
      l6a_ae_continuous_convMollify hd κ hκ P
        (fun ω => addFun (h₀ ω) (g ω)) hhplus (hεs n)
  filter_upwards [hfull, hW, hc] with ω hω hWω hcω
  obtain ⟨hD, hWω⟩ := hWω
  obtain ⟨M, hM⟩ := hgb ω
  have hfconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn
      (fun _ : ℕ => ⇑(g ω)) ⇑(g ω) atTop
      (closedBall (0 : Rd d) R) := by
    intro R _
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    exact Eventually.of_forall fun _ z _ => by simpa using hη
  apply l8_tendsto_contMap_of_balls
  intro R hR
  have ht := hω (fun _ => g ω) (g ω) M (fun _ z => hM z)
    hfconv R hR
  have heq (n : ℕ) (p : Rd d × Rd d) :
      lfppSeq κ ξ εs (addFun (h₀ ω) (g ω)) n p =
        (aEps κ ξ (εs n))⁻¹ *
          lfppDist κ ξ (εs n) (addFun (h₀ ω) (g ω)) p := by
    have hfun : lfppDist κ ξ (εs n) (addFun (h₀ ω) (g ω)) =
        fieldLfpp ξ (convMollify κ (εs n) (addFun (h₀ ω) (g ω))) := by
      funext q
      exact (fieldLfpp_eq_lfppDistOn (hcω n) q).symm
    have hscaled : Continuous
        ((aEps κ ξ (εs n))⁻¹ •
          lfppDist κ ξ (εs n) (addFun (h₀ ω) (g ω))) := by
      rw [hfun]
      exact (continuous_fieldLfpp (hcω n)).const_smul _
    exact toCMapRd_apply_of_continuous hscaled p
  have htarget (p : Rd d × Rd d) :
      (weylScale ξ (g ω) (D₀ ω) p.1 p.2).toReal =
        (l8_patch hd hκ ξ εs hεs
          (addFun (h₀ ω) (g ω))).1 p := by
    rw [hWω (g ω), weylMetric_apply]
  exact (ht.congr (Eventually.of_forall fun n p _ => (heq n p).symm)).congr_right
    (fun p _ => htarget p)

/-- The bounded-input convergence clause, in continuous-map form. -/
theorem l8_prob_bdd_of_normalized_good
    (h36 : L8Lemma36FullInput)
    {d : ℕ} (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    (hN : L8NormalizedGood hd hκ ξ εs hεs)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsLGFPlusBddCont h P) :
    TendstoInProbLU P (fun n ω => lfppSeq κ ξ εs (h ω) n)
      atTop (fun ω => (l8_patch hd hκ ξ εs hεs (h ω)).1) := by
  obtain ⟨h₀, g, hh₀, hgm, hgb, hdec⟩ :=
    l8_lgfPlusBddCont_decomp hd P h hh
  obtain ⟨hgood, hconv, hW⟩ := hN P h₀ hh₀
  have hsample := l8_ae_bdd_lfppSeq_conv h36 hd κ hκ ξ εs hεs hεt
    P h₀ (fun ω => l8_patch hd hκ ξ εs hεs (h₀ ω)) hh₀
    g hgm hgb hgood hconv hW
  have hae : ∀ᵐ ω ∂P,
      Tendsto (fun n => lfppSeq κ ξ εs (h ω) n) atTop
        (𝓝 (l8_patch hd hκ ξ εs hεs (h ω)).1) := by
    filter_upwards [hsample] with ω ht
    simpa only [hdec ω] using ht
  have hXm (n : ℕ) : AEMeasurable
      (fun ω => lfppSeq κ ξ εs (h ω) n) P :=
    l6a_aemeasurable_normalized_lfpp hd κ hκ ξ (hεs n) P h hh
  have hYm : Measurable
      (fun ω => (l8_patch hd hκ ξ εs hεs (h ω)).1) :=
    measurable_subtype_coe.comp
      ((l8_measurable_patch hd hκ ξ εs hεs).comp hh.1)
  exact l8_tendstoInProbLU_of_ae P _ _ hXm hYm hae

/-- The exact B3 convergence expression uses the raw LFPP distance rather
than its continuous-map totalization. They agree almost surely at every
positive cutoff. -/
theorem l8_prob_bdd_raw_of_normalized_good
    (h36 : L8Lemma36FullInput)
    {d : ℕ} (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    (hN : L8NormalizedGood hd hκ ξ εs hεs)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsLGFPlusBddCont h P) :
    TendstoInProbLU P
      (fun n ω => (aEps κ ξ (εs n))⁻¹ •
        lfppDist κ ξ (εs n) (h ω)) atTop
      (fun ω => (l8_patch hd hκ ξ εs hεs (h ω)).1) := by
  have hc : ∀ᵐ ω ∂P, ∀ n,
      Continuous (convMollify κ (εs n) (h ω)) :=
    ae_all_iff.2 fun n =>
      l6a_ae_continuous_convMollify hd κ hκ P h hh (hεs n)
  have hEq : ∀ᵐ ω ∂P, ∀ n, ∀ p : Rd d × Rd d,
      ((aEps κ ξ (εs n))⁻¹ • lfppDist κ ξ (εs n) (h ω)) p =
        lfppSeq κ ξ εs (h ω) n p := by
    filter_upwards [hc] with ω hω n p
    have hfun : lfppDist κ ξ (εs n) (h ω) =
        fieldLfpp ξ (convMollify κ (εs n) (h ω)) := by
      funext q
      exact (fieldLfpp_eq_lfppDistOn (hω n) q).symm
    have hscaled : Continuous
        ((aEps κ ξ (εs n))⁻¹ • lfppDist κ ξ (εs n) (h ω)) := by
      rw [hfun]
      exact (continuous_fieldLfpp (hω n)).const_smul _
    exact (toCMapRd_apply_of_continuous hscaled p).symm
  have ht := l8_prob_bdd_of_normalized_good h36 hd κ hκ ξ εs hεs
    hεt hN P h hh
  intro R hR δ hδ
  refine (ht R hR δ hδ).congr' (Eventually.of_forall fun n => ?_)
  apply measure_congr
  filter_upwards [hEq] with ω hω
  have heq : (fun p => ((aEps κ ξ (εs n))⁻¹ •
        lfppDist κ ξ (εs n) (h ω)) p) =
      (fun p => lfppSeq κ ξ εs (h ω) n p) :=
    funext (hω n)
  simp only [heq]

end HigherDimLQGMetric
