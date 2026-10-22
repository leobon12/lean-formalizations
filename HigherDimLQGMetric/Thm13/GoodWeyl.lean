import HigherDimLQGMetric.Thm13.GoodCoupling
import HigherDimLQGMetric.Trunc.Main

/-! Lemma 3.6 supplies the single event needed for MA5 A21(4). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The exact current statement of the truncated half of L6c Lemma 3.6. -/
def L8Lemma36TruncInput : Prop :=
  ∀ {d : ℕ} (_hd : 2 ≤ d) (κ : Rd d → ℝ)
    (_hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (_hL2c : L2c_trunc)
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
    ∀ᵐ ω ∂P, L8Lemma36Event κ ξ εs (h ω) (Dh ω)

/-- The exact current statement of L6c Lemma 3.1(1). -/
def L8LengthLimitInput : Prop :=
  (∀ d ξ κ, L6a_tight d ξ κ) → ∀ {d : ℕ} (ξ : ℝ) (κ : Rd d → ℝ)
    (_hB2 : ∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧
      DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistRd d),
    IsNormalizedLGF h P →
    ∀ μ : ProbabilityMeasure C(Rd d × Rd d, ℝ),
      μ ∈ closure {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
        ∃ ε ∈ Ioo (0 : ℝ) 1,
          (ν : Measure C(Rd d × Rd d, ℝ)) =
            P.map (fun ω => toCMapRd ((aEps κ ξ ε)⁻¹ •
              lfppDist κ ξ ε (h ω)))} →
      ∀ᵐ E ∂(μ : Measure C(Rd d × Rd d, ℝ)), IsContLengthFn E

/-- On the almost-sure Lemma 3.6 event, the measurable patch has one
simultaneous Weyl identity for all continuous perturbations. -/
theorem l8_ae_patch_addFun_eq_weyl
    (h36 : L8Lemma36TruncInput)
    {d : ℕ} (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (hL2c : L2c_trunc)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (Dh : Ω → ContMetric d) (hh : IsNormalizedLGF h P)
    (hgood : ∀ᵐ ω ∂P, (Dh ω).IsLength ∧ IsProperFn (Dh ω).1)
    (hae : ∀ᵐ ω ∂P,
      Tendsto (fun n => lfppSeq κ ξ εs (h ω) n) atTop (𝓝 (Dh ω).1)) :
    ∀ᵐ ω ∂P, ∃ hD : (Dh ω).IsLength,
      ∀ f : C(Rd d, ℝ),
        l8_patch hd hκ ξ εs hεs (addFun (h ω) f) =
          weylMetric ξ f (Dh ω) hD := by
  have hlim : ∀ᵐ ω ∂P, (Dh ω).IsLength ∧ IsProperFn (Dh ω).1 ∧
      ∀ R : ℝ, 0 < R → TendstoUniformlyOn
        (fun n => ⇑(lfppSeq κ ξ εs (h ω) n))
        ⇑(Dh ω).1 atTop
        (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) := by
    filter_upwards [hgood, hae] with ω hω ht
    refine ⟨hω.1, hω.2, ?_⟩
    intro R _
    exact (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp ht) _
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hevent := h36 hd κ hκ ξ hL2c εs hεs hεt P h Dh hh hlim
  filter_upwards [hgood, hevent] with ω hω h36ω
  exact ⟨hω.1, fun f =>
    l8_patch_addFun_eq_weyl_of_lemma36_event hd hκ ξ εs hεs hεt
      (h ω) (Dh ω) hω.1 h36ω f⟩

/-- The A21(1) coupling can be chosen so that A21(4) holds on one event. -/
theorem l8_exists_weyl_coupling
    (hL6a : ∀ d ξ κ, L6a_tight d ξ κ)
    (hLen : L8LengthLimitInput)
    (hL7f : ∀ d ξ κ, L7f_determined d ξ κ)
    (h36 : L8Lemma36TruncInput)
    {d : ℕ} (hd : 2 ≤ d) (ξ : ℝ) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hB2 : ∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (hMarkov : DMarkovRd) (hShell : ShellDecouplingFun)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (_ : IsProbabilityMeasure P) (h : Ω → DistRd d)
        (Dh : Ω → ContMetric d),
        IsNormalizedLGF h P ∧ Measurable Dh ∧
          (∀ᵐ ω ∂P, (Dh ω).IsLength ∧ IsProperFn (Dh ω).1) ∧
          LQGMetric.AEDeterminedBy Dh h P ∧
          StablyTendstoLU P h
            (fun n ω => lfppSeq κ ξ (εs ∘ φ) (h ω) n)
            (fun ω => (Dh ω).1) ∧
          (∀ᵐ ω ∂P, ∃ hD : (Dh ω).IsLength,
            ∀ f : C(Rd d, ℝ),
              l8_patch hd hκ ξ (εs ∘ φ) (fun n => hεs (φ n))
                (addFun (h ω) f) = weylMetric ξ f (Dh ω) hD) ∧
          (∀ᵐ ω ∂P, Tendsto
            (fun n => lfppSeq κ ξ (εs ∘ φ) (h ω) n)
            atTop (𝓝 (Dh ω).1)) := by
  obtain ⟨φ, hφ, Ω, mΩ, P, hP, h, Dh, hh, hDm, hgood, hdet, hstable, hae⟩ :=
    l8_exists_good_coupling hL6a hLen hL7f hd ξ κ hB2
      hMarkov hShell εs hεs hεt
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure P := hP
  have hεφt : Tendsto (εs ∘ φ) atTop (𝓝 0) :=
    hεt.comp hφ.tendsto_atTop
  have hweyl := l8_ae_patch_addFun_eq_weyl h36 hd κ hκ ξ
    l2c_trunc (εs ∘ φ) (fun n => hεs (φ n)) hεφt
    P h Dh hh hgood hae
  exact ⟨φ, hφ, Ω, mΩ, P, hP, h, Dh, hh, hDm,
    hgood, hdet, hstable, hweyl, hae⟩

theorem l8_weylMetric_zero {d : ℕ} (ξ : ℝ) (D : ContMetric d)
    (hD : D.IsLength) : weylMetric ξ 0 D hD = D := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  rw [weylMetric_apply, show (0 : C(Rd d, ℝ)) =
    ContinuousMap.const (Rd d) 0 from rfl,
    weylScale_const_of_isLength hD]
  simp only [mul_zero, Real.exp_zero, one_mul,
    ENNReal.toReal_ofReal (D.nonneg p.1 p.2)]

theorem l8_patch_eq_of_weyl_event
    {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (g : DistRd d) (D : ContMetric d) (hD : D.IsLength)
    (hW : ∀ f : C(Rd d, ℝ),
      l8_patch hd hκ ξ εs hεs (addFun g f) = weylMetric ξ f D hD) :
    l8_patch hd hκ ξ εs hεs g = D := by
  simpa only [addFun_zero, l8_weylMetric_zero] using hW 0

end HigherDimLQGMetric
