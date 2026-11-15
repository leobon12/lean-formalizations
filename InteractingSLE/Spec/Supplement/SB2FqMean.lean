/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FmBase
import InteractingSLE.Spec.Supplement.SB2QtNested
import InteractingSLE.Spec.Supplement.SB2MtChart
import InteractingSLE.GFF.LocalSets.Prop38

/-!
# F3's mean identity from the retained law

Worker PROVE-SB2-F3LAW (round 5, D76: CANON's (P1)). F2b′'s successor statements (`Cz.…Statement6E`, `Ne.…9E`),
D34's reduction `Fm.ae_heightClause_of_leftAdm` and CONDFIN's K2 inputs (`hF3`) take **F3's mean identity** of the
retained set `A` as a premise: for every local-set mean `g₁` of `A`, almost surely, every harmonic representative `w₁`
of `g₁` off `A` satisfies `w₁ + u₀ = β.mean ∘ (hullChart A 0).1 − χ · (hullChart A 0).2.2` on `ℍ ∖ A`. Here it is
derived from the retained law `Fl.MvLaw` on its event `G`, for any marks `𝓗` relative to which `A` is a
history-avoidance-local set:

* `ae_mean_eq_of_le_on`: the mean form of REVIEW-FABLE-T14's nested Gaussian identity
  (`Qt.ae_condExp_cexp_eq_gaussCF_of_le_on`, same proof): the finer Gaussian mean equals the coarser word's mean;
* `ae_condExp_congr_on`: conditional expectations of a.s. equal variables agree on an event of the σ-algebra;
* **`ae_meanIdentity_of_mvLaw`**: the finer σ-algebra is `germSigma A ⊔ 𝓗`; there the field's characteristic
  functional has the local-set mean (`Supp8.RelSafeS.ae_condExp_cexp_marked`), read in the chart
  (`Restart.ae_condExp_cexp_chartTransport_random_on`); the coarser one is the law's word; the two means agree on
  countably many bumps of `ℍ`, both sides are harmonic, so they agree on `ℍ`, hence on `ℍ ∖ A` through the chart.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Fq

open Restart Exist Exist.Staged Exist.StagedLaw LocalSets WholeField

section Nested

variable {Ω : Type*} {m m' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω}

open LQGMetric QuantumZipper Restart in
/-- **The mean form of the nested Gaussian identity**: under the hypotheses of `Qt.ae_condExp_cexp_eq_gaussCF_of_le_on`
the finer mean distribution `M'` pairs with `ψ` as the coarser word's mean, almost surely on `G`. -/
theorem ae_mean_eq_of_le_on [IsProbabilityMeasure P] (hm : m ≤ m') (hm' : m' ≤ mΩ)
    {Y : Ω → DistOn upperHalfPlaneOpens} (hY : Measurable Y) {β : Ω → BoundaryWord} (hβ : Measurable[m] β)
    {M' : Ω → DistOn upperHalfPlaneOpens}
    (hM' : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable[m'] fun ω => M' ω ψ)
    {L G : Set Ω} (hL : MeasurableSet[m] L) (hG : MeasurableSet[m'] G) (hGL : G ⊆ L)
    (hc : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ L →
      P[fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ)) | m] ω = gaussCF (β ω) ψ)
    (hf : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ G →
      P[fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ)) | m'] ω =
        Complex.exp (Complex.I * (M' ω ψ : ℂ) -
          (zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) ψ ψ : ℂ) / 2))
    (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ G → M' ω ψ = ∫ z, (β ω).mean z * ψ z := by
  have hH : (upperHalfPlaneOpens : Set ℂ) = H := rfl
  have hXm : Measurable fun ω => Y ω ψ := (measurable_distOn_apply ψ).comp hY
  have hcov0 : 0 ≤ zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) ψ ψ := by
    rw [hH, LocalExt.zeroGFFTestCov_self_eq_norm_sq isOpen_H Subset.rfl]
    positivity
  have hfun : ∀ t : ℝ, (fun ω' => Complex.exp ((t : ℂ) * ((Y ω' ψ : ℝ) : ℂ) * Complex.I)) =
      fun ω' => Complex.exp (Complex.I * ((Y ω' (t • ψ) : ℝ) : ℂ)) := by
    intro t
    funext ω'
    rw [map_smul, smul_eq_mul]
    congr 1
    push_cast
    ring
  have hcovt : ∀ t : ℝ, zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) ⇑(t • ψ) ⇑(t • ψ) =
      t ^ 2 * zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) ψ ψ := fun t => by
    rw [hH]
    exact LocalSets.zeroGFFTestCov_smul_self isOpen_H Subset.rfl t ψ
  have hmeant : ∀ (t : ℝ) (c : BoundaryWord), ∫ z, c.mean z * (t • ψ) z = t * ∫ z, c.mean z * ψ z := by
    intro t c
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show c.mean z * (t • ψ) z = t * (c.mean z * ψ z)
    rw [show (t • ψ) z = t * ψ z from rfl]
    ring
  -- the two Gaussian conditional characteristic functions of the pairing `Y ψ`
  have hc' : ∀ t : ℝ, ∀ᵐ ω ∂P, ω ∈ L →
      P[fun ω' => Complex.exp ((t : ℂ) * ((Y ω' ψ : ℝ) : ℂ) * Complex.I) | m] ω =
        Complex.exp ((t : ℂ) * ((∫ z, (β ω).mean z * ψ z : ℝ) : ℂ) * Complex.I -
          (((zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) ψ ψ).toNNReal : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) := by
    intro t
    filter_upwards [hc (t • ψ)] with ω hω hωL
    rw [hfun t, hω hωL, gaussCF, hcovt, hmeant, Real.coe_toNNReal _ hcov0]
    congr 1
    push_cast
    ring
  have hf' : ∀ t : ℝ, ∀ᵐ ω ∂P, ω ∈ G →
      P[fun ω' => Complex.exp ((t : ℂ) * ((Y ω' ψ : ℝ) : ℂ) * Complex.I) | m'] ω =
        Complex.exp ((t : ℂ) * ((M' ω ψ : ℝ) : ℂ) * Complex.I -
          (((zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) ψ ψ).toNNReal : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) := by
    intro t
    filter_upwards [hf (t • ψ)] with ω hω hωG
    rw [hfun t, hω hωG, hcovt, map_smul, smul_eq_mul, Real.coe_toNNReal _ hcov0]
    congr 1
    push_cast
    ring
  have hcK := Qt.ae_map_condExpKernel_eq_gaussianReal (hm.trans hm') hXm hc'
  have hfK := Qt.ae_map_condExpKernel_eq_gaussianReal hm' hXm hf'
  have hμ : Measurable[m] fun ω => ∫ z, (β ω).mean z * ψ z :=
    (BoundaryWord.measurable_integral_mean_mul ψ).comp hβ
  exact Qt.ae_eq_of_gaussian_le_on hm hm' hXm hμ (hM' ψ) hL hG hGL hcK hfK

end Nested

/-- **Conditional expectations of variables equal almost surely on an event of the σ-algebra agree there.** -/
theorem ae_condExp_congr_on {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f f' : Ω → ℂ} (hf : Integrable f P) (hf' : Integrable f' P)
    {G : Set Ω} (hG : MeasurableSet[m] G) (he : ∀ᵐ ω ∂P, ω ∈ G → f ω = f' ω) :
    ∀ᵐ ω ∂P, ω ∈ G → P[f | m] ω = P[f' | m] ω := by
  have h1 := condExp_indicator (m := m) hf hG
  have h2 := condExp_indicator (m := m) hf' hG
  have h3 : G.indicator f =ᵐ[P] G.indicator f' := by
    filter_upwards [he] with ω hω
    by_cases hωG : ω ∈ G
    · rw [indicator_of_mem hωG, indicator_of_mem hωG, hω hωG]
    · rw [indicator_of_notMem hωG, indicator_of_notMem hωG]
  have h4 := condExp_congr_ae (m := m) h3
  filter_upwards [h1, h2, h4] with ω e1 e2 e4 hωG
  have := e1.symm.trans (e4.trans e2)
  rwa [indicator_of_mem hωG, indicator_of_mem hωG] at this

open LQGMetric QuantumZipper Restart Theorem14.SB in
/-- **F3's mean identity from the retained law.** See the module docstring. -/
theorem ae_meanIdentity_of_mvLaw {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    {𝓗 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (h𝓗 : 𝓗 ≤ mΩ)
    {A : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A) (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (hloc : IsHistoryAvoidanceLocal 𝓗 A (centredField h u₀) P)
    {K : Ω → Set ℂ} {G : Set Ω} {Y : Ω → DistOn upperHalfPlaneOpens} {β : Ω → BoundaryWord} {M : ℝ}
    (hlaw : Fl.MvLaw κ 𝓗 P h A K G Y β M) :
    ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A (centredField h u₀) P g₁ →
      ∀ᵐ ω ∂P, ω ∈ G → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
        EqOn (fun z => w₁ z + u₀ z)
          (fun z => (β ω).mean ((Mo.hullChart (A ω) 0).1 z) - chiC κ * (Mo.hullChart (A ω) 0).2.2 z)
          (H \ A ω) := by
  intro g₁ hg₁
  obtain ⟨hKm, hKc, hKp, hGm, hfill, hYm, hYt, hβm, hβs, -, -, hlawY⟩ := hlaw
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hm₂ : germSigma A (centredField h u₀) ⊔ 𝓗 ≤ mΩ := sup_le (germSigma_le hAm hh0.measurable) h𝓗
  have hle : 𝓗 ≤ germSigma A (centredField h u₀) ⊔ 𝓗 := le_sup_right
  have hc := Mu.isConformal_canon (fun _ => (0 : ℝ)) hKc hKp
  have hKm₂ : @IsDyadicHitMeasurable Ω (germSigma A (centredField h u₀) ⊔ 𝓗) K := fun n j => hle _ (hKm n j)
  obtain ⟨-, hliftc, -, hdomm, hfwdm, hliftm⟩ :=
    @Mt.hullChart_k2Inputs Ω (germSigma A (centredField h u₀) ⊔ 𝓗) K (fun _ => 0) hKm₂ hKc hKp measurable_const
  -- the mean of the field given the finer σ-algebra
  set Mg : Ω → DistOn upperHalfPlaneOpens := fun ω => g₁ ω + (h ω - centredField h u₀ ω) with hMgdef
  have hMφ : ∀ ω φ, Mg ω φ = g₁ ω φ + ∫ z, u₀ z * φ z := fun ω φ => by
    simp only [hMgdef, add_apply, sub_apply, WholeField.centredField_apply h hu₀.1 ω φ]
    ring
  have hMm : Measurable[germSigma A (centredField h u₀) ⊔ 𝓗] Mg := by
    let _ : MeasurableSpace Ω := germSigma A (centredField h u₀) ⊔ 𝓗
    refine LQGMetric.measurable_distOn_iff.2 fun φ => ?_
    have e : (fun ω => Mg ω φ) = fun ω => g₁ ω φ + ∫ z, u₀ z * φ z := funext fun ω => hMφ ω φ
    rw [e]
    exact (((LQGMetric.measurable_distOn_apply φ).comp hg₁.1).mono le_sup_left le_rfl).add_const _
  have hGm₂ : MeasurableSet[germSigma A (centredField h u₀) ⊔ 𝓗] G := hle _ hGm
  have hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ G →
      tsupport φ ⊆ ((Mo.hullChart (fillH (K ω)) 0).dom : Set ℂ) →
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | germSigma A (centredField h u₀) ⊔ 𝓗] ω =
        Complex.exp (Complex.I * (Mg ω φ : ℂ) -
          (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov ((Mo.hullChart (fillH (K ω)) 0).dom : Set ℂ) φ φ : ℝ) :
            ℂ)) := by
    intro φ
    set cst : ℂ := Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) with hcst
    have hfun : (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) =
        cst • fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)) := by
      funext ω'
      rw [Pi.smul_apply, smul_eq_mul, hcst, ← Complex.exp_add, WholeField.centredField_apply h hu₀.1 ω' φ]
      congr 1
      push_cast
      ring
    filter_upwards [Supp8.RelSafeS.ae_condExp_cexp_marked hh0 hAm hAc h𝓗 hloc hg₁ φ,
      condExp_smul (m := germSigma A (centredField h u₀) ⊔ 𝓗) (μ := P) cst
        (fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ))), hfill] with ω hω hsm hfω hωG _
    have hdom : ((Mo.hullChart (fillH (K ω)) 0).dom : Set ℂ) = H \ A ω := by
      rw [Mo.coe_dom_hullChart (Mo.isHPHull_fillH hKc hKp ω) 0, hfω hωG]
    rw [hfun, hsm, Pi.smul_apply, hω, hdom, smul_eq_mul, hcst, hMφ, Complex.ofReal_exp, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hfine := fun ψ => Restart.ae_condExp_cexp_chartTransport_random_on hm₂ hc hdomm hfwdm hliftm hliftc hh.1
    (chiC κ) hGm₂ hcond ψ
  -- the exact chart field and the law's field agree on `G`
  have hY'm : Measurable fun ω => Chart.chartTransport (hc ω) 1 0 (chiC κ) (h ω) :=
    Chart.measurable_chartTransport_random' hc (fun z => hm₂ _ (hdomm z)) (fun z => (hfwdm z).mono hm₂ le_rfl)
      (fun z => (hliftm z).mono hm₂ le_rfl) hliftc hh.1 1 0 (chiC κ)
  have hYY' : ∀ᵐ ω ∂P, ω ∈ G → Y ω = Chart.chartTransport (hc ω) 1 0 (chiC κ) (h ω) := by
    filter_upwards [hYt] with ω hω hωG
    exact (hω hωG).unique (hc ω) (Chart.isChartTransport_chartTransport (hc ω)
      (Chart.locallyIntegrableOn_of_continuousOn (Mu.continuousOn_lift_inv_hullChart
        (Mo.isHPHull_fillH hKc hKp ω) 0)) 1 0 (chiC κ) (h ω))
  have hcoarse : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ G →
      P[fun ω' => Complex.exp (Complex.I * (Chart.chartTransport (hc ω') 1 0 (chiC κ) (h ω') ψ : ℂ)) | 𝓗] ω =
        gaussCF (β ω) ψ := by
    intro ψ
    have h1 := S3.ae_condExp_gaussCF_of_kernel h𝓗 hYm (Eventually.of_forall fun ω _ => hβs ω) hlawY ψ
    have h2 := ae_condExp_congr_on (m := 𝓗) (f := fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ)))
      (f' := fun ω' => Complex.exp (Complex.I * (Chart.chartTransport (hc ω') 1 0 (chiC κ) (h ω') ψ : ℂ)))
      (GFF.integrable_exp_I_mul (P := P) ((LQGMetric.measurable_distOn_apply ψ).comp hYm))
      (GFF.integrable_exp_I_mul (P := P) ((LQGMetric.measurable_distOn_apply ψ).comp hY'm)) hGm
      (by filter_upwards [hYY'] with ω hω hωG; rw [hω hωG])
    filter_upwards [h1, h2] with ω e1 e2 hωG
    rw [← e2 hωG, e1 hωG]
  have hM' : ∀ ψ : TestOn upperHalfPlaneOpens,
      Measurable[germSigma A (centredField h u₀) ⊔ 𝓗]
        fun ω => Chart.chartTransport (hc ω) 1 0 (chiC κ) (Mg ω) ψ := fun ψ =>
    (LQGMetric.measurable_distOn_apply ψ).comp
      (@Chart.measurable_chartTransport_random' Ω (germSigma A (centredField h u₀) ⊔ 𝓗)
        _ hc hdomm hfwdm hliftm hliftc _ hMm 1 0 (chiC κ))
  have hmeq := fun ψ => ae_mean_eq_of_le_on hle hm₂ hY'm hβm hM' hGm hGm₂ subset_rfl hcoarse (fun ψ => by
    filter_upwards [hfine ψ] with ω hω hωG
    have hH : (upperHalfPlaneOpens : Set ℂ) = H := rfl
    rw [hω hωG, hH]
    congr 1
    push_cast
    ring) ψ
  -- countably many bumps
  set x : ℕ → ℂ := TopologicalSpace.denseSeq ℂ with hx
  have hδ : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hall : ∀ᵐ ω ∂P, ∀ p : ℕ × ℕ,
      ∀ hB : closedBall (x p.1) (1 / ((p.2 : ℝ) + 1)) ⊆ (upperHalfPlaneOpens : Set ℂ), ω ∈ G →
        Chart.chartTransport (hc ω) 1 0 (chiC κ) (Mg ω) (GFF.bumpTest (x p.1) (hδ p.2) hB) =
          ∫ z, (β ω).mean z * GFF.bumpTest (x p.1) (hδ p.2) hB z := by
    refine ae_all_iff.2 fun p => ?_
    by_cases hB : closedBall (x p.1) (1 / ((p.2 : ℝ) + 1)) ⊆ (upperHalfPlaneOpens : Set ℂ)
    · filter_upwards [hmeq (GFF.bumpTest (x p.1) (hδ p.2) hB)] with ω hω hB' hωG
      exact hω hωG
    · exact Eventually.of_forall fun ω hB' => absurd hB' hB
  filter_upwards [hall, hfill] with ω hω hfω hωG w₁ hw₁ hrep
  have hA : A ω = fillH (K ω) := (hfω hωG).symm
  rw [hA] at hw₁ hrep ⊢
  set c := Mo.hullChart (fillH (K ω)) 0 with hcdef
  have hcω : c.IsConformal := hc ω
  have hHP := Mo.isHPHull_fillH hKc hKp ω
  have hdom : (c.dom : Set ℂ) = H \ fillH (K ω) := Mo.coe_dom_hullChart hHP 0
  have hU : IsOpen (H \ fillH (K ω)) := hdom ▸ c.dom.isOpen
  have hu₀h : InnerProductSpace.HarmonicOnNhd u₀ H := hu₀.1
  have hmaps : MapsTo c.2.1 H (H \ fillH (K ω)) := fun y hy => hdom ▸ hcω.inv_mem_dom hy
  -- the two harmonic functions on `ℍ`
  set F : ℂ → ℝ := fun y => (w₁ (c.2.1 y) + u₀ (c.2.1 y)) + chiC κ * c.2.2 (c.2.1 y) with hFdef
  have hWh : InnerProductSpace.HarmonicOnNhd (fun z => w₁ z + u₀ z) (H \ fillH (K ω)) := fun z hz =>
    (hw₁ z hz).add (hu₀h z hz.1)
  have hF1 := LQGMetric.harmonicOnNhd_comp_holo hU isOpen_H hWh hcω.1 hmaps
  have hL : InnerProductSpace.HarmonicOnNhd c.2.2 (H \ fillH (K ω)) := hdom ▸ Mt.harmonicOnNhd_lift_hullChart hHP 0
  have hF2 := LQGMetric.harmonicOnNhd_comp_holo hU isOpen_H hL hcω.1 hmaps
  have hF : InnerProductSpace.HarmonicOnNhd F H := fun y hy =>
    (hF1 y hy).add (InnerProductSpace.HarmonicAt.const_smul (hF2 y hy) :
      InnerProductSpace.HarmonicAt (chiC κ • (c.2.2 ∘ c.2.1)) y)
  have hBh : InnerProductSpace.HarmonicOnNhd (β ω).mean H := by
    rw [BoundaryWord.mean_eq_harmonicExtH (β ω) (hβs ω)]
    exact StepData.harmonicOnNhd_harmonicExtH _
  -- the finer mean read as the function `F`
  have hcont1 : ContinuousOn (fun y => w₁ (c.2.1 y) + u₀ (c.2.1 y)) H := fun y hy =>
    (hF1 y hy).1.continuousAt.continuousWithinAt
  have hcont2 : ContinuousOn (fun y => c.2.2 (c.2.1 y)) H := Mu.continuousOn_lift_inv_hullChart hHP 0
  have hpair : ∀ ψ : TestOn upperHalfPlaneOpens,
      Chart.chartTransport hcω 1 0 (chiC κ) (Mg ω) ψ = ∫ y, F y * ψ y := by
    intro ψ
    have hℓ := Chart.locallyIntegrableOn_of_continuousOn hcont2
    have hts : tsupport (Chart.pushTest hcω ψ) ⊆ H \ fillH (K ω) := hdom ▸ Chart.tsupport_pushTest_subset hcω ψ
    rw [Chart.chartTransport_apply hcω hℓ, hMφ, hrep _ hts]
    have hi1 : Integrable fun z => w₁ z * Chart.pushTest hcω ψ z :=
      LocalSets.integrable_mul_test hU (fun z hz => (hw₁ z hz).1.continuousAt.continuousWithinAt) _ hts
    have hi2 : Integrable fun z => u₀ z * Chart.pushTest hcω ψ z :=
      LocalSets.integrable_mul_test isOpen_H (fun z hz => (hu₀h z hz).1.continuousAt.continuousWithinAt) _
        (hts.trans sdiff_subset)
    rw [← integral_add hi1 hi2]
    have e1 := Chart.integral_mul_pushTest hcω ψ (fun z => w₁ z + u₀ z)
    have e2 : (fun z => w₁ z * Chart.pushTest hcω ψ z + u₀ z * Chart.pushTest hcω ψ z) =
        fun z => (w₁ z + u₀ z) * Chart.pushTest hcω ψ z := funext fun z => by ring
    rw [e2, e1]
    have hψH : tsupport ψ ⊆ H := ψ.tsupport_subset
    have hi3 : Integrable fun y => (w₁ (c.2.1 y) + u₀ (c.2.1 y)) * ψ y :=
      LocalSets.integrable_mul_test isOpen_H hcont1 ψ hψH
    have hi4 : Integrable fun y => c.2.2 (c.2.1 y) * ψ y := LocalSets.integrable_mul_test isOpen_H hcont2 ψ hψH
    have e3 : (∫ y, F y * ψ y) = ∫ y, ((w₁ (c.2.1 y) + u₀ (c.2.1 y)) * ψ y + chiC κ * (c.2.2 (c.2.1 y) * ψ y)) :=
      integral_congr_ae (Eventually.of_forall fun y => by simp only [hFdef]; ring)
    rw [e3, integral_add hi3 (hi4.const_mul _), integral_const_mul]
    ring
  -- the two harmonic functions agree at the dense points, hence on `ℍ`
  have hval : ∀ k n : ℕ, ∀ hB : closedBall (x k) (1 / ((n : ℝ) + 1)) ⊆ (upperHalfPlaneOpens : Set ℂ),
      F (x k) = (β ω).mean (x k) := by
    intro k n hB
    have e := hω (k, n) hB hωG
    have hB' : closedBall (x k) (1 / ((n : ℝ) + 1)) ⊆ H := hB
    rw [hpair, GFF.coe_bumpTest, GFF.integral_mul_bumpFun_of_harmonic isOpen_H hF (hδ n) hB',
      GFF.integral_mul_bumpFun_of_harmonic isOpen_H hBh (hδ n) hB'] at e
    have : 0 < (1 / ((n : ℝ) + 1)) ^ 2 * GFF.bumpMass := by
      have := GFF.bumpMass_pos; have := hδ n; positivity
    exact mul_right_cancel₀ this.ne' e
  have heqH : ∀ z ∈ H, F z = (β ω).mean z := by
    intro z hz
    by_contra hne
    have hd : 0 < |F z - (β ω).mean z| := abs_pos.2 (sub_ne_zero.2 hne)
    have hcz : ContinuousAt (fun w => F w - (β ω).mean w) z :=
      (hF z hz).1.continuousAt.sub (hBh z hz).1.continuousAt
    obtain ⟨η, hη, hηc⟩ := Metric.continuousAt_iff.1 hcz _ hd
    obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.1 isOpen_H z hz
    set r := min η ρ with hr
    have hr0 : 0 < r := lt_min hη hρ
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.1 (TopologicalSpace.denseRange_denseSeq ℂ) z (r / 2)
      (half_pos hr0)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hr0)
    have hsub : closedBall (x k) (1 / ((n : ℝ) + 1)) ⊆ H := by
      intro w hw
      refine hρO ?_
      rw [mem_ball]
      have h1 := dist_triangle w (x k) z
      rw [mem_closedBall] at hw
      have h2 : dist (x k) z < r / 2 := by rw [dist_comm]; exact hk
      have h3 : r ≤ ρ := min_le_right _ _
      linarith
    have hk' := hval k n hsub
    have hdk : dist (x k) z < η := by
      have h2 : dist (x k) z < r / 2 := by rw [dist_comm]; exact hk
      have h3 : r ≤ η := min_le_left _ _
      linarith
    have := hηc hdk
    rw [hk', sub_self, Real.dist_eq, zero_sub, abs_neg] at this
    exact lt_irrefl _ this
  -- back through the chart
  intro z hz
  have hzd : z ∈ c.dom := by rw [← SetLike.mem_coe, hdom]; exact hz
  have e := heqH (c.1 z) (hcω.fwd_mem hzd)
  simp only [hFdef, hcω.inv_fwd hzd] at e
  show w₁ z + u₀ z = (β ω).mean (c.1 z) - chiC κ * c.2.2 z
  linarith

end InteractingSLE.Theorem14.SB.Fq
