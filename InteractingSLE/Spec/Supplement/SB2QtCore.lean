/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2QtBaseLaw

/-!
# The retained law given finer marks: the probabilistic core of every stage of SB2(2)'s induction

Worker REVIEW-FABLE-T14 (orchestrator split of PROVE-SB2-LCMEAN's handoff R13.8, items 2–3).

Every stage of SB2(2)'s retained-law induction has the same probabilistic core as its base
(`Qt.sb2LowerBaseLawStatement_of_head`): a conditional GFF law of the field read in a canonical hull chart is known
given **coarse** marks `m` (the upper past at the base; the previous stage's marks and the relative record of the
last piece at a later stage), and is wanted given **finer** marks `ℋ` (the kernel half's `lineFiltC`), on an event
`G ∈ ℋ` on which a set `A`, marked local for `ℋ`, is the hull of the chart.

* **`ae_isGFF_of_coarse_of_marked`**: then, almost surely on `G`, the field is under the regular conditional law given
  `ℋ` a GFF with the same word. (The marked Gaussian kernel of `A` read in the chart; the nested Gaussian identity on
  the event `G`, which lies in the finer σ-algebra only; the tower property.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Qt

open Restart Exist Exist.Staged Exist.StagedLaw LocalSets WholeField

/-- **The retained law given finer marks.** Let `m ≤ ℋ ≤ mΩ`. Let `K` be a random compact set, `K ∪ {im ≤ 0}`
preconnected, dyadic-hit measurable for `ℋ`, and `Y` the field `h` read in `Mo.hullChart (fill K) 0`. Suppose that
almost surely on `L ∈ m`, given `m`, `Y` is a GFF with the data of a sorted `m`-measurable word `β`; that `A` is a
relatively closed local set of the centred field, history-avoidance local for `ℋ`; and that `A = fill K` on
`G ∈ ℋ`, `G ⊆ L`. Then almost surely on `G`, given `ℋ`, `Y` is a GFF with the data of `β`. -/
theorem ae_isGFF_of_coarse_of_marked {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    {m ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (hmℋ : m ≤ ℋ) (hℋ : ℋ ≤ mΩ)
    {K : Ω → Set ℂ} (hKm : @IsDyadicHitMeasurable Ω ℋ K) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) {Y : Ω → DistOn upperHalfPlaneOpens}
    (hYm : Measurable Y) (hYt : ∀ ω, IsChartTransport (Mo.hullChart (fillH (K ω)) 0) 1 0 (chiC κ) (h ω) (Y ω))
    {β : Ω → BoundaryWord} (hβm : Measurable[m] β) (hβs : ∀ ω, (β ω).IsSorted) {L : Set Ω}
    (hL : MeasurableSet[m] L)
    (hlaw : ∀ᵐ ω₀ ∂P, ω₀ ∈ L → IsGFFWithBoundaryData (condExpKernel P m ω₀) Y (β ω₀).fn (β ω₀).jumps)
    {A : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A) (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (hAloc : IsHistoryAvoidanceLocal ℋ A (centredField h u₀) P) (hAl : IsLocalSet A (centredField h u₀) P)
    {G : Set Ω} (hG : MeasurableSet[ℋ] G) (hGL : G ⊆ L) (hGA : ∀ ω ∈ G, A ω = fillH (K ω)) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ G → IsGFFWithBoundaryData (condExpKernel P ℋ ω₀) Y (β ω₀).fn (β ω₀).jumps := by
  classical
  have hm : m ≤ mΩ := hmℋ.trans hℋ
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hh0 hAm hAl
  have hm₂ : germSigma A (centredField h u₀) ⊔ ℋ ≤ mΩ := sup_le (germSigma_le hAm hh0.measurable) hℋ
  have hGm₂ : MeasurableSet[germSigma A (centredField h u₀) ⊔ ℋ] G := (le_sup_right : ℋ ≤ _) _ hG
  have hc := Mu.isConformal_canon (fun _ => (0 : ℝ)) hKc hKp
  have hKm₂ : @IsDyadicHitMeasurable Ω (germSigma A (centredField h u₀) ⊔ ℋ) K :=
    fun n j => (le_sup_right : ℋ ≤ _) _ (hKm n j)
  obtain ⟨-, hliftc, -, hdomm, hfwdm, hliftm⟩ :=
    @Mt.hullChart_k2Inputs Ω (germSigma A (centredField h u₀) ⊔ ℋ) K (fun _ => 0) hKm₂ hKc hKp measurable_const
  have hYeq : ∀ ω, Y ω = Chart.chartTransport (hc ω) 1 0 (chiC κ) (h ω) := fun ω =>
    (hYt ω).unique (hc ω) (Chart.isChartTransport_chartTransport (hc ω) (Chart.locallyIntegrableOn_of_continuousOn
      (Mu.continuousOn_lift_inv_hullChart (Mo.isHPHull_fillH hKc hKp ω) 0)) 1 0 (chiC κ) (h ω))
  set Mf : Ω → DistOn upperHalfPlaneOpens := fun ω => g ω + (h ω - centredField h u₀ ω) with hMfdef
  have hMφ : ∀ ω φ, Mf ω φ = g ω φ + ∫ z, u₀ z * φ z := fun ω φ => by
    simp only [hMfdef, add_apply, sub_apply, WholeField.centredField_apply h hu₀.1 ω φ]
    ring
  have hMm : Measurable[germSigma A (centredField h u₀) ⊔ ℋ] Mf := by
    let _ : MeasurableSpace Ω := germSigma A (centredField h u₀) ⊔ ℋ
    refine LQGMetric.measurable_distOn_iff.2 fun φ => ?_
    have e : (fun ω => Mf ω φ) = fun ω => g ω φ + ∫ z, u₀ z * φ z := funext fun ω => hMφ ω φ
    rw [e]
    exact (((LQGMetric.measurable_distOn_apply φ).comp hg.1).mono le_sup_left le_rfl).add_const _
  have hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ G →
      tsupport φ ⊆ ((Mo.hullChart (fillH (K ω)) 0).dom : Set ℂ) →
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | germSigma A (centredField h u₀) ⊔ ℋ] ω =
        Complex.exp (Complex.I * (Mf ω φ : ℂ) -
          (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov ((Mo.hullChart (fillH (K ω)) 0).dom : Set ℂ) φ φ : ℝ) : ℂ)) := by
    intro φ
    set cst : ℂ := Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) with hcst
    have hfun : (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) =
        cst • fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)) := by
      funext ω'
      rw [Pi.smul_apply, smul_eq_mul, hcst, ← Complex.exp_add, WholeField.centredField_apply h hu₀.1 ω' φ]
      congr 1
      push_cast
      ring
    filter_upwards [Supp8.RelSafeS.ae_condExp_cexp_marked hh0 hAm hAc hℋ hAloc hg φ,
      condExp_smul (m := germSigma A (centredField h u₀) ⊔ ℋ) (μ := P) cst
        (fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)))] with ω hω hsm hωG _
    have hdom : ((Mo.hullChart (fillH (K ω)) 0).dom : Set ℂ) = H \ A ω := by
      rw [Mo.coe_dom_hullChart (Mo.isHPHull_fillH hKc hKp ω) 0, hGA ω hωG]
    rw [hfun, hsm, Pi.smul_apply, hω, hdom, smul_eq_mul, hcst, hMφ, Complex.ofReal_exp, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hfine := fun ψ => Restart.ae_condExp_cexp_chartTransport_random_on hm₂ hc hdomm hfwdm hliftm hliftc hh.1
    (chiC κ) hGm₂ hcond ψ
  have hmm₂ : m ≤ germSigma A (centredField h u₀) ⊔ ℋ := hmℋ.trans le_sup_right
  have hM' : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable[germSigma A (centredField h u₀) ⊔ ℋ]
      fun ω => Chart.chartTransport (hc ω) 1 0 (chiC κ) (Mf ω) ψ := fun ψ =>
    (LQGMetric.measurable_distOn_apply ψ).comp
      (@Chart.measurable_chartTransport_random' Ω (germSigma A (centredField h u₀) ⊔ ℋ)
        _ hc hdomm hfwdm hliftm hliftc _ hMm 1 0 (chiC κ))
  have hcoarse := fun ψ => S3.ae_condExp_gaussCF_of_kernel hm hYm (Eventually.of_forall fun ω _ => hβs ω) hlaw ψ
  have hH : (upperHalfPlaneOpens : Set ℂ) = H := rfl
  have hnest : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ G →
      P[fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ)) | germSigma A (centredField h u₀) ⊔ ℋ] ω =
        gaussCF (β ω) ψ := by
    refine Qt.ae_condExp_cexp_eq_gaussCF_of_le_on hmm₂ hm₂ hYm hβm hM' hL hGm₂ hGL hcoarse (fun ψ => ?_)
    have hY' : (fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ))) =
        fun ω' => Complex.exp (Complex.I * (Chart.chartTransport (hc ω') 1 0 (chiC κ) (h ω') ψ : ℂ)) := by
      funext ω'
      rw [hYeq ω']
    filter_upwards [hfine ψ] with ω hω hωG
    rw [hY', hω hωG, hH]
    congr 1
    push_cast
    ring
  have hgiven : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ G →
      P[fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ)) | ℋ] ω = gaussCF (β ω) ψ := fun ψ =>
    Restart.ae_condExp_eq_on_of_le le_sup_right hm₂
      (GFF.integrable_exp_I_mul (P := P) ((LQGMetric.measurable_distOn_apply ψ).comp hYm))
      ((Restart.measurable_gaussCF ψ).comp (hβm.mono hmℋ le_rfl)).stronglyMeasurable
      (fun ω => Restart.norm_gaussCF_le _ ψ) hG (hnest ψ)
  exact Exist.StagedLaw.ae_isGFFWithBoundaryData_condExpKernel hℋ (Eventually.of_forall fun ω _ => hβs ω) hYm hgiven

end InteractingSLE.Theorem14.SB.Qt
