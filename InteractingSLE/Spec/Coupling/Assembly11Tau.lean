import InteractingSLE.Spec.Coupling.Assembly11Drv
import InteractingSLE.Spec.Coupling.StopFamily

/-!
# Theorem 1.1, the conditional-law clause at every frozen stopping time

Packet PROVE-T11-ASM (obligation 5 of `planning/handoffs/PROVE-T11-L312.md` §4; Astra §1, "Arbitrary stopping times").
Suppose a field `h` is coupled with an integrated evolution so that it satisfies the protected-kernel constraint
(`IsSampledAt`) on a countable family of stops that exhausts avoidance (the hypotheses of
`setIntegral_cexp_eq_cfAt_of_family`). Then, for every stopping time `τ < ζ` of the frozen `drivingFiltration`,
every choice of the bounded harmonic extensions at `τ` and every test function `φ`, almost surely on
`{supp φ ∩ K_τ = ∅}`,

  `E[exp(i (h, φ)) | 𝓕_τ] = exp(i (𝔥_τ, φ) − ½ E_τ(φ))`,

with `𝓕_τ` the frozen stopped σ-algebra of the driving filtration: this is the conditional-law conjunct of the frozen
`IsOptionalHullCoupling` (`condExp_cexp_eq_frozenRHS_of_family`).

Proof: `setIntegral_cexp_eq_cfAt_of_family` gives the identity on events of the evolution's stopped σ-algebra inside
the avoidance event, which contains the driving `𝓕_τ`; `exists_drivingStopped_measurable` supplies an event
`E' ∈ 𝓕_τ`, almost surely equal to the avoidance event, on which the right-hand side is `𝓕_τ`-measurable; the
conditional expectation of `1_{E'} exp(i (h, φ))` is then `1_{E'}` times the right-hand side.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Coupling

open Ito

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

theorem norm_cexp_I_mul_ofReal (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x

/-- The driving `𝓕_τ` sits inside the evolution's stopped σ-algebra at `τ.untopD 0`. -/
theorem measurableSpace_driving_le_untopD
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) :
    hτ.measurableSpace ≤ (isStoppingTime_untopD_of_drivingFiltration hE hX hτ hτζ).measurableSpace := by
  have hτf : ∀ᵐ ω ∂P, τ ω ≠ ⊤ := hτζ.mono fun _ h => ne_top_of_lt_zeta h
  have hτ'𝓓 : IsStoppingTime (drivingFiltration P hX)
      fun ω => (((τ ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) :=
    isStoppingTime_untopD (𝓕 := killedDrivingFiltration hX) hτ hτf
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 →
      MeasurableSet[drivingFiltration P hX 0] s := fun s hs h0 =>
    measurableSet_usualAugmentation_of_null (𝓕 := killedDrivingFiltration hX) hs h0 0
  rw [measurableSpace_untopD_eq hnull hτ hτf hτ'𝓓]
  exact measurableSpace_le_of_filtration_le (drivingFiltration_le_usualAugmentation hE hX) hτ'𝓓 _

/-- **The conditional-law clause of Theorem 1.1 at every frozen stopping time.** For a field satisfying the
protected-kernel constraint on a countable family of stops that exhausts avoidance, and every stopping time `τ < ζ`
of the frozen driving filtration: for every test function `φ`, almost surely on `{supp φ ∩ K_τ = ∅}`,
`E[exp(i (h, φ)) | 𝓕_τ] = exp(i (𝔥_τ, φ) − ½ E_τ(φ))`. -/
theorem condExp_cexp_eq_frozenRHS_of_family
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
    (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (hh : ∀ ψ, Measurable fun ω => h ω ψ)
    {ι : Type*} [Countable ι] (U : ι → Set ℂ) (s : ι → Ω → ℝ≥0)
    (hs : ∀ i, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (s i ω : WithTop ℝ≥0))
    (hsafe : ∀ i, ∀ᵐ ω ∂P, (s i ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (U i) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s i ω)))
    (hsamp : ∀ i, IsSampledAt κ W u P h (U i) (hs i))
    (hexh : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ K : Set ℂ, IsCompact K → K ⊆ H →
      Disjoint K (fwdHull (fun r : ℝ => W r.toNNReal ω) t) → ∃ i, K ⊆ U i ∧ t ≤ s i ω)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    (uτ : Ω → ℂ → ℝ)
    (huτ : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (uτ ω))
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, Disjoint (tsupport φ)
        (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
      condExp hτ.measurableSpace P (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) ω =
        frozenRHS κ W uτ φ (fun ω => (τ ω).untopD 0) ω := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  set τ' : Ω → ℝ≥0 := fun ω => (τ ω).untopD 0 with hτ'def
  obtain ⟨E', hE'm, hE'sub, hE'ae, hE'mean, hE'path, hE'sm⟩ :=
    exists_drivingStopped_measurable hE hX φ hτ hτζ uτ huτ
  set f : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) with hf
  have hfm : Measurable f :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp (hh φ)))
  have hfint : Integrable f P :=
    Integrable.of_bound hfm.aestronglyMeasurable 1
      (ae_of_all _ fun ω => (norm_cexp_I_mul_ofReal _).le)
  set g : Ω → ℂ := E'.indicator (frozenRHS κ W uτ φ τ') with hg
  -- on `E'` the right-hand side is the characteristic functional at `τ`
  have hcf : ∀ ω ∈ E', frozenRHS κ W uτ φ τ' ω = cfAt κ W u φ 1 τ' ω := fun ω hω => by
    simp only [frozenRHS, cfAt]
    rw [← hE'mean ω hω (u ω (τ' ω)) (hu ω (τ' ω))]
    congr 1
    push_cast
    ring
  have hgb : ∀ ω, ‖g ω‖ ≤ 1 := fun ω => by
    by_cases hω : ω ∈ E'
    · rw [hg, indicator_of_mem hω, hcf ω hω]
      obtain ⟨h1, h2, h3⟩ := hE'path ω hω
      exact norm_cfAt_le_one u 1 φ (r := τ') h1 h2 h3
    · rw [hg, indicator_of_notMem hω, norm_zero]; exact zero_le_one
  have hgm : StronglyMeasurable[hτ.measurableSpace] g := hE'sm
  have hgint : Integrable g P :=
    Integrable.of_bound ((hgm.mono hτ.measurableSpace_le).aestronglyMeasurable) 1
      (ae_of_all _ hgb)
  have hE'mΩ : MeasurableSet E' := hτ.measurableSpace_le _ hE'm
  have hτ𝓖 := isStoppingTime_untopD_of_drivingFiltration hE hX hτ hτζ
  have hσle := measurableSpace_driving_le_untopD hE hX hτ hτζ
  -- the identity on the events of `𝓕_τ`
  have key : g =ᵐ[P] condExp hτ.measurableSpace P (E'.indicator f) := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le
      (hfint.indicator hE'mΩ) (fun A _ _ => hgint.integrableOn) (fun A hA _ => ?_)
      hgm.aestronglyMeasurable
    have hAm : MeasurableSet A := hτ.measurableSpace_le _ hA
    rw [hg, setIntegral_indicator hE'mΩ, setIntegral_indicator hE'mΩ]
    have hAE : MeasurableSet[hτ𝓖.measurableSpace] (A ∩ E') :=
      hσle _ (@MeasurableSet.inter Ω hτ.measurableSpace _ _ hA hE'm)
    have hfam := setIntegral_cexp_eq_cfAt_of_family hE hκ u hu h hh U s hs hsafe hsamp hexh φ hτ𝓖
      (hτζ.mono fun ω h => coe_untopD_lt_zeta h) hAE (inter_subset_right.trans hE'sub)
    rw [hfam]
    refine setIntegral_congr_fun (hAm.inter hE'mΩ) fun ω hω => ?_
    exact hcf ω hω.2
  have hind := condExp_indicator (m := hτ.measurableSpace) (μ := P) hfint hE'm
  filter_upwards [key, hind, hE'ae] with ω h1 h2 h3 hdis
  have hω : ω ∈ E' := h3 hdis
  have e1 : condExp hτ.measurableSpace P f ω =
      E'.indicator (condExp hτ.measurableSpace P f) ω := (indicator_of_mem hω _).symm
  rw [e1, ← h2, ← h1, hg, indicator_of_mem hω]

end Coupling

end InteractingSLE
