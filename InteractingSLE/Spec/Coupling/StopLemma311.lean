import InteractingSLE.Spec.Coupling.StopCharFun

/-!
# Lemma 3.11 at an arbitrary stopping time

Packet PROVE-T11-L312 (Specification §3.3, `source/spec/p049-096.md#lem-3.11`, L569–L586; graph node
`SPEC.lem-3.11`). Fix a test function `ψ` on `ℍ` and a finite stopping time `τ` of the usual augmentation with, almost
surely, `τ < T_* = ζ` and `supp ψ ∩ K_τ = ∅` (for `U ⋐ ℍ`, `supp ψ ⊆ U` and `τ < τ_U ∧ T_*` this holds). The field
`h_{U,τ}` is sampled from the driving history up to `τ`, a zero-boundary GFF on `ℍ ∖ K_τ` and the mean `𝔥_τ`: tested
against `ψ`, conditionally on `𝓕_τ` it is Gaussian with mean `(𝔥_τ, ψ)` and variance `E_τ(ψ)`. The lemma:
`(h_{U,τ}, ψ) =d (h̃ + 𝔥₀, ψ)`, `h̃` a zero-boundary GFF on `ℍ`.

This removes the restriction to safe stops of PROVE-T11-L311: optional stopping between `0` and `τ`
(`setIntegral_cfAt_eq_of_le`) gives `E[exp(iθ (𝔥_τ, ψ) − θ² E_τ(ψ)/2)] = exp(iθ (𝔥₀, ψ) − θ² E₀(ψ)/2)`.

## Main results

* `integral_cfAt_eq_of_stoppingTime`: `E[cfAt τ] = exp(iθ ∫ u₀ ψ − θ² E₀(ψ)/2)`;
* **`map_eq_gaussianReal_of_condExp_cfAt`** (Lemma 3.11): for any sub-σ-algebra `𝒢` (for instance `𝓕_τ` of the
  usual augmentation or of the frozen driving filtration), a variable whose conditional characteristic function
  given `𝒢` is `exp(iθ (𝔥_τ, ψ) − θ² E_τ(ψ)/2)` has the law `N(∫ u₀ ψ, ‖ψ‖²_{H⁻¹(ℍ)})` of `(h̃ + 𝔥₀, ψ)`;
* `isStoppingTime_untopD_of_drivingFiltration`: a stopping time `τ < ζ` of the frozen driving filtration, read as
  the finite time `τ.untopD 0` of the frozen statement, is a stopping time of the usual augmentation;
* `map_eq_gaussianReal_of_condExp_driving`: Lemma 3.11 for the frozen stopping times.
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

section Main

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
  (u : Ω → ℝ≥0 → ℂ → ℝ)
  (hu : ∀ ω s, IsBoundedHarmonicExtension
    (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
    (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
  {u₀ : ℂ → ℝ}
  (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
  (ψ : LQGMetric.TestOn upperHalfPlaneOpens)
include hE hκ hu hu₀

/-- **Optional stopping of the characteristic-function martingale at an arbitrary stopping time** (the step "(by
(3.19))" of Lemma 3.11): if `τ` is a stopping time of the usual augmentation with `τ < ζ` and `supp ψ ∩ K_τ = ∅`
almost surely, then `E[exp(iθ (𝔥_τ, ψ) − θ² E_τ(ψ)/2)] = exp(iθ ∫ u₀ ψ − θ² E₀(ψ)/2)`. -/
theorem integral_cfAt_eq_of_stoppingTime {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (τ ω : WithTop ℝ≥0))
    (hτs : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (τ ω))) (θ : ℝ) :
    ∫ ω, cfAt κ W u ψ θ τ ω ∂P =
      Complex.exp (Complex.I * θ * ((∫ z, u₀ z * ψ z : ℝ) : ℂ) -
        θ ^ 2 * ((greenEnergy0 ψ : ℝ) : ℂ) / 2) := by
  have hE' := isIntegratedSLEEvolution_usualAugmentation hE
  have h0 : IsStoppingTime (usualAugmentation 𝓕 P) fun _ : Ω => ((0 : ℝ≥0) : WithTop ℝ≥0) :=
    isStoppingTime_const _ _
  have h1 := setIntegral_cfAt_eq_of_le hE hκ u hu ψ h0 hτ (fun ω => zero_le (a := τ ω)) hτs
    (S := univ) MeasurableSet.univ θ
  rw [setIntegral_univ, setIntegral_univ] at h1
  rw [h1]
  have hKH : tsupport (ψ : ℂ → ℝ) ⊆ H := tsupport_subset_H ψ
  obtain ⟨m, hm, hKm⟩ := exists_pos_le_im_of_isCompact ψ.hasCompactSupport.isCompact hKH
  have h0' : IsStoppingTime (nullAugmented (usualAugmentation 𝓕 P) P)
      fun _ : Ω => ((0 : ℝ≥0) : WithTop ℝ≥0) := isStoppingTime_const _ _
  have hsafe : ∀ᵐ ω ∂P, IsTestSafe W ζ ψ (fun _ => 0) m 0 ω := by
    filter_upwards [hτs, hE.2.2.2.2] with ω hω hP
    refine ⟨lt_of_le_of_lt (by exact_mod_cast zero_le (a := τ ω)) hω.1, le_rfl, fun z hz => ⟨?_, ?_⟩⟩
    · simpa using exists_isForwardSol_zero (rpath (W · ω)) (hKH hz)
    · rw [NNReal.coe_zero, fwdMap_zero_eq_sub _ (hKH hz)]
      simpa [rpath, hP.1] using hKm z hz
  exact integral_cexp_testMean_stopped_of_safe hE' hκ h0' hsafe hKH ψ.continuous ψ.hasCompactSupport hm
    u hu hu₀ θ

/-- **Lemma 3.11 at an arbitrary stopping time** (Specification L569–L586). Let `τ` be a stopping time of the usual
augmentation with `τ < ζ` and `supp ψ ∩ K_τ = ∅` almost surely, and `𝒢` a sub-σ-algebra. If, conditionally on `𝒢`,
`Y` is Gaussian with mean `(𝔥_τ, ψ)` and variance `E_τ(ψ)` (the sampled field `𝔥_τ + h⁰ ∘ f_τ` tested against
`ψ`), then `Y ∼ N((𝔥₀, ψ), ‖ψ‖²_{H⁻¹(ℍ)})`, the law of `(h̃ + 𝔥₀, ψ)`. -/
theorem map_eq_gaussianReal_of_condExp_cfAt {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (τ ω : WithTop ℝ≥0))
    (hτs : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (τ ω)))
    {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ mΩ) {Y : Ω → ℝ} (hY : Measurable[mΩ] Y)
    (hcond : ∀ θ : ℝ, P[fun ω => Complex.exp (Complex.I * θ * Y ω) | 𝒢] =ᵐ[P]
      fun ω => cfAt κ W u ψ θ τ ω) :
    @Measure.map Ω ℝ mΩ _ Y P = gaussianReal (∫ z, u₀ z * ψ z) (zeroGFFTestCov upperHalfPlaneOpens ψ ψ).toNNReal := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hnn : 0 ≤ zeroGFFTestCov upperHalfPlaneOpens ψ ψ :=
    LQGMetric.zeroGFFTestCov_self_nonneg (LQGMetric.zbAdmissible_of_subset_H subset_rfl) ψ
  refine map_eq_gaussianReal_of_condExp h𝒢 hY hcond fun θ => ?_
  have h := integral_cfAt_eq_of_stoppingTime hE hκ u hu hu₀ ψ hτ hτs θ
  rw [greenEnergy0_eq_zeroGFFTestCov] at h
  rw [Real.coe_toNNReal _ hnn]
  exact h

end Main

/-! ### The stopping times of the frozen statement -/

/-- The frozen statement reads a stopping time `τ : Ω → WithTop ℝ≥0` at the finite time `τ.untopD 0`. If `τ` is a
stopping time of the usual augmentation and `τ < ⊤` almost surely, so is `τ.untopD 0` (the usual augmentation is
complete). -/
theorem isStoppingTime_untopD {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (usualAugmentation 𝓕 P) τ) (hτf : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (((τ ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) := by
  set 𝓖 := usualAugmentation 𝓕 P
  have htop : MeasurableSet {ω | τ ω = ⊤} := by
    have e : {ω | τ ω = ⊤} = ⋂ n : ℕ, {ω | τ ω ≤ (n : ℝ≥0)}ᶜ := by
      ext ω
      simp only [mem_ofPred_eq, mem_iInter, mem_compl_iff, not_le]
      constructor
      · intro h n; rw [h]; exact WithTop.coe_lt_top _
      · intro h
        by_contra hne
        obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hne
        obtain ⟨n, hn⟩ := exists_nat_ge (a : ℝ)
        have := h n
        rw [← ha, WithTop.coe_lt_coe] at this
        exact absurd (by exact_mod_cast hn : a ≤ (n : ℝ≥0)) (not_le.2 this)
    rw [e]
    exact MeasurableSet.iInter fun n => (𝓖.le (n : ℝ≥0) _ (hτ (n : ℝ≥0))).compl
  have hnull : P {ω | τ ω = ⊤} = 0 := by
    simpa only [ne_eq, not_not] using ae_iff.1 hτf
  intro t
  have e : {ω | (((τ ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) ≤ t} = {ω | τ ω ≤ t} ∪ {ω | τ ω = ⊤} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union]
    by_cases h : τ ω = ⊤
    · rw [h, WithTop.untopD_top]
      exact iff_of_true (WithTop.coe_le_coe.2 (zero_le (a := t))) (Or.inr rfl)
    · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 h
      rw [← ha, WithTop.untopD_coe]
      exact ⟨Or.inl, fun h' => h'.resolve_right WithTop.coe_ne_top⟩
  rw [e]
  exact (hτ t).union (measurableSet_usualAugmentation_of_null htop hnull t)

theorem coe_untopD_of_ne_top {τ : WithTop ℝ≥0} (h : τ ≠ ⊤) :
    ((τ.untopD 0 : ℝ≥0) : WithTop ℝ≥0) = τ := by
  obtain ⟨a, rfl⟩ := WithTop.ne_top_iff_exists.1 h
  rfl

theorem ne_top_of_lt_zeta {τ : WithTop ℝ≥0} {z : ℝ≥0∞} (h : (τ : ℝ≥0∞) < z) : τ ≠ ⊤ := by
  rintro rfl
  exact absurd h (not_lt.2 le_top)

theorem coe_untopD_lt_zeta {τ : WithTop ℝ≥0} {z : ℝ≥0∞} (h : (τ : ℝ≥0∞) < z) :
    ((τ.untopD 0 : ℝ≥0) : ℝ≥0∞) < z := by
  obtain ⟨a, rfl⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt_zeta h)
  exact h

/-- **A stopping time of the frozen driving filtration** with `τ < ζ` almost surely, read at `τ.untopD 0`, is a
stopping time of the usual augmentation of the evolution's filtration. -/
theorem isStoppingTime_untopD_of_drivingFiltration
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) :
    IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (((τ ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) :=
  isStoppingTime_untopD (isStoppingTime_usualAugmentation_of_drivingFiltration hE hX hτ)
    (hτζ.mono fun _ h => ne_top_of_lt_zeta h)

/-- **Lemma 3.11 for the stopping times of the frozen statement**: `τ` a stopping time of the frozen
`drivingFiltration` with `τ < ζ` and `supp ψ ∩ K_τ = ∅` almost surely; `Y` with conditional characteristic function
`exp(iθ (𝔥_τ, ψ) − θ² E_τ(ψ)/2)` given `𝓕_τ` (the σ-algebra of `τ` for the frozen filtration). Then `Y` has the law
of `(h̃ + 𝔥₀, ψ)`. -/
theorem map_eq_gaussianReal_of_condExp_driving
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
    (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (ψ : LQGMetric.TestOn upperHalfPlaneOpens) (hX : IsMeasurableKilledDriving W VL VR ζ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (drivingFiltration P hX) τ)
    (hτs : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)))
    {Y : Ω → ℝ} (hY : Measurable Y)
    (hcond : ∀ θ : ℝ, P[fun ω => Complex.exp (Complex.I * θ * Y ω) | hτ.measurableSpace] =ᵐ[P]
      fun ω => cfAt κ W u ψ θ (fun ω => (τ ω).untopD 0) ω) :
    P.map Y = gaussianReal (∫ z, u₀ z * ψ z) (zeroGFFTestCov upperHalfPlaneOpens ψ ψ).toNNReal :=
  map_eq_gaussianReal_of_condExp_cfAt hE hκ u hu hu₀ ψ
    (isStoppingTime_untopD_of_drivingFiltration hE hX hτ (hτs.mono fun _ h => h.1))
    (hτs.mono fun _ h => ⟨coe_untopD_lt_zeta h.1, h.2⟩) hτ.measurableSpace_le hY hcond

end Coupling

end InteractingSLE
