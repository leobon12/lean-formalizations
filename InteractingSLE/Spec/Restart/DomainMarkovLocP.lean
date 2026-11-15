/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtOPiece
import InteractingSLE.Spec.Sec7.Lemma72DMember
import InteractingSLE.Spec.Coupling.MartMeans2Announce
import InteractingSLE.Spec.Restart.DomainMarkovLocCrit

/-!
# The domain Markov step, locality II: the member identity of the restarted field on the original space

Packet PROVE-DOMAINMARKOV3. For a frozen coupling (`κ > 0`), a finite stopping time `T` of its driving filtration `𝓓`
and a `𝓓_T`-measurable version `K` of the stopped history, the restarted field `h' = restartField κ (h, K)` satisfies,
under `P` itself, the **member identity** at every deterministic restarted time `s`: for a finite family `F` of
rational closed balls in `ℍ` and every event `D` of `𝓓_{T+s}` on which `s < ζ − T` and the restarted hull `K'_s` avoids
`ballsK F`,

  `∫_D e^{i h'(−Δf/2π + Ξ)} dP = projFactor (ballsU F) f Ξ · ∫_D e^{i h'(Ξ)} dP`  (`f ∈ C_c^∞(ballsU F)`, `Ξ` any).

Proof. With an announcing sequence `ρ_n` of `ζ` (admissible seed; at an inadmissible seed `ζ = 0` and `D` is null) put
`σ_n = (T + s) ∧ ρ_n < ζ` and `E_n = {T + s ≤ ρ_n} ∈ 𝓓_{σ_n}`. Under `P[· | E_n]`, PROVE-LOCEXT-O's conditional
decomposition through the restart chart (`LocalExt.exists_condDecomp_chart`, fed by the history-marked locality of the
hull at `σ_n`, `WholeField.isHistoryAvoidanceLocal_hull`) writes `h' = M + Y` with `M` measurable for
`𝒢 = germs(K_{σ_n}) ∨ 𝓓_{σ_n}` and harmonic off `K'_s`, `Y` a conditional zero-boundary GFF on `ℍ ∖ K'_s` given `𝒢`; so
`h'` has the Gaussian kernel `rangeKerCF M (ℍ ∖ K'_s)` given `𝒢` (`condExp_cexp_eq_rangeKerCF`), and the member
identity holds on `D ∩ E_n` (`Lemma72D.setIntegral_lapTest_of_kernel`). The pieces `D ∩ E_n` increase to `D` almost
surely.

* `condExp_cexp_eq_rangeKerCF`: a measurable mean plus a conditional zero-boundary GFF is a Gaussian kernel;
* **`setIntegral_lapTest_restart`**: the member identity above.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open QuantumZipper (H fwdHull zeroGFFTestCov)
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Restart.DomainMarkov

open LQGMetric LQGMetric.MarkovZB LocalSets WholeField Sec7 Sec5.Markov Sec2.Restart LocalExt Coupling
open QuantumZipper.K3 QuantumZipper.Thm11Asm

/-! ### A measurable mean plus a conditional zero-boundary field is a Gaussian kernel -/

section Kernel

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsFiniteMeasure Q]

/-- **A `𝒢`-measurable mean plus a conditional zero-boundary GFF given `𝒢` has the Gaussian kernel**
`rangeKerCF M V`: `Q[e^{i X(χ)} | 𝒢] = exp(i M(χ) − ½ G_V(χ, χ))`. -/
theorem condExp_cexp_eq_rangeKerCF (h𝒢 : 𝒢 ≤ mΩ) {X M : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X)
    (hMm : Measurable[𝒢] M) {V : Ω → Set ℂ} (hcond : IsCondZeroBoundaryGFF Q 𝒢 V fun ω => X ω - M ω)
    (χ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂Q, Q[fun ω' => Complex.exp (Complex.I * (X ω' χ : ℂ)) | 𝒢] ω = rangeKerCF (M ω) (V ω) χ := by
  set Wp : Ω → ℂ := fun ω => Complex.exp (Complex.I * (M ω χ : ℂ)) with hWpdef
  set F : Ω → ℂ := fun ω => Complex.exp (Complex.I * (((X ω - M ω) χ : ℝ) : ℂ)) with hFdef
  have hWpm : StronglyMeasurable[𝒢] Wp :=
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      ((measurable_distOn_apply χ).comp hMm)))).stronglyMeasurable
  have hWpb : ∀ ω, ‖Wp ω‖ ≤ 1 := fun ω => by
    simp only [Wp, Complex.norm_exp_I_mul_ofReal, le_refl]
  have hMm' : Measurable M := hMm.mono h𝒢 le_rfl
  have hYm : Measurable fun ω => X ω - M ω :=
    measurable_distOn_iff.2 fun φ => ((measurable_distOn_apply φ).comp hXm).sub ((measurable_distOn_apply φ).comp hMm')
  have hF : Integrable F Q := GFF.integrable_exp_I_mul ((measurable_distOn_apply χ).comp hYm)
  have hWF : Integrable (fun ω => Wp ω * F ω) Q :=
    hF.bdd_mul (hWpm.mono h𝒢).aestronglyMeasurable (Eventually.of_forall hWpb)
  have hfac := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hWpm
    (by simpa [ContinuousLinearMap.mul_apply'] using hWF) hF
  have e : (fun ω' => Complex.exp (Complex.I * (X ω' χ : ℂ))) =
      fun ω => (ContinuousLinearMap.mul ℝ ℂ) (Wp ω) (F ω) := by
    funext ω
    simp only [Wp, F, ContinuousLinearMap.mul_apply', sub_apply, Complex.ofReal_sub, ← Complex.exp_add]
    congr 1
    ring
  rw [e]
  filter_upwards [hfac, hcond χ] with ω h1 h2
  rw [h1, ContinuousLinearMap.mul_apply', h2]
  simp only [Wp, rangeKerCF, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Kernel

/-! ### The member identity of the restarted field -/

section Member

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {T : Ω → ℝ≥0}

omit [IsProbabilityMeasure P] in
/-- Set integrals over a subset of the conditioning event. -/
theorem setIntegral_cond_of_subset' {Q : Measure Ω} {E A : Set Ω} (hA : MeasurableSet A) (hAE : A ⊆ E)
    (g : Ω → ℂ) : ∫ ω in A, g ω ∂(Q[|E]) = (Q E)⁻¹.toReal • ∫ ω in A, g ω ∂Q := by
  rw [ProbabilityTheory.cond, Measure.restrict_smul, integral_smul_measure, Measure.restrict_restrict hA,
    inter_eq_left.2 hAE]

/-- **The member identity of the restarted field on one piece** `D ∩ {T + s ≤ ρ}`, `ρ < ζ` a stopping time of `𝓓`
(see the module docstring). -/
theorem setIntegral_lapTest_restart_piece (hκ : 0 < κ)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    {K : Ω → DrivingHist nL nR} (hKm : Measurable[hT.measurableSpace] K)
    (hK : ∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < ζ ω →
      K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω)
    (s : ℝ≥0) {F : Finset (ℚ × ℚ × ℚ)} (hFH : ballsK F ⊆ H)
    {ρ : Ω → ℝ≥0} (hρ : IsStoppingTime (drivingFiltration P hX) fun ω => (ρ ω : WithTop ℝ≥0))
    (hρζ : ∀ᵐ ω ∂P, (ρ ω : ℝ≥0∞) < ζ ω)
    {D : Set Ω} (hD : MeasurableSet[restartFiltration (drivingFiltration P hX) T hT s] D)
    (hDs : ∀ᵐ ω ∂P, ω ∈ D → Disjoint (ballsK F) (fwdHull (fun r : ℝ => restartDrv W T r.toNNReal ω) (s : ℝ)))
    (f : zsSub (ballsU F)) (Ξ : TestOn upperHalfPlaneOpens) :
    ∫ ω in D ∩ {ω | ((T ω + s : ℝ≥0) : WithTop ℝ≥0) ≤ (ρ ω : WithTop ℝ≥0)},
        Complex.exp (Complex.I * (restartField κ (h ω, K ω) (lapTest (ballsOpen F) f + Ξ) : ℂ)) ∂P =
      projFactor (ballsOpen F) f Ξ * ∫ ω in D ∩ {ω | ((T ω + s : ℝ≥0) : WithTop ℝ≥0) ≤ (ρ ω : WithTop ℝ≥0)},
        Complex.exp (Complex.I * (restartField κ (h ω, K ω) Ξ : ℂ)) ∂P := by
  classical
  obtain ⟨E, hEdef⟩ : ∃ E : Set Ω, E = {ω | ((T ω + s : ℝ≥0) : WithTop ℝ≥0) ≤ (ρ ω : WithTop ℝ≥0)} :=
    ⟨_, rfl⟩
  rw [← hEdef]
  have hTs : IsStoppingTime (drivingFiltration P hX) fun ω => ((T ω + s : ℝ≥0) : WithTop ℝ≥0) :=
    isStoppingTime_add_const hT s
  have hσ := hTs.min hρ
  set σ : Ω → WithTop ℝ≥0 := fun ω => min ((T ω + s : ℝ≥0) : WithTop ℝ≥0) (ρ ω : WithTop ℝ≥0) with hσdef
  have hDE : MeasurableSet[hσ.measurableSpace] (D ∩ E) := by
    rw [hEdef]; exact hTs.measurableSet_inter_le hρ D (by rwa [restartFiltration_apply] at hD)
  have hEσ : MeasurableSet[hσ.measurableSpace] E := by
    have := hTs.measurableSet_inter_le hρ univ MeasurableSet.univ
    rwa [univ_inter, ← hEdef] at this
  have hEm : MeasurableSet E := hσ.measurableSpace_le _ hEσ
  have hDEm : MeasurableSet (D ∩ E) := hσ.measurableSpace_le _ hDE
  by_cases hPE : P E = 0
  · have h0 : P (D ∩ E) = 0 := measure_mono_null inter_subset_right hPE
    rw [setIntegral_measure_zero _ h0, setIntegral_measure_zero _ h0, mul_zero]
  have : IsProbabilityMeasure (P[|E]) := cond_isProbabilityMeasure hPE
  have hEac : P[|E] ≪ P := cond_absolutelyContinuous
  have hEae : ∀ᵐ ω ∂(P[|E]), ω ∈ E := ae_cond_mem hEm
  have hpathP := hC.1.2.2.2.2
  -- on `E` the stop is `T + s`
  have hσE : ∀ ω ∈ E, σ ω = ((T ω + s : ℝ≥0) : WithTop ℝ≥0) := fun ω hω => by
    rw [hEdef] at hω; exact min_eq_left hω
  have hTσ : ∀ ω ∈ E, ((T ω : ℝ≥0) : WithTop ℝ≥0) ≤ σ ω := fun ω hω => by
    rw [hσE ω hω]; exact WithTop.coe_le_coe.2 le_self_add
  have hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω := by
    filter_upwards [hρζ] with ω hω
    exact lt_of_le_of_lt (min_le_right _ _) hω
  have hTsζ : ∀ᵐ ω ∂P, ω ∈ E → ((T ω + s : ℝ≥0) : ℝ≥0∞) < ζ ω := by
    filter_upwards [hρζ] with ω hω hωE
    rw [hEdef] at hωE
    have h1 : T ω + s ≤ ρ ω := WithTop.coe_le_coe.1 hωE
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 h1) hω
  obtain ⟨ω₀, -⟩ := nonempty_of_measure_ne_zero hPE
  -- the history read on `E`, measurable for `𝓓_σ`
  obtain ⟨Kp, hKpdef⟩ : ∃ Kp : Ω → DrivingHist nL nR, Kp = E.piecewise K fun _ => K ω₀ := ⟨_, rfl⟩
  have hKpm : Measurable[hσ.measurableSpace] Kp := by
    rw [hKpdef]; exact measurable_piecewise_stopping hT hσ hKm hEσ hTσ (K ω₀)
  have hKpE : ∀ ω ∈ E, Kp ω = K ω := fun ω hω => by rw [hKpdef]; exact Set.piecewise_eq_of_mem _ _ _ hω
  -- the hull at `σ`
  have hpath : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 := by
    filter_upwards [hpathP] with ω hp using ⟨hp.2.2.2.1, hp.1⟩
  obtain ⟨A₀, hA₀m, hA₀K, -⟩ := Coupling.exists_hittingVersion_hull hX hpath hσ hσζ
  have hσζ' : ∀ᵐ ω ∂P, (((σ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω :=
    hσζ.mono fun ω h => Coupling.coe_untopD_lt_zeta h
  have hBm : Measurable[mΩ, hittingSigma] fun ω => relClosureH (A₀ ω) := measurable_relClosureH.comp hA₀m
  have hBc : ∀ ω, relClosureH (A₀ ω) ⊆ H ∧ IsOpen (H \ relClosureH (A₀ ω)) := fun ω =>
    ⟨relClosureH_subset _, isOpen_H_diff_relClosureH _⟩
  have hBK : ∀ᵐ ω ∂P, relClosureH (A₀ ω) = fwdHull (fun s : ℝ => W s.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) := by
    filter_upwards [hA₀K, Coupling.ae_hull_subset_isOpen (hpath.mono fun ω h => h.1) hσζ'] with ω h1 h2
    rw [h1]
    exact relClosureH_eq h2.1 h2.2
  have hu₀ := isBoundedHarmonicExtension_bheAt κ ρL ρR xL xR
  have hloc := isHistoryAvoidanceLocal_hull hC hκ hu₀ hX hσ hσζ hBm hBK
  have hh0 := isZeroBoundaryGFF_centredField hC hu₀
  -- the restarted hull at `s` on `E`
  set τc : Ω → WithTop ℝ≥0 := fun _ => (s : WithTop ℝ≥0) with hτc
  obtain ⟨K', hK'def⟩ : ∃ K' : Ω → Set ℂ, K' = E.piecewise (fun ω => tsHull (restartHist ζ W T τc ω)) fun _ => ∅ :=
    ⟨_, rfl⟩
  have hK'c : ∀ ω, K' ω ⊆ H ∧ IsOpen (H \ K' ω) := fun ω => by
    rw [hK'def]; exact relClosed_restartHull_piece (ζ := ζ) (W := W) (T := T) E τc ω
  have hlt : ∀ ω, ((T ω + s : ℝ≥0) : ℝ≥0∞) < ζ ω → (((τc ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < restartLife ζ T ω :=
    fun ω h => by
      simp only [hτc, WithTop.untopD_coe]
      exact (Sec2.Restart.coe_lt_sub_iff (T ω) s).2 h
  have hBK' : ∀ᵐ ω ∂(P[|E]), H \ relClosureH (A₀ ω) = (histChart (Kp ω)).2.1 '' (H \ K' ω) := by
    filter_upwards [hEae, hEac.ae_le hpathP, hEac.ae_le hBK, hEac.ae_le hTsζ, hEac.ae_le hK] with ω hωE hp hB hTs'
      hKω
    have hTsω := hTs' hωE
    have hTζ : (T ω : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast le_self_add) hTsω
    have hσv : (σ ω).untopD 0 = T ω + (τc ω).untopD 0 := by
      rw [hσE ω hωE, WithTop.untopD_coe]
      simp only [hτc, WithTop.untopD_coe]
    rw [hB, hσv, hKpE ω hωE, hKω hTζ, hK'def, Set.piecewise_eq_of_mem _ _ _ hωE]
    exact compl_fwdHull_restart_eq_image hp.2.2.2.1 hp.1 (hlt ω hTsω)
  obtain ⟨M, hMm, hMharm, hMcond⟩ := exists_condDecomp_chart (P := P) hC.2.1 hu₀.1 hh0
    (fun ω => isConformal_histChart (Kp ω)) (fun z => hKpm (measurableSet_mem_dom_histChart z))
    (fun z => (measurable_indicator_fwd_histChart z).comp hKpm)
    (fun z => (measurable_indicator_lift_histChart z).comp hKpm)
    (fun ω => continuousOn_lift_histChart (Kp ω)) (fun ω => harmonicOnNhd_lift_histChart (Kp ω))
    hσ.measurableSpace_le hBm hBc hloc hK'c hEσ hPE hBK' 0 (QuantumZipper.chiC κ)
  -- the Gaussian kernel given germs ∨ marks and the member identity on `D ∩ E` under `P[· | E]`
  have h𝒢 : germSigma (fun ω => relClosureH (A₀ ω)) (centredField h (bheAt κ ρL ρR xL xR)) ⊔
      hσ.measurableSpace ≤ mΩ :=
    sup_le (germSigma_le hBm (measurable_centredField hC.2.1 _)) hσ.measurableSpace_le
  have hXm : Measurable fun ω => restartField κ (h ω, Kp ω) :=
    (measurable_restartField κ).comp (hC.2.1.prodMk (hKpm.mono hσ.measurableSpace_le le_rfl))
  have hker := fun χ => condExp_cexp_eq_rangeKerCF (Q := P[|E]) h𝒢 hXm hMm hMcond χ
  have hUH : ballsOpen F ≤ upperHalfPlaneOpens := fun z hz => hFH (ballsU_subset_ballsK F hz)
  have hDE𝒢 : MeasurableSet[germSigma (fun ω => relClosureH (A₀ ω)) (centredField h (bheAt κ ρL ρR xL xR)) ⊔
      hσ.measurableSpace] (D ∩ E) := (le_sup_right : hσ.measurableSpace ≤ _) _ hDE
  have hDV : ∀ᵐ ω ∂(P[|E]), ω ∈ D ∩ E → IsOpen (H \ K' ω) ∧ H \ K' ω ⊆ H ∧
      ((ballsOpen F : Set ℂ) ⊆ H \ K' ω) ∧ IsHarmonicDistOn (M ω) (H \ K' ω) := by
    filter_upwards [hMharm, hEac.ae_le hpathP, hEac.ae_le hTsζ, hEac.ae_le hDs] with ω hM hp hTs' hds hωDE
    refine ⟨(hK'c ω).2, sdiff_subset, fun z hz => ⟨hFH (ballsU_subset_ballsK F hz), fun hzK => ?_⟩, hM⟩
    have hK'ω : K' ω = fwdHull (fun r : ℝ => restartDrv W T r.toNNReal ω) (s : ℝ) := by
      rw [hK'def, Set.piecewise_eq_of_mem _ _ _ hωDE.2]
      have := tsHull_restartHist (τ := τc) hp.2.2.2.1 (hlt ω (hTs' hωDE.2))
      rw [this]
      simp only [hτc, WithTop.untopD_coe]
    rw [hK'ω] at hzK
    exact Set.disjoint_left.1 (hds hωDE.1) (ballsU_subset_ballsK F hz) hzK
  have key := Lemma72D.setIntegral_lapTest_of_kernel (P := P[|E]) h𝒢 hXm hker hUH hDE𝒢 hDV f Ξ
  -- back to `P`
  have e₁ : ∀ χ : TestOn upperHalfPlaneOpens,
      ∫ ω in D ∩ E, Complex.exp (Complex.I * (restartField κ (h ω, Kp ω) χ : ℂ)) ∂(P[|E]) =
        (P E)⁻¹.toReal • ∫ ω in D ∩ E, Complex.exp (Complex.I * (restartField κ (h ω, K ω) χ : ℂ)) ∂P := by
    intro χ
    rw [setIntegral_cond_of_subset' hDEm inter_subset_right]
    congr 1
    refine setIntegral_congr_fun hDEm fun ω hω => ?_
    simp only [hKpE ω hω.2]
  rw [e₁, e₁, mul_smul_comm] at key
  have hne : (P E)⁻¹.toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨ENNReal.inv_ne_zero.2 (measure_ne_top _ _), ENNReal.inv_ne_top.2 hPE⟩
  exact smul_right_injective ℂ hne key

/-- **The member identity of the restarted field** (see the module docstring): on every event `D ∈ 𝓓_{T+s}` on which
`s < ζ − T` and the restarted hull `K'_s` avoids `ballsK F`, the Dirichlet directions of `ballsU F` enter the
characteristic functional of `h' = restartField κ (h, K)` with the Gaussian factor of the projection onto
`H(ballsU F)`. -/
theorem setIntegral_lapTest_restart (hκ : 0 < κ)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    {K : Ω → DrivingHist nL nR} (hKm : Measurable[hT.measurableSpace] K)
    (hK : ∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < ζ ω →
      K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω)
    (s : ℝ≥0) {F : Finset (ℚ × ℚ × ℚ)} (hFH : ballsK F ⊆ H)
    {D : Set Ω} (hD : MeasurableSet[restartFiltration (drivingFiltration P hX) T hT s] D)
    (hDs : ∀ᵐ ω ∂P, ω ∈ D → (s : ℝ≥0∞) < restartLife ζ T ω ∧
      Disjoint (ballsK F) (fwdHull (fun r : ℝ => restartDrv W T r.toNNReal ω) (s : ℝ)))
    (f : zsSub (ballsU F)) (Ξ : TestOn upperHalfPlaneOpens) :
    ∫ ω in D, Complex.exp (Complex.I * (restartField κ (h ω, K ω) (lapTest (ballsOpen F) f + Ξ) : ℂ)) ∂P =
      projFactor (ballsOpen F) f Ξ * ∫ ω in D, Complex.exp (Complex.I * (restartField κ (h ω, K ω) Ξ : ℂ)) ∂P := by
  have hDm : MeasurableSet D := (restartFiltration (drivingFiltration P hX) T hT).le s _ hD
  have hK' : Measurable K := hKm.mono hT.measurableSpace_le le_rfl
  have hh'm : Measurable fun ω => restartField κ (h ω, K ω) :=
    (measurable_restartField κ).comp (hC.2.1.prodMk hK')
  have hnorm : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ ≤ 1 := fun x =>
    (Complex.norm_exp_I_mul_ofReal x).le
  have hint : ∀ χ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => Complex.exp (Complex.I * (restartField κ (h ω, K ω) χ : ℂ))) P := fun χ =>
    Integrable.of_bound (GFF.measurable_exp_I_mul ((measurable_distOn_apply χ).comp hh'm)).aestronglyMeasurable 1
      (ae_of_all _ fun _ => hnorm _)
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · -- at an inadmissible seed `ζ = 0`, so `D` is null
    have hD0 : P D = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hC.1.2.2.2.2, hDs] with ω hp hds hωD
      have hz := WangWu.IsIntegratedSLEPath.lifetime_eq_zero_of_threshold hp hseed
      have := (hds hωD).1
      rw [restartLife, hz, zero_tsub] at this
      exact ENNReal.not_lt_zero this
    rw [setIntegral_measure_zero _ hD0, setIntegral_measure_zero _ hD0, mul_zero]
  obtain ⟨ρ, ⟨hρst, hρmono, hρζ, hρex⟩, -⟩ := hC.1.exists_isAnnouncingSeq_drivingFiltration hκ hseed hX
  have hTs : IsStoppingTime (drivingFiltration P hX) fun ω => ((T ω + s : ℝ≥0) : WithTop ℝ≥0) :=
    isStoppingTime_add_const hT s
  set Dn : ℕ → Set Ω := fun n => D ∩ {ω | ((T ω + s : ℝ≥0) : WithTop ℝ≥0) ≤ (ρ n ω : WithTop ℝ≥0)} with hDndef
  have hpiece : ∀ n, ∫ ω in Dn n, Complex.exp (Complex.I *
      (restartField κ (h ω, K ω) (lapTest (ballsOpen F) f + Ξ) : ℂ)) ∂P = projFactor (ballsOpen F) f Ξ *
        ∫ ω in Dn n, Complex.exp (Complex.I * (restartField κ (h ω, K ω) Ξ : ℂ)) ∂P := fun n =>
    setIntegral_lapTest_restart_piece hκ hC hX hT hKm hK s hFH (hρst n) (hρζ n) hD
      (hDs.mono fun ω h hω => (h hω).2) f Ξ
  have hDnm : ∀ n, MeasurableSet (Dn n) := fun n =>
    hDm.inter (hTs.measurableSpace_le _ (hTs.measurableSet_le_stopping_time (hρst n)))
  have hmono : Monotone Dn := fun m n hmn ω hω =>
    ⟨hω.1, le_trans hω.2 (WithTop.coe_le_coe.2 (hρmono ω hmn))⟩
  have hU : (⋃ n, Dn n : Set Ω) =ᵐ[P] D := by
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · rw [sdiff_eq_empty.2 (iUnion_subset fun n => inter_subset_left), measure_empty]
    · rw [← compl_compl (D \ ⋃ n, Dn n), ← mem_ae_iff]
      filter_upwards [hDs, hρex] with ω hds hex
      intro hω
      obtain ⟨hωD, hωU⟩ := hω
      have hlt : ((T ω + s : ℝ≥0) : ℝ≥0∞) < ζ ω := (Sec2.Restart.coe_lt_sub_iff (T ω) s).1 (hds hωD).1
      obtain ⟨n, hn⟩ := hex (T ω + s) hlt
      exact hωU (mem_iUnion.2 ⟨n, hωD, WithTop.coe_le_coe.2 hn⟩)
  have L1 := tendsto_setIntegral_of_monotone hDnm hmono (hint (lapTest (ballsOpen F) f + Ξ)).integrableOn
  have L2 := (tendsto_setIntegral_of_monotone hDnm hmono (hint Ξ).integrableOn).const_mul
    (projFactor (ballsOpen F) f Ξ)
  rw [setIntegral_congr_set hU] at L1 L2
  simp_rw [← hpiece] at L2
  exact tendsto_nhds_unique L1 L2

end Member

end InteractingSLE.Restart.DomainMarkov
