import QuantumZipper.Proofs.MainResults13
import QuantumZipper.Proofs.NonVacuityFinal
import QuantumZipper.Proofs.Probability.BrownianPathMeas
import QuantumZipper.Proofs.Thm14.FromThm13
import QuantumZipper.Proofs.Loewner.WeldingConsistency
import QuantumZipper.Proofs.RS.RohdeSchrammSimple

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FINAL-13: non-vacuity certificates for Theorems 1.3, 1.4 and Corollary 1.5

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.3 (pp. 15–16),
Theorem 1.4 (p. 16), Corollary 1.5 (pp. 17–18). Statement check FINAL-13 (handoff/FINAL-13.md).

The hypotheses of `theorem1_3`, `theorem1_4a/b` and `theorem1_5` are satisfiable
(`NonVacuity.exists_BM_indep_freeGFF_uncond`). This file certifies that their conclusions are
not true for a junk-value reason:

* `thm13_certificate`: almost surely the boundary measure `ν_h` of Theorem 1.3 is a genuine
  (locally finite, nonzero) vague limit of the paper's approximations (1.2), finite on compact
  intervals, the hull `η_T` is a simple curve (so the SLE driver itself is an admissible
  competitor in Theorem 1.4 (a)), and clause (ii) applies to at least one genuine pair
  `x₋ < 0 < x₊` identified at a point of `η_T`, with equal, finite, positive masses.
* `cor15_aemeasurable_zip`: for every `t`, the zipped configuration of Corollary 1.5 is
  a.e.-measurable, so the law identity (a) is an identity of genuine laws, not the
  `Measure.map` Dirac-mass junk value (`Measure.map_of_not_aemeasurable_of_ne_zero`). The key
  input is `configLawMod0_ne_dirac`: the law of the input configuration is not a Dirac mass,
  because its driver at time `1` is `√κ B₁ ∼ N(0,κ)`, which has no atoms.

Own elementary arguments (bookkeeping only); no new mathematics.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper

namespace Final13

variable {Ω : Type} [MeasurableSpace Ω]

/-- The input configuration of Corollary 1.5 is a.e.-measurable (into the target of
`configLawMod0`). -/
theorem aemeasurable_cfgData {κ : ℝ} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) :
    AEMeasurable (fun ω => (fun ρ : TestFun0 H => pairRaw (ofFun (h0rev κ) + X ω) ρ.1.1,
      fun t : ℝ≥0 => drive κ B ω t)) P := by
  refine AEMeasurable.prodMk ?_ ?_
  · refine Measurable.aemeasurable (measurable_pi_iff.mpr fun ρ => ?_)
    have hc : ∀ μ : Measure ℂ, Measurable fun ω => (ofFun (h0rev κ) + X ω) μ :=
      fun μ => measurable_const.add (hX.measurable_coord μ)
    exact measurable_pairRaw_comp hc ρ.1.1
  · have hm : Measurable fun f : ℝ≥0 → ℝ => fun t : ℝ≥0 => Real.sqrt κ * f t :=
      measurable_pi_iff.mpr fun t => (measurable_pi_apply t).const_mul _
    have he : (fun ω => fun t : ℝ≥0 => drive κ B ω t) =
        (fun f : ℝ≥0 → ℝ => fun t : ℝ≥0 => Real.sqrt κ * f t) ∘ pathOf B := by
      funext ω t
      simp [drive, pathOf]
    rw [he]
    exact hm.comp_aemeasurable (IsBrownianReal.aemeasurable_pathOf hB)

/-- The law of the input configuration of Corollary 1.5 is not a Dirac mass: its driver at
time `1` is `√κ B₁`, a nondegenerate Gaussian, which has no atoms. -/
theorem configLawMod0_ne_dirac {κ : ℝ} (hκ : 0 < κ) {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (d : (TestFun0 H → ℝ) × (ℝ≥0 → ℝ)) :
    configLawMod0 (fun ω => (ofFun (h0rev κ) + X ω, drive κ B ω)) P ≠ Measure.dirac d := by
  intro hEq
  set S : Set ((TestFun0 H → ℝ) × (ℝ≥0 → ℝ)) := {q | q.2 1 = d.2 1} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_singleton (d.2 1)).preimage ((measurable_pi_apply 1).comp measurable_snd)
  have h1 : Measure.dirac d S = 1 := by
    rw [Measure.dirac_apply' _ hSm]
    simp [hS]
  have h0 : configLawMod0 (fun ω => (ofFun (h0rev κ) + X ω, drive κ B ω)) P S = 0 := by
    unfold configLawMod0
    rw [Measure.map_apply_of_aemeasurable (aemeasurable_cfgData hB hX) hSm]
    have hsk : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.mpr hκ).ne'
    have hsub : (fun ω => (fun ρ : TestFun0 H => pairRaw (ofFun (h0rev κ) + X ω) ρ.1.1,
        fun t : ℝ≥0 => drive κ B ω t)) ⁻¹' S ⊆ B 1 ⁻¹' {d.2 1 / Real.sqrt κ} := by
      intro ω hω
      simp only [hS, Set.mem_preimage, Set.mem_setOf_eq, drive] at hω
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      rw [eq_div_iff hsk, ← hω]
      simp [mul_comm]
    refine le_antisymm (le_trans (measure_mono hsub) ?_) bot_le
    have hlaw := hB.hasLaw_eval 1
    have hnull : gaussianReal 0 (1 : ℝ≥0) {d.2 1 / Real.sqrt κ} = 0 := by
      have := nullSingletonClass_gaussianReal (μ := 0) (v := (1 : ℝ≥0)) one_ne_zero
      exact measure_singleton _
    rw [← hlaw.map_eq, Measure.map_apply_of_aemeasurable hlaw.aemeasurable
      (measurableSet_singleton _)] at hnull
    exact hnull.le
  rw [hEq, h1] at h0
  exact one_ne_zero h0

/-- **Corollary 1.5 (a) is not the `Measure.map` junk.** In the setting of Corollary 1.5, for
every `t ∈ ℝ` the zipped configuration `Z^CAP_t c` is a.e.-measurable, so the proved law
identity `theorem1_5_proved` compares genuine laws. -/
theorem cor15_aemeasurable_zip {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hI : IndepFun (pathOf B) X P)
    (t : ℝ) :
    AEMeasurable (fun ω =>
      (fun ρ : TestFun0 H =>
          pairRaw (zipCap (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1 ρ.1.1,
        fun u : ℝ≥0 => (zipCap (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).2 u)) P := by
  by_contra hne
  have ha := (theorem1_5_proved κ hκ hκ4 P B X hB hX hI).1 t
  simp only at ha
  have hP : P ≠ 0 := IsProbabilityMeasure.ne_zero P
  unfold configLawMod0 at ha
  rw [Measure.map_of_not_aemeasurable_of_ne_zero hne hP] at ha
  exact configLawMod0_ne_dirac hκ hB hX _ ha.symm

/-- **Theorem 1.3 / 1.4 (a) are not vacuous.** In the setting of Theorem 1.3, almost surely:
the SLE driver is an admissible competitor in Theorem 1.4 (a) (continuous, `W 0 = 0`, simple
curve hull); `ν_h` is a genuine vague limit of the approximations (1.2) (not the junk `0`), and
finite on every compact interval; and clause (ii) of Theorem 1.3 is used by at least one genuine
pair `x₋ < 0 < x₊` identified at a point of `η_T`, with equal, finite and positive masses. -/
theorem thm13_certificate {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {T : ℝ} (hT : 0 < T)
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hI : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P,
      (Continuous (drive κ B ω) ∧ drive κ B ω 0 = 0 ∧
        IsSimpleCurveHull (revHull (drive κ B ω) T)) ∧
      (∃ ν : Measure ℝ, IsVagueLimitR
          (bdryApprox (Real.sqrt κ) (couplingFieldRev κ (drive κ B ω) T (X ω))) ν ∧
        qBoundaryMeasure (Real.sqrt κ) (couplingFieldRev κ (drive κ B ω) T (X ω)) = ν) ∧
      (∀ u v : ℝ, qBoundaryMeasure (Real.sqrt κ)
          (couplingFieldRev κ (drive κ B ω) T (X ω)) (Set.Icc u v) < ⊤) ∧
      ∃ xm xp : ℝ, xm < 0 ∧ 0 < xp ∧
        revMapBdry (drive κ B ω) T xm = revMapBdry (drive κ B ω) T xp ∧
        revMapBdry (drive κ B ω) T xm ∈ revHull (drive κ B ω) T ∧
        0 < qBoundaryMeasure (Real.sqrt κ) (couplingFieldRev κ (drive κ B ω) T (X ω))
          (Set.Icc xm 0) ∧
        qBoundaryMeasure (Real.sqrt κ) (couplingFieldRev κ (drive κ B ω) T (X ω))
            (Set.Icc xm 0) =
          qBoundaryMeasure (Real.sqrt κ) (couplingFieldRev κ (drive κ B ω) T (X ω))
            (Set.Icc 0 xp) ∧
        qBoundaryMeasure (Real.sqrt κ) (couplingFieldRev κ (drive κ B ω) T (X ω))
          (Set.Icc 0 xp) < ⊤ := by
  filter_upwards [theorem1_3_proved κ hκ hκ4 T hT P B X hB hX hI,
    Thm14FromThm13.ae_isSimpleCurveHull_revHull RS.rohdeSchrammSimple hκ hκ4 hT P B hB,
    hB.cont, hB.eval_zero_ae_eq_zero] with ω h13 hK hc h0
  obtain ⟨hi, hii, hiii⟩ := h13
  set W := drive κ B ω with hW
  set x := couplingFieldRev κ W T (X ω) with hx
  -- the boundary measure is a genuine vague limit
  have hex : ∃ ν, IsVagueLimitR (bdryApprox (Real.sqrt κ) x) ν := by
    by_contra hne
    have hz : qBoundaryMeasure (Real.sqrt κ) x = 0 := by
      unfold qBoundaryMeasure
      rw [dif_neg hne]
    have := hiii 0 1 one_pos
    rw [hz] at this
    simp at this
  obtain ⟨ν, hν⟩ := hex
  have hqe : qBoundaryMeasure (Real.sqrt κ) x = ν := qBoundaryMeasure_eq hν
  have hfin : ∀ u v : ℝ, qBoundaryMeasure (Real.sqrt κ) x (Set.Icc u v) < ⊤ := by
    intro u v
    rw [hqe]
    have := hν.1
    exact measure_Icc_lt_top
  refine ⟨⟨Thm14FromThm13.continuous_drive hc, drive_zero h0, hK⟩, ⟨ν, hν, hqe⟩, hfin, ?_⟩
  -- a non-tip point of the simple curve hull
  obtain ⟨g, -, hinj, -, -, hKeq⟩ := hK
  have h1 : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨one_pos, le_rfl⟩
  have h2 : (1 / 2 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hne12 : g 1 ≠ g (1 / 2) := by
    intro h
    have := hinj (Set.Ioc_subset_Icc_self h1) (Set.Ioc_subset_Icc_self h2) h
    norm_num at this
  have hmem : ∀ s ∈ Set.Ioc (0 : ℝ) 1, g s ∈ revHull W T := fun s hs => by
    rw [hKeq]; exact ⟨s, hs, rfl⟩
  obtain ⟨z, hzK, hztip⟩ : ∃ z ∈ revHull W T, z ≠ revMapBdry W T 0 := by
    by_cases hA : g 1 = revMapBdry W T 0
    · exact ⟨g (1 / 2), hmem _ h2, fun h => hne12 (hA.trans h.symm)⟩
    · exact ⟨g 1, hmem _ h1, hA⟩
  obtain ⟨xm, xp, hxm, hxp, hfm, hfp⟩ := hi z hzK hztip
  have heq := hii xm xp hxm hxp (hfm.trans hfp.symm) (by rw [hfm]; exact Set.mem_insert_of_mem _ hzK)
  refine ⟨xm, xp, hxm, hxp, hfm.trans hfp.symm, hfm ▸ hzK, ?_, heq, hfin 0 xp⟩
  exact lt_of_lt_of_le (hiii xm 0 hxm) (measure_mono Set.Ioo_subset_Icc_self)

end Final13

end QuantumZipper
