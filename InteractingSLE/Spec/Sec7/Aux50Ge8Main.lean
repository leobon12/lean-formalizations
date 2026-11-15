/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux50Ge8Kernel
import InteractingSLE.Spec.Sec7.TwoForceMain2Exhaust
import InteractingSLE.Spec.Sec7.Lemma725Det

/-!
# Aux. lemma 50 for every `κ > 0` on a continuous trace (in particular `κ ≥ 8`)

Packet PROVE-AUX50C. Specification Aux. lemma 50 (`source/spec/p193-240.md` L819ff., pp. 236–242: "with any parameter
`κ > 0`", "No simplicity, trace-dimension bound, or Sobolev removability across the whole trace is needed") and Aux.
lemma 51 (p. 242).

For a coupling of a force word with infinite lifetime and a continuous trace:

* `integral_mul_exp_pocketSum` (forgetting the germs, (HGV10)): given the history at `N`, the pocket fluctuations have
  the centred Gaussian law with the retained energy of the pocket part (C.4 on each pattern of pocket pieces);
* **`tendsto_setIntegral_kerApprox`**: for every Borel set `B` of histories,
  `∫_{H_N ∈ B} e^{i(h, φ)} = lim_n ∫_{H_N ∈ B} kerApprox_n(H_N)`, the common Borel approximants of `Aux50Ge8Kernel`
  (the covariance exhaustion `tendsto_integral_sq_exhaust`);
* **`traceStopLawUnique`**: Aux. lemma 51 at the integer times for the two-seed words and **every** `κ > 0`, hence
  `hasTraceStopKernel` (`Aux50.HasTraceStopKernel`) and the two named inputs of PROVE-AUX50B:
  **`r7KernelGeEightStatement`** and **`lemma725KernelGeEightStatement`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Aux50Ge8

open QuantumZipper QuantumZipper.K3 LQGMetric LocalSets WholeField Coupling Aux50Hit Sec4 LawUnique WangWu

section Coupling

universe v

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- Pull a bounded `m`-measurable complex factor out of an integral against a conditional expectation. -/
theorem integral_mul_condExp_complex {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {G f : Ω → ℂ}
    (hG : StronglyMeasurable[m] G) (hGb : ∀ ω, ‖G ω‖ ≤ 1) (hf : Integrable f P) :
    ∫ ω, G ω * (P[f | m]) ω ∂P = ∫ ω, G ω * f ω ∂P := by
  have h1 := condExp_stronglyMeasurable_bilin_of_bound (ContinuousLinearMap.mul ℝ ℂ) hm hG hf 1
    (Eventually.of_forall hGb)
  rw [← integral_condExp hm (f := fun ω => G ω * f ω)]
  exact integral_congr_ae (h1.mono fun ω hω => by simpa using hω.symm)

open scoped Classical in
/-- **Forgetting the germs** ((HGV10), C.4 on each pattern of pocket pieces): for a bounded factor `g` measurable for
the history at `N`, `E[g e^{i Y_S}] = E[g e^{−Q_{U_N}(φ_S)/2}]`, `Y_S = ∑ₖ 1_{Eₖ} ((h, ψₖ) − E[(h, ψₖ) | 𝓕_N])` and
`φ_S = ∑ₖ 1_{Eₖ} ψₖ`. -/
theorem integral_mul_exp_pocketSum (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hX : IsMeasurableKilledDriving W VL VR ζ) {N : ℕ}
    (hN : IsStoppingTime (drivingFiltration P hX) (ruleTime (natStop N) W VL VR ζ)) {ι : Type*} (s : Finset ι)
    (ψ : ι → TestOn upperHalfPlaneOpens) {g : Ω → ℂ} (hgm : StronglyMeasurable[hN.measurableSpace] g)
    (hgb : ∀ ω, ‖g ω‖ ≤ 1) :
    (∀ᵐ ω ∂P, 0 ≤ WangWu.retainedGreenEnergy (W · ω) N (fun z => ∑ k ∈ s,
        {ω | histPoc N (tsupport (ψ k)) (stopHistory (natStop N) (killedHistory W VL VR ζ ω))}.indicator
          (fun _ => (1 : ℝ)) ω * ψ k z)) ∧
    ∫ ω, g ω * cexp (((∑ k ∈ s, {ω | histPoc N (tsupport (ψ k))
        (stopHistory (natStop N) (killedHistory W VL VR ζ ω))}.indicator
        (fun ω => h ω (ψ k) - (P[fun ω' => h ω' (ψ k) | hN.measurableSpace]) ω) ω : ℝ) : ℂ) * I) ∂P =
      ∫ ω, g ω * ((Real.exp (-(1 / 2) * WangWu.retainedGreenEnergy (W · ω) N (fun z => ∑ k ∈ s,
        {ω | histPoc N (tsupport (ψ k)) (stopHistory (natStop N) (killedHistory W VL VR ζ ω))}.indicator
          (fun _ => (1 : ℝ)) ω * ψ k z)) : ℝ) : ℂ) ∂P := by
  set E : ι → Set Ω := fun k =>
    {ω | histPoc N (tsupport (ψ k)) (stopHistory (natStop N) (killedHistory W VL VR ζ ω))} with hEdef
  have hEm : ∀ k, MeasurableSet[hN.measurableSpace] (E k) := fun k => measurableSet_pocketEvent hX hN (ψ k)
  have hNle : hN.measurableSpace ≤ mΩ := hN.measurableSpace_le
  set lamf : ι → Ω → ℝ := fun k ω => (P[fun ω' => h ω' (ψ k) | hN.measurableSpace]) ω with hlamf
  set Sω : Ω → Finset ι := fun ω => s.filter fun k => ω ∈ E k with hS
  set F : Finset ι → Set Ω := fun t => {ω | Sω ω = t} with hF
  have hFm : ∀ t ∈ s.powerset, MeasurableSet[hN.measurableSpace] (F t) := by
    intro t ht
    have ht' : t ⊆ s := Finset.mem_powerset.1 ht
    have e : F t = ⋂ k ∈ s, {ω | (ω ∈ E k ↔ k ∈ t)} := by
      ext ω
      simp only [hF, hS, mem_ofPred_eq, mem_iInter]
      constructor
      · rintro rfl k hk; simp [hk]
      · intro hω
        ext k
        simp only [Finset.mem_filter]
        exact ⟨fun h' => (hω k h'.1).1 h'.2, fun h' => ⟨ht' h', (hω k (ht' h')).2 h'⟩⟩
    rw [e]
    refine MeasurableSet.biInter s.countable_toSet fun k _ => ?_
    by_cases hkt : k ∈ t
    · simp only [hkt, iff_true, ofPred_mem_eq]; exact hEm k
    · simp only [hkt, iff_false]; exact (hEm k).compl
  have hh2 : ∀ k, MemLp (fun ω => h ω (ψ k)) 2 P := by
    intro k
    obtain ⟨u₀, hu₀⟩ := exists_bhe κ ρL ρR xL xR
    exact memLp_pairing hC hu₀ (ψ k)
  have hpart : ∀ (f : Ω → ℂ) ω, ∑ t ∈ s.powerset, (F t).indicator f ω = f ω := by
    intro f ω
    rw [Finset.sum_eq_single (Sω ω)]
    · rw [indicator_of_mem (show ω ∈ F (Sω ω) from rfl)]
    · intro t _ hne
      exact indicator_of_notMem (fun h' => hne h'.symm) _
    · intro hn
      exact absurd (Finset.mem_powerset.2 (Finset.filter_subset _ s)) hn
  have hpattern : ∀ t ω, ω ∈ F t → ∀ (c : ι → ℝ) (f : ι → ℝ),
      ∑ k ∈ s, (E k).indicator (fun _ => c k) ω * f k = ∑ k ∈ t, c k * f k := by
    intro t ω hω c f
    have hω' : Sω ω = t := hω
    rw [← hω', hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : ω ∈ E k
    · simp [hk]
    · simp [hk]
  have hgood := ae_isGoodPath hC.1 hζ
  -- each pattern
  have hpat : ∀ t ∈ s.powerset,
      (∀ᵐ ω ∂P, ω ∈ F t → 0 ≤ WangWu.retainedGreenEnergy (W · ω) N
        ((∑ k ∈ t, ψ k : TestOn upperHalfPlaneOpens) : ℂ → ℝ)) ∧
      Integrable ((F t).indicator fun ω => g ω * ((Real.exp (-(1 / 2) *
        WangWu.retainedGreenEnergy (W · ω) N ((∑ k ∈ t, ψ k : TestOn upperHalfPlaneOpens) : ℂ → ℝ)) : ℝ) : ℂ)) P ∧
      ∫ ω, (F t).indicator (fun ω => g ω * cexp (((∑ k ∈ s, (E k).indicator (fun ω => h ω (ψ k) - lamf k ω) ω :
        ℝ) : ℂ) * I)) ω ∂P =
      ∫ ω, (F t).indicator (fun ω => g ω * ((Real.exp (-(1 / 2) *
        WangWu.retainedGreenEnergy (W · ω) N
          ((∑ k ∈ t, ψ k : TestOn upperHalfPlaneOpens) : ℂ → ℝ)) : ℝ) : ℂ)) ω ∂P := by
    intro t ht
    have hNσ : IsStoppingTime (drivingFiltration P hX) fun _ : Ω => ((N : ℝ≥0) : WithTop ℝ≥0) := hN
    have hms : hNσ.measurableSpace = hN.measurableSpace := rfl
    set Z : Ω → ℝ := fun ω => h ω (∑ k ∈ t, ψ k) with hZdef
    have hZsum : Z = ∑ k ∈ t, fun ω => h ω (ψ k) := by
      funext ω; simp only [hZdef, map_sum, Finset.sum_apply]
    have hμ : P[Z | hN.measurableSpace] =ᵐ[P] fun ω => ∑ k ∈ t, lamf k ω := by
      rw [hZsum]
      filter_upwards [condExp_finsetSum (μ := P) (fun k _ => (hh2 k).integrable one_le_two) hN.measurableSpace]
        with ω hω
      rw [hω, Finset.sum_apply]
    have h4 := ae_condExp_exp_eq_cmKer_of_isLabel hC hκ hX ψ t (σ := fun _ => (N : ℝ≥0)) hNσ
      (hζ.mono fun ω hω => by rw [hω]; exact ENNReal.coe_lt_top) (N := (N : ℝ≥0)) (fun _ => le_rfl) 1
    rw [hms] at h4
    simp only [one_smul] at h4
    have e1 : (fun ω => cexp ((Z ω : ℂ) * I)) = fun ω' => cexp (I * (h ω' (∑ k ∈ t, ψ k) : ℂ)) := by
      funext ω'; rw [mul_comm]
    -- the factor in front of `e^{iZ}`
    set G : Ω → ℂ := (F t).indicator fun ω => g ω * cexp (((-(P[Z | hN.measurableSpace]) ω : ℝ) : ℂ) * I)
      with hGdef
    have hGm : StronglyMeasurable[hN.measurableSpace] G := by
      refine StronglyMeasurable.indicator ?_ (hFm t ht)
      exact hgm.mul (Complex.continuous_exp.comp_stronglyMeasurable
        ((Complex.continuous_ofReal.comp_stronglyMeasurable stronglyMeasurable_condExp.neg).mul
          stronglyMeasurable_const))
    have hGb : ∀ ω, ‖G ω‖ ≤ 1 := by
      intro ω
      by_cases hω : ω ∈ F t
      · rw [hGdef, indicator_of_mem hω, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
        exact hgb ω
      · rw [hGdef, indicator_of_notMem hω, norm_zero]; exact zero_le_one
    have hint : Integrable (fun ω => cexp ((Z ω : ℂ) * I)) P :=
      Integrable.of_bound (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
        ((Sobolev.measurable_distOn_apply _).comp hC.2.1)).mul_const _)).aestronglyMeasurable 1
        (Eventually.of_forall fun ω => (Complex.norm_exp_ofReal_mul_I _).le)
    have hbdd : ∀ᵐ ω ∂P, ‖(P[fun ω => cexp ((Z ω : ℂ) * I) | hN.measurableSpace]) ω‖ ≤ 1 := by
      have h1 := norm_condExp_le (μ := P) (m := hN.measurableSpace) (fun ω => cexp ((Z ω : ℂ) * I))
      have h2 : (P[fun ω => ‖cexp ((Z ω : ℂ) * I)‖ | hN.measurableSpace]) = fun _ => 1 := by
        simp only [Complex.norm_exp_ofReal_mul_I]
        exact condExp_const hNle 1
      filter_upwards [h1] with ω hω
      rw [h2] at hω
      exact hω
    have key := integral_mul_condExp_complex hNle hGm hGb hint
    -- the pattern identity, pointwise
    have hpt : ∀ᵐ ω ∂P, G ω * (P[fun ω => cexp ((Z ω : ℂ) * I) | hN.measurableSpace]) ω =
        (F t).indicator (fun ω => g ω * ((Real.exp (-(1 / 2) *
          WangWu.retainedGreenEnergy (W · ω) N ((∑ k ∈ t, ψ k : TestOn upperHalfPlaneOpens) : ℂ → ℝ)) : ℝ) : ℂ)) ω ∧
        (ω ∈ F t → 0 ≤ WangWu.retainedGreenEnergy (W · ω) N ((∑ k ∈ t, ψ k : TestOn upperHalfPlaneOpens) : ℂ → ℝ)) := by
      filter_upwards [h4, hgood, hbdd] with ω e4 hg hb
      by_cases hωF : ω ∈ F t
      · have hlab : ∀ k ∈ t, IsLabel (W · ω) (tsupport (ψ k)) (N : ℝ≥0) := by
          intro k hk
          have hkE : ω ∈ E k := by
            have hω' : Sω ω = t := hωF
            rw [← hω', hS, Finset.mem_filter] at hk
            exact hk.2
          exact (histLab_iff hg N (ψ k).tsupport_subset).1 hkE.1
        have e5 : (P[fun ω => cexp ((Z ω : ℂ) * I) | hN.measurableSpace]) ω =
            WangWu.gaussCF ((P[Z | hN.measurableSpace]) ω)
              (WangWu.retainedGreenEnergy (W · ω) N ((∑ k ∈ t, ψ k : TestOn upperHalfPlaneOpens) : ℂ → ℝ)) := by
          rw [e1, e4 hlab, cmKer]
        have hnn : 0 ≤ WangWu.retainedGreenEnergy (W · ω) N ((∑ k ∈ t, ψ k : TestOn upperHalfPlaneOpens) : ℂ → ℝ) := by
          rw [e5, WangWu.gaussCF, Complex.norm_exp] at hb
          simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, sub_zero, mul_zero, zero_sub] at hb
          have := Real.exp_le_one_iff.1 hb
          linarith
        refine ⟨?_, fun _ => hnn⟩
        rw [hGdef, indicator_of_mem hωF, indicator_of_mem hωF, e5, WangWu.gaussCF, mul_assoc, ← Complex.exp_add,
          Complex.ofReal_exp]
        congr 2
        push_cast
        ring
      · exact ⟨by rw [hGdef, indicator_of_notMem hωF, indicator_of_notMem hωF, zero_mul], fun h' => absurd h' hωF⟩
    have hRint : Integrable ((F t).indicator fun ω => g ω * ((Real.exp (-(1 / 2) *
        WangWu.retainedGreenEnergy (W · ω) N ((∑ k ∈ t, ψ k : TestOn upperHalfPlaneOpens) : ℂ → ℝ)) : ℝ) : ℂ)) P := by
      refine (Integrable.of_bound ?_ 1 ?_).congr (hpt.mono fun ω hω => hω.1)
      · exact (hGm.mono hNle).aestronglyMeasurable.mul (stronglyMeasurable_condExp.mono hNle).aestronglyMeasurable
      · filter_upwards [hbdd] with ω hω
        rw [norm_mul]
        calc ‖G ω‖ * ‖(P[fun ω => cexp ((Z ω : ℂ) * I) | hN.measurableSpace]) ω‖ ≤ 1 * 1 :=
              mul_le_mul (hGb ω) hω (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    refine ⟨hpt.mono fun ω hω => hω.2, hRint, ?_⟩
    calc ∫ ω, (F t).indicator (fun ω => g ω * cexp (((∑ k ∈ s, (E k).indicator
          (fun ω => h ω (ψ k) - lamf k ω) ω : ℝ) : ℂ) * I)) ω ∂P
        = ∫ ω, G ω * cexp ((Z ω : ℂ) * I) ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hμ] with ω hω
          by_cases hωF : ω ∈ F t
          · rw [indicator_of_mem hωF, hGdef, indicator_of_mem hωF, hω]
            have hsum : (∑ k ∈ s, (E k).indicator (fun ω => h ω (ψ k) - lamf k ω) ω) =
                Z ω - ∑ k ∈ t, lamf k ω := by
              have := hpattern t ω hωF (fun _ => 1) (fun k => h ω (ψ k) - lamf k ω)
              simp only [one_mul] at this
              rw [show (∑ k ∈ s, (E k).indicator (fun ω => h ω (ψ k) - lamf k ω) ω) =
                ∑ k ∈ s, (E k).indicator (fun _ => (1 : ℝ)) ω * (h ω (ψ k) - lamf k ω) from
                Finset.sum_congr rfl fun k _ => by
                  by_cases hk : ω ∈ E k
                  · simp [hk]
                  · simp [hk], this, Finset.sum_sub_distrib]
              simp only [hZdef, map_sum]
            rw [hsum, mul_assoc, ← Complex.exp_add]
            congr 2
            push_cast
            ring
          · rw [indicator_of_notMem hωF, hGdef, indicator_of_notMem hωF, zero_mul]
      _ = ∫ ω, G ω * (P[fun ω => cexp ((Z ω : ℂ) * I) | hN.measurableSpace]) ω ∂P := key.symm
      _ = _ := integral_congr_ae (hpt.mono fun ω hω => hω.1)
  -- the pocket energy on each pattern
  have hQS : ∀ t ω, ω ∈ F t → WangWu.retainedGreenEnergy (W · ω) N (fun z => ∑ k ∈ s,
      (E k).indicator (fun _ => (1 : ℝ)) ω * ψ k z) =
        WangWu.retainedGreenEnergy (W · ω) N ((∑ k ∈ t, ψ k : TestOn upperHalfPlaneOpens) : ℂ → ℝ) := by
    intro t ω hω
    congr 1
    funext z
    rw [hpattern t ω hω (fun _ => 1) (fun k => ψ k z), testOn_sum_apply]
    simp only [one_mul]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_all_iff.2 fun t : s.powerset => (hpat t.1 t.2).1] with ω hω
    have hmem : Sω ω ∈ s.powerset := Finset.mem_powerset.2 (Finset.filter_subset _ s)
    rw [hQS (Sω ω) ω rfl]
    exact hω ⟨Sω ω, hmem⟩ rfl
  -- sum over the patterns
  have hint1 : ∀ t ∈ s.powerset, Integrable ((F t).indicator fun ω => g ω * cexp (((∑ k ∈ s, (E k).indicator
      (fun ω => h ω (ψ k) - lamf k ω) ω : ℝ) : ℂ) * I)) P := by
    intro t ht
    have hY : Measurable fun ω => ∑ k ∈ s, (E k).indicator (fun ω => h ω (ψ k) - lamf k ω) ω :=
      Finset.measurable_sum _ fun k _ => (((Sobolev.measurable_distOn_apply _).comp hC.2.1).sub
        (stronglyMeasurable_condExp.mono hNle).measurable).indicator (hNle _ (hEm k))
    refine Integrable.indicator ?_ (hNle _ (hFm t ht))
    refine Integrable.of_bound ((hgm.mono hNle).aestronglyMeasurable.mul (Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp hY).mul_const _)).aestronglyMeasurable) 1 (Eventually.of_forall fun ω => ?_)
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hgb ω
  calc ∫ ω, g ω * cexp (((∑ k ∈ s, (E k).indicator (fun ω => h ω (ψ k) - lamf k ω) ω : ℝ) : ℂ) * I) ∂P
      = ∑ t ∈ s.powerset, ∫ ω, (F t).indicator (fun ω => g ω * cexp (((∑ k ∈ s, (E k).indicator
          (fun ω => h ω (ψ k) - lamf k ω) ω : ℝ) : ℂ) * I)) ω ∂P := by
        rw [← integral_finsetSum _ hint1]
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        dsimp only
        exact (hpart (fun ω => g ω * cexp (((∑ k ∈ s, (E k).indicator
          (fun ω => h ω (ψ k) - lamf k ω) ω : ℝ) : ℂ) * I)) ω).symm
    _ = ∑ t ∈ s.powerset, ∫ ω, (F t).indicator (fun ω => g ω * ((Real.exp (-(1 / 2) *
          WangWu.retainedGreenEnergy (W · ω) N
          ((∑ k ∈ t, ψ k : TestOn upperHalfPlaneOpens) : ℂ → ℝ)) : ℝ) : ℂ)) ω ∂P :=
        Finset.sum_congr rfl fun t ht => (hpat t ht).2.2
    _ = _ := by
        rw [← integral_finsetSum _ fun t ht => (hpat t ht).2.1]
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        dsimp only
        rw [Finset.sum_eq_single (Sω ω)]
        · rw [indicator_of_mem (show ω ∈ F (Sω ω) from rfl), hQS (Sω ω) ω rfl]
        · intro t _ hne
          exact indicator_of_notMem (fun h' => hne h'.symm) _
        · intro hn
          exact absurd (Finset.mem_powerset.2 (Finset.filter_subset _ s)) hn

/-! ### The approximants along the coupling -/

theorem aGreen_congr {V V' : ℝ → ℝ} (hV : Continuous V) (hV' : Continuous V') {T : ℝ} (hT : 0 ≤ T)
    (heq : EqOn V V' (Icc 0 T)) (a b : ℂ) : aGreen V T a b = aGreen V' T a b := by
  have hK : fwdHull V T = fwdHull V' T :=
    YuanCorollary13.fwdHull_eq_of_eqOn_Icc hV hV' hT fun r hr => heq hr
  unfold aGreen actDom vtKer
  rw [hK, Ito.fwdMap_congr_of_eqOn heq, Ito.fwdMap_congr_of_eqOn (z := b) heq]

omit mΩ [IsProbabilityMeasure P] in
/-- On a good path, the history Green energy at `N` is the conditional covariance `G_{D_N}(φ, φ)`. -/
theorem histC_eq {ω : Ω} (hg : IsGoodPath W VL VR ζ ω) (N : ℕ) (φ : TestOn upperHalfPlaneOpens) :
    histC N φ (stopHistory (cstop (N : ℝ≥0)) (stopHistory (natStop N) (killedHistory W VL VR ζ ω))) =
      covAt W N φ φ ω := by
  rw [stopHistory_cstop_natStop le_rfl, covAt,
    show actDom (fun s : ℝ => W s.toNNReal ω) ((N : ℝ≥0) : ℝ) = actDom (Ito.rpath fun t => W t ω) ((N : ℝ≥0) : ℝ)
      from rfl, zeroGFFTestCov_actDom_eq (continuous_rpath_of hg.continuous) (by simp [Ito.rpath, hg.2.1])
      (NNReal.coe_nonneg _) φ φ, histC]
  have hpath := regPath_stopHistory hg (cstop (N : ℝ≥0))
  refine integral_congr_ae (Eventually.of_forall fun a => integral_congr_ae (Eventually.of_forall fun b => ?_))
  show φ a * (vtKerH (N : ℝ) (N : ℝ) (stopHistory (cstop (N : ℝ≥0)) (killedHistory W VL VR ζ ω), a, b)).toReal *
    φ b = φ a * φ b * aGreen (Ito.rpath fun t => W t ω) ((N : ℝ≥0) : ℝ) a b
  rw [vtKerH_toReal_eq, hpath, NNReal.coe_natCast]
  have hc1 : Continuous (Ito.rpath fun t => W (min t (cstop (N : ℝ≥0) (killedHistory W VL VR ζ ω))) ω) :=
    continuous_rpath_of (hg.continuous.comp (continuous_id.min continuous_const))
  rw [aGreen_congr hc1 (continuous_rpath_of hg.continuous) (Nat.cast_nonneg N) (fun r hr => ?_)]
  · ring
  · simp only [Ito.rpath, cstop]
    congr 1
    exact min_eq_left (by
      have := hr.2
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]
      exact_mod_cast this)

omit mΩ [IsProbabilityMeasure P] in
open scoped Classical in
/-- On a good path, the history pocket energy is the retained energy of the pocket part. -/
theorem histPocQ_eq {ω : Ω} (hg : IsGoodPath W VL VR ζ ω) (N : ℕ) (φ : TestOn upperHalfPlaneOpens) (n : ℕ) :
    histPocQ N φ n (stopHistory (natStop N) (killedHistory W VL VR ζ ω)) =
      WangWu.retainedGreenEnergy (W · ω) N (fun z => ∑ k ∈ pIdx φ n,
        {ω | histPoc N (tsupport (pouTest φ n k)) (stopHistory (natStop N) (killedHistory W VL VR ζ ω))}.indicator
          (fun _ => (1 : ℝ)) ω * pouTest φ n k z) := by
  rw [histPocQ, histQ_eq hg]
  congr 1
  funext z
  rw [testOn_sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : histPoc N (tsupport (pouTest φ n k)) (stopHistory (natStop N) (killedHistory W VL VR ζ ω))
  · simp [hk, Set.indicator]
  · simp [hk, Set.indicator]

/-- `L²`-convergence to `0` gives `L¹`-convergence to `0`. -/
theorem tendsto_integral_abs_of_sq {Y : ℕ → Ω → ℝ} (hY : ∀ n, MemLp (Y n) 2 P)
    (h : Tendsto (fun n => ∫ ω, Y n ω ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |Y n ω| ∂P) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := ε / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨n₀, hn₀⟩ := (Metric.tendsto_atTop.1 h) (δ ^ 2) (by positivity)
  refine ⟨n₀, fun n hn => ?_⟩
  have h1 := hn₀ n hn
  rw [Real.dist_eq, sub_zero] at h1 ⊢
  have hint := (hY n).integrable_sq
  have habs : Integrable (fun ω => |Y n ω|) P := ((hY n).integrable one_le_two).abs
  have hpt : ∀ ω, |Y n ω| ≤ δ + Y n ω ^ 2 / δ := by
    intro ω
    rw [← sub_nonneg]
    have : δ + Y n ω ^ 2 / δ - |Y n ω| = (|Y n ω| - δ) ^ 2 / δ + |Y n ω| := by
      field_simp; rw [show Y n ω ^ 2 = |Y n ω| ^ 2 from (sq_abs _).symm]; ring
    rw [this]; positivity
  have hle : ∫ ω, |Y n ω| ∂P ≤ ∫ ω, (δ + Y n ω ^ 2 / δ) ∂P :=
    integral_mono habs ((integrable_const δ).add (hint.div_const δ)) hpt
  rw [integral_add (integrable_const δ) (hint.div_const δ), integral_const, integral_div] at hle
  have hu : P.real Set.univ = 1 := by simp [Measure.real]
  rw [hu, one_smul] at hle
  have hnn : 0 ≤ ∫ ω, |Y n ω| ∂P := integral_nonneg fun ω => abs_nonneg _
  have hsq : 0 ≤ ∫ ω, Y n ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  rw [abs_of_nonneg hnn]
  rw [abs_of_nonneg hsq] at h1
  have : (∫ ω, Y n ω ^ 2 ∂P) / δ < δ := by rw [div_lt_iff₀ hδ0]; nlinarith
  linarith

open scoped Classical in
/-- **The common Borel approximants** (Aux. lemma 50, last paragraph): for a coupling with infinite lifetime and a
continuous trace, `N ≥ 1`, a test `φ` and a Borel set `S` of histories,
`∫_{H_N ∈ S} kerApprox_n(H_N) → ∫_{H_N ∈ S} e^{i(h, φ)}`. -/
theorem tendsto_setIntegral_kerApprox (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hX : IsMeasurableKilledDriving W VL VR ζ)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : IsStoppingTime (drivingFiltration P hX) (ruleTime (natStop N) W VL VR ζ)) (φ : TestOn upperHalfPlaneOpens)
    {S : Set (HistorySpace nL nR)} (hS : MeasurableSet S) :
    Tendsto (fun n => ∫ ω in (fun ω => stopHistory (natStop N) (killedHistory W VL VR ζ ω)) ⁻¹' S,
        kerApprox κ ρL ρR N φ n (stopHistory (natStop N) (killedHistory W VL VR ζ ω)) ∂P) atTop
      (𝓝 (∫ ω in (fun ω => stopHistory (natStop N) (killedHistory W VL VR ζ ω)) ⁻¹' S,
        cexp ((h ω φ : ℂ) * I) ∂P)) := by
  obtain ⟨u₀, hu₀⟩ := exists_bhe κ ρL ρR xL xR
  have hNσ : IsStoppingTime (drivingFiltration P hX) fun _ : Ω => ((N : ℝ≥0) : WithTop ℝ≥0) := hN
  have hms : hNσ.measurableSpace = hN.measurableSpace := rfl
  have hlt : ∀ᵐ ω ∂P, (((N : ℝ≥0) : ℝ≥0) : ℝ≥0∞) < ζ ω :=
    hζ.mono fun ω hω => by rw [hω]; exact ENNReal.coe_lt_top
  obtain ⟨AN, hAN, hANK, -⟩ := exists_hullVersion hC hκ hX hNσ hlt
  set Hh : Ω → HistorySpace nL nR := fun ω => stopHistory (natStop N) (killedHistory W VL VR ζ ω) with hHh
  have hHm : Measurable[hN.measurableSpace] Hh := measurable_stopHistory_killedHistory hX hN
  set G := Hh ⁻¹' S with hGdef
  have hGN : MeasurableSet[hN.measurableSpace] G := hHm hS
  have hNle := hN.measurableSpace_le
  have hGm : MeasurableSet G := hNle _ hGN
  have hh0m := measurable_centredField hC.2.1 u₀
  have hΓle : histGerm hNσ.measurableSpace AN (centredField h u₀) ≤ mΩ :=
    histGerm_le hNσ.measurableSpace_le hAN hh0m
  have hNΓ : hN.measurableSpace ≤ histGerm hNσ.measurableSpace AN (centredField h u₀) := le_histGerm _ _
  have hgood := ae_isGoodPath hC.1 hζ
  have hL2 := tendsto_integral_sq_exhaust hC hκ hu₀ hX hζ htr hN1 hNσ hAN hANK φ
  set Y : ℕ → Ω → ℝ := fun n ω => (P[fun ω' => centredField h u₀ ω' φ |
        histGerm hNσ.measurableSpace AN (centredField h u₀)]) ω -
      ∑ k ∈ pIdx φ n, ((P[fun ω' => h ω' (pouTest φ n k) |
        (isStoppingTime_pieceT hC hζ hX φ N n k).measurableSpace]) ω - ∫ z, u₀ z * pouTest φ n k z) -
      ∑ k ∈ pIdx φ n, {ω | histPoc N (tsupport (pouTest φ n k))
          (stopHistory (natStop N) (killedHistory W VL VR ζ ω))}.indicator
        (fun ω => h ω (pouTest φ n k) - (P[fun ω' => h ω' (pouTest φ n k) | hNσ.measurableSpace]) ω) ω with hYdef
  have hY2 : ∀ n, MemLp (Y n) 2 P := by
    intro n
    refine ((((memLp_centredField hC hu₀ φ).condExp one_le_two).sub (memLp_finsetSum _ fun k _ =>
      ((memLp_pairing hC hu₀ (pouTest φ n k)).condExp one_le_two).sub
        (memLp_const (∫ z, u₀ z * pouTest φ n k z)))).sub (memLp_finsetSum _ fun k _ =>
      ((memLp_pairing hC hu₀ (pouTest φ n k)).sub ((memLp_pairing hC hu₀ (pouTest φ n k)).condExp
        one_le_two)).indicator (hNle _ (measurableSet_pocketEvent hX hN _))))
  have hL1 := tendsto_integral_abs_of_sq hY2 hL2
  have hω₀ : ∃ ω₀ : Ω, True := by
    obtain ⟨ω₀, -⟩ := hgood.exists
    exact ⟨ω₀, trivial⟩
  obtain ⟨ω₀, -⟩ := hω₀
  -- the bound at each scale
  have hbound : ∀ n, ‖(∫ ω in G, cexp ((h ω φ : ℂ) * I) ∂P) -
      ∫ ω in G, kerApprox κ ρL ρR N φ n (Hh ω) ∂P‖ ≤ ∫ ω, |Y n ω| ∂P := by
    intro n
    set X : Ω → ℝ := fun ω => centredField h u₀ ω φ with hXdef
    set c : ℝ := ∫ z, u₀ z * φ z with hcdef
    set N0 := P[X | histGerm hNσ.measurableSpace AN (centredField h u₀)] with hN0
    set C : Ω → ℝ := fun ω => covAt W N φ φ ω with hCdef
    set A : Ω → ℝ := fun ω => ∑ k ∈ pIdx φ n, ((P[fun ω' => h ω' (pouTest φ n k) |
        (isStoppingTime_pieceT hC hζ hX φ N n k).measurableSpace]) ω - ∫ z, u₀ z * pouTest φ n k z) with hAdef
    set YS : Ω → ℝ := fun ω => ∑ k ∈ pIdx φ n, {ω | histPoc N (tsupport (pouTest φ n k))
          (stopHistory (natStop N) (killedHistory W VL VR ζ ω))}.indicator
        (fun ω => h ω (pouTest φ n k) - (P[fun ω' => h ω' (pouTest φ n k) | hN.measurableSpace]) ω) ω
      with hYSdef
    have hYeq : ∀ ω, Y n ω = N0 ω - A ω - YS ω := fun ω => rfl
    have hgerm := ae_condExp_exp_germ_eq hC hκ hu₀ hX hNσ hlt hAN hANK φ
    have hC0 : ∀ᵐ ω ∂P, 0 ≤ C ω := by
      filter_upwards [ae_isOpen_actDom hC hX hNσ hlt] with ω ho
      exact LocalSets.zeroGFFTestCov_self_nonneg ho sdiff_subset φ
    have hcN : ∀ ω, cexp ((h ω φ : ℂ) * I) = cexp ((c : ℂ) * I) * cexp (I * (X ω : ℂ)) := by
      intro ω; rw [← Complex.exp_add]; simp only [hXdef]; rw [centredField_apply h hu₀.1]; congr 1; push_cast; ring
    have hXm : Measurable X := measurable_centredField_apply hC u₀ φ
    have hgi : Integrable (fun ω => cexp (I * (X ω : ℂ))) P :=
      Integrable.of_bound (Complex.measurable_exp.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp hXm))).aestronglyMeasurable 1
        (Eventually.of_forall fun ω => by rw [mul_comm]; exact (Complex.norm_exp_ofReal_mul_I _).le)
    -- the germ side
    set U : Ω → ℂ := fun ω => cexp ((c : ℂ) * I) * (cexp (I * (N0 ω : ℂ)) *
      ((Real.exp (-(1 / 2) * C ω) : ℝ) : ℂ)) with hUdef
    have hU : ∫ ω in G, cexp ((h ω φ : ℂ) * I) ∂P = ∫ ω in G, U ω ∂P := by
      have e1 : ∫ ω in G, cexp ((h ω φ : ℂ) * I) ∂P =
          cexp ((c : ℂ) * I) * ∫ ω in G, cexp (I * (X ω : ℂ)) ∂P := by
        rw [← integral_const_mul]; exact setIntegral_congr_fun hGm fun ω _ => hcN ω
      rw [e1, ← setIntegral_condExp hΓle hgi (hNΓ _ hGN), ← integral_const_mul]
      refine setIntegral_congr_ae hGm ?_
      filter_upwards [hgerm] with ω hω _
      rw [hω]
    have hUi : IntegrableOn U G P := by
      refine Integrable.integrableOn (Integrable.of_bound ?_ 1 ?_)
      · refine AEStronglyMeasurable.congr (f := fun ω => cexp ((c : ℂ) * I) *
          (P[fun ω => cexp (I * (X ω : ℂ)) | histGerm hNσ.measurableSpace AN (centredField h u₀)]) ω) ?_ ?_
        · exact aestronglyMeasurable_const.mul
            ((stronglyMeasurable_condExp.mono hΓle).aestronglyMeasurable)
        · filter_upwards [hgerm] with ω hω
          simp only [hUdef]
          rw [hω]
      · filter_upwards [hC0] with ω hc0
        rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, mul_comm I, Complex.norm_exp_ofReal_mul_I,
          one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.2 (by nlinarith)
    -- the explicit side
    set Z : Ω → ℂ := fun ω => cexp ((c : ℂ) * I) * (cexp (I * ((A ω + YS ω : ℝ) : ℂ)) *
      ((Real.exp (-(1 / 2) * C ω) : ℝ) : ℂ)) with hZdef
    have hUZ : ∀ᵐ ω ∂P, ‖U ω - Z ω‖ ≤ |Y n ω| := by
      filter_upwards [hC0] with ω hc0
      have e : U ω - Z ω = cexp ((c : ℂ) * I) * ((cexp (I * (N0 ω : ℂ)) - cexp (I * ((A ω + YS ω : ℝ) : ℂ))) *
          ((Real.exp (-(1 / 2) * C ω) : ℝ) : ℂ)) := by
        simp only [hUdef, hZdef]; ring
      rw [e, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      have h1 := Sec7.norm_exp_mul_I_sub_exp_mul_I_le (N0 ω) (A ω + YS ω)
      have h2 : Real.exp (-(1 / 2) * C ω) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      have h3 : N0 ω - (A ω + YS ω) = Y n ω := by rw [hYeq]; ring
      rw [h3] at h1
      calc _ ≤ |Y n ω| * 1 := mul_le_mul h1 h2 (Real.exp_pos _).le (abs_nonneg _)
        _ = |Y n ω| := mul_one _
    -- the Borel factor of the history
    set Φ : HistorySpace nL nR → ℂ := fun γ => cexp (((∑ k ∈ pIdx φ n, charMean (histG κ ρL ρR) (pouTest φ n k)
        (stopHistory (safeRule (tsupport (pouTest φ n k)) (testLow (pouTest φ n k)) N n) γ) : ℝ) : ℂ) * I) *
      ((Real.exp (-(1 / 2) * max 0 (histC N φ (stopHistory (cstop (N : ℝ≥0)) γ))) : ℝ) : ℂ) with hΦdef
    have hΦm : Measurable Φ := by
      have hm : Measurable fun γ : HistorySpace nL nR => ∑ k ∈ pIdx φ n, charMean (histG κ ρL ρR) (pouTest φ n k)
          (stopHistory (safeRule (tsupport (pouTest φ n k)) (testLow (pouTest φ n k)) N n) γ) :=
        Finset.measurable_sum _ fun k _ => (measurable_charMean (measurable_histG κ ρL ρR) _).comp
          (measurable_stopHistory (measurable_safeRule (pouTest φ n k).tsupport_subset (testLow_pos _) N n))
      have hq : Measurable fun γ : HistorySpace nL nR => max 0 (histC N φ (stopHistory (cstop (N : ℝ≥0)) γ)) :=
        measurable_const.max ((measurable_histC N φ).comp (measurable_stopHistory (measurable_cstop _)))
      exact (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp hm).mul_const _)).mul
        (Complex.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hq)))
    set g' : Ω → ℂ := G.indicator fun ω => Φ (Hh ω) with hg'def
    have hg'm : StronglyMeasurable[hN.measurableSpace] g' :=
      ((hΦm.comp hHm).stronglyMeasurable).indicator hGN
    have hg'b : ∀ ω, ‖g' ω‖ ≤ 1 := by
      intro ω
      by_cases hω : ω ∈ G
      · rw [hg'def, indicator_of_mem hω]
        simp only [hΦdef]
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.2 (by nlinarith [le_max_left 0 (histC N φ (stopHistory (cstop (N : ℝ≥0)) (Hh ω)))])
      · rw [hg'def, indicator_of_notMem hω, norm_zero]; exact zero_le_one
    have hpoc := integral_mul_exp_pocketSum hC hκ hζ hX hN (pIdx φ n) (fun k => pouTest φ n k) hg'm hg'b
    -- the frozen means are read from the history
    have hcsum : ∑ k ∈ pIdx φ n, ∫ z, u₀ z * pouTest φ n k z = c := by
      have e : ∀ k, ∫ z, u₀ z * pouTest φ n k z = h ω₀ (pouTest φ n k) - centredField h u₀ ω₀ (pouTest φ n k) := by
        intro k; rw [centredField_apply h hu₀.1]; ring
      have hM : testRad φ * 2 ^ n ≤ (scaleIdx (testRad φ) n : ℝ) := Nat.le_ceil _
      have hsum : ∑ k ∈ pIdx φ n, pouTest φ n k = φ :=
        sum_pouTest (M := scaleIdx (testRad φ) n) (tsupport_subset_testRad φ) hM
      simp only [e, Finset.sum_sub_distrib]
      rw [← map_sum (h ω₀), ← map_sum (centredField h u₀ ω₀), hsum, hcdef, centredField_apply h hu₀.1]
      ring
    have hchar : ∀ᵐ ω ∂P, ∑ k ∈ pIdx φ n, charMean (histG κ ρL ρR) (pouTest φ n k)
        (stopHistory (safeRule (tsupport (pouTest φ n k)) (testLow (pouTest φ n k)) N n) (Hh ω)) = A ω + c := by
      have hk : ∀ k : ℤ × ℤ, ∀ᵐ ω ∂P, charMean (histG κ ρL ρR) (pouTest φ n k)
          (stopHistory (safeRule (tsupport (pouTest φ n k)) (testLow (pouTest φ n k)) N n) (Hh ω)) =
          (P[fun ω' => h ω' (pouTest φ n k) | (isStoppingTime_pieceT hC hζ hX φ N n k).measurableSpace]) ω := by
        intro k
        have h1 := ae_charMean_eq_condExp (κ := κ) (ρL := ρL) (ρR := ρR) hC hζ hX
          (s := safeKRule (tsupport (pouTest φ n k)) (testLow (pouTest φ n k)) N n)
          (isStoppingTime_pieceT hC hζ hX φ N n k) (pouTest φ n k)
        filter_upwards [h1, ae_disjoint_pieceT hC hζ φ N n k] with ω e1 hd
        simp only [hHh]
        rw [stopHistory_stopHistory_natStop _ (safeRule_le _ _ _ _ _)]
        exact e1 hd
      filter_upwards [ae_all_iff.2 hk] with ω hω
      simp only [hω, hAdef, Finset.sum_sub_distrib, hcsum]
      ring
    have hYSm : Measurable YS := Finset.measurable_sum _ fun k _ =>
      (((Sobolev.measurable_distOn_apply _).comp hC.2.1).sub
        (stronglyMeasurable_condExp.mono hNle).measurable).indicator
        (hNle _ (measurableSet_pocketEvent hX hN _))
    have hZg : ∀ᵐ ω ∂P, G.indicator Z ω = g' ω * cexp (((YS ω : ℝ) : ℂ) * I) := by
      filter_upwards [hchar, hgood, hC0] with ω e1 hg hc0
      by_cases hω : ω ∈ G
      · rw [indicator_of_mem hω, hg'def, indicator_of_mem hω]
        simp only [hΦdef, hZdef]
        rw [e1, show stopHistory (cstop (N : ℝ≥0)) (Hh ω) = stopHistory (cstop (N : ℝ≥0))
          (stopHistory (natStop N) (killedHistory W VL VR ζ ω)) from rfl, histC_eq hg, max_eq_right hc0]
        calc cexp ((c : ℂ) * I) * (cexp (I * ((A ω + YS ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * C ω) : ℝ) : ℂ))
            = cexp ((c : ℂ) * I + I * ((A ω + YS ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * C ω) : ℝ) : ℂ) := by
              rw [Complex.exp_add]; ring
          _ = cexp ((((A ω + c : ℝ) : ℂ) * I) + ((YS ω : ℝ) : ℂ) * I) * ((Real.exp (-(1 / 2) * C ω) : ℝ) : ℂ) := by
              congr 2; push_cast; ring
          _ = _ := by rw [Complex.exp_add]; ring
      · rw [indicator_of_notMem hω, hg'def, indicator_of_notMem hω, zero_mul]
    have hgk : ∀ᵐ ω ∂P, g' ω * ((Real.exp (-(1 / 2) * WangWu.retainedGreenEnergy (W · ω) N
        (fun z => ∑ k ∈ pIdx φ n, {ω | histPoc N (tsupport (pouTest φ n k))
          (stopHistory (natStop N) (killedHistory W VL VR ζ ω))}.indicator (fun _ => (1 : ℝ)) ω *
            pouTest φ n k z)) : ℝ) : ℂ) =
        G.indicator (fun ω => kerApprox κ ρL ρR N φ n (Hh ω)) ω := by
      filter_upwards [hgood, hC0] with ω hg hc0
      by_cases hω : ω ∈ G
      · rw [hg'def, indicator_of_mem hω, indicator_of_mem hω]
        simp only [hΦdef, kerApprox]
        rw [show stopHistory (cstop (N : ℝ≥0)) (Hh ω) = stopHistory (cstop (N : ℝ≥0))
          (stopHistory (natStop N) (killedHistory W VL VR ζ ω)) from rfl, histC_eq hg,
          max_eq_right hc0, show histPocQ N φ n (Hh ω) = histPocQ N φ n
          (stopHistory (natStop N) (killedHistory W VL VR ζ ω)) from rfl, histPocQ_eq hg]
        rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
        congr 3
        ring
      · rw [hg'def, indicator_of_notMem hω, indicator_of_notMem hω, zero_mul]
    have hZi : IntegrableOn Z G P := by
      rw [← integrable_indicator_iff hGm]
      refine (Integrable.of_bound ?_ 1 (Eventually.of_forall fun ω => ?_)).congr (hZg.mono fun ω hω => hω.symm)
      · exact (hg'm.mono hNle).aestronglyMeasurable.mul (Complex.measurable_exp.comp
          ((Complex.measurable_ofReal.comp hYSm).mul_const _)).aestronglyMeasurable
      · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]; exact hg'b ω
    have hZk : ∫ ω in G, Z ω ∂P = ∫ ω in G, kerApprox κ ρL ρR N φ n (Hh ω) ∂P := by
      rw [← integral_indicator hGm, ← integral_indicator hGm, integral_congr_ae hZg, hpoc.2]
      exact integral_congr_ae hgk
    rw [hU, ← hZk, ← integral_sub hUi hZi]
    have hYi : Integrable (fun ω => |Y n ω|) P := ((hY2 n).integrable one_le_two).abs
    calc ‖∫ ω in G, (U ω - Z ω) ∂P‖ ≤ ∫ ω in G, ‖U ω - Z ω‖ ∂P := norm_integral_le_integral_norm _
      _ ≤ ∫ ω in G, |Y n ω| ∂P := setIntegral_mono_ae (hUi.sub hZi).norm hYi.integrableOn hUZ
      _ ≤ ∫ ω, |Y n ω| ∂P := setIntegral_le_integral hYi (Eventually.of_forall fun ω => abs_nonneg _)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hL1
  rw [norm_sub_rev]
  exact hbound n

end Coupling

/-! ### Aux. lemma 51 at the integer times, every `κ > 0` -/

section Law

universe u v

variable {κ rL rR : ℝ}

/-- **Aux. lemma 51 at an integer time `N ≥ 1`, every `κ > 0`**: two couplings of the two-seed word `SLE_κ(rL; rR)`
(`rL, rR > −2`) with continuous traces have the same joint law of the field and the history at `N` (the common Borel
approximants `kerApprox` have the same integrals under the common history law). -/
theorem map_prod_stopHistory_eq_of_one_le (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR) {N : ℕ} (hN1 : 1 ≤ N)
    {Ω₁ : Type u} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ VR₁ : Fin 1 → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ}
    {ζ₁ : Ω₁ → ℝ≥0∞} {h₁ : Ω₁ → DistOn upperHalfPlaneOpens}
    (hC₁ : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁)
    (htr₁ : ∀ᵐ ω ∂P₁, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₁ t ω) (ζ₁ ω) η)
    {Ω₂ : Type v} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
    {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}
    (hC₂ : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂)
    (htr₂ : ∀ᵐ ω ∂P₂, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₂ t ω) (ζ₂ ω) η) :
    P₁.map (fun ω => (h₁ ω, stopHistory (natStop N) (killedHistory W₁ VL₁ VR₁ ζ₁ ω))) =
      P₂.map (fun ω => (h₂ ω, stopHistory (natStop N) (killedHistory W₂ VL₂ VR₂ ζ₂ ω))) := by
  obtain ⟨hX₁, -⟩ := hC₁.2.2.2
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  have hζ₁ := R7.ae_lifetime_eq_top hκ hL hR hC₁.1
  have hζ₂ := R7.ae_lifetime_eq_top hκ hL hR hC₂.1
  have hst : Measurable (stopHistory (nL := 1) (nR := 1) (natStop N)) :=
    measurable_stopHistory (measurable_natStop N)
  have hH₁ : Measurable fun ω => stopHistory (natStop N) (killedHistory W₁ VL₁ VR₁ ζ₁ ω) :=
    hst.comp (measurable_killedHistory hX₁)
  have hH₂ : Measurable fun ω => stopHistory (natStop N) (killedHistory W₂ VL₂ VR₂ ζ₂ ω) :=
    hst.comp (measurable_killedHistory hX₂)
  have hlaw : P₁.map (fun ω => stopHistory (natStop N) (killedHistory W₁ VL₁ VR₁ ζ₁ ω)) =
      P₂.map (fun ω => stopHistory (natStop N) (killedHistory W₂ VL₂ VR₂ ζ₂ ω)) :=
    map_stopHistory_eq (killedStateLawUnique_of_isOrderedForceWord hκ _ _ LP.isOrderedForceWord_twoSeed)
      (measurable_natStop N) hC₁.1 hX₁ hC₂.1 hX₂
  refine Sobolev.measure_eq_of_setIntegral_exp fun φ S hS => ?_
  have hexp : Measurable fun p : DistOn upperHalfPlaneOpens × HistorySpace 1 1 => cexp (((p.1 φ : ℝ) : ℂ) * I) :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      ((Sobolev.measurable_distOn_apply φ).comp measurable_fst)).mul_const _)
  have hset : MeasurableSet (univ ×ˢ S : Set (DistOn upperHalfPlaneOpens × HistorySpace 1 1)) :=
    MeasurableSet.univ.prod hS
  rw [setIntegral_map hset hexp.aestronglyMeasurable (hC₁.2.1.prodMk hH₁).aemeasurable,
    setIntegral_map hset hexp.aestronglyMeasurable (hC₂.2.1.prodMk hH₂).aemeasurable]
  have e₁ : (fun ω => (h₁ ω, stopHistory (natStop N) (killedHistory W₁ VL₁ VR₁ ζ₁ ω))) ⁻¹' (univ ×ˢ S) =
      (fun ω => stopHistory (natStop N) (killedHistory W₁ VL₁ VR₁ ζ₁ ω)) ⁻¹' S := by
    ext ω; simp
  have e₂ : (fun ω => (h₂ ω, stopHistory (natStop N) (killedHistory W₂ VL₂ VR₂ ζ₂ ω))) ⁻¹' (univ ×ˢ S) =
      (fun ω => stopHistory (natStop N) (killedHistory W₂ VL₂ VR₂ ζ₂ ω)) ⁻¹' S := by
    ext ω; simp
  rw [e₁, e₂]
  have t₁ := tendsto_setIntegral_kerApprox hC₁ hκ hζ₁ hX₁ htr₁ hN1 (isStoppingTime_natStop (P := P₁) hX₁ N) φ hS
  have t₂ := tendsto_setIntegral_kerApprox hC₂ hκ hζ₂ hX₂ htr₂ hN1 (isStoppingTime_natStop (P := P₂) hX₂ N) φ hS
  refine tendsto_nhds_unique t₁ (t₂.congr fun n => ?_)
  have hk : ∀ μ : Measure (HistorySpace 1 1), AEStronglyMeasurable (kerApprox κ (fun _ : Fin 1 => rL)
      (fun _ : Fin 1 => rR) N φ n) μ := fun μ =>
    (measurable_kerApprox κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) N φ n).aestronglyMeasurable
  rw [← setIntegral_map hS (hk _) hH₂.aemeasurable, ← setIntegral_map hS (hk _) hH₁.aemeasurable, hlaw]

/-- **Aux. lemma 51 at every integer time, every `κ > 0`** (the time `0` from the time `1`). -/
theorem map_prod_stopHistory_eq (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR) (N : ℕ)
    {Ω₁ : Type u} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ VR₁ : Fin 1 → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ}
    {ζ₁ : Ω₁ → ℝ≥0∞} {h₁ : Ω₁ → DistOn upperHalfPlaneOpens}
    (hC₁ : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁)
    (htr₁ : ∀ᵐ ω ∂P₁, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₁ t ω) (ζ₁ ω) η)
    {Ω₂ : Type v} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
    {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}
    (hC₂ : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂)
    (htr₂ : ∀ᵐ ω ∂P₂, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₂ t ω) (ζ₂ ω) η) :
    P₁.map (fun ω => (h₁ ω, stopHistory (natStop N) (killedHistory W₁ VL₁ VR₁ ζ₁ ω))) =
      P₂.map (fun ω => (h₂ ω, stopHistory (natStop N) (killedHistory W₂ VL₂ VR₂ ζ₂ ω))) := by
  have h1 := map_prod_stopHistory_eq_of_one_le hκ hL hR (N := N + 1) (by omega) hC₁ htr₁ hC₂ htr₂
  have hst : Measurable (stopHistory (nL := 1) (nR := 1) (natStop (N + 1))) :=
    measurable_stopHistory (measurable_natStop (N + 1))
  have hm₁ : Measurable fun ω => (h₁ ω, stopHistory (natStop (N + 1)) (killedHistory W₁ VL₁ VR₁ ζ₁ ω)) :=
    hC₁.2.1.prodMk (hst.comp (measurable_killedHistory hC₁.2.2.2.1))
  have hm₂ : Measurable fun ω => (h₂ ω, stopHistory (natStop (N + 1)) (killedHistory W₂ VL₂ VR₂ ζ₂ ω)) :=
    hC₂.2.1.prodMk (hst.comp (measurable_killedHistory hC₂.2.2.2.1))
  have hR' : Measurable fun q : DistOn upperHalfPlaneOpens × HistorySpace 1 1 =>
      (q.1, stopHistory (cstop (N : ℝ≥0)) q.2) :=
    measurable_fst.prodMk ((measurable_stopHistory (measurable_cstop _)).comp measurable_snd)
  have hle : (N : ℝ≥0) ≤ ((N + 1 : ℕ) : ℝ≥0) := by exact_mod_cast Nat.le_succ N
  have e₁ : (fun ω => (h₁ ω, stopHistory (natStop N) (killedHistory W₁ VL₁ VR₁ ζ₁ ω))) =
      (fun q : DistOn upperHalfPlaneOpens × HistorySpace 1 1 => (q.1, stopHistory (cstop (N : ℝ≥0)) q.2)) ∘
        fun ω => (h₁ ω, stopHistory (natStop (N + 1)) (killedHistory W₁ VL₁ VR₁ ζ₁ ω)) := by
    funext ω
    simp only [Function.comp_apply, stopHistory_cstop_natStop hle]
    rfl
  have e₂ : (fun ω => (h₂ ω, stopHistory (natStop N) (killedHistory W₂ VL₂ VR₂ ζ₂ ω))) =
      (fun q : DistOn upperHalfPlaneOpens × HistorySpace 1 1 => (q.1, stopHistory (cstop (N : ℝ≥0)) q.2)) ∘
        fun ω => (h₂ ω, stopHistory (natStop (N + 1)) (killedHistory W₂ VL₂ VR₂ ζ₂ ω)) := by
    funext ω
    simp only [Function.comp_apply, stopHistory_cstop_natStop hle]
    rfl
  rw [e₁, e₂, ← Measure.map_map hR' hm₁, ← Measure.map_map hR' hm₂, h1]

/-- **Aux. lemma 51 at the integer times for the two-seed words, every `κ > 0`** (`Aux50.TraceStopLawUnique`). -/
theorem traceStopLawUnique (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR) :
    Aux50.TraceStopLawUnique.{u, v} κ rL rR := by
  intro Ω₁ m₁ P₁ _ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁ hC₁ htr₁ Ω₂ m₂ P₂ _ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ htr₂ n
  exact map_prod_stopHistory_eq hκ hL hR n hC₁ htr₁ hC₂ htr₂

/-- **Aux. lemma 50's common kernel at the integer times, every `κ > 0`** (`Aux50.HasTraceStopKernel`) for the
two-seed words with seed weights `rL, rR > −2`. -/
theorem hasTraceStopKernel (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR) :
    Aux50.HasTraceStopKernel.{u, v} κ rL rR :=
  Aux50.hasTraceStopKernel_of_traceStopLawUnique (traceStopLawUnique hκ hL hR) (traceStopLawUnique hκ hL hR)
    (traceStopLawUnique hκ hL hR)

end Law

/-! ### The two named inputs -/

universe u v

/-- **Aux. lemma 50 for the R.7 two-seed words at `κ ≥ 8`** (`Aux50Hit.R7KernelGeEightStatement`): **proved**. -/
theorem r7KernelGeEightStatement : Aux50Hit.R7KernelGeEightStatement.{u, v} :=
  fun _ hκ _ _ hL hR _ => hasTraceStopKernel (by linarith) hL hR

/-- **Aux. lemma 50 for the both-low two-seed words at `κ ≥ 8`** (`Aux50Hit.Lemma725KernelGeEightStatement`):
**proved**. -/
theorem lemma725KernelGeEightStatement : Aux50Hit.Lemma725KernelGeEightStatement.{u} :=
  fun _ hκ _ _ hL _ hR _ => hasTraceStopKernel (by linarith) hL hR

/-- **Theorem R.7's field kernel** (`R7.R7FieldKernelStatement`): **proved**. -/
theorem r7FieldKernelStatement : R7.R7FieldKernelStatement.{u, v} :=
  Aux50Hit.r7FieldKernelStatement_of_geEight r7KernelGeEightStatement

/-- **Theorem R.7's determination consequence** (`LP.R7DeterminationStatement`) from the R.7 reference alone. -/
theorem r7DeterminationStatement_of_reference (href : R7.R7ReferenceStatement.{v}) :
    LP.R7DeterminationStatement.{u} :=
  Aux50Hit.r7DeterminationStatement_of_geEight href r7KernelGeEightStatement

/-- **Lemma 7.25, determination** (`LP.Lemma725DeterminationStatement`) from its trace part and the reference alone
(the `κ ≥ 8` kernel is proved). -/
theorem lemma725DeterminationStatement_of_reference (h725t : LP.Lemma725TraceStatement.{u})
    (href : Aux50Hit.Lemma725DetReferenceStatement.{u}) : LP.Lemma725DeterminationStatement.{u} :=
  Aux50Hit.lemma725DeterminationStatement_of_reference h725t href lemma725KernelGeEightStatement

end Aux50Ge8

end InteractingSLE
