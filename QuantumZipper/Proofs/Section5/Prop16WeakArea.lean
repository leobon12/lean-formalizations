import QuantumZipper.Proofs.Section5.Prop16WeakCore

/-!
# Proposition 1.6, D4-a′: area convergence from TV-local convergence of a nearby field

Decision D24 (`DECISIONS.md`). Sheffield, *Conformal weldings of random surfaces*,
arXiv:1012.4797, proof of Proposition 1.6 (p. 25): conditioned on the marked point `x`, the field
is its original law plus `−γ log|x − ·|` plus a continuous function that is "approximately constant"
near `x`. After zooming, the area measure of the canonical field is, up to an error that tends to
`0` in probability, the area measure of a field whose local law converges in total variation to
the `γ`-quantum wedge. The TV part cannot absorb the continuous remainder (Cameron–Martin, D24),
so the two are combined here in law (Slutsky), not in total variation.

`areaConvergesInLawOn_of_tvLocal_close`: let `Z c` be fields whose local coordinates converge in
total variation to those of `Y'`, and suppose that, for every test function `f` supported in
`ball 0 R`, the pairing `∫ f dμ_{Y c}` of the pre-limit area measures is within any `δ > 0` of the
measurable local pairing `locArea γ R f (Z c)` with probability tending to `1`. Then
`AreaConvergesInLawOn γ P Y U P' Y'`.

Proof: the pairing vector of `Z c` is a measurable function `Φ` of `locField N (Z c)`
(`Prop16Area.locArea_eq_comp_locField`), so `E F(Φ(locField N (Z c))) → E' F(pairings of Y')` by
bounded TV duality, and the same TV bound gives tightness; `tendsto_integral_sub_of_close`
(Slutsky) transfers the convergence to the pairings of `Y c`. Own elementary proof.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Area

open TV Factorization

/-- `locField R` factors through the raw coordinates. -/
theorem measurable_locField_of_coords {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {x : α → FieldSample} (hx : AEMeasurable (fun a => coords (x a)) μ) (R : ℕ) :
    AEMeasurable (fun a => locField R (x a)) μ := by
  classical
  let G : (ℕ → ℝ) → ℕ → ℝ := fun v n => if inBall R n then v n else 0
  have hG : Measurable G := measurable_pi_iff.2 fun n => by
    by_cases h : inBall R n
    · simp only [G, h, ite_true]; exact measurable_pi_apply n
    · simp only [G, h, ite_false]; exact measurable_const
  exact hG.comp_aemeasurable hx

/-- **D4-a′.** TV-local convergence of nearby fields `Z c` plus closeness in probability of the
area pairings implies `AreaConvergesInLawOn`. -/
theorem areaConvergesInLawOn_of_tvLocal_close (γ : ℝ) {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℝ → Ω → FieldSample)
    (U : ℝ → Ω → Set ℂ) (Z : ℝ → Ω → FieldSample) (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y' : Ω' → FieldSample)
    (hZ : ∀ c, AEMeasurable (fun ω => coords (Z c ω)) P)
    (hY' : AEMeasurable (fun ω => coords (Y' ω)) P')
    (hTV : ∀ R : ℕ, Tendsto (fun c => tvDist (P.map fun ω => locField R (Z c ω))
      (P'.map fun ω => locField R (Y' ω))) atTop (𝓝 0))
    (hclose : ∀ (R : ℕ) (f : ℂ → ℝ), Continuous f → HasCompactSupport f →
      (∀ z, f z ≠ 0 → z ∈ Metric.ball (0 : ℂ) R) → ∀ δ > 0,
      Tendsto (fun c => P {ω | δ < |∫ z, f z ∂(qAreaMeasureOn γ (Y c ω) (U c ω)) -
        locArea γ R f (Z c ω)|}) atTop (𝓝 0))
    (hgood' : ∀ᵐ ω ∂P', ∃ μ, IsVagueLimitOn H (areaApprox γ (Y' ω)) μ)
    (hmeas : ∀ᶠ c in atTop, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      AEMeasurable (fun ω => ∫ z, f z ∂(qAreaMeasureOn γ (Y c ω) (U c ω))) P) :
    AreaConvergesInLawOn γ P Y U P' Y' := by
  intro m f hf hfc F hF hFb
  obtain ⟨C, hC⟩ := hFb
  obtain ⟨R, hR⟩ : ∃ R : ℕ, ∀ j z, f j z ≠ 0 → z ∈ Metric.ball (0 : ℂ) R := by
    have hb : Bornology.IsBounded (⋃ j, tsupport (f j)) :=
      Bornology.isBounded_iUnion.2 fun j => (hfc j).isBounded
    obtain ⟨r, hr⟩ := hb.subset_ball 0
    exact ⟨⌈r⌉₊, fun j z hz => Metric.ball_subset_ball (Nat.le_ceil r)
      (hr (mem_iUnion.2 ⟨j, subset_tsupport _ hz⟩))⟩
  have hRN : (R : ℝ) + 1 ≤ ((R + 1 : ℕ) : ℝ) := by push_cast; exact le_rfl
  set N := R + 1 with hN
  -- the pairing vector as a measurable function of the local coordinates
  let Φ : (ℕ → ℝ) → Fin m → ℝ := fun y j => locArea γ R (f j) (locRecon N y)
  have hΦm : Measurable Φ := measurable_pi_iff.2 fun j =>
    (measurable_locArea γ R (hf j).measurable).comp (measurable_locRecon N)
  have hΦx : ∀ x, Φ (locField N x) = fun j => locArea γ R (f j) x := fun x => by
    funext j; exact (locArea_eq_comp_locField hRN (f j) x).symm
  have hLm : ∀ c, AEMeasurable (fun ω => locField N (Z c ω)) P := fun c =>
    measurable_locField_of_coords (hZ c) N
  have hLm' : AEMeasurable (fun ω => locField N (Y' ω)) P' :=
    measurable_locField_of_coords hY' N
  set ν := P'.map fun ω => locField N (Y' ω) with hν
  have hFΦ : Measurable fun y => F (Φ y) := hF.measurable.comp hΦm
  -- the limit side
  have hlim : ∫ ω, F (fun j => ∫ z, f j z ∂qAreaMeasure γ (Y' ω)) ∂P' = ∫ y, F (Φ y) ∂ν := by
    rw [hν, integral_map hLm' hFΦ.aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [hgood'] with ω hω
    rw [hΦx]
    congr 1
    funext j
    exact integral_qAreaMeasure_eq_locArea hω (hf j) (hfc j) (hR j)
  -- step 1: the nearby fields, by TV
  have hstep1 : Tendsto (fun c => ∫ ω, F (Φ (locField N (Z c ω))) ∂P) atTop
      (𝓝 (∫ y, F (Φ y) ∂ν)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun c => norm_nonneg _) (fun c => ?_) (g := fun c =>
      2 * max C 1 * (tvDist (P.map fun ω => locField N (Z c ω)) ν).toReal) ?_
    · rw [← integral_map (hLm c) hFΦ.aestronglyMeasurable, Real.norm_eq_abs]
      exact abs_integral_sub_le_mul hFΦ fun y => hC _
    · have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hTV N)).const_mul (2 * max C 1)
      simpa using this
  -- tightness of the nearby pairing vectors
  have htight : ∀ η : ℝ≥0∞, 0 < η → ∃ M : ℝ, ∀ᶠ c in atTop,
      P {ω | M < ‖Φ (locField N (Z c ω))‖} < η := by
    intro η hη
    let A : ℕ → Set (ℕ → ℝ) := fun M => {y | (M : ℝ) < ‖Φ y‖}
    have hAm : ∀ M, MeasurableSet (A M) := fun M =>
      measurableSet_lt measurable_const (continuous_norm.measurable.comp hΦm)
    have hanti : Antitone A := fun M M' hMM y hy => by
      simp only [A, mem_ofPred_eq] at hy ⊢
      exact lt_of_le_of_lt (by exact_mod_cast hMM) hy
    have hempty : (⋂ M, A M) = ∅ := by
      ext y
      simp only [A, mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall,
        not_lt]
      obtain ⟨M, hM⟩ := exists_nat_ge ‖Φ y‖
      exact ⟨M, hM⟩
    have ht := tendsto_measure_iInter_atTop (μ := ν) (fun M => (hAm M).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
    rw [hempty, measure_empty] at ht
    have hη2 : (0 : ℝ≥0∞) < η / 2 := ENNReal.div_pos hη.ne' ENNReal.ofNat_ne_top
    obtain ⟨M, hM⟩ := (ht.eventually (gt_mem_nhds hη2)).exists
    refine ⟨M, ?_⟩
    filter_upwards [(hTV N).eventually (gt_mem_nhds hη2)] with c hc
    have hset : {ω | (M : ℝ) < ‖Φ (locField N (Z c ω))‖} =
        (fun ω => locField N (Z c ω)) ⁻¹' A M := rfl
    rw [hset, ← Measure.map_apply_of_aemeasurable (hLm c) (hAm M)]
    have h1 := le_tvDist (μ := P.map fun ω => locField N (Z c ω)) (ν := ν) (hAm M)
    calc (P.map fun ω => locField N (Z c ω)) (A M) ≤ ν (A M) + tvDist
          (P.map fun ω => locField N (Z c ω)) ν := tsub_le_iff_left.1 h1
      _ < η / 2 + η / 2 := ENNReal.add_lt_add hM hc
      _ = η := ENNReal.add_halves η
  -- step 2: Slutsky
  have hstep2 := tendsto_integral_sub_of_close P hF hC
    (fun c ω => Φ (locField N (Z c ω)))
    (fun c ω j => ∫ z, f j z ∂qAreaMeasureOn γ (Y c ω) (U c ω))
    (fun c => hΦm.comp_aemeasurable (hLm c))
    (hmeas.mono fun c hc => AEMeasurable.of_eval fun j => hc (f j) (hf j) (hfc j))
    htight (fun j δ hδ => by
      simpa only [hΦx] using hclose R (f j) (hf j) (hfc j) (hR j) δ hδ)
  rw [hlim]
  have := hstep2.add hstep1
  rw [zero_add] at this
  exact this.congr fun c => sub_add_cancel _ _

end Prop16Area

end QuantumZipper
