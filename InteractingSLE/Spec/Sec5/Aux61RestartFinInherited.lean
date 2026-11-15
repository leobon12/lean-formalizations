import InteractingSLE.Spec.Sec5.Aux61RestartFinRetargetLog

/-!
# Measurably preserving the original-target derivative branch

Packet PROVE-AUX61-R1. A compact filled retained-hull record supplies the
canonical logarithm and its measurable anchor. Positive scale and real seed
translation alter no imaginary part. The integer correction therefore gives
the literal physical branch `canonDerivLog B ∘ retarget + retargetLog`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec5.Aux61Restart

open Restart Sec7.Lemma71E

/-- Whole-collar normalizations determine the same positive scale as the
existing sequence-based uniqueness theorem. No new boundary comparison input
is introduced by passing from the former to the latter. -/
theorem exists_pos_scale_of_same_collar_limits {D : Set ℂ} (hDo : IsOpen D)
    {φ ψ F₀ F₁ : ℂ → ℂ} (hφ : IsConformalBijection φ D H)
    (hψ : IsConformalBijection ψ D H)
    (hF₀ : ∃ δ > 0, MapsTo F₀ (ball 0 δ ∩ H) D)
    (hF₁ : ∃ δ > 0, MapsTo F₁ (ball 0 δ ∩ H) D)
    (hφ₀ : Tendsto (φ ∘ F₀) (𝓝[H] 0) (𝓝 0))
    (hψ₀ : Tendsto (ψ ∘ F₀) (𝓝[H] 0) (𝓝 0))
    (hφ₁ : Tendsto (fun w => ‖φ (F₁ w)‖) (𝓝[H] 0) atTop)
    (hψ₁ : Tendsto (fun w => ‖ψ (F₁ w)‖) (𝓝[H] 0) atTop) :
    ∃ a : ℝ, 0 < a ∧ EqOn ψ (fun z => (a : ℂ) * φ z) D := by
  have : (𝓝[H] (0 : ℂ)).NeBot := PrimeEnd.approachH_neBot (0 : ℝ)
  obtain ⟨w, hw⟩ := Filter.exists_seq_tendsto (𝓝[H] (0 : ℂ))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hw.eventually
    ((eventually_mem_of_collar hF₀).and (eventually_mem_of_collar hF₁)))
  have hseq := hw.comp (tendsto_add_atTop_nat N)
  exact exists_pos_eqOn_mul_of_tendsto hDo hφ hψ
    (fun n => (hN (n + N) (Nat.le_add_left N n)).1)
    (fun n => (hN (n + N) (Nat.le_add_left N n)).2)
    (hφ₀.comp hseq) (hψ₀.comp hseq) (hφ₁.comp hseq) (hψ₁.comp hseq)

/-- A real seed translation and positive scale preserve the inherited phase;
the only new complex-log summand is the real number `log a`. -/
theorem isDerivLog_pos_scale_sub {D : Set ℂ} (hDo : IsOpen D)
    {f g L : ℂ → ℂ} (hg : DifferentiableOn ℂ g D) (hL : IsDerivLog g L D)
    {a x : ℝ} (ha : 0 < a)
    (heq : EqOn f (fun z => (a : ℂ) * (g z - (x : ℂ))) D) :
    IsDerivLog f (fun z => (Real.log a : ℂ) + L z) D := by
  have hscaled : IsDerivLog (fun z => (a : ℂ) * (g z - (x : ℂ)))
      (fun z => (Real.log a : ℂ) + L z) D := by
    refine ⟨hL.1.const_add _, fun z hz => ?_⟩
    have hd := ((hg z hz).differentiableAt (hDo.mem_nhds hz)).hasDerivAt
    rw [((hd.sub_const (x : ℂ)).const_mul (a : ℂ)).deriv, exp_add,
      ← ofReal_exp, Real.exp_log ha, hL.2 z hz]
  exact IsDerivLog.congr_of_eqOn hDo hscaled heq.symm (fun _ _ => rfl)

/-- The physical canonical branch has a measurable value at every recorded
dense-sequence interior point of its chart domain. -/
theorem measurable_physicalRestartLog_anchor
    {Ω : Type*} [MeasurableSpace Ω] {K : Ω → Set ℂ}
    (hm : IsDyadicHitMeasurable K) (hc : ∀ ω, IsCompact (K ω))
    (hp : ∀ ω, IsPreconnected (K ω ∪ lowerHalf))
    {e : ℕ → ℂ} {N : Ω → ℕ} (hN : Measurable N)
    (hz : ∀ ω, stripRightRetarget (e (N ω)) ∈ H \ fillH (K ω)) :
    Measurable fun ω => physicalRestartLog (fillH (K ω)) (e (N ω)) := by
  have hCB := measurable_at_seq (e := stripRightRetarget ∘ e) hN hz
    (measurable_indicator_canonDerivLog hm hc hp)
  have hR : Measurable fun ω => stripRightRetargetLog (e (N ω)) :=
    (measurable_from_top (f := fun n => stripRightRetargetLog (e n))).comp hN
  exact hCB.add hR

/-- Correct a measurable restart chart to the actual canonical original-target
branch, from its compact filled-hull record and positive-scale representation.
No additional analytic logarithm or its anchor measurability is assumed. -/
theorem exists_measurable_original_target_inherited_shift
    {Ω : Type*} [MeasurableSpace Ω] {c : Ω → Chart}
    (hDc : ∀ ω, IsPreconnected ((c ω).dom : Set ℂ))
    (hDH : ∀ ω, (c ω).dom ≤ upperHalfPlaneOpens)
    (hlog : ∀ ω, ∃ L : ℂ → ℂ, IsDerivLog (c ω).1 L (c ω).dom ∧
      ∀ z ∈ (c ω).dom, (c ω).2.2 z = (L z).im)
    (hdom : ∀ z, MeasurableSet {ω | z ∈ (c ω).dom})
    (hlift : ∀ z, Measurable
      ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    {K : Ω → Set ℂ} (hm : IsDyadicHitMeasurable K) (hc : ∀ ω, IsCompact (K ω))
    (hp : ∀ ω, IsPreconnected (K ω ∪ lowerHalf))
    (hK : ∀ ω, fillH (K ω) = stripTargetHull ((c ω).dom : Set ℂ))
    (hscale : ∀ ω, ∃ a x : ℝ, 0 < a ∧ EqOn (c ω).1
      (fun z => (a : ℂ) * (ConformalImage.mapOut (fillH (K ω)) (stripRightRetarget z) - x))
      (c ω).dom)
    {e : ℕ → ℂ} {N : Ω → ℕ} (hN : Measurable N)
    (hNC : ∀ ω, e (N ω) ∈ (c ω).dom) :
    ∃ n : Ω → ℤ, Measurable n ∧
      (∀ ω z, z ∈ (c ω).dom → (shiftLift (c ω) (n ω)).2.2 z =
        (physicalRestartLog (fillH (K ω)) z).im) ∧
      (∀ z, Measurable ({ω | z ∈ (shiftLift (c ω) (n ω)).dom}.indicator
        fun ω => (shiftLift (c ω) (n ω)).2.2 z)) ∧
      (∀ ω, ContinuousOn (shiftLift (c ω) (n ω)).2.2 (c ω).dom) := by
  choose a x ha hscale using hscale
  have hB := fun ω => isHPHull_fillH_of_compact (hc ω) (hp ω)
  have hmaps : ∀ ω, MapsTo stripRightRetarget (c ω).dom (H \ fillH (K ω)) := by
    intro ω z hz
    rw [hK ω, H_diff_stripTargetHull (hDH ω)]
    exact ⟨z, hz, rfl⟩
  have hbase := fun ω => isDerivLog_physicalRestartLog (c ω).dom.isOpen
    (hB ω) (hDH ω) (hmaps ω)
  have hL : ∀ ω, IsDerivLog (c ω).1
      (fun z => (Real.log (a ω) : ℂ) + physicalRestartLog (fillH (K ω)) z) (c ω).dom := by
    intro ω
    exact isDerivLog_pos_scale_sub (c ω).dom.isOpen
      ((ConformalImage.isMapOut_mapOut (hB ω)).1.1.comp
        (isConformalBijection_stripRightRetarget.1.mono (hDH ω)) (hmaps ω))
      (hbase ω) (ha ω) (hscale ω)
  have hLm := Complex.measurable_im.comp
    (measurable_physicalRestartLog_anchor hm hc hp hN (fun ω => hmaps ω (hNC ω)))
  obtain ⟨n, hnm, hneq, hnmf, hnc⟩ := exists_measurable_inherited_shift
    (fun ω => (c ω).dom.isOpen) hDc hlog hL hdom hlift hN hNC
    (by simpa only [Function.comp_def, add_im, ofReal_im, zero_add] using hLm)
  exact ⟨n, hnm, fun ω z hz => by
    simpa only [add_im, ofReal_im, zero_add] using hneq ω z hz, hnmf, hnc⟩

end InteractingSLE.Sec5.Aux61Restart
