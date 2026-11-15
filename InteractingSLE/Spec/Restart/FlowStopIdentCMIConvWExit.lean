/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvWClock
import InteractingSLE.Foundations.Brownian.Exit

/-! # A measurable version of the raw exit exists on the original sample space -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
namespace CMIVSetting
variable {S : Type u} [MeasurableSpace S] (D : CMIVSetting S)

/-- Reconstruct and regularize the closed available trace. The extension after
its lifetime is constant, and the ambient measurable space is unchanged. -/
theorem exists_continuous_measurable_trace :
    ∃ η : S → ℝ≥0 → ℂ, (∀ t, Measurable fun ω => η ω t) ∧ (∀ ω, Continuous (η ω)) ∧
      ∀ᵐ ω ∂D.Q₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ D.U ω → η ω t = D.Γ ω t := by
  classical
  let wk : S → ℝ≥0 → ℝ := fun ω t => if (t : ℝ≥0∞) < D.U ω then D.W₀ t ω else 0
  have hwk : Measurable wk := measurable_pi_iff.2 fun t =>
    Restart.measurable_ite_of_adaptedBefore D.coupling.1.2.1 t
  have hUm : Measurable D.U := FlowStopIdentLift.measurable_lifetime D.killed
  let η₀ : S → ℝ≥0 → ℂ := fun ω t => (D.y : ℂ) + (LP.drivingTrace (D.U ω, wk ω)).2 t
  have hm : ∀ t, Measurable fun ω => η₀ ω t := fun t => measurable_const.add
    ((measurable_pi_apply t).comp (measurable_snd.comp
      (LP.measurable_drivingTrace.comp (hUm.prodMk hwk))))
  have hgood : ∀ᵐ ω ∂D.Q₀, Continuous (η₀ ω) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ D.U ω → η₀ ω t = D.Γ ω t := by
    filter_upwards [D.trace, D.coupling.1.ae_isIntegratedSLEPath] with ω hg hp
    have hr := LP.drivingTrace_eq hg hp.isForcePath.continuousOn_w hp.isForcePath.w_zero
      (w' := wk ω) (fun s hs => ite_eq_left hs)
    have heq : ∀ t, η₀ ω t = D.Γ ω (min (t : ℝ≥0∞) (D.U ω)).toNNReal := by
      intro t
      change (D.y : ℂ) + (LP.drivingTrace (D.U ω, wk ω)).2 t = _
      rw [hr]
      dsimp only
      exact add_sub_cancel _ _
    refine ⟨?_, fun t ht => by rw [heq, min_eq_left ht, ENNReal.toNNReal_coe]⟩
    by_cases htop : D.U ω = ⊤
    · have he : η₀ ω = D.Γ ω := funext fun t => by
        rw [heq, htop, min_top_right, ENNReal.toNNReal_coe]
      rw [he]
      have hc := hg.2.1.add (continuousOn_const (c := (D.y : ℂ)))
      have hc' : ContinuousOn (D.Γ ω) Set.univ :=
        (hc.mono (fun t _ => by simp [htop])).congr (fun t _ => by
          change D.Γ ω t = D.Γ ω t - (D.y : ℂ) + D.y
          exact (sub_add_cancel _ _).symm)
      exact continuousOn_univ.1 hc'
    · let T : ℝ≥0 := (D.U ω).toNNReal
      have hT : (T : ℝ≥0∞) = D.U ω := ENNReal.coe_toNNReal htop
      have hc : ContinuousOn (D.Γ ω) (Iic T) := by
        have h := (hg.2.1.add (continuousOn_const (c := (D.y : ℂ)))).mono
          (fun t ht => hT ▸ ENNReal.coe_le_coe.2 ht)
        exact h.congr fun t _ => by
          change D.Γ ω t = D.Γ ω t - (D.y : ℂ) + D.y
          exact (sub_add_cancel _ _).symm
      have hf : η₀ ω = fun t => D.Γ ω (min t T) := funext fun t => by
        rw [heq, ← hT, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
      rw [hf]
      exact hc.comp_continuous (continuous_id.min continuous_const)
        (fun t => by change min t T ≤ T; exact min_le_right _ _)
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  let η : S → ℝ≥0 → ℂ := fun ω t => if ω ∈ N then D.y else η₀ ω t
  refine ⟨η, fun t => Measurable.ite hNm measurable_const (hm t), fun ω => ?_, ?_⟩
  · by_cases hω : ω ∈ N
    · simpa only [η, hω, ↓reduceIte] using (continuous_const : Continuous fun _ : ℝ≥0 => (D.y : ℂ))
    · have hg : Continuous (η₀ ω) ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ D.U ω → η₀ ω t = D.Γ ω t :=
        not_not.1 (fun h => hω (hNsub h))
      simpa only [η, hω, ↓reduceIte] using hg.1
  · have hnae : ∀ᵐ ω ∂D.Q₀, ω ∉ N := ae_iff.2 (by
      convert hN0 using 1
      congr 1
      ext ω
      simp only [mem_ofPred_eq, not_not])
    filter_upwards [hgood, hnae] with ω hg hn t ht
    simpa only [η, hn, ↓reduceIte] using hg.2 t ht

/-- R66's measurable exit version exists without a clock hypothesis.
Its stopping-time and predictability properties require the separate history argument. -/
theorem exists_measurable_exit :
    ∃ e : S → ℝ≥0∞, Measurable e ∧
      e =ᵐ[D.Q₀] fun ω => RLC.exitTime D.V (D.Γ ω) (D.U ω) := by
  obtain ⟨η, hηm, hηc, hag⟩ := D.exists_continuous_measurable_trace
  refine ⟨fun ω => min (D.U ω) (InteractingSLE.exitTime D.V (η ω)),
    (FlowStopIdentLift.measurable_lifetime D.killed).min
      (InteractingSLE.measurable_exitTime hηm hηc D.V_open), ?_⟩
  filter_upwards [hag] with ω hω
  change RLC.exitTime D.V (η ω) (D.U ω) = RLC.exitTime D.V (D.Γ ω) (D.U ω)
  have huniv : ∀ γ : ℝ≥0 → ℂ, RLC.exitTime Set.univ γ (D.U ω) = D.U ω := fun γ => by
    change min (D.U ω) (InteractingSLE.exitTime Set.univ γ) = D.U ω
    rw [InteractingSLE.exitTime_univ, min_top_right]
  exact (RLC.StoppedAgree.mono (V := D.V) (V' := Set.univ) (subset_univ _)
    ⟨by rw [huniv, huniv], fun t ht => hω t (by rwa [huniv] at ht)⟩).1

end CMIVSetting
end InteractingSLE.Restart.FlowStopIdentCMI
