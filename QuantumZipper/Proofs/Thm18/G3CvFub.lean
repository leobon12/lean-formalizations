import QuantumZipper.Proofs.Thm18.G3CvMom

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3-CURVE, piece 1h: stochastic Fubini for the pulled-back harmonic part

For a free field `W` and a local measure `μ` carried by `closedBall b r₂` (`r₂ < ρ`), the
continuous version `Y = kolY (pullIncr W Φ b ρ r₂)` of `z ↦ W(Φ_*P_z) − W(Φ_*P_b)` satisfies a.s.
`∫ Y dμ = W(Φ_*bal μ) − W(μ(ℂ) • Φ_*P_b)` (`pull_stochFubini`, from `stochFubini_kernel` with the
kernel `z ↦ Φ_*P_z`, whose potentials are bounded uniformly through the bi-Lipschitz bound).
Together with `exists_pullCoupling` this writes, near `b`, the pulled-back field as
`W(Φ_*μ) = X'(μ) − X'(bal μ) + ∫ Y dμ + μ(ℂ) W(Φ_*P_b)`. Own adaptation of
`markov_decomposition` (HalfDiscMarkov.lean).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set
open scoped ComplexConjugate ENNReal Topology

namespace QuantumZipper
namespace G3Cv

open K3

variable {Φ : ℂ → ℂ} {b r₀ ρ r₁ m M : ℝ}

/-- Uniform potential bound for pushforwards. -/
theorem lintegral_logPot_map_le (hΦ : LocConf Φ b r₀) (hρr : ρ < r₀) (hbl : BiLip Φ b ρ m M)
    {α : Measure ℂ} [IsFiniteMeasure α] (hαc : α (closedBall (b : ℂ) ρ)ᶜ = 0)
    (hαa : ∀ p, α {p} = 0) {C : ℝ≥0∞}
    (hC : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂α ≤ C) (y : ℂ) :
    ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂(α.map Φ) ≤
      C + ENNReal.ofReal (-Real.log (m / 2)) * α Set.univ := by
  obtain ⟨hm, -, hb⟩ := hbl
  set K := closedBall (b : ℂ) ρ with hK
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hΦc : ContinuousOn Φ K := (hΦ.diff.mono (closedBall_subset_ball hρr)).continuousOn
  rw [lintegral_map (admissible_measurable_logNeg_sub y) hΦ.meas]
  by_cases hKne : ρ < 0
  · have : α Set.univ = 0 := by
      have hK0 : K = ∅ := closedBall_eq_empty.2 hKne
      rw [hK0, compl_empty] at hαc; exact hαc
    rw [Measure.measure_univ_eq_zero.1 this, lintegral_zero_measure]; exact zero_le
  push Not at hKne
  obtain ⟨x₀, hx₀, hmin⟩ := hKc.exists_isMinOn (nonempty_closedBall.2 hKne)
    ((hΦc.sub continuousOn_const).norm (f := fun x => Φ x - y))
  have hne : ∀ᵐ x ∂α, x ≠ x₀ := by
    rw [ae_iff]; simpa only [ne_eq, not_not, Set.ofPred_eq_eq_singleton] using hαa x₀
  have hpt : ∀ᵐ x ∂α, ENNReal.ofReal (-Real.log ‖Φ x - y‖) ≤
      ENNReal.ofReal (-Real.log ‖x - x₀‖) + ENNReal.ofReal (-Real.log (m / 2)) := by
    filter_upwards [hne, mem_ae_iff.2 hαc] with x hx hxK
    have h1 := (hb x hxK x₀ hx₀).1
    have h2 : ‖Φ x₀ - y‖ ≤ ‖Φ x - y‖ := hmin hxK
    have h3 : ‖Φ x - Φ x₀‖ ≤ ‖Φ x - y‖ + ‖Φ x₀ - y‖ := by
      have := norm_sub_le (Φ x - y) (Φ x₀ - y)
      rwa [sub_sub_sub_cancel_right] at this
    have hxx : 0 < ‖x - x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
    have ha : 0 < m / 2 * ‖x - x₀‖ := by positivity
    have hA : m / 2 * ‖x - x₀‖ ≤ ‖Φ x - y‖ := by linarith
    have hlog : -Real.log ‖Φ x - y‖ ≤ -Real.log ‖x - x₀‖ + -Real.log (m / 2) := by
      have := Real.log_le_log ha hA
      rw [Real.log_mul (by positivity) hxx.ne'] at this
      linarith
    exact (ENNReal.ofReal_le_ofReal hlog).trans ENNReal.ofReal_add_le
  calc ∫⁻ x, ENNReal.ofReal (-Real.log ‖Φ x - y‖) ∂α
      ≤ ∫⁻ x, (ENNReal.ofReal (-Real.log ‖x - x₀‖) + ENNReal.ofReal (-Real.log (m / 2))) ∂α :=
        lintegral_mono_ae hpt
    _ = ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - x₀‖) ∂α +
          ENNReal.ofReal (-Real.log (m / 2)) * α Set.univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ ≤ _ := by gcongr; exact hC x₀

/-- Pushforward commutes with `bind`. -/
theorem map_bind_g3cv {κ : ℂ → Measure ℂ} (hκ : Measurable κ) (hΦm : Measurable Φ)
    (ν : Measure ℂ) : (ν.bind κ).map Φ = ν.bind fun z => (κ z).map Φ := by
  have hm : Measurable fun z => (κ z).map Φ := fun s hs =>
    (Measure.measurable_map Φ hΦm).comp hκ hs
  ext A hA
  rw [Measure.map_apply hΦm hA, Measure.bind_apply (hΦm hA) hκ.aemeasurable,
    Measure.bind_apply hA hm.aemeasurable]
  refine lintegral_congr fun z => ?_
  rw [Measure.map_apply hΦm hA]

/-- **Stochastic Fubini for the pulled-back harmonic part.** -/
theorem pull_stochFubini {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : Ω → FieldSample} (hW : IsFreeGFFModConstH W P) (hD : PullData Φ b r₀ ρ r₁ m M)
    {r₂ : ℝ} (hr₂ : 0 < r₂) (hr₂ρ : r₂ < ρ) (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hμ : μ (closedBall (b : ℂ) r₂ ∩ Hbar)ᶜ = 0) {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, ContinuousOn (fun z => Y z ω) Hbar)
    (hY : ∀ z ∈ Hbar, Y z =ᵐ[P] pullIncr W Φ b ρ r₂ z) :
    (fun ω => ∫ z, Y z ω ∂μ) =ᵐ[P]
      fun ω => W ω ((bal b ρ μ).map Φ) - W ω ((μ Set.univ • halfDiscPoisson b ρ (b : ℂ)).map Φ) := by
  have hρ := hD.hρ
  set K := closedBall (b : ℂ) r₂ ∩ Hbar with hKdef
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hbK : (b : ℂ) ∈ K := ⟨mem_closedBall_self hr₂.le, by show (0 : ℝ) ≤ (b : ℂ).im; simp⟩
  have hKb : ∀ z ∈ K, ‖z - b‖ ≤ r₂ := fun z hz => mem_closedBall_iff_norm.1 hz.1
  set c : ℂ → Measure ℂ := fun z => (halfDiscPoisson b ρ z).map Φ with hc
  have hcm : Measurable c := (Measure.measurable_map Φ hD.conf.meas).comp
    (measurable_halfDiscPoisson b ρ)
  -- support
  obtain ⟨R₀, hR₀⟩ := (isCompact_closedBall (b : ℂ) ρ).exists_bound_of_continuousOn
    ((hD.conf.diff.mono (closedBall_subset_ball hD.hρr)).continuousOn)
  have hcS : ∀ z ∈ K, c z (CircleFubini.ballH R₀)ᶜ = 0 := by
    intro z _
    rw [hc, Measure.map_apply hD.conf.meas (CircleFubini.measurableSet_ballH R₀).compl]
    have h := ae_iff.1 (ae_halfDiscPoisson_mem (t := b) hρ z)
    refine measure_mono_null (fun x hx => ?_) h
    intro hx'
    exact hx ⟨mem_closedBall_zero_iff.2 (hR₀ x (sphere_subset_closedBall hx'.1)),
      hD.up x ⟨sphere_subset_closedBall hx'.1, hx'.2⟩⟩
  have hcU : ∀ z ∈ K, c z Set.univ = 1 := by
    intro z hz
    have := isProbabilityMeasure_halfDiscPoisson hρ (mem_ball_of_le_k3 hr₂ρ (hKb z hz))
    rw [hc, Measure.map_apply hD.conf.meas MeasurableSet.univ, preimage_univ, measure_univ]
  have hcP : ∀ z ∈ K, ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂c z ≤
      potC ρ r₂ + ENNReal.ofReal (-Real.log (m / 2)) * 1 := by
    intro z hz y
    have hP := isProbabilityMeasure_halfDiscPoisson hρ (mem_ball_of_le_k3 hr₂ρ (hKb z hz))
    have h := lintegral_logPot_map_le hD.conf hD.hρr hD.bl
      (halfDiscPoisson_closedBall_compl hρ z)
      (measure_singleton_of_admissible (isAdmissibleH_halfDiscPoisson hρ hr₂ρ (hKb z hz)))
      (fun y' => halfDiscPoisson_pot_le hρ hr₂ρ (hKb z hz) y') y
    rwa [measure_univ] at h
  have hCt : potC ρ r₂ + ENNReal.ofReal (-Real.log (m / 2)) * 1 ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨potC_ne_top ρ r₂, by simp⟩
  have hWm : ∀ z, Measurable (pullIncr W Φ b ρ r₂ z) := fun z =>
    (hW.measurable_coord _).sub (hW.measurable_coord _)
  have hWK : ∀ z ∈ K, pullIncr W Φ b ρ r₂ z = fun ω => W ω (c z) - W ω (c b) := by
    intro z hz
    funext ω
    simp only [pullIncr, hc, retr_eq_self hz.2 (hKb z hz)]
  have hF := stochFubini_kernel hW hcm hKc inter_subset_right hbK hCt hcU hcS hcP hYc hWm hY
    hWK μ hμ
  have e1 : μ.bind c = (bal b ρ μ).map Φ := by
    rw [bal, map_bind_g3cv (measurable_halfDiscPoisson b ρ) hD.conf.meas]
  have e2 : μ Set.univ • c b = (μ Set.univ • halfDiscPoisson b ρ (b : ℂ)).map Φ := by
    rw [hc, Measure.map_smul]
    exact hD.conf.meas.aemeasurable
  rw [e1, e2] at hF
  exact hF

end G3Cv
end QuantumZipper
