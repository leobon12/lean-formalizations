import QuantumZipper.Proofs.Thm18.G3CvReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3-CURVE, piece 1f: the outside of the pulled-back field is orthogonal to its local part

For a balanced pair `α, α'` of admissible measures carried away from `Φ(closedBall b ρ)` and from
its reflection, the free vector difference `v̂_α − v̂_α'` is orthogonal to every pulled-back local
generator `pullLocVec ν` (`inner_fvM_sub_pullLocVec_eq_zero`): `w ↦ neumannH y (Φ w)` is harmonic
near `closedBall b ρ` and even across `ℝ`, hence reproduced by the balayage. Consequently the
increments of the field `W` outside `Φ(B(b, ρ))` are coordinates of the variables `Ξ` of
`exists_pullCoupling` (vectors `(u, 0)`, `u ⊥` the pulled-back local part), i.e. independent of
the coupled free field `X'` (the domain Markov property of `W ∘ Φ`; Sheffield (2007) Thm. 2.17).
Own adaptation of `inner_freeVec_sub_freeLocVec_eq_zero` (MixedM7Local.lean).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set InnerProductSpace
open scoped ComplexConjugate ENNReal Topology RealInnerProductSpace

namespace QuantumZipper
namespace G3Cv

open K3 GFFExist

variable {Φ : ℂ → ℂ} {b r₀ ρ r₁ m M : ℝ}

/-- `w ↦ neumannH y (Φ w)` is harmonic at points `w` of the disc where `Φ w ≠ y, ȳ`. -/
theorem harmonicAt_neumannH_comp (hΦ : LocConf Φ b r₀) {y w : ℂ} (hw : w ∈ ball (b : ℂ) r₀)
    (h1 : Φ w ≠ y) (h2 : Φ w ≠ conj y) : HarmonicAt (fun v => neumannH y (Φ v)) w := by
  have hA : AnalyticAt ℂ Φ w := hΦ.diff.analyticAt (isOpen_ball.mem_nhds hw)
  have e1 := (hA.sub (analyticAt_const (v := y))).harmonicAt_log_norm (sub_ne_zero.2 h1)
  have e2 := (hA.sub (analyticAt_const (v := conj y))).harmonicAt_log_norm
    (sub_ne_zero.2 h2)
  convert e1.neg.add e2.neg using 1
  funext v
  simp only [neumannH, Pi.add_apply, Pi.neg_apply, Pi.sub_apply]
  rw [norm_sub_rev y, norm_sub_conj_comm]
  ring

/-- Reproduction of `w ↦ neumannH y (Φ w)` by the balayage. -/
theorem integral_neumannH_comp_bal (hD : PullData Φ b r₀ ρ r₁ m M) {y : ℂ}
    (hy : ∀ w ∈ closedBall (b : ℂ) ρ, Φ w ≠ y ∧ Φ w ≠ conj y) (ν : LocIdx b r₁) :
    ∫ w, neumannH y (Φ w) ∂(bal b ρ ν.1) = ∫ w, neumannH y (Φ w) ∂ν.1 := by
  have := ν.2.1.1
  have := isFiniteMeasure_bal hD.hρ hD.hr₁ ν.2.2
  have hsub : closedBall (b : ℂ) ρ ⊆ ball (b : ℂ) r₀ := closedBall_subset_ball hD.hρr
  have hH : HarmonicOnNhd (fun v => neumannH y (Φ v)) (closedBall (b : ℂ) ρ) := fun w hw =>
    harmonicAt_neumannH_comp hD.conf (hsub hw) (hy w hw).1 (hy w hw).2
  have hcont : ContinuousOn (fun v => neumannH y (Φ v)) (closedBall (b : ℂ) ρ) := fun w hw =>
    (hH w hw).1.continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall (b : ℂ) ρ).exists_bound_of_continuousOn hcont
  have hmeas : Measurable fun v => neumannH y (Φ v) :=
    measurable_neumannH.comp (measurable_const.prodMk hD.conf.meas)
  have hint : Integrable (fun v => neumannH y (Φ v)) (bal b ρ ν.1) :=
    Integrable.of_bound hmeas.aestronglyMeasurable C
      ((ae_mem_of_compl_null_g3cv (bal_closedBall_compl_g3cv hD.hρ ν.1)).mono fun w hw => hC w hw)
  rw [(integral_bal hint).2]
  refine integral_congr_ae ?_
  filter_upwards [ae_mem_of_compl_null_g3cv ν.2.2] with w' hw'
  have hw'b : w' ∈ ball (b : ℂ) ρ := mem_ball_of_le_k3 hD.hr₁ (mem_closedBall_iff_norm.1 hw')
  exact integral_halfDiscPoisson_of_harmonic hD.hρ hw'b hH fun x hx => by
    have hxB : x ∈ ball (b : ℂ) r₀ := hsub (sphere_subset_closedBall hx)
    simp only [hD.conf.symm x hxB, neumannH_conj_right_g3cv]

/-- **Outside increments are orthogonal to the pulled-back local part.** -/
theorem inner_fvM_sub_pullLocVec_eq_zero (hD : PullData Φ b r₀ ρ r₁ m M) {α α' : Measure ℂ}
    (hα : IsAdmissibleH α) (hα' : IsAdmissibleH α') (hm : α Set.univ = α' Set.univ)
    (hαy : ∀ᵐ y ∂α, ∀ w ∈ closedBall (b : ℂ) ρ, Φ w ≠ y ∧ Φ w ≠ conj y)
    (hα'y : ∀ᵐ y ∂α', ∀ w ∈ closedBall (b : ℂ) ρ, Φ w ≠ y ∧ Φ w ≠ conj y)
    (ν : LocIdx b r₁) :
    ⟪fvM α - fvM α', pullLocVec Φ b ρ ν.1⟫ = 0 := by
  obtain ⟨a1, a2, e1⟩ := hD.local_adm ν
  have := ν.2.1.1
  have := isFiniteMeasure_bal hD.hρ hD.hr₁ ν.2.2
  simp only [pullLocVec, fvM_eq hα, fvM_eq hα', fvM_eq a1, fvM_eq a2]
  rw [freeVec_inner ⟨α, hα⟩ ⟨α', hα'⟩ ⟨_, a1⟩ ⟨_, a2⟩ hm e1]
  have hmap : ∀ (β : Measure ℂ) (y : ℂ),
      ∫ v, neumannH y v ∂(β.map Φ) = ∫ w, neumannH y (Φ w) ∂β := fun β y =>
    integral_map hD.conf.meas.aemeasurable
      ((measurable_neumannH.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  have hkey : ∀ γ : Measure ℂ, (∀ᵐ y ∂γ, ∀ w ∈ closedBall (b : ℂ) ρ, Φ w ≠ y ∧ Φ w ≠ conj y) →
      kernelCov neumannH γ (ν.1.map Φ) = kernelCov neumannH γ ((bal b ρ ν.1).map Φ) := by
    intro γ hγ
    unfold kernelCov
    refine integral_congr_ae ?_
    filter_upwards [hγ] with y hy
    rw [hmap, hmap, integral_neumannH_comp_bal hD hy ν]
  simp only [kernelCov2]
  rw [hkey α hαy, hkey α' hα'y]
  ring

/-- **Pushed-forward arc measures are orthogonal to the pulled-back local part**: for admissible
`γ, γ'` of equal mass, carried by `closedBall b ρ` and giving no mass to `ball b ρ` (e.g. the
half-disc Poisson measures `P_z`), `⟪v̂_{Φ_*γ} − v̂_{Φ_*γ'}, pullLocVec ν⟫ = 0` (the Neumann part is
the free arc case `inner_freeVec_sub_freeLocVec_eq_zero`, the correction `kPull` is reproduced by
the balayage). -/
theorem inner_fvM_map_sub_pullLocVec_eq_zero (hD : PullData Φ b r₀ ρ r₁ m M) {γ γ' : Measure ℂ}
    (hγ : IsAdmissibleH γ) (hγ' : IsAdmissibleH γ') (hm : γ Set.univ = γ' Set.univ)
    (hγc : γ (closedBall (b : ℂ) ρ)ᶜ = 0) (hγ'c : γ' (closedBall (b : ℂ) ρ)ᶜ = 0)
    (hγB : γ (ball (b : ℂ) ρ) = 0) (hγ'B : γ' (ball (b : ℂ) ρ) = 0) (ν : LocIdx b r₁) :
    ⟪fvM (γ.map Φ) - fvM (γ'.map Φ), pullLocVec Φ b ρ ν.1⟫ = 0 := by
  obtain ⟨a1, a2, e1⟩ := hD.local_adm ν
  have := ν.2.1.1
  have := hγ.1
  have := hγ'.1
  have := isFiniteMeasure_bal hD.hρ hD.hr₁ ν.2.2
  have g1 := hD.adm_map hγ hγc
  have g2 := hD.adm_map hγ' hγ'c
  have hmass : (γ.map Φ) Set.univ = (γ'.map Φ) Set.univ := by
    rw [Measure.map_apply hD.conf.meas MeasurableSet.univ,
      Measure.map_apply hD.conf.meas MeasurableSet.univ, preimage_univ, hm]
  have hνρ : ν.1 (closedBall (b : ℂ) ρ)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 (closedBall_subset_closedBall hD.hr₁.le)) ν.2.2
  have hbA := isAdmissibleH_bal hD.hρ hD.hr₁ ν.2.2
  have hbc := bal_closedBall_compl_g3cv (b := b) hD.hρ ν.1
  simp only [pullLocVec, fvM_eq g1, fvM_eq g2, fvM_eq a1, fvM_eq a2]
  rw [freeVec_inner ⟨_, g1⟩ ⟨_, g2⟩ ⟨_, a1⟩ ⟨_, a2⟩ hmass e1]
  simp only [kernelCov2]
  rw [kernelCov_map_g3cv hD.conf, kernelCov_map_g3cv hD.conf, kernelCov_map_g3cv hD.conf,
    kernelCov_map_g3cv hD.conf,
    kernelCov_pull_split hD.conf hD.hρr hD.bl hγ ν.2.1 hγc hνρ,
    kernelCov_pull_split hD.conf hD.hρr hD.bl hγ hbA hγc hbc,
    kernelCov_pull_split hD.conf hD.hρr hD.bl hγ' ν.2.1 hγ'c hνρ,
    kernelCov_pull_split hD.conf hD.hρr hD.bl hγ' hbA hγ'c hbc]
  have hN := inner_freeVec_sub_freeLocVec_eq_zero hD.hρ hD.hr₁ hγ hγ' hm hγB hγ'B ν
  simp only [freeLocVec] at hN
  rw [freeVec_inner ⟨γ, hγ⟩ ⟨γ', hγ'⟩ ⟨ν.1, ν.2.1⟩ ⟨_, ν.bal_adm hD.hρ hD.hr₁⟩ hm
    (bal_univ hD.hρ hD.hr₁ ν.2.2).symm] at hN
  simp only [kernelCov2] at hN
  have hk : ∀ α : Measure ℂ, α (closedBall (b : ℂ) ρ)ᶜ = 0 →
      kernelCov (kPull Φ) α (bal b ρ ν.1) = kernelCov (kPull Φ) α ν.1 := fun α hα =>
    integral_congr_ae ((ae_mem_of_compl_null_g3cv hα).mono fun x hx =>
      integral_kPull_bal hD.conf hD.hρ hD.hρr hD.bl hD.hr₁ ν.2.2
        (measure_singleton_of_admissible ν.2.1) hx)
  rw [hk γ hγc, hk γ' hγ'c]
  linarith

end G3Cv
end QuantumZipper
