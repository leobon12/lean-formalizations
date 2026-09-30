import QuantumZipper.Proofs.GFF.CoordRegCompFixed

/-!
# RC3 for general measures, convergence form

`CoordReg.ae_evalReg_coordChange_revMap_gen` states RC3 as an equality `evalReg = raw value`. For
the constant invariance of the transfer integrand of E1-TR (`handoff/E1-TR.md`, M3) we need the
underlying facts in the form they are proved: almost surely the pulled-back field
`y = coordChange (ofFun (a log‖·‖ + g₁) + X) (revMap W T) Q` is a regular sample, every
`avgReg y k` is `ν`-integrable, and `∫ avgReg y k dν` converges
(`ae_regShift_coordChange_revMap_gen`). The proof is that of
`CoordReg.ae_evalReg_coordChange_revMap_gen` (unchanged up to the last step), which follows
Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), Prop. 3.1
and its proof (p. 18).

`CoordRegComp.ae_regShift_comp_fixed` / `_fc` / `_compact`: the same at the pushed measures of the
composition law for fixed drivers (the proofs of `CoordRegComp.ae_evalReg_comp_fixed` / `_fc` /
`_compact`, with the convergence form in the last step).
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal Real ComplexConjugate Topology

namespace QuantumZipper
namespace CoordReg

open CircleFubini FrostmanReg SmoothConv RegSample ProbabilityTheory

variable {W : ℝ → ℝ} {T : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Ω → FieldSample}

/-- **RC3 for general measures, convergence form.** -/
theorem ae_regShift_coordChange_revMap_gen (hW : Continuous W) (hT : 0 ≤ T) (hX : IsFreeGFFModConstH X P)
    [IsProbabilityMeasure P] (a : ℝ) {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ)
    {ν : Measure ℂ} [IsProbabilityMeasure ν] {R α C c γ α' C' : ℝ}
    (hsupp : ν (closedBall 0 R ∩ Hbar)ᶜ = 0) (hνH : ∀ᵐ z ∂ν, z ∈ H) (hF : IsFrostman ν α C)
    (hα : 0 < α) (hlν : Integrable (fun z : ℂ => |Real.log z.im|) ν) (hS : StripBound ν c γ)
    (hγ : 0 < γ) (hFf : IsFrostman (ν.map (revMap W T)) α' C') (hα' : 0 < α') :
    ∀ᵐ ω ∂P, IsRegularSample (coordChange (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω)
        (revMap W T) Q) ∧
      (∀ k : ℕ, Integrable (fun z => avgReg (coordChange
        (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) (revMap W T) Q) k z) ν) ∧
      ∃ L, Tendsto (fun k => ∫ z, avgReg (coordChange
        (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) (revMap W T) Q) k z ∂ν) atTop (𝓝 L) := by
  have hf := TwoPoint.measurable_revMap hW hT
  set R₁ := max R 0 with hR₁
  have hsupp1 : ν (ballH R₁)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 (inter_subset_inter_left _
      (closedBall_subset_closedBall (le_max_left _ _)))) hsupp
  have hsuppR₁ : ν (closedBall 0 R₁ ∩ Hbar)ᶜ = 0 := hsupp1
  have hν : ∀ᵐ z ∂ν, z ∈ H ∧ ‖z‖ ≤ R₁ := by
    filter_upwards [ae_mem_of_compl_null_frostman hsupp1, hνH] with z h1 h2
    exact ⟨h2, by simpa using h1.1⟩
  -- support of the pushforward
  obtain ⟨Bf, hBf⟩ := norm_revMap_le' hW hT R₁
  have hsuppf : (ν.map (revMap W T)) (closedBall 0 Bf ∩ Hbar)ᶜ = 0 := by
    have hae : ∀ᵐ z ∂ν, revMap W T z ∈ closedBall 0 Bf ∩ Hbar :=
      hν.mono fun z hz => ⟨by rw [mem_closedBall, dist_zero_right]; exact hBf z hz.1 hz.2,
        (TwoPoint.im_revMap_pos hW hz.1 hT).le⟩
    rw [Measure.map_apply hf (isClosed_closedBall.inter isClosed_Hbar).measurableSet.compl,
      show revMap W T ⁻¹' (closedBall 0 Bf ∩ Hbar)ᶜ =
        {z : ℂ | revMap W T z ∈ closedBall 0 Bf ∩ Hbar}ᶜ from rfl]
    exact mem_ae_iff.1 hae
  -- the random ingredients
  obtain ⟨Vh, hVc, hVV, hreg⟩ := exists_regular_witness_revMap hW hT hX
    (by norm_num : (0 : ℝ) < 1 / 12) (energyModulus_holds hW hT) a hg₁ Q
  have hfub : ∀ᵐ ω ∂P, ∀ k : ℕ, ∫ u, Vh (pr u (radius k) 0) ω ∂ν =
      X ω (ν.bind (pK hW hT (radius k))) :=
    ae_all_iff.2 fun k => ae_integral_Vhat_eq_gen hW hT hX hVc hVV (le_max_right _ _) hsupp1
      (radius_pos k)
  have hconv := ae_tendsto_push_bind hW hT hX hsuppR₁ hνH hF hα hlν hS hγ hsuppf hFf hα'
  -- the deterministic part
  have hL1 := logBounded_log_norm_revMap hW hT
  have hL2 := logBounded_comp_revMap hW hT hg₁
  have hL3 := logBounded_log_norm_deriv_revMap hW hT
  set Ψ : ℂ → ℝ := fun w => a * Real.log ‖revMap W T w‖ + g₁ (revMap W T w) +
    Q * Real.log ‖deriv (revMap W T) w‖ with hΨ
  have hDΨ : ∀ w (r : ℝ), 0 < r → Dfun W T a g₁ Q (w, r) = ∫ u, Ψ u ∂foldedCircle w r := by
    intro w r hr
    have j : Integrable (fun u => a * Real.log ‖revMap W T u‖ + g₁ (revMap W T u))
        (foldedCircle w r) := ((hL1.integrable w hr).const_mul a).add (hL2.integrable w hr)
    unfold Dfun
    rw [hΨ, integral_add j ((hL3.integrable w hr).const_mul Q),
      integral_add ((hL1.integrable w hr).const_mul a) (hL2.integrable w hr),
      integral_const_mul, integral_const_mul]
  obtain ⟨A1, hA1, hb1⟩ := hL1.2.2 (R₁ + 1)
  obtain ⟨A2, hA2, hb2⟩ := hL2.2.2 (R₁ + 1)
  obtain ⟨A3, hA3, hb3⟩ := hL3.2.2 (R₁ + 1)
  have hΨb : ∀ u ∈ H, ‖u‖ ≤ R₁ + 1 →
      |Ψ u| ≤ (|a| * A1 + A2 + |Q| * A3) + (|a| + 1 + |Q|) * |Real.log u.im| := by
    intro u hu huR
    have e1 := mul_le_mul_of_nonneg_left (hb1 u hu huR) (abs_nonneg a)
    have e2 := hb2 u hu huR
    have e3 := mul_le_mul_of_nonneg_left (hb3 u hu huR) (abs_nonneg Q)
    have t1 := abs_add_le (a * Real.log ‖revMap W T u‖ + g₁ (revMap W T u))
      (Q * Real.log ‖deriv (revMap W T) u‖)
    have t2 := abs_add_le (a * Real.log ‖revMap W T u‖) (g₁ (revMap W T u))
    rw [abs_mul] at t1 t2
    simp only [hΨ]
    linarith
  have hΨm : Measurable Ψ := ((hL1.1.const_mul a).add hL2.1).add (hL3.1.const_mul Q)
  have hΨc : ContinuousOn Ψ H :=
    ((continuousOn_const.mul hL1.2.1).add hL2.2.1).add (continuousOn_const.mul hL3.2.1)
  have hdet := tendsto_integral_bind_fc hΨm hΨc (by positivity) hΨb hν hlν
  have hrad1 : ∀ k, radius k ≤ 1 := fun k => by
    unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hDint : ∀ k : ℕ, Integrable (fun w => ∫ u, Ψ u ∂foldedCircle w (radius k)) ν := fun k =>
    integrable_integral_fc_of_bound hΨm hΨb hν hlν (radius_pos k) (hrad1 k)
  -- assembly
  filter_upwards [hreg, hfub, hconv] with ω hω h1 h2
  set y := coordChange (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) (revMap W T) Q with hy
  have hae : ∀ k : ℕ, (fun z => avgReg y k z) =ᵐ[ν]
      fun z => Vh (pr z (radius k) 0) ω + ∫ u, Ψ u ∂foldedCircle z (radius k) := by
    intro k
    filter_upwards [hν] with z hz
    rw [hω.avgReg_eq k (show (0 : ℝ) ≤ z.im from le_of_lt hz.1), hDΨ z _ (radius_pos k)]
  have hVi : ∀ k : ℕ, Integrable (fun z => Vh (pr z (radius k) 0) ω) ν := fun k =>
    integrable_of_continuous_ballH (g := fun z => Vh (pr z (radius k) 0) ω)
      ((hVc ω).comp (continuous_pr_fst (radius k) 0)) hsupp1
  have hk : ∀ k : ℕ, ∫ z, avgReg y k z ∂ν =
      X ω (ν.bind (pK hW hT (radius k))) + ∫ w, (∫ u, Ψ u ∂foldedCircle w (radius k)) ∂ν := by
    intro k
    rw [integral_congr_ae (hae k),
      integral_add (f := fun z => Vh (pr z (radius k) 0) ω)
        (g := fun z => ∫ u, Ψ u ∂foldedCircle z (radius k)) (hVi k) (hDint k), h1 k]
  have hlim : Tendsto (fun k => ∫ z, avgReg y k z ∂ν) atTop
      (𝓝 (X ω (ν.map (revMap W T)) + ∫ w, Ψ w ∂ν)) := by
    rw [show (fun k => ∫ z, avgReg y k z ∂ν) = fun k => X ω (ν.bind (pK hW hT (radius k))) +
      ∫ w, (∫ u, Ψ u ∂foldedCircle w (radius k)) ∂ν from funext hk]
    exact h2.add hdet
  exact ⟨⟨_, hω⟩, fun k => ((hVi k).add (hDint k)).congr (hae k).symm, _, hlim⟩

end CoordReg

namespace CoordRegComp
open CoordReg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **RC3 composition law, fixed drivers.** -/
theorem ae_regShift_comp_fixed (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P] (a : ℝ)
    {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ) {Vf V A : ℝ → ℝ} (hVf : Continuous Vf)
    (hV : Continuous V) (hA : Continuous A) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hVV : EqOn Vf V (Icc 0 t)) (hAV : ∀ r ∈ Icc (0 : ℝ) s, Vf (t + r) - Vf t = A r)
    {μ : Measure ℂ} [IsProbabilityMeasure μ] {R c γ α C α' C' : ℝ}
    (hμR : ∀ᵐ z ∂μ, z ∈ H ∧ ‖z‖ ≤ R) (hl : Integrable (fun z : ℂ => |Real.log z.im|) μ)
    (hS : StripBound μ c γ) (hγ : 0 < γ) (hF : IsFrostman (μ.map (revMap V t)) α C)
    (hα : 0 < α) (hF' : IsFrostman (μ.map (revMap Vf (t + s))) α' C') (hα' : 0 < α') :
    ∀ᵐ ω ∂P, IsRegularSample (coordChange (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω)
        (revMap A s) Q) ∧
      (∀ k : ℕ, Integrable (fun z => avgReg (coordChange
        (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) (revMap A s) Q) k z) (μ.map (revMap V t))) ∧
      ∃ L, Tendsto (fun k => ∫ z, avgReg (coordChange
        (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) (revMap A s) Q) k z ∂(μ.map (revMap V t))) atTop
        (𝓝 L) := by
  have hFm := TwoPoint.measurable_revMap hV ht
  have hAm := TwoPoint.measurable_revMap hA hs
  obtain ⟨Bf, hBf⟩ := norm_revMap_le' hV ht R
  have hνH : ∀ᵐ z ∂(μ.map (revMap V t)), z ∈ H :=
    (ae_map_iff hFm.aemeasurable isOpen_H.measurableSet).2
      (hμR.mono fun z hz => TwoPoint.im_revMap_pos hV hz.1 ht)
  have hsupp : (μ.map (revMap V t)) (closedBall 0 Bf ∩ Hbar)ᶜ = 0 := by
    have hae : ∀ᵐ z ∂μ, revMap V t z ∈ closedBall 0 Bf ∩ Hbar :=
      hμR.mono fun z hz => ⟨by rw [mem_closedBall, dist_zero_right]; exact hBf z hz.1 hz.2,
        (TwoPoint.im_revMap_pos hV hz.1 ht).le⟩
    rw [Measure.map_apply hFm (isClosed_closedBall.inter isClosed_Hbar).measurableSet.compl,
      show revMap V t ⁻¹' (closedBall 0 Bf ∩ Hbar)ᶜ =
        {z : ℂ | revMap V t z ∈ closedBall 0 Bf ∩ Hbar}ᶜ from rfl]
    exact mem_ae_iff.1 hae
  have hup : ∀ᵐ z ∂μ, z ∈ H ∧ z.im ≤ (revMap V t z).im ∧ (revMap V t z).im ≤ Bf :=
    hμR.mono fun z hz => ⟨hz.1, im_le_im_revMap V hV z hz.1 ht,
      (Complex.im_le_norm _).trans (hBf z hz.1 hz.2)⟩
  have hlν := integrable_abs_log_im_map hFm hup hl
  have hSν := stripBound_map hFm (hup.mono fun z hz => ⟨hz.1, hz.2.1⟩) hl hS
  have hmap : (μ.map (revMap V t)).map (revMap A s) = μ.map (revMap Vf (t + s)) := by
    rw [Measure.map_map hAm hFm]
    exact Measure.map_congr (hμR.mono fun z hz =>
      (TwoPoint.revMap_concat_eq hVf ht hs hVV hAV hz.1).symm)
  have hFf : IsFrostman ((μ.map (revMap V t)).map (revMap A s)) α' C' := by
    rw [hmap]; exact hF'
  exact CoordReg.ae_regShift_coordChange_revMap_gen hA hs hX a hg₁ Q hsupp hνH hF hα hlν hSν
    hγ hFf hα'

/-- **RC3 composition law at a folded circle** (arbitrary centre `w ∈ ℂ`, radius `r > 0`). -/
theorem ae_regShift_comp_fc (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P] (a : ℝ)
    {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ) {Vf V A : ℝ → ℝ} (hVf : Continuous Vf)
    (hV : Continuous V) (hA : Continuous A) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hVV : EqOn Vf V (Icc 0 t)) (hAV : ∀ r ∈ Icc (0 : ℝ) s, Vf (t + r) - Vf t = A r)
    (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, IsRegularSample (coordChange (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω)
        (revMap A s) Q) ∧
      (∀ k : ℕ, Integrable (fun z => avgReg (coordChange
        (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) (revMap A s) Q) k z) ((foldedCircle w r).map (revMap V t))) ∧
      ∃ L, Tendsto (fun k => ∫ z, avgReg (coordChange
        (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) (revMap A s) Q) k z ∂((foldedCircle w r).map (revMap V t))) atTop
        (𝓝 L) := by
  have hμR : ∀ᵐ z ∂foldedCircle w r, z ∈ H ∧ ‖z‖ ≤ ‖w‖ + r := by
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H w hr,
      TwoPoint.foldedCircle_ae_norm_le w hr.le] with z h1 h2 using ⟨h1, h2⟩
  have hF := TwoPoint.isFrostman_revMap_foldedCircle hV ht hr le_rfl (le_refl (‖w‖ + r))
  have hF' := TwoPoint.isFrostman_revMap_foldedCircle hVf (add_nonneg ht hs) hr le_rfl
    (le_refl (‖w‖ + r))
  exact ae_regShift_comp_fixed hX a hg₁ Q hVf hV hA ht hs hVV hAV hμR
    (TwoPoint.integrable_log_im_foldedCircle w hr).abs (stripBound_foldedCircle w hr)
    (by norm_num) (fun p ρ hρ => hF p ρ hρ) (by norm_num) (fun p ρ hρ => hF' p ρ hρ)
    (by norm_num)

/-- **RC3 composition law at a compactly supported Frostman probability measure.** -/
theorem ae_regShift_comp_compact (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P] (a : ℝ)
    {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ) {Vf V A : ℝ → ℝ} (hVf : Continuous Vf)
    (hV : Continuous V) (hA : Continuous A) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hVV : EqOn Vf V (Icc 0 t)) (hAV : ∀ r ∈ Icc (0 : ℝ) s, Vf (t + r) - Vf t = A r)
    {ϖ : Measure ℂ} [IsProbabilityMeasure ϖ] {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H)
    (hϖ : ϖ Kᶜ = 0) {α C : ℝ} (hFϖ : IsFrostman ϖ α C) (hα : 0 < α) :
    ∀ᵐ ω ∂P, IsRegularSample (coordChange (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω)
        (revMap A s) Q) ∧
      (∀ k : ℕ, Integrable (fun z => avgReg (coordChange
        (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) (revMap A s) Q) k z) (ϖ.map (revMap V t))) ∧
      ∃ L, Tendsto (fun k => ∫ z, avgReg (coordChange
        (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) (revMap A s) Q) k z ∂(ϖ.map (revMap V t))) atTop
        (𝓝 L) := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  have hμR : ∀ᵐ z ∂ϖ, z ∈ H ∧ ‖z‖ ≤ M := (ae_iff.2 hϖ).mono fun z hz =>
    ⟨hKH hz, by simpa using hM z hz⟩
  obtain ⟨c, hS, hl⟩ := stripBound_of_compact hK hKH hϖ
  have hF2 : TwoPoint.IsFrostman ϖ α C := fun p ρ hρ => hFϖ p ρ hρ
  obtain ⟨C₁, hF⟩ := B2.isFrostman_map_revMap_of_compact hV ht hK hKH hϖ hα.le hF2
  obtain ⟨C₂, hF'⟩ := B2.isFrostman_map_revMap_of_compact hVf (add_nonneg ht hs) hK hKH hϖ
    hα.le hF2
  exact ae_regShift_comp_fixed hX a hg₁ Q hVf hV hA ht hs hVV hAV hμR hl hS one_pos
    (fun p ρ hρ => hF p ρ hρ) hα (fun p ρ hρ => hF' p ρ hρ) hα

end CoordRegComp
end QuantumZipper
