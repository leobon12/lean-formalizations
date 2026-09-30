import QuantumZipper.Proofs.Thm18.G1RCUnwind

/-!
# G1-RC, part 8: `G1RawSmoothStmt` from the profile facts; `G1RegRepRC2Stmt` from two inputs

With the unwinding of G1RCUnwind.lean, the raw value of the pulled-back canonical wedge field at
`fc(d, r)` is, for a good sample and whenever the free-field part converges to `L`,

  `L + profPart + Q log S + Q ∫ log |ψ'| dfc(d, r)`,

where `profPart` is the limit of the circle-smoothed wedge profile integrated against
`ν = ψ_* fc(d, r)` (`G1RC.raw_coordChange_rescale_wedge`). This reduces `G1RawSmoothStmt` to
`G1RC.G1ProfileStmt` (`G1RC.g1RawSmoothStmt_of_profile`), which collects the remaining
**deterministic-per-sample analytic facts** about the pushed circles `ν`: they are carried by `Hbar` and, for all large `k`, do not charge the circle
`{‖w‖ = 2^{-k}}` (a pushed analytic arc lies on at most one circle about `0`), the integrability of the two parts, convergence of
the profile part, continuity and smoothing symmetry of the resulting `D` (`S > 0` a.s. is from the repository:
`WedgeCan4.ae_wedge_canonical_spec_of_inputs`).

Main result: `G1RC.g1RegRepRC2Stmt_of_psi_profile : G1PsiExtStmt → G1ProfileStmt →
G1RegRepRC2Stmt` (and every-circle RC3, `G1RC.ae_rc3_of_psi_profile`).

The a.s. goodness of the free sample and the radial path is from the repository
(`IsRegVersion.ae_good`, `WedgeCan.ae_raw_dyadic`, `WedgeCan4.ae_continuous_wedgeProcess`,
`F1.wedgeCircleIntStmt_holds`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function Real
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open WedgeTK CircleFubini

/-- The profile part of the canonical wedge field at a measure `ν` (junk `0` without a limit). -/
def profPart (x : FieldSample) (A : ℝ → ℝ) (Q S : ℝ) (ν : Measure ℂ) : ℝ :=
  limUnder atTop fun k : ℕ => ∫ w, (∫ u, WedgeCan.wedgeProfile x A Q u
    ∂foldedCircle ((S : ℂ) * w) (S * radius k)) ∂ν

/-- The analytic hypotheses on a pushed circle `ν` used by the unwinding. -/
def ProfileGood (x : FieldSample) (F : ℂ × ℝ → ℝ) (A : ℝ → ℝ) (Q S : ℝ) (ν : Measure ℂ) :
    Prop :=
  (∀ᵐ w ∂ν, w ∈ Hbar) ∧ (∀ᶠ k : ℕ in atTop, ∀ᵐ w ∂ν, ‖w‖ ≠ radius k) ∧
  (∀ k : ℕ, Integrable (fun w => F ((S : ℂ) * w, S * radius k)) ν) ∧
  (∀ k : ℕ, Integrable (fun w => ∫ u, WedgeCan.wedgeProfile x A Q u
    ∂foldedCircle ((S : ℂ) * w) (S * radius k)) ν) ∧
  ∃ Lp : ℝ, Tendsto (fun k : ℕ => ∫ w, (∫ u, WedgeCan.wedgeProfile x A Q u
    ∂foldedCircle ((S : ℂ) * w) (S * radius k)) ∂ν) atTop (𝓝 Lp)

variable {x : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ}

/-- **Raw value of the pulled-back canonical wedge field**, given convergence of the free part. -/
theorem raw_coordChange_rescale_wedge (h : WedgeGood x F A) (Q : ℝ) {S : ℝ} (hS : 0 < S)
    {ψ ψe : ℂ → ℂ} (hψm : Measurable ψ) (heq : EqOn ψ ψe H) {d : ℂ} {r : ℝ} (hr : 0 < r)
    (hP : ProfileGood x F A Q S ((foldedCircle d r).map ψ)) {L : ℝ}
    (hL : Tendsto (fun k : ℕ => ∫ u, F (u, S * radius k)
      ∂((foldedCircle d r).map fun z => (S : ℂ) * ψe z)) atTop (𝓝 L)) :
    coordChange (rescale (wedgeField (lateralPart x) A Q) Q S) ψ Q (foldedCircle d r) =
      L + (profPart x A Q S ((foldedCircle d r).map ψ) + Q * Real.log S +
        Q * ∫ z, Real.log ‖deriv ψ z‖ ∂foldedCircle d r) := by
  obtain ⟨hν, hνk, hiF, hiP, Lp, hLp⟩ := hP
  set ν := (foldedCircle d r).map ψ with hνdef
  have : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hψm.aemeasurable).2 inferInstance
  have hmS : Measurable fun w : ℂ => (S : ℂ) * w := measurable_const_mul _
  have hmap : (foldedCircle d r).map (fun z => (S : ℂ) * ψe z) =
      ν.map (fun w => (S : ℂ) * w) := by
    rw [hνdef, Measure.map_map hmS hψm]
    refine Measure.map_congr ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hr] with z hz
    show (S : ℂ) * ψe z = (S : ℂ) * ψ z
    rw [heq hz]
  have hHb : ∀ᵐ u ∂(ν.map fun w => (S : ℂ) * w), u ∈ Hbar := by
    refine (ae_map_iff (p := fun u : ℂ => u ∈ Hbar) hmS.aemeasurable
      (by exact isClosed_Hbar.measurableSet)).2 ?_
    filter_upwards [hν] with w hw
    show 0 ≤ ((S : ℂ) * w).im
    rw [Complex.im_ofReal_mul]; exact mul_nonneg hS.le hw
  have hint : ∀ k : ℕ, ∫ u, F (u, S * radius k) ∂(ν.map fun w => (S : ℂ) * w) =
      ∫ w, F ((S : ℂ) * w, S * radius k) ∂ν := by
    intro k
    refine integral_map hmS.aemeasurable ?_
    have hc : ContinuousOn (fun u => F (u, S * radius k)) Hbar :=
      h.good.1.1.comp (continuous_id.prodMk continuous_const).continuousOn
        fun u hu => mk_mem_prod hu (show S * radius k ∈ Ioi 0 from mul_pos hS (radius_pos k))
    rw [← Measure.restrict_eq_self_of_ae_mem hHb]
    exact hc.aestronglyMeasurable isClosed_Hbar.measurableSet
  have hL' : Tendsto (fun k : ℕ => ∫ w, F ((S : ℂ) * w, S * radius k) ∂ν) atTop (𝓝 L) := by
    rw [hmap] at hL
    simpa only [hint] using hL
  have hev := evalReg_rescale_wedge h Q hS hν hνk hiF hiP hLp hL'
  have hpp : profPart x A Q S ν = Lp := hLp.limUnder_eq
  show evalReg _ ν + Q * _ = _
  rw [hev, hpp]
  ring

/-- The random `D` of the pulled-back canonical wedge field. -/
def dPart (γ : ℝ) {Ω' : Type} (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ) (ψ : ℂ → ℂ) (ω' : Ω')
    (p : ℂ × ℝ) : ℝ :=
  profPart (X ω') (fun t => A t ω') (Qc γ) (scaleParam γ (wedge0 γ X A ω'))
      ((foldedCircle p.1 p.2).map ψ) +
    Qc γ * Real.log (scaleParam γ (wedge0 γ X A ω')) +
    Qc γ * ∫ z, Real.log ‖deriv ψ z‖ ∂foldedCircle p.1 p.2

/-- **Profile input** (deterministic per sample; analytic facts about the pushed circles). -/
def G1ProfileStmt : Prop :=
  G1RepSetting fun γ _ _ P B Ω' _ P' X A => ∀ Ψ, G1PsiSel γ Ψ →
    ∀ᵐ a ∂(P.map (pathOf B)), ∀ left : Bool, ∀ G : Ω' → ℂ × ℝ → ℝ, IsRegVersion X P' G →
      ∀ᵐ ω' ∂P',
        (∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → ProfileGood (X ω') (G ω') (fun t => A t ω') (Qc γ)
          (scaleParam γ (wedge0 γ X A ω')) ((foldedCircle d r).map (Ψ left a))) ∧
        ContinuousOn (dPart γ X A (Ψ left a) ω') (Hbar ×ˢ Ioi 0) ∧
        ∀ w ∈ Hbar, ∀ r ρ : ℝ, 0 < r → 0 < ρ →
          ∫ u, dPart γ X A (Ψ left a) ω' (u, ρ) ∂foldedCircle w r =
            ∫ v, dPart γ X A (Ψ left a) ω' (v, r) ∂foldedCircle w ρ

/-- A.s. goodness of the free sample and the radial path. -/
theorem ae_wedgeGood {γ : ℝ} {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ} {G : Ω' → ℂ × ℝ → ℝ}
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P') (hG : IsRegVersion X P' G) :
    ∀ᵐ ω' ∂P', WedgeGood (X ω') (G ω') (fun t => A t ω') := by
  filter_upwards [hG.ae_good, WedgeCan.ae_raw_dyadic hG,
    WedgeCan4.ae_continuous_wedgeProcess hA,
    F1.wedgeCircleIntStmt_holds γ (γ - 2 / γ) P' X A hX hA hXA] with ω hg hray hAc hint
  exact ⟨hg, hray, hAc, fun w ρ hρ => (hint w ρ hρ).1, fun w ρ hρ => (hint w ρ hρ).2⟩

/-- A.s. positivity of the canonical scale of the unscaled wedge field (repository). -/
theorem ae_scale_pos {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P') :
    ∀ᵐ ω' ∂P', 0 < scaleParam γ (wedge0 γ X A ω') := by
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  exact (WedgeCan4.ae_wedge_canonical_spec_of_inputs
    (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hαQ) (WedgeInf.wedgeInfiniteTotal hγ hγ2 hαQ)
    hγ hγ2 hαQ hX hA hXA).mono fun _ h => h.1

theorem g1RawSmoothStmt_of_profile (h : G1ProfileStmt) : G1RawSmoothStmt := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA Ψ hΨ
  filter_upwards [h γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ] with a ha left ψe heq G hG
  refine ⟨dPart γ X A (Ψ left a), ?_, ?_⟩
  · filter_upwards [ha left G hG, ae_scale_pos hγ hγ2 hX hA hXA] with ω' hω hS
      using ⟨hS, hω.2.1, hω.2.2⟩
  · have hψm : Measurable (Ψ left a) :=
      (hΨ.1 left).comp (measurable_const.prodMk measurable_id)
    filter_upwards [ha left G hG, ae_wedgeGood hX hA hXA hG,
      ae_scale_pos hγ hγ2 hX hA hXA] with ω' hω hW hS
    intro d hd r hr L hL
    exact raw_coordChange_rescale_wedge hW (Qc γ) hS hψm heq hr (hω.1 d hd r hr) hL

/-- **`G1RegRepRC2Stmt` from the analytic map input and the profile input.** -/
theorem g1RegRepRC2Stmt_of_psi_profile (h1 : G1PsiExtStmt) (h2 : G1ProfileStmt) :
    G1RegRepRC2Stmt :=
  g1RegRepRC2Stmt_of h1 (g1RawSmoothStmt_of_profile h2)

end G1RC
end Thm18Asm
end QuantumZipper
