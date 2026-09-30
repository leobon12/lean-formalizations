import QuantumZipper.Proofs.Thm18.G3ZqFCore
import QuantumZipper.Proofs.Zipper.D3PlusN2Loc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-CORE-C: the conditional zoom core with the window certificate at every smaller radius

`cond_zoom_palm_free_cert`: `G3Cv.G3ZqF.cond_zoom_palm_free_full` with one extra conclusion —
the measurable window certificate `G3ZqF.dyadCert` of the dyadic data of the zoom holds a.s. at
every radius `ρ ≤ r''` (on the coupling space by `dyadCert_of_model` with the local area limit
restricted from `halfDisc r''` to `halfDisc ρ`; transferred along the dyadic law, since the
dyadic data at radius `ρ` is a measurable restriction of the data at radius `r''`).

Sources: Sheffield arXiv:1012.4797 pp. 70–71 and proof of Prop. 5.5 (p. 65). Own bookkeeping
(AGENT_GUIDE cost rule), a copy of the proof of `cond_zoom_palm_free_full`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric InnerProductSpace
open scoped NNReal ENNReal Topology ComplexConjugate

namespace QuantumZipper
namespace G3Cv
namespace ZqCC

open G3ZqF D3Plus K3 GFFExist LQGDimension.ExistAsm

/-- **The conditional zoom core with the window certificate at every smaller radius.** -/
theorem cond_zoom_palm_free_cert {r₀ : ℝ} {ψ : ℂ → ℂ} (hr₀ : 0 < r₀)
    (hψ : Thm18Asm.IsG0Map r₀ ψ) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρf : ℝ} (hρf : 0 < ρf)
    {f h : ℂ → ℝ} (hf : ∀ u ∈ closedBall (0 : ℂ) ρf ∩ Hbar, f u = γ * -Real.log ‖u‖ + h u)
    (hh : Continuous h) (hfm : Measurable f) (hhh : HarmonicOnNhd h (ball (0 : ℂ) ρf))
    (hhc : ∀ u ∈ ball (0 : ℂ) ρf, h (conj u) = h u)
    {S : Measure ℂ} (hS : IsAdmissibleH S) (hS1 : S Set.univ = 1)
    (hSf : ∀ᵐ y ∂S, ρf < ‖y‖) {rmax : ℝ} (hrmax : 0 < rmax) :
    ∃ r'' R₀ : ℝ, 0 < r'' ∧ r'' ≤ rmax ∧ 0 < R₀ ∧ R₀ ≤ ρf ∧
      ∀ (x : ℝ), IsAdmissibleH (S.map (· + (x : ℂ))) →
      ∀ {K : Type} (q : K → WedgeTK.BPair),
        (∀ k, IsAdmissibleH ((q k).1.1.map (· + ((-x : ℝ) : ℂ))) ∧
          IsAdmissibleH ((q k).1.2.map (· + ((-x : ℝ) : ℂ))) ∧
          (∀ᵐ y ∂((q k).1.1.map (· + ((-x : ℝ) : ℂ))), R₀ < ‖y‖) ∧
          (∀ᵐ y ∂((q k).1.2.map (· + ((-x : ℝ) : ℂ))), R₀ < ‖y‖)) →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (V : Ω' → FieldSample), IsFreeGFFModConstH V P' →
      (∀ ρ : ℝ, 0 < ρ → ρ ≤ r'' → ∀ L, ∀ᵐ ω ∂P',
          G3ZqF.dyadCert γ ρ (dyadData ρ (zoomS γ L (Qc γ) f ψ S (rawTranslate (V ω) x)))) ∧
      (∀ L, AEMeasurable (fun ω => dyadData r''
          (zoomS γ L (Qc γ) f ψ S (rawTranslate (V ω) x))) P') ∧
      (∀ L, ∀ᵐ ω ∂P', ∃ m, IsVagueLimitOn (halfDisc r'')
          (areaApprox γ (zoomS γ L (Qc γ) f ψ S (rawTranslate (V ω) x))) m) ∧
      (∀ R : ℕ, Tendsto (fun L => P' ((fun ω => dyadData r''
          (zoomS γ L (Qc γ) f ψ S (rawTranslate (V ω) x))) ⁻¹' dyadBad γ r'' R)) atTop (𝓝 0)) ∧
      ∀ {Ω₁ : Type} [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
        (Y' : Ω₁ → FieldSample), IsQuantumWedge γ γ Y' P₁ →
      ∀ (R : ℕ) (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞), Measurable Γ → (∀ y, Γ y ≤ 1) →
      ∀ η : ℝ≥0∞, 0 < η → ∀ᶠ L in atTop, ∀ B : Set (K → ℝ), MeasurableSet B →
        ∫⁻ ω, B.indicator 1 (fun k => WedgeTK.gaussFam V q k ω) *
            Γ (locFieldFull R (canonicalOn γ (zoomS γ L (Qc γ) f ψ S (rawTranslate (V ω) x))
              (halfDisc r''))) ∂P' ≤
          P' ((fun ω k => WedgeTK.gaussFam V q k ω) ⁻¹' B) *
            ∫⁻ ω, Γ (locFieldFull R (Y' ω)) ∂P₁ + η ∧
        P' ((fun ω k => WedgeTK.gaussFam V q k ω) ⁻¹' B) *
            ∫⁻ ω, Γ (locFieldFull R (Y' ω)) ∂P₁ ≤
          ∫⁻ ω, B.indicator 1 (fun k => WedgeTK.gaussFam V q k ω) *
            Γ (locFieldFull R (canonicalOn γ (zoomS γ L (Qc γ) f ψ S (rawTranslate (V ω) x))
              (halfDisc r''))) ∂P' + η := by
  have hD3 : D3PlusIStmtRich := d3PlusIRich_of_N2 d3PlusIN2RichStmt_holds
  obtain ⟨r, s, hr, -, E', _, U, X', Ξ, g, hU, hSet, hag, R₀, hR₀, hR₀le, hfar⟩ :=
    G3Za.G3ZqF.exists_g0Setup_palm_far_le hr₀ hψ hγ hγ2 hρf hf hh hfm hhh hhc hS hS1 hSf
  obtain ⟨Ψ, r₀', ρ, r₁, m, M, -, hD, heq⟩ := pullData_of_isG0Map hr₀ hψ
  have hΨ0 : Ψ 0 = 0 := by rw [heq (mem_ball_self hD.conf.pos)]; exact hψ.2.2.2.1
  have hM := hD.bl.2.1
  set ρ' : ℝ := min ρ (ρf / (2 * M)) with hρ'
  have hρ'0 : 0 < ρ' := lt_min hD.hρ (by positivity)
  have hDs := hD.shrink hρ'0 (min_le_left _ _)
  have hMρ : M * ρ' < ρf := by
    have h1 : ρ' ≤ ρf / (2 * M) := min_le_right _ _
    have h2 : M * ρ' ≤ M * (ρf / (2 * M)) := mul_le_mul_of_nonneg_left h1 hM.le
    have h3 : M * (ρf / (2 * M)) = ρf / 2 := by
      rw [mul_div_assoc', mul_comm 2 M, mul_div_mul_left _ _ hM.ne']
    linarith
  have hfR : ∀ u ∈ closedBall (0 : ℂ) ρf ∩ Hbar, f u = γ * -Real.log ‖u‖ + h u := hf
  set r'' : ℝ := min (min r ρ') rmax with hr''
  have hr''0 : 0 < r'' := lt_min (lt_min hr hρ'0) hrmax
  have hr''r : r'' ≤ r := (min_le_left _ _).trans (min_le_left _ _)
  have hr''ρ : r'' ≤ ρ' := (min_le_left _ _).trans (min_le_right _ _)
  refine ⟨r'', R₀, hr''0, min_le_right _ _, hR₀, hR₀le, ?_⟩
  intro x hSx K q hq Ω' _ P' _ V hV
  have hS'' := hSet.mono_radius hr''0 hr''r
  have hag'' : ∀ᵐ ω ∂stdP, ∀ L : ℝ, AgreeNear (zoomS γ L (Qc γ) f ψ S (U ω))
      (zoomModel γ γ L (foldedCircle 0 s) (X' ω) (g ω)) r'' :=
    hag.mono fun ω h L => AgreeNear.mono_radius (h L) hr''r
  -- the coupled field translated back
  set Yc : (ℕ → ℝ) → FieldSample := fun ω => rawTranslate (U ω) (-x) with hYc
  have hYc : IsFreeGFFModConstH Yc stdP := isFree_rawTranslate hU (-x)
  have hYU : ∀ ω, rawTranslate (Yc ω) x = U ω := fun ω => rawTranslate_neg (U ω) x
  -- the conditioning is a function of `Ξ`
  have hkF : ∀ k, ∃ F : E' → ℝ, Measurable F ∧
      ∀ᵐ ω ∂stdP, WedgeTK.gaussFam Yc q k ω = F (Ξ ω) := by
    intro k
    obtain ⟨a1, a2, a3, a4⟩ := hq k
    have hmass : ((q k).1.1.map (· + ((-x : ℝ) : ℂ))) Set.univ =
        ((q k).1.2.map (· + ((-x : ℝ) : ℂ))) Set.univ := by
      rw [Measure.map_apply (measurable_add_const _) MeasurableSet.univ,
        Measure.map_apply (measurable_add_const _) MeasurableSet.univ, preimage_univ]
      exact (q k).2.2.2
    obtain ⟨F, hF, hFe⟩ := hfar _ _ a1 a2 hmass a3 a4
    exact ⟨F, hF, hFe.mono fun ω h => by
      show U ω ((q k).1.1.map (· + ((-x : ℝ) : ℂ))) - U ω ((q k).1.2.map (· + ((-x : ℝ) : ℂ))) =
        F (Ξ ω)
      exact h⟩
  have hVΞ : ∀ B : Set (K → ℝ), MeasurableSet B → ∃ B' : Set E', MeasurableSet B' ∧
      (fun ω k => WedgeTK.gaussFam Yc q k ω) ⁻¹' B =ᵐ[stdP] Ξ ⁻¹' B' := fun B hB =>
    exists_ae_eq_preimage_of_coords (V := fun ω k => WedgeTK.gaussFam Yc q k ω) hkF hB
  have hlaw := fun L => dyadLawCond_eq_free hDs hΨ0 heq hfR hh hfm hMρ γ L (Qc γ) x hSx hS1
    (r := r'') hr''ρ q hYc hV
  simp only [hYU] at hlaw
  -- the dyadic marginals
  have hDm : ∀ L, AEMeasurable (fun ω => dyadData r''
      (zoomS γ L (Qc γ) f ψ S (rawTranslate (V ω) x))) P' := fun L => (hlaw L).2.1.fst
  have hDsm : ∀ L, AEMeasurable (fun ω => dyadData r'' (zoomS γ L (Qc γ) f ψ S (U ω))) stdP :=
    fun L => (hlaw L).1.fst
  have hmarg : ∀ L, (stdP.map fun ω => dyadData r'' (zoomS γ L (Qc γ) f ψ S (U ω))) =
      P'.map fun ω => dyadData r'' (zoomS γ L (Qc γ) f ψ S (rawTranslate (V ω) x)) := by
    intro L
    have e := congrArg (fun μ : Measure ((DyIdxIn r'' → ℝ) × (K → ℝ)) => μ.map Prod.fst)
      (hlaw L).2.2
    rwa [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable (hlaw L).1,
      AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable (hlaw L).2.1] at e
  have hsetup := fun R : ℕ => tendsto_dyadBad_of_setup hS''
    (Zf := fun L ω => zoomS γ L (Qc γ) f ψ S (U ω)) hag'' hDsm R
  -- goodness on `P'`
  have hg' : ∀ L, ∀ᵐ ω ∂P', ∃ m, IsVagueLimitOn (halfDisc r'')
      (areaApprox γ (zoomS γ L (Qc γ) f ψ S (rawTranslate (V ω) x))) m := by
    intro L
    have hmeas := measurableSet_dyadCert γ r''
    have hcS : ∀ᵐ ω ∂stdP, dyadCert γ r'' (dyadData r'' (zoomS γ L (Qc γ) f ψ S (U ω))) := by
      filter_upwards [(hsetup 0).1 L, hag'', AreaOffsets.ae_isLQGGood hS''.hX hγ hγ2]
        with ω h1 h2 h3
      exact dyadCert_of_model h3.1 (continuousOn_g_of_harm (hS''.harm ω)) (h2 L) le_rfl h1
    have h0 : P' ((fun ω => dyadData r''
        (zoomS γ L (Qc γ) f ψ S (rawTranslate (V ω) x))) ⁻¹' {ξ | dyadCert γ r'' ξ}ᶜ) = 0 := by
      rw [← Measure.map_apply₀ (hDm L) hmeas.compl.nullMeasurableSet, ← hmarg L,
        Measure.map_apply₀ (hDsm L) hmeas.compl.nullMeasurableSet]
      exact ae_iff.1 hcS
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω
    refine exists_vague_of_dyadCert ?_
    by_contra hc
    exact hω hc
  -- the certificate at every smaller radius
  have hcert : ∀ ρ₂ : ℝ, 0 < ρ₂ → ρ₂ ≤ r'' → ∀ L, ∀ᵐ ω ∂P',
      dyadCert γ ρ₂ (dyadData ρ₂ (zoomS γ L (Qc γ) f ψ S (rawTranslate (V ω) x))) := by
    intro ρ₂ _hρ₂ hρ L
    have hmeas := measurableSet_dyadCert γ ρ₂
    let restr : (DyIdxIn r'' → ℝ) → (DyIdxIn ρ₂ → ℝ) :=
      fun ξ i => ξ ⟨i.1, lt_of_lt_of_le i.2 hρ⟩
    have hrm : Measurable restr := measurable_pi_iff.2 fun i => measurable_pi_apply _
    have hC : MeasurableSet (restr ⁻¹' {ξ | dyadCert γ ρ₂ ξ}ᶜ) := hrm hmeas.compl
    have hcS : ∀ᵐ ω ∂stdP,
        dyadCert γ ρ₂ (restr (dyadData r'' (zoomS γ L (Qc γ) f ψ S (U ω)))) := by
      filter_upwards [(hsetup 0).1 L, hag'', AreaOffsets.ae_isLQGGood hS''.hX hγ hγ2]
        with ω h1 h2 h3
      obtain ⟨m, hm⟩ := h1
      exact dyadCert_of_model h3.1 (continuousOn_g_of_harm (hS''.harm ω)) (h2 L) hρ
        ⟨_, isVagueLimitOn_restrict (isOpen_halfDisc ρ₂)
          (inter_subset_inter_left _ (Metric.ball_subset_ball hρ)) hm⟩
    have h0 : P' ((fun ω => dyadData r''
        (zoomS γ L (Qc γ) f ψ S (rawTranslate (V ω) x))) ⁻¹'
          (restr ⁻¹' {ξ | dyadCert γ ρ₂ ξ}ᶜ)) = 0 := by
      rw [← Measure.map_apply₀ (hDm L) hC.nullMeasurableSet, ← hmarg L,
        Measure.map_apply₀ (hDsm L) hC.nullMeasurableSet]
      exact ae_iff.1 hcS
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω
    by_contra hc
    exact hω hc
  refine ⟨hcert, hDm, hg', fun R => ?_, ?_⟩
  · refine ((hsetup R).2.congr fun L => ?_)
    show (stdP.map fun ω => dyadData r'' (zoomS γ L (Qc γ) f ψ S (U ω))) (dyadBad γ r'' R) = _
    rw [hmarg L, Measure.map_apply₀ (hDm L) (measurableSet_dyadBad γ r'' R).nullMeasurableSet]
  · intro Ω₁ _ P₁ _ Y' hY' R Γ hΓ hΓ1 η hη
    exact cond_zoom_of_lawEq' hD3 hS'' hag'' hVΞ (fun L => (hlaw L).1) (fun L => (hlaw L).2.1)
      (fun L => (hlaw L).2.2) hg' hY' R hΓ hΓ1 η hη

end ZqCC
end G3Cv
end QuantumZipper
