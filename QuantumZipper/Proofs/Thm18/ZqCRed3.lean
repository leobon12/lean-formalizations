import QuantumZipper.Proofs.Thm18.ZqCRed2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-CORE (10): `ZqCLocSandwichStmt → ZqCZoomTransferStmt → G3ZqO6CoreDStmt`

The two one-sided bounds `E Φ_L(h) ≤ ∫_T ρ J_L + 2 B_L` and `∫_T ρ J_L ≤ E Φ_L(h) + 2 B_L`,
`B_L = ∫_T ρ(x) E β_L(h^x) dx → 0` (`tendsto_palmM_zero`). See `ZqCRed`. Own bookkeeping
(AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqC

open G3Z2b2 D3Plus G1Zm G3Zq G3ZqL G3ZqO Factorization G2PalmLoc

/-- Splitting the weighted core integral. -/
theorem palmM_split {γ : ℝ} {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [SFinite P']
    {V : Ω' → FieldSample} (hV : IsFreeGFFModConstH V P') (left : Bool) (η : ℝ)
    (J : ℝ → ℝ≥0∞) {F : (ℕ → ℝ) → ℝ → ℝ≥0∞} (hF : Measurable (uncurry F)) :
    ∫⁻ x, (coreSet left η).indicator (fun x => rhoP γ x * (J x + palmE F γ P' V x)) x =
      (∫⁻ x, (coreSet left η).indicator (fun x => rhoP γ x * J x) x) + palmM F γ P' V left η := by
  rw [palmM, ← lintegral_add_right' _ (measurable_palmW hF γ hV left η).aemeasurable]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ coreSet left η
  · simp only [indicator_of_mem hx, mul_add]
  · simp only [indicator_of_notMem hx, add_zero]

/-- The wedge-side mass of a circle functional is a.e.-measurable in the sample. -/
theorem aemeasurable_wedge_coreInt {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : Ω' → FieldSample}
    {A : ℝ → Ω' → ℝ} (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P') {F : (ℕ → ℝ) → ℝ → ℝ≥0∞}
    (hF : Measurable (uncurry F)) (left : Bool) (η : ℝ) :
    AEMeasurable (fun ω => ∫⁻ x, (coreSet left η).indicator (fun x => F (vOf (F2.zU γ X A ω)) x) x
      ∂(qBoundaryMeasure γ (F2.zU γ X A ω))) P' := by
  have hcu : AEMeasurable (fun ω' => coords (wedgeU γ X A ω')) P' :=
    WedgeMeas.aemeasurable_coords_wedgeField hX.measurable_coord hA
  have hG := measurable_coreInt γ hF (measurableSet_coreSet left η)
  refine ((hG.comp measurable_reconstruct).comp_aemeasurable hcu).congr ?_
  filter_upwards [LogSingGood.wedgeRefGoodAS_holds hγ hγ2 (alpha_lt_Qc hγ hγ2) Ω' _ P' X A
    inferInstance hX hA hXA] with ω hg
  have hgU : IsLQGGood γ (wedgeU γ X A ω) := hg
  have hB : bdryM γ (wedgeU γ X A ω) = qBoundaryMeasure γ (wedgeU γ X A ω) := by
    rw [bdryM, if_pos (G4Core.bCert_of_isLQGGood hgU)]
  simp only [Function.comp_apply]
  rw [vOf_reconstruct, R18.bdryM_congr (avgReg_reconstruct_coords _), hB]

theorem palmE_add {F G : (ℕ → ℝ) → ℝ → ℝ≥0∞} (hF : Measurable (uncurry F)) (γ : ℝ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {V : Ω' → FieldSample}
    (hV : IsFreeGFFModConstH V P') (x : ℝ) :
    palmE (fun v x => F v x + G v x) γ P' V x = palmE F γ P' V x + palmE G γ P' V x :=
  lintegral_add_left (measurable_palmE_omega hF γ hV x) _

theorem palmM_add {F G : (ℕ → ℝ) → ℝ → ℝ≥0∞} (hF : Measurable (uncurry F))
    (hG : Measurable (uncurry G)) (γ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [SFinite P'] {V : Ω' → FieldSample} (hV : IsFreeGFFModConstH V P') (left : Bool) (η : ℝ) :
    palmM (fun v x => F v x + G v x) γ P' V left η = palmM F γ P' V left η + palmM G γ P' V left η := by
  have e : palmM (fun v x => F v x + G v x) γ P' V left η =
      ∫⁻ x, (coreSet left η).indicator (fun x => rhoP γ x * (palmE F γ P' V x + palmE G γ P' V x)) x := by
    unfold palmM
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ coreSet left η
    · rw [indicator_of_mem hx, indicator_of_mem hx, palmE_add (G := G) hF γ hV x]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  rw [e, palmM_split hV left η _ hG]
  rfl

section Bounds

variable {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} {Ω' : Type} [MeasurableSpace Ω']
  {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}
  {V : Ω' → FieldSample} {a : ℝ≥0 → ℝ} {left : Bool} {R : ℕ}
  {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞} {U η δ L : ℝ} {φ β : (ℕ → ℝ) → ℝ → ℝ≥0∞}

/-- **The wedge-side upper bound.** -/
theorem wedge_upper (hγ : 0 < γ) (hγ2 : γ < 2) (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P') (hXA : IndepFun X (fun ω t => A t ω) P')
    (hV : IsFreeGFFModConstH V P') (hPF : ZqCPalmFor γ P' X A V)
    (hη : 0 < η) (hη4 : η < 1 / 4) (hδ : 0 < δ) (hδη : δ < η / 2)
    (hφm : Measurable (uncurry φ)) (hβm : Measurable (uncurry β))
    (hsand : ∀ (y : FieldSample), ∀ x ∈ coreSet left η,
      Γ (g1zLocData R (g1zM γ L Ψ left ((y, a), x))) ≤ φ (vOf y) x + β (vOf y) x ∧
      φ (vOf y) x ≤ Γ (g1zLocData R (g1zM γ L Ψ left ((y, a), x))) + β (vOf y) x) :
    ∫⁻ ω', g1PhiD γ L R Γ Ψ left U η δ (wedgeU γ X A ω', a) ∂P' ≤
      (∫⁻ x, (coreSet left η).indicator
        (fun x => rhoP γ x * palmJ γ L R Γ Ψ left U δ a P' V x) x) +
        (palmM β γ P' V left η + palmM β γ P' V left η) := by
  have hgood := LogSingGood.wedgeRefGoodAS_holds hγ hγ2 (alpha_lt_Qc hγ hγ2) Ω' _ P' X A
    inferInstance hX hA hXA
  have hwm : Measurable (uncurry (winPhi γ left U δ)) := measurable_winPhi γ left U δ
  have hfm : Measurable (uncurry fun v x => winPhi γ left U δ v x * φ v x) := hwm.mul hφm
  have hgm : Measurable (uncurry fun v x => winPhi γ left U δ v x * φ v x + β v x) := hfm.add hβm
  have hββm : Measurable (uncurry fun v x => β v x + β v x) := hβm.add hβm
  have hpalm : ∀ x ∈ coreSet left η,
      palmE (fun v x => winPhi γ left U δ v x * φ v x + β v x) γ P' V x ≤
        palmJ γ L R Γ Ψ left U δ a P' V x + palmE (fun v x => β v x + β v x) γ P' V x := by
    intro x hx
    unfold palmE palmJ
    rw [← lintegral_add_right' _ (measurable_palmE_omega hββm γ hV x).aemeasurable]
    refine lintegral_mono fun ω => ?_
    beta_reduce
    rw [winPhi_palm γ left U hη4 hδ hδη hx V ω]
    have hw1 : (palmWin γ left U δ x V).indicator (1 : Ω' → ℝ≥0∞) ω ≤ 1 :=
      indicator_le (fun _ _ => le_rfl) _
    have h := sandwich_mul hw1 (hsand (G1Zm.palmFieldAt γ x (V ω)) x hx).2
    calc _ ≤ ((palmWin γ left U δ x V).indicator 1 ω *
            Γ (g1zLocData R (g1zM γ L Ψ left ((G1Zm.palmFieldAt γ x (V ω), a), x))) +
            β (vOf (G1Zm.palmFieldAt γ x (V ω))) x) +
          β (vOf (G1Zm.palmFieldAt γ x (V ω))) x := add_le_add h le_rfl
      _ = _ := by rw [add_assoc]
  calc ∫⁻ ω', g1PhiD γ L R Γ Ψ left U η δ (wedgeU γ X A ω', a) ∂P'
      ≤ ∫⁻ ω, ∫⁻ x, (coreSet left η).indicator (fun x =>
          winPhi γ left U δ (vOf (F2.zU γ X A ω)) x * φ (vOf (F2.zU γ X A ω)) x +
            β (vOf (F2.zU γ X A ω)) x) x ∂(qBoundaryMeasure γ (F2.zU γ X A ω)) ∂P' := by
        refine lintegral_mono_ae ?_
        filter_upwards [hgood] with ω hg
        have hgU : IsLQGGood γ (wedgeU γ X A ω) := hg
        unfold g1PhiD
        rw [show bdryM γ (wedgeU γ X A ω) = qBoundaryMeasure γ (F2.zU γ X A ω) by
          rw [bdryM, if_pos (G4Core.bCert_of_isLQGGood hgU)]]
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ coreSet left η
        · rw [core_winD_indicator hgU left U hη hη4 hδ hδη hx, indicator_of_mem hx]
          exact sandwich_mul (winPhi_le_one _ _ _ _ _ _) (hsand _ x hx).1
        · rw [indicator_of_notMem (fun h => hx h.1)]; exact bot_le
    _ = palmM (fun v x => winPhi γ left U δ v x * φ v x + β v x) γ P' V left η :=
        palm_vOf hPF left hη hη4 hgm
    _ ≤ ∫⁻ x, (coreSet left η).indicator (fun x => rhoP γ x *
          (palmJ γ L R Γ Ψ left U δ a P' V x +
            palmE (fun v x => β v x + β v x) γ P' V x)) x := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ coreSet left η
        · simp only [indicator_of_mem hx]
          exact mul_le_mul' le_rfl (hpalm x hx)
        · simp only [indicator_of_notMem hx, le_refl]
    _ = (∫⁻ x, (coreSet left η).indicator
          (fun x => rhoP γ x * palmJ γ L R Γ Ψ left U δ a P' V x) x) +
          palmM (fun v x => β v x + β v x) γ P' V left η :=
        palmM_split hV left η _ hββm
    _ = _ := by rw [palmM_add hβm hβm γ hV left η]

/-- **The wedge-side lower bound.** -/
theorem wedge_lower (hγ : 0 < γ) (hγ2 : γ < 2) (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P') (hXA : IndepFun X (fun ω t => A t ω) P')
    (hV : IsFreeGFFModConstH V P') (hPF : ZqCPalmFor γ P' X A V)
    (hη : 0 < η) (hη4 : η < 1 / 4) (hδ : 0 < δ) (hδη : δ < η / 2)
    (hφm : Measurable (uncurry φ)) (hβm : Measurable (uncurry β))
    (hsand : ∀ (y : FieldSample), ∀ x ∈ coreSet left η,
      Γ (g1zLocData R (g1zM γ L Ψ left ((y, a), x))) ≤ φ (vOf y) x + β (vOf y) x ∧
      φ (vOf y) x ≤ Γ (g1zLocData R (g1zM γ L Ψ left ((y, a), x))) + β (vOf y) x) :
    (∫⁻ x, (coreSet left η).indicator
        (fun x => rhoP γ x * palmJ γ L R Γ Ψ left U δ a P' V x) x) ≤
      ∫⁻ ω', g1PhiD γ L R Γ Ψ left U η δ (wedgeU γ X A ω', a) ∂P' +
        (palmM β γ P' V left η + palmM β γ P' V left η) := by
  have hT := measurableSet_coreSet left η
  have hgood := LogSingGood.wedgeRefGoodAS_holds hγ hγ2 (alpha_lt_Qc hγ hγ2) Ω' _ P' X A
    inferInstance hX hA hXA
  have hwm : Measurable (uncurry (winPhi γ left U δ)) := measurable_winPhi γ left U δ
  have hfm : Measurable (uncurry fun v x => winPhi γ left U δ v x * φ v x) := hwm.mul hφm
  have hpalm : ∀ x ∈ coreSet left η, palmJ γ L R Γ Ψ left U δ a P' V x ≤
      palmE (fun v x => winPhi γ left U δ v x * φ v x) γ P' V x + palmE β γ P' V x := by
    intro x hx
    unfold palmE palmJ
    rw [← lintegral_add_right' _ (measurable_palmE_omega hβm γ hV x).aemeasurable]
    refine lintegral_mono fun ω => ?_
    beta_reduce
    rw [winPhi_palm γ left U hη4 hδ hδη hx V ω]
    have hw1 : (palmWin γ left U δ x V).indicator (1 : Ω' → ℝ≥0∞) ω ≤ 1 :=
      indicator_le (fun _ _ => le_rfl) _
    exact sandwich_mul hw1 (hsand _ x hx).1
  have hβsec : ∀ y : FieldSample, Measurable fun x => (coreSet left η).indicator
      (fun x => β (vOf y) x) x := by
    intro y
    have h := hβm.comp ((measurable_const (a := vOf y)).prodMk measurable_id)
    simp only [Function.comp_def] at h
    exact h.indicator hT
  calc (∫⁻ x, (coreSet left η).indicator
        (fun x => rhoP γ x * palmJ γ L R Γ Ψ left U δ a P' V x) x)
      ≤ ∫⁻ x, (coreSet left η).indicator (fun x => rhoP γ x *
          (palmE (fun v x => winPhi γ left U δ v x * φ v x) γ P' V x + palmE β γ P' V x)) x := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ coreSet left η
        · simp only [indicator_of_mem hx]
          exact mul_le_mul' le_rfl (hpalm x hx)
        · simp only [indicator_of_notMem hx, le_refl]
    _ = palmM (fun v x => winPhi γ left U δ v x * φ v x) γ P' V left η + palmM β γ P' V left η :=
        palmM_split hV left η _ hβm
    _ ≤ (∫⁻ ω', g1PhiD γ L R Γ Ψ left U η δ (wedgeU γ X A ω', a) ∂P' + palmM β γ P' V left η) +
          palmM β γ P' V left η := by
        refine add_le_add ?_ le_rfl
        rw [← palm_vOf hPF left hη hη4 hfm, ← palm_vOf hPF left hη hη4 hβm,
          ← lintegral_add_right' _ (aemeasurable_wedge_coreInt hγ hγ2 hX hA hXA hβm left η)]
        refine lintegral_mono_ae ?_
        filter_upwards [hgood] with ω hg
        have hgU : IsLQGGood γ (wedgeU γ X A ω) := hg
        unfold g1PhiD
        rw [show bdryM γ (wedgeU γ X A ω) = qBoundaryMeasure γ (F2.zU γ X A ω) by
          rw [bdryM, if_pos (G4Core.bCert_of_isLQGGood hgU)]]
        rw [← lintegral_add_right _ (hβsec (F2.zU γ X A ω))]
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ coreSet left η
        · rw [core_winD_indicator hgU left U hη hη4 hδ hδη hx, indicator_of_mem hx,
            indicator_of_mem hx]
          exact sandwich_mul (winPhi_le_one _ _ _ _ _ _) (hsand _ x hx).2
        · rw [indicator_of_notMem hx]; exact bot_le
    _ = _ := by rw [add_assoc]

end Bounds

/-- **`ZqCZoomTransferStmt` from the local sandwich.** -/
theorem zqCZoomTransferStmt_of_sandwich (hS : ZqCLocSandwichStmt) : ZqCZoomTransferStmt := by
  intro γ hγ hγ2 Ψ hsel Ω' _ P' _ X A hX hA hXA V hV hPF a ha left R Γ hΓ hΓ1 U hU η hη hη4 δ hδ
    hδη e he
  obtain ⟨φ, β, hφm, hβm, hβ1, hsand, hlimβ⟩ := hS γ hγ hγ2 Ψ hsel a ha left R Γ hΓ hΓ1 η hη hη4
  have hB := tendsto_palmM_zero hγ hβm hβ1 hV left hη hη4 (fun x hx => hlimβ P' V hV x hx)
  have he2 : (0 : ℝ≥0∞) < e / 2 := ENNReal.div_pos he.ne' ENNReal.ofNat_ne_top
  have hsum : e / 2 + e / 2 = e := ENNReal.add_halves e
  filter_upwards [hB.eventually (Iic_mem_nhds he2)] with L hL
  have hL' : palmM (β L) γ P' V left η + palmM (β L) γ P' V left η ≤ e := by
    rw [← hsum]; exact add_le_add hL hL
  constructor
  · exact (wedge_upper hγ hγ2 hX hA hXA hV hPF hη hη4 hδ hδη (hφm L) (hβm L)
      (hsand L)).trans (add_le_add le_rfl hL')
  · exact (wedge_lower hγ hγ2 hX hA hXA hV hPF hη hη4 hδ hδη (hφm L) (hβm L)
      (hsand L)).trans (add_le_add le_rfl hL')

/-- **The core node from the local sandwich.** -/
theorem g3ZqO6CoreDStmt_of_sandwich (hS : ZqCLocSandwichStmt) : G3ZqO6CoreDStmt :=
  g3ZqO6CoreDStmt_of_zoomTransfer (zqCZoomTransferStmt_of_sandwich hS)

end ZqC
end Thm18Asm
end QuantumZipper
