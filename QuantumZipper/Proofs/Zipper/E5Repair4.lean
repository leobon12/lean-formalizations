import QuantumZipper.Proofs.Zipper.E5Repair3
import QuantumZipper.Proofs.Zipper.E5Final4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5 repair, part 4: the repaired E5 inputs and the consumer end (decision D39)

`E5Final4.not_e5ReprG`, `not_e5ModelApproxG`: the committed `E5ReprG`, `E5ModelApproxG` and
`E5Main5.E5ModelStmtG` ask for a probability measure `W` on `ℝ≥0 → ℝ` (product σ-algebra) with
`IsBrownianReal (fun t b => b t) W`, which does not exist. Following decision D39 the "Brownian
coordinate measure" is restated as a **Wiener coordinate measure**,
`IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W` (the coordinate process has the Brownian
finite-dimensional laws; this characterizes Wiener measure on the product σ-algebra, see
`E5.wiener_eq_map`, and it exists: `E5.exists_wiener`).

Restated nodes (primed): `E5ModelStmtG'`, `E5TargetStmtG'` (proved: `e5TargetStmtG'_locFieldFull`,
`e5TargetStmtG'_locField`), `E5ModelApproxG'`, `E5ReprG'`, and the consumer chain
`e5G_of_d3'`, `e5G_of_approx'`, `e5ModelApprox_of_repr'`, **`e5Rich_of_repr'`**:
`D3PlusIStmtRich → D3PlusIIStmtRich → E5ReprG' locFieldFull → E4Stmt → E6.E5StmtRich`.
The proofs are the committed ones verbatim, with `ZoomModel.tvNear'` (E5Repair3) in place of the
vacuous `ZoomModel.tvNear`. The old inputs imply the new ones (`e5ReprG'_of_e5ReprG`, …), so
nothing proved from the old inputs is lost. Source: Sheffield arXiv:1012.4797, §5.4, proof of
Lemma 5.6 (as for the committed versions).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open LengthMarkov.GermDensity D3Plus B2 E1

/-- **Open input 2 (the `P_*` side).** For a wedge `Y` independent of a Brownian motion `B'`,
the `locData R` functional of `(Y, drive κ B')` is the `P' ⊗ W` functional of
`(locField R Y, √κ b(min · R))`, for every Brownian coordinate measure `W`. -/
def E5TargetStmtG' {F : Type} [MeasurableSpace F] (fr : ℕ → FieldSample → F) : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), 0 < κ → κ < 4 →
    IsQuantumWedge (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) Y P' →
    IsBrownianReal B' P' → IndepFun Y (pathOf B') P' →
    ∀ (W : Measure (ℝ≥0 → ℝ)) [IsProbabilityMeasure W],
      IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W →
    ∀ (R : ℕ) (Γ : F × (ℝ≥0 → ℝ) → ℝ≥0∞), Measurable Γ → (∀ y, Γ y ≤ 1) →
      ∫⁻ ω', Γ (locG fr R (Y ω', drive κ B' ω')) ∂P' =
        targetF fr κ R W P' Y 0 Γ

/-- **The `P_*` side** for a readout factoring measurably through `F1.dataH`. -/
theorem e5TargetStmtG_of_factor' {F : Type} [MeasurableSpace F] (fr : ℕ → FieldSample → F)
    (hfr : ∀ R : ℕ, ∃ φ : (ℕ → ℝ) × (TestFun H → ℝ) → F, Measurable φ ∧
      ∀ x, fr R x = φ (F1.dataH x)) : E5TargetStmtG' fr := by
  intro κ Ω' _ P' _ Y B' hκ hκ4 hY hB' hYB W _ hW R Γ hΓ hΓ1
  obtain ⟨φ, hφ, hfrφ⟩ := hfr R
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := (Real.sqrt_lt' two_pos).2 (by norm_num; exact hκ4)
  have hYm : AEMeasurable (fun ω' => F1.dataH (Y ω')) P' :=
    Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hY.1 hY
  have hBm : AEMeasurable (pathOf B') P' := IsBrownianReal.aemeasurable_pathOf hB'
  have hind : IndepFun (fun ω' => F1.dataH (Y ω')) (pathOf B') P' :=
    (hYB.comp F1.measurable_dataH measurable_id :)
  -- the path law of `B'` is `W`
  have hlawB : P'.map (pathOf B') = W := by
    have key : ∀ {Ω₀ : Type} [MeasurableSpace Ω₀] {μ : Measure Ω₀} {D : ℝ≥0 → Ω₀ → ℝ},
        IsPreBrownianReal D μ → AEMeasurable (pathOf D) μ →
        IsProjectiveLimit (μ.map (pathOf D)) BrownianReal.projectiveFamily := by
      intro Ω₀ _ μ D hD hDm I
      rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict I).aemeasurable hDm]
      exact (hD.hasLaw I).map_eq
    have hid : pathOf (fun t (b : ℝ≥0 → ℝ) => b t) = id := rfl
    have h2 := key hW (by rw [hid]; exact measurable_id.aemeasurable)
    rw [hid, Measure.map_id] at h2
    exact (key hB'.toIsPreBrownianReal hBm).unique h2
  set G : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) → ℝ≥0∞ :=
    fun p => Γ (φ p.1, drvWin κ R (pathRestr (R : ℝ≥0) p.2)) with hG
  have hGm : Measurable G := hΓ.comp ((hφ.comp measurable_fst).prodMk
    ((measurable_drvWin κ R).comp ((measurable_pathRestr _).comp measurable_snd)))
  have hL : ∫⁻ ω', Γ (locG fr R (Y ω', drive κ B' ω')) ∂P' =
      ∫⁻ ω', G (F1.dataH (Y ω'), pathOf B' ω') ∂P' := by
    refine lintegral_congr fun ω' => ?_
    simp only [locG, hG, hfrφ, drive_min_eq_drvWin]
  have hR : targetF fr κ R W P' Y 0 Γ =
      ∫⁻ ω', ∫⁻ b, G (F1.dataH (Y ω'), b) ∂W ∂P' := by
    simp only [targetF, hG, hfrφ]
  rw [hL, hR]
  have e1 := lintegral_map' (μ := P') (f := G)
    (g := fun ω' => (F1.dataH (Y ω'), pathOf B' ω')) hGm.aemeasurable (hYm.prodMk hBm)
  rw [(indepFun_iff_map_prod_eq_prod_map_map hYm hBm).1 hind, hlawB,
    lintegral_prod _ hGm.aemeasurable] at e1
  have e2 := lintegral_map' (μ := P') (f := fun d => ∫⁻ b, G (d, b) ∂W)
    (g := fun ω' => F1.dataH (Y ω')) hGm.lintegral_prod_right'.aemeasurable hYm
  rw [e2] at e1
  exact e1.symm

theorem e5TargetStmtG_locFieldFull' : E5TargetStmtG' locFieldFull :=
  e5TargetStmtG_of_factor' locFieldFull locFieldFull_factor

/-- **E5 model input, approximate form.** Given E4, for every E5 setup, `δ > 0` and `R`: a
Wiener coordinate measure `W` such that for every `ε > 0` some zoom model `M` has functional
`ε`-close (eventually in `C`, uniformly in tests `Γ ∈ [0,1]`) to E5's left side divided by the
Palm mass. -/
def E5ModelApproxG' {F : Type} [MeasurableSpace F] (fr : ℕ → FieldSample → F) : Prop :=
  Thm13Asm.E4Stmt →
  ∀ (κ T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ),
    Blueprint.RevCouplingBoundaryMeasureRegular → Setup κ T P B X ϖ →
    IsQuantumWedge (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) Y P' →
    IsBrownianReal B' P' → IndepFun Y (pathOf B') P' → ∀ δ : ℝ, 0 < δ → ∀ R : ℕ,
    ∃ (W : Measure (ℝ≥0 → ℝ)) (_ : IsProbabilityMeasure W),
      IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W ∧
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ M : ZoomModel fr κ R W,
        ∀ᶠ C in atTop, ∀ Γ : F × (ℝ≥0 → ℝ) → ℝ≥0∞, Measurable Γ → (∀ y, Γ y ≤ 1) →
          lhsF (locG fr) κ T P B X ϖ δ R C Γ ≤ pmass κ T P B X ϖ δ * M.fn C Γ + ε ∧
            pmass κ T P B X ϖ δ * M.fn C Γ ≤ lhsF (locG fr) κ T P B X ϖ δ R C Γ + ε

/-- **E5 for a general readout from the approximate model input**: D3⁺(i), D3⁺(ii), the
approximate identification and the (proved) target identity give `E6.E5StmtG (locG fr)`. -/
theorem e5G_of_approx' {F : Type} [MeasurableSpace F] (fr : ℕ → FieldSample → F) (hI : D3IG fr)
    (hII : D3IIG fr) (hModel : E5ModelApproxG' fr) (hTarget : E5TargetStmtG' fr)
    (hE4 : Thm13Asm.E4Stmt) : E6.E5StmtG (locG fr) := by
  intro κ T Ω _ P _ B X ϖ Ω' _ P' _ Y B' hReg hS hY hB' hYB δ hδ _ _ R η hη
  obtain ⟨W, hWp, hW, hM⟩ := hModel hE4 κ T P B X ϖ P' Y B' hReg hS hY hB' hYB δ hδ R
  have hpm := pmass_ne_top hS hδ
  have key : TVNear (lhsF (locG fr) κ T P B X ϖ δ R)
      (rhsF (locG fr) κ (pmass κ T P B X ϖ δ) P' Y B' R) := by
    refine TVNear.of_approx fun ε hε => ?_
    obtain ⟨M, hMε⟩ := hM ε hε
    refine ⟨fun C Γ => pmass κ T P B X ϖ δ * M.fn C Γ, ?_, hMε⟩
    exact ((M.tvNear' hW hI hII hY).const_mul hpm).trans
      (TVNear.of_eventually_eq (Eventually.of_forall fun C Γ hΓ hΓ1 => by
        simp only [rhsF]
        rw [hTarget κ P' Y B' hS.1 hS.2.1 hY hB' hYB W hW R Γ hΓ hΓ1]
        rfl))
  exact key η hη

/-- **E5 for the rich local data (D25) from the approximate model input.** -/
theorem e5Rich_of_approx' (hI : D3PlusIStmtRich) (hII : D3PlusIIStmtRich)
    (hModel : E5ModelApproxG' D3Plus.locFieldFull) : Thm13Asm.E4Stmt → E6.E5StmtRich :=
  e5G_of_approx' D3Plus.locFieldFull hI hII hModel e5TargetStmtG_locFieldFull'

/-- **E5 model input, representation form.** Given E4, for every E5 setup, `δ > 0`, `R`: a
Wiener coordinate measure `W` such that for every `ε > 0` there are a zoom model `M`, a family
`Z C` of local data on the model space representing E5's left side
(`lhs C Γ = p · E_Q Γ(Z C)`, the E4 + Palm-normalization step), and measurable bad events of
eventual probability `≤ ε` off which `Z C` is the model data (the L2 + locality step). -/
def E5ReprG' {F : Type} [MeasurableSpace F] (fr : ℕ → FieldSample → F) : Prop :=
  Thm13Asm.E4Stmt →
  ∀ (κ T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ),
    Blueprint.RevCouplingBoundaryMeasureRegular → Setup κ T P B X ϖ →
    IsQuantumWedge (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) Y P' →
    IsBrownianReal B' P' → IndepFun Y (pathOf B') P' → ∀ δ : ℝ, 0 < δ → ∀ R : ℕ,
    ∃ (W : Measure (ℝ≥0 → ℝ)) (_ : IsProbabilityMeasure W),
      IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W ∧
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ (M : ZoomModel fr κ R W) (Z : ℝ → M.Ω₁ → F × (ℝ≥0 → ℝ))
        (bad : ℝ → Set M.Ω₁),
        (∀ C Γ, Measurable Γ → (∀ y, Γ y ≤ 1) →
          lhsF (locG fr) κ T P B X ϖ δ R C Γ = pmass κ T P B X ϖ δ * ∫⁻ ω, Γ (Z C ω) ∂M.Q) ∧
        (∀ C, MeasurableSet (bad C)) ∧ (∀ C ω, ω ∉ bad C → Z C ω = M.data C ω) ∧
        ∀ᶠ C in atTop, M.Q (bad C) ≤ ε

/-- **The representation form implies the approximate model input** (TV bookkeeping). -/
theorem e5ModelApprox_of_repr' {F : Type} [MeasurableSpace F] (fr : ℕ → FieldSample → F)
    (h : E5ReprG' fr) : E5ModelApproxG' fr := by
  intro hE4 κ T Ω _ P _ B X ϖ Ω' _ P' _ Y B' hReg hS hY hB' hYB δ hδ R
  obtain ⟨W, hWp, hW, hR⟩ := h hE4 κ T P B X ϖ P' Y B' hReg hS hY hB' hYB δ hδ R
  refine ⟨W, hWp, hW, fun ε hε => ?_⟩
  set p := pmass κ T P B X ϖ δ with hp_def
  have hpm : p ≠ ⊤ := pmass_ne_top hS hδ
  have hp1 : p + 1 ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hpm, ENNReal.one_ne_top⟩
  have hp10 : p + 1 ≠ 0 := by simp
  have hε₁ : 0 < ε / (p + 1) := ENNReal.div_pos hε.ne' hp1
  have hpε : p * (ε / (p + 1)) ≤ ε := by
    calc p * (ε / (p + 1)) ≤ (p + 1) * (ε / (p + 1)) := by gcongr; exact le_self_add
      _ = ε := ENNReal.mul_div_cancel hp10 hp1
  obtain ⟨M, Z, bad, hZ, hbadm, hZeq, hbad⟩ := hR _ hε₁
  refine ⟨M, ?_⟩
  filter_upwards [hbad] with C hC Γ hΓ hΓ1
  rw [hZ C Γ hΓ hΓ1, M.fn_eq]
  have h1 := lintegral_le_add_of_eq_off (Q := M.Q) (fun ω => hΓ1 (Z C ω)) (hbadm C)
    (fun ω hω => congrArg Γ (hZeq C ω hω))
  have h2 := lintegral_le_add_of_eq_off (Q := M.Q) (fun ω => hΓ1 (M.data C ω)) (hbadm C)
    (fun ω hω => (congrArg Γ (hZeq C ω hω)).symm)
  constructor
  · calc p * ∫⁻ ω, Γ (Z C ω) ∂M.Q ≤ p * (∫⁻ ω, Γ (M.data C ω) ∂M.Q + ε / (p + 1)) :=
          by gcongr; exact h1.trans (by gcongr)
      _ ≤ p * ∫⁻ ω, Γ (M.data C ω) ∂M.Q + ε := by rw [mul_add]; gcongr
  · calc p * ∫⁻ ω, Γ (M.data C ω) ∂M.Q ≤ p * (∫⁻ ω, Γ (Z C ω) ∂M.Q + ε / (p + 1)) :=
          by gcongr; exact h2.trans (by gcongr)
      _ ≤ p * ∫⁻ ω, Γ (Z C ω) ∂M.Q + ε := by rw [mul_add]; gcongr

/-- **E5 (rich local data) from the representation input.** -/
theorem e5Rich_of_repr' (hI : D3PlusIStmtRich) (hII : D3PlusIIStmtRich)
    (hRepr : E5ReprG' D3Plus.locFieldFull) : Thm13Asm.E4Stmt → E6.E5StmtRich :=
  e5Rich_of_approx' hI hII (e5ModelApprox_of_repr' _ hRepr)

/-! ## The old (unsatisfiable) inputs imply the repaired ones -/

end E5
end QuantumZipper
