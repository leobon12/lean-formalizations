import QuantumZipper.Proofs.Thm18.ZqCWin
import QuantumZipper.Proofs.Thm18.G3ZqO5Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-CORE (3): the core node `G3ZqO6CoreDStmt` from the Palm transfer of the core functional

The Palm side of the core limit is proved here: at every core point `x` the conditional zoom of
the wedge Palm field `h^x` jointly with the window event `W_x` converges
(`ZqC.palm_window_fix`), and the Palm density `ρ` is bounded on the core
(`G3ZqO.rhoNorm_le_core`), so by dominated convergence in `x`

  `∫_T ρ(x) E[1_{W_x} Γ(zoom_L h^x)] dx → c ∫_T ρ(x) P(W_x) dx`,  `c = E Γ(loc_R(wedge))`.

What remains is the transfer of the two wedge expectations to the Palm side through the wedge
Palm identity (`R18.G3WedgePalmIdStmt`, for any free field `V` satisfying it,
`ZqCPalmFor`):

* `ZqCWinMassStmt`: `E ν_h(T ∩ W) = ∫_T ρ(x) P(W_x) dx` (the window mass, exact);
* `ZqCZoomTransferStmt`: `E Φ_L(h) = ∫_T ρ(x) E[1_{W_x} Γ(zoom_L h^x)] dx + o(1)` as `L → ∞`
  (the zoom functional reads the field outside the unit disc, where the Palm identity says
  nothing, so only the localized version, up to the vanishing bad-scale mass, is available).

`ZqCTop.g3ZqO6CoreDStmt_of_zoomTransfer : ZqCZoomTransferStmt → G3ZqO6CoreDStmt` (the window
mass is proved in `ZqCMass2`, the measurability in `ZqCMeas`).

Sheffield, arXiv:1012.4797, pp. 70–71 (the one-point Palm limit, "as in Proposition 1.6");
Duplantier–Sheffield, arXiv:0808.1560, §3.3 (rooted measure). Own bookkeeping (AGENT_GUIDE cost
rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqC

open G3Z2b2 D3Plus G1Zm G3Zq G3ZqL G3ZqO Factorization

/-- The Palm identity of the wedge boundary measure for the free field `V`
(the body of `R18.G3WedgePalmIdStmt`). -/
def ZqCPalmFor (γ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ) (V : Ω' → FieldSample) : Prop :=
  ∀ a b : ℝ, Icc a b ⊆ Icc (-(1 / 2)) (1 / 2) → (0 : ℝ) ∉ Icc a b →
    ∀ (c : ℕ → ℂ) (r : ℕ → ℝ), (∀ j, c j ∈ Hbar) → (∀ j, 0 < r j) →
      (∀ j, Metric.closedBall (c j) (r j) ∩ Hbar ⊆ Metric.ball (0 : ℂ) 1) →
    ∀ w : ℝ → ℝ, Continuous w → (∀ x, 0 ≤ w x) → (∀ x ∉ Icc a b, w x = 0) →
    ∀ φ : (ℕ → ℝ) → ℝ → ℝ≥0∞, Measurable (Function.uncurry φ) →
      ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (w x) *
          φ (fun j => F2.zU γ X A ω (foldedCircle (c j) (r j))) x
          ∂(qBoundaryMeasure γ (F2.zU γ X A ω)) ∂P' =
        ∫⁻ x, ENNReal.ofReal (w x * PalmNorm.rhoNorm γ (LogSingGood.Lf (γ - 2 / γ)) R18.g3zS x) *
          ∫⁻ ω, φ (fun j => PalmNorm.normAt R18.g3zS
            (ofFun (PalmNorm.shiftFun γ (LogSingGood.Lf (γ - 2 / γ)) R18.g3zS x) + V ω)
            (foldedCircle (c j) (r j))) x ∂P'

/-- Every wedge carries a free field satisfying the Palm identity. -/
theorem exists_palmFor {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type} [MeasurableSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P'] (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ)
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P') :
    ∃ V : Ω' → FieldSample, IsFreeGFFModConstH V P' ∧ ZqCPalmFor γ P' X A V :=
  R18.g3WedgePalmIdStmt_holds γ hγ hγ2 P' X A hX hA hXA

/-- The Palm density as a weight. -/
def rhoP (γ x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (PalmNorm.rhoNorm γ (LogSingGood.Lf (γ - 2 / γ)) R18.g3zS x)

/-- The Palm-side core functional at `x`: `E[1_{W_x} Γ(zoom_L h^x)]`. -/
def palmJ (γ L : ℝ) (R : ℕ) (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞)
    (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (U δ : ℝ) (a : ℝ≥0 → ℝ)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (V : Ω' → FieldSample) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (palmWin γ left U δ x V).indicator 1 ω *
    Γ (g1zLocData R (G3Z2b2.g1zM γ L Ψ left ((G1Zm.palmFieldAt γ x (V ω), a), x))) ∂P'

/-- **Palm transfer of the window mass (open node).** -/
def ZqCWinMassStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 →
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
    IsFreeGFFModConstH X P' → IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' →
    IndepFun X (fun ω t => A t ω) P' →
  ∀ V : Ω' → FieldSample, IsFreeGFFModConstH V P' → ZqCPalmFor γ P' X A V →
  ∀ left : Bool, ∀ U : ℝ, 0 < U → ∀ η : ℝ, 0 < η → η < 1 / 4 → ∀ δ : ℝ, 0 < δ → δ < η / 2 →
    ∫⁻ ω', winCoreD γ left U η δ (wedgeU γ X A ω') ∂P' =
      ∫⁻ x, (coreSet left η).indicator (fun x => rhoP γ x * P' (palmWin γ left U δ x V)) x

/-- **Palm transfer of the core functional up to a vanishing error (open node).** -/
def ZqCZoomTransferStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
    IsFreeGFFModConstH X P' → IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' →
    IndepFun X (fun ω t => A t ω) P' →
  ∀ V : Ω' → FieldSample, IsFreeGFFModConstH V P' → ZqCPalmFor γ P' X A V →
  ∀ a : ℝ≥0 → ℝ, G3ZqGoodPath γ a → ∀ left : Bool,
  ∀ (R : ℕ) (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞), Measurable Γ → (∀ y, Γ y ≤ 1) →
  ∀ U : ℝ, 0 < U → ∀ η : ℝ, 0 < η → η < 1 / 4 → ∀ δ : ℝ, 0 < δ → δ < η / 2 →
    ∀ e : ℝ≥0∞, 0 < e → ∀ᶠ L in atTop,
      ∫⁻ ω', g1PhiD γ L R Γ Ψ left U η δ (wedgeU γ X A ω', a) ∂P' ≤
          (∫⁻ x, (coreSet left η).indicator
            (fun x => rhoP γ x * palmJ γ L R Γ Ψ left U δ a P' V x) x) + e ∧
        ∫⁻ x, (coreSet left η).indicator
            (fun x => rhoP γ x * palmJ γ L R Γ Ψ left U δ a P' V x) x ≤
          ∫⁻ ω', g1PhiD γ L R Γ Ψ left U η δ (wedgeU γ X A ω', a) ∂P' + e

theorem palmJ_le_one (γ L : ℝ) (R : ℕ) {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞}
    (hΓ1 : ∀ y, Γ y ≤ 1) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (U δ : ℝ)
    (a : ℝ≥0 → ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (V : Ω' → FieldSample) (x : ℝ) : palmJ γ L R Γ Ψ left U δ a P' V x ≤ 1 := by
  unfold palmJ
  refine (lintegral_mono fun ω => ?_).trans (le_of_eq (lintegral_one.trans measure_univ))
  exact mul_le_one' (indicator_le (fun _ _ => le_rfl) _) (hΓ1 _)

theorem mem_side_of_core {left : Bool} {η x : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4)
    (hx : x ∈ coreSet left η) : x ∈ g1SideHalf left ∧ |x| ≤ 1 / 2 := by
  cases left
  · simp only [coreSet, Bool.false_eq_true, ite_false, mem_Icc] at hx
    refine ⟨by simp only [g1SideHalf, Bool.false_eq_true, ite_false, mem_Ioi]; linarith, ?_⟩
    rw [abs_of_pos (by linarith)]; linarith
  · simp only [coreSet, ite_true, mem_Icc] at hx
    refine ⟨by simp only [g1SideHalf, ite_true, mem_Iio]; linarith, ?_⟩
    rw [abs_of_neg (by linarith)]; linarith

/-- **The Palm side: dominated convergence over the core.** -/
theorem tendsto_palm_side {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}
    (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ} (ha : G3ZqGoodPath γ a) {left : Bool}
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (V : Ω' → FieldSample) (hV : IsFreeGFFModConstH V P')
    {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    (Y'' : Ω'' → FieldSample) (hW : IsQuantumWedge γ γ Y'' P'') (R : ℕ)
    (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞) (hΓ : Measurable Γ) (hΓ1 : ∀ y, Γ y ≤ 1)
    (U : ℝ) {η δ : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) (hδ : 0 < δ) (hδη : δ < η / 2)
    (hJm : ∀ L, AEMeasurable (palmJ γ L R Γ Ψ left U δ a P' V)
      (volume.restrict (coreSet left η))) :
    Tendsto (fun L => ∫⁻ x, (coreSet left η).indicator
        (fun x => rhoP γ x * palmJ γ L R Γ Ψ left U δ a P' V x) x) atTop
      (𝓝 (∫⁻ x, (coreSet left η).indicator (fun x => rhoP γ x *
        (P' (palmWin γ left U δ x V) * ∫⁻ ω, Γ (locFieldFull R (Y'' ω)) ∂P'')) x)) := by
  have hT := measurableSet_coreSet left η
  obtain ⟨K, hK⟩ := rhoNorm_le_core γ hγ left hη hη4
  set c := ∫⁻ ω, Γ (locFieldFull R (Y'' ω)) ∂P'' with hc
  have hc1 : c ≤ 1 := by
    calc c ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂P'' := lintegral_mono fun ω => hΓ1 _
      _ = 1 := by simp
  simp_rw [lintegral_indicator hT]
  refine tendsto_lintegral_filter_of_dominated_convergence' (fun _ => ENNReal.ofReal K)
    (Eventually.of_forall fun L => ?_) (Eventually.of_forall fun L => ?_) ?_ ?_
  · exact ((E1.measurable_rhoNorm (((Real.measurable_log.comp measurable_norm).neg).const_mul _ :
      Measurable (LogSingGood.Lf (γ - 2 / γ))) R18.g3zS).ennreal_ofReal
      ).aemeasurable.mul (hJm L)
  · refine (ae_restrict_iff' hT).2 (Eventually.of_forall fun x hx => ?_)
    calc rhoP γ x * palmJ γ L R Γ Ψ left U δ a P' V x ≤ rhoP γ x * 1 :=
          mul_le_mul' le_rfl (palmJ_le_one γ L R hΓ1 Ψ left U δ a P' V x)
      _ ≤ ENNReal.ofReal K := by rw [mul_one]; exact ENNReal.ofReal_le_ofReal (hK x hx)
  · rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    cases left
    · simp [coreSet]
    · simp [coreSet]
  · refine (ae_restrict_iff' hT).2 (Eventually.of_forall fun x hx => ?_)
    obtain ⟨hxs, hx1⟩ := mem_side_of_core hη hη4 hx
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr ENNReal.ofReal_ne_top)
    have hfin : P' (palmWin γ left U δ x V) * c ≠ ⊤ :=
      ENNReal.mul_ne_top (measure_ne_top _ _) (ne_top_of_le_ne_top ENNReal.one_ne_top hc1)
    refine (ENNReal.tendsto_nhds hfin).2 fun e he => ?_
    filter_upwards [palm_window_fix hγ hγ2 hsel ha hxs hx1 hδ (by linarith) P' V hV P'' Y'' hW R
      Γ hΓ hΓ1 U he] with L hL
    exact ⟨tsub_le_iff_right.2 hL.2, hL.1⟩

end ZqC
end Thm18Asm
end QuantumZipper
