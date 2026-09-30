import QuantumZipper.Proofs.Thm18.G3ZqO1Eps
import QuantumZipper.Proofs.Thm18.G1ZmWin
import QuantumZipper.Proofs.Thm18.G3FidProxy
import QuantumZipper.Proofs.Thm18.G4CMeas4Good
import QuantumZipper.Proofs.Thm18.G4WedgeRightInf
import QuantumZipper.Proofs.Thm18.G1RCProfile
import QuantumZipper.Proofs.Wire4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-G1 (2): truncating the Palm window to `η ≤ |x| ≤ 1/4`

The Palm identity of the wedge boundary measure (`R18.G3WedgePalmIdStmt`) reads only windows
`[a, b] ⊆ [−1/2, 1/2]` avoiding the root. We cut the Palm window `W` (points of the side
half-line within quantum length `U` of the root) to the core `T = {η ≤ |x| ≤ 1/4}`:

* `measure_winDiff_le`: `ν(W \ T) ≤ min(U, ν(0, η)) + U · 1[ν[0, 1/4] ≤ U]` (deterministic: a
  window point beyond `1/4` forces `ν[0, 1/4] ≤ U`);
* `g1PhiM_le_phiT_add`, `g1PhiT_le_g1PhiM`: the full functional against the truncated one
  `g1PhiT` (integrand cut to `T`);
* `ae_wedgeU_bdry`: a.s. the boundary measure of the unscaled wedge is atomless, positive on
  open intervals and of infinite mass on both half-lines (from the canonical wedge by the
  rescaling covariance `GoodTransforms.qBoundaryMeasure_rescale`), so the window has mass
  exactly `U` (`G1Zm.measure_g1Win_eq`);
* the core node **`G3ZqO2CoreStmt`**: for every `U > 0` and `0 < η < 1/4`, for a.e. path, the
  expectation of the truncated functional is eventually close to `c · E ν(W ∩ T)`, `c` the wedge
  value. This is the part of the one-point Palm limit inside the range of the Palm identity.

Sheffield, arXiv:1012.4797, pp. 70–71. Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqO

open G3Z2b2 D3Plus G1Zm G3Zq G3ZqL Factorization

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- The core of the side half-line: `η ≤ |x| ≤ 1/4`. -/
def coreSet (left : Bool) (η : ℝ) : Set ℝ :=
  if left then Icc (-(1 / 4)) (-η) else Icc η (1 / 4)

/-- The part of the side half-line near the root: `0 < |x| < η`. -/
def nearSet (left : Bool) (η : ℝ) : Set ℝ := if left then Ioo (-η) 0 else Ioo 0 η

/-- The side point at distance `1/4`. -/
def quarterPt (left : Bool) : ℝ := if left then -(1 / 4) else 1 / 4

/-- The Palm window of `y`. -/
def winSet (γ : ℝ) (left : Bool) (U : ℝ) (y : FieldSample) : Set ℝ :=
  {x | x ∈ g1SideHalf left ∧ bdryM γ y (g1SideSeg left x) ≤ ENNReal.ofReal U}

theorem measurableSet_coreSet (left : Bool) (η : ℝ) : MeasurableSet (coreSet left η) := by
  cases left <;> simp [coreSet, measurableSet_Icc]

theorem measurableSet_nearSet (left : Bool) (η : ℝ) : MeasurableSet (nearSet left η) := by
  cases left <;> simp [nearSet, measurableSet_Ioo]

/-- **The truncated Palm-window functional** (integrand cut to the core). -/
def g1PhiT (γ L : ℝ) (R : ℕ) (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞)
    (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (U η : ℝ) (p : FieldSample × (ℝ≥0 → ℝ)) :
    ℝ≥0∞ :=
  ∫⁻ x, (coreSet left η).indicator (fun x => g1IntM γ L R Γ Ψ left U (p, x)) x ∂(bdryM γ p.1)

/-- The boundary mass of the window inside the core. -/
def winCore (γ : ℝ) (left : Bool) (U η : ℝ) (y : FieldSample) : ℝ≥0∞ :=
  bdryM γ y (winSet γ left U y ∩ coreSet left η)

/-- The truncation error bound. -/
def truncErr (left : Bool) (U η : ℝ) (μ : Measure ℝ) : ℝ≥0∞ :=
  min (ENNReal.ofReal U) (μ (nearSet left η)) +
    (if μ (g1SideSeg left (quarterPt left)) ≤ ENNReal.ofReal U then ENNReal.ofReal U else 0)

theorem measurable_truncErr (left : Bool) (U η : ℝ) : Measurable (truncErr left U η) := by
  have hseg : MeasurableSet (g1SideSeg left (quarterPt left)) := by
    cases left <;> simp [g1SideSeg, measurableSet_Icc]
  exact (measurable_const.min (Measure.measurable_coe (measurableSet_nearSet left η))).add
    (Measurable.ite (measurableSet_le (Measure.measurable_coe hseg) measurable_const)
      measurable_const measurable_const)

/-- A window point outside the core is near the root or beyond `1/4`. -/
theorem mem_near_or_far {left : Bool} {η : ℝ} {x : ℝ} (hx : x ∈ g1SideHalf left)
    (hT : x ∉ coreSet left η) :
    x ∈ nearSet left η ∨ g1SideSeg left (quarterPt left) ⊆ g1SideSeg left x := by
  cases left
  · simp only [g1SideHalf, Bool.false_eq_true, ite_false, mem_Ioi] at hx
    simp only [coreSet, Bool.false_eq_true, ite_false, mem_Icc, not_and_or, not_le] at hT
    rcases hT with h | h
    · left; simp [nearSet, hx, h]
    · right
      simp only [g1SideSeg, quarterPt, Bool.false_eq_true, ite_false]
      exact Icc_subset_Icc_right h.le
  · simp only [g1SideHalf, ite_true, mem_Iio] at hx
    simp only [coreSet, ite_true, mem_Icc, not_and_or, not_le] at hT
    rcases hT with h | h
    · right
      simp only [g1SideSeg, quarterPt, ite_true]
      exact Icc_subset_Icc_left h.le
    · left; simp [nearSet, hx, h]

/-- **The window outside the core has small mass.** -/
theorem measure_winDiff_le (γ : ℝ) (left : Bool) (U η : ℝ) (y : FieldSample) :
    bdryM γ y (winSet γ left U y \ coreSet left η) ≤ truncErr left U η (bdryM γ y) := by
  set μ := bdryM γ y
  set W := winSet γ left U y
  have hW : μ W ≤ ENNReal.ofReal U := measure_g1Win_le μ left _
  have hsub : W \ coreSet left η ⊆ (W ∩ nearSet left η) ∪
      (W ∩ {x | g1SideSeg left (quarterPt left) ⊆ g1SideSeg left x}) := by
    intro x hx
    rcases mem_near_or_far hx.1.1 hx.2 with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨hx.1, h⟩
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add ?_ ?_))
  · exact le_min ((measure_mono inter_subset_left).trans hW) (measure_mono inter_subset_right)
  · by_cases hq : μ (g1SideSeg left (quarterPt left)) ≤ ENNReal.ofReal U
    · rw [if_pos hq]
      exact (measure_mono inter_subset_left).trans hW
    · rw [if_neg hq]
      have he : W ∩ {x | g1SideSeg left (quarterPt left) ⊆ g1SideSeg left x} = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
        intro hxW hs
        exact hq ((measure_mono hs).trans hxW.2)
      rw [he, measure_empty]

theorem g1PhiT_le_g1PhiM {γ L : ℝ} {R : ℕ} {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞}
    {left : Bool} {U η : ℝ} (p : FieldSample × (ℝ≥0 → ℝ)) :
    g1PhiT γ L R Γ Ψ left U η p ≤ g1PhiM γ L R Γ Ψ left U p :=
  lintegral_mono fun _ => indicator_le_self _ _ _

/-- **The full functional is the truncated one plus at most the mass of the window outside
the core.** -/
theorem g1PhiM_le_phiT_add {γ : ℝ} (hsel : G1PsiSel γ Ψ) (L : ℝ) (R : ℕ)
    {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞} (hΓ : Measurable Γ) (hΓ1 : ∀ y, Γ y ≤ 1)
    (left : Bool) (U η : ℝ) (p : FieldSample × (ℝ≥0 → ℝ)) :
    g1PhiM γ L R Γ Ψ left U p ≤ g1PhiT γ L R Γ Ψ left U η p +
      bdryM γ p.1 (winSet γ left U p.1 \ coreSet left η) := by
  classical
  have hm : Measurable fun x => (coreSet left η).indicator
      (fun x => g1IntM γ L R Γ Ψ left U (p, x)) x :=
    ((measurable_g1IntM hsel L R hΓ left U).comp (measurable_const.prodMk measurable_id)).indicator
      (measurableSet_coreSet left η)
  have hpt : ∀ x, g1IntM γ L R Γ Ψ left U (p, x) ≤ (coreSet left η).indicator
      (fun x => g1IntM γ L R Γ Ψ left U (p, x)) x +
      (winSet γ left U p.1 \ coreSet left η).indicator 1 x := by
    intro x
    by_cases hT : x ∈ coreSet left η
    · rw [indicator_of_mem hT]; exact le_self_add
    · rw [indicator_of_notMem hT, zero_add]
      unfold g1IntM
      split_ifs with h
      · rw [indicator_of_mem (show x ∈ winSet γ left U p.1 \ coreSet left η from ⟨h, hT⟩)]
        exact hΓ1 _
      · exact bot_le
  calc g1PhiM γ L R Γ Ψ left U p
      ≤ ∫⁻ x, ((coreSet left η).indicator (fun x => g1IntM γ L R Γ Ψ left U (p, x)) x +
          (winSet γ left U p.1 \ coreSet left η).indicator 1 x) ∂(bdryM γ p.1) :=
        lintegral_mono hpt
    _ = g1PhiT γ L R Γ Ψ left U η p + ∫⁻ x, (winSet γ left U p.1 \ coreSet left η).indicator 1 x
          ∂(bdryM γ p.1) := lintegral_add_left hm _
    _ ≤ _ := by
        refine add_le_add le_rfl ((lintegral_indicator_le _ _).trans ?_)
        simp

/-- **Boundary facts of the unscaled wedge**, a.s.: atomless, positive on open intervals, of
infinite mass on both closed half-lines. -/
theorem ae_wedgeU_bdry {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P') :
    ∀ᵐ ω' ∂P', (∀ t : ℝ, bdryM γ (wedgeU γ X A ω') {t} = 0) ∧
      (∀ u v : ℝ, u < v → 0 < bdryM γ (wedgeU γ X A ω') (Ioo u v)) ∧
      bdryM γ (wedgeU γ X A ω') (Ici 0) = ⊤ ∧ bdryM γ (wedgeU γ X A ω') (Iic 0) = ⊤ := by
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  have hrep : IsQuantumWedge γ (γ - 2 / γ) (wedgeRep γ X A) P' :=
    ⟨hαQ, Ω', inferInstance, P', X, A, inferInstance, hX, hA, hXA, rfl⟩
  have hm := WedgeMeasND.aemeasurable_dataFull_of_isQuantumWedge
    (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hαQ) (WedgeInf.wedgeInfiniteTotal hγ hγ2 hαQ)
    hγ hγ2 hrep
  have hfin := WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hαQ
  have hinf := WedgeInf.wedgeInfiniteTotal hγ hγ2 hαQ
  have hat := WedgeBdry.ae_atomless_pos_of_isQuantumWedge hγ hγ2 P' (wedgeRep γ X A) hrep hm
    (fun Ω'' _ P'' X' A' hP'' hX' hA' hI' => by
      have := hP''
      exact ⟨(WedgeCan4.ae_wedge_canonical_spec_of_inputs hfin hinf hγ hγ2 hαQ hX' hA' hI').mono
          fun _ h => h.1,
        WedgeMeas.aemeasurable_wedgeRefData hX' hA'
          (LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hαQ Ω'' _ P'' X' A' hP'' hX' hA' hI') H⟩)
  filter_upwards [hat, wedgeRightInfStmt_holds γ P' (wedgeRep γ X A) hγ hγ2 hrep,
    Wire4.wedgeLeftInfStmt γ P' (wedgeRep γ X A) hγ hγ2 hrep,
    LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hαQ Ω' _ P' X A inferInstance hX hA hXA,
    G1RC.ae_scale_pos hγ hγ2 hX hA hXA] with ω' ⟨hatom, hpos⟩ hRinf hLinf hg hb
  have hgU : IsLQGGood γ (wedgeU γ X A ω') := hg
  set b := scaleParam γ (wedgeU γ X A ω') with hbdef
  have hb' : 0 < b := hb
  have hB : bdryM γ (wedgeU γ X A ω') = qBoundaryMeasure γ (wedgeU γ X A ω') :=
    bdryM_of_bCert γ (G4Core.bCert_of_isLQGGood hgU)
  have e : wedgeRep γ X A ω' = rescale (wedgeU γ X A ω') (Qc γ) b := rfl
  have hmap : qBoundaryMeasure γ (wedgeRep γ X A ω') =
      (qBoundaryMeasure γ (wedgeU γ X A ω')).map fun u => u / b := by
    rw [e]; exact GoodTransforms.qBoundaryMeasure_rescale hgU hγ hb'
  have htr : ∀ S T : Set ℝ, MeasurableSet S → (fun u : ℝ => u / b) ⁻¹' S = T →
      bdryM γ (wedgeU γ X A ω') T = qBoundaryMeasure γ (wedgeRep γ X A ω') S := by
    intro S T hS hST
    rw [hB, hmap, Measure.map_apply (by fun_prop : Measurable fun u : ℝ => u / b) hS, hST]
  refine ⟨fun t => ?_, fun u v huv => ?_, ?_, ?_⟩
  · rw [htr {t / b} {t} (measurableSet_singleton _) (by
      ext u; simp [div_left_inj' hb'.ne'])]
    exact hatom _
  · rw [htr (Ioo (u / b) (v / b)) (Ioo u v) measurableSet_Ioo (by
      ext x; simp [div_lt_div_iff_of_pos_right hb'])]
    exact hpos _ _ ((div_lt_div_iff_of_pos_right hb').2 huv)
  · rw [htr (Ici 0) (Ici 0) measurableSet_Ici (by
      ext x; simp [le_div_iff₀ hb'])]
    exact hRinf
  · rw [htr (Iic 0) (Iic 0) measurableSet_Iic (by
      ext x; simp [div_le_iff₀ hb'])]
    exact hLinf

/-- On the a.s. event of `ae_wedgeU_bdry`, the window has mass exactly `U` and the quarter
segment has positive mass. -/
theorem window_facts {γ : ℝ} {y : FieldSample} (hat : ∀ t : ℝ, bdryM γ y {t} = 0)
    (hpos : ∀ u v : ℝ, u < v → 0 < bdryM γ y (Ioo u v))
    (hR : bdryM γ y (Ici 0) = ⊤) (hL : bdryM γ y (Iic 0) = ⊤) (left : Bool) {U : ℝ}
    (_hU : 0 ≤ U) :
    bdryM γ y (winSet γ left U y) = ENNReal.ofReal U ∧
      0 < bdryM γ y (g1SideSeg left (quarterPt left)) := by
  set μ := bdryM γ y
  have hfin : ∀ x, μ (g1SideSeg left x) ≠ ⊤ := by
    intro x; cases left <;> simp only [g1SideSeg, Bool.false_eq_true, ite_false, ite_true] <;>
      exact R18.bdryM_Icc_ne_top γ y _ _
  have hinf : μ (g1SideHalf left) = ⊤ := by
    cases left
    · simp only [g1SideHalf, Bool.false_eq_true, ite_false]
      have h1 : μ (Ici 0) ≤ μ {0} + μ (Ioi 0) := by
        rw [← Ioi_insert, insert_eq]; exact measure_union_le _ _
      rw [hR, hat, zero_add] at h1
      exact top_le_iff.1 h1
    · simp only [g1SideHalf, ite_true]
      have h1 : μ (Iic 0) ≤ μ {0} + μ (Iio 0) := by
        rw [← Iio_insert, insert_eq]; exact measure_union_le _ _
      rw [hL, hat, zero_add] at h1
      exact top_le_iff.1 h1
  refine ⟨measure_g1Win_eq μ left ENNReal.ofReal_ne_top hat hfin hinf, ?_⟩
  cases left
  · simp only [g1SideSeg, quarterPt, Bool.false_eq_true, ite_false]
    exact (hpos 0 (1 / 4) (by norm_num)).trans_le (measure_mono Ioo_subset_Icc_self)
  · simp only [g1SideSeg, quarterPt, ite_true]
    exact (hpos (-(1 / 4)) 0 (by norm_num)).trans_le (measure_mono Ioo_subset_Icc_self)

/-- **The core node**: the one-point fixed-path Palm limit of the unscaled wedge on the core
`η ≤ |x| ≤ 1/4` of the window (inside the range of the Palm identity `G3WedgePalmIdStmt`). -/
def G3ZqO2CoreStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
    IsFreeGFFModConstH X P' → IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' →
    IndepFun X (fun ω t => A t ω) P' →
  ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    (Y'' : Ω'' → FieldSample), IsQuantumWedge γ γ Y'' P'' →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P → ∀ left : Bool,
  ∀ (R : ℕ) (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞), Measurable Γ → (∀ y, Γ y ≤ 1) →
  ∀ U : ℝ, 0 < U → ∀ η : ℝ, 0 < η → η < 1 / 4 →
  ∀ᵐ a ∂(P.map (pathOf B)), Continuous a → IsSimpleChord (pathTrace (γ ^ 2) a) →
    ∀ e : ℝ≥0∞, 0 < e → ∀ᶠ L in atTop,
      ∫⁻ ω', g1PhiT γ L R Γ Ψ left U η (wedgeU γ X A ω', a) ∂P' ≤
          (∫⁻ ω'', Γ (locFieldFull R (Y'' ω'')) ∂P'') *
            ∫⁻ ω', winCore γ left U η (wedgeU γ X A ω') ∂P' + e ∧
        (∫⁻ ω'', Γ (locFieldFull R (Y'' ω'')) ∂P'') *
            ∫⁻ ω', winCore γ left U η (wedgeU γ X A ω') ∂P' ≤
          ∫⁻ ω', g1PhiT γ L R Γ Ψ left U η (wedgeU γ X A ω', a) ∂P' + e

end G3ZqO
end Thm18Asm
end QuantumZipper
