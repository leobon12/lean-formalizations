import QuantumZipper.Proofs.Thm18.ZqCMass

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-CORE (5): the window-mass node `ZqCWinMassStmt`

`E ν_h(T ∩ W) = ∫_T ρ(x) P(W_x) dx` for the unscaled wedge `h` and the wedge Palm field `h^x`
of any free field `V` satisfying the Palm identity (`ZqCPalmFor`), `T` the core, `W` the shifted
window and `W_x` its local form at `x` (`palmWin`).

Proof: the Palm identity on the core with the trapezoid weight (`palmFor_core`, as
`G3ZqO.wedge_palm_core`) applied to the functional
`φ(v, x) = 1[locLen(recF v)[segment of x] ≤ U]` of the circle averages inside the unit disc
(`ZqCMass`). On the wedge side a.s. the wedge is good, so `bdryM = qBoundaryMeasure` and the
window condition is `φ` (`bdryM_seg_eq_winLen`, `winLen_eq_locLen`, `locLen_recF`); on the Palm
side `φ(h^x) = 1_{W_x}` for every sample.

Duplantier–Sheffield, arXiv:0808.1560, §3.3 (rooted measure), through `R18.G3WedgePalmIdStmt`.
Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqC

open G3Z2b2 D3Plus G1Zm G3Zq G3ZqL G3ZqO Factorization G2PalmLoc

/-- **The Palm identity on the core for a free field satisfying it.** -/
theorem palmFor_core {γ : ℝ} {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ} {V : Ω' → FieldSample}
    (hPI : ZqCPalmFor γ P' X A V) (left : Bool) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4)
    (c : ℕ → ℂ) (r : ℕ → ℝ) (hc : ∀ j, c j ∈ Hbar) (hr : ∀ j, 0 < r j)
    (hin : ∀ j, Metric.closedBall (c j) (r j) ∩ Hbar ⊆ Metric.ball (0 : ℂ) 1)
    (φ : (ℕ → ℝ) → ℝ → ℝ≥0∞) (hφ : Measurable (Function.uncurry φ)) :
    ∫⁻ ω, ∫⁻ x, (coreSet left η).indicator
        (fun x => φ (fun j => F2.zU γ X A ω (foldedCircle (c j) (r j))) x) x
        ∂(qBoundaryMeasure γ (F2.zU γ X A ω)) ∂P' =
      ∫⁻ x, (coreSet left η).indicator (fun x =>
        ENNReal.ofReal (PalmNorm.rhoNorm γ (LogSingGood.Lf (γ - 2 / γ)) R18.g3zS x) *
        ∫⁻ ω, φ (fun j => PalmNorm.normAt R18.g3zS
          (ofFun (PalmNorm.shiftFun γ (LogSingGood.Lf (γ - 2 / γ)) R18.g3zS x) + V ω)
          (foldedCircle (c j) (r j))) x ∂P') x := by
  obtain ⟨u, v, e, hsub, h0⟩ := coreSet_margin left hη hη4
  rw [e]
  have hm : 0 < η / 2 := by positivity
  set φ' : (ℕ → ℝ) → ℝ → ℝ≥0∞ := fun d x => (Icc u v).indicator (fun x => φ d x) x with hφ'
  have hφ'm : Measurable (Function.uncurry φ') := by
    have : Function.uncurry φ' = (Prod.snd ⁻¹' Icc u v).indicator (Function.uncurry φ) := by
      funext q
      simp only [Function.uncurry, hφ', indicator, mem_preimage]
    rw [this]
    exact hφ.indicator (measurable_snd measurableSet_Icc)
  have h := hPI (u - η / 2) (v + η / 2) hsub h0 c r hc hr hin (trapW u v (η / 2))
    (continuous_trapW u v (η / 2)) (trapW_nonneg u v (η / 2)) (fun x hx => trapW_eq_zero hm hx)
    φ' hφ'm
  convert h using 1
  · refine lintegral_congr fun ω => lintegral_congr fun x => ?_
    by_cases hx : x ∈ Icc u v
    · simp only [hφ', indicator_of_mem hx, trapW_eq_one hm hx, ENNReal.ofReal_one, one_mul]
    · simp only [hφ', indicator_of_notMem hx, mul_zero]
  · refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ Icc u v
    · simp only [hφ', indicator_of_mem hx, trapW_eq_one hm hx, one_mul]
    · simp only [hφ', indicator_of_notMem hx, lintegral_zero, mul_zero]

theorem measurable_segLo (left : Bool) (δ : ℝ) : Measurable (segLo left δ) := by
  cases left
  · have e : segLo false δ = fun _ => 0 := by funext x; simp [segLo]
    rw [e]; exact measurable_const
  · have e : segLo true δ = fun x => x + δ := by funext x; simp [segLo]
    rw [e]; exact measurable_id.add_const δ

theorem measurable_segHi (left : Bool) (δ : ℝ) : Measurable (segHi left δ) := by
  cases left
  · have e : segHi false δ = fun x => x - δ := by funext x; simp [segHi]
    rw [e]; exact measurable_id.sub_const δ
  · have e : segHi true δ = fun _ => 0 := by funext x; simp [segHi]
    rw [e]; exact measurable_const

theorem seg_bounds {left : Bool} {η δ x : ℝ} (hη4 : η < 1 / 4) (hδ : 0 < δ) (hδη : δ < η / 2)
    (hx : x ∈ coreSet left η) :
    -(3 / 4) ≤ segLo left δ x - δ / 4 ∧ segHi left δ x + δ / 4 ≤ 3 / 4 := by
  cases left
  · simp only [coreSet, Bool.false_eq_true, ite_false, mem_Icc] at hx
    simp only [segLo, segHi, Bool.false_eq_true, ite_false]
    constructor <;> linarith
  · simp only [coreSet, ite_true, mem_Icc] at hx
    simp only [segLo, segHi, ite_true]
    constructor <;> linarith

/-- The window condition as a set of (circle data, point). -/
def winS (γ : ℝ) (left : Bool) (U δ : ℝ) : Set ((ℕ → ℝ) × ℝ) :=
  {q | locLen γ (recF q.1) (segLo left δ q.2) (segHi left δ q.2) (δ / 4) ≤ ENNReal.ofReal U}

/-- The window functional of the circle data. -/
def winPhi (γ : ℝ) (left : Bool) (U δ : ℝ) (v : ℕ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  (winS γ left U δ).indicator 1 (v, x)

theorem measurable_segTriple (left : Bool) (δ : ℝ) :
    Measurable fun q : (ℕ → ℝ) × ℝ => (q.1, segLo left δ q.2, segHi left δ q.2) :=
  measurable_fst.prodMk (((measurable_segLo left δ).comp measurable_snd).prodMk
    ((measurable_segHi left δ).comp measurable_snd))

theorem measurable_winLenC (γ : ℝ) (left : Bool) (δ : ℝ) :
    Measurable fun q : (ℕ → ℝ) × ℝ =>
      locLen γ (recF q.1) (segLo left δ q.2) (segHi left δ q.2) (δ / 4) := by
  have h := (measurable_locLen_recF γ (δ / 4)).comp (measurable_segTriple left δ)
  simp only [Function.comp_def] at h
  exact h

theorem measurableSet_winS (γ : ℝ) (left : Bool) (U δ : ℝ) :
    MeasurableSet (winS γ left U δ) :=
  measurableSet_le (measurable_winLenC γ left δ) measurable_const

theorem measurable_winPhi (γ : ℝ) (left : Bool) (U δ : ℝ) :
    Measurable (Function.uncurry (winPhi γ left U δ)) := by
  have : Function.uncurry (winPhi γ left U δ) = (winS γ left U δ).indicator 1 := by
    funext q; rfl
  rw [this]; exact measurable_one.indicator (measurableSet_winS γ left U δ)

/-- **`ZqCWinMassStmt` holds.** -/
theorem zqCWinMassStmt_holds : ZqCWinMassStmt := by
  intro γ hγ hγ2 Ω' _ P' _ X A hX hA hXA V hV hPF left U hU η hη hη4 δ hδ hδη
  classical
  have hw : 0 < δ / 4 := by positivity
  have hcore := palmFor_core hPF left hη hη4 cJ rJ cJ_mem rJ_pos cJ_ball (winPhi γ left U δ)
    (measurable_winPhi γ left U δ)
  have hkey : ∀ x ∈ coreSet left η, ∀ y : FieldSample,
      (vOf y, x) ∈ winS γ left U δ ↔ winLen γ left δ x y ≤ ENNReal.ofReal U := by
    intro x hx y
    obtain ⟨b1, b2⟩ := seg_bounds hη4 hδ hδη hx
    show locLen γ (recF (vOf y)) _ _ (δ / 4) ≤ _ ↔ _
    rw [locLen_recF γ y hw b1 b2, winLen_eq_locLen γ left hδ]
  -- the wedge side
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  have hL : ∫⁻ ω', winCoreD γ left U η δ (wedgeU γ X A ω') ∂P' =
      ∫⁻ ω, ∫⁻ x, (coreSet left η).indicator
        (fun x => winPhi γ left U δ (fun j => F2.zU γ X A ω (foldedCircle (cJ j) (rJ j))) x) x
        ∂(qBoundaryMeasure γ (F2.zU γ X A ω)) ∂P' := by
    refine lintegral_congr_ae ?_
    filter_upwards [LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hαQ Ω' _ P' X A inferInstance hX hA
      hXA] with ω hg
    have hgU : IsLQGGood γ (wedgeU γ X A ω) := hg
    set y := wedgeU γ X A ω with hy
    have hB : bdryM γ y = qBoundaryMeasure γ y := by
      rw [bdryM, if_pos (G4Core.bCert_of_isLQGGood hgU)]
    have hset : winD γ left U δ y ∩ coreSet left η = coreSet left η ∩ {x | (vOf y, x) ∈ winS γ left U δ} := by
      ext x
      constructor
      · rintro ⟨⟨-, hxU⟩, hxc⟩
        refine ⟨hxc, (hkey x hxc y).2 ?_⟩
        rw [← bdryM_seg_eq_winLen hgU left hδ]
        exact hxU
      · rintro ⟨hxc, hxS⟩
        refine ⟨⟨(mem_side_of_core hη hη4 hxc).1, ?_⟩, hxc⟩
        rw [bdryM_seg_eq_winLen hgU left hδ]
        exact (hkey x hxc y).1 hxS
    have hmeas : MeasurableSet (coreSet left η ∩ {x | (vOf y, x) ∈ winS γ left U δ}) :=
      (measurableSet_coreSet left η).inter (measurable_prodMk_left (measurableSet_winS γ left U δ))
    show bdryM γ y (winD γ left U δ y ∩ coreSet left η) = _
    rw [hB, hset, ← lintegral_indicator_one hmeas]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ coreSet left η
    · rw [indicator_of_mem hx]
      by_cases hS : (vOf y, x) ∈ winS γ left U δ
      · rw [indicator_of_mem (show x ∈ coreSet left η ∩ {x | (vOf y, x) ∈ winS γ left U δ} from ⟨hx, hS⟩)]
        show (1 : ℝ≥0∞) = (winS γ left U δ).indicator 1 (vOf y, x)
        rw [indicator_of_mem hS]; rfl
      · rw [indicator_of_notMem (fun h => hS h.2)]
        show (0 : ℝ≥0∞) = (winS γ left U δ).indicator 1 (vOf y, x)
        rw [indicator_of_notMem hS]
    · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx h.1)]
  -- the Palm side
  have hR : ∀ x ∈ coreSet left η, ∫⁻ ω, winPhi γ left U δ (fun j => PalmNorm.normAt R18.g3zS
      (ofFun (PalmNorm.shiftFun γ (LogSingGood.Lf (γ - 2 / γ)) R18.g3zS x) + V ω)
      (foldedCircle (cJ j) (rJ j))) x ∂P' = P' (palmWin γ left U δ x V) := by
    intro x hx
    obtain ⟨B, hB, hWB⟩ := exists_gauss_preimage_winLen V γ left (δ := δ) (x := x)
      (by
        have := (mem_side_of_core hη hη4 hx).2
        linarith) (ENNReal.ofReal U)
    have hWm : MeasurableSet (palmWin γ left U δ x V) := by
      show MeasurableSet {ω | winLen γ left δ x (G1Zm.palmFieldAt γ x (V ω)) ≤ ENNReal.ofReal U}
      rw [hWB]
      exact (WedgeTK.measurable_gaussFam_pi hV _) hB
    rw [← lintegral_indicator_one hWm]
    refine lintegral_congr fun ω => ?_
    have hiff := hkey x hx (G1Zm.palmFieldAt γ x (V ω))
    by_cases hω : ω ∈ palmWin γ left U δ x V
    · rw [indicator_of_mem hω]
      show (winS γ left U δ).indicator 1 (vOf (G1Zm.palmFieldAt γ x (V ω)), x) = _
      rw [indicator_of_mem (hiff.2 hω)]; rfl
    · rw [indicator_of_notMem hω]
      show (winS γ left U δ).indicator 1 (vOf (G1Zm.palmFieldAt γ x (V ω)), x) = _
      rw [indicator_of_notMem (fun h => hω (hiff.1 h))]
  rw [hL, hcore]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ coreSet left η
  · rw [indicator_of_mem hx, indicator_of_mem hx, hR x hx]
    rfl
  · rw [indicator_of_notMem hx, indicator_of_notMem hx]

end ZqC
end Thm18Asm
end QuantumZipper
