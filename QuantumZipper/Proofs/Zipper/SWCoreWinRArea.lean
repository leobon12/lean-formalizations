import QuantumZipper.Proofs.Zipper.SWCoreWinR
import QuantumZipper.Proofs.Zipper.AreaWinDense
import QuantumZipper.Proofs.Zipper.AreaWinWedge

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-CORE (derivation 3, task SWC-W0, area half): `E6.FreeWindowStmt` and `E6.WedgeWindowStmt`
# from the `R`-normalized area window split

Task SW-CONSOLIDATE (`handoff/SW-CORE.md` §4). Area analogue of `SWCoreWinR.lean`: for one `N` and
one test function `φ` (compact support in `ℍ`), pick `R ∈ ℕ`, `R ≥ 2`, with `tsupport φ ⊆
B(0,R−1)`, apply `SWCore.SWWindowSplitStmtR` to `Z = X − X(fc(0,R))`, get the a.s. window limits
of `Z` (SW proof of Thm 1.1, p. 9, Borel–Cantelli) and transfer them to `X` (area densities and
area measure of `Z` are those of `X` times `e^{−γX(fc(0,R))}`). No global normalization, hence no
exceptional strip at the unit semicircle.

Main results: `ae_window_of_splitR`, `ae_windowLimits_of_splitR`, `freeWindowStmt_of_splitR`,
`wedgeWindowStmt_of_splitR`. Own elementary bookkeeping, following `E6.freeWindowStmt_of_split`
(`AreaWinDense.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace SWCore

open E6 VagueH

/-- One area window sequence passes from `y` to `x` under an additive constant (single `N`, `φ`
version of `E6.windowLimits_of_scaled`). -/
theorem tendsto_win_of_scaled {γ : ℝ} {x y : FieldSample} {e : ℝ} (he : 0 < e)
    (hd : ∀ ρ : ℝ, 0 < ρ → ∀ z, areaDens γ y ρ z = e * areaDens γ x ρ z)
    (hq : qAreaMeasure γ y = ENNReal.ofReal e • qAreaMeasure γ x) {N : ℕ} {c c' : ℕ → ℝ}
    {φ : ℂ → ℝ}
    (h1 : Tendsto (fun j => supInt γ y c N j φ) atTop
      (𝓝 (ENNReal.ofReal (∫ w, φ w ∂qAreaMeasure γ y))))
    (h2 : Tendsto (fun j => infInt γ y c' N j φ) atTop
      (𝓝 (ENNReal.ofReal (∫ w, φ w ∂qAreaMeasure γ y)))) :
    Tendsto (fun j => supInt γ x c N j φ) atTop
        (𝓝 (ENNReal.ofReal (∫ w, φ w ∂qAreaMeasure γ x))) ∧
      Tendsto (fun j => infInt γ x c' N j φ) atTop
        (𝓝 (ENNReal.ofReal (∫ w, φ w ∂qAreaMeasure γ x))) := by
  have hsup : ∀ j w, supWin γ y N j w = ENNReal.ofReal e * supWin γ x N j w := by
    intro j w
    simp only [supWin, ENNReal.mul_iSup]
    refine iSup_congr fun ρ => iSup_congr fun hρ => ?_
    rw [hd ρ ((winLo_pos N j).trans_le hρ.1) w, ENNReal.ofReal_mul he.le]
  have hinf : ∀ j w, infWin γ y N j w = ENNReal.ofReal e * infWin γ x N j w := by
    intro j w
    have h0 : ENNReal.ofReal e ≠ 0 := (ENNReal.ofReal_pos.2 he).ne'
    simp only [infWin, ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
    refine iInf_congr fun ρ => iInf_congr fun hρ => ?_
    rw [hd ρ ((winLo_pos N j).trans_le hρ.1) w, ENNReal.ofReal_mul he.le]
  have key : ∀ A : ℕ → ℝ≥0∞, Tendsto (fun j => ENNReal.ofReal e * A j) atTop
      (𝓝 (ENNReal.ofReal (∫ w, φ w ∂qAreaMeasure γ y))) →
      Tendsto A atTop (𝓝 (ENNReal.ofReal (∫ w, φ w ∂qAreaMeasure γ x))) := by
    intro A hA
    have h := ENNReal.Tendsto.const_mul hA (Or.inr ENNReal.ofReal_ne_top)
      (a := ENNReal.ofReal e⁻¹)
    rw [hq, integral_smul_measure, ENNReal.toReal_ofReal he.le, smul_eq_mul,
      ← ENNReal.ofReal_mul (inv_nonneg.2 he.le), ← mul_assoc, inv_mul_cancel₀ he.ne',
      one_mul] at h
    refine h.congr fun j => ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 he.le), inv_mul_cancel₀ he.ne',
      ENNReal.ofReal_one, one_mul]
  refine ⟨key _ (h1.congr fun j => ?_), key _ (h2.congr fun j => ?_)⟩
  · simp only [supInt]
    simp_rw [hsup, mul_assoc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    ring
  · simp only [infInt]
    simp_rw [hinf, mul_assoc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    ring

/-- A natural radius `R ≥ 2` with the compact support of `φ` inside `B(0, R−1)`. -/
theorem exists_radius_ball_of_hasCompactSupport {φ : ℂ → ℝ} (hφs : HasCompactSupport φ) :
    ∃ R : ℕ, 2 ≤ R ∧ tsupport φ ⊆ ball (0 : ℂ) ((R : ℝ) - 1) := by
  obtain ⟨r, hr⟩ := hφs.isBounded.subset_closedBall 0
  refine ⟨⌈r⌉₊ + 2, by omega, fun w hw => ?_⟩
  have h1 : dist w 0 ≤ r := hr hw
  have h2 : r ≤ (⌈r⌉₊ : ℝ) := Nat.le_ceil r
  rw [mem_ball]
  push_cast
  linarith

/-- SW proof of Thm 1.1 (p. 9), fixed `N` and `φ`, from the `R`-normalized split: a.s. window
convergence for the **unnormalized** free field. -/
theorem ae_window_of_splitR {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {c c' : ℕ → ℝ}
    (hSW : SWWindowSplitStmtR γ c c') {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {N : ℕ}
    (hN : 1 ≤ N) {φ : ℂ → ℝ} (hφ : IsTestH φ) (hφ0 : ∀ w, 0 ≤ φ w) :
    ∀ᵐ ω ∂P, Tendsto (fun j => supInt γ (X ω) c N j φ) atTop
        (𝓝 (ENNReal.ofReal (∫ w, φ w ∂qAreaMeasure γ (X ω)))) ∧
      Tendsto (fun j => infInt γ (X ω) c' N j φ) atTop
        (𝓝 (ENNReal.ofReal (∫ w, φ w ∂qAreaMeasure γ (X ω)))) := by
  obtain ⟨R, hR, hsupp⟩ := exists_radius_ball_of_hasCompactSupport hφ.2.1
  set Z : Ω → FieldSample := fun ω => BdryExist.zField X R ω with hZdef
  have hZ : IsFreeGFFModConstH Z P :=
    S5.FieldLaw.Raw.isFreeGFFModConstH_addConst hX (c := fun ω => -X ω (foldedCircle 0 R))
      (hX.measurable_coord _).neg
  have hZ0 : ∀ ω, Z ω (foldedCircle 0 R) = 0 := fun ω => by
    simp [hZdef, BdryExist.zField, addConst]
  obtain ⟨h1, h2⟩ := hSW P Z hZ R hR hZ0 N hN φ hφ hφ0 hsupp
  have hB : ∀ᵐ ω ∂P, ENNReal.ofReal (∫ w, φ w ∂qAreaMeasure γ (Z ω)) ≠ ∞ ∧
      Tendsto (fun j => winRef γ (Z ω) N j φ) atTop
        (𝓝 (ENNReal.ofReal (∫ w, φ w ∂qAreaMeasure γ (Z ω)))) := by
    filter_upwards [RegSample.ae_isRegularSample hZ, AreaOffsets.ae_hasAreaLimit hZ hγ hγ2]
      with ω hr hl
    exact ⟨ENNReal.ofReal_ne_top, tendsto_winRef hr hl hN hφ hφ0⟩
  filter_upwards [ae_tendsto_of_winSplit h1 _ hB, ae_tendsto_of_winSplit h2 _ hB,
    RegSample.ae_isRegularSample hX, AreaOffsets.ae_qAreaMeasure_zField_eq hX hγ hγ2 R]
    with ω a b hreg hq
  obtain ⟨F, hF⟩ := hreg
  have hd : ∀ ρ : ℝ, 0 < ρ → ∀ z, areaDens γ (Z ω) ρ z =
      Real.exp (-(γ * X ω (foldedCircle 0 R))) * areaDens γ (X ω) ρ z := by
    intro ρ hρ z
    have hFZ := AllOffsets.regular_zField (X := X) (R := R) hF
    unfold areaDens
    rw [hFZ.evalReg_fc z hρ, hF.evalReg_fc z hρ,
      show γ * (F (foldH z, ρ) + -X ω (foldedCircle 0 R)) =
        γ * F (foldH z, ρ) + -(γ * X ω (foldedCircle 0 R)) by ring, Real.exp_add]
    ring
  exact tendsto_win_of_scaled (Real.exp_pos _) hd hq a b

/-- A.s. window limits for the free field (no normalization), from the `R`-normalized split
(dense-family argument of `E6.ae_windowLimits_normalized`). -/
theorem ae_windowLimits_of_splitR {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {c c' : ℕ → ℝ}
    (hSW : SWWindowSplitStmtR γ c c') {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) :
    ∀ᵐ ω ∂P, WindowLimits γ (X ω) c c' := by
  obtain ⟨Fam, hFc, hFd⟩ := exists_denseTestFamily
  have hcnt : ∀ᵐ ω ∂P, ∀ N : ℕ, 1 ≤ N → ∀ g ∈ Fam,
      Tendsto (fun j => supInt γ (X ω) c N j (posPart' g)) atTop
        (𝓝 (ENNReal.ofReal (∫ w, posPart' g w ∂qAreaMeasure γ (X ω)))) ∧
      Tendsto (fun j => infInt γ (X ω) c' N j (posPart' g)) atTop
        (𝓝 (ENNReal.ofReal (∫ w, posPart' g w ∂qAreaMeasure γ (X ω)))) := by
    refine ae_all_iff.2 fun N => ?_
    by_cases hN : 1 ≤ N
    · have h := (ae_ball_iff hFc).2 fun g hg =>
        ae_window_of_splitR hγ hγ2 hSW hX hN (isTestH_posPart' (hFd.1 g hg))
          (fun z => le_max_right _ _)
      filter_upwards [h] with ω hω _ g hg
      exact hω g hg
    · exact Eventually.of_forall fun ω h => absurd h hN
  filter_upwards [hcnt, RegSample.ae_isRegularSample hX,
    AreaOffsets.ae_hasAreaLimit hX hγ hγ2] with ω hω hreg hl
  intro N hN φ hφc hφs hφH hφ0
  have hφ : IsTestH φ := ⟨hφc, hφs, hφH⟩
  exact ⟨tendsto_winInt_of_dense (fun j => measurable_supWin hreg γ N j) hl.2.1 hFd
      (fun g hg => (hω N hN g hg).1) hφ hφ0,
    tendsto_winInt_of_dense (fun j => measurable_infWin hreg γ N j) hl.2.1 hFd
      (fun g hg => (hω N hN g hg).2) hφ hφ0⟩

/-- **`E6.FreeWindowStmt` from the `R`-normalized area window split** (task SWC-W0). -/
theorem freeWindowStmt_of_splitR {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {c c' : ℕ → ℝ}
    (hSW : SWWindowSplitStmtR γ c c') : FreeWindowStmt γ c c' :=
  fun _ _ _ hX => ae_windowLimits_of_splitR hγ hγ2 hSW hX

/-- **W-A-var-win (`E6.WedgeWindowStmt`) from the `R`-normalized area window split.** -/
theorem wedgeWindowStmt_of_splitR
    (h : ∀ κ : ℝ, 0 < κ → κ < 4 → ∃ c c' : ℕ → ℝ, Tendsto c atTop (𝓝 1) ∧
      Tendsto c' atTop (𝓝 1) ∧ SWWindowSplitStmtR (Real.sqrt κ) c c') : WedgeWindowStmt :=
  wedgeWindowStmt_of_free fun κ hκ hκ4 => by
    obtain ⟨c, c', hc, hc', hSW⟩ := h κ hκ hκ4
    have h2 : Real.sqrt κ < 2 := (Real.sqrt_lt' (by norm_num)).2 (by linarith)
    exact ⟨c, c', hc, hc', freeWindowStmt_of_splitR (Real.sqrt_pos.2 hκ) h2 hSW⟩

end SWCore
end QuantumZipper
