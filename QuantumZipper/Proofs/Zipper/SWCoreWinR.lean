import QuantumZipper.Proofs.Zipper.SWCoreDefs
import QuantumZipper.Proofs.Zipper.BdryAllMapsDist

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-CORE (derivation 2, task SWC-W0, boundary half): `F1.BdryWindowStmt` from the
# `R`-normalized window split

Task SW-CONSOLIDATE (`handoff/SW-CORE.md` §4). `SWCore.SWBdryWindowSplitStmtR` normalizes the free
field at the semicircle of radius `R` and tests only `φ` supported in `(−(R−1), R−1)`. For one
`N` and `φ`, pick `R` with the support inside, apply the split to `Z = X − X(fc(0,R))` (again a
free field), get the a.s. window limits of `Z` (Borel–Cantelli, `ae_tendsto_of_winSplit`, SW
p. 8–9), and transfer them to `X`: densities and boundary measure of `Z` are those of `X` times
`e^{−γX(fc(0,R))/2}`. So no global normalization is needed, and `F1.BdryWindowStmt` follows for
the unnormalized field directly.

Main results: `ae_bWindow_of_splitR`, `ae_bWindowLimits_of_splitR`, `bdryWindowStmt_of_splitR`,
`bdryAllMapsStmt_of_splitR_distClass`. Own elementary bookkeeping, following
`F1.bdryWindowStmt_of_split` (`BdryAllMapsSplit.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace SWCore

open E6 GoodSample BdryVague F1

/-- The boundary measure of `X − X(fc(0,R))` is `e^{−γX(fc(0,R))/2} ν_X` (copy of
`F1.ae_qBoundaryMeasure_zField_one` at radius `R`). -/
theorem ae_qBoundaryMeasure_zField {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (R : ℝ) :
    ∀ᵐ ω ∂P, qBoundaryMeasure γ (BdryExist.zField X R ω) =
      ENNReal.ofReal (Real.exp (-(γ / 2 * X ω (foldedCircle 0 R)))) •
        qBoundaryMeasure γ (X ω) := by
  filter_upwards [BdryExist.ae_isVagueLimitR_qBoundaryMeasure hX hγ hγ2,
    BdryExist.ae_bdryApprox_eq_smul hX γ R] with ω hν hs
  set c := ENNReal.ofReal (Real.exp (γ / 2 * X ω (foldedCircle 0 R))) with hc
  have hc0 : c ≠ 0 := by rw [hc, Ne, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _
  have hcT : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hZ : (fun k => c⁻¹ • bdryApprox γ (X ω) k) = bdryApprox γ (BdryExist.zField X R ω) := by
    funext k; rw [hs k, smul_smul, ENNReal.inv_mul_cancel hc0 hcT, one_smul]
  have hν' := BdryVague.IsVagueLimitR.const_smul hν (c := c⁻¹) (ENNReal.inv_ne_top.2 hc0)
  rw [hZ] at hν'
  rw [qBoundaryMeasure_eq hν', hc, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), Real.exp_neg]

/-- One window sequence passes from `y` to `x` when `y`'s densities are `e` times `x`'s and the
boundary measures scale likewise (single `N`, `φ` version of `F1.bWindowLimits_of_scaled`). -/
theorem tendsto_bWin_of_scaled {γ : ℝ} {x y : FieldSample} {e : ℝ} (he : 0 < e)
    (hd : ∀ ρ : ℝ, 0 < ρ → ∀ u, bdryDens γ y ρ u = e * bdryDens γ x ρ u)
    (hq : qBoundaryMeasure γ y = ENNReal.ofReal e • qBoundaryMeasure γ x) {N : ℕ} {c c' : ℝ}
    {φ : ℝ → ℝ}
    (h1 : Tendsto (fun j => bWinInt c (bSupWin γ y N j) φ) atTop
      (𝓝 (ENNReal.ofReal (∫ u, φ u ∂qBoundaryMeasure γ y))))
    (h2 : Tendsto (fun j => bWinInt c' (bInfWin γ y N j) φ) atTop
      (𝓝 (ENNReal.ofReal (∫ u, φ u ∂qBoundaryMeasure γ y)))) :
    Tendsto (fun j => bWinInt c (bSupWin γ x N j) φ) atTop
        (𝓝 (ENNReal.ofReal (∫ u, φ u ∂qBoundaryMeasure γ x))) ∧
      Tendsto (fun j => bWinInt c' (bInfWin γ x N j) φ) atTop
        (𝓝 (ENNReal.ofReal (∫ u, φ u ∂qBoundaryMeasure γ x))) := by
  have hsup : ∀ j u, bSupWin γ y N j u = ENNReal.ofReal e * bSupWin γ x N j u := by
    intro j u
    simp only [bSupWin, ENNReal.mul_iSup]
    refine iSup_congr fun ρ => iSup_congr fun hρ => ?_
    rw [hd ρ ((winLo_pos N j).trans_le hρ.1) u, ENNReal.ofReal_mul he.le]
  have hinf : ∀ j u, bInfWin γ y N j u = ENNReal.ofReal e * bInfWin γ x N j u := by
    intro j u
    have h0 : ENNReal.ofReal e ≠ 0 := (ENNReal.ofReal_pos.2 he).ne'
    simp only [bInfWin, ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
    refine iInf_congr fun ρ => iInf_congr fun hρ => ?_
    rw [hd ρ ((winLo_pos N j).trans_le hρ.1) u, ENNReal.ofReal_mul he.le]
  have key : ∀ A : ℕ → ℝ≥0∞, Tendsto (fun j => ENNReal.ofReal e * A j) atTop
      (𝓝 (ENNReal.ofReal (∫ u, φ u ∂qBoundaryMeasure γ y))) →
      Tendsto A atTop (𝓝 (ENNReal.ofReal (∫ u, φ u ∂qBoundaryMeasure γ x))) := by
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
  · simp only [bWinInt]
    simp_rw [hsup, mul_assoc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    ring
  · simp only [bWinInt]
    simp_rw [hinf, mul_assoc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    ring

/-- A natural radius `R ≥ 2` with the compact support of `φ` inside `(−(R−1), R−1)`. -/
theorem exists_radius_of_hasCompactSupport {φ : ℝ → ℝ} (hφs : HasCompactSupport φ) :
    ∃ R : ℕ, 2 ≤ R ∧ tsupport φ ⊆ Ioo (-((R : ℝ) - 1)) ((R : ℝ) - 1) := by
  obtain ⟨r, hr⟩ := hφs.isBounded.subset_closedBall 0
  refine ⟨⌈r⌉₊ + 2, by omega, fun u hu => ?_⟩
  have h1 : |u| ≤ r := by simpa [Real.dist_eq] using hr hu
  have h2 : r ≤ (⌈r⌉₊ : ℝ) := Nat.le_ceil r
  have h3 : |u| < ((⌈r⌉₊ + 2 : ℕ) : ℝ) - 1 := by push_cast; linarith
  exact ⟨by linarith [neg_abs_le u], (le_abs_self u).trans_lt h3⟩

/-- SW proof of Thm 4.2, fixed `N` and `φ`, from the `R`-normalized split: a.s. window
convergence for the **unnormalized** free field. -/
theorem ae_bWindow_of_splitR {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {c c' : ℕ → ℝ}
    (hSW : SWBdryWindowSplitStmtR γ c c') {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {N : ℕ}
    (hN : 1 ≤ N) {φ : ℝ → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hφ0 : ∀ u, 0 ≤ φ u) :
    ∀ᵐ ω ∂P, Tendsto (fun j => bWinInt (c N) (bSupWin γ (X ω) N j) φ) atTop
        (𝓝 (ENNReal.ofReal (∫ u, φ u ∂qBoundaryMeasure γ (X ω)))) ∧
      Tendsto (fun j => bWinInt (c' N) (bInfWin γ (X ω) N j) φ) atTop
        (𝓝 (ENNReal.ofReal (∫ u, φ u ∂qBoundaryMeasure γ (X ω)))) := by
  obtain ⟨R, hR, hsupp⟩ := exists_radius_of_hasCompactSupport hφs
  set Z : Ω → FieldSample := fun ω => BdryExist.zField X R ω with hZdef
  have hZ : IsFreeGFFModConstH Z P :=
    S5.FieldLaw.Raw.isFreeGFFModConstH_addConst hX (c := fun ω => -X ω (foldedCircle 0 R))
      (hX.measurable_coord _).neg
  have hZ0 : ∀ ω, Z ω (foldedCircle 0 R) = 0 := fun ω => by
    simp [hZdef, BdryExist.zField, addConst]
  obtain ⟨h1, h2⟩ := hSW P Z hZ R hR hZ0 N hN φ hφc hφs hφ0 hsupp
  have hB : ∀ᵐ ω ∂P, ENNReal.ofReal (∫ u, φ u ∂qBoundaryMeasure γ (Z ω)) ≠ ∞ ∧
      Tendsto (fun j => bWinRef γ (Z ω) N j φ) atTop
        (𝓝 (ENNReal.ofReal (∫ u, φ u ∂qBoundaryMeasure γ (Z ω)))) := by
    filter_upwards [RegSample.ae_isRegularSample hZ, AllOffsets.ae_hasBdryLimit hZ hγ hγ2]
      with ω hr hl
    exact ⟨ENNReal.ofReal_ne_top, tendsto_bWinRef hr hl hN hφc hφs hφ0⟩
  filter_upwards [ae_tendsto_of_winSplit h1 _ hB, ae_tendsto_of_winSplit h2 _ hB,
    RegSample.ae_isRegularSample hX, ae_qBoundaryMeasure_zField hX hγ hγ2 R]
    with ω a b hreg hq
  obtain ⟨F, hF⟩ := hreg
  have hd : ∀ ρ : ℝ, 0 < ρ → ∀ u, bdryDens γ (Z ω) ρ u =
      Real.exp (-(γ / 2 * X ω (foldedCircle 0 R))) * bdryDens γ (X ω) ρ u := by
    intro ρ hρ u
    have hFZ := AllOffsets.regular_zField (X := X) (R := R) hF
    unfold bdryDens
    rw [hFZ.evalReg_fc _ hρ, hF.evalReg_fc _ hρ,
      show γ / 2 * (F (foldH (u : ℂ), ρ) + -X ω (foldedCircle 0 R)) =
        γ / 2 * F (foldH (u : ℂ), ρ) + -(γ / 2 * X ω (foldedCircle 0 R)) by ring, Real.exp_add]
    ring
  exact tendsto_bWin_of_scaled (Real.exp_pos _) hd hq a b

/-- A.s. boundary window limits for the free field (no normalization), from the
`R`-normalized split (dense-family argument of `F1.ae_bWindowLimits_normalized`). -/
theorem ae_bWindowLimits_of_splitR {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {c c' : ℕ → ℝ}
    (hSW : SWBdryWindowSplitStmtR γ c c') {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) :
    ∀ᵐ ω ∂P, BdryWindowLimits γ (X ω) c c' := by
  have hcnt : ∀ᵐ ω ∂P, ∀ N : ℕ, 1 ≤ N →
      (∀ M m : ℕ, Tendsto (fun j => bWinInt (c N) (bSupWin γ (X ω) N j) (posR (testFam M m)))
          atTop (𝓝 (ENNReal.ofReal (∫ u, posR (testFam M m) u ∂qBoundaryMeasure γ (X ω)))) ∧
        Tendsto (fun j => bWinInt (c' N) (bInfWin γ (X ω) N j) (posR (testFam M m)))
          atTop (𝓝 (ENNReal.ofReal (∫ u, posR (testFam M m) u ∂qBoundaryMeasure γ (X ω))))) ∧
      (∀ M : ℕ, Tendsto (fun j => bWinInt (c N) (bSupWin γ (X ω) N j) (bump M))
          atTop (𝓝 (ENNReal.ofReal (∫ u, bump M u ∂qBoundaryMeasure γ (X ω)))) ∧
        Tendsto (fun j => bWinInt (c' N) (bInfWin γ (X ω) N j) (bump M))
          atTop (𝓝 (ENNReal.ofReal (∫ u, bump M u ∂qBoundaryMeasure γ (X ω))))) := by
    refine ae_all_iff.2 fun N => ?_
    by_cases hN : 1 ≤ N
    · have hA := ae_all_iff.2 fun M => ae_all_iff.2 fun m =>
        ae_bWindow_of_splitR hγ hγ2 hSW hX hN
          (posR_test (continuous_testFam M m) (hasCompactSupport_testFam M m)).1
          (posR_test (continuous_testFam M m) (hasCompactSupport_testFam M m)).2
          (fun z => le_max_right _ _)
      have hB := ae_all_iff.2 fun M => ae_bWindow_of_splitR hγ hγ2 hSW hX hN
        (continuous_bump M) (hasCompactSupport_bump M) (bump_nonneg M)
      filter_upwards [hA, hB] with ω h1 h2 _
      exact ⟨h1, h2⟩
    · exact Eventually.of_forall fun ω h => absurd h hN
  filter_upwards [hcnt, RegSample.ae_isRegularSample hX,
    BdryExist.ae_isVagueLimitR_qBoundaryMeasure hX hγ hγ2] with ω hω hreg hν
  have : IsLocallyFiniteMeasure (qBoundaryMeasure γ (X ω)) := hν.1
  intro N hN φ hφc hφs hφ0
  obtain ⟨hA, hB⟩ := hω N hN
  exact ⟨tendsto_bWinInt_of_dense (fun j => measurable_bSupWin hreg γ N j)
      (fun M m => (hA M m).1) (fun M => (hB M).1) hφc hφs hφ0,
    tendsto_bWinInt_of_dense (fun j => measurable_bInfWin hreg γ N j)
      (fun M m => (hA M m).2) (fun M => (hB M).2) hφc hφs hφ0⟩

/-- **`F1.BdryWindowStmt` from the `R`-normalized boundary window split** (task SWC-W0). -/
theorem bdryWindowStmt_of_splitR
    (h : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ c c' : ℕ → ℝ, Tendsto c atTop (𝓝 1) ∧
      Tendsto c' atTop (𝓝 1) ∧ SWBdryWindowSplitStmtR γ c c') : BdryWindowStmt := by
  intro γ hγ hγ2
  obtain ⟨c, c', hc, hc', hSW⟩ := h γ hγ hγ2
  exact ⟨c, c', hc, hc', fun _ _ _ hX => ae_bWindowLimits_of_splitR hγ hγ2 hSW hX⟩

end SWCore
end QuantumZipper
