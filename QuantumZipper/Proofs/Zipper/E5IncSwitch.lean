import QuantumZipper.Proofs.Zipper.E5IncMeas

/-!
# E5-INC, part 3: the collision-constant surrogate and the switched `Setup` (decision D28)

Task D28 (Theorem 1.3, node E5). For the regular version `X' = regField ϖ ρ₀ ∘ X` of the
collision free field (`E5IncField`, a free field whenever `X` is, with `X' ν = X ν` a.s. at every
fixed `ν`):

* `exists_inc_regField`: for `r < r'` with `ρ₀(ball 0 r') = 0`, a `condSigma Ξ X' r`-measurable `inc` equal to the raw
  collision constant `X'(ρ₀) − X'(ϖ_τ)` at **every** `ω` with `ϖ_τ(ball 0 r') = 0`. This is the
  input `inc`/`hincm`/`hinc` of `setup_locCorr_switch`, with the switch event at radius `r'`.
* `setup_locCorr_switch_reg`: the D3⁺ `Setup` of the collision correction switched to the
  fallback `g₀` on `{ϖ_τ(ball 0 r') ≠ 0}`, for the regular version, with no `inc` hypothesis.
  (Same proof as `setup_locCorr_switch`, `E5LocC.lean`, with the larger switch radius `r'`.)

Own elementary measure-theoretic arguments.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open B2 E1 D3Plus

/-- The circle readings of the halved base field are measurable for `condSigma` of the regular
version: they are halved balanced differences of `X'` at mass-2 measures missing `ball 0 r`. -/
theorem measurable_halfShift_fc_condSigma {Ω₁ E' : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace E'] (Ξ : Ω₁ → E') (X : Ω₁ → FieldSample) {ϖ ρ₀ : Measure ℂ} {r : ℝ}
    (hρ₀ : IsAdmissibleH ρ₀) (hρ1 : ρ₀ univ = 1) (hρB : ρ₀ (ball (0 : ℂ) r) = 0) {d : ℂ} {k : ℕ}
    (hd : r + radius k ≤ ‖d‖) :
    Measurable[condSigma Ξ (fun ω => regField ϖ ρ₀ (X ω)) r]
      fun ω => halfShift ρ₀ (X ω) (foldedCircle d (radius k)) := by
  have hfc1 : foldedCircle d (radius k) univ = 1 := measure_univ
  have heq : (fun ω => halfShift ρ₀ (X ω) (foldedCircle d (radius k))) = fun ω =>
      (regField ϖ ρ₀ (X ω) ((2 : ℝ≥0) • foldedCircle d (radius k)) -
        regField ϖ ρ₀ (X ω) ((2 : ℝ≥0) • ρ₀)) / 2 := by
    funext ω
    rw [← halfShift_regField (ϖ := ϖ) hρ1 (X ω) hfc1]
    simp [halfShift, hfc1]
  rw [heq]
  refine (measurable_condSigma_sub Ξ _ ?_ ?_ ?_ ?_ ?_).div_const 2
  · rw [nnreal_smul_measure_eq]
    exact isAdmissibleH_smul (D3Plus.isAdmissibleH_foldedCircle' d (radius_pos k))
      ENNReal.coe_lt_top
  · rw [nnreal_smul_measure_eq]
    exact isAdmissibleH_smul hρ₀ ENNReal.coe_lt_top
  · simp [Measure.smul_apply, hfc1, hρ1]
  · simp [Measure.smul_apply, foldedCircle_ball_zero_inc (radius_pos k).le hd]
  · simp [Measure.smul_apply, hρB]

/-- **The collision-constant surrogate** (discharges `inc` of `setup_locCorr_switch`, with the
switch event at radius `r' > r`): a `condSigma`-measurable `inc` equal to
`X'(ρ₀) − X'(ϖ_{t_ω})` for the regular version `X'`, at every `ω` with `ϖ_{t_ω}(ball 0 r') = 0`. -/
theorem exists_inc_regField {Ω₁ E' : Type*} [MeasurableSpace Ω₁] [MeasurableSpace E']
    {r r' : ℝ} (hrr : r < r') {ρ₀ ϖ : Measure ℂ} (X : Ω₁ → FieldSample) (Ξ : Ω₁ → E')
    (hρ₀ : IsAdmissibleH ρ₀) (hρ1 : ρ₀ univ = 1) (hρB : ρ₀ (ball (0 : ℂ) r) = 0)
    (hρB' : ρ₀ (ball (0 : ℂ) r') = 0)
    (hϖ : IsNormalizer ϖ) (Vω : Ω₁ → ℝ → ℝ) (tω : Ω₁ → ℝ) (hV : ∀ ω, Continuous (Vω ω))
    (ht : ∀ ω, 0 ≤ tω ω)
    (hν : ∀ A : Set ℂ, MeasurableSet A →
      Measurable[MeasurableSpace.comap Ξ inferInstance] fun ω => varpiT (Vω ω) (tω ω) ϖ A) :
    ∃ inc : Ω₁ → ℝ, Measurable[condSigma Ξ (fun ω => regField ϖ ρ₀ (X ω)) r] inc ∧
      ∀ ω, ω ∉ radiusBad (fun ω => varpiT (Vω ω) (tω ω) ϖ) r' →
        inc ω = regField ϖ ρ₀ (X ω) ρ₀ - regField ϖ ρ₀ (X ω) (varpiT (Vω ω) (tω ω) ϖ) := by
  classical
  obtain ⟨k₀, hk₀⟩ := exists_k0_inc hrr
  have hY : ∀ (d : ℂ) (k : ℕ), r + radius k ≤ ‖d‖ →
      Measurable[condSigma Ξ (fun ω => regField ϖ ρ₀ (X ω)) r]
        fun ω => halfShift ρ₀ (X ω) (foldedCircle d (radius k)) := fun d k h =>
    measurable_halfShift_fc_condSigma Ξ X hρ₀ hρ1 hρB h
  refine ⟨fun ω => (if ρ₀ ∈ varpiFam ϖ then regCut r' k₀ (halfShift ρ₀ (X ω)) ρ₀ else 0) -
      regCut r' k₀ (halfShift ρ₀ (X ω)) (varpiT (Vω ω) (tω ω) ϖ), ?_, ?_⟩
  · refine Measurable.sub ?_ (@measurable_regCut Ω₁ (condSigma Ξ _ r)
      (fun ω => halfShift ρ₀ (X ω)) r r' k₀ hk₀ hY _
      (fun A hA => (hν A hA).mono le_sup_left le_rfl)
      (fun ω => isProbabilityMeasure_varpiT hϖ (hV ω) (ht ω)))
    by_cases h0 : ρ₀ ∈ varpiFam ϖ
    · simp only [h0, ite_true]
      have hp : IsProbabilityMeasure ρ₀ := ⟨hρ1⟩
      exact @measurable_regCut Ω₁ (condSigma Ξ _ r) (fun ω => halfShift ρ₀ (X ω)) r r' k₀ hk₀ hY
        (fun _ => ρ₀) (fun _ _ => measurable_const) (fun _ => hp)
    · simp only [h0, ite_false]
      exact measurable_const
  · intro ω hω
    have h0 : varpiT (Vω ω) (tω ω) ϖ (ball (0 : ℂ) r') = 0 := by
      by_contra h
      exact hω h
    have hmem : varpiT (Vω ω) (tω ω) ϖ ∈ varpiFam ϖ :=
      ⟨(isProbabilityMeasure_varpiT hϖ (hV ω) (ht ω)).measure_univ, Vω ω, hV ω, tω ω, ht ω, rfl⟩
    rw [regField_rho, regField_of_mem _ hmem, regRead, evalReg_eq_regCut k₀ _ h0]
    by_cases hρm : ρ₀ ∈ varpiFam ϖ
    · simp only [hρm, ite_true, regRead]
      rw [evalReg_eq_regCut k₀ _ hρB']
      ring
    · simp only [hρm, ite_false]
      ring

/-- **`Setup` for the switched collision correction of the regular version** (D28): as
`setup_locCorr_switch`, with the switch event `{ϖ_{t_ω}(ball 0 r') ≠ 0}` for some `r' > r`, and
no hypothesis on the collision constant (it is supplied by `exists_inc_regField`). -/
theorem setup_locCorr_switch_reg {Ω₁ E' : Type} [MeasurableSpace Ω₁] [MeasurableSpace E']
    {r r' : ℝ} (hrr : r < r') (κ : ℝ) {ρ₀ ϖ : Measure ℂ} {Q : Measure Ω₁}
    {X : Ω₁ → FieldSample} {Ξ : Ω₁ → E'} {g₀ : Ω₁ → ℂ → ℝ}
    (hS₀ : D3Plus.Setup (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ Q
      (fun ω => regField ϖ ρ₀ (X ω)) Ξ g₀) (hρB' : ρ₀ (ball (0 : ℂ) r') = 0)
    (hϖ : IsNormalizer ϖ) (Vω : Ω₁ → ℝ → ℝ) (tω : Ω₁ → ℝ) (hV : ∀ ω, Continuous (Vω ω))
    (ht : ∀ ω, 0 ≤ tω ω)
    (hν : ∀ A : Set ℂ, MeasurableSet A →
      Measurable[MeasurableSpace.comap Ξ inferInstance] fun ω => varpiT (Vω ω) (tω ω) ϖ A)
    (hdrv : ∀ z, Measurable[MeasurableSpace.comap Ξ inferInstance]
      fun ω => locCorrDrv κ (Vω ω) (tω ω) ϖ z) :
    D3Plus.Setup (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ Q
      (fun ω => regField ϖ ρ₀ (X ω)) Ξ
      (switchG (radiusBad (fun ω => varpiT (Vω ω) (tω ω) ϖ) r')
        (fun ω => locCorr κ (Vω ω) (tω ω) ϖ ρ₀ (regField ϖ ρ₀ (X ω))) g₀) := by
  obtain ⟨inc, hincm, hinc⟩ :=
    exists_inc_regField hrr X Ξ hS₀.hρ hS₀.hρ1 hS₀.hρB hρB' hϖ Vω tω hV ht hν
  have hle : MeasurableSpace.comap Ξ inferInstance ≤
      condSigma Ξ (fun ω => regField ϖ ρ₀ (X ω)) r := le_sup_left
  refine setup_switch_of_harm_off (gt := fun ω z => locCorrDrv κ (Vω ω) (tω ω) ϖ z + inc ω)
    hS₀ (measurableSet_radiusBad _ (fun A hA => (hν A hA).mono hle le_rfl) r') ?_ ?_ ?_
  · intro ω hω
    have h0 : varpiT (Vω ω) (tω ω) ϖ (ball (0 : ℂ) r) = 0 := by
      by_contra h
      exact hω (radiusBad_mono _ hrr.le h)
    exact harmonicOnNhd_locCorr_foldH_of_normalizer κ ρ₀ _ hϖ (hV ω) (ht ω) h0
  · intro ω hω
    funext z
    rw [locCorr_eq_drv_add_incr, hinc ω hω]
  · intro z
    exact ((hdrv z).mono hle le_rfl).add hincm

end E5
end QuantumZipper
