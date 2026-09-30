import QuantumZipper.Proofs.Thm18.G3Area
import QuantumZipper.Proofs.LQG.PositivityArea
import QuantumZipper.Proofs.LQG.LogSingGood

/-!
# G3 area Palm input (Theorem 1.8): Theorem 1.2's field is a.s. area-good

Sheffield, arXiv:1012.4797, proof of Theorem 1.8 (§5.4, pp. 70–71): near the Palm point the
scheme's field `h` looks like a free field, hence its quantum area charges every nonempty open
subset of `ℍ` (so the zoomed area at the Palm point tends to infinity, `G3AreaCore`/`G3Area`).
This file proves the deterministic-plus-a.s. half of `G3AreaPalmStmt`: a.s. Theorem 1.2's field
`h = normField γ X₀` is area-good (`IsAreaGood`, `G3Area.lean`).

Route (own assembly; all inputs cited):

* `h0rev_eq_Lf_neg`: `h0rev (γ ^ 2) = Lf (-(2/γ))`, i.e. the field is the free field plus a
  boundary log potential of strength `α = -(2/γ)` at `0` (`LogSingGood.Lf`); note the *negative*
  strength, so the area density `‖z‖^{−αγ} = ‖z‖²` is bounded, and `α < Q` holds trivially;
* `normField_fc_eq_Lf`: on folded circles (probability measures), `normField` agrees with the
  normalized free field `zField X 1` plus `Lf α` (the `(μ univ).toReal` normalization of
  `addConst` is what makes the comparison a pointwise ring identity);
* `ae_isLQGGood_normField`: goodness of `normField` a.s., from `LogSingGoodAS γ α`
  (`LogSingGood.logSingGoodAS_holds`, M4-P4 with offsets) via `IsLQGGood.addConst` and the
  coordinates-congruence `WedgeGood.isLQGGood_congr_coords`;
* `qAreaMeasure_add_Lf_of_isLQGGood`: the area measure of `x + Lf α` is
  `(qAreaMeasure γ x).withDensity (‖z‖^{−αγ})` (`LogSingGood.hasAreaLimit_add_Lf` + uniqueness);
* `ae_isAreaGood_normField`: **a.s. `IsAreaGood γ (normField γ X₀)`**: the area is
  `e^{γc} • (μ_{X₀}.withDensity ‖z‖²)`, and a positive continuous density on a rational box
  inside a nonempty open `V ⊆ ℍ` (the box construction of `PositivityArea`) gives positivity
  from `PositivityArea.ae_forall_pos_qAreaMeasure` (M4-P2) for the free field.

Own elementary arguments on top of the cited lemmas (AGENT_GUIDE cost rule); the box argument is
the one of `PositivityArea.ae_forall_pos_qAreaMeasure`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open LQGMeas LocalRule Factorization CoordsFull
open GoodSample

set_option linter.unusedSectionVars false

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-! ## Theorem 1.2's field as a free field plus a log potential -/

/-- `h0rev (γ ^ 2) = Lf (-(2/γ))`: the log potential of Theorem 1.2's field, in the sign
convention of `LogSingGood.Lf` (the singularity of the area density is `‖z‖^{2}`). -/
theorem h0rev_eq_Lf_neg {γ : ℝ} (hγ : 0 < γ) :
    h0rev (γ ^ 2) = LogSingGood.Lf (-(2 / γ)) := by
  funext v
  simp only [h0rev, LogSingGood.Lf, Real.sqrt_sq hγ.le]
  ring

/-- On folded circles (probability measures) Theorem 1.2's field agrees with the normalized free
field `zField X 1` plus the log potential `Lf (-(2/γ))`. -/
theorem normField_fc_eq_Lf {γ : ℝ} (hγ : 0 < γ) (X : Ω → FieldSample) (ω : Ω) (c : ℂ) (ρ : ℝ) :
    normField γ X ω (foldedCircle c ρ) =
      (BdryExist.zField X 1 ω + ofFun (LogSingGood.Lf (-(2 / γ)))) (foldedCircle c ρ) := by
  simp only [normField, BdryExist.zField, addConst, Pi.add_apply, measure_univ,
    ENNReal.toReal_one, mul_one, h0rev_eq_Lf_neg hγ]
  ring

/-- The coefficients of Theorem 1.2's field and of the log-potential representative agree. -/
theorem coords_normField_eq_Lf {γ : ℝ} (hγ : 0 < γ) (X : Ω → FieldSample) (ω : Ω) :
    coords (normField γ X ω) =
      coords (BdryExist.zField X 1 ω + ofFun (LogSingGood.Lf (-(2 / γ)))) :=
  funext fun _ => normField_fc_eq_Lf hγ X ω _ _

/-- The log-potential representative is a constant shift of the a.s. good log-singular field. -/
theorem zField_add_Lf_eq_addConst (X : Ω → FieldSample) (ω : Ω) (α : ℝ) :
    BdryExist.zField X 1 ω + ofFun (LogSingGood.Lf α) =
      addConst (X ω + ofFun (LogSingGood.Lf α)) (-(X ω (foldedCircle 0 1))) := by
  have h : ∀ (y : FieldSample) (c : ℝ),
      addConst (y + ofFun (LogSingGood.Lf α)) c = addConst y c + ofFun (LogSingGood.Lf α) := by
    intro y c
    funext μ
    simp only [addConst, ofFun, Pi.add_apply]
    ring
  rw [h]
  rfl

/-- The exponent `-αγ` at `α = -(2/γ)` is `2`. -/
theorem neg_mul_eq_two {γ : ℝ} (hγ : 0 < γ) : -((-(2 / γ)) * γ) = (2 : ℝ) := by
  have h0 : γ ≠ 0 := hγ.ne'
  field_simp

/-! ## Almost sure goodness of Theorem 1.2's field -/

/-- Almost surely the normalized free field plus the log potential is a good sample. -/
theorem ae_isLQGGood_zField_add_Lf [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, IsLQGGood γ (BdryExist.zField X 1 ω + ofFun (LogSingGood.Lf (-(2 / γ)))) := by
  have hαQ : -(2 / γ) < Qc γ := by
    have h1 : 0 < 2 / γ := by positivity
    have h2 : 0 < Qc γ := by unfold Qc; positivity
    linarith
  filter_upwards [LogSingGood.logSingGoodAS_holds (γ := γ) (α := -(2 / γ)) hγ hγ2 hαQ
      Ω _ P X ‹IsProbabilityMeasure P› hX] with ω hω
  rw [zField_add_Lf_eq_addConst]
  exact hω.addConst _

/-- **Almost surely Theorem 1.2's field is a good sample.** -/
theorem ae_isLQGGood_normField [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, IsLQGGood γ (normField γ X ω) := by
  filter_upwards [ae_isLQGGood_zField_add_Lf (X := X) hX hγ hγ2] with ω hω
  exact (WedgeGood.isLQGGood_congr_coords (coords_normField_eq_Lf hγ X ω)).2 hω

/-! ## The area measure of the log-potential field -/

/-- **The area measure of a good sample plus the log potential `Lf α`**: it is the area measure
of the sample weighted by `‖z‖^{−αγ}`. -/
theorem qAreaMeasure_add_Lf_of_isLQGGood {γ α : ℝ} {x : FieldSample} (hx : IsLQGGood γ x) :
    qAreaMeasure γ (x + ofFun (LogSingGood.Lf α)) =
      (qAreaMeasure γ x).withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (-(α * γ)))) := by
  obtain ⟨F, hF⟩ := hx.1
  exact qAreaMeasure_eq_of_hasAreaLimit ⟨_, LogSingGood.regular_add_Lf hF α⟩
    (LogSingGood.hasAreaLimit_add_Lf hF hx.qAreaMeasure_spec α)

/-! ## Boxes inside a nonempty open subset of `ℍ` -/

/-- The rational box `(a₁,b₁) × (a₂,b₂)` is nonempty. -/
theorem obox_nonempty {a₁ b₁ a₂ b₂ : ℝ} (h₁ : a₁ < b₁) (h₂ : a₂ < b₂) :
    (PositivityArea.obox a₁ b₁ a₂ b₂).Nonempty :=
  ⟨((a₁ + b₁) / 2 : ℝ) + ((a₂ + b₂) / 2 : ℝ) * Complex.I, by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp <;> linarith⟩

/-- A box with `a₂ > 0` lies in the open half-plane. -/
theorem obox_subset_H {a₁ b₁ a₂ b₂ : ℝ} (h₂ : 0 < a₂) :
    PositivityArea.obox a₁ b₁ a₂ b₂ ⊆ H :=
  fun _ hz => lt_trans h₂ hz.2.1

/-- Every nonempty open subset of `ℍ` contains a rational box `(a₁,b₁) × (a₂,b₂)` with
`a₂ > 0`. -/
theorem exists_obox_subset {V : Set ℂ} (hV : IsOpen V) (hVH : V ⊆ H) (hne : V.Nonempty) :
    ∃ a₁ b₁ a₂ b₂ : ℚ, (a₁ : ℝ) < b₁ ∧ (a₂ : ℝ) < b₂ ∧ 0 < (a₂ : ℝ) ∧
      PositivityArea.obox a₁ b₁ a₂ b₂ ⊆ V := by
  obtain ⟨z, hz⟩ := hne
  have him : 0 < z.im := hVH hz
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV z hz
  set δ := min (ε / 2) (z.im / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  have hδi : δ ≤ z.im / 2 := min_le_right _ _
  obtain ⟨a₁, ha₁, ha₁'⟩ := exists_rat_btwn (show z.re - δ < z.re by linarith)
  obtain ⟨b₁, hb₁, hb₁'⟩ := exists_rat_btwn (show z.re < z.re + δ by linarith)
  obtain ⟨a₂, ha₂, ha₂'⟩ := exists_rat_btwn (show z.im - δ < z.im by linarith)
  obtain ⟨b₂, hb₂, hb₂'⟩ := exists_rat_btwn (show z.im < z.im + δ by linarith)
  have ha₂pos : (0 : ℝ) < (a₂ : ℝ) := by linarith
  refine ⟨a₁, b₁, a₂, b₂, by linarith, by linarith, ha₂pos, fun w hw => ?_⟩
  apply hball
  rw [Metric.mem_ball, dist_eq_norm]
  have h1 : |(w - z).re| < δ := by
    rw [Complex.sub_re, abs_lt]
    constructor <;> linarith [hw.1.1, hw.1.2]
  have h2 : |(w - z).im| < δ := by
    rw [Complex.sub_im, abs_lt]
    constructor <;> linarith [hw.2.1, hw.2.2]
  linarith [Complex.norm_le_abs_re_add_abs_im (w - z)]

/-! ## Positive measures stay positive after weighting by `‖z‖²` -/

/-- **Weighting by `‖z‖²` preserves positivity on open subsets of `ℍ`**: a box inside `V` on
which `‖z‖² ≥ a₂² > 0` gives the lower bound `a₂² · μ(box)`. -/
theorem pos_withDensity_normSq {μ : Measure ℂ}
    (hpos : ∀ V : Set ℂ, IsOpen V → V ⊆ H → V.Nonempty → 0 < μ V)
    {V : Set ℂ} (hV : IsOpen V) (hVH : V ⊆ H) (hne : V.Nonempty) :
    0 < (μ.withDensity fun z => ENNReal.ofReal (‖z‖ ^ (2 : ℝ))) V := by
  obtain ⟨a₁, b₁, a₂, b₂, h₁, h₂, ha₂, hsub⟩ := exists_obox_subset hV hVH hne
  have hlow : ∫⁻ z in PositivityArea.obox a₁ b₁ a₂ b₂,
        ENNReal.ofReal ((a₂ : ℝ) ^ (2 : ℝ)) ∂μ ≤
      ∫⁻ z in PositivityArea.obox a₁ b₁ a₂ b₂,
        ENNReal.ofReal (‖z‖ ^ (2 : ℝ)) ∂μ := by
    refine setLIntegral_mono
      (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const 2)) ?_
    intro z hz
    have hza : (a₂ : ℝ) ≤ ‖z‖ := by
      have h1' := Complex.abs_im_le_norm z
      rw [abs_of_pos (lt_trans ha₂ hz.2.1)] at h1'
      linarith [hz.2.1]
    rw [Real.rpow_two, Real.rpow_two]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ha₂.le hza 2)
  have hposB : 0 < ∫⁻ z in PositivityArea.obox a₁ b₁ a₂ b₂,
      ENNReal.ofReal ((a₂ : ℝ) ^ (2 : ℝ)) ∂μ := by
    rw [setLIntegral_const]
    refine ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos ha₂ 2)).ne' ?_
    exact (hpos _ PositivityArea.isOpen_obox (obox_subset_H ha₂)
      (obox_nonempty h₁ h₂)).ne'
  refine lt_of_lt_of_le hposB ?_
  calc ∫⁻ z in PositivityArea.obox a₁ b₁ a₂ b₂,
        ENNReal.ofReal ((a₂ : ℝ) ^ (2 : ℝ)) ∂μ
      ≤ ∫⁻ z in PositivityArea.obox a₁ b₁ a₂ b₂,
        ENNReal.ofReal (‖z‖ ^ (2 : ℝ)) ∂μ := hlow
    _ = (μ.withDensity fun z => ENNReal.ofReal (‖z‖ ^ (2 : ℝ)))
        (PositivityArea.obox a₁ b₁ a₂ b₂) :=
        (withDensity_apply _ PositivityArea.isOpen_obox.measurableSet).symm
    _ ≤ (μ.withDensity fun z => ENNReal.ofReal (‖z‖ ^ (2 : ℝ))) V := measure_mono hsub

/-! ## Area-goodness of Theorem 1.2's field -/

/-- **Almost surely Theorem 1.2's field is area-good** (good, with positive quantum area on
every nonempty open subset of `ℍ`). -/
theorem ae_isAreaGood_normField [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, IsAreaGood γ (normField γ X ω) := by
  have hαQ : -(2 / γ) < Qc γ := by
    have h1 : 0 < 2 / γ := by positivity
    have h2 : 0 < Qc γ := by unfold Qc; positivity
    linarith
  filter_upwards [PositivityArea.ae_forall_pos_qAreaMeasure hX hγ hγ2,
    LogSingGood.logSingGoodAS_holds (γ := γ) (α := -(2 / γ)) hγ hγ2 hαQ Ω _ P X
      ‹IsProbabilityMeasure P› hX,
    AreaOffsets.ae_isLQGGood hX hγ hγ2,
    ae_isLQGGood_zField_add_Lf (X := X) hX hγ hγ2,
    ae_isLQGGood_normField (X := X) hX hγ hγ2] with ω hpos hLf hXg hgoodZ hgood
  refine ⟨hgood, fun V hV hVH hne => ?_⟩
  -- the area measure of the log-potential representative
  have hrep : qAreaMeasure γ (BdryExist.zField X 1 ω + ofFun (LogSingGood.Lf (-(2 / γ)))) =
      ENNReal.ofReal (Real.exp (γ * (-(X ω (foldedCircle 0 1))))) •
        (qAreaMeasure γ (X ω)).withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (2 : ℝ))) := by
    have hLf' : IsLQGGood γ (X ω + ofFun (LogSingGood.Lf (-(2 / γ)))) := hLf
    have h1 : qAreaMeasure γ (addConst (X ω + ofFun (LogSingGood.Lf (-(2 / γ))))
          (-(X ω (foldedCircle 0 1)))) =
        ENNReal.ofReal (Real.exp (γ * (-(X ω (foldedCircle 0 1))))) •
          qAreaMeasure γ (X ω + ofFun (LogSingGood.Lf (-(2 / γ)))) :=
      qAreaMeasure_addConst hLf' _
    have h2 : qAreaMeasure γ (X ω + ofFun (LogSingGood.Lf (-(2 / γ)))) =
        (qAreaMeasure γ (X ω)).withDensity
          (fun z => ENNReal.ofReal (‖z‖ ^ (-((-(2 / γ)) * γ)))) :=
      qAreaMeasure_add_Lf_of_isLQGGood (x := X ω) hXg
    rw [zField_add_Lf_eq_addConst, h1, h2]
    simp only [neg_mul_eq_two hγ]
  -- the area measures of `normField` and of the representative agree
  have hap : areaApprox γ (normField γ X ω) =
      areaApprox γ (BdryExist.zField X 1 ω + ofFun (LogSingGood.Lf (-(2 / γ)))) :=
    PositivityArea.areaApprox_congr_pcirc
      (fun i => congrFun (coords_normField_eq_Lf hγ X ω) i.1) γ
  have hlim : IsVagueLimitOn H (areaApprox γ (normField γ X ω))
      (qAreaMeasure γ (BdryExist.zField X 1 ω + ofFun (LogSingGood.Lf (-(2 / γ))))) := by
    rw [hap]
    exact Prop16Area.G.isVagueLimitOn_H_of_good hgoodZ
  rw [qAreaMeasure_eq hlim, hrep, Measure.smul_apply, smul_eq_mul]
  refine ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' ?_
  exact (pos_withDensity_normSq (fun V hV hVH hne => hpos V hV hVH hne) hV hVH hne).ne'

end Thm18Asm
end QuantumZipper
