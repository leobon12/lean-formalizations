import QuantumZipper.Proofs.Zipper.D3PlusN2Loc
import QuantumZipper.Proofs.Zipper.D3PlusN2Bridge
import QuantumZipper.Proofs.Zipper.D3PlusN2Cutoff

/-!
# D3⁺(i), node N2 in N1's measurable form: assembly of `D3PlusIN2RichStmt`

Task D3P-N2. The fixed-correction zoom is read through N1's measurable factorization map
`TmRichN1` (`D3PlusN1Scale.lean`): for a deterministic correction `φ` put
`circData α φ μ = ∫ (α(−log‖·‖) + φ) dμ`; the zoomed rich data of the local field `Z` plus `φ`
is `TmRichN1 γ r R L (Z, circData α φ)`, a measurable function of `Z`, so no separate
measurability node is needed.

## Result

`d3PlusIN2Rich_of_nodes : D3PlusIN2TmZeroStmt → CMIncrStmt → D3PlusIN2FixScaleStmt →
D3PlusIN2FixMacroStmt → D3PlusIN2RichStmt`, from

* `D3PlusIN2TmZeroStmt` — the model zoom (correction `0`): radial part (D3-RAD,
  `ZoomRadial.abs_prob_zoomRadial_sub_le`, unconditional via
  `Williams.williamsDriftDecomposition_holds`) and lateral scale invariance;
* `CMIncrStmt` — Cameron–Martin TV bound for the free field (task CM-TV);
* `D3PlusIN2FixScaleStmt` — the local scale tends to `0` in probability;
* `D3PlusIN2FixMacroStmt` — the frozen macroscopic data is circle data of an admissible `φ_ω`.

Proved steps (own elementary arguments): the level shift (`locModel_circData_const`: a constant
correction `c` is the level `L + γ c`), the congruence of `TmRichN1` in the local model
(`TmRichN1_congr`), the Cameron–Martin step `tendsto_tvDist_tm_cm` (locality `D3PlusN2Loc`,
local CM bound `D3PlusN2CMLoc` + cutoff `D3PlusN2Cutoff`, coupling off the bad-scale event), and
the triangle inequality through the constant correction `φ(0)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- Circle data of a deterministic correction: `μ ↦ ∫ (α(−log‖·‖) + φ) dμ`. -/
def circData (α : ℝ) (φ : ℂ → ℝ) : FieldSample := fun μ => ∫ z, (α * -Real.log ‖z‖ + φ z) ∂μ

theorem TmRichN1_congr {γ r L L' : ℝ} {R : ℕ} {p p' : N1Idx r}
    (h : locModel γ L r p = locModel γ L' r p') : TmRichN1 γ r R L p = TmRichN1 γ r R L' p' := by
  have hs : scaleSur γ L r p = scaleSur γ L' r p' := by
    simp only [scaleSur, Prop16Area.Meas.M, Prop16Area.Meas.Psi, bumpHD, h]
  simp only [TmRichN1, zoomN1, hs, h]

theorem locModel_congr_circ {γ L r : ℝ} {s : LocIdx r → ℝ} {f f' : FieldSample}
    (h : ∀ μ ∈ circSet r, f μ = f' μ) : locModel γ L r (s, f) = locModel γ L r (s, f') := by
  classical
  funext μ
  unfold locModel
  split_ifs with hμ
  · dsimp only
    rw [h μ hμ]
  · rfl

theorem integrable_circ {α r : ℝ} {ψ : ℂ → ℝ}
    (hψ : ContinuousOn ψ (Metric.ball (0 : ℂ) r ∩ Hbar)) {μ : Measure ℂ} (hμ : μ ∈ circSet r) :
    Integrable (fun z => α * -Real.log ‖z‖ + ψ z) μ := by
  have hloc := isLocalH_of_mem_circSet hμ
  have hfin : IsFiniteMeasure μ := hloc.1.1
  exact ((WedgeRes.integrable_log_norm_adm hloc.1).neg.const_mul α).add
    (integrable_of_admCorr le_rfl hψ ⟨μ, hloc⟩)

/-- A constant correction is a level shift, at the level of the local model. -/
theorem locModel_circData_const {γ : ℝ} (hγ : γ ≠ 0) (α L r c : ℝ) (s : LocIdx r → ℝ) :
    locModel γ L r (s, circData α (fun _ => c)) =
      locModel γ (L + γ * c) r (s, circData α (fun _ => 0)) := by
  classical
  funext μ
  unfold locModel
  split_ifs with hμ
  · obtain ⟨d, ρ, -, -, rfl⟩ := exists_of_mem_circSet hμ
    have hint : Integrable (fun z : ℂ => α * -Real.log ‖z‖) (foldedCircle d ρ) :=
      (CoordReg.integrable_log_norm_foldedCircle d ρ).neg.const_mul α
    simp only [circData]
    rw [integral_add hint (integrable_const c), integral_add hint (integrable_const 0),
      integral_const, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul,
      one_smul, add_div, mul_div_cancel_left₀ _ hγ]
    ring
  · rfl

/-! ## The statements in N1 form -/

/-- **N2, fixed correction, N1 form.** -/
def D3PlusIN2TmStmt : Prop :=
  ∀ (γ α r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (Y' : Ω' → FieldSample) (φ : ℂ → ℝ),
    0 < γ → γ < 2 → 0 < r → IsFreeGFFModConstH X P → IsQuantumWedge γ α Y' P' → AdmCorr r φ →
    ∀ R : ℕ, Tendsto (fun L => TV.tvDist
      (P.map fun ω => TmRichN1 γ r R L (localZ X r ω, circData α φ))
      (P'.map fun ω' => locFieldFull R (Y' ω'))) atTop (𝓝 0)

/-- **N2-zero, N1 form** (the model zoom: correction `0`). Remaining analytic heart: radial part
(D3-RAD) and lateral scale invariance. -/
def D3PlusIN2TmZeroStmt : Prop :=
  ∀ (γ α r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (Y' : Ω' → FieldSample),
    0 < γ → γ < 2 → 0 < r → IsFreeGFFModConstH X P → IsQuantumWedge γ α Y' P' →
    ∀ R : ℕ, Tendsto (fun L => TV.tvDist
      (P.map fun ω => TmRichN1 γ r R L (localZ X r ω, circData α (fun _ => 0)))
      (P'.map fun ω' => locFieldFull R (Y' ω'))) atTop (𝓝 0)

/-! ## The Cameron–Martin step -/

/-- **Two admissible corrections agreeing at `0` give TV-close zooms** (N1 form). -/
theorem tendsto_tvDist_tm_cm (hCM : D3PlusIN2FixCMLocStmt) (hSc : D3PlusIN2FixScaleStmt)
    {γ α r : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ) (hr : 0 < r)
    (hX : IsFreeGFFModConstH X P) {φ φ' : ℂ → ℝ} (hφ : AdmCorr r φ) (hφ' : AdmCorr r φ')
    (h0 : φ 0 = φ' 0) (R : ℕ) :
    Tendsto (fun L => TV.tvDist
      (P.map fun ω => TmRichN1 γ r R L (localZ X r ω, circData α φ))
      (P.map fun ω => TmRichN1 γ r R L (localZ X r ω, circData α φ'))) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  have hh0 : (fun z => φ' z - φ z) 0 = 0 := by simp [h0]
  have hcm := hCM r P X _ hr hX (admCorr_sub hφ hφ') hh0
  obtain ⟨ε, hεt, hεpos, hεr⟩ := ((ENNReal.tendsto_nhds_zero.1 hcm _ hη2).and
    (Ioc_mem_nhdsGT hr)).exists
  have hδ : 0 < ε / (R + 2) := by positivity
  have hRr : ε / (R + 2) ≤ r / (R + 1) :=
    (div_le_div_of_nonneg_left hεpos.le (by positivity) (by linarith)).trans
      (div_le_div_of_nonneg_right hεr (by positivity))
  have hsum := (hSc γ α r P X φ hγ hγ2 hα hr hX hφ _ hδ).add
    (hSc γ α r P X φ' hγ hγ2 hα hr hX hφ' _ hδ)
  rw [add_zero] at hsum
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hsum _ hη2] with L hL
  have hZ := measurable_localZ hX hr
  have hWm : Measurable fun ω => resField ε (locZField X r ω) :=
    (measurable_resField ε).comp ((measurable_extLoc r).comp hZ)
  set G : (LocIdx ε → ℝ) → (ℕ → ℝ) × (TestFun H → ℝ) := fun v => TmRichN1 γ ε R 0 (v, 0)
  have hG : Measurable G :=
    (measurable_TmRichN1 γ ε R 0).comp (measurable_id.prodMk measurable_const)
  have hA : ∀ ψ : ℂ → ℝ, Measurable fun ω => TmRichN1 γ r R L (localZ X r ω, circData α ψ) :=
    fun ψ => (measurable_TmRichN1 γ r R L).comp (hZ.prodMk measurable_const)
  have hB : ∀ ψ : ℂ → ℝ, AdmCorr r ψ → ∀ᵐ ω ∂P, ω ∉ {ω |
      ¬(0 < scaleParamOn γ (locZField X r ω + ofFun (n2Shift γ α L ψ)) (halfDisc r) ∧
        scaleParamOn γ (locZField X r ω + ofFun (n2Shift γ α L ψ)) (halfDisc r) <
          ε / (R + 2))} →
      TmRichN1 γ r R L (localZ X r ω, circData α ψ) =
        G (resField ε (locZField X r ω + ofFun (n2Shift γ α L ψ))) := by
    intro ψ hψ
    refine Eventually.of_forall fun ω hnot => ?_
    have hq := not_not.1 hnot
    have hag := agreeNear_n2 (γ := γ) (L := L) (s := localZ X r ω) (f := circData α ψ)
      fun μ hμ => ⟨integrable_circ hψ.1 hμ, rfl⟩
    rw [← n2Canon_eq_TmRichN1 hag hq.1 (hq.2.trans_le hRr)]
    exact locFieldFull_canonicalOn_eq_local hεpos hεr hq.1 hq.2
  have e1 : (fun ω => resField ε (locZField X r ω + ofFun (n2Shift γ α L φ))) =
      fun ω => resField ε (locZField X r ω) + pairShift ε (n2Shift γ α L φ) := rfl
  have e2 : (fun ω => resField ε (locZField X r ω + ofFun (n2Shift γ α L φ'))) =
      fun ω => resField ε (locZField X r ω) + pairShift ε (n2Shift γ α L φ) +
        pairShift ε (fun z => φ' z - φ z) :=
    funext fun ω => resField_n2_sub hεr hφ.1 hφ'.1 _
  have hρ1 : AEMeasurable
      (fun ω => resField ε (locZField X r ω + ofFun (n2Shift γ α L φ))) P := by
    rw [e1]; exact (hWm.add_const _).aemeasurable
  have hρ2 : AEMeasurable
      (fun ω => resField ε (locZField X r ω + ofFun (n2Shift γ α L φ'))) P := by
    rw [e2]; exact ((hWm.add_const _).add_const _).aemeasurable
  have hloc := tvDist_map_le_of_local (hA φ).aemeasurable (hA φ').aemeasurable hρ1 hρ2 hG
    (hB φ hφ) (hB φ' hφ')
  rw [e1, e2] at hloc
  calc _ ≤ _ := hloc
    _ ≤ η / 2 + η / 2 := add_le_add ((tvDist_map_add_le P hWm _ _).trans hεt) hL
    _ = η := ENNReal.add_halves η

/-! ## Assembly -/

/-- **N2 (N1 form) from the model zoom, the local CM bound and the scale** (triangle inequality
through the constant correction `φ(0)`, which is the level shift `L + γ φ(0)`). -/
theorem d3PlusIN2Tm_of_parts (hZ : D3PlusIN2TmZeroStmt) (hCM : D3PlusIN2FixCMLocStmt)
    (hSc : D3PlusIN2FixScaleStmt) : D3PlusIN2TmStmt := by
  intro γ α r Ω _ P _ X Ω' _ P' _ Y' φ hγ hγ2 hr hX hW hφ R
  set ν := P'.map fun ω' => locFieldFull R (Y' ω')
  have h1 := tendsto_tvDist_tm_cm hCM hSc hγ hγ2 hW.1 hr hX hφ (admCorr_const r (φ 0)) rfl R
  have h2 := (hZ γ α r P X P' Y' hγ hγ2 hr hX hW R).comp
    (tendsto_atTop_add_const_right atTop (γ * φ 0) tendsto_id)
  have h2' : Tendsto (fun L => TV.tvDist
      (P.map fun ω => TmRichN1 γ r R L (localZ X r ω, circData α (fun _ => φ 0))) ν)
      atTop (𝓝 0) := by
    refine h2.congr fun L => ?_
    have e : (fun ω => TmRichN1 γ r R (L + γ * φ 0) (localZ X r ω, circData α fun _ => 0)) =
        fun ω => TmRichN1 γ r R L (localZ X r ω, circData α fun _ => φ 0) :=
      funext fun ω => TmRichN1_congr (locModel_circData_const hγ.ne' α L r (φ 0) _).symm
    show TV.tvDist (P.map fun ω => TmRichN1 γ r R (L + γ * φ 0)
      (localZ X r ω, circData α fun _ => 0)) ν = _
    rw [e]
  have hsum := h1.add h2'
  rw [add_zero] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) (fun L => TV.tvDist_triangle)

/-- **`D3PlusIN2RichStmt` from the N1-form fixed-correction zoom and the macroscopic
decomposition.** -/
theorem d3PlusIN2Rich_of_tm (hT : D3PlusIN2TmStmt) (hMac : D3PlusIN2FixMacroStmt) :
    D3PlusIN2RichStmt := by
  intro γ α r ρ₀ Ω _ P _ X E' _ Ξ g Ω' _ P' _ Y' hS hW R
  filter_upwards [hMac γ α r ρ₀ P X Ξ g hS] with ω hω
  obtain ⟨φ, hφ, hdec⟩ := hω
  refine (hT γ α r P X P' Y' φ hS.hγ hS.hγ2 hS.hr hS.hX hW hφ R).congr fun L => ?_
  have hTm : Measurable fun s => TmRichN1 γ r R L (s, macroF α r ρ₀ X g ω) :=
    (measurable_TmRichN1 γ r R L).comp (measurable_id.prodMk measurable_const)
  have e : (fun ω₁ => TmRichN1 γ r R L (localZ X r ω₁, circData α φ)) =
      (fun s => TmRichN1 γ r R L (s, macroF α r ρ₀ X g ω)) ∘ localZ X r :=
    funext fun ω₁ => TmRichN1_congr (locModel_congr_circ fun μ hμ => (hdec μ hμ).2.symm)
  rw [Measure.map_map hTm (measurable_localZ hS.hX hS.hr), e]

/-- **Node N2 (rich) from the remaining nodes.** -/
theorem d3PlusIN2Rich_of_nodes (hZ : D3PlusIN2TmZeroStmt) (hCMI : CMIncrStmt)
    (hSc : D3PlusIN2FixScaleStmt) (hMac : D3PlusIN2FixMacroStmt) : D3PlusIN2RichStmt :=
  d3PlusIN2Rich_of_tm (d3PlusIN2Tm_of_parts hZ (d3PlusIN2FixCMLoc_of_parts hCMI n2Cutoff_holds)
    hSc) hMac

end D3Plus
end QuantumZipper
