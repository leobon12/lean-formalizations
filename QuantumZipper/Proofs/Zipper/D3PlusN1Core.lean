import QuantumZipper.Proofs.Zipper.D3PlusN1Scale
import QuantumZipper.Proofs.Zipper.LocRichD3
import QuantumZipper.Proofs.Wire2b

/-!
# D3⁺(i), node N1 (part 4): factorization and measurability; reduction of the core node to N2

With `ε₀ = r/(R+1)`, `T = FieldSample`, `F = macroF α r ρ₀ X g` and `Tm = TmN1 γ r R`
(resp. `TmRichN1` for D25's rich data):

* (b) `locField_canonicalOn_eq_TmN1`, `locFieldFull_canonicalOn_eq_TmRichN1`: for **every** `ω`
  outside `badScale`, the local canonical data of the model field equal `Tm L (localZ X r ω, F ω)`
  (locality `AgreeNear` + measurable surrogate of the scale, equal to the true scale since the
  latter is positive);
* (a) `nullMeasurableSet_badScale`: a.s. the local area measure of every `Y_L` exists
  (`LocalRule.isVagueLimitOn_add_ofFun`, as in `d3PlusIII_holds`), so `badScale` is a.e. equal to
  the measurable event `{¬ 0 < scaleSur < ε₀}` pulled back by `(localZ, F)`;
* (c) `aemeasurable_locFieldFull_wedge`, `aemeasurable_locField_wedge`: from WEDGE-MEAS (1)
  (`Wire2.aemeasurable_dataFull_of_isQuantumWedge`).

`D3PlusIN2Stmt` is item (d) of `D3PlusICoreStmt` for this concrete `Tm` (node N2: TV
convergence of the zoom of the local part plus a fixed macroscopic correction), and
`d3PlusICore_of_N2 : D3PlusIN2Stmt → D3PlusICoreStmt`. `n1_rich` bundles (a)–(c) for D25's rich
data. Own elementary arguments (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace D3Plus

section Core

variable {γ α r : ℝ} {ρ₀ : Measure ℂ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Ω → FieldSample} {E' : Type*} [MeasurableSpace E'] {Ξ : Ω → E'} {g : Ω → ℂ → ℝ}

/-- Off `badScale`, the surrogate scale of `(localZ, F)` is the true local scale, which lies in
`(0, ε₀)`. -/
theorem scaleSur_eq_of_not_bad (hS : Setup γ α r ρ₀ P X Ξ g) {ε₀ L : ℝ} {ω : Ω}
    (hω : ω ∉ badScale γ α r ε₀ ρ₀ X g L) :
    scaleSur γ L r (localZ X r ω, macroF α r ρ₀ X g ω) =
        scaleParamOn γ (zoomModel γ α L ρ₀ (X ω) (g ω)) (halfDisc r) ∧
      0 < scaleParamOn γ (zoomModel γ α L ρ₀ (X ω) (g ω)) (halfDisc r) ∧
      scaleParamOn γ (zoomModel γ α L ρ₀ (X ω) (g ω)) (halfDisc r) < ε₀ := by
  have hag := agreeNear_zoomModel_locModel hS L ω
  have hsc := scaleParamOn_halfDisc_congr (γ := γ) hag
  simp only [badScale, mem_setOf_eq, not_not] at hω
  have hgood := mem_goodN1_of_pos (hsc ▸ hω.1)
  exact ⟨(scaleSur_eq hgood).trans hsc.symm, hω⟩

theorem mul_lt_of_lt_div_succ {s r : ℝ} {R : ℕ} (hs : 0 < s) (h : s < r / (R + 1)) :
    s * R < r := by
  have hR : (0 : ℝ) < R + 1 := by positivity
  have h' : s * (R + 1) < r := by rwa [lt_div_iff₀ hR] at h
  nlinarith

/-- **(b), D25 rich data.** -/
theorem locFieldFull_canonicalOn_eq_TmRichN1 (hS : Setup γ α r ρ₀ P X Ξ g) {R : ℕ} (L : ℝ)
    (ω : Ω) (hω : ω ∉ badScale γ α r (r / (R + 1)) ρ₀ X g L) :
    locFieldFull R (canonicalOn γ (zoomModel γ α L ρ₀ (X ω) (g ω)) (halfDisc r)) =
      TmRichN1 γ r R L (localZ X r ω, macroF α r ρ₀ X g ω) := by
  obtain ⟨h1, h2, h3⟩ := scaleSur_eq_of_not_bad hS hω
  unfold TmRichN1 zoomN1
  rw [h1, canonicalOn]
  exact locFieldFull_rescale_congr (agreeNear_zoomModel_locModel hS L ω) h2
    (mul_lt_of_lt_div_succ h2 h3)

/-- A.s. the local area measure of every model field exists (as in `d3PlusIII_holds`). -/
theorem ae_exists_isVagueLimitOn_zoomModel [IsProbabilityMeasure P]
    (hS : Setup γ α r ρ₀ P X Ξ g) :
    ∀ᵐ ω ∂P, ∀ L : ℝ, ∃ m, IsVagueLimitOn (halfDisc r)
      (areaApprox γ (zoomModel γ α L ρ₀ (X ω) (g ω))) m := by
  filter_upwards [AreaExist.ae_isVagueLimitOn_qAreaMeasure hS.hX hS.hγ hS.hγ2,
    AreaOffsets.ae_isLQGGood hS.hX hS.hγ hS.hγ2] with ω hvag hgood L
  have hg := continuousOn_g_of_harm (hS.harm ω)
  have hU := isOpen_halfDisc r
  have hres := AtomlessUncond.isVagueLimitOn_restrict hU (halfDisc_subset_H r) hvag
  have hW : IsOpen (Metric.ball (0 : ℂ) r \ {0}) := Metric.isOpen_ball.sdiff isClosed_singleton
  exact ⟨_, LocalRule.isVagueLimitOn_add_ofFun hgood.1 hU (halfDisc_subset_H r) hres hW
    (halfDisc_subset_ball_diff r) (continuousOn_zoomPot (γ := γ) (α := α) (L := L) (ρ₀ := ρ₀)
      (x := X ω) hg)⟩

theorem measurable_localZ_macroF (hS : Setup γ α r ρ₀ P X Ξ g) :
    Measurable fun ω => (localZ X r ω, macroF α r ρ₀ X g ω) :=
  (measurable_localZ hS.hX hS.hr).prodMk ((measurable_macroF hS).mono (condSigma_le hS) le_rfl)

/-- **(a)** The bad-scale events are null-measurable. -/
theorem nullMeasurableSet_badScale [IsProbabilityMeasure P] (hS : Setup γ α r ρ₀ P X Ξ g)
    (ε₀ L : ℝ) : NullMeasurableSet (badScale γ α r ε₀ ρ₀ X g L) P := by
  set B' : Set Ω := (fun ω => (localZ X r ω, macroF α r ρ₀ X g ω)) ⁻¹'
    {p | ¬ (0 < scaleSur γ L r p ∧ scaleSur γ L r p < ε₀)} with hB'def
  have hB' : MeasurableSet B' := measurable_localZ_macroF hS
    (((measurableSet_lt measurable_const (measurable_scaleSur γ L r)).inter
      (measurableSet_lt (measurable_scaleSur γ L r) measurable_const)).compl)
  refine hB'.nullMeasurableSet.congr ?_
  filter_upwards [ae_exists_isVagueLimitOn_zoomModel hS] with ω hω
  have hag := agreeNear_zoomModel_locModel hS L ω
  have hgood : (localZ X r ω, macroF α r ρ₀ X g ω) ∈ goodN1 γ L r :=
    (exists_isVagueLimitOn_halfDisc_iff hag).1 (hω L)
  have e := (scaleSur_eq hgood).trans (scaleParamOn_halfDisc_congr hag).symm
  show (ω ∈ B') = (ω ∈ badScale γ α r ε₀ ρ₀ X g L)
  simp only [hB'def, badScale, mem_preimage, mem_setOf_eq, e]

end Core

open Classical in
/-- Truncation of WEDGE-MEAS data to the rich local data at radius `R`. -/
def truncData (R : ℕ) (c : (ℕ → ℝ) × (TestFun H → ℝ)) : (ℕ → ℝ) × (TestFun H → ℝ) :=
  (fun i => if inBallFull R i then c.1 i else 0, fun ρ => if suppIn R ρ then c.2 ρ else 0)

theorem measurable_truncData (R : ℕ) : Measurable (truncData R) := by
  classical
  unfold truncData
  refine Measurable.prodMk (measurable_pi_iff.2 fun i => ?_) (measurable_pi_iff.2 fun ρ => ?_)
  · split_ifs
    · exact (measurable_pi_apply i).comp measurable_fst
    · exact measurable_const
  · split_ifs
    · exact (measurable_pi_apply ρ).comp measurable_snd
    · exact measurable_const

theorem locFieldFull_eq_truncData (R : ℕ) (y : FieldSample) :
    locFieldFull R y = truncData R (WedgeMeas.dataFull H y) := rfl

/-- **(c), rich data.** -/
theorem aemeasurable_locFieldFull_wedge {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type*}
    [MeasurableSpace Ω'] {P' : Measure Ω'} {Y' : Ω' → FieldSample}
    (hW : IsQuantumWedge γ α Y' P') (R : ℕ) :
    AEMeasurable (fun ω' => locFieldFull R (Y' ω')) P' := by
  simp only [locFieldFull_eq_truncData]
  exact (measurable_truncData R).comp_aemeasurable
    (Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hW.1 hW)

/-- **(c), D23 data.** -/
theorem aemeasurable_locField_wedge {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type*}
    [MeasurableSpace Ω'] {P' : Measure Ω'} {Y' : Ω' → FieldSample}
    (hW : IsQuantumWedge γ α Y' P') (R : ℕ) :
    AEMeasurable (fun ω' => TV.locField R (Y' ω')) P' := by
  simp only [locField_eq_projField]
  exact measurable_projField.comp_aemeasurable (aemeasurable_locFieldFull_wedge hγ hγ2 hW R)

/-- **N1 for D25's rich local data**: items (a)–(c) of the core node with `TmRichN1`. -/
theorem n1_rich {γ α r : ℝ} {ρ₀ : Measure ℂ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} {E' : Type*} [MeasurableSpace E']
    {Ξ : Ω → E'} {g : Ω → ℂ → ℝ} {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {Y' : Ω' → FieldSample} (hS : Setup γ α r ρ₀ P X Ξ g) (hW : IsQuantumWedge γ α Y' P')
    (R : ℕ) :
    0 < r / (R + 1) ∧ Measurable[condSigma Ξ X r] (macroF α r ρ₀ X g) ∧
      (∀ L, Measurable (TmRichN1 γ r R L)) ∧
      (∀ L, NullMeasurableSet (badScale γ α r (r / (R + 1)) ρ₀ X g L) P) ∧
      (∀ L, ∀ ω, ω ∉ badScale γ α r (r / (R + 1)) ρ₀ X g L →
        locFieldFull R (canonicalOn γ (zoomModel γ α L ρ₀ (X ω) (g ω)) (halfDisc r)) =
          TmRichN1 γ r R L (localZ X r ω, macroF α r ρ₀ X g ω)) ∧
      AEMeasurable (fun ω' => locFieldFull R (Y' ω')) P' :=
  ⟨div_pos hS.hr (by positivity), measurable_macroF hS, fun L => measurable_TmRichN1 γ r R L,
    fun L => nullMeasurableSet_badScale hS _ L,
    fun L ω hω => locFieldFull_canonicalOn_eq_TmRichN1 hS L ω hω,
    aemeasurable_locFieldFull_wedge hS.hγ hS.hγ2 hW R⟩

end D3Plus
end QuantumZipper
