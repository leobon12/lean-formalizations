import QuantumZipper.Proofs.Zipper.LocLenR5aFlow
import QuantumZipper.Proofs.Zipper.CfgBatchScale
import QuantumZipper.Proofs.Zipper.TruncFreeCore
import QuantumZipper.Proofs.Zipper.LocLenF2Step4
import QuantumZipper.Proofs.Zipper.LocLenF2Loc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R5a (D75): the open-arc total left length of the `Γ⁰` sample is infinite, up to the law node

Open-arc copy of the LEN-INF argument of LenInfCore.lean (own argument there; Sheffield
arXiv:1012.4797 §5.4 uses the fact without proof):

* `lenTotArc`, `CfgNormLenLawArcStmt` (copy of `E6.CfgNormLenLawStmt`: the law of the total
  open-arc left length of a normalized `Γ⁰` sample is universal);
* `ae_lenFstArc_addConst` (copy of `E6.cfgB_ae_lenFst_addConst`, rule (5.1), with
  `arcLen_addConst`), `ae_unzipLengthsArc_rawRescale` (LocLenF2Step4, R7-S14);
* `cfgLenScaleNormArc` (copy of `E6.cfgLenScaleNormStmt_of_raw`) from the proved
  `scaleGeomAeLoc_of_yMergeOffTip` (R4d) and `unzipLengthsArc_scale` (R7-S14);
* `ae_lenTotArc_pos` (from `b5UniformArcStmt_holds` at time `1` and `Wire2.ae_nu0_regular`);
* `cfgLenInfArc_of_law`: `CfgLenInfArcStmt` from `CfgNormLenLawArcStmt` via the proved
  zero-infinity lemma `E6.ae_eq_top_of_drift` and the proved semicircle drift
  `E6.semicircleDriftStmt_holds`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open B2 E1 D3Plus E6 RegUnif

/-- Total left open-arc length of a configuration. -/
def lenTotArc (κ : ℝ) (c : FieldSample × (ℝ → ℝ)) : ℝ≥0∞ :=
  ⨆ t ∈ Ici (0 : ℝ), (unzipLengthsArc (Real.sqrt κ) c t).1

/-- Open-arc copy of `E6.CfgNormLenLawStmt` (CfgBatch/LenInfCore.lean). -/
def CfgNormLenLawArcStmt (κ : ℝ) : Prop :=
  0 < κ → κ < 4 →
  ∀ {Ω₁ : Type} [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (B₁ : ℝ≥0 → Ω₁ → ℝ) (X₁ : Ω₁ → FieldSample)
    {Ω₂ : Type} [MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (B₂ : ℝ≥0 → Ω₂ → ℝ) (X₂ : Ω₂ → FieldSample),
    IsBrownianReal B₁ P₁ → IsFreeGFFModConstH X₁ P₁ → IndepFun (pathOf B₁) X₁ P₁ →
    (∀ᵐ ω ∂P₁, X₁ ω (foldedCircle 0 1) = 0) →
    IsBrownianReal B₂ P₂ → IsFreeGFFModConstH X₂ P₂ → IndepFun (pathOf B₂) X₂ P₂ →
    (∀ᵐ ω ∂P₂, X₂ ω (foldedCircle 0 1) = 0) →
    AEMeasurable (fun ω => lenTotArc κ (cfg κ B₁ X₁ ω)) P₁ ∧
      P₁.map (fun ω => lenTotArc κ (cfg κ B₁ X₁ ω)) =
        P₂.map (fun ω => lenTotArc κ (cfg κ B₂ X₂ ω))

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Rule (5.1) for the left open-arc length of `Γ⁰`** (copy of `E6.cfgB_ae_lenFst_addConst`). -/
theorem ae_lenFstArc_addConst {κ : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ c : ℝ,
      (unzipLengthsArc (Real.sqrt κ) (addConst (cfg κ B X ω).1 c, drive κ B ω) t).1 =
        ENNReal.ofReal (Real.exp (Real.sqrt κ * c / 2)) *
          (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) t).1 := by
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ s ∈ Icc (0 : ℝ) ((n : ℝ) + 1),
      (∀ k : ℕ, ∀ d ∈ Dy, E1.RegShift (cfg κ B X ω).1
        ((foldedCircle d (radius k)).map (fwdMapInv (drive κ B ω) s))) ∧
        Cor15Group.BdryConvAE (h0f κ s B X ω) :=
    ae_all_iff.2 fun n => gaugeRegDyStmt_holds (κ := κ) (T := (n : ℝ) + 1) hB hX hind
      (by positivity)
  filter_upwards [hall, RegUnif.ae_forall_isRegularSample (κ := κ) (γ := Real.sqrt κ) hB hX hind]
    with ω h hreg t ht c
  obtain ⟨hR, -⟩ := h ⌈t⌉₊ t ⟨ht, by linarith [Nat.le_ceil t]⟩
  have hav : avgReg (unzippedField (Real.sqrt κ) (addConst (cfg κ B X ω).1 c, drive κ B ω) t) =
      avgReg (addConst (unzippedField (Real.sqrt κ) (cfg κ B X ω) t) c) :=
    avgReg_coordChange_addConst_dy (ψ := fwdMapInv (drive κ B ω) t) (Q := Qc (Real.sqrt κ)) hR
  show arcLen (Real.sqrt κ) (unzippedField (Real.sqrt κ) (addConst (cfg κ B X ω).1 c,
      drive κ B ω) t) (sideImages (drive κ B ω) t).1 0 =
    ENNReal.ofReal (Real.exp (Real.sqrt κ * c / 2)) *
      arcLen (Real.sqrt κ) (unzippedField (Real.sqrt κ) (cfg κ B X ω) t)
        (sideImages (drive κ B ω) t).1 0
  rw [arcLen_congr hav]
  exact arcLen_addConst (x := unzippedField (Real.sqrt κ) (cfg κ B X ω) t)
    (fun k z _ => (hreg t ht).2 k z trivial) _ _ _

/-- **Scaling and normalization identity, open arcs** (copy of
`E6.cfgLenScaleNormStmt_of_raw` with `ScaleGeomAeLocStmt'`, proved). -/
theorem cfgLenScaleNormArc {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ a : ℝ, 1 ≤ a → ∃ X' : Ω → FieldSample,
      IsBrownianReal (F2.bmScale (Real.toNNReal (a ^ 2)) B) P ∧ IsFreeGFFModConstH X' P ∧
      IndepFun (pathOf (F2.bmScale (Real.toNNReal (a ^ 2)) B)) X' P ∧
      (∀ᵐ ω ∂P, X' ω (foldedCircle 0 1) = 0) ∧
      ∀ᵐ ω ∂P, lenTotArc κ (cfg κ B X ω) = ENNReal.ofReal (Real.exp (driftC κ a (X ω))) *
        lenTotArc κ (cfg κ (F2.bmScale (Real.toNNReal (a ^ 2)) B) X' ω) := by
  intro a ha1
  have ha : 0 < a := by linarith
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hcR : ((Real.toNNReal (a ^ 2) : ℝ≥0) : ℝ) = a ^ 2 := Real.coe_toNNReal _ (sq_nonneg a)
  have hc0 : Real.toNNReal (a ^ 2) ≠ 0 := by
    intro h
    have : ((Real.toNNReal (a ^ 2) : ℝ≥0) : ℝ) = 0 := by rw [h]; rfl
    rw [hcR] at this
    exact (pow_pos ha 2).ne' this
  have hY : IsFreeGFFModConstH (fun ω => F2.rawRescale (X ω) (Qc (Real.sqrt κ)) a) P :=
    F2.isFreeGFFModConstH_rawRescale hX (Qc (Real.sqrt κ)) ha
  have hmm : Measurable fun ω =>
      F2.rawRescale (X ω) (Qc (Real.sqrt κ)) a InfMass.fc01 :=
    hY.measurable_coord _
  -- the normalization map on field samples
  have hΨ : Measurable fun y : FieldSample => addConst y (-(y InfMass.fc01)) := by
    refine measurable_pi_iff.2 fun μ => ?_
    simp only [addConst]
    exact (measurable_pi_apply μ).add ((measurable_pi_apply _).neg.mul_const _)
  have hX' : IsFreeGFFModConstH (fun ω => addConst
      (F2.rawRescale (X ω) (Qc (Real.sqrt κ)) a)
      (-(F2.rawRescale (X ω) (Qc (Real.sqrt κ)) a InfMass.fc01))) P :=
    S5.FieldLaw.Raw.isFreeGFFModConstH_addConst hY hmm.neg
  have hB' : IsBrownianReal (F2.bmScale (Real.toNNReal (a ^ 2)) B) P := hB.smul hc0
  have hind' : IndepFun (pathOf (F2.bmScale (Real.toNNReal (a ^ 2)) B)) (fun ω => addConst
      (F2.rawRescale (X ω) (Qc (Real.sqrt κ)) a)
      (-(F2.rawRescale (X ω) (Qc (Real.sqrt κ)) a InfMass.fc01))) P := by
    have hΦ : Measurable fun b : ℝ≥0 → ℝ => (fun t : ℝ≥0 =>
        (√(Real.toNNReal (a ^ 2) : ℝ))⁻¹ * b (Real.toNNReal (a ^ 2) * t)) := by
      rw [measurable_pi_iff]
      exact fun t => measurable_const.mul (measurable_pi_apply _)
    exact (F2.indepFun_rawRescale hind (Qc (Real.sqrt κ)) a).comp hΦ hΨ
  refine ⟨_, hB', hX', hind', ae_of_all _ fun ω => ?_, ?_⟩
  · simp only [addConst, InfMass.fc01, measure_univ, ENNReal.toReal_one, mul_one, add_neg_cancel]
  -- the a.s. identity
  filter_upwards [scaleGeomAeLoc_of_yMergeOffTip SWCore.yMergeOffTipStmt_holds κ hκ hκ4 P B X
      hB hX hind a ha, ae_lenFstArc_addConst (κ := κ) hB' hX' hind',
    ae_unzipLengthsArc_rawRescale hX (Real.sqrt κ) (Qc (Real.sqrt κ)) ha (h0rev κ)
      (2 / Real.sqrt κ * Real.log a)] with ω hω hC hraw
  set E := ENNReal.ofReal (Real.exp (driftC κ a (X ω))) with hE
  have h2 : (√((Real.toNNReal (a ^ 2) : ℝ≥0) : ℝ))⁻¹ = a⁻¹ := by
    rw [hcR, Real.sqrt_sq ha.le]
  have hdrv : drive κ (F2.bmScale (Real.toNNReal (a ^ 2)) B) ω =
      fun s => drive κ B ω (a ^ 2 * s) / a := by
    funext r
    rw [F2.drive_bmScale_all κ _ B ω r, h2, hcR, div_eq_mul_inv]
    ring
  -- the constant
  have hconst : Real.sqrt κ *
      (F2.rawRescale (X ω) (Qc (Real.sqrt κ)) a InfMass.fc01 +
        2 / Real.sqrt κ * Real.log a) / 2 = driftC κ a (X ω) := by
    rw [InfMass.fc01, F2.rawRescale_apply_prob, driftC, InfMass.fc01]
    field_simp
    ring
  have hstep : ∀ t : ℝ, 0 ≤ t →
      (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) (a ^ 2 * t)).1 =
        E * (unzipLengthsArc (Real.sqrt κ) (cfg κ (F2.bmScale (Real.toNNReal (a ^ 2)) B)
          (fun ω => addConst (F2.rawRescale (X ω) (Qc (Real.sqrt κ)) a)
            (-(F2.rawRescale (X ω) (Qc (Real.sqrt κ)) a InfMass.fc01))) ω) t).1 := by
    intro t ht
    obtain ⟨hgood, hL, hR, hfield⟩ := hω t ht
    have hsc := unzipLengthsArc_scale hγ ha ht hL hR hgood hfield
    have hfeq : ofFun (h0rev κ) + addConst (F2.rawRescale (X ω) (Qc (Real.sqrt κ)) a)
        (2 / Real.sqrt κ * Real.log a) =
        addConst (cfg κ (F2.bmScale (Real.toNNReal (a ^ 2)) B)
          (fun ω => addConst (F2.rawRescale (X ω) (Qc (Real.sqrt κ)) a)
            (-(F2.rawRescale (X ω) (Qc (Real.sqrt κ)) a InfMass.fc01))) ω).1
          (F2.rawRescale (X ω) (Qc (Real.sqrt κ)) a InfMass.fc01 +
            2 / Real.sqrt κ * Real.log a) := by
      funext μ
      simp only [cfg, addConst, Pi.add_apply]
      ring
    have hcfg : cfg κ B X ω = (ofFun (h0rev κ) + X ω, drive κ B ω) := rfl
    rw [hcfg, ← hsc, ← hraw, hfeq, ← hdrv, hC t ht, hconst]
  show (⨆ s ∈ Ici (0 : ℝ), (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) s).1) =
    E * ⨆ t ∈ Ici (0 : ℝ), _
  rw [cfgB_iSup_Ici_mul (pow_pos ha 2), ENNReal.mul_iSup]
  refine iSup_congr fun t => ?_
  rw [ENNReal.mul_iSup]
  exact iSup_congr fun ht => hstep t ht

/-- **Positivity of the total left open-arc length.** -/
theorem ae_lenTotArc_pos {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, 0 < lenTotArc κ (cfg κ B X ω) := by
  filter_upwards [b5UniformArcStmt_holds κ hκ hκ4 1 one_pos P B X hB hX hind,
    Wire2.ae_nu0_regular (T := 1) hκ hκ4 one_pos hB hX hind,
    Wire2.ae_zeroMinus_Vr_facts hκ hκ4.le one_pos P B hB] with ω hU hν hzm
  have h1 := (hU 1 ⟨zero_le_one, le_rfl⟩).1
  rw [sub_self, hzm.1] at h1
  have hpos : 0 < (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) 1).1 := by
    rw [h1]; exact hν.2.1 _ _ hzm.2.1
  exact hpos.trans_le (le_iSup₂_of_le (f := fun t (_ : t ∈ Ici (0 : ℝ)) =>
    (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) t).1) 1 (mem_Ici.2 zero_le_one) le_rfl)

/-- **`CfgLenInfArcStmt` from the universal-law node** (copy of `E6.cfgLenInfStmt_of_parts`). -/
theorem cfgLenInfArc_of_law (hL : ∀ κ : ℝ, CfgNormLenLawArcStmt κ) : CfgLenInfArcStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  show ∀ᵐ ω ∂P, lenTotArc κ (cfg κ B X ω) = ⊤
  have hS := cfgLenScaleNormArc hκ hκ4 hB hX hind
  obtain ⟨X₁, hB₁, hX₁, hi₁, hn₁, he₁⟩ := hS 1 le_rfl
  refine ae_eq_top_of_drift
    (T := fun ω => lenTotArc κ (cfg κ (F2.bmScale (Real.toNNReal (1 ^ 2)) B) X₁ ω))
    (hL κ hκ hκ4 P _ X₁ P _ X₁ hB₁ hX₁ hi₁ hn₁ hB₁ hX₁ hi₁ hn₁).1 ?_ ?_
  · filter_upwards [ae_lenTotArc_pos hκ hκ4 hB hX hind, he₁] with ω hp he
    rw [he] at hp
    refine pos_iff_ne_zero.2 fun h0 => ?_
    rw [h0, mul_zero] at hp
    exact lt_irrefl _ hp
  · intro K ε hε
    obtain ⟨a, ha, hc⟩ := semicircleDriftStmt_holds κ hκ P X hX K ε hε
    obtain ⟨X', hB', hX', hi', hn', he'⟩ := hS a ha
    obtain ⟨hm, hlaw⟩ := hL κ hκ hκ4 P _ X' P _ X₁ hB' hX' hi' hn' hB₁ hX₁ hi₁ hn₁
    exact ⟨fun ω => driftC κ a (X ω), _, hm, hlaw, he', hc⟩

/-- **`E6PalmRegArcStmt` from the universal-law node.** -/
theorem e6PalmRegArc_of_law (hL : ∀ κ : ℝ, CfgNormLenLawArcStmt κ) : E6PalmRegArcStmt :=
  e6PalmRegArc_of_lenInf (cfgLenInfArc_of_law hL)

end LocLen
end QuantumZipper
