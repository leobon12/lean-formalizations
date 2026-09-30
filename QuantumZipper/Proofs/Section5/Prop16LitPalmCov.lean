import QuantumZipper.Proofs.Section5.Prop16LitPalmCovLoc
import QuantumZipper.Proofs.Section5.Prop16BdryMomMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: clause (1) under the weighted law from the fixed-point form

`Prop16Lit.prop16LitCov1Stmt_of_fix`: `Prop16LitCov1Stmt` from `Prop16LitFixCov1Stmt` (the chart
identity at a fixed `x ∈ (a,b)` for the Palm-shifted field) and the deterministic measurability
node `Prop16LitRepMeasStmt` (the set of readings `(y, x)` of the local dyadic circles for which
the identity holds, for the field rebuilt from `y`, is Borel).

Argument: the Palm formula (`Prop16Asm.prop16PalmGlobalStmt_holds_bdryMom`; Duplantier–Sheffield,
arXiv:0808.1560, §3.3, p. 22) applied to the indicator of the complement of that set, exactly as
in `Prop16Asm.prop16PalmWinMaskStmt_of_rep`. The identity only reads the field through the local
circles (`litIdent_congr`), so for both the field `h0 + X` and the Palm-shifted field it is
equivalent to the identity for the rebuilt field. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Lit

open Prop16Asm

/-- **Palm transfer of a Borel property of the local readings.** If a Borel set `S` of readings
`(y, x)` contains the Palm-shifted readings at every fixed `x ∈ (a,b)` `P`-a.s., then it contains
the readings of `h0 + X` at the weighted point `prop16Q`-a.s. (Palm formula,
`prop16PalmGlobalStmt_holds_bdryMom`; the argument of `prop16PalmWinMaskStmt_of_rep`). -/
theorem ae_readings_of_palm {γ : ℝ} {D : Set ℂ} {c d a b : ℝ} {h0 : ℂ → ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample} (hdat : Prop16Data γ D c d a b h0 P X)
    {S : Set ((ℕ → ℝ) × ℝ)} (hS : MeasurableSet S)
    (hpalm : ∀ x ∈ Ioo a b, ∀ᵐ ω ∂P,
      (palmRawCoords γ D c d h0 X (repMeas D a b) (ω, x), x) ∈ S) :
    ∀ᵐ p ∂(prop16Q γ h0 a b P X), p.2 ∈ Ioo a b →
      (rawCoords h0 X (repMeas D a b) p.1, p.2) ∈ S := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, hX, hpos, hfin⟩ := id hdat
  have hN := prop16LocNiceStmt_of_coupling prop16MixedFreeLocCoupling_mm γ D c d a b h0 P X hdat
  have hν := prop16NuMeasStmt_of_loc (prop16LocGoodStmt_of_coupling prop16MixedFreeLocCoupling_mm)
    γ D c d a b h0 P X hdat
  have hH : Prop16PalmHyp γ D c d a b h0 P X := ⟨hdat, hν, hN⟩
  obtain ⟨-, hPG⟩ := prop16PalmGlobalStmt_holds_bdryMom γ D c d a b h0 P X hH (repMeas D a b)
    (locAdm_repMeas D a b)
  -- the weighted side, on windows
  set ν : Ω → Measure ℝ := fun ω => prop16Nu γ h0 a b (X ω) with hνdef
  have hraw : Measurable (rawCoords h0 X (repMeas D a b)) :=
    measurable_coords_mixed hX h0 (repMeas D a b)
  set Y' : Ω × ℝ → (ℕ → ℝ) × ℝ := fun p => (rawCoords h0 X (repMeas D a b) p.1, p.2) with hY'def
  have hY' : Measurable Y' := (hraw.comp measurable_fst).prodMk measurable_snd
  have hG : Measurable fun q : (ℕ → ℝ) × ℝ => Sᶜ.indicator (1 : (ℕ → ℝ) × ℝ → ℝ≥0∞) q :=
    measurable_one.indicator hS.compl
  have hpre : palmPre P ν a b = (∫⁻ ω, ν ω (Icc a b) ∂P) • prop16Q γ h0 a b P X := by
    rw [show prop16Q γ h0 a b P X = _ from prop16Law_eq_smul_palmPre, smul_smul,
      ENNReal.mul_inv_cancel hpos.ne' hfin.ne, one_smul]
  have hwin : ∀ a' b' : ℝ, a < a' → b' < b →
      prop16Q γ h0 a b P X (Y' ⁻¹' Sᶜ ∩ univ ×ˢ Ioo a' b') = 0 := by
    intro a' b' ha' hb'
    have hW : MeasurableSet (univ ×ˢ Ioo a' b' : Set (Ω × ℝ)) :=
      MeasurableSet.univ.prod measurableSet_Ioo
    have hSm : MeasurableSet (Y' ⁻¹' Sᶜ ∩ univ ×ˢ Ioo a' b') := (hY' hS.compl).inter hW
    have hsub : Ioo a' b' ⊆ Icc a b := Ioo_subset_Icc_self.trans (Icc_subset_Icc ha'.le hb'.le)
    have hL : ∀ᵐ ω ∂P, (Measure.dirac ω).prod ((ν ω).restrict (Icc a b))
        (Y' ⁻¹' Sᶜ ∩ univ ×ˢ Ioo a' b') =
        ∫⁻ x in Ioo a' b', Sᶜ.indicator 1 (rawCoords h0 X (repMeas D a b) ω, x) ∂(ν ω) := by
      filter_upwards [ae_nu_ne_top hν hfin] with ω hω
      have : IsFiniteMeasure ((ν ω).restrict (Icc a b)) := isFiniteMeasure_restrict.mpr hω
      have hT : MeasurableSet ((fun x => (rawCoords h0 X (repMeas D a b) ω, x)) ⁻¹' Sᶜ) :=
        (measurable_const.prodMk measurable_id) hS.compl
      have e : Prod.mk ω ⁻¹' (Y' ⁻¹' Sᶜ ∩ univ ×ˢ Ioo a' b') =
          (fun x => (rawCoords h0 X (repMeas D a b) ω, x)) ⁻¹' Sᶜ ∩ Ioo a' b' := by
        ext x; simp [Y']
      rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hSm, e,
        Measure.restrict_apply (hT.inter measurableSet_Ioo), inter_assoc,
        inter_eq_left.2 hsub,
        indicator_one_comp_eq (fun x => (rawCoords h0 X (repMeas D a b) ω, x)) Sᶜ,
        lintegral_indicator_one hT, Measure.restrict_apply hT]
    have hzero : palmPre P ν a b (Y' ⁻¹' Sᶜ ∩ univ ×ˢ Ioo a' b') = 0 := by
      rw [palmPre, Measure.bind_apply hSm (aemeasurable_prop16Kernel hν hfin),
        lintegral_congr_ae hL, hPG a' b' ha' hb' _ hG]
      have h0' : ∀ x ∈ Ioo a' b', ∫⁻ ω, Sᶜ.indicator (1 : (ℕ → ℝ) × ℝ → ℝ≥0∞)
          (palmRawCoords γ D c d h0 X (repMeas D a b) (ω, x), x) ∂P = 0 := by
        intro x hx
        have hx' : x ∈ Ioo a b := ⟨ha'.trans hx.1, hx.2.trans hb'⟩
        rw [lintegral_congr_ae (g := fun _ => (0 : ℝ≥0∞)) ?_, lintegral_zero]
        filter_upwards [hpalm x hx'] with ω hω
        exact indicator_of_notMem (fun h => (mem_compl_iff _ _).1 h hω) _
      rw [lintegral_congr_ae (g := fun _ => (0 : ℝ≥0∞))
        ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ h0')), lintegral_zero]
    rw [hpre, Measure.smul_apply, smul_eq_mul] at hzero
    exact (mul_eq_zero.1 hzero).resolve_left hpos.ne'
  -- exhaust `(a,b)` by windows
  have hQ : prop16Q γ h0 a b P X (Y' ⁻¹' Sᶜ ∩ univ ×ˢ Ioo a b) = 0 := by
    refine measure_mono_null (t := ⋃ n : ℕ, (Y' ⁻¹' Sᶜ ∩
      univ ×ˢ Ioo (a + 1 / ((n : ℝ) + 1)) (b - 1 / ((n : ℝ) + 1)))) ?_
      (measure_iUnion_null fun n => hwin _ _ (by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith) (by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith))
    rintro p ⟨hp1, -, hp2⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min (sub_pos.2 hp2.1) (sub_pos.2 hp2.2))
    refine mem_iUnion.2 ⟨n, hp1, mem_univ _, ?_, ?_⟩
    · have := (lt_min_iff.1 hn).1; linarith
    · have := (lt_min_iff.1 hn).2; linarith
  refine ae_iff.2 (measure_mono_null (fun p hp => ?_) hQ)
  simp only [mem_ofPred_eq, not_imp] at hp
  exact ⟨hp.2, mem_univ _, hp.1⟩

end Prop16Lit

end QuantumZipper
