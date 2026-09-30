import QuantumZipper.Proofs.Thm18.G3ZqG3Unif
import QuantumZipper.Proofs.Thm18.G3ZqIdent
import QuantumZipper.Proofs.Thm18.G3ZqGood
import QuantumZipper.Proofs.Thm18.G3ZqWireU
import QuantumZipper.Proofs.Thm18.G3Z2b2Dil2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH (13): the fixed-path two-point Palm limit from the map-zoom layers (D92)

Assembly of `G3ZqPathSmallUStmt` (G3ZqWireU) from
* the generalized G3 layer `R18.g3UnscaledTransferZ_unif` (G3ZqG3Unif; the window bound `U₀` is
  chosen before the zooms), instantiated with the zooms through the local maps of a good path,
* the map mixing body with the wedge law `g3FixMixBody_map` (G3ZqBody; leaves `G3ZqFixXStmt`,
  `G3ZqFixRStmt`, `G3ZqZoomLocStmt`),
* the identification of the plain limit `plain_limit_eq` (G3ZqIdent: `c = 𝒲(s) 𝒲(t)`),
* the bridge `g3PhiM2_eq_plPhiZ`: on a good field whose length partners are positive, the
  measurable fixed-path functional `g3PhiM2` is the abstract-zoom functional `g3plPhiZ` of the
  map zooms.

The locality hypotheses of the generalized G3 layer for the map zooms are kept as explicit
hypotheses of the assembly (their reduction is in progress, G3ZqG3*). Own bookkeeping
(Sheffield, arXiv:1012.4797, pp. 65–66 and 71).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zq

open G3Z2b2 G1Zm

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- **Bridge: the measurable fixed-path functional is the map-zoom functional.** -/
theorem g3PhiM2_eq_plPhiZ {γ L U : ℝ} {s t : Set LawD} {y : FieldSample} (hy : IsLQGGood γ y)
    (hpos : ∀ x : ℝ, x < 0 → 0 < R18.g3zPartner γ y x) (a : ℝ≥0 → ℝ) :
    g3PhiM2 γ L Ψ U s t (y, a) =
      R18.g3plPhiZ (g3zMapZ γ Ψ true a) (g3zMapZ γ Ψ false a) γ L U s t y := by
  classical
  have hbM : bdryM γ y = qBoundaryMeasure γ y := by
    unfold bdryM; rw [if_pos (G4Core.bCert_of_isLQGGood hy)]
  have hhalf : MeasurableSet (g1SideHalf true) := measurableSet_Iio
  have hwin := measurableSet_g1zWedgeWin γ true y U
  unfold g3PhiM2 R18.g3plPhiZ
  rw [hbM, Measure.restrict_restrict hwin, ← lintegral_indicator (hwin.inter hhalf)]
  refine lintegral_congr fun x => ?_
  have hmem : x ∈ g1zWedgeWin γ true y U ↔
      (x ∈ g1SideHalf true ∧ qBoundaryMeasure γ y (g1SideSeg true x) ≤ ENNReal.ofReal U) :=
    Iff.rfl
  have hpart : partM γ y x = R18.g3zPartner γ y x := by simp only [partM, R18.g3zPartner, hbM]
  by_cases hx : x ∈ g1zWedgeWin γ true y U
  · have hxh : x ∈ g1SideHalf true := hx.1
    rw [indicator_of_mem (show x ∈ g1zWedgeWin γ true y U ∩ g1SideHalf true from ⟨hx, hxh⟩)]
    have hp : R18.g3zPartner γ y x ∈ g1SideHalf false := by
      simpa [g1SideHalf] using hpos x hxh
    simp only [g3IntM2, hbM]
    rw [if_pos (hmem.1 hx), hpart]
    simp only [g3zMapZ, if_pos hxh, if_pos hp]
  · rw [indicator_of_notMem (fun h => hx h.1)]
    simp only [g3IntM2, hbM]
    rw [if_neg (fun h => hx (hmem.2 h))]

/-- **A.s. facts of the unscaled wedge**: good, and positive length partners at every `x < 0`. -/
theorem ae_wedgeU_good_pos {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P') :
    ∀ᵐ ω' ∂P', IsLQGGood γ (wedgeU γ X A ω') ∧
      ∀ x : ℝ, x < 0 → 0 < R18.g3zPartner γ (wedgeU γ X A ω') x := by
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
    LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hαQ Ω' _ P' X A inferInstance hX hA hXA,
    G1RC.ae_scale_pos hγ hγ2 hX hA hXA] with ω' ⟨hatom, hpos⟩ hRinf hg hb
  have hgU : IsLQGGood γ (wedgeU γ X A ω') := hg
  refine ⟨hgU, fun x hx => ?_⟩
  set b := scaleParam γ (wedgeU γ X A ω') with hbdef
  have hb' : 0 < b := hb
  have hx' : x / b < 0 := div_neg_of_neg_of_pos hx hb'
  have hR : 0 < R18.g3zPartner γ (wedgeRep γ X A ω') (x / b) := by
    refine R18.g3_lenRight_pos (hatom 0) hRinf
      (fun c => qBoundaryMeasure_Icc_lt_top γ _ 0 c) ?_
    exact ENNReal.toReal_pos
      (lt_of_lt_of_le (hpos (x / b) 0 hx') (measure_mono Ioo_subset_Icc_self)).ne'
      (qBoundaryMeasure_Icc_lt_top γ _ (x / b) 0).ne
  have e : wedgeRep γ X A ω' = rescale (wedgeU γ X A ω') (Qc γ) b := rfl
  rw [e, G3Z2b2.g3zPartner_rescale hγ hgU hb' x] at hR
  exact (div_pos_iff_of_pos_right hb').1 hR

/-- ENNReal-to-real arithmetic of the assembly. Own elementary proof. -/
theorem abs_toReal_div_sub_le {J : ℝ≥0∞} {U c e : ℝ} (hU : 0 < U) (hc : 0 ≤ c) (he : 0 < e)
    (hJ : J ≤ ENNReal.ofReal U) (h1 : (ENNReal.ofReal U)⁻¹ * J ≤ ENNReal.ofReal c + ENNReal.ofReal e)
    (h2 : ENNReal.ofReal c ≤ (ENNReal.ofReal U)⁻¹ * J + ENNReal.ofReal e) :
    |J.toReal / U - c| ≤ e := by
  have hJt : J ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hJ
  have hx0 : 0 ≤ J.toReal / U := div_nonneg ENNReal.toReal_nonneg hU.le
  have key : (ENNReal.ofReal U)⁻¹ * J = ENNReal.ofReal (J.toReal / U) := by
    rw [← ENNReal.ofReal_toReal hJt, ← ENNReal.ofReal_inv_of_pos hU,
      ← ENNReal.ofReal_mul (inv_nonneg.2 hU.le), ENNReal.toReal_ofReal ENNReal.toReal_nonneg,
      inv_mul_eq_div]
  rw [key, ← ENNReal.ofReal_add hc he.le] at h1
  rw [key, ← ENNReal.ofReal_add hx0 he.le] at h2
  have h1' := (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h1
  have h2' := (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h2
  rw [abs_le]; constructor <;> linarith

end G3Zq
end Thm18Asm
end QuantumZipper
