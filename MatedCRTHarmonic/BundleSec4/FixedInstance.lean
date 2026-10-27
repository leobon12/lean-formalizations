import MatedCRTHarmonic.BundleSec4.RecEventually
import MatedCRTHarmonic.BundleSec4.Prop210Source
import MatedCRTHarmonic.Lemma38Source.MTC
import MatedCRTHarmonic.MesoModel.FinalAssembly
import MatedCRTHarmonic.GMS4.Prop210
import MatedCRTHarmonic.GMS4.CellGraphInterface
import MatedCRTHarmonic.MesoModel.RecAdmissible
import MatedCRTHarmonic.MesoModel.RecBridge

/-!
# The mated-CRT map conclusion from ONE fixed-parameter instance of [18] Proposition 2.10 (the producer shape)

The uniform Proposition 2.10 producer is instantiated once, as
`GMS4.UniformL27GMSAProp210Producer M S R (3/4) 100 betaG4 A α Cfail` (the one-scale estimate's instance). This file shows that this
single instance is ALL the endgame needs:

* `Prop210At F ρ C` — the per-test conclusion of `GMS4.proposition210_holds` at ambient radius `ρ` and test constant
  `C` (some `betaG4, α > 0`, `A, Cfail ≥ 0`, threshold `2A`, tolerance `mesh k ^ α`), i.e. exactly what one uniform
  producer gives (`prop210At_of_uniformProducer`) and exactly the one-scale estimate's premise at `(3/4, 100)`;
* `annulus38OneScaleBadBound_of_prop210At` — `hAnnulus38` at one coupling from `Prop210At F (3/4) 100` (the one-scale estimate);
* `matedCRTRecurrencePathScaleInput_of_prop210At` — `hREC` from `Prop210At F ρG4 C₀` for ANY `ρG4 ∈ (0, 1)`,
  `16π ≤ C₀` (in particular `(3/4, 100)`), through `RecEventually` (coarse scales absorbed into L27's constant);
* `exists_cellModel_of_matingOfTrees_of_prop210At`, the companion map conclusion — both frozen v3
  conclusions with `Prop210At M.coupled.family (3/4) 100` (MTC's family of every coupling) as the only remaining input.

`Prop210Source` (the source quantifier order) implies `Prop210At` at every admissible `(ρ, C)`
(`prop210At_of_source`), so these theorems are the weakest-input versions of `BundleSec4.Endgame`'s.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Real
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.BundleSec4

open MatedCRTHarmonic

/-- **One fixed-parameter instance of [18] Proposition 2.10** for `F` at ambient radius `ρ` and test constant `C`, in
The exact conclusion shape of G4's `GMS4.proposition210_holds` (threshold `2A`, tolerance `mesh k ^ α`). -/
def Prop210At (F : CellFamily.RandomCellFamily) (ρ C : ℝ) : Prop :=
  ∃ β A α Cfail : ℝ, 0 < β ∧ 0 < α ∧ 0 ≤ A ∧ 0 ≤ Cfail ∧
    ∀ (k : ℕ) (V : Set ℂ) (f : ℂ → ℝ), GMS4.Prop210Admissible (CellFamily.mesh k) ρ C β V f →
      F.P (GMS4.Prop210Bad F k V f (2 * A) (CellFamily.mesh k ^ α)) ≤
        ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α)

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **`hAnnulus38` at one coupling from the single instance `(3/4, 100)`** (the one-scale estimate). -/
theorem annulus38OneScaleBadBound_of_prop210At
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2)
    (h : Prop210At (MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family (3 / 4) 100) :
    MesoModel.Annulus38OneScaleBadBound (MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family
      (MoTInput.unitMesoModelOfCoupling D hstd hγ).ρ := by
  obtain ⟨β, A, α, Cfail, hβ, hα, hA, hCfail, h⟩ := h
  exact Lemma38Source.annulus38OneScaleBadBound_of_proposition210_at_mtc D hstd hγ hβ hα hA hCfail h

/-- **`hREC` at one coupling from a single instance** at any fixed `ρG4 ∈ (0, 1)`, `16π ≤ C₀`: L27 at radius
`ρ₁ = ρG4`, inner radius `ρ = ρG4/2`, exponents `α = min(α₀, α₂₇/2)`, `β = min(q, βG, α)/4`, `β' = min(q, βG)`, and the
coarse scales (`mesh k ^ β > ρ e^{-2}`) absorbed (`bundle_matedCRTRecurrenceScaleInput_of_eventually`). -/
theorem matedCRTRecurrencePathScaleInput_of_prop210At
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) {ρG4 C0 : ℝ}
    (hρ0 : 0 < ρG4) (hρ1 : ρG4 < 1) (hC0 : 16 * π ≤ C0)
    (h : Prop210At (MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family ρG4 C0) :
    MesoModel.MatedCRTRecurrencePathScaleInput γ := by
  obtain ⟨βG, A, α₀, Cfail, hβG, hα₀, hA, hCfail, h⟩ := h
  let M := MoTInput.unitMesoModelOfCoupling D hstd hγ
  let C := MoTInput.coneRealizationOfCoupling D hstd hγ
  let hpar : CellScaling.AreaParametrization C := MesoModel.final_areaParametrization_of_coupling D hstd hγ
  let S := C.toCellModelGraphCoupling hpar
  have hq0 : 0 < M.q := M.hq.1
  have hq2 : M.q < 2 / (2 + γ) ^ 2 := M.hq.2
  have hL : 0 < GMSLemma27.lemma27Exponent M.q γ :=
    GMSLemma27.lemma27Exponent_pos hγ.1 hq0 hq2
  obtain ⟨α, hα0, hαα₀, hαL⟩ : ∃ α : ℝ, 0 < α ∧ α ≤ α₀ ∧ α < GMSLemma27.lemma27Exponent M.q γ :=
    ⟨min α₀ (GMSLemma27.lemma27Exponent M.q γ / 2), lt_min hα₀ (by linarith), min_le_left _ _,
      lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩
  obtain ⟨m, hm0, hmq, hmβ, hmα⟩ : ∃ m : ℝ, 0 < m ∧ m ≤ M.q ∧ m ≤ βG ∧ m ≤ α :=
    ⟨min M.q (min βG α), lt_min hq0 (lt_min hβG hα0), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hβ0 : 0 < m / 4 := by positivity
  have h3βq : 3 * (m / 4) < M.q := by linarith
  have hββ' : 2 * (m / 4) < min M.q βG := lt_min (by linarith) (by linarith)
  have hβ'q : min M.q βG ≤ M.q := min_le_left _ _
  have h2βα : 2 * (m / 4) < α := by linarith
  have h3ββG : 3 * (m / 4) ≤ βG := by linarith
  have hβ'βG : min M.q βG ≤ βG := min_le_right _ _
  have hρ : 0 < ρG4 / 2 := by positivity
  have hρρ₁ : ρG4 / 2 < ρG4 := by linarith
  -- the fine scales
  have hc : 0 < ρG4 / 2 * Real.exp (-2) := by positivity
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (Lemma38Source.eventually_meshPow_lt hβ0 hc)
  have hAdm : ∀ k : ℕ, k₀ ≤ k → 1 ≤ k →
      GMS4.Prop210Admissible (CellFamily.mesh k) ρG4 C0 βG
        (GMS3.annulusSet 0 (CellFamily.mesh k ^ (m / 4)) (ρG4 / 2))
        (fun u => ‖fderiv ℝ (GMS3.logRad 0 (ρG4 / 2) (CellFamily.mesh k ^ (m / 4))) u‖ ^ 2) ∧
      GMS4.Prop210Admissible (CellFamily.mesh k) ρG4 C0 βG
        (GMS3.annulusSet 0 (CellFamily.mesh k ^ (m / 4)) (ρG4 / 2)) (fun _ => 1) ∧
      GMS4.Prop210Admissible (CellFamily.mesh k) ρG4 C0 βG
        (ball 0 ρG4)
        (GMS3.lemma34Layer (CellFamily.mesh k ^ (m / 4)) (ρG4 / 2) (CellFamily.mesh k ^ min M.q βG)) :=
    fun k hk hk1 => bundle_recThreeAdmissible_of_small hk1 hρ hρρ₁ le_rfl hρ1 hC0 hβG hβ0 h3ββG
      hβ'βG (hk₀ k hk).le
  -- L27 at radius `ρG4`
  have h27 := GMSLemma27.cellDiamBound_of_cellModel (C.toCellModel hpar)
    (MesoModel.final_segmentsContainBalls_of_coupling D hstd hγ hpar)
    (GMCFacts.gmcLowerTail_holds hγ.1 hγ.2)
    (GMCFacts.areaDominates_toCellModel C hpar hγ.1 hγ.2)
    hγ.1 S.toRandomCellFamily S.modelMap S.measurePreserving_modelMap S.ae_cell_eq hq0 hq2
    (show ρG4 ∈ Ioo (0 : ℝ) 1 from ⟨hρ0, hρ1⟩) hαL
  -- Proposition 2.10 at the lowered exponent `α ≤ α₀`
  have h210' : ∀ k (V : Set ℂ) (f : ℂ → ℝ),
      GMS4.Prop210Admissible (CellFamily.mesh k) ρG4 C0 βG V f →
        S.toRandomCellFamily.P
          (GMS4.Prop210Bad S.toRandomCellFamily k V f (2 * A) (CellFamily.mesh k ^ α)) ≤
          ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α) := by
    intro k V f hadm
    have hpow : CellFamily.mesh k ^ α₀ ≤ CellFamily.mesh k ^ α := bundle_mesh_rpow_le_of_le k hαα₀
    calc
      S.toRandomCellFamily.P
          (GMS4.Prop210Bad S.toRandomCellFamily k V f (2 * A) (CellFamily.mesh k ^ α)) ≤
          S.toRandomCellFamily.P
            (GMS4.Prop210Bad S.toRandomCellFamily k V f (2 * A) (CellFamily.mesh k ^ α₀)) :=
        measure_mono (prop210Bad_anti_tol _ k V f (2 * A) hpow)
      _ ≤ ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α₀) := h k V f hadm
      _ ≤ ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow hCfail)
  exact MesoModel.matedCRTRecurrencePathScaleInput_of_scaleInput
    (bundle_matedCRTRecurrenceScaleInput_of_eventually (C.toCellModel hpar) S hstd k₀ hρ hρρ₁ hβ0
      h3βq hββ' hβ'q h2βα hA h27 h210' hCfail hAdm)

end Coupling

/-! ### The final assembly from the single instance `(3/4, 100)` -/

theorem bundle_sixteen_pi_le_hundred : 16 * π ≤ (100 : ℝ) := by
  have := Real.pi_lt_d2
  linarith

/-- **`hAnnulus38` of the final assembly from the single instance.** -/
theorem hAnnulus38_of_prop210At
    (h : MesoModel.FinalForAllCouplings fun _ M _ => Prop210At M.coupled.family (3 / 4) 100) :
    MesoModel.FinalForAllCouplings fun _ M _ => MesoModel.Annulus38OneScaleBadBound M.coupled.family M.ρ :=
  fun γ hγ Ω mΩ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D =>
    annulus38OneScaleBadBound_of_prop210At D hstd hγ
      (h γ hγ Ω mΩ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D)

/-- **`hREC` of the final assembly from the single instance.** -/
theorem hREC_of_prop210At
    (h : MesoModel.FinalForAllCouplings fun _ M _ => Prop210At M.coupled.family (3 / 4) 100) :
    MesoModel.FinalForAllCouplings fun γ _ _ => MesoModel.MatedCRTRecurrencePathScaleInput γ :=
  fun γ hγ Ω mΩ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D =>
    matedCRTRecurrencePathScaleInput_of_prop210At D hstd hγ (by norm_num) (by norm_num)
      bundle_sixteen_pi_le_hundred (h γ hγ Ω mΩ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D)

/-- **`exists_cellModel_of_matingOfTrees` (frozen v3 type) from ONE Proposition 2.10 instance** at
`(ρ, C) = (3/4, 100)` for MTC's family of every coupling. -/
theorem exists_cellModel_of_matingOfTrees_of_prop210At
    (h : MesoModel.FinalForAllCouplings fun _ M _ => Prop210At M.coupled.family (3 / 4) 100) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → MatedCRT.MatingOfTreesInput γ → MatedCRT.CellModelExists γ :=
  MesoModel.exists_cellModel_of_matingOfTrees_of_remaining (hAnnulus38_of_prop210At h) (hREC_of_prop210At h)

end MatedCRTHarmonic.BundleSec4
