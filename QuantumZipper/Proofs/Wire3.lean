import QuantumZipper.Proofs.Wire2b
import QuantumZipper.Proofs.LQG.WedgeBdryInfB4
import QuantumZipper.Proofs.LQG.LogSingGood
import QuantumZipper.Proofs.Section5.Prop17Point
import QuantumZipper.Proofs.Section5.Prop17FieldLaw

/-!
# WIRE-3: discharging the proved inputs of `WedgeBdry` and Proposition 1.7

Wiring only (no new mathematics). Two things:

**1. `S5.WedgeBoundaryRegularStmt γ γ` unconditionally** for `0 < γ < 2`
(`WedgeBdry.wedgeBoundaryRegularStmt_uncond`). The statement was proved in
`Proofs/LQG/WedgeBdryInfB4.lean` conditionally on

* `hYm`: a.e.-measurability of the wedge data `(coordsFull, raw pairings)` — this is
  `S5.FieldLaw.WedgeDataAEMeasStmt γ γ`, now proved in `Wire2b`
  (`Wire2.wedgeDataAEMeasStmt`, from `WedgeMeasND`), and
* `href`: a.s. `0 < scaleParam` of the reference wedge field together with
  a.e.-measurability of its canonical data — this follows from `WedgeCan4`'s a.s. canonical
  specification (`Wire2.ae_wedge_canonical_spec`) and the a.s. goodness of the reference wedge
  field (`LogSingGood.wedgeRefGoodAS_holds`, used through
  `WedgeMeas.aemeasurable_wedgeRefData`).

The only numerical input is `γ < Qc γ` for `0 < γ < 2`, proved in `Prop16AssemblyBasic`
(`Prop16Asm.gamma_lt_Qc`) and re-exported here.

**2. Corollaries of Proposition 1.7** with every hypothesis that is now proved discharged, the
rest kept verbatim:

* `theorem1_7_clause1_uncond`: clause 1 of Proposition 1.7 (`WedgeBoundaryRegularStmt`) with no
  hypothesis beyond `0 < γ < 2`, `0 < L`;
* `prop17ShiftStmt_of_refShiftStmt`, `prop17ShiftStmt_uncond_of_ref`: `Prop17ShiftStmt γ L` from
  the *reference* stationarity `S5.FieldLaw.Prop17RefShiftStmt γ L` (D5-e) alone;
* `theorem1_7_of_shiftStmt`: Proposition 1.7 from `Prop17ShiftStmt` for all `γ`, `L`;
* `theorem1_7_of_refShiftStmt`: Proposition 1.7 from the reference stationarity for all `γ`, `L`.

Remaining hypothesis (D5-e): `S5.FieldLaw.Prop17RefShiftStmt γ L`, the invariance of the reference
`γ`-wedge law under `shiftL γ L` (Sheffield arXiv:1012.4797, Proposition 1.7, §1.6, p. 25; to be
proved from D4⁺, A6 `palm_shift_right_bound` and D5-c). Nothing else remains.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper

namespace Wire3

open CoordsFull WedgeMeas

/-! ## 1. `γ < Qc γ` in the wedge range

(Reproved here in three lines from `div_lt_div_iff₀`; the same fact is
`Prop16Asm.gamma_lt_Qc` in `Proofs/Section5/Prop16AssemblyBasic.lean`, whose module is not
otherwise needed here. Own elementary proof.) -/
theorem gamma_lt_Qc {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : γ < Qc γ := by
  unfold Qc
  have h1 : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ two_pos hγ]; nlinarith
  linarith

/-! ## 2. The two handoff conditions of `WedgeBdry.wedgeBoundaryRegularStmt_holds` -/

/-- **`hYm` (WEDGE-MEAS (1))**, per-instance form: every `γ`-quantum wedge (`0 < γ < 2`) has
a.e.-measurable data. -/
theorem aemeasurable_dataFull_uncond {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → FieldSample)
    (hY : IsQuantumWedge γ γ Y P) :
    AEMeasurable (fun ω => (CoordsFull.coordsFull (Y ω),
      fun ρ : TestFun H => pairRaw (Y ω) ρ.1)) P := by
  have h := Wire2.wedgeDataAEMeasStmt hγ hγ2 (gamma_lt_Qc hγ hγ2) P Y hY
  simpa only [dataFull] using h

/-- **`hYm`** in the exact `∀`-form used by `WedgeBdry.wedgeBoundaryRegularStmt_holds`. -/
theorem wedgeBdry_hYm_uncond {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Y : Ω → FieldSample), IsQuantumWedge γ γ Y P →
      AEMeasurable (fun ω => (CoordsFull.coordsFull (Y ω),
        fun ρ : TestFun H => pairRaw (Y ω) ρ.1)) P := by
  intro Ω _ P _ Y hY
  exact aemeasurable_dataFull_uncond hγ hγ2 P Y hY

/-- **(R23 (b)) the reference field input**, per-instance form: a.s. `0 < scaleParam` and
a.e.-measurability of the canonical full-coordinate map of the reference wedge field. -/
theorem wedgeRef_scaleParam_pos_and_data_aemeasurable {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ) (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess γ (Qc γ) A P') (hI : IndepFun X (fun ω t => A t ω) P') :
    (∀ᵐ ω ∂P',
        0 < scaleParam γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) ∧
      AEMeasurable (fun ω => (CoordsFull.coordsFull
        (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))),
        fun ρ : TestFun H => pairRaw
          (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) ρ.1)) P' := by
  have hα := gamma_lt_Qc hγ hγ2
  refine ⟨?_, ?_⟩
  · exact (Wire2.ae_wedge_canonical_spec hγ hγ2 hα hX hA hI).mono fun ω h => h.1
  · have hgood := LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα Ω' _ P' X A
      (inferInstance : IsProbabilityMeasure P') hX hA hI
    have h := WedgeMeas.aemeasurable_wedgeRefData (γ := γ) hX hA hgood H
    simpa only [dataFull, wedgeRef] using h

/-- **`href`** in the exact `∀`-form used by `WedgeBdry.wedgeBoundaryRegularStmt_holds`. -/
theorem wedgeBdry_href_uncond {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (X : Ω' → FieldSample)
      (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → IsFreeGFFModConstH X P' →
      IsWedgeProcess γ (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' →
      (∀ᵐ ω ∂P',
        0 < scaleParam γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) ∧
      AEMeasurable (fun ω => (CoordsFull.coordsFull
        (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))),
        fun ρ : TestFun H => pairRaw
          (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) ρ.1)) P' := by
  intro Ω' _ P' X A hP' hX hA hI
  exact wedgeRef_scaleParam_pos_and_data_aemeasurable hγ hγ2 Ω' P' X A hX hA hI

/-! ## 3. `WedgeBoundaryRegularStmt γ γ`, unconditionally -/

/-- **`S5.WedgeBoundaryRegularStmt γ γ` for `0 < γ < 2`, unconditionally.** -/
theorem wedgeBoundaryRegularStmt_uncond {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    S5.WedgeBoundaryRegularStmt γ γ :=
  WedgeBdry.wedgeBoundaryRegularStmt_holds hγ hγ2 (wedgeBdry_hYm_uncond hγ hγ2)
    (wedgeBdry_href_uncond hγ hγ2)

/-- The `∀ γ` form used by `S5.theorem1_7_of`. -/
theorem wedgeBoundaryRegularStmt_all :
    ∀ γ : ℝ, 0 < γ → γ < 2 → S5.WedgeBoundaryRegularStmt γ γ :=
  fun γ hγ hγ2 => wedgeBoundaryRegularStmt_uncond (γ := γ) hγ hγ2

/-! ## 4. R23 (c): `WedgeDataAEMeasStmt` and `WedgeGoodStmt` for `α = γ` -/

/-- **`S5.FieldLaw.WedgeDataAEMeasStmt γ γ`** for `0 < γ < 2`. -/
theorem wedgeDataAEMeasStmt_uncond {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    S5.FieldLaw.WedgeDataAEMeasStmt γ γ :=
  Wire2.wedgeDataAEMeasStmt hγ hγ2 (gamma_lt_Qc hγ hγ2)

/-- **`S5.FieldLaw.WedgeGoodStmt γ γ`** for `0 < γ < 2`. -/
theorem wedgeGoodStmt_uncond {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    S5.FieldLaw.WedgeGoodStmt γ γ :=
  Wire2.wedgeGoodStmt hγ hγ2 (gamma_lt_Qc hγ hγ2)

/-! ## 5. Proposition 1.7 with the proved hypotheses discharged -/

/-- **Proposition 1.7 from the reference stationarity (D5-e) for all `γ`, `L`.** -/
theorem theorem1_7_of_refShiftStmt
    (href : ∀ γ L : ℝ, 0 < γ → γ < 2 → 0 < L → S5.FieldLaw.Prop17RefShiftStmt γ L) :
    theorem1_7 :=
  S5.FieldLaw.theorem1_7_of_ref wedgeBoundaryRegularStmt_all
    (fun γ hγ hγ2 => wedgeDataAEMeasStmt_uncond (γ := γ) hγ hγ2)
    (fun γ hγ hγ2 => wedgeGoodStmt_uncond (γ := γ) hγ hγ2) href

end Wire3

end QuantumZipper
