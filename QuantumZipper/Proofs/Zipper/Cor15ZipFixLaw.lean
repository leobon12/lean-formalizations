import QuantumZipper.Proofs.Zipper.Cor15ZipFixVer

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D42 (COR15-ZIPFIX): the zip coordinate law by transfer from the unzipped configuration

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 and §1.4
(zipping is the inverse of unzipping; the configuration is stationary modulo constants).

The coordinate law `Cor15ZipCoordLawStmt'` and the raw convergence `Cor15ZipRawConvStmt`
(`Cor15ZipFixVer`) are transferred from the unzipped configuration `y = D_a c` to `c` by the
proved B1-FULL law identity (`b1_full_data`: `b1Data y` and `b1Data c` have the same law) —
the same pattern as `Cor15LawTransfer.map_comp_eq_of_goodSet` (used for Corollary 1.5(a)):

* at `y = D_a c` the zip side is known pathwise: `U_a y` has the circle coordinates of `c`
  (`ae_coordsFull_zipFld_zipCapDown`, from the proved re-zip inputs (K0) `cor15HullNullStmt`,
  (R) `cor15RezipRegStmt` and `rezip_apply`) and the driver `√κ B`
  (`ae_zipDrv_zipCapDown`), so the zip data of `y` are `(nrm0 (coordsFull X), B)`;
* **remaining node** `Cor15ZipCoordReadStmt`: on a measurable set `A` of B1-FULL data charged
  a.s. by `b1Data y`, the zip data `(nrm0 (coordsFull (zipFld x − 𝔥₀)), zipDrv x)` are a fixed
  measurable function `Ψ` of `b1Data x`, and the raw circle averages of `zipFld x` converge.
  (Deterministic content: `U_a` commutes with the additive constant removed by `nrm`, on the
  regularity set; the welding driver is already read by `cor15WeldRead`.)

Hence `theorem1_5_of_theorem1_3_of_zipFixRead'`: Corollary 1.5 from Theorem 1.3, the good set
`Cor15ShiftGoodStmt`, the round-trip field half `Cor15UnzipZipFieldGoodStmt` and the reading
node. Own bookkeeping (law transfer), no new analytic input.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open CoordsFull B1Full B2

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-! ## The zip side at the unzipped configuration -/

/-- **Circle coordinates of `U_a (D_a c)` are those of `c`** (raw values, not only `RegEq`). -/
theorem ae_coordsFull_zipFld_zipCapDown (h13 : theorem1_3) {κ a : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) (hS : IsGrpSetup P B X) (ha : 0 < a) :
    ∀ᵐ ω ∂P, coordsFull (zipFld κ a (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω))) =
      coordsFull (grpCfg κ B X ω).1 := by
  obtain ⟨hB, hX, hind⟩ := hS
  filter_upwards [ae_zipCapUp_zipCapDown_fst (h13 := h13) (hRSS := RS.rohdeSchrammSimple)
      (hκ := hκ) (hκ4 := hκ4) (hB := hB) (hX := hX) (hind := hind) (ht := ha),
    ae_all_iff.2 (cor15HullNullStmt κ hκ hκ4 a ha P B hB),
    ae_all_iff.2 (cor15RezipRegStmt κ hκ hκ4 a ha P B X hB hX hind),
    ae_evalReg_fc_h0rev_add κ hX, hB.cont, hB.eval_zero_ae_eq_zero] with ω hfst hk hr hd hc h0
  have hWc : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  have hVc : Continuous (vrev (drive κ B ω) a) := continuous_vrev hWc a
  funext i
  have hri := UnzipFull.fullIndex_radius_pos i
  have hHc : foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 Hᶜ = 0 :=
    ae_iff.1 (TwoPoint.foldedCircle_ae_mem_H _ hri)
  have hμ : foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2
      (revMap (vrev (drive κ B ω) a) a '' H)ᶜ = 0 := by
    refine measure_mono_null (fun z hz => ?_) (measure_union_null hHc (hk i))
    by_cases hzH : z ∈ H
    · exact Or.inr ⟨hzH, hz⟩
    · exact Or.inl hzH
  show (zipCapUp (Real.sqrt κ) a
      (zipCapDown (Real.sqrt κ) a (ofFun (h0rev κ) + X ω, drive κ B ω))).1 _ = _
  rw [hfst]
  show coordChange (coordChange (ofFun (h0rev κ) + X ω) (fwdMapInv (drive κ B ω) a)
      (Qc (Real.sqrt κ))) (revMapInv (vrev (drive κ B ω) a) a) (Qc (Real.sqrt κ)) _ = _
  rw [rezip_apply hVc ha.le _ _ (fun z hz => fwdMapInv_eq_revMap_vrev hWc hW0 ha.le hz) hμ
    (hr i)]
  exact hd i

/-- **The zipped driver of `D_a c` is `B`.** -/
theorem ae_zipDrv_zipCapDown (h13 : theorem1_3) {κ a : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hS : IsGrpSetup P B X) (ha : 0 < a) :
    ∀ᵐ ω ∂P, zipDrv κ a (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω)) = pathOf B ω := by
  obtain ⟨hB, hX, hind⟩ := hS
  filter_upwards [ae_zipCapUp_zipCapDown_snd (h13 := h13) (hRSS := RS.rohdeSchrammSimple)
      (hκ := hκ) (hκ4 := hκ4) (hB := hB) (hX := hX) (hind := hind) (ht := ha)]
    with ω hω
  funext u
  have hsk : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  simp only [zipDrv]
  rw [show zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω) =
      zipCapDown (Real.sqrt κ) a (ofFun (h0rev κ) + X ω, drive κ B ω) from rfl,
    hω (u : ℝ) u.2, show drive κ B ω (u : ℝ) = (grpCfg κ B X ω).2 (u : ℝ) from rfl,
    grpCfg_snd, Real.toNNReal_coe, inv_mul_cancel_left₀ hsk]
  rfl

/-- The zip data of `D_a c` are `(nrm0 (coordsFull X), B)`. -/
theorem ae_zipData_zipCapDown (h13 : theorem1_3) {κ a : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hS : IsGrpSetup P B X) (ha : 0 < a) :
    ∀ᵐ ω ∂P, (nrm0 (coordsFull (zipFld κ a (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω)) -
        ofFun (h0rev κ))), zipDrv κ a (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω))) =
      (nrm0 (coordsFull (X ω)), pathOf B ω) := by
  filter_upwards [ae_coordsFull_zipFld_zipCapDown h13 hκ hκ4 hS ha,
    ae_zipDrv_zipCapDown h13 hκ hκ4 hS ha] with ω hc hd
  refine Prod.ext ?_ hd
  show nrm0 _ = nrm0 _
  congr 1
  funext i
  have := congrFun hc i
  simp only [coordsFull, Pi.sub_apply] at this ⊢
  rw [this]
  show (ofFun (h0rev κ) + X ω) _ - _ = _
  simp only [Pi.add_apply]
  ring

/-! ## The reading node and the transfer -/

/-- **Remaining reading node (D42).** A measurable set `A` of B1-FULL data values, charged a.s. by
the data of `D_a c`, on which the zip data `(nrm0 (coordsFull (zipFld x − 𝔥₀)), zipDrv x)` are a
fixed measurable function `Ψ` of `b1Data x` and the raw circle averages of `zipFld x` converge. -/
def Cor15ZipCoordReadStmt (κ a : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) :
    Prop :=
  ∃ (Ψ : B1E → (ℕ → ℝ) × (ℝ≥0 → ℝ)) (A : Set B1E), Measurable Ψ ∧ MeasurableSet A ∧
    (∀ x : FieldSample × (ℝ → ℝ), b1Data x ∈ A →
      (nrm0 (coordsFull (zipFld κ a x - ofFun (h0rev κ))), zipDrv κ a x) = Ψ (b1Data x) ∧
      ∀ k : ℕ, ∀ z : ℂ, ∃ l, Tendsto
        (fun n => zipFld κ a x (foldedCircle (dyadicRoundC n z) (radius k))) atTop (𝓝 l)) ∧
    ∀ᵐ ω ∂P, b1Data (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω)) ∈ A

/-- **Transfer**: the reading node gives the coordinate law and the raw convergence at `c`. -/
theorem zipCoordLaw_rawConv_of_read (h13 : theorem1_3) {κ a : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hS : IsGrpSetup P B X) (ha : 0 < a) (hR : Cor15ZipCoordReadStmt κ a P B X) :
    (AEMeasurable (fun ω => nrm0 (coordsFull (zipFld κ a (grpCfg κ B X ω) -
        ofFun (h0rev κ)))) P ∧
      P.map (fun ω => (nrm0 (coordsFull (zipFld κ a (grpCfg κ B X ω) - ofFun (h0rev κ))),
          zipDrv κ a (grpCfg κ B X ω))) =
        P.map (fun ω => (nrm0 (coordsFull (X ω)), pathOf B ω))) ∧
    ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ z : ℂ, ∃ l, Tendsto
      (fun n => zipFld κ a (grpCfg κ B X ω) (foldedCircle (dyadicRoundC n z) (radius k)))
      atTop (𝓝 l) := by
  obtain ⟨Ψ, A, hΨ, hA, hfac, hyA⟩ := hR
  have hlaw : P.map (fun ω => b1Data (grpCfg κ B X ω)) =
      P.map (fun ω => b1Data (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω))) :=
    (b1_full_data (κ := κ) (B := B) (X := X) hκ hS.1 hS.2.1 hS.2.2 ha).symm
  have hec : AEMeasurable (fun ω => b1Data (grpCfg κ B X ω)) P :=
    aemeasurable_b1Data_c κ hS.1 hS.2.1
  have hey : AEMeasurable (fun ω => b1Data (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω))) P :=
    aemeasurable_b1Data_unzip κ hκ hS.1 hS.2.1 hS.2.2 ha
  have hcA : ∀ᵐ ω ∂P, b1Data (grpCfg κ B X ω) ∈ A := ae_mem_of_map_eq hA hec hey hlaw hyA
  set G : FieldSample × (ℝ → ℝ) → (ℕ → ℝ) × (ℝ≥0 → ℝ) :=
    fun x => (nrm0 (coordsFull (zipFld κ a x - ofFun (h0rev κ))), zipDrv κ a x) with hG
  have hLc : P.map (fun ω => G (id (grpCfg κ B X ω))) =
      P.map (fun ω => G (id (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω)))) :=
    map_comp_eq_of_goodSet (c := fun ω => grpCfg κ B X ω)
      (y := fun ω => zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω)) (Z := id) (e := b1Data)
      (m := G) hΨ hA (fun x hx => (hfac x hx).1) hec hey hlaw hyA
  have hGc : (fun ω => G (grpCfg κ B X ω)) =ᵐ[P] fun ω => Ψ (b1Data (grpCfg κ B X ω)) := by
    filter_upwards [hcA] with ω hω using (hfac _ hω).1
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h1 : AEMeasurable (fun ω => Ψ (b1Data (grpCfg κ B X ω))) P := hΨ.comp_aemeasurable hec
    exact (measurable_fst.comp_aemeasurable h1).congr
      (hGc.mono fun ω hω => (congrArg Prod.fst hω).symm)
  · show P.map (fun ω => G (id (grpCfg κ B X ω))) = _
    rw [hLc]
    exact Measure.map_congr (ae_zipData_zipCapDown h13 hκ hκ4 hS ha)
  · filter_upwards [hcA] with ω hω using (hfac _ hω).2

theorem cor15ZipCoordLawStmt'_of_read (h13 : theorem1_3)
    (hR : ∀ κ : ℝ, 0 < κ → κ < 4 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), IsGrpSetup P B X →
      ∀ a : ℝ, 0 < a → Cor15ZipCoordReadStmt κ a P B X) : Cor15ZipCoordLawStmt' := by
  intro κ hκ hκ4 Ω _ P _ B X hS a ha
  exact (zipCoordLaw_rawConv_of_read h13 hκ hκ4 hS ha (hR κ hκ hκ4 P B X hS a ha)).1

theorem cor15ZipRawConvStmt_of_read (h13 : theorem1_3)
    (hR : ∀ κ : ℝ, 0 < κ → κ < 4 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), IsGrpSetup P B X →
      ∀ a : ℝ, 0 < a → Cor15ZipCoordReadStmt κ a P B X) : Cor15ZipRawConvStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hS a ha
  exact (zipCoordLaw_rawConv_of_read h13 hκ hκ4 hS ha (hR κ hκ hκ4 P B X hS a ha)).2

end Cor15Group
end QuantumZipper
