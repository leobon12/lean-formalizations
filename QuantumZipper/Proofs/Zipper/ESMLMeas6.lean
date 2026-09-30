import QuantumZipper.Proofs.Zipper.ESMLMeas5
import QuantumZipper.Proofs.Zipper.B5VHccInd
import QuantumZipper.Proofs.Zipper.Cor15GroupZero
import QuantumZipper.Proofs.Zipper.Cor15RegBasic
import QuantumZipper.Proofs.LQG.RevCouplingReg

/-!
# ESM-LMEAS-4: the `s = 0` certificate and the unconditional `hLad`

Sixth (final) part of the ESM-LMEAS task (node **E-SM**, obligation `hLad` of
`ESM.lintegral_levelTime_strongMarkov_lenA`, decision D21). `ESMLMeas5` proves

  `hLad_lenMinus_pos`  (`s > 0`, from `E1.ae_bCert_h0f`) and
  `hLad_lenMinus_zero_of_bCert` (`s = 0`, *given* the boundary certificate of the time-`0`
  unzipped field `coordChange (𝔥₀ + X) id (Qc √κ) = evalReg (𝔥₀ + X)`).

Here we supply that certificate, and assemble the full `hLad` for all `s ≥ 0`.

* `ae_bCert_h0rev_add`: **a.s. `𝔥₀ + X` carries the certificate `E1.M4.BCert (√κ)`.** The route is
  the one of E1-EX (`E1.ae_exists_isVagueLimitR_normAt_h0rev`, i.e. the log-singularity theorem of
  Duplantier–Sheffield, *LQG and KPZ*, arXiv:0808.1560, §3, as formalized in node M4-P4), here
  taken in its packaged form `RevCouplingReg.ae_cert_nrm_gamma0`: a.s. the normalized
  `nrm (𝔥₀ + X)` satisfies the countable certificate `RevCouplingReg.Cert` (global vague limit
  with no atoms, positive on intervals, finite on compacts). The additive constant is removed with
  `Cor15Group.bCert_addConst`, which needs the raw circle averages of `𝔥₀ + X` to converge
  (`B5.rawConverges_h0rev_add` from `RegSample.ae_isRegularSample hX`) — this is where the
  finiteness on `Icc` and the log singularity enter.
* `ae_coordsFull_unzipFieldCoord_zero`: **the time-`0` unzipped field has the circle coordinates
  of `𝔥₀ + X`.** Unzipping for time `0` is the identity: the reverse flow at time `0` of the zero
  driver (`revPath 0` is the zero path, `Wof κ 0` the zero driver) fixes `ℍ`
  (`CharFun.revMap_zero_eq`), a map agreeing on `ℍ` with `id` gives the same coordinate change on
  measures concentrated on `ℍ` (`UnzipInvariance.coordChange_congr_of_eqOn`,
  `foldedCircle_compl_H_eq_zero`), `coordChange y id Q = evalReg y`
  (`Cor15Partial.coordChange_id_apply`), and a.s. `evalReg` and the raw field agree at the dyadic
  folded circles (`Cor15Group.ae_evalReg_fc_h0rev_add`).
* `ae_bCert_unzipFieldCoord_zero`: the input `h0bCert` of `hLad_lenMinus_zero_of_bCert`, by
  transport along the coordinate identity (`B5.bCert_congr_full`).
* **`hLad_lenMinus`**: the full adaptedness obligation, all `s ≥ 0`, no certificate hypothesis
  (`s > 0` from `hLad_lenMinus_pos`, `s = 0` from `hLad_lenMinus_zero_of_bCert`), and its
  unconditional form `hLad_lenMinus_uncond` (RCBMR, `RevCouplingReg.revCouplingBoundaryMeasureRegular`).

Paper: Sheffield, arXiv:1012.4797, proof of Lemma 5.6 (pp. 66–68); the `s = 0` case is the
degenerate ("nothing zipped") case of the same statement. The coordinate bookkeeping is our own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace ESM

open F1 CoordsFull CharFun

/-! ## 1. The boundary certificate of `𝔥₀ + X` -/

/-- **The certificate of `𝔥₀ + X`.** A.s. the field `ofFun (h0rev κ) + X` carries the countable
boundary certificate `E1.M4.BCert (√κ)`: from `RevCouplingReg.ae_cert_nrm_gamma0` for the
normalized field (E1-EX, the log-singularity input) and the removal of the additive constant
(`Cor15Group.bCert_addConst` along `Cor15Group.addConst_nrm`), which needs the raw circle averages
of `𝔥₀ + X` (`B5.rawConverges_h0rev_add` from `RegSample.ae_isRegularSample hX`). -/
theorem ae_bCert_h0rev_add {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    ∀ᵐ ω ∂P, E1.M4.BCert (Real.sqrt κ) (ofFun (h0rev κ) + X ω) := by
  filter_upwards [RevCouplingReg.ae_cert_nrm_gamma0 hX hκ hκ4, RegSample.ae_isRegularSample hX]
    with ω hcert hregX
  have hraw : LocalRule.RawConverges (ofFun (h0rev κ) + X ω) Hbar :=
    B5.rawConverges_h0rev_add κ hregX.rawConverges
  have hbcy : Cor15Group.BdryConvAE (ofFun (h0rev κ) + X ω) := fun k =>
    Eventually.of_forall fun s => hraw k (s : ℂ) (by simp [Hbar])
  have hbc : E1.M4.BCert (Real.sqrt κ) (B1Full.nrm (ofFun (h0rev κ) + X ω)) := by
    obtain ⟨ν, hν, -⟩ := RevCouplingReg.good_of_cert hcert
    exact E1.M4.bCert_of_isVagueLimitR hcert.1 hν
  have h := Cor15Group.bCert_addConst (Cor15Group.bdryConvAE_addConst hbcy _) hbc
    ((ofFun (h0rev κ) + X ω) (foldedCircle 0 1))
  have h' : E1.M4.BCert (Real.sqrt κ) (addConst (B1Full.nrm (ofFun (h0rev κ) + X ω))
      ((ofFun (h0rev κ) + X ω) (foldedCircle 0 1))) := h
  rwa [Cor15Group.addConst_nrm (ofFun (h0rev κ) + X ω)] at h'

/-! ## 2. The time-`0` unzipped field has the coordinates of `𝔥₀ + X` -/

/-- **Unzipping for time `0` is the identity.** A.s. the circle coordinates of the path–surrogate
field at `s = 0` (which does not depend on the path: `revPath 0` is the zero path and `Wof κ 0`
the zero driver) are those of `𝔥₀ + X`. -/
theorem ae_coordsFull_unzipFieldCoord_zero {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hBc : ∀ ω : Ω, Continuous fun u : ℝ≥0 => B u ω) (hX : IsFreeGFFModConstH X P) (κ : ℝ) :
    ∀ᵐ ω ∂P, coordsFull (unzipFieldCoord κ 0 le_rfl (X ω, pathC 0 B hBc ω)) =
      coordsFull (ofFun (h0rev κ) + X ω) := by
  filter_upwards [Cor15Group.ae_evalReg_fc_h0rev_add κ hX] with ω hreg
  funext i
  have hr := UnzipFull.fullIndex_radius_pos i
  have hμH : foldedCircle (fullIndex i).1 (fullIndex i).2 Hᶜ = 0 :=
    foldedCircle_compl_H_eq_zero _ hr
  have hW0 : Wof κ 0 le_rfl (revPath 0 le_rfl (pathC 0 B hBc ω)) 0 = 0 := by
    simp [Wof, revPath, projIcc_left]
  have hEq : EqOn (revMap (Wof κ 0 le_rfl (revPath 0 le_rfl (pathC 0 B hBc ω))) 0) id H :=
    fun z hz => CharFun.revMap_zero_eq (continuous_Wof κ 0 le_rfl _) hW0 hz
  rw [coordsFull_unzipFieldCoord, unzipFieldPath_apply]
  exact (UnzipInvariance.coordChange_congr_of_eqOn hEq hμH _ _).trans
    ((Cor15Partial.coordChange_id_apply _ _ _).trans (hreg i))

/-! ## 3. The certificate of the time-`0` unzipped field -/

/-- **The certificate `h0bCert` of `hLad_lenMinus_zero_of_bCert`.** Transport of
`ae_bCert_h0rev_add` along the circle-coordinate identity of the time-`0` unzipped field
(`ae_coordsFull_unzipFieldCoord_zero`, `B5.bCert_congr_full`). -/
theorem ae_bCert_unzipFieldCoord_zero {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hBc : ∀ ω : Ω, Continuous fun u : ℝ≥0 => B u ω)
    (hX : IsFreeGFFModConstH X P) :
    ∀ᵐ ω ∂P, E1.M4.BCert (Real.sqrt κ)
      (unzipFieldCoord κ 0 le_rfl (X ω, pathC 0 B hBc ω)) := by
  filter_upwards [ae_bCert_h0rev_add hX hκ hκ4,
    ae_coordsFull_unzipFieldCoord_zero hBc hX κ] with ω hbc hcoord
  exact B5.bCert_congr_full hcoord.symm hbc

/-! ## 4. The full adaptedness obligation `hLad` -/

/-- **`hLad` for all times.** The intrinsic left length `L⁻_s` is
`complFiltration`-adapted for every `s : ℝ≥0`, with no certificate hypothesis: `s > 0` is
`hLad_lenMinus_pos` (`E1.ae_bCert_h0f`), `s = 0` is `hLad_lenMinus_zero_of_bCert` fed with
`ae_bCert_unzipFieldCoord_zero`. -/
theorem hLad_lenMinus {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hReg : Blueprint.RevCouplingBoundaryMeasureRegular) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hBc : ∀ ω : Ω, Continuous fun u : ℝ≥0 => B u ω) :
    ∀ s : ℝ≥0, Measurable[complFiltration hB hX s] (lenMinus κ B X s ∘ ofCompl P) := by
  intro s
  rcases (NNReal.coe_nonneg s).eq_or_lt with h0 | hpos
  · have hs0 : s = 0 := NNReal.coe_eq_zero.1 h0.symm
    subst hs0
    exact hLad_lenMinus_zero_of_bCert hκ hκ4.le hB hX hind hBc
      (ae_bCert_unzipFieldCoord_zero hκ hκ4 hBc hX)
  · exact hLad_lenMinus_pos hReg hκ hκ4 hB hX hind hBc s hpos

/-- **`hLad`, unconditional** (RCBMR, `RevCouplingReg.revCouplingBoundaryMeasureRegular`). -/
theorem hLad_lenMinus_uncond {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hBc : ∀ ω : Ω, Continuous fun u : ℝ≥0 => B u ω) :
    ∀ s : ℝ≥0, Measurable[complFiltration hB hX s] (lenMinus κ B X s ∘ ofCompl P) :=
  hLad_lenMinus RevCouplingReg.revCouplingBoundaryMeasureRegular hκ hκ4 hB hX hind hBc

end ESM
end QuantumZipper
