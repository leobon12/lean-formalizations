import QuantumZipper.Proofs.Zipper.E1TransferM4Cert
import QuantumZipper.Proofs.Zipper.E1NuExist

/-!
# M4: the boundary certificate of the normalized field `h⁰ − m` holds a.s.

`handoff/E1-TR.md` (M4). Notation of `B2Defs`/`E1Defs`.

* `ae_continuousOn_avgReg_h0f`: a.s. every regularized circle average `avgReg h⁰ k` is continuous
  on `Hbar` (the raw values of `h⁰` on folded circles are those of the RC2 field, whose
  certificate `GoodMeas.C1` holds a.s. by `E1.ae_C1_h0rev_random`).
* `ae_bCert_h0f`: under `Blueprint.RevCouplingBoundaryMeasureRegular` (B3(a)), a.s.
  `M4.BCert (√κ) (h⁰ − m)`: finiteness of the approximations on `[-N, N]` (continuous densities)
  plus the vague limit `E1.ae_exists_isVagueLimitR_nuPalm`, via `M4.bCert_of_isVagueLimitR`.

Source: Sheffield, arXiv:1012.4797, §5.2 (pp. 57–59) and Lemma 5.6 (pp. 66–68), where the boundary
measure of the normalized field is taken for granted. The derivation is **own bookkeeping**
(as in `E1NuExist`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1

open B2 CharFun UnzipInvariance UnzipFull TwoPoint

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- A.s. every regularized circle average of `h⁰` is continuous on `Hbar`. -/
theorem ae_continuousOn_avgReg_h0f (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, ContinuousOn (avgReg (h0f κ T B X ω) k) Hbar := by
  obtain ⟨B', -, hB'm, hB'c, hind', hV⟩ := exists_revDriver (κ := κ) hB hind hT
  set g := pathC T B' hB'c with hg_def
  have hgm : Measurable g := measurable_pathC T hB'm hB'c
  have hig : IndepFun g X P := indepFun_pathC T hind' hB'c
  filter_upwards [hV, hB.cont, hB.eval_zero_ae_eq_zero,
    ae_C1_h0rev_random κ hT (Qc (Real.sqrt κ)) hX hgm hig] with ω hVω hc h0 hC1
  have hrevV : revMap (Vr κ T B ω) T = revMap (drive κ B' ω) T :=
    funext fun z => ReverseFlow.revMap_congr_drive z hVω
  have hE : EqOn (fwdMapInv (drive κ B ω) T) (revMap (drive κ B' ω) T) H := fun z hz => by
    rw [fwdMapInv_eq_revMap_vrev (drive_continuous hc) (drive_zero h0) hT hz, ← hrevV]; rfl
  have hrev : revMap (drive κ B' ω) T = revMap (Wof κ T hT (g ω)) T :=
    revMap_drive_eq κ T hT B' hB'c ω
  have key : ∀ (c : ℂ) (k : ℕ), h0f κ T B X ω (foldedCircle c (radius k)) =
      GoodMeas.raw (coordChange (ofFun (h0rev κ) + X ω) (revMap (Wof κ T hT (g ω)) T)
        (Qc (Real.sqrt κ))) c k := by
    intro c k
    have hμH : foldedCircle c (radius k) Hᶜ = 0 :=
      ae_iff.1 (foldedCircle_ae_mem_H c (radius_pos k))
    rw [h0f_eq_unzippedField]
    show coordChange (ofFun (h0rev κ) + X ω) (fwdMapInv (drive κ B ω) T) (Qc (Real.sqrt κ))
      (foldedCircle c (radius k)) = _
    rw [coordChange_congr_of_eqOn hE hμH, hrev]
    rfl
  intro k
  have e : avgReg (h0f κ T B X ω) k = avgReg (coordChange (ofFun (h0rev κ) + X ω)
      (revMap (Wof κ T hT (g ω)) T) (Qc (Real.sqrt κ))) k := by
    funext z
    unfold avgReg
    simp_rw [key]
    rfl
  rw [e]
  exact GoodMeas.continuousOn_avgReg_of_C1 hC1 k

/-- Finiteness of the boundary approximations on compacts, from continuity of `avgReg` on
`Hbar`. -/
theorem bdryApprox_Icc_lt_top_of_continuousOn {γ : ℝ} {x : FieldSample} {k : ℕ}
    (h : ContinuousOn (avgReg x k) Hbar) (N : ℕ) :
    bdryApprox γ x k (Icc (-(N : ℝ)) N) < ⊤ := by
  have hc : Continuous fun t : ℝ => avgReg x k (t : ℂ) :=
    h.comp_continuous Complex.continuous_ofReal fun t => show (0 : ℝ) ≤ (t : ℂ).im by simp
  exact GoodSample.withDensity_lt_top isCompact_Icc isCompact_Icc.measure_lt_top
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc))).continuousOn

/-- Under B3(a), a.s. the boundary certificate `M4.BCert` of `h⁰ − m` holds. -/
theorem ae_bCert_h0f (hReg : Blueprint.RevCouplingBoundaryMeasureRegular)
    (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (ϖ : Measure ℂ) :
    ∀ᵐ ω ∂P, M4.BCert (Real.sqrt κ) (addConst (h0f κ T B X ω) (-(mReg κ T B X ϖ ω))) := by
  filter_upwards [ae_exists_isVagueLimitR_nuPalm hReg hκ hκ4 hT hB hX hind ϖ,
    ae_rawConverges_h0f (κ := κ) hB hX hind hT.le,
    ae_continuousOn_avgReg_h0f (κ := κ) hB hX hind hT.le] with ω hex hraw hcont
  obtain ⟨ν, hν⟩ := hex
  refine M4.bCert_of_isVagueLimitR (fun k N => ?_) hν
  rw [LocalRule.bdryApprox_addConst hraw, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (bdryApprox_Icc_lt_top_of_continuousOn (hcont k) N)

end E1
end QuantumZipper
