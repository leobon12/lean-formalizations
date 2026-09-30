import QuantumZipper.Proofs.Zipper.E1Defs
import QuantumZipper.Proofs.GFF.CoordRegRandom
import QuantumZipper.Proofs.LQG.GoodMeasurableReg
import QuantumZipper.Blueprint.External2
import QuantumZipper.Proofs.LQG.LocalRule

/-!
# NU-EX: existence of the normalized boundary measure `ν = ν_{h⁰ − m}` (decision D19)

`handoff/E1-PLAN.md`, node NU-EX; `DECISIONS.md` D19. Notation of `B2Defs`/`E1Defs`.

* `measurableSet_C1_h0rev`: the countable certificate `GoodMeas.C1` (uniform continuity of the raw
  dyadic circle averages on bounded sets) of `coordChange (𝔥₀ + x) (revMap (Wof f) T) Q` is a
  measurable event in `(f, x)`.
* `ae_C1_h0rev_random`: for a random driver path `g ⊥ X`, a.s. `C1` holds (RC2 for every
  continuous driver, `CoordReg.ae_isRegularSample_coordChange_h0rev'`, `GoodMeas.C1_of_regular`,
  and independence `CharFun.ae_indep`).
* `ae_rawConverges_h0f`: a.s. the raw circle averages of `h⁰` converge at every centre of `Hbar`.
* `ae_nuPalm_eq_smul`: a.s. `ν = e^{γ(−m)/2} • ν_{h⁰}`.
* `ae_exists_isVagueLimitR_nuPalm`: under `Blueprint.RevCouplingBoundaryMeasureRegular` (B3(a)),
  a.s. the boundary approximations of `h⁰ − m` have a vague limit.

Source: Sheffield, arXiv:1012.4797, §5.2 (pp. 57–59) and Lemma 5.6 (pp. 66–68), where the boundary
measure of the normalized field is taken for granted. The derivation from RC2 plus independence is
**own bookkeeping** (D19): the identification of `h⁰` with `coordChange (𝔥₀ + X) (revMap V T) Q`
on `ℍ` repeats the computation in the proof of `B2.b2_ident`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1

open B2 CharFun UnzipInvariance UnzipFull TwoPoint

/-- (1) The certificate `C1` of the RC2 field is a measurable event in (driver path, field). -/
theorem measurableSet_C1_h0rev (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) (Q : ℝ) :
    MeasurableSet {p : C(Icc (0 : ℝ) T, ℝ) × FieldSample |
      GoodMeas.C1 (coordChange (ofFun (h0rev κ) + p.2) (revMap (Wof κ T hT p.1) T) Q)} := by
  refine measurableSet_setOfPred.2 ?_
  unfold GoodMeas.C1
  refine Measurable.forall fun k => Measurable.forall fun M => Measurable.forall fun e =>
    Measurable.exists fun j => ?_
  refine Measurable.forall fun n => Measurable.forall fun a => Measurable.forall fun b =>
    Measurable.forall fun n' => Measurable.forall fun a' => Measurable.forall fun b' => ?_
  refine measurable_const.imp (measurable_const.imp (measurable_const.imp
    (measurable_const.imp (measurable_const.imp ?_))))
  exact GoodMeas.mprop_abs_le
    (CoordReg.measurable_coordChange_fc κ hT (h0rev κ) Q _ (radius_pos k))
    (CoordReg.measurable_coordChange_fc κ hT (h0rev κ) Q _ (radius_pos k)) _

/-- (2) RC2 certificate for a random driver path independent of the free field. -/
theorem ae_C1_h0rev_random (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) (Q : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) {g : Ω → C(Icc (0 : ℝ) T, ℝ)} (hg : Measurable g)
    (hind : IndepFun g X P) :
    ∀ᵐ ω ∂P, GoodMeas.C1 (coordChange (ofFun (h0rev κ) + X ω) (revMap (Wof κ T hT (g ω)) T) Q) := by
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  exact ae_indep hg hXm hind (measurableSet_C1_h0rev κ hT Q) fun f => by
    filter_upwards [CoordReg.ae_isRegularSample_coordChange_h0rev' (continuous_Wof κ T hT f) hT hX
      κ Q] with ω hω
    obtain ⟨F, hF⟩ := hω
    exact GoodMeas.C1_of_regular hF

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- (3) A.s. the raw circle averages of `h⁰` converge at every centre of `Hbar`. -/
theorem ae_rawConverges_h0f (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, LocalRule.RawConverges (h0f κ T B X ω) Hbar := by
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
  intro k z hz
  refine ⟨_, (GoodMeas.tendsto_raw_of_C1 hC1 k hz).congr fun n => ?_⟩
  exact (key _ k).symm

/-- (4) A.s. `ν = e^{γ(−m)/2} • ν_{h⁰}`. -/
theorem ae_nuPalm_eq_smul (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (hT : 0 ≤ T) (ϖ : Measure ℂ) :
    ∀ᵐ ω ∂P, nuPalm κ T B X ϖ ω =
      ENNReal.ofReal (Real.exp (Real.sqrt κ * -(mReg κ T B X ϖ ω) / 2)) •
        qBoundaryMeasure (Real.sqrt κ) (h0f κ T B X ω) := by
  filter_upwards [ae_rawConverges_h0f (κ := κ) hB hX hind hT] with ω h
  exact LocalRule.qBoundaryMeasure_addConst' h _ _

/-- (5) Under B3(a), a.s. the boundary approximations of the normalized field `h⁰ − m` have a
vague limit (the existence hypothesis `hex` of `E1.restrict_nuPalm_eq`). -/
theorem ae_exists_isVagueLimitR_nuPalm (hReg : Blueprint.RevCouplingBoundaryMeasureRegular)
    (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (ϖ : Measure ℂ) :
    ∀ᵐ ω ∂P, ∃ l, IsVagueLimitR
      (bdryApprox (Real.sqrt κ) (addConst (h0f κ T B X ω) (-(mReg κ T B X ϖ ω)))) l := by
  obtain ⟨B'', hB'', hind'', hV⟩ := b2_V_brownian (κ := κ) hB hind hT.le
  filter_upwards [hReg κ hκ hκ4 T hT P B'' X hB'' hX hind'', hV,
    b2_ident_qBoundaryMeasure hB hX hind hT.le, ae_rawConverges_h0f (κ := κ) hB hX hind hT.le]
    with ω hRω hVω hid hraw
  have hrevV : revMap (Vr κ T B ω) T = revMap (drive κ B'' ω) T :=
    funext fun z => ReverseFlow.revMap_congr_drive z hVω
  have hcf : couplingFieldRev κ (Vr κ T B ω) T (X ω) =
      couplingFieldRev κ (drive κ B'' ω) T (X ω) := by
    simp only [couplingFieldRev, hrevV]
  have hne : qBoundaryMeasure (Real.sqrt κ) (h0f κ T B X ω) ≠ 0 := by
    rw [hid, hcf]
    intro h0
    have := hRω.2.1 0 1 one_pos
    rw [h0] at this
    simp at this
  have hex : ∃ ν, IsVagueLimitR (bdryApprox (Real.sqrt κ) (h0f κ T B X ω)) ν := by
    by_contra hn
    exact hne (by rw [qBoundaryMeasure, dif_neg hn])
  obtain ⟨ν, hν⟩ := hex
  set c := ENNReal.ofReal (Real.exp (Real.sqrt κ * -(mReg κ T B X ϖ ω) / 2)) with hc
  refine ⟨c • ν, ?_⟩
  have e : bdryApprox (Real.sqrt κ) (addConst (h0f κ T B X ω) (-(mReg κ T B X ϖ ω))) =
      fun k => c • bdryApprox (Real.sqrt κ) (h0f κ T B X ω) k :=
    funext (LocalRule.bdryApprox_addConst hraw _ _)
  rw [e]
  exact BdryVague.IsVagueLimitR.const_smul hν ENNReal.ofReal_ne_top

end E1
end QuantumZipper
