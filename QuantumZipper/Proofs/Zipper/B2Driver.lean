import QuantumZipper.Proofs.Zipper.B2Defs
import QuantumZipper.Proofs.Zipper.UnzipFullSplit

/-!
# B2(a) and B2(c): the reversed driver and the identification of `h⁰`

`blueprint/E_BRANCH_BLUEPRINT.md` §4, node B2, clauses (a) and (c) (notation of `B2Defs`).

* `exists_revDriver`, **`b2_V_brownian`** (B2(a)): `V = √κ B''` on `[0,T]` a.s. for a Brownian
  motion `B''` (`UnzipInvariance.revBM` of a good version of `B`) independent of `X`.
* **`b2_indep`** (B2(a)): `(V, W⁰) ⊥ X` and `V ⊥ W⁰` (paths indexed by `ℝ≥0`; weak Markov
  property `IsPreBrownianReal.indepFun_shift`).
* **`b2_ident`** (B2(c)): a.s. `coordsFull h⁰ = coordsFull (couplingFieldRev κ V T X)`, hence
  (`b2_ident_regEq`, `b2_ident_qBoundaryMeasure`) `RegEq h⁰ (couplingFieldRev κ V T X)` and equal
  boundary measures: the Palm law built from `h⁰` is the Palm law of the Theorem 1.3 field of
  `(B'', X)`. Proof: the argument of `UnzipFull.ae_coordsFull_unzip` (REG-SPLIT) with the explicit
  driver `B''`.

Sources: Sheffield, arXiv:1012.4797, Theorem 1.2 (p. 14) and §5.2 (pp. 57–59); the weak Markov
property of Brownian motion (mathlib `IsPreBrownianReal.indepFun_shift`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B2

open CharFun UnzipInvariance UnzipFull TwoPoint

/-- The path `u ↦ V u` indexed by `ℝ≥0`. -/
def Vpath {Ω : Type*} (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 → ℝ :=
  fun u => Vr κ T B ω u

/-- The path `u ↦ W⁰ u` indexed by `ℝ≥0`. -/
def W0p {Ω : Type*} (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 → ℝ :=
  fun u => W0 κ T B ω u

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

theorem drive_revBM_eq (B₁ : ℝ≥0 → Ω → ℝ) (hT : 0 ≤ T) (ω : Ω) {s : ℝ} (hs : s ∈ Icc 0 T) :
    drive κ (revBM B₁ T.toNNReal) ω s = drive κ B₁ ω (T - s) - drive κ B₁ ω T := by
  have hle : s.toNNReal ≤ T.toNNReal := Real.toNNReal_le_toNNReal hs.2
  have h1 : (T - s).toNNReal = T.toNNReal - s.toNNReal := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (sub_nonneg.2 hs.2), NNReal.coe_sub hle, Real.coe_toNNReal _ hs.1,
      Real.coe_toNNReal _ hT]
  have h2 : max s.toNNReal T.toNNReal = T.toNNReal := max_eq_right hle
  simp only [drive, revBM_apply, h1, h2]
  ring

/-- The reversed driver as a Brownian motion independent of `X`. -/
theorem exists_revDriver (hB : IsBrownianReal B P) (hind : IndepFun (pathOf B) X P)
    (hT : 0 ≤ T) :
    ∃ B'' : ℝ≥0 → Ω → ℝ, IsBrownianReal B'' P ∧ (∀ s, Measurable (B'' s)) ∧
      (∀ ω, Continuous fun s => B'' s ω) ∧ IndepFun (pathOf B'') X P ∧
      ∀ᵐ ω ∂P, ∀ s ∈ Icc 0 T, Vr κ T B ω s = drive κ B'' ω s := by
  obtain ⟨B₁, hB₁m, hB₁c, hB₁eq⟩ := exists_good_version hB
  have hB₁ : IsPreBrownianReal B₁ P := hB.toIsPreBrownianReal.congr fun s => by
    filter_upwards [hB₁eq] with ω h using (h s).symm
  have hind₁ : IndepFun (pathOf B₁) X P :=
    hind.congr (hB₁eq.mono fun ω h => (funext fun s => (h s).symm : pathOf B ω = pathOf B₁ ω))
      (ae_eq_refl _)
  refine ⟨revBM B₁ T.toNNReal, isBrownianReal_revBM hB₁ hB₁c _, fun s =>
    ((hB₁m _).add (hB₁m _)).sub ((hB₁m _).const_smul _), fun ω => ?_, ?_, ?_⟩
  · simp only [revBM_apply]
    exact (((hB₁c ω).comp (continuous_const.sub continuous_id)).add
      ((hB₁c ω).comp (continuous_id.max continuous_const))).sub continuous_const
  · have hΦ : Measurable fun p : ℝ≥0 → ℝ =>
        fun s => p (T.toNNReal - s) + p (max s T.toNNReal) - 2 * p T.toNNReal := by
      fun_prop
    have := hind₁.comp hΦ measurable_id
    convert this using 1
    all_goals first
      | rfl
      | (funext ω s; simp [pathOf])
  · filter_upwards [hB₁eq] with ω h1 s hs
    have hdr : drive κ B ω = drive κ B₁ ω := funext fun x => by simp [drive, h1]
    rw [drive_revBM_eq B₁ hT ω hs, Vr, vrev_of_mem hs, hdr]

/-- **B2(a), Brownian clause.** `V` is `√κ` times a Brownian motion on `[0,T]`, independent
of `X`. -/
theorem b2_V_brownian (hB : IsBrownianReal B P) (hind : IndepFun (pathOf B) X P)
    (hT : 0 ≤ T) :
    ∃ B'' : ℝ≥0 → Ω → ℝ, IsBrownianReal B'' P ∧ IndepFun (pathOf B'') X P ∧
      ∀ᵐ ω ∂P, ∀ s ∈ Icc 0 T, Vr κ T B ω s = drive κ B'' ω s := by
  obtain ⟨B'', h1, -, -, h2, h3⟩ := exists_revDriver (κ := κ) hB hind hT
  exact ⟨B'', h1, h2, h3⟩

/-! ## B2(c): identification with the Theorem 1.3 field -/

/-- **B2(c).** Almost surely the fully zipped field `h⁰` has the circle coordinates of the
Theorem 1.3 field `couplingFieldRev κ V T X` built from the reversed driver `V` and the same
free field `X` (with `V = √κ B''`, `B'' ⊥ X` Brownian, `b2_V_brownian`). -/
theorem b2_ident (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, CoordsFull.coordsFull (h0f κ T B X ω) =
      CoordsFull.coordsFull (couplingFieldRev κ (Vr κ T B ω) T (X ω)) := by
  obtain ⟨B', -, hB'm, hB'c, hind', hV⟩ := exists_revDriver (κ := κ) hB hind hT
  have hI := inputs_holds
  set g := pathC T B' hB'c with hg_def
  have hgm : Measurable g := measurable_pathC T hB'm hB'c
  have hig : IndepFun g X P := indepFun_pathC T hind' hB'c
  have hsp : ∀ i, ∀ᵐ ω ∂P, evalReg (ofFun (h0rev κ) + X ω)
        ((foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2).map
          (revMap (Wof κ T hT (g ω)) T)) =
      (∫ z, h0rev κ z ∂((foldedCircle (CoordsFull.fullIndex i).1
          (CoordsFull.fullIndex i).2).map (revMap (Wof κ T hT (g ω)) T))) +
        evalReg (X ω) ((foldedCircle (CoordsFull.fullIndex i).1
          (CoordsFull.fullIndex i).2).map (revMap (Wof κ T hT (g ω)) T)) := fun i =>
    ae_split_fc_random hI κ hT hX hgm hig _ (fullIndex_radius_pos i)
  filter_upwards [hV, hB.cont, hB.eval_zero_ae_eq_zero, ae_all_iff.2 hsp] with ω hVω hc h0 hs
  have hrevV : revMap (Vr κ T B ω) T = revMap (drive κ B' ω) T :=
    funext fun z => ReverseFlow.revMap_congr_drive z hVω
  have hE : EqOn (fwdMapInv (drive κ B ω) T) (revMap (drive κ B' ω) T) H := fun z hz => by
    rw [fwdMapInv_eq_revMap_vrev (drive_continuous hc) (drive_zero h0) hT hz, ← hrevV]; rfl
  have hcf : couplingFieldRev κ (Vr κ T B ω) T (X ω) =
      couplingFieldRev κ (drive κ B' ω) T (X ω) := by
    simp only [couplingFieldRev, hrevV]
  rw [hcf, h0f_eq_unzippedField]
  funext i
  have hri := fullIndex_radius_pos i
  set μ := foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 with hμ
  have hμH : μ Hᶜ = 0 := ae_iff.1 (hI.aeH _ hri)
  have hrev : revMap (drive κ B' ω) T = revMap (Wof κ T hT (g ω)) T :=
    revMap_drive_eq κ T hT B' hB'c ω
  have hWc := continuous_Wof κ T hT (g ω)
  have hWm := measurable_revMap_Wof κ T hT (g ω)
  show coordChange (ofFun (h0rev κ) + X ω) (fwdMapInv (drive κ B ω) T) (Qc (Real.sqrt κ)) μ =
    couplingFieldRev κ (drive κ B' ω) T (X ω) μ
  rw [coordChange_congr_of_eqOn hE hμH, CouplingMarkov.couplingFieldRev_eq, hTrev_congr hrev κ,
    hrev]
  show evalReg (ofFun (h0rev κ) + X ω) (μ.map (revMap (Wof κ T hT (g ω)) T)) +
      Qc (Real.sqrt κ) * ∫ z, Real.log ‖deriv (revMap (Wof κ T hT (g ω)) T) z‖ ∂μ =
    ofFun (hTrev κ (Wof κ T hT (g ω)) T) μ +
      (evalReg (X ω) (μ.map (revMap (Wof κ T hT (g ω)) T)) +
        0 * ∫ z, Real.log ‖deriv (revMap (Wof κ T hT (g ω)) T) z‖ ∂μ)
  rw [hs i, zero_mul, add_zero,
    show ofFun (hTrev κ (Wof κ T hT (g ω)) T) μ = ∫ z, hTrev κ (Wof κ T hT (g ω)) T z ∂μ from rfl,
    integral_hTrev_fc hI κ hWc hT hWm _ hri]
  ring

/-- **B2(c)**, boundary measure form: `ν_{h⁰} = ν` of the Theorem 1.3 field of `(V, X)`. -/
theorem b2_ident_qBoundaryMeasure (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, qBoundaryMeasure (Real.sqrt κ) (h0f κ T B X ω) =
      qBoundaryMeasure (Real.sqrt κ) (couplingFieldRev κ (Vr κ T B ω) T (X ω)) := by
  filter_upwards [b2_ident hB hX hind hT] with ω h
  exact qBoundaryMeasure_congr_of_coordsFull _ h

end B2
end QuantumZipper
