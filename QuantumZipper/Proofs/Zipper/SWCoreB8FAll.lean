import QuantumZipper.Proofs.Zipper.SWCoreB8FId
import QuantumZipper.Proofs.Zipper.SWCoreB7dFinal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B8F (8): `RegUnif.YMergeOffInputStmt` and `WedgeUnzip.YMergeOffTipStmt`

* **`anchorUnifFamOffStmt_holds`**: `RegUnif.AnchorUnifFamOffStmt` (offset AC-fam-ext) at every
  horizon: the anchor `q = 0` uses the pair `(B, X)`, a rational anchor `q > 0` the pair
  `(B^q, Y_q)` of `Cor15Group.cor15UnzipVersionStmt_holds` (as `anchorUnifFamExtStmt_holds`,
  SWCoreB7dFinal.lean), through `acfam_off_of_pair` and `ident_off_of_pair`;
* **`yMergeOffInputStmt_holds`**: `RegUnif.YMergeOffInputStmt` (pair and reflected pair);
* **`yMergeOffTipStmt_holds`**: `WedgeUnzip.YMergeOffTipStmt`, by
  `RegUnif.yMergeOffTipStmt_of_offInput` (SWCoreB8UoMain.lean).

Sources: Sheffield–Wang arXiv:1605.06171 Thm 1.4 (continuous radius) and Thm 4.3 (all maps at
once), through the D64 family cores with the dilation as a family parameter and the D70
independence transfer; Sheffield arXiv:1012.4797 Thm 1.2, §1.4 (anchor fields). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace SWCore

open CharFun B2 B5 RevMapExtension RegUnif

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

set_option maxHeartbeats 1000000 in
/-- **Offset AC-fam-ext at one horizon** (SWC-B8). -/
theorem anchorUnifFamOffStmt_holds {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    {T : ℝ} (hT : 0 < T) : RegUnif.AnchorUnifFamOffStmt κ T P B X := by
  intro q hq hqT u v i a b c d
  by_cases hord : (u : ℝ) < a ∧ (a : ℝ) < b ∧ (b : ℝ) < c ∧ (c : ℝ) < d ∧ (d : ℝ) < v
  swap
  · exact ae_of_all _ fun ω h1 h2 h3 h4 h5 _ => absurd ⟨h1, by exact_mod_cast h2,
      by exact_mod_cast h3, by exact_mod_cast h4, h5⟩ hord
  obtain ⟨h1, h2, h3, h4, h5⟩ := hord
  have hfs := RegUnif.tsupport_swFam_subset (i := i) h2 h4
  have hfc : Continuous (RegUnif.swFam i a b c d) := RegUnif.continuous_swFam _ _ _ _ _
  have hfcs : HasCompactSupport (RegUnif.swFam i a b c d) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hfs
  have hfsub : tsupport (RegUnif.swFam i a b c d) ⊆ Ioo (u : ℝ) v := fun x hx =>
    ⟨lt_of_lt_of_le h1 (hfs hx).1, lt_of_le_of_lt (hfs hx).2 h5⟩
  have huv : (u : ℝ) < v := by linarith
  have hcont : ∀ᵐ ω ∂P, (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) → ∀ s ∈ Icc (q : ℝ) T,
      ∀ k : ℕ, ContinuousOn
        (fun e => awIntOff κ T B X ω u v (swFam i a b c d) s (k, e)) (Icc (1 : ℝ) 2) := by
    filter_upwards [awIntOff_contC hκ hκ4 hT hB hX hind q hq hqT.le u v] with ω h hv
    exact h huv hv _ hfc hfcs hfsub
  rcases hq.eq_or_lt with hq0 | hq0
  · -- anchor `0`: the pair `(B, X)`
    have hq0' : q = 0 := by exact_mod_cast hq0.symm
    subst hq0'
    have hRE : ∀ᵐ ω ∂P, ∀ σ : ℚ, (σ : ℝ) ∈ Icc (0 : ℝ) (T - ((0 : ℚ) : ℝ)) →
        RegEq (h0f κ (((0 : ℚ) : ℝ) + σ) B X ω) (coordChange (ofFun (h0rev κ) + X ω)
          (revMap (vrev (drive κ B ω) σ) σ) (Qc (Real.sqrt κ))) := by
      filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hc h0 σ hσ
      simp only [Rat.cast_zero, zero_add, sub_zero] at hσ ⊢
      have hW : Continuous (drive κ B ω) := drive_continuous hc
      have hW0 : drive κ B ω 0 = 0 := by simp [drive, h0]
      have hEq : EqOn (fwdMapInv (drive κ B ω) σ) (revMap (vrev (drive κ B ω) σ) σ) H := by
        intro w hw
        rw [UnzipInvariance.fwdMapInv_eq_revMap_timeRev _ hW hW0 hσ.1 hw]
        exact ReverseFlow.revMap_congr_drive w (fun r hr => (vrev_of_mem hr).symm)
      intro k z
      rw [h0f_eq_unzippedField]
      simp only [unzippedField, cfg]
      rw [Cor15Group.avgReg_coordChange_congr_H _ hEq _]
    have hwin : ∀ᵐ ω ∂P, ∀ σ : ℚ, (σ : ℝ) ∈ Icc (0 : ℝ) (T - ((0 : ℚ) : ℝ)) →
        realRevMap (Vr κ T B ω) (T - (((0 : ℚ) : ℝ) + σ)) =
          realRevMap (vrev (drive κ B ω) (T - ((0 : ℚ) : ℝ))) (T - ((0 : ℚ) : ℝ) - σ) :=
      ae_of_all _ fun ω σ _ => by simp only [Rat.cast_zero, zero_add, sub_zero]; rfl
    filter_upwards [acfam_off_of_pair hκ hκ4 hqT h1 h2 h3 h4 h5 hB hX hind
      (ident_off_of_pair hB hX hind hq hqT hκ hB hX hind hRE hwin u v _)
      (live_zero hκ hκ4 hB hT v) hcont] with ω hω
    intro _ _ _ _ _ hv
    exact hω hv
  · -- rational anchor `q > 0`: the pair `(B^q, Y_q)`
    obtain ⟨Y, -, hYf, hYind, hreg⟩ :=
      Cor15Group.cor15UnzipVersionStmt_holds κ hκ hκ4 P B X ⟨hB, hX, hind⟩ q hq0
    have hreg' : ∀ᵐ ω ∂P, RegEq (h0f κ q B X ω) (ofFun (h0rev κ) + Y ω) := by
      filter_upwards [hreg] with ω h
      rw [h0f_eq_zipCapDown]; exact h
    have hBq : IsBrownianReal (shB q B) P := hB.shift (q : ℝ).toNNReal
    have hindq : IndepFun (pathOf (shB q B)) Y P := hYind
    have hRE : ∀ᵐ ω ∂P, ∀ σ : ℚ, (σ : ℝ) ∈ Icc (0 : ℝ) (T - q) →
        RegEq (h0f κ ((q : ℝ) + σ) B X ω) (coordChange (ofFun (h0rev κ) + Y ω)
          (revMap (vrev (drive κ (shB q B) ω) σ) σ) (Qc (Real.sqrt κ))) := by
      refine ae_all_iff.2 fun σ => ?_
      by_cases hσ : (σ : ℝ) ∈ Icc (0 : ℝ) (T - q)
      swap
      · exact ae_of_all _ fun ω h => absurd h hσ
      filter_upwards [b2_regEq (κ := κ) (T := (q : ℝ) + σ) (t := σ) hB hX hind hσ.1
        (by linarith [hq0.le] : (σ : ℝ) ≤ q + σ), hreg'] with ω hb hr _
      have e := Yf_horizon_eq_h0f (B := B) (X := X) κ q ((q : ℝ) + σ) ω
      rw [add_sub_cancel_left] at e
      rw [e, coordChange_congr_regEq hr] at hb
      have hmap : revMap (Vr κ ((q : ℝ) + σ) B ω) σ = revMap (vrev (drive κ (shB q B) ω) σ) σ :=
        funext fun z => ReverseFlow.revMap_congr_drive z
          (fun r hr => (vrev_shB_eqOn κ B ω hq hσ.1 hr).symm)
      rw [hmap] at hb
      exact hb
    have hwin : ∀ᵐ ω ∂P, ∀ σ : ℚ, (σ : ℝ) ∈ Icc (0 : ℝ) (T - q) →
        realRevMap (Vr κ T B ω) (T - ((q : ℝ) + σ)) =
          realRevMap (vrev (drive κ (shB q B) ω) (T - q)) (T - q - σ) := by
      refine ae_of_all _ fun ω σ hσ => ?_
      funext x
      rw [show T - ((q : ℝ) + σ) = T - q - σ by ring]
      refine B5.realRevMap_congr_drive' (fun r hr => ?_) x
      have hT0 : 0 ≤ T - q := hσ.1.trans hσ.2
      have h := vrev_shB_eqOn κ B ω hq hT0 (⟨hr.1, by linarith [hr.2, hσ.1]⟩ :
        r ∈ Icc (0 : ℝ) (T - q))
      rw [show (q : ℝ) + (T - q) = T by ring] at h
      exact h.symm
    filter_upwards [acfam_off_of_pair hκ hκ4 hqT h1 h2 h3 h4 h5 hBq hYf hindq
      (ident_off_of_pair hB hX hind hq hqT hκ hBq hYf hindq hRE hwin u v _)
      (live_pos hκ hκ4 hB hT hq hqT v) hcont] with ω hω
    intro _ _ _ _ _ hv
    exact hω hv

/-- **`RegUnif.YMergeOffInputStmt` holds** (SWC-B8): offset AC-fam-ext at every horizon, for the
pair and its reflection. -/
theorem yMergeOffInputStmt_holds : RegUnif.YMergeOffInputStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  exact ⟨fun T hT => anchorUnifFamOffStmt_holds hκ hκ4 hB hX hind hT,
    fun T hT => anchorUnifFamOffStmt_holds hκ hκ4 hB.neg
      (RegUnif.isFreeGFFModConstH_reflRaw hX) (RegUnif.indepFun_neg_reflRaw hind) hT⟩

/-- **`WedgeUnzip.YMergeOffTipStmt` holds** (offset merging off the tip for `y_t`, a.s. all
`t ≥ 0`). -/
theorem yMergeOffTipStmt_holds : WedgeUnzip.YMergeOffTipStmt :=
  RegUnif.yMergeOffTipStmt_of_offInput yMergeOffInputStmt_holds

end SWCore
end QuantumZipper
