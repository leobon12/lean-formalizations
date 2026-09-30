import QuantumZipper.Proofs.Thm18.G1Z5Bm
import QuantumZipper.Proofs.Thm18.G1Z4Side
import QuantumZipper.Proofs.Thm18.G4WedgeCert
import QuantumZipper.Proofs.Thm18.G1ProfileRed
import QuantumZipper.Proofs.Thm18.G1Z2ReflChord

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z5 (D58, S1): `G1Z4SideLimStmt` from the per-path node

`g1Z4SideLimStmt_of_path : G1Z4SideLimPathStmt → G1RegRepRC2Stmt → G1Z4SideLimStmt`.

The measurable good set is `{p | RepGood true} ∩ {p | RepGood false}`, where `RepGood left m c`
(for the selected map `m = Ψ left a` and the circle coordinates `c`) asks for
* RC2 of the pulled-back field (`G1Meas.measurableSet_rc2`),
* the countable side certificate `SideCert` (G1Z5SideCert.lean),
* the boundary certificate `E1.M4.BCert` of the rebuilt field (vague boundary limit),
* the countable transport identity `IdT` for the glued test family, read with the
  path-measurable boundary map `bm` (G1Z5Bm.lean).
On it the side limit exists (`sideLim_of_cert`) and equals the pullback
(`eq_pullback_of_ident`, with `Φ` from `G1Z2.sideReflChordStmt_holds`, `glue_bm`). Almost sure
membership: for a.e. path (`G1RC.ae_map_pathOf_of_chord`), the per-path node gives the side
limit, hence `SideCert` and `IdT`; `BCert` of the wedge is `ae_certF_of_isQuantumWedge`; RC2 is
`G1RegRepRC2Stmt`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1Z5

open GoodSample GoodMeas
open BdryVague (testFam bump continuous_testFam hasCompactSupport_testFam continuous_bump
  hasCompactSupport_bump)

/-- The transport identity for one test function. -/
def IdT (γ : ℝ) (left : Bool) (m : ℂ → ℂ) (c : ℕ → ℝ) (g : ℝ → ℝ) : Prop :=
  Tendsto (fun k => ∫ t, g (bm m left t) ∂bdryR γ (coordChange (E1.fromC c) m (Qc γ))
    (goodRad (k, 1))) atTop (𝓝 (limUnder atTop fun k => ∫ t, g t ∂bdryApprox γ (E1.fromC c) k))

/-- The good pairs for one side. -/
def RepGood (γ : ℝ) (left : Bool) (m : ℂ → ℂ) (c : ℕ → ℝ) : Prop :=
  IsRegularSample (coordChange (E1.fromC c) m (Qc γ)) ∧
    SideCert γ left (coordChange (E1.fromC c) m (Qc γ)) ∧ E1.M4.BCert γ (E1.fromC c) ∧
    (∀ N n : ℕ, IdT γ left m c (glue left (testFam N n))) ∧
    ∀ N : ℕ, IdT γ left m c (glue left (bump N))

theorem bCert_congr {γ : ℝ} {x x' : FieldSample} (h : avgReg x = avgReg x') :
    E1.M4.BCert γ x ↔ E1.M4.BCert γ x' := by
  have hb : bdryApprox γ x = bdryApprox γ x' := by
    funext k; unfold bdryApprox; rw [h]
  simp only [E1.M4.BCert, hb]

theorem measurableSet_repGood {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ)
    (left : Bool) : MeasurableSet {p : G1PathData | RepGood γ left (Ψ left p.1) p.2.1} := by
  have hM : Measurable fun q : G1PathData × ℂ => Ψ left q.1.1 q.2 :=
    (hΨ.1 left).comp (measurable_fst.fst.prodMk measurable_snd)
  have hMd : Measurable fun q : G1PathData × ℂ => Real.log ‖deriv (Ψ left q.1.1) q.2‖ :=
    (hΨ.2.1 left).comp (measurable_fst.fst.prodMk measurable_snd)
  have hy : Measurable fun p : G1PathData => E1.fromC p.2.1 :=
    G1Meas.measurable_fromC'.comp measurable_snd.fst
  have hco : ∀ i, Measurable fun p : G1PathData =>
      CoordsFull.coordsFull (coordChange (E1.fromC p.2.1) (Ψ left p.1) (Qc γ)) i :=
    fun i => G1Meas.measurable_coordsFull_coordChange (ψ := fun p : G1PathData => Ψ left p.1)
      hy hM hMd (Qc γ) i
  have hZ : Measurable fun p : G1PathData =>
      E1.fromC (CoordsFull.coordsFull (coordChange (E1.fromC p.2.1) (Ψ left p.1) (Qc γ))) :=
    G1Meas.measurable_fromC'.comp (measurable_pi_iff.2 hco)
  have hT : ∀ g : ℝ → ℝ, Measurable g →
      MeasurableSet {p : G1PathData | IdT γ left (Ψ left p.1) p.2.1 g} := by
    intro g hg
    have e : ∀ p : G1PathData, bdryR γ (coordChange (E1.fromC p.2.1) (Ψ left p.1) (Qc γ)) =
        bdryR γ (E1.fromC (CoordsFull.coordsFull
          (coordChange (E1.fromC p.2.1) (Ψ left p.1) (Qc γ)))) := fun p =>
      bdryR_congr_avg (CoordsFull.avgReg_congr_full (E1.coordsFull_fromC _)).symm
    unfold IdT
    simp_rw [e]
    refine measurableSet_tendsto_fun (fun k => ?_) ?_
    · exact measurable_integral_bdryR_param hZ
        (G := fun (p : G1PathData) t => g (bm (Ψ left p.1) left t))
        (hg.comp (measurable_bm (M := fun p : G1PathData => Ψ left p.1) hM left)) γ
        (mul_pos one_pos (radius_pos k))
    · exact (StronglyMeasurable.limUnder fun k =>
        ((LQGMeas.meas_integral_bdryApprox γ k hg).comp hy).stronglyMeasurable).measurable
  simp only [RepGood, ofPred_and, ofPred_forall]
  refine (G1Meas.measurableSet_rc2 hΨ left).inter ((measurableSet_sideCert_of_coords γ left hco).inter
    ((hy (E1.M4.measurableSet_bCert γ)).inter ((MeasurableSet.iInter fun N =>
      MeasurableSet.iInter fun n => hT _ ?_).inter (MeasurableSet.iInter fun N => hT _ ?_))))
  · exact (continuous_glue left (continuous_testFam N n) (hasCompactSupport_testFam N n)).measurable
  · exact (continuous_glue left (continuous_bump N) (hasCompactSupport_bump N)).measurable

/-- The side limit tested against `glue G ∘ Φ`. -/
theorem tendsto_glue_comp {γ : ℝ} {left : Bool} {z : FieldSample} {ν : Measure ℝ}
    (hν : G1Z2SideBdryLim γ left z ν) {Φ : ℝ ≃o ℝ} (h0 : Φ 0 = 0) {G : ℝ → ℝ}
    (hG : Continuous G) (hGc : HasCompactSupport G) :
    Tendsto (fun k => ∫ t, glue left G (Φ t) ∂bdryR γ z (goodRad (k, 1))) atTop
      (𝓝 (∫ t, glue left G (Φ t) ∂ν)) := by
  have hg := continuous_glue left hG hGc
  have hgc := hasCompactSupport_glue left hG hGc
  have hgS := tsupport_glue_side left hG hGc
  have hIm : Φ '' g1SideHalf left = g1SideHalf left := image_g1SideHalf h0 left
  have hImS : Φ.symm '' g1SideHalf left = g1SideHalf left := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [← hIm] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      simpa using hv
    · intro ht
      refine ⟨Φ t, ?_, Φ.symm_apply_apply t⟩
      rw [← hIm]; exact mem_image_of_mem _ ht
  have hcompc : HasCompactSupport (glue left G ∘ Φ) :=
    IsCompact.of_isClosed_subset (hgc.image Φ.symm.continuous) (isClosed_tsupport _)
      (tsupport_comp_iso_subset hgc Φ)
  have hcompS : tsupport (glue left G ∘ Φ) ⊆ g1SideHalf left := by
    refine (tsupport_comp_iso_subset hgc Φ).trans ?_
    rw [← hImS]; exact image_mono hgS
  exact (hν.2.2 _ (hg.comp Φ.continuous) hcompc hcompS).comp tendsto_one_goodFilter

theorem integral_glue_pullback {left : Bool} (μ : Measure ℝ) (Φ : ℝ ≃o ℝ) {G : ℝ → ℝ}
    (hG : Continuous G) (hGc : HasCompactSupport G) :
    ∫ t, glue left G (Φ t) ∂((μ.restrict (g1SideHalf left)).map Φ.symm) =
      ∫ t, glue left G t ∂μ := by
  have hg := continuous_glue left hG hGc
  have hgS := tsupport_glue_side left hG hGc
  rw [integral_map (f := fun t => glue left G (Φ t)) Φ.symm.continuous.aemeasurable
    (hg.comp Φ.continuous).aestronglyMeasurable]
  simp only [OrderIso.apply_symm_apply]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht =>
    image_eq_zero_of_notMem_tsupport fun h => ht (hgS h)

end G1Z5

end Thm18Asm
end QuantumZipper
