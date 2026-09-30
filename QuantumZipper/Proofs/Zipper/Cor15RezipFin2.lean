import QuantumZipper.Proofs.Zipper.Cor15RezipFin
import QuantumZipper.Proofs.Zipper.Cor15HullNull

/-!
# Corollary 1.5, positive times: `cor15RezipRegStmt` (input (R) proved)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18).
Assembly of (R) = `Cor15RezipRegStmt` from the fixed-driver theorem
`ae_evalReg_coordChange_pushed_fc` (analytic input: Duplantier–Sheffield, *Liouville quantum
gravity and KPZ*, Invent. Math. 185 (2011), Prop. 3.1, via RC3), the a.s. goodness of the
reversed driver `ae_rezip_good`, and Fubini over the independent pair (path, field)
(`CharFunRhs.ae_indep_ae`) with the jointly measurable event of `Cor15RezipFin`.
**Own elementary argument** (Fubini bookkeeping).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open CharFun B2

/-- The reversed driver of the path `pathC t B₁` agrees on `[0,t]` with `vrev (√κ B) t`. -/
theorem finV_pathC_eqOn {κ t : ℝ} (ht : 0 < t) {Ω : Type*} {B B₁ : ℝ≥0 → Ω → ℝ}
    (hB₁c : ∀ ω, Continuous fun s => B₁ s ω) {ω : Ω} (hb : ∀ s, B₁ s ω = B s ω) :
    EqOn (Wof κ t ht.le (finRevPath ht.le (CharFun.pathC t B₁ hB₁c ω)))
      (vrev (drive κ B ω) t) (Icc 0 t) := by
  intro r hr
  rw [finV_apply κ ht _ hr]
  simp only [vrev, drive, max_eq_left hr.1, min_eq_left hr.2]
  show Real.sqrt κ * (B₁ (t - r).toNNReal ω - B₁ t.toNNReal ω) = _
  rw [hb, hb]
  ring

/-- **Input (R) of Corollary 1.5 at positive times.** A.s. the unzipped field is regular at the
image under `f_t = revMapInv (vrev W t) t` of each dyadic folded circle. -/
theorem cor15RezipRegStmt : Cor15RezipRegStmt := by
  intro κ hκ hκ4 t ht Ω _ P _ B X hB hX hind i
  set σ := foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 with hσ
  have hr := UnzipFull.fullIndex_radius_pos i
  obtain ⟨B₁, hB₁m, hB₁c, hB₁eq⟩ := CharFun.exists_good_version hB
  have hind₁ : IndepFun (pathOf B₁) X P :=
    hind.congr (hB₁eq.mono fun ω h => (funext fun s => (h s).symm : pathOf B ω = pathOf B₁ ω))
      (ae_eq_refl _)
  set g := CharFun.pathC t B₁ hB₁c with hgdef
  have hg : Measurable g := measurable_pathC t hB₁m hB₁c
  have hindg : IndepFun g X P := indepFun_pathC t hind₁ hB₁c
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  obtain ⟨β, hβ, hgood⟩ := ae_rezip_good hB hind hκ hκ4 ht (CoordsFull.fullIndex i).1 hr
  set E : Set (C(Icc (0 : ℝ) t, ℝ) × FieldSample) := {p | finL κ ht σ p = finR κ ht σ p}
    with hEdef
  have hE : MeasurableSet E := measurableSet_eq_fun (measurable_finL κ ht σ) (measurable_finR κ ht σ)
  have hrev : ∀ᵐ ω ∂P,
      revMap (Wof κ t ht.le (finRevPath ht.le (g ω))) t = revMap (vrev (drive κ B ω) t) t ∧
      EqOn (Wof κ t ht.le (finRevPath ht.le (g ω))) (vrev (drive κ B ω) t) (Icc 0 t) := by
    filter_upwards [hB₁eq] with ω hb
    have heq := finV_pathC_eqOn (κ := κ) ht hB₁c hb
    exact ⟨funext fun z => ReverseFlow.revMap_congr_drive z heq, heq⟩
  have hfib : ∀ᵐ ω ∂P, ∀ᵐ ω' ∂P, (g ω, X ω') ∈ E := by
    filter_upwards [hgood, hrev] with ω hω hF
    obtain ⟨-, -, hS, hK, ⟨c, hc0, hc⟩, M, hM, C, hC, hHol⟩ := hω
    obtain ⟨hF, hVeq⟩ := hF
    have hK' : σ (H \ revMap (Wof κ t ht.le (finRevPath ht.le (g ω))) t '' H) = 0 := by
      rw [hF]; exact hK
    have hσD := ae_mem_revMap_image_fc hr hK'
    have hM' : ∀ r ∈ Icc (0 : ℝ) t, |Wof κ t ht.le (finRevPath ht.le (g ω)) r| ≤ M :=
      fun r hr' => by rw [hVeq hr']; exact hM r hr'
    filter_upwards [ae_evalReg_coordChange_pushed_fc hX κ (Qc (Real.sqrt κ))
      (continuous_finV κ ht (g ω)) (finV_zero κ ht (g ω)) ht hr hK' (by rw [hF]; exact hS) hM'
      hC hβ (by rw [hF]; exact hHol) hc0 hc] with ω' h
    show finL κ ht σ (g ω, X ω') = finR κ ht σ (g ω, X ω')
    rw [finL_eq, finR_eq κ ht _ _ hσD]
    exact h
  have hmain := CharFunRhs.ae_indep_ae hg hXm hindg hE hfib
  filter_upwards [hmain, hgood, hrev, hB.cont, hB.eval_zero_ae_eq_zero] with ω hω hgd hF hc h0
  obtain ⟨hVc, -, -, hK, -⟩ := hgd
  obtain ⟨hF, -⟩ := hF
  have hK' : σ (H \ revMap (Wof κ t ht.le (finRevPath ht.le (g ω))) t '' H) = 0 := by
    rw [hF]; exact hK
  have hσD := ae_mem_revMap_image_fc hr hK'
  have h1 : finL κ ht σ (g ω, X ω) = finR κ ht σ (g ω, X ω) := hω
  rw [finL_eq, finR_eq κ ht _ _ hσD] at h1
  have hinv : revMapInv (Wof κ t ht.le (finRevPath ht.le (g ω))) t =
      revMapInv (vrev (drive κ B ω) t) t :=
    revMapInv_congr_H fun z _ => congrFun hF z
  rw [hF, hinv] at h1
  exact evalReg_unzip_eq_of (drive_continuous hc) (drive_zero h0) ht.le _ _
    (ae_mem_H_map_revMapInv hVc ht.le (ae_mem_revMap_image_fc hr hK)) h1

/-- **The field half of the re-zip identity** (blocker 1 of Corollary 1.5 at `t > 0`), now
unconditional: (K0) `cor15HullNullStmt` and (R) `cor15RezipRegStmt` are both proved. -/
theorem cor15RezipFieldStmt_holds : Cor15RezipFieldStmt :=
  cor15RezipFieldStmt_of cor15HullNullStmt cor15RezipRegStmt

end Cor15Group
end QuantumZipper
