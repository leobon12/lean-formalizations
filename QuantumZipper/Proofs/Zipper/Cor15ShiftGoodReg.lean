import QuantumZipper.Proofs.Zipper.Cor15ShiftGoodFix
import QuantumZipper.Proofs.Zipper.Cor15TdensMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# COR15-SHIFTGOOD (2): convergence form of RC3 for the unzipped field at re-zip-pushed circles

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18).
For every folded circle `σ = fc(w₀, r₀)` and `t > 0`, almost surely the unzipped field
`y_t = unzippedField √κ c t` satisfies `E1.RegShift` at `σ.map f_t`, `f_t = revMapInv (vrev W t) t`
(the centered forward map, i.e. the zipping map of `y_t`).

Route: exactly `ae_tdens_reg_one` (`Cor15TdensMain`) with the test density replaced by a folded
circle: fixed-driver theorem `ae_regShift_coordChange_pushed_fc` (`Cor15ShiftGoodFix`; analytic
input Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Prop. 3.1, via RC3), the a.s. goodness of the reversed driver `ae_rezip_good`
(`Cor15RezipRegGood`), and Fubini over the independent pair (path, field)
(`CharFunRhs.ae_indep_ae`) with the measurable event `measurableSet_regShift_raw`.
**Own elementary argument** (Fubini and measurability bookkeeping, copied from
`ae_tdens_reg_one`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open CharFun B2

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **Convergence form of RC3 for the unzipped field at one re-zip-pushed folded circle.** -/
theorem ae_regShift_unzip_pushed_fc (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {t : ℝ} (ht : 0 < t)
    (w₀ : ℂ) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∀ᵐ ω ∂P,
      E1.RegShift (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t)
        ((foldedCircle w₀ r₀).map (revMapInv (vrev (drive κ B ω) t) t)) := by
  set σ := foldedCircle w₀ r₀ with hσ
  obtain ⟨B₁, hB₁m, hB₁c, hB₁eq⟩ := CharFun.exists_good_version hB
  have hind₁ : IndepFun (pathOf B₁) X P :=
    hind.congr (hB₁eq.mono fun ω h => (funext fun s => (h s).symm : pathOf B ω = pathOf B₁ ω))
      (ae_eq_refl _)
  set g := CharFun.pathC t B₁ hB₁c with hgdef
  have hg : Measurable g := measurable_pathC t hB₁m hB₁c
  have hindg : IndepFun g X P := indepFun_pathC t hind₁ hB₁c
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  obtain ⟨β, hβ, hgood⟩ := ae_rezip_good hB hind hκ hκ4 ht w₀ hr₀
  set E : Set (C(Icc (0 : ℝ) t, ℝ) × FieldSample) :=
    {p | E1.RegShift (coordChange (ofFun (h0rev κ) + p.2)
        (revMap (Wof κ t ht.le (finRevPath ht.le p.1)) t) (Qc (Real.sqrt κ)))
        (σ.map (revMapInv (Wof κ t ht.le (finRevPath ht.le p.1)) t))} with hEdef
  have hE : MeasurableSet E :=
    measurableSet_regShift_raw
      (y := fun p : C(Icc (0 : ℝ) t, ℝ) × FieldSample => coordChange (ofFun (h0rev κ) + p.2)
        (revMap (Wof κ t ht.le (finRevPath ht.le p.1)) t) (Qc (Real.sqrt κ)))
      (fun n k => measurable_raw_finY κ ht _ n k)
      (f := fun p z => revMapInv (Wof κ t ht.le (finRevPath ht.le p.1)) t z)
      ((measurable_finInv κ ht).comp
        (f := fun q : (C(Icc (0 : ℝ) t, ℝ) × FieldSample) × ℂ => (q.1.1, q.2))
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)) σ
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
    have hM' : ∀ r ∈ Icc (0 : ℝ) t, |Wof κ t ht.le (finRevPath ht.le (g ω)) r| ≤ M :=
      fun r hr' => by rw [hVeq hr']; exact hM r hr'
    filter_upwards [ae_regShift_coordChange_pushed_fc hX κ (Qc (Real.sqrt κ))
      (continuous_finV κ ht (g ω)) (finV_zero κ ht (g ω)) ht hr₀ hK' (by rw [hF]; exact hS) hM'
      hC hβ (by rw [hF]; exact hHol) hc0 hc] with ω' h
    exact h
  have hmain := CharFunRhs.ae_indep_ae hg hXm hindg hE hfib
  filter_upwards [hmain, hrev, hB.cont, hB.eval_zero_ae_eq_zero] with ω hω hF hc h0
  obtain ⟨hF, -⟩ := hF
  have h1 : E1.RegShift (coordChange (ofFun (h0rev κ) + X ω)
      (revMap (Wof κ t ht.le (finRevPath ht.le (g ω))) t) (Qc (Real.sqrt κ)))
      (σ.map (revMapInv (Wof κ t ht.le (finRevPath ht.le (g ω))) t)) := hω
  have hinv : revMapInv (Wof κ t ht.le (finRevPath ht.le (g ω))) t =
      revMapInv (vrev (drive κ B ω) t) t :=
    revMapInv_congr_H fun z _ => congrFun hF z
  rw [hF, hinv] at h1
  have hWc : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  have hFF : EqOn (fwdMapInv (drive κ B ω) t) (revMap (vrev (drive κ B ω) t) t) H :=
    fun z hz => fwdMapInv_eq_revMap_vrev hWc hW0 ht.le hz
  exact regShift_congr_dyadic (fun n k z => (coordChange_congr_H _ hFF _
    (TwoPoint.foldedCircle_ae_mem_H _ (radius_pos k))).symm) h1

end Cor15Group
end QuantumZipper
