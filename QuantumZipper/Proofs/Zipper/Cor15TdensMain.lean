import QuantumZipper.Proofs.Zipper.Cor15TdensFixed
import QuantumZipper.Proofs.Zipper.Cor15TdensGood
import QuantumZipper.Proofs.Zipper.Cor15RezipFin2
import QuantumZipper.Proofs.Zipper.Cor15LastMain

/-!
# COR15-TDENS (3): `Cor15TdensRegStmt` (the last input of Corollary 1.5(a))

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18).
For each test function `ρ`, almost surely the unzipped field `y = (Z^CAP_{-t} x).1` satisfies
`RegShift y ν±` and `evalReg y ν± = y ν±` at `ν± = (tdens (±ρ)).map (revMapInv (vrev (√κ B) t) t)`.

Route (as `cor15RezipRegStmt`, `Cor15RezipFin2`, with the folded circle replaced by `tdens (±ρ)`):
fixed-driver theorem `ae_regShift_evalReg_pushed_tdens` (analytic input: Duplantier–Sheffield,
*Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), Prop. 3.1, via RC3), a.s. goodness
of the reversed driver `ae_rezip_good_gen`, and Fubini over the independent pair (path, field)
(`CharFunRhs.ae_indep_ae`) with the jointly measurable event `{RegShift} ∩ {finL = finR}`
(`measurableSet_regShift_raw`, `measurable_raw_finY`, `measurable_finL`, `measurable_finR`).
Finally `fwdMapInv W t = revMap (vrev W t) t` on `ℍ` transfers both properties to the unzipped
field. **Own elementary argument** (Fubini and measurability bookkeeping).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open CharFun B2

theorem ae_mem_of_null_diff {σ : Measure ℂ} {D : Set ℂ} (hσH : ∀ᵐ z ∂σ, z ∈ H)
    (hK : σ (H \ D) = 0) : ∀ᵐ z ∂σ, z ∈ D := by
  filter_upwards [hσH, measure_eq_zero_iff_ae_notMem.1 hK] with z hz h
  by_contra hc
  exact h ⟨hz, hc⟩

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **Regularity of the unzipped field at one pushed test density.** -/
theorem ae_tdens_reg_one (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {t : ℝ} (ht : 0 < t)
    {a : ℂ → ℝ} {K : Set ℂ} {Md δ : ℝ} (hd : Dens a K Md δ) :
    ∀ᵐ ω ∂P,
      E1.RegShift (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1
        ((tdens a).map (revMapInv (vrev (drive κ B ω) t) t)) ∧
      evalReg (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1
          ((tdens a).map (revMapInv (vrev (drive κ B ω) t) t)) =
        (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1
          ((tdens a).map (revMapInv (vrev (drive κ B ω) t) t)) := by
  set σ := tdens a with hσ
  have : IsFiniteMeasure σ := hd.admissible.1
  obtain ⟨R₀, hR₀⟩ := hd.compact.isBounded.subset_closedBall (0 : ℂ)
  have hσH : ∀ᵐ z ∂σ, z ∈ H :=
    (measure_eq_zero_iff_ae_notMem.1 hd.tdens_compl).mono fun z hz => hd.subH (by simpa using hz)
  obtain ⟨B₁, hB₁m, hB₁c, hB₁eq⟩ := CharFun.exists_good_version hB
  have hind₁ : IndepFun (pathOf B₁) X P :=
    hind.congr (hB₁eq.mono fun ω h => (funext fun s => (h s).symm : pathOf B ω = pathOf B₁ ω))
      (ae_eq_refl _)
  set g := CharFun.pathC t B₁ hB₁c with hgdef
  have hg : Measurable g := measurable_pathC t hB₁m hB₁c
  have hindg : IndepFun g X P := indepFun_pathC t hind₁ hB₁c
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  obtain ⟨β, hβ, hgood⟩ :=
    ae_rezip_good_gen hB hind hκ hκ4 ht hσH (lintegral_im_rpow_tdens_ne_top hd) R₀
  set E : Set (C(Icc (0 : ℝ) t, ℝ) × FieldSample) :=
    {p | E1.RegShift (coordChange (ofFun (h0rev κ) + p.2)
        (revMap (Wof κ t ht.le (finRevPath ht.le p.1)) t) (Qc (Real.sqrt κ)))
        (σ.map (revMapInv (Wof κ t ht.le (finRevPath ht.le p.1)) t))} ∩
      {p | finL κ ht σ p = finR κ ht σ p} with hEdef
  have hE : MeasurableSet E := by
    refine MeasurableSet.inter ?_
      (measurableSet_eq_fun (measurable_finL κ ht σ) (measurable_finR κ ht σ))
    exact measurableSet_regShift_raw
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
    have hσD := ae_mem_of_null_diff hσH hK'
    have hM' : ∀ r ∈ Icc (0 : ℝ) t, |Wof κ t ht.le (finRevPath ht.le (g ω)) r| ≤ M :=
      fun r hr' => by rw [hVeq hr']; exact hM r hr'
    filter_upwards [ae_regShift_evalReg_pushed_tdens hX κ (Qc (Real.sqrt κ))
      (continuous_finV κ ht (g ω)) (finV_zero κ ht (g ω)) ht hd hR₀ hK'
      (by rw [hF]; exact hS) hM' hC hβ (by rw [hF]; exact hHol) hc0 hc] with ω' h
    refine ⟨h.1, ?_⟩
    show finL κ ht σ (g ω, X ω') = finR κ ht σ (g ω, X ω')
    rw [finL_eq, finR_eq κ ht _ _ hσD]
    exact h.2
  have hmain := CharFunRhs.ae_indep_ae hg hXm hindg hE hfib
  filter_upwards [hmain, hgood, hrev, hB.cont, hB.eval_zero_ae_eq_zero] with ω hω hgd hF hc h0
  obtain ⟨hVc, -, -, hK, -⟩ := hgd
  obtain ⟨hF, -⟩ := hF
  obtain ⟨h1, h2⟩ := hω
  have hK' : σ (H \ revMap (Wof κ t ht.le (finRevPath ht.le (g ω))) t '' H) = 0 := by
    rw [hF]; exact hK
  have hσD := ae_mem_of_null_diff hσH hK'
  have h2' : finL κ ht σ (g ω, X ω) = finR κ ht σ (g ω, X ω) := h2
  rw [finL_eq, finR_eq κ ht _ _ hσD] at h2'
  have hinv : revMapInv (Wof κ t ht.le (finRevPath ht.le (g ω))) t =
      revMapInv (vrev (drive κ B ω) t) t :=
    revMapInv_congr_H fun z _ => congrFun hF z
  have h1' : E1.RegShift (coordChange (ofFun (h0rev κ) + X ω)
      (revMap (Wof κ t ht.le (finRevPath ht.le (g ω))) t) (Qc (Real.sqrt κ)))
      (σ.map (revMapInv (Wof κ t ht.le (finRevPath ht.le (g ω))) t)) := h1
  rw [hF, hinv] at h1' h2'
  have hWc : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  have hνH := ae_mem_H_map_revMapInv hVc ht.le (ae_mem_of_null_diff hσH hK)
  have hFF : EqOn (fwdMapInv (drive κ B ω) t) (revMap (vrev (drive κ B ω) t) t) H :=
    fun z hz => fwdMapInv_eq_revMap_vrev hWc hW0 ht.le hz
  refine ⟨?_, evalReg_unzip_eq_of hWc hW0 ht.le _ _ hνH h2'⟩
  exact regShift_congr_dyadic (fun n k z => (coordChange_congr_H _ hFF _
    (TwoPoint.foldedCircle_ae_mem_H _ (radius_pos k))).symm) h1'

/-- **COR15-TDENS: the last input of Corollary 1.5(a) at positive times.** -/
theorem cor15TdensRegStmt : Cor15TdensRegStmt := by
  intro κ hκ hκ4 t ht Ω _ P _ B X hB hX hind
  have key : ∀ ρ : TestFun H, ∀ᵐ ω ∂P,
      (E1.RegShift (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1
          ((tdens ρ.1).map (revMapInv (vrev (drive κ B ω) t) t)) ∧
        evalReg (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1
            ((tdens ρ.1).map (revMapInv (vrev (drive κ B ω) t) t)) =
          (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1
            ((tdens ρ.1).map (revMapInv (vrev (drive κ B ω) t) t))) ∧
      (E1.RegShift (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1
          ((tdens fun z => -ρ.1 z).map (revMapInv (vrev (drive κ B ω) t) t)) ∧
        evalReg (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1
            ((tdens fun z => -ρ.1 z).map (revMapInv (vrev (drive κ B ω) t) t)) =
          (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1
            ((tdens fun z => -ρ.1 z).map (revMapInv (vrev (drive κ B ω) t) t))) := fun ρ => by
    obtain ⟨M, δ, hd⟩ := exists_dens ρ
    filter_upwards [ae_tdens_reg_one hB hX hind hκ hκ4 ht hd,
      ae_tdens_reg_one hB hX hind hκ hκ4 ht hd.neg] with ω h1 h2
    exact ⟨h1, h2⟩
  exact ⟨fun ρ => (key ρ).mono fun ω h => ⟨h.1.1, h.2.1⟩,
    fun ρ => (key ρ).mono fun ω h => ⟨h.1.2, h.2.2⟩⟩

end Cor15Group
end QuantumZipper
