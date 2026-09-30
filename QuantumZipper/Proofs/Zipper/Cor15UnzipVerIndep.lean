import QuantumZipper.Proofs.Zipper.Cor15UnzipVerMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# COR15-UNZIPVER (2): the Markov input `Cor15UnzipCoordIndepStmt` holds

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.4 (Corollary 1.5).
Task COR15-UNZIPVER.

The circle coordinates of the unzipped field `D_a c` are a.s. a measurable function of the
field `X` and of the reversed Brownian path on `[0, a]` (`UnzipFull.exists_unzip_driver`,
`UnzipInvariance.coordChange_congr_of_eqOn`, `B1Full.measurable_unzip_apply`), hence of `X` and
the past `B|[0,a]`; they are therefore independent of the future increments `B(a + ·) − B(a)` by
the weak Markov property with an independent field (`UnzipInvariance.indepFun_of_past_future`;
Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Prop. 2.5 (simple Markov
property)).

* `cor15UnzipCoordIndepStmt_holds : Cor15UnzipCoordIndepStmt`.
* `cor15UnzipVersionStmt_of_freeCircleRecon`: `Cor15UnzipVersionStmt` from the reconstruction
  input alone.
* `theorem1_5_of_theorem1_3_of_freeCircleRecon`: Corollary 1.5 from Theorem 1.3, the
  reconstruction input, the round-trip field half and the zip version.

Own bookkeeping around the cited Markov property.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open CoordsFull B1Full CharFun UnzipInvariance

/-- **The Markov input holds.** -/
theorem cor15UnzipCoordIndepStmt_holds : Cor15UnzipCoordIndepStmt := by
  intro κ _ _ Ω _ P _ B X hS a ha
  obtain ⟨hB, hX, hind⟩ := hS
  have ha0 : (0 : ℝ) ≤ a := ha.le
  set τ : ℝ≥0 := a.toNNReal with hτ
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  -- a good version of `B`
  obtain ⟨B₁, hB₁m, hB₁c, hB₁eq⟩ := exists_good_version hB
  have hB₁ : IsPreBrownianReal B₁ P := hB.toIsPreBrownianReal.congr fun s => by
    filter_upwards [hB₁eq] with ω h using (h s).symm
  have hind₁ : IndepFun (pathOf B₁) X P :=
    hind.congr (hB₁eq.mono fun ω h => (funext fun s => (h s).symm : pathOf B ω = pathOf B₁ ω))
      (ae_eq_refl _)
  -- the reversed path on `[0, a]`
  have hRc : ∀ ω, Continuous fun s => revBM B₁ τ s ω := fun ω => by
    simp only [revBM_apply]
    exact (((hB₁c ω).comp (continuous_const.sub continuous_id)).add
      ((hB₁c ω).comp (continuous_id.max continuous_const))).sub continuous_const
  have hEq : ∀ᵐ ω ∂P, EqOn (fwdMapInv (drive κ B ω) a) (revMap (drive κ (revBM B₁ τ) ω) a) H := by
    filter_upwards [hB₁eq, hB₁.eval_zero_ae_eq_zero] with ω h1 h0 w hw
    have hdr : drive κ B ω = drive κ B₁ ω := funext fun x => by simp [drive, h1]
    rw [hdr, fwdMapInv_eq_revMap_timeRev _ (drive_continuous (hB₁c ω)) (drive_zero h0) ha0 hw,
      revMap_timeRev_eq_drive_revBM κ B₁ ha0 ω w]
  set g : Ω → C(Icc (0 : ℝ) a, ℝ) := pathC a (revBM B₁ τ) hRc with hg
  -- the measurable reading of the coordinates
  set Ψ : C(Icc (0 : ℝ) a, ℝ) × FieldSample → ℕ → ℝ := fun p =>
    coordsFull (coordChange (ofFun (h0rev κ) + p.2) (revMap (Wof κ a ha0 p.1) a)
      (Qc (Real.sqrt κ)) - ofFun (h0rev κ)) with hΨ
  have hfcH : ∀ i, foldedCircle (fullIndex i).1 (fullIndex i).2 Hᶜ = 0 := fun i =>
    ae_iff.1 (TwoPoint.foldedCircle_ae_mem_H _ (UnzipFull.fullIndex_radius_pos i))
  have hΨm : Measurable Ψ := measurable_pi_iff.2 fun i =>
    (measurable_unzip_apply κ a ha0 _ (hfcH i)).sub measurable_const
  -- the coordinates agree a.s. with `Ψ (g, X)`
  have hae : (fun ω => coordsFull ((zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω)).1 -
      ofFun (h0rev κ))) =ᵐ[P] fun ω => Ψ (g ω, X ω) := by
    filter_upwards [hEq] with ω hE
    funext i
    simp only [hΨ, coordsFull, Pi.sub_apply, zipCapDown]
    rw [coordChange_congr_of_eqOn hE (hfcH i), revMap_drive_eq κ a ha0 _ hRc ω]
  -- the future path
  have hfut : (fun ω => shiftPath a (pathOf B ω)) =ᵐ[P]
      fun ω (s : ℝ≥0) => B₁ (τ + s) ω - B₁ τ ω := by
    filter_upwards [hB₁eq] with ω h
    funext s
    simp only [shiftPath, pathOf, hτ, h]
  -- measurability of `g` with respect to the past
  have hgP : @Measurable Ω _
      (MeasurableSpace.comap (fun ω (u : Set.Iic τ) => B₁ u ω) MeasurableSpace.pi) _ g := by
    let _ : MeasurableSpace Ω :=
      MeasurableSpace.comap (fun ω (u : Set.Iic τ) => B₁ u ω) MeasurableSpace.pi
    refine ContinuousMap.measurable_iff_eval.2 fun x => ?_
    have hs : x.1.toNNReal ≤ τ := Real.toNNReal_le_toNNReal x.2.2
    have e : (fun ω => g ω x) = (fun f : Set.Iic τ → ℝ =>
        f ⟨τ - x.1.toNNReal, Set.mem_Iic.2 tsub_le_self⟩ + f ⟨τ, Set.mem_Iic.2 le_rfl⟩ -
          2 * f ⟨τ, Set.mem_Iic.2 le_rfl⟩) ∘ (fun ω (u : Set.Iic τ) => B₁ u ω) := by
      funext ω
      simp only [hg, pathC, ContinuousMap.coe_mk, revBM_apply, Function.comp_apply,
        max_eq_right hs]
    have hm : Measurable (fun f : Set.Iic τ → ℝ =>
        f ⟨τ - x.1.toNNReal, Set.mem_Iic.2 tsub_le_self⟩ + f ⟨τ, Set.mem_Iic.2 le_rfl⟩ -
          2 * f ⟨τ, Set.mem_Iic.2 le_rfl⟩) := by fun_prop
    rw [e]
    exact hm.comp (comap_measurable _)
  have hF : @Measurable Ω _ (MeasurableSpace.comap (fun ω (u : Set.Iic τ) => B₁ u ω) MeasurableSpace.pi ⊔
      MeasurableSpace.comap X MeasurableSpace.pi) _
      (fun ω => Ψ (g ω, X ω)) := by
    have h1 : @Measurable Ω _ (MeasurableSpace.comap (fun ω (u : Set.Iic τ) => B₁ u ω) MeasurableSpace.pi ⊔
      MeasurableSpace.comap X MeasurableSpace.pi) _ g :=
      hgP.mono le_sup_left le_rfl
    have h2 : @Measurable Ω _ (MeasurableSpace.comap (fun ω (u : Set.Iic τ) => B₁ u ω) MeasurableSpace.pi ⊔
      MeasurableSpace.comap X MeasurableSpace.pi) _ X :=
      (comap_measurable X).mono le_sup_right le_rfl
    exact hΨm.comp (h1.prodMk h2)
  have hG : @Measurable Ω _ (MeasurableSpace.comap (fun ω (s : ℝ≥0) => B₁ (τ + s) ω - B₁ τ ω)
      MeasurableSpace.pi) _ (fun ω (s : ℝ≥0) => B₁ (τ + s) ω - B₁ τ ω) :=
    comap_measurable _
  have hI := indepFun_of_past_future hB₁ hB₁m hXm hind₁ τ hF hG
  exact hI.congr hae.symm hfut.symm

/-- **`Cor15UnzipVersionStmt` from the reconstruction input alone.** -/
theorem cor15UnzipVersionStmt_of_freeCircleRecon (hRec : FreeCircleReconStmt) :
    Cor15UnzipVersionStmt :=
  cor15UnzipVersionStmt_of_recon hRec cor15UnzipCoordIndepStmt_holds

end Cor15Group
end QuantumZipper
