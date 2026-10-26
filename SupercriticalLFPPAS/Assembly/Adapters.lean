import SupercriticalLFPPAS.Compare.LocalizedComparison
import SupercriticalLFPPAS.Scaling.Dilation
import SupercriticalLFPPAS.Scaling.ScalingD
import SupercriticalLFPPAS.Geodesic.LFPP
import SupercriticalLFPPAS.Tightness.Annular
import SupercriticalLFPPAS.Separating.Lemma35Final
import SupercriticalLFPPAS.Separating.UnitGood
import SupercriticalLFPPAS.Local.Interface
import SupercriticalLFPPAS.Contraction.Lemma41
import SupercriticalLFPPAS.Main.Theorem
import SupercriticalLFPPAS.GoodRoot.RootEvent
import SupercriticalLFPPAS.ContractionStep.Main
import SupercriticalLFPPAS.Identification.NoContract
import SupercriticalLFPPAS.Proposition51.Final
import SupercriticalLFPPAS.Escape.Lemma62
import SupercriticalLFPPAS.Field.InterfaceForms
import SupercriticalLQGUniqueness.Frozen.Exists_strongLQGMetric_lfppLimit
import SupercriticalLQGUniqueness.Frozen.ExistsUnique_isLFPPExponent
import SupercriticalLQGUniqueness.B2.LscTop.InProbability
import LQGMetric.Papers.DFGPS.L2_1PolarJoint

/-!
# Assembly adapters and the main theorem composition

The comparison adapters and the existence/corollary arguments are proved here. The main theorem
is assembled from the landed packets, with only the corrected normalizer-window interface left
as an input.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set

namespace SupercriticalLFPPAS.Assembly

open SupercriticalLQGUniqueness (IsLFPPNormalizer)
open SupercriticalLFPPAS.Core

theorem kappaBounds_holds (S : Core.Setup) : Core.KappaBoundsStmt S :=
  fun _ζ h0 h1 => Compare.kappa_bounds S.ξ S.Q S.hQ S.m S.hm h0 h1

theorem locCompare_holds (S : Core.Setup) : Core.LocCompareStmt S :=
  fun _ζ h0 h1 => Compare.localized_comparison S.ξ S.Q S.hQ S.D S.hD S.m S.hm h0 h1

theorem exists_setup (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε)) : ∃ S : Core.Setup, S.ξ = ξ ∧ S.m = m := by
  obtain ⟨Q, hQ, -⟩ := SupercriticalLQGUniqueness.existsUnique_isLFPPExponent ξ
  obtain ⟨D, hD, hlim⟩ := SupercriticalLQGUniqueness.exists_strongLQGMetric_lfppLimit ξ Q hQ
  exact ⟨⟨ξ, Q, hQ, m, hm, D, hD, hlim⟩, rfl, rfl⟩

theorem allXi_of_mainAe (H : ∀ S : Core.Setup, Core.MainAeStmt S) :
    Core.Lfpp_ae_lscTendstoAllXiStmt := by
  intro ξ m hm Ω _ P _ h hh X hX hXc L hL
  obtain ⟨S, hSξ, hSm⟩ := exists_setup ξ m hm
  subst hSξ hSm
  have hBdd : LQGMetric.IsGFFPlusBddCont h P := LQGMetric.DFGPS.isGFFPlusBddCont_of_wp hh.1
  have hD := S.hlim S.m S.hm P h hBdd X hX
  have hae := SupercriticalLQGUniqueness.B2.LscTop.LSCTendstoInProbability.ae_eq_limit hL hD
  filter_upwards [H S P h hh X ⟨hX, hXc⟩, hae] with ω h1 h2
  intro ε hε
  rw [h2]
  exact h1 ε hε

/-- Compose all landed packets into §7, leaving Lemma 6.1's normalizer window as the only input. -/
theorem mainAe_holds_of_window (hWindow : ∀ S : Core.Setup, Core.NormalizerWindowStmt S) :
    ∀ S : Core.Setup, Core.MainAeStmt S := by
  intro S
  have hScale : Core.ScalingDStmt S := Scaling.scalingD_holds S
  have hDilation : Core.DilationStmt S := Scaling.dilation_holds S
  have hKappa : Core.KappaBoundsStmt S := kappaBounds_holds S
  have hCompare : Core.LocCompareStmt S := locCompare_holds S
  have hLocA : Core.LocApproxStmt := Field.locApprox_holds
  have hMesh : Core.MeshOscStmt := Field.meshOsc_holds
  have hUnif : Core.UnifLocStmt := Field.unifLoc_holds
  have hTight : Core.AnnTightStmt S := Tightness.annTight_of S hUnif
  have h32Meas : Core.Lemma32MeasStmt S := Local.lemma32Meas_holds S
  have h32Local : Core.Lemma32LocalityStmt S := Local.lemma32Locality_holds S
  have h32Loc : Core.Lemma32LocStmt S := Local.lemma32Loc_of S h32Meas hUnif
  have h35 : Core.Lemma35Stmt S := Separating.lemma35_of S hKappa hScale hDilation hTight
  have hUnit : Core.UnitGoodStmt S := Separating.unitGood_of S h32Loc h32Local h35 hTight
  have hRoot : Core.RootEventStmt S := GoodRoot.rootEvent_of S hUnit hScale hDilation
  have h41 : Core.Lemma41Stmt := Contraction.lemma41_holds
  have hContr : Core.ContractionStmt S := ContractionStep.contraction_of S hRoot h41
  have hConf : Core.ConfinementStmt S := Local.confinement_of S hCompare hLocA
  have hCircle : Core.LocCircleStmt S := Local.locCircle_of S hCompare hLocA
  have hGeo : Core.LFPPGeodesicStmt := Geodesic.lfppGeodesic_holds
  have hNo : Core.NoContractStmt S := Identification.noContract_of S hConf hCircle hLocA hGeo
  have h51 : Core.Prop51Stmt S := Proposition51.prop51_of S hContr hCompare hNo
  have hW : Core.NormalizerWindowStmt S := hWindow S
  have h62 : Core.Lemma62Stmt S := Escape.lemma62_of S hCompare hLocA hMesh hW
  apply Main.mainAe_of S
  · exact h51
  · exact hW
  · exact h62
  · exact hMesh
  · exact hLocA
  · exact hGeo

/-- The unfrozen all-ξ corollary, conditional only on Lemma 6.1. -/
theorem lfpp_ae_lscTendsto_allXi_of_window
    (hWindow : ∀ S : Core.Setup, Core.NormalizerWindowStmt S) :
    Core.Lfpp_ae_lscTendstoAllXiStmt :=
  allXi_of_mainAe (mainAe_holds_of_window hWindow)

/-- The frozen anchor's exact statement, conditional only on Lemma 6.1. -/
theorem lfpp_ae_lscTendsto_of_window
    (hWindow : ∀ S : Core.Setup, Core.NormalizerWindowStmt S) :
    Core.Lfpp_ae_lscTendstoStmt := by
  intro ξ _
  exact lfpp_ae_lscTendsto_allXi_of_window hWindow ξ

end SupercriticalLFPPAS.Assembly
