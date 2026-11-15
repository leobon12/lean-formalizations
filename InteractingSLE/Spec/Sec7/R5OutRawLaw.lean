/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutDecay
import InteractingSLE.Spec.Sec7.R5EnlAdded
import InteractingSLE.Spec.Sec7.PocketStopSideEndLaws

/-!
# The ambient reference versus the marked raw union

PROVE-R5-OUTER, R98 §2. The smaller ambient hull germ is retained before
transporting the two kernels. The current `raw` chart records an open
complement and need not be conformal or connected. Every version of each
physical mean is covered by the resulting increment law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.R5Out

open LocalSets PocketStopSide R5Enl WholeField

variable {Ω : Type*} {ℋ₀ ℋ₁ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {K B : Ω → Set ℂ}

/-- The ambient-hull to raw-union increment law, including the smaller
hull germ in the later record. The raw complement can have several components. -/
theorem hasAmbientRawIncrementLawOn_of_marked
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hInfo : ℋ₀ ≤ ℋ₁) (hℋ₁ : ℋ₁ ≤ mΩ)
    (hKm : Measurable[ℋ₀, hittingSigma] K) (hBm : Measurable[ℋ₁, hittingSigma] B)
    (hKreg : ∀ ω, K ω ⊆ H ∧ IsOpen (H \ K ω))
    (hBreg : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω))
    (hKloc : IsHistoryAvoidanceLocal ℋ₀ K h P)
    (hBloc : IsHistoryAvoidanceLocal ℋ₁ B h P)
    (hSub : ∀ ω, K ω ∩ H ⊆ B ω)
    {G : Set Ω} (hG : MeasurableSet[germSigma K h ⊔ ℋ₀] G)
    {old : Ω → Chart} (hOld : ∀ ω ∈ G, (old ω).IsConformal)
    (hfwd : ∀ z, Measurable[germSigma K h ⊔ ℋ₀]
      ((G ∩ {ω | z ∈ (old ω).dom}).indicator fun ω => (old ω).1 z))
    (hOldDom : ∀ ω ∈ G, ((old ω).dom : Set ℂ) = H \ K ω)
    {M : Set Ω} (hMG : M ⊆ G) {raw : Ω → Chart}
    (hRawDom : ∀ ω ∈ M, ((raw ω).dom : Set ℂ) = H \ B ω) :
    ∀ gK : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean K h P gK →
      ∀ gB : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean B h P gB →
        HasOldChartIncrementLawOn P M old raw gK gB := by
  have hℋ₀ : ℋ₀ ≤ mΩ := hInfo.trans hℋ₁
  have hKm' : Measurable[mΩ, hittingSigma] K := hKm.mono hℋ₀ le_rfl
  have hBm' : Measurable[mΩ, hittingSigma] B := hBm.mono hℋ₁ le_rfl
  have hGermK : germSigma K h ≤ mΩ := germSigma_le hKm' hh.measurable
  have hLater : ℋ₁ ⊔ germSigma K h ≤ mΩ := sup_le hℋ₁ hGermK
  have hBloc' : IsHistoryAvoidanceLocal (ℋ₁ ⊔ germSigma K h) B h P :=
    Lemma725RefMarks.isHistoryAvoidanceLocal_sup_germSigma hh hℋ₁ hBm' hBloc
      (hKm.mono hInfo le_rfl) hSub
  obtain ⟨g₀, hg₀, hHarm₀, hK₀⟩ := Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal
    hh hKm' hℋ₀ hKloc (ae_of_all P hKreg)
  have hNest : ∀ ω, H \ B ω ⊆ H \ K ω := fun ω z hz =>
    ⟨hz.1, fun hzK => hz.2 (hSub ω ⟨hzK, hz.1⟩)⟩
  have hRecords : germSigma K h ⊔ ℋ₀ ≤ germSigma B h ⊔ (ℋ₁ ⊔ germSigma K h) :=
    sup_le (le_sup_right.trans le_sup_right) (hInfo.trans (le_sup_left.trans le_sup_right))
  exact hasOldChartIncrementLawOn_of_enlarged_marked_fwd hh le_sup_left hg₀ hHarm₀ hK₀
    hLater hLater hBm' (ae_of_all P hBreg) hBloc' hBm' (ae_of_all P hBreg) hBloc' hRecords
    (E := univ) MeasurableSet.univ MeasurableSet.univ (fun _ _ => rfl) rfl hG hOld hfwd
    hOldDom (fun ω _ => (hKreg ω).2) (fun ω _ => (hBreg ω).2) (fun ω _ => hNest ω)
    hMG (subset_univ M) hRawDom

end InteractingSLE.Sec7.R5Out
