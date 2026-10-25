import SLUFieldSupport
import LQGMetric.Meas.LocalEvent
import LQGMetric.Meas.LocalEventRandom2
import LQGMetric.Field.StandardBorelRange
import LQGMetric.Papers.CONF.S3D110A
import LQGMetric.Papers.GM.S4.L46Meas
import LQGMetric.Papers.GM.S2.SpatialIndepShift
import LQGMetric.Papers.GM.S3.DeterministicScale
import LQGMetric.Papers.GM.S2.SpatialIndepAsm1
import LQGMetric.Papers.DFGPS.L2_19
import LQGMetric.Field.CircleAvgAffine
import LQGMetric.Papers.GM.S2.TightLaw




 







set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric.Blueprint
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Toolkit.LocalEvents

open LQGMetric (DistC DistOn restrictTo pairJ)

 

theorem isGFFPlusCont_addConst
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : LQGMetric.IsGFFPlusCont h P)
    {c : Ω → ℝ} (hc : Measurable c) :
    LQGMetric.IsGFFPlusCont (fun ω => LQGMetric.addConst (h ω) (c ω)) P := by
  obtain ⟨hm, f, hfm, hwhole⟩ := hh
  refine ⟨LQGMetric.DFGPS.L219.measurable_addConst_of hm hc, f, hfm, ?_⟩
  have he : (fun ω => LQGMetric.addConst (h ω) (c ω) - LQGMetric.ofCont (f ω)) =
      (fun ω => LQGMetric.addConst (h ω - LQGMetric.ofCont (f ω)) (c ω)) := by
    funext ω
    ext φ
    simp only [sub_apply, LQGMetric.GFFInv.addConst_apply]
    ring
  rw [he]
  exact hwhole.addConst hc

 
theorem isGFFPlusCont_normIn
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : LQGMetric.IsGFFPlusCont h P)
    (ψ : LQGMetric.TestC) :
    LQGMetric.IsGFFPlusCont (LQGMetric.CONF.normIn h ψ) P := by
  exact isGFFPlusCont_addConst hh
    (((LQGMetric.measurable_evalDist ψ).comp hh.1).neg)

 

theorem aeEventIn_fieldSigma0On_of_normIn
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (h : Ω → DistC) (ψ : LQGMetric.TestC)
    (hψ : ∫ x, ψ x = 1) (U : TopologicalSpace.Opens ℂ)
    (hψU : tsupport (ψ : ℂ → ℝ) ⊆ (U : Set ℂ)) {E : Set Ω}
    (hE : AEEventIn P (fieldSigma (LQGMetric.CONF.normIn h ψ) U) E) :
    AEEventIn P (fieldSigma0On h U) E := by
  have hsigma : fieldSigma (LQGMetric.CONF.normIn h ψ) U =
      fieldSigma0On h U := by
    exact (LQGMetric.GM.gm_fieldSigma_eq_fieldSigma0On hψ
      (LQGMetric.CONF.normIn_apply_psi h hψ) hψU).trans
        (LQGMetric.CONF.fieldSigma0On_normIn h ψ U)
  rw [← hsigma]
  exact hE

 

theorem aeEventIn_fieldSigmaClosed0_of_normIn
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (h : Ω → DistC) (ψ : LQGMetric.TestC)
    (hψ : ∫ x, ψ x = 1) (K : Set ℂ)
    (hψK : tsupport (ψ : ℂ → ℝ) ⊆ K) {E : Set Ω}
    (hE : ∀ n : ℕ,
      AEEventIn P
        (fieldSigma (LQGMetric.CONF.normIn h ψ)
          (nbhdO (1 / ((n : ℝ) + 1)) K)) E) :
    AEEventIn P (fieldSigmaClosed0 h K) E := by
  have hclosed : AEEventIn P (fieldSigmaClosed (LQGMetric.CONF.normIn h ψ) K) E :=
    LQGMetric.GM.gm_aeEventIn_fieldSigmaClosed _ K hE
  rw [← LQGMetric.CONF.fieldSigmaClosed_normIn_eq h hψ hψK]
  exact hclosed

 
theorem exists_local_event_versions
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (m : MeasurableSpace Ω) {ι : Type} [Countable ι] (E : ι → Set Ω)
    (hE : ∀ i, @AEEventIn Ω mΩ P m (E i)) :
    ∃ F : ι → Set Ω, (∀ i, MeasurableSet[m] (F i)) ∧
      (∀ᵐ ω ∂P, ∀ i, (ω ∈ E i ↔ ω ∈ F i)) := by
  classical
  choose F hFm hEF using hE
  refine ⟨F, hFm, ?_⟩
  rw [ae_all_iff]
  intro i
  filter_upwards [hEF i] with ω hω
  exact Iff.of_eq hω

 

theorem aeEventIn_translate
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (g : Ω → DistC) (z : ℂ) (U V : TopologicalSpace.Opens ℂ)
    (hUV : ∀ y : ℂ, y ∈ V ↔ (1 : ℝ) • y + z ∈ U)
    {E : Set Ω} (hE : AEEventIn P (fieldSigma g U) E) :
    AEEventIn P (fieldSigma
      (fun ω => LQGMetric.affineComp 1 z (g ω)) V) E := by
  obtain ⟨F, hFm, hFa⟩ := hE
  exact ⟨F, LQGMetric.GM.fieldSigma_le_affineComp one_pos hUV g F hFm, hFa⟩

 

theorem aeEventIn_internal_family
    {ι : Type} [Fintype ι] (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : ι → DistC → LSCMetric)
    (hD : ∀ i, IsWeakLQGMetric ξ Q (D i))
    (U : TopologicalSpace.Opens ℂ)
    (Φ : (ι → (↥(U : Set ℂ) × ↥(U : Set ℂ) → ℝ≥0∞)) → DistOn U → Prop)
    (hB : NullMeasurableSet
      {g : DistC | Φ (fun i => (D i g).internal (U : Set ℂ)) (restrictTo U g)} μ) :
    AEEventIn μ (fieldSigma id U)
      {g : DistC | Φ (fun i => (D i g).internal (U : Set ℂ)) (restrictTo U g)} := by
  classical
  let B : Set DistC :=
    {g | Φ (fun i => (D i g).internal (U : Set ℂ)) (restrictTo U g)}
  have hLoc : ∀ i : ι, ∃ F : DistOn U →
      (↥(U : Set ℂ) × ↥(U : Set ℂ) → ℝ≥0∞),
      ∀ᵐ g ∂μ, (D i g).internal (U : Set ℂ) = F (restrictTo U g) := by
    intro i
    obtain ⟨F, _, hF⟩ := (hD i).locality μ id hμ U
    exact ⟨F, hF⟩
  choose F hF using hLoc
  let Wraw : Set DistC :=
    {g | ∀ i, (D i g).internal (U : Set ℂ) = F i (restrictTo U g)}
  have hWraw : ∀ᵐ g ∂μ, g ∈ Wraw := by
    change ∀ᵐ g ∂μ, ∀ i, (D i g).internal (U : Set ℂ) = F i (restrictTo U g)
    exact ae_all_iff.mpr hF
  obtain ⟨W, hWae, hWm, hWsub⟩ := hWraw.exists_measurable_mem
  let R : DistC → LQGMetric.CoordJ → ℝ :=
    fun g => pairJ U (restrictTo U g)
  have hR : Measurable R :=
    (LQGMetric.measurable_pairJ U).comp (LQGMetric.measurable_restrictTo U)
  have hV : Measurable[fieldSigma id U] R :=
    (LQGMetric.measurable_pairJ U).comp (Measurable.of_comap_le le_rfl)
  have hSat : ∀ g₁ ∈ W, ∀ g₂ ∈ W,
      R g₁ = R g₂ → g₁ ∈ B → g₂ ∈ B := by
    intro g₁ hg₁ g₂ hg₂ he hB₁
    have hRes : restrictTo U g₁ = restrictTo U g₂ :=
      LQGMetric.injective_pairJ U he
    have hInt : ∀ i, (D i g₁).internal (U : Set ℂ) =
        (D i g₂).internal (U : Set ℂ) := by
      intro i
      calc
        _ = F i (restrictTo U g₁) := hWsub g₁ hg₁ i
        _ = F i (restrictTo U g₂) := by rw [hRes]
        _ = _ := (hWsub g₂ hg₂ i).symm
    change Φ (fun i => (D i g₁).internal (U : Set ℂ)) (restrictTo U g₁) at hB₁
    change Φ (fun i => (D i g₂).internal (U : Set ℂ)) (restrictTo U g₂)
    simp only [← hInt, ← hRes]
    exact hB₁
  simpa only [B, Set.preimage_id] using
    (LQGMetric.LocalEvent.aeEventIn_of_saturated
      (Y := id) (R := R) (V := R) (B := B) (W := W)
      measurable_id hR hV (Filter.Eventually.of_forall fun _ => rfl)
      hWm (by simpa only [B, Measure.map_id] using hB) hWae hSat)


 

theorem aeEventIn_internal_windows
    {ι : Type} [Fintype ι] (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : ι → DistC → LSCMetric)
    (hD : ∀ i, IsWeakLQGMetric ξ Q (D i))
    (U : TopologicalSpace.Opens ℂ) (Ui : ι → TopologicalSpace.Opens ℂ)
    (hUi : ∀ i, Ui i ≤ U)
    (Φ : (∀ i, (↥(Ui i : Set ℂ) × ↥(Ui i : Set ℂ) → ℝ≥0∞)) →
      DistOn U → Prop)
    (hB : NullMeasurableSet
      {g : DistC | Φ (fun i => (D i g).internal (Ui i : Set ℂ)) (restrictTo U g)} μ) :
    AEEventIn μ (fieldSigma id U)
      {g : DistC | Φ (fun i => (D i g).internal (Ui i : Set ℂ)) (restrictTo U g)} := by
  classical
  let B : Set DistC :=
    {g | Φ (fun i => (D i g).internal (Ui i : Set ℂ)) (restrictTo U g)}
  have hLoc : ∀ i : ι, ∃ F : DistOn (Ui i) →
      (↥(Ui i : Set ℂ) × ↥(Ui i : Set ℂ) → ℝ≥0∞),
      ∀ᵐ g ∂μ, (D i g).internal (Ui i : Set ℂ) = F (restrictTo (Ui i) g) := by
    intro i
    obtain ⟨F, _, hF⟩ := (hD i).locality μ id hμ (Ui i)
    exact ⟨F, hF⟩
  choose F hF using hLoc
  let Wraw : Set DistC :=
    {g | ∀ i, (D i g).internal (Ui i : Set ℂ) = F i (restrictTo (Ui i) g)}
  have hWraw : ∀ᵐ g ∂μ, g ∈ Wraw := by
    change ∀ᵐ g ∂μ, ∀ i,
      (D i g).internal (Ui i : Set ℂ) = F i (restrictTo (Ui i) g)
    exact ae_all_iff.mpr hF
  obtain ⟨W, hWae, hWm, hWsub⟩ := hWraw.exists_measurable_mem
  let R : DistC → LQGMetric.CoordJ → ℝ :=
    fun g => pairJ U (restrictTo U g)
  have hR : Measurable R :=
    (LQGMetric.measurable_pairJ U).comp (LQGMetric.measurable_restrictTo U)
  have hV : Measurable[fieldSigma id U] R :=
    (LQGMetric.measurable_pairJ U).comp (Measurable.of_comap_le le_rfl)
  have hSat : ∀ g₁ ∈ W, ∀ g₂ ∈ W,
      R g₁ = R g₂ → g₁ ∈ B → g₂ ∈ B := by
    intro g₁ hg₁ g₂ hg₂ he hB₁
    have hRes : restrictTo U g₁ = restrictTo U g₂ :=
      LQGMetric.injective_pairJ U he
    have hResi : ∀ i, restrictTo (Ui i) g₁ = restrictTo (Ui i) g₂ := by
      intro i
      calc
        _ = LQGMetric.GM.distRes (Ui i) U (restrictTo U g₁) :=
          (LQGMetric.GM.distRes_restrictTo (hUi i) g₁).symm
        _ = LQGMetric.GM.distRes (Ui i) U (restrictTo U g₂) := by rw [hRes]
        _ = _ := LQGMetric.GM.distRes_restrictTo (hUi i) g₂
    have hInt : ∀ i, (D i g₁).internal (Ui i : Set ℂ) =
        (D i g₂).internal (Ui i : Set ℂ) := by
      intro i
      calc
        _ = F i (restrictTo (Ui i) g₁) := hWsub g₁ hg₁ i
        _ = F i (restrictTo (Ui i) g₂) := by rw [hResi i]
        _ = _ := (hWsub g₂ hg₂ i).symm
    change Φ (fun i => (D i g₁).internal (Ui i : Set ℂ)) (restrictTo U g₁) at hB₁
    change Φ (fun i => (D i g₂).internal (Ui i : Set ℂ)) (restrictTo U g₂)
    simp only [← hInt, ← hRes]
    exact hB₁
  simpa only [B, Set.preimage_id] using
    (LQGMetric.LocalEvent.aeEventIn_of_saturated
      (Y := id) (R := R) (V := R) (B := B) (W := W)
      measurable_id hR hV (Filter.Eventually.of_forall fun _ => rfl)
      hWm (by simpa only [B, Measure.map_id] using hB) hWae hSat)


 


theorem aeEventIn_borel_internal_windows
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : LQGMetric.IsGFFPlusCont h P)
    {ι : Type} [Fintype ι] (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D : ι → DistC → LSCMetric)
    (hD : ∀ i, IsWeakLQGMetric ξ Q (D i))
    (U : TopologicalSpace.Opens ℂ) (Ui : ι → TopologicalSpace.Opens ℂ)
    (hUi : ∀ i, Ui i ≤ U)
    (Φ : (∀ i, (↥(Ui i : Set ℂ) × ↥(Ui i : Set ℂ) → ℝ≥0∞)) →
      DistOn U → Prop)
    (hΦ : MeasurableSet
      {p : (∀ i, (↥(Ui i : Set ℂ) × ↥(Ui i : Set ℂ) → ℝ≥0∞)) × DistOn U |
        Φ p.1 p.2}) :
    AEEventIn P (fieldSigma h U)
      {ω | Φ (fun i => (D i (h ω)).internal (Ui i : Set ℂ))
        (restrictTo U (h ω))} := by
  classical
  have hLoc : ∀ i : ι, ∃ F : DistOn (Ui i) →
      (↥(Ui i : Set ℂ) × ↥(Ui i : Set ℂ) → ℝ≥0∞),
      Measurable F ∧
      ∀ᵐ ω ∂P, (D i (h ω)).internal (Ui i : Set ℂ) = F (restrictTo (Ui i) (h ω)) := by
    intro i
    exact (hD i).locality P h hh (Ui i)
  choose F hFm hFae using hLoc
  let R : Ω → DistOn U := fun ω => restrictTo U (h ω)
  have hR : Measurable[fieldSigma h U] R := Measurable.of_comap_le le_rfl
  have hRi : ∀ i, Measurable[fieldSigma h U]
      (fun ω => restrictTo (Ui i) (h ω)) := by
    intro i
    have he : (fun ω => restrictTo (Ui i) (h ω)) =
        LQGMetric.GM.distRes (Ui i) U ∘ R := by
      funext ω
      exact (LQGMetric.GM.distRes_restrictTo (hUi i) (h ω)).symm
    rw [he]
    exact (LQGMetric.GM.measurable_distRes (Ui i) U).comp hR
  let V : Ω → (∀ i, (↥(Ui i : Set ℂ) × ↥(Ui i : Set ℂ) → ℝ≥0∞)) :=
    fun ω i => F i (restrictTo (Ui i) (h ω))
  have hV : Measurable[fieldSigma h U] V := by
    exact @Measurable.of_eval Ω ι
      (fun i => (↥(Ui i : Set ℂ) × ↥(Ui i : Set ℂ) → ℝ≥0∞))
      (fieldSigma h U) _ V (fun i => (hFm i).comp (hRi i))
  let B : Set Ω := {ω | Φ (V ω) (R ω)}
  have hBm : MeasurableSet[fieldSigma h U] B :=
    hΦ.preimage (hV.prodMk hR)
  have hEq : ∀ᵐ ω ∂P,
      (fun i => (D i (h ω)).internal (Ui i : Set ℂ)) = V ω := by
    have hall : ∀ᵐ ω ∂P, ∀ i,
        (D i (h ω)).internal (Ui i : Set ℂ) = F i (restrictTo (Ui i) (h ω)) :=
      ae_all_iff.mpr hFae
    filter_upwards [hall] with ω hω
    exact funext hω
  refine ⟨B, hBm, ?_⟩
  filter_upwards [hEq] with ω hω
  change (Φ (fun i => (D i (h ω)).internal (Ui i : Set ℂ)) (R ω)) =
    (Φ (V ω) (R ω))
  rw [hω]


 

theorem aeEventIn_borel_internal_windows_modConst
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : LQGMetric.IsGFFPlusCont h P)
    {ι : Type} [Fintype ι] (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D : ι → DistC → LSCMetric)
    (hD : ∀ i, IsWeakLQGMetric ξ Q (D i))
    (U : TopologicalSpace.Opens ℂ) (Ui : ι → TopologicalSpace.Opens ℂ)
    (hUi : ∀ i, Ui i ≤ U)
    (ψ : LQGMetric.TestC) (hψ : ∫ x, ψ x = 1)
    (hψU : tsupport (ψ : ℂ → ℝ) ⊆ (U : Set ℂ))
    (Φ : (∀ i, (↥(Ui i : Set ℂ) × ↥(Ui i : Set ℂ) → ℝ≥0∞)) →
      DistOn U → Prop)
    (hΦ : MeasurableSet
      {p : (∀ i, (↥(Ui i : Set ℂ) × ↥(Ui i : Set ℂ) → ℝ≥0∞)) × DistOn U |
        Φ p.1 p.2})
    (hInv : ∀ (g : DistC) (c : ℝ),
      (Φ (fun i => (D i (LQGMetric.addConst g c)).internal (Ui i : Set ℂ))
        (restrictTo U (LQGMetric.addConst g c)) ↔
       Φ (fun i => (D i g).internal (Ui i : Set ℂ)) (restrictTo U g))) :
    AEEventIn P (fieldSigma0On h U)
      {ω | Φ (fun i => (D i (h ω)).internal (Ui i : Set ℂ))
        (restrictTo U (h ω))} := by
  let g := LQGMetric.CONF.normIn h ψ
  have hg : LQGMetric.IsGFFPlusCont g P := isGFFPlusCont_normIn hh ψ
  have hE : AEEventIn P (fieldSigma g U)
      {ω | Φ (fun i => (D i (g ω)).internal (Ui i : Set ℂ))
        (restrictTo U (g ω))} :=
    aeEventIn_borel_internal_windows P g hg ξ Q D hD U Ui hUi Φ hΦ
  have hE0 := aeEventIn_fieldSigma0On_of_normIn h ψ hψ U hψU hE
  have heq : {ω | Φ (fun i => (D i (h ω)).internal (Ui i : Set ℂ))
        (restrictTo U (h ω))} =
      {ω | Φ (fun i => (D i (g ω)).internal (Ui i : Set ℂ))
        (restrictTo U (g ω))} := by
    ext ω
    exact (hInv (h ω) (-(h ω ψ))).symm
  rw [heq]
  exact hE0


 

theorem aeEventIn_borel_internal_windows_modConst_ae
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : LQGMetric.IsGFFPlusCont h P)
    {ι : Type} [Fintype ι] (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D : ι → DistC → LSCMetric)
    (hD : ∀ i, IsWeakLQGMetric ξ Q (D i))
    (U : TopologicalSpace.Opens ℂ) (Ui : ι → TopologicalSpace.Opens ℂ)
    (hUi : ∀ i, Ui i ≤ U)
    (ψ : LQGMetric.TestC) (hψ : ∫ x, ψ x = 1)
    (hψU : tsupport (ψ : ℂ → ℝ) ⊆ (U : Set ℂ))
    (Φ : (∀ i, (↥(Ui i : Set ℂ) × ↥(Ui i : Set ℂ) → ℝ≥0∞)) →
      DistOn U → Prop)
    (hΦ : MeasurableSet
      {p : (∀ i, (↥(Ui i : Set ℂ) × ↥(Ui i : Set ℂ) → ℝ≥0∞)) × DistOn U |
        Φ p.1 p.2})
    (hInv : ∀ᵐ ω ∂P,
      (Φ (fun i => (D i (h ω)).internal (Ui i : Set ℂ))
          (restrictTo U (h ω)) ↔
       Φ (fun i => (D i (LQGMetric.CONF.normIn h ψ ω)).internal
          (Ui i : Set ℂ))
          (restrictTo U (LQGMetric.CONF.normIn h ψ ω)))) :
    AEEventIn P (fieldSigma0On h U)
      {ω | Φ (fun i => (D i (h ω)).internal (Ui i : Set ℂ))
        (restrictTo U (h ω))} := by
  let g := LQGMetric.CONF.normIn h ψ
  have hg : LQGMetric.IsGFFPlusCont g P := isGFFPlusCont_normIn hh ψ
  have hE : AEEventIn P (fieldSigma g U)
      {ω | Φ (fun i => (D i (g ω)).internal (Ui i : Set ℂ))
        (restrictTo U (g ω))} :=
    aeEventIn_borel_internal_windows P g hg ξ Q D hD U Ui hUi Φ hΦ
  obtain ⟨F, hFm, hEF⟩ :=
    aeEventIn_fieldSigma0On_of_normIn h ψ hψ U hψU hE
  refine ⟨F, hFm, ?_⟩
  filter_upwards [hInv, hEF] with ω hi he
  exact propext (hi.trans (Iff.of_eq he))


 

theorem exists_borel_internal_windows_modConst_versions
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : LQGMetric.IsGFFPlusCont h P)
    {ι : Type} [Fintype ι] {κ : Type} [Countable κ]
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D : ι → DistC → LSCMetric)
    (hD : ∀ i, IsWeakLQGMetric ξ Q (D i))
    (U : TopologicalSpace.Opens ℂ) (Ui : ι → TopologicalSpace.Opens ℂ)
    (hUi : ∀ i, Ui i ≤ U)
    (ψ : LQGMetric.TestC) (hψ : ∫ x, ψ x = 1)
    (hψU : tsupport (ψ : ℂ → ℝ) ⊆ (U : Set ℂ))
    (Φ : κ → (∀ i, (↥(Ui i : Set ℂ) × ↥(Ui i : Set ℂ) → ℝ≥0∞)) →
      DistOn U → Prop)
    (hΦ : ∀ j, MeasurableSet
      {p : (∀ i, (↥(Ui i : Set ℂ) × ↥(Ui i : Set ℂ) → ℝ≥0∞)) × DistOn U |
        Φ j p.1 p.2})
    (hInv : ∀ (j : κ) (g : DistC) (c : ℝ),
      (Φ j (fun i => (D i (LQGMetric.addConst g c)).internal (Ui i : Set ℂ))
        (restrictTo U (LQGMetric.addConst g c)) ↔
       Φ j (fun i => (D i g).internal (Ui i : Set ℂ)) (restrictTo U g))) :
    ∃ F : κ → Set Ω, (∀ j, MeasurableSet[fieldSigma0On h U] (F j)) ∧
      (∀ᵐ ω ∂P, ∀ j,
        (Φ j (fun i => (D i (h ω)).internal (Ui i : Set ℂ))
          (restrictTo U (h ω)) ↔ ω ∈ F j)) := by
  let E : κ → Set Ω := fun j =>
    {ω | Φ j (fun i => (D i (h ω)).internal (Ui i : Set ℂ))
      (restrictTo U (h ω))}
  have hE : ∀ j, AEEventIn P (fieldSigma0On h U) (E j) := by
    intro j
    exact aeEventIn_borel_internal_windows_modConst P h hh ξ Q D hD U Ui hUi
      ψ hψ hψU (Φ j) (hΦ j) (hInv j)
  simpa only [E, Set.mem_ofPred_eq] using
    (exists_local_event_versions (P := P) (fieldSigma0On h U) E hE)


 

theorem exists_borel_internal_windows_modConst_ae_versions
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : LQGMetric.IsGFFPlusCont h P)
    {ι : Type} [Fintype ι] {κ : Type} [Countable κ]
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D : ι → DistC → LSCMetric)
    (hD : ∀ i, IsWeakLQGMetric ξ Q (D i))
    (U : TopologicalSpace.Opens ℂ) (Ui : ι → TopologicalSpace.Opens ℂ)
    (hUi : ∀ i, Ui i ≤ U)
    (ψ : LQGMetric.TestC) (hψ : ∫ x, ψ x = 1)
    (hψU : tsupport (ψ : ℂ → ℝ) ⊆ (U : Set ℂ))
    (Φ : κ → (∀ i, (↥(Ui i : Set ℂ) × ↥(Ui i : Set ℂ) → ℝ≥0∞)) →
      DistOn U → Prop)
    (hΦ : ∀ j, MeasurableSet
      {p : (∀ i, (↥(Ui i : Set ℂ) × ↥(Ui i : Set ℂ) → ℝ≥0∞)) × DistOn U |
        Φ j p.1 p.2})
    (hInv : ∀ j : κ, ∀ᵐ ω ∂P,
      (Φ j (fun i => (D i (h ω)).internal (Ui i : Set ℂ))
          (restrictTo U (h ω)) ↔
       Φ j (fun i => (D i (LQGMetric.CONF.normIn h ψ ω)).internal
          (Ui i : Set ℂ))
          (restrictTo U (LQGMetric.CONF.normIn h ψ ω)))) :
    ∃ F : κ → Set Ω, (∀ j, MeasurableSet[fieldSigma0On h U] (F j)) ∧
      (∀ᵐ ω ∂P, ∀ j,
        (Φ j (fun i => (D i (h ω)).internal (Ui i : Set ℂ))
          (restrictTo U (h ω)) ↔ ω ∈ F j)) := by
  let E : κ → Set Ω := fun j =>
    {ω | Φ j (fun i => (D i (h ω)).internal (Ui i : Set ℂ))
      (restrictTo U (h ω))}
  have hE : ∀ j, AEEventIn P (fieldSigma0On h U) (E j) := by
    intro j
    exact aeEventIn_borel_internal_windows_modConst_ae P h hh ξ Q D hD
      U Ui hUi ψ hψ hψU (Φ j) (hΦ j) (hInv j)
  simpa only [E, Set.mem_ofPred_eq] using
    (exists_local_event_versions (P := P) (fieldSigma0On h U) E hE)


 

theorem aeEventIn_limsup_neighborhoods0
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (h : Ω → DistC) (ψ : LQGMetric.TestC)
    (hψ : ∫ x, ψ x = 1) (K : Set ℂ)
    (hψK : tsupport (ψ : ℂ → ℝ) ⊆ K)
    (E : ℕ → Set Ω)
    (hE : ∀ n : ℕ,
      AEEventIn P
        (fieldSigma (LQGMetric.CONF.normIn h ψ)
          (nbhdO (1 / ((n : ℝ) + 1)) K)) (E n)) :
    AEEventIn P (fieldSigmaClosed0 h K)
      (⋂ N, ⋃ n, ⋃ (_ : N ≤ n), E n) := by
  classical
  choose F hFm hEF using hE
  let g := LQGMetric.CONF.normIn h ψ
  have hmono : ∀ {m n : ℕ}, m ≤ n →
      fieldSigma g (nbhdO (1 / ((n : ℝ) + 1)) K) ≤
      fieldSigma g (nbhdO (1 / ((m : ℝ) + 1)) K) := by
    intro m n hmn
    refine LQGMetric.GM.fieldSigma_mono g (fun x hx => Metric.thickening_mono ?_ K hx)
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hmn 1)
  let B : Set Ω := ⋂ N, ⋃ n, ⋃ (_ : N ≤ n), F n
  have hBm : MeasurableSet[fieldSigmaClosed g K] B := by
    rw [fieldSigmaClosed, MeasurableSpace.measurableSet_iInf]
    intro ε
    rw [MeasurableSpace.measurableSet_iInf]
    intro hε
    obtain ⟨M, hM⟩ := exists_nat_one_div_lt hε
    have hle : fieldSigma g (nbhdO (1 / ((M : ℝ) + 1)) K) ≤
        fieldSigma g (nbhdO ε K) :=
      LQGMetric.GM.fieldSigma_mono g
        (fun x hx => Metric.thickening_mono hM.le K hx)
    have heq : B = ⋂ N, ⋃ n, ⋃ (_ : max N M ≤ n), F n := by
      ext ω
      simp only [B, Set.mem_iInter, Set.mem_iUnion]
      constructor
      · intro hω N
        exact hω (max N M)
      · intro hω N
        obtain ⟨n, hn, hFn⟩ := hω N
        exact ⟨n, (le_max_left N M).trans hn, hFn⟩
    rw [heq]
    exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n =>
      MeasurableSet.iUnion fun hn =>
        hle _ (hmono ((le_max_right N M).trans hn) _ (hFm n))
  have hBE : (⋂ N, ⋃ n, ⋃ (_ : N ≤ n), E n) =ᵐ[P] B := by
    have hall : ∀ᵐ ω ∂P, ∀ n, (ω ∈ E n ↔ ω ∈ F n) := by
      rw [ae_all_iff]
      intro n
      filter_upwards [hEF n] with ω hω
      exact Iff.of_eq hω
    filter_upwards [hall] with ω hAll
    apply propext
    simp only [B, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro hω N
      obtain ⟨n, hn, hEn⟩ := hω N
      exact ⟨n, hn, (hAll n).mp hEn⟩
    · intro hω N
      obtain ⟨n, hn, hFn⟩ := hω N
      exact ⟨n, hn, (hAll n).mpr hFn⟩
  refine ⟨B, ?_, hBE⟩
  rw [← LQGMetric.CONF.fieldSigmaClosed_normIn_eq h hψ hψK]
  exact hBm


 

private theorem testTranslate_eq_testAffinePull_one (z : ℂ)
    (φ : LQGMetric.TestC) :
    testTranslate z φ = LQGMetric.testAffinePull 1 z φ := by
  ext x
  rw [LQGMetric.testAffinePull_apply 1 z one_ne_zero]
  simp only [Complex.ofReal_one, div_one]
  rfl

private theorem translateDist_eq_affineComp_one (z : ℂ) (g : DistC) :
    translateDist z g = LQGMetric.affineComp 1 z g := by
  ext φ
  rw [LQGMetric.GFFInv.affineComp_apply, one_pow, inv_one, one_mul]
  exact congrArg g (testTranslate_eq_testAffinePull_one z φ)

private theorem ae_centered_translate_eq_affine {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) (z : ℂ) (r : Set.Ioi (0 : ℝ)) :
    ∀ᵐ ω ∂P,
      LQGMetric.affineComp 1 z
        (LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) r z)) =
        LQGMetric.addConst
          (LQGMetric.addConst (translateDist z (h ω))
            (-LQGMetric.circleAvg (h ω) 1 z))
          (-LQGMetric.circleAvg
            (LQGMetric.addConst (translateDist z (h ω))
              (-LQGMetric.circleAvg (h ω) 1 z)) r 0) := by
  have htrans := hh.1.affineComp one_pos z
  filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst htrans 0 r.2]
    with ω hca
  rw [translateDist_eq_affineComp_one, hca,
    LQGMetric.GM.affineComp_addConst one_pos,
    LQGMetric.GM.addConst_addConst,
    LQGMetric.GM.Tight.circleAvg_affineComp_one]
  congr 1
  ring


theorem aeEventIn_centered_translate_from_toolkit
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P)
    (z : ℂ) (r : Set.Ioi (0 : ℝ))
    (U V : TopologicalSpace.Opens ℂ)
    (hUV : ∀ y : ℂ, y ∈ V ↔ (1 : ℝ) • y + z ∈ U)
    {E : Set Ω}
    (hE : AEEventIn P
      (fieldSigma (fun ω => LQGMetric.addConst (h ω)
        (-LQGMetric.circleAvg (h ω) r z)) U) E) :
    AEEventIn P
      (fieldSigma
        (fun ω => LQGMetric.addConst
          (LQGMetric.addConst (translateDist z (h ω))
            (-LQGMetric.circleAvg (h ω) 1 z))
          (-LQGMetric.circleAvg
            (LQGMetric.addConst (translateDist z (h ω))
              (-LQGMetric.circleAvg (h ω) 1 z)) r 0)) V) E := by
  have hT := aeEventIn_translate
    (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) r z))
    z U V hUV hE
  exact LQGMetric.GM.aeEventIn_of_ae_eq
    (ae_centered_translate_eq_affine hh z r) V hT


end SupercriticalLQGUniqueness.Uniqueness.Toolkit.LocalEvents
