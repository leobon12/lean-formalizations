/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafMartMNoise
import InteractingSLE.Spec.Coupling.WFSLeafMartMDouglas
import InteractingSLE.Spec.Sec2.AssemblyTheorem

/-!
# Uniqueness of the history law under closed-space mean preservation

A dominated measure preserving continuous closed means preserves the stopped
noise exponentials. Complete that noise by an independent Brownian motion,
lift the original path equations, and apply the landed SLE uniqueness in law.
This includes two-sided entrance words and terminal lifetimes.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open WholeField LawUnique Coupling Sec6.Prop65

/-- The full killed-history law is unchanged by every dominated probability
measure preserving the means of terminal variables with continuous closed means.
This SLE-specific extremality argument has no additional mathematical input. -/
theorem map_killedHistory_eq_of_continuousClosedSpace_means
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P Q : Measure Ω}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hQP : Q ≤ (2 : ℝ≥0∞) • P)
    (hmeans : ∀ Z ∈ continuousClosedSpace (drivingFiltration P hX) P,
      (∫ ω, Z ω ∂Q) = ∫ ω, Z ω ∂P) :
    Q.map (killedHistory W VL VR ζ) = P.map (killedHistory W VL VR ζ) := by
  have hac : Q ≪ P := Measure.absolutelyContinuous_of_le_smul hQP
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · have he : killedHistory W VL VR ζ =ᵐ[P] fun _ => (0 : HistorySpace nL nR) :=
      (hE.ae_lifetime_eq_zero_of_threshold hseed).mono fun ω hω => by
        simp only [killedHistory, hω, not_lt_zero, ↓reduceIte]
        rfl
    rw [Measure.map_congr (hac.ae_le he), Measure.map_congr he]
    simp only [Measure.map_const, measure_univ, one_smul]
  let 𝓓 := drivingFiltration P hX
  obtain ⟨σ, hσ⟩ := exists_isAnnouncingSeq_driving hE hκ hX hseed
  obtain ⟨Bv, hBvm, hBvc, hBv0, hBve, hmart⟩ := exists_stoppedNoise_exponentials hκ hE hX hσ
  have hQE (m : ℕ) (a : ℝ) : Martingale (fun t ω => Real.exp
      (a * Bv (min t (σ m ω)) ω - a ^ 2 * ((min t (σ m ω) : ℝ≥0) : ℝ) / 2)) 𝓓 Q := by
    apply martingale_of_continuousClosedSpace_means hQP hmeans (hmart m a)
    exact ae_of_all _ fun ω => Real.continuous_exp.comp
      (((hBvc ω).comp (continuous_id.min continuous_const)).const_mul a |>.sub
        (((NNReal.continuous_coe.comp (continuous_id.min continuous_const)).const_mul _).div_const _))
  have hSm (m : ℕ) (t : ℝ≥0) : Measurable[𝓓 t] (fun ω => min t (σ m ω)) := by
    have hm := (WithTop.measurable_untopD (0 : ℝ≥0)).comp ((hσ.1 m).min_const t).measurable
    have hl := ((hσ.1 m).min_const t).measurableSpace_le_of_le_const fun _ => min_le_right _ _
    simpa only [Function.comp_def, ← WithTop.coe_min, WithTop.untopD_coe, min_comm]
      using hm.mono hl le_rfl
  have hiSup : iSupFiltration (fun _ : ℕ => 𝓓) = 𝓓 := by
    apply Filtration.ext
    funext t
    exact iSup_const
  have hTC : IsTCExpMartingale Q 𝓓 (fun t ω => Bv (annClock σ t ω) ω) (annClock σ) := by
    have hh := isTCExpMartingale_annClock (𝒢 := fun _ : ℕ => 𝓓)
      (fun _ => monotone_const) hσ.2.1 hSm hBvc hBv0 hQE
    rwa [hiSup] at hh
  have hNB : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
      annClock σ t ω = t ∧ Bv (annClock σ t ω) ω = B t ω := by
    filter_upwards [hac.ae_le hσ.2.2.2, hac.ae_le hBve] with ω hex he t ht
    obtain ⟨m, hm⟩ := hex t ht
    have hh := annClock_eq_of_le hm
    exact ⟨hh, by rw [hh, he t]⟩
  obtain ⟨B₀, hB₀m, hB₀c, hB₀0, hB₀, _⟩ := QuantumZipper.RS.exists_good_version0 hE.1.1
  have hFB := hB₀.toIsPreBrownianReal.isFilteredPreBrownian hB₀m
  let 𝓦 := Filtration.natural B₀ fun t => (hB₀m t).stronglyMeasurable
  obtain ⟨hβ, _⟩ := WholeField.IsTCExpMartingale.isFilteredBrownianReal_complNoise
    hTC hFB hB₀c hB₀0
  let N : ℝ≥0 → Ω → ℝ := fun t ω => Bv (annClock σ t ω) ω
  let 𝓖 := prodFiltration 𝓓 𝓦
  have hle (t : ℝ≥0) : (𝓓 t).comap Prod.fst ≤ 𝓖 t := comap_fst_le_prodFiltration 𝓓 𝓦 t
  have hWa := Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ P)
    (adaptedBefore_killedDriving_W hX)
  have hVLa := fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ P)
    (adaptedBefore_killedDriving_VL hX i)
  have hVRa := fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ P)
    (adaptedBefore_killedDriving_VR hX i)
  have hÊ : IsIntegratedSLEEvolution κ xL xR ρL ρR (Q.prod P) 𝓖
      (fun t p => W t p.1) (fun i t p => VL i t p.1) (fun j t p => VR j t p.1)
      (complNoise N (annClock σ) B₀) (fun p => ζ p.1) := by
    refine ⟨hβ, fun t A hA => hle t _ ⟨_, hWa t A hA, rfl⟩,
      fun i t A hA => hle t _ ⟨_, hVLa i t A hA, rfl⟩,
      fun j t A hA => hle t _ ⟨_, hVRa j t A hA, rfl⟩, ?_⟩
    have hp : ∀ᵐ ω ∂Q, IsIntegratedSLEPath κ xL xR ρL ρR (W · ω)
        (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) (ζ ω) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
          annClock σ t ω = t ∧ Bv (annClock σ t ω) ω = B t ω := by
      filter_upwards [hac.ae_le hE.2.2.2.2, hNB] with ω h1 h2 using ⟨h1, h2⟩
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hp] with p hh
    exact Sec2.Assembly.isIntegratedSLEPath_congr hh.1 rfl (fun _ => rfl) (fun _ => rfl)
      (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) fun t ht => by
        rw [complNoise_of_eq (hh.2 t ht).1]
        exact (hh.2 t ht).2
  have he := map_killedHistory_eq
    (Sec4.killedStateLawUnique_of_isOrderedForceWord hκ ρL ρR hF)
    hÊ (Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hÊ) hE hX
  change (Q.prod P).map ((killedHistory W VL VR ζ) ∘ Prod.fst) =
    P.map (killedHistory W VL VR ζ) at he
  rw [← Measure.map_map (measurable_killedHistory hX) measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul] at he
  exact he

end InteractingSLE.WFS
