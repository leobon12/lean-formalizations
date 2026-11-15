import InteractingSLE.Spec.Sec2.T24BrProtect
import InteractingSLE.Spec.Sec2.T24BrLive

/-!
# Forward local martingales for regular coordinate versions

All stochastic steps of the forward implication are assembled here for everywhere
continuous adapted coordinate versions. The source's a.s. coordinate hypotheses are
handled separately by measurable modification.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec2.T24Bridge

open Coupling Coupling.MartMeans Sec7.PhaseSelFull MartChar

theorem isContLocalMartingaleBeforeV2_of_evolution_regular
    {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {P : Measure Ω} [IsProbabilityMeasure P] {Q : Measure Ω'} {π : Ω' → Ω}
    {𝓕' : Filtration ℝ≥0 mΩ'} {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω' → ℝ} {ζ : Ω → ℝ≥0∞}
    {η : ℝ≥0 → Ω → ℂ} (hη : ∀ t, StronglyMeasurable (η t))
    (hπ : MeasurePreserving π Q P)
    (hgen : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (η · ω))
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR Q 𝓕' (fun t ω => W t (π ω))
      (fun i t ω => VL i t (π ω)) (fun i t ω => VR i t (π ω)) B (ζ ∘ π))
    (hWc : ∀ ω, Continuous (W · ω)) (hVLc : ∀ i ω, Continuous (VL i · ω))
    (hVRc : ∀ i ω, Continuous (VR i · ω))
    (hWa : StronglyAdapted (usualAugmentation (Filtration.natural η hη) P) W)
    (hVLa : ∀ i, StronglyAdapted (usualAugmentation (Filtration.natural η hη) P) (VL i))
    (hVRa : ∀ i, StronglyAdapted (usualAugmentation (Filtration.natural η hη) P) (VR i))
    (hW0 : ∀ ω, W 0 ω = 0) (hVL0 : ∀ i ω, VL i 0 ω = xL i)
    (hVR0 : ∀ i ω, VR i 0 ω = xR i)
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hζ : IsStoppingTime (usualAugmentation (Filtration.natural η hη) P) ζ)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    (U : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω t, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω))
      (forceJumpSet (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω)) (U ω t))
    {z : ℂ} (hz : 0 < z.im) :
    IsContLocalMartingaleBeforeV2 (usualAugmentation (Filtration.natural η hη) P) P
      (fun ω => (min (QuantumZipper.swallowTime (Ito.rpath (W · ω)) z) (ζ ω) : ℝ≥0∞))
      (fun t ω => couplingMean κ (Ito.rpath (W · ω)) t (U ω t) z) := by
  let 𝓖 := usualAugmentation (Filtration.natural η hη) P
  have : IsProbabilityMeasure Q := hE.1.isProbabilityMeasure'
  have hWb := adaptedBefore_of_stronglyAdapted hζ hWa
  have hVLb := fun i => adaptedBefore_of_stronglyAdapted hζ (hVLa i)
  have hVRb := fun i => adaptedBefore_of_stronglyAdapted hζ (hVRa i)
  obtain ⟨T, hT, -⟩ := exists_isAnnouncingSeq_of_evolution_pullback hπ hζ.measurable'
    hWb hVLb hVRb (G := univ) MeasurableSet.univ (Eventually.of_forall fun _ => mem_univ _)
    (fun ω _ => (hWc ω).continuousOn) (fun ω _ i => (hVLc i ω).continuousOn)
    (fun ω _ i => (hVRc i ω).continuousOn) hE hκ hseed
  have hgood : ∀ᵐ ω ∂P, (∀ n, (T n ω : ℝ≥0∞) < ζ ω) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∃ n, t ≤ T n ω :=
    (ae_all_iff.2 hT.2.2.1).and hT.2.2.2
  obtain ⟨G, hGm, hG0, hGp⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧
      ∀ ω ∈ G, (∀ n, (T n ω : ℝ≥0∞) < ζ ω) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∃ n, t ≤ T n ω := by
    refine ⟨(toMeasurable P {ω | ¬ ((∀ n, (T n ω : ℝ≥0∞) < ζ ω) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∃ n, t ≤ T n ω)})ᶜ,
      (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
    · rw [compl_compl, measure_toMeasurable]
      exact ae_iff.1 hgood
    · intro ω hω
      by_contra hh
      exact hω (subset_toMeasurable _ _ hh)
  have hGa : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hG0
  have hG : MeasurableSet[𝓖 0] G := by
    simpa only [compl_compl] using
      (Ito.measurableSet_usualAugmentation_of_null (𝓕 := Filtration.natural η hη) hGm.compl hG0 0).compl
  have hGt (t : ℝ≥0) : MeasurableSet[𝓖 t] G := 𝓖.mono zero_le _ hG
  let V := jointV VL VR
  have hVc : ∀ i ω, Continuous (V i · ω) := by
    intro i
    cases i with
    | inl i => exact hVLc i
    | inr i => exact hVRc i
  have hVa : ∀ i, StronglyAdapted 𝓖 (V i) := by
    intro i
    cases i with
    | inl i => exact hVLa i
    | inr i => exact hVRa i
  obtain ⟨K, hK⟩ := exists_nat_gt ((∑ i, |xL i|) + ∑ i, |xR i|)
  have hinit (ω : Ω) : absSum W V 0 ω < K := by
    simpa only [absSum, V, jointV, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      hW0, hVL0, hVR0, abs_zero, zero_add] using hK
  let σ := protectedCurveTime z W V T ζ G K
  have hσ (n : ℕ) : IsStoppingTime 𝓖 fun ω => (σ n ω : WithTop ℝ≥0) :=
    isStoppingTime_protectedCurveTime hWb (fun ω _ => (hWc ω).continuousOn) hGt
      hWc hVc hWa hVa hT.1 hz n
  have hsafe (n : ℕ) (ω : Ω) (hω : ω ∈ G) :=
    isSafeAt_protectedCurveTime (V := V) (K := K) hω (hWc ω).continuousOn (hW0 ω) hz ((hGp ω hω).1 n)
  have hzs (n : ℕ) : ({z} : Set ℂ) ⊆ Metric.closedBall z (locRad z n) :=
    singleton_subset_iff.2 (Metric.mem_closedBall_self (locRad_pos hz n).le)
  have hsafes (n : ℕ) (ω : Ω) (hω : ω ∈ G) :
      IsSafeAt {z} (locLevel z n) n (σ n ω) (ζ ω) (W · ω) (σ n ω) :=
    ⟨(hsafe n ω hω).1, le_rfl, (hsafe n ω hω).2.2.1,
      fun y hy => (hsafe n ω hω).2.2.2 y (hzs n hy)⟩
  refine ⟨?_, (fun n ω => (σ n ω : WithTop ℝ≥0)), hσ, ?_, ?_, fun n => ?_⟩
  · filter_upwards [] with ω
    apply (continuousOn_couplingMean_before_swallow (hWc ω) (fun i => hVLc i ω) (fun i => hVRc i ω)
      (hordL ω) (hordR ω) (U ω) (hu ω) hz).mono
    intro t ht
    change (t : ℝ≥0∞) < QuantumZipper.swallowTime (Ito.rpath (W · ω)) z
    simp only [mem_ofPred_eq] at ht
    exact (lt_min_iff.1 (ennreal_lt_of_withTop_lt ht)).1
  · intro n ω
    by_cases hω : ω ∈ G
    · apply Or.inr
      apply lt_min _ (hsafe n ω hω).1
      have hn := notMem_fwdHull_of_alive (hWc ω).continuousOn (hsafe n ω hω).1 hz
        ((hsafes n ω hω).2.2.2 z (mem_singleton z)).1
      by_contra hh
      apply hn
      refine ⟨hz, ?_⟩
      rw [ENNReal.ofReal_coe_nnreal]
      exact not_lt.1 hh
    · exact Or.inl (by simp [σ, protectedCurveTime, hω])
  · filter_upwards [hGa] with ω hω r hr
    have hh := eventually_lt_protectedCurveTime (K := K) hWc hVc hω (hT.2.1 ω)
      (hGp ω hω).2 hz (lt_of_lt_of_le hr (min_le_left _ _)) (lt_of_lt_of_le hr (min_le_right _ _))
    exact hh.mono fun _ h => WithTop.coe_lt_coe.2 h
  · have hGQ := hπ.quasiMeasurePreserving.ae hGa
    let R : ℝ := max ((n + K : ℕ) : ℝ)
      ((2 * ((n + K : ℕ) : ℝ) + (∑ i, |jointρ ρL ρR i|) * ((n + K : ℕ) : ℝ)) / Real.sqrt κ)
    have hprot : ∀ᵐ ω ∂Q, (σ n (π ω) : ℝ≥0∞) < ζ (π ω) ∧
        (∃ u, QuantumZipper.IsForwardSol (Ito.rpath (W · (π ω))) z (σ n (π ω)) u) ∧
        locLevel z n ≤ (QuantumZipper.fwdMap (Ito.rpath (W · (π ω))) (σ n (π ω)) z).im ∧
        (σ n (π ω) : ℝ) ≤ n ∧ ∀ s ≤ σ n (π ω), |W s (π ω)| ≤ R ∧ |B s ω| ≤ R ∧
          (∀ i, |VL i s (π ω)| ≤ R) ∧ ∀ i, |VR i s (π ω)| ≤ R := by
      filter_upwards [hGQ, hE.2.2.2.2] with ω hω hp
      have hs := hsafes n (π ω) hω
      refine ⟨hs.1, (hs.2.2.2 z (mem_singleton z)).1, (hs.2.2.2 z (mem_singleton z)).2,
        hs.2.2.1, fun s hss => ?_⟩
      have hb := abs_le_of_le_protectedCurveTime hWc hVc (hinit (π ω)) hss
      have hbB := abs_normalized_martProc_le_of_le_protectedCurveTime
        (ρ := jointρ ρL ρR) hκ hWc hVc hss
      have heB := brownian_eq_martValue_before hκ hp
        (lt_of_le_of_lt (by exact_mod_cast hss) hs.1)
      have heB' : B s ω = martProc (jointρ ρL ρR) W V s (π ω) / Real.sqrt κ := by
        simpa only [martProc, martValue, V, jointV, jointρ, Fintype.sum_sum_type,
          Sum.elim_inl, Sum.elim_inr] using heB
      rw [← heB'] at hbB
      exact ⟨hb.1.trans (le_max_left _ _), hbB.trans (le_max_right _ _),
        fun i => (hb.2 (Sum.inl i)).trans (le_max_left _ _),
        fun i => (hb.2 (Sum.inr i)).trans (le_max_left _ _)⟩
    have hXa := stronglyAdapted_stopped_couplingMean hWb hVLb hVRb
      (fun ω _ => (hWc ω).continuousOn) (fun ω _ i => (hVLc i ω).continuousOn)
      (fun ω _ i => (hVRc i ω).continuousOn) hG (hσ n) hz (locLevel_pos hz n) (hsafes n)
      (fun ω _ s _ => hordL ω s) (fun ω _ s _ => hordR ω s) U hu
    have hle : ∀ᵐ ω ∂Q, (σ n (π ω) : WithTop ℝ≥0) ≤ ζ (π ω) := hprot.mono fun _ h => h.1.le
    have hσ' := isStoppingTime_curve_pullback_before hη hπ hE.2.1 hgen (hσ n) hle
    obtain ⟨M, hM, he⟩ := Ito.exists_martingale_couplingMean_usualAugmentation hE hκ hz hσ'
      (locLevel_pos hz n) hprot (fun ω t => U (π ω) t) (fun ω t => hu (π ω) t)
    have hXd : Martingale (fun t ω => if ω ∈ G then couplingMean κ (Ito.rpath (W · ω))
        (min t (σ n ω) : ℝ≥0) (U ω (min t (σ n ω))) z else 0) 𝓖 P := by
      apply martingale_curveFiltration_of_stopped_pullback hη hπ hE.2.1 hgen (hσ n) hle hXa
        (Eventually.of_forall fun ω s t hs ht => ?_) hM
        (fun t => ?_)
      · by_cases hω : ω ∈ G
        · simp only [hω, ↓reduceIte, min_eq_right (WithTop.coe_le_coe.1 hs),
            min_eq_right (WithTop.coe_le_coe.1 ht)]
        · simp only [hω, ↓reduceIte]
      · filter_upwards [he, hGQ] with ω hω hωG
        simpa only [hωG, ↓reduceIte] using (hω t).symm
    have hA : MeasurableSet[𝓖 0] {ω | 0 < (σ n ω : WithTop ℝ≥0)} := by
      simpa only [Set.compl_ofPred, not_le, WithTop.coe_zero] using (hσ n 0).compl
    convert martingale_indicator_initial hXd hA using 1
    funext t ω
    rw [stoppedProcess_coe_apply]
    by_cases hω : ω ∈ G
    · simp [Set.indicator, hω]
    · have hs0 : σ n ω = 0 := by simp [σ, protectedCurveTime, hω]
      simp only [Set.indicator, mem_ofPred_eq, hω, ↓reduceIte]
      split_ifs with hp
      · have hp' : (0 : ℝ≥0) < σ n ω := by exact_mod_cast hp
        rw [hs0] at hp'
        exact absurd hp' (lt_irrefl _)
      · rfl

end InteractingSLE.Sec2.T24Bridge
