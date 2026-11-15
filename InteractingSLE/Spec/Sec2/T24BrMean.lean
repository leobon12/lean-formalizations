import InteractingSLE.Spec.Sec2.T24BrForward
import InteractingSLE.Spec.Coupling.Assembly11Meas

/-!
# Adaptedness of protected coupling means

An arbitrary bounded harmonic extension agrees in the upper half-plane with the
explicit harmonic formula. Its stopped mean therefore has an adapted version even
when the chosen extension family has no measurability assumption.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec2.T24Bridge

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω} {z : ℂ}

open Ito Coupling

/-- The explicit mean restricted to the live, unswallowed event is adapted. -/
theorem measurable_meanCan_alive (hWa : AdaptedBefore 𝓖 ζ W)
    (hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i)) (hVRa : ∀ i, AdaptedBefore 𝓖 ζ (VR i))
    (hGc : ∀ ω ∈ G, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hG : MeasurableSet[𝓖 0] G) (hz : 0 < z.im) (s : ℝ≥0) :
    Measurable[𝓖 s] (fun ω => if ω ∈ aliveSet W ζ G z s then
      meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s z else 0) := by
  classical
  let a : Ω → Fin nL → ℝ := fun ω i => Girsanov.killed ζ (VL i) s ω - Girsanov.killed ζ W s ω
  let b : Ω → Fin nR → ℝ := fun ω i => Girsanov.killed ζ (VR i) s ω - Girsanov.killed ζ W s ω
  have ha : Measurable[𝓖 s] a := @Measurable.of_eval Ω (Fin nL) (fun _ => ℝ) (𝓖 s) _ _
    fun i => (Girsanov.measurable_killed (hVLa i) s).sub (Girsanov.measurable_killed hWa s)
  have hb : Measurable[𝓖 s] b := @Measurable.of_eval Ω (Fin nR) (fun _ => ℝ) (𝓖 s) _ _
    fun i => (Girsanov.measurable_killed (hVRa i) s).sub (Girsanov.measurable_killed hWa s)
  have hf := measurable_fwdMap_alive hWa hGc hG hz s
  have hL := measurable_logDerivFwd_alive hWa hGc hG hz s
  have hA := measurableSet_aliveSet hWa hGc hG hz s
  have hm := (measurable_meanHarmonic_prod κ ρL ρR).comp (ha.prodMk (hb.prodMk hf))
  have hh : Measurable[𝓖 s] (fun ω => if ω ∈ aliveSet W ζ G z s then
      meanHarmonic κ ρL ρR (a ω) (b ω)
        (if ω ∈ aliveSet W ζ G z s then QuantumZipper.fwdMap (rpath (W · ω)) s z else 0) -
      QuantumZipper.chiC κ *
        (if ω ∈ aliveSet W ζ G z s then QuantumZipper.logDerivFwd (rpath (W · ω)) s z else 0).im
      else 0) := Measurable.ite hA
    (hm.sub ((measurable_const (a := QuantumZipper.chiC κ)).mul (Complex.measurable_im.comp hL)))
    (measurable_const (a := (0 : ℝ)))
  convert hh using 1
  funext ω
  by_cases h : ω ∈ aliveSet W ζ G z s
  · simp only [h, ↓reduceIte, a, b, Girsanov.killed_of_lt h.2.1, meanCan]
  · simp only [h, ↓reduceIte]

/-- Protected explicit means, set to zero off an initial good event, are strongly adapted. -/
theorem stronglyAdapted_stopped_meanCan (hWa : AdaptedBefore 𝓖 ζ W)
    (hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i)) (hVRa : ∀ i, AdaptedBefore 𝓖 ζ (VR i))
    (hGc : ∀ ω ∈ G, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVLc : ∀ ω ∈ G, ∀ i, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVRc : ∀ ω ∈ G, ∀ i, ContinuousOn (VR i · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hG : MeasurableSet[𝓖 0] G) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime 𝓖 fun ω => (σ ω : WithTop ℝ≥0)) (hz : 0 < z.im)
    {δ N : ℝ} (hδ : 0 < δ)
    (hsafe : ∀ ω ∈ G, IsSafeAt {z} δ N (σ ω) (ζ ω) (W · ω) (σ ω)) :
    StronglyAdapted 𝓖 (fun t ω => if ω ∈ G then
      meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (min t (σ ω)) z else 0) := by
  classical
  have hKH : ({z} : Set ℂ) ⊆ QuantumZipper.H := singleton_subset_iff.2 hz
  intro t
  apply Measurable.stronglyMeasurable
  apply measurable_stopped_of_agree
    (X := fun s ω => meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s z)
    hσ (measurable_meanCan_alive (κ := κ) (ρL := ρL) (ρR := ρR)
      hWa hVLa hVRa hGc hG hz) hG 0
  · intro ω hω s hs
    have hA : ω ∈ aliveSet W ζ G z s :=
      ⟨hω, lt_of_le_of_lt (by exact_mod_cast hs) (hsafe ω hω).1,
        (hsafe ω hω).alive hKH (hGc ω hω) hs (mem_singleton z)⟩
    simp only [hA, ↓reduceIte]
  · intro ω hω
    exact (hsafe ω hω).continuousOn_meanCan_time (hGc ω hω) (hVLc ω hω) (hVRc ω hω)
      hKH hδ (mem_singleton z)

/-- No measurability of the chosen harmonic extensions is needed for a protected stopped mean. -/
theorem stronglyAdapted_stopped_couplingMean (hWa : AdaptedBefore 𝓖 ζ W)
    (hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i)) (hVRa : ∀ i, AdaptedBefore 𝓖 ζ (VR i))
    (hGc : ∀ ω ∈ G, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVLc : ∀ ω ∈ G, ∀ i, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVRc : ∀ ω ∈ G, ∀ i, ContinuousOn (VR i · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hG : MeasurableSet[𝓖 0] G) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime 𝓖 fun ω => (σ ω : WithTop ℝ≥0)) (hz : 0 < z.im)
    {δ N : ℝ} (hδ : 0 < δ)
    (hsafe : ∀ ω ∈ G, IsSafeAt {z} δ N (σ ω) (ζ ω) (W · ω) (σ ω))
    (hordL : ∀ ω ∈ G, ∀ s ≤ σ ω, ∀ i, VL i s ω ≤ W s ω)
    (hordR : ∀ ω ∈ G, ∀ s ≤ σ ω, ∀ i, W s ω ≤ VR i s ω)
    (U : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (U ω s)) :
    StronglyAdapted 𝓖 (fun t ω => if ω ∈ G then couplingMean κ (fun s : ℝ => W s.toNNReal ω)
      (min t (σ ω) : ℝ≥0) (U ω (min t (σ ω))) z else 0) := by
  classical
  have hh := stronglyAdapted_stopped_meanCan (κ := κ) (ρL := ρL) (ρR := ρR)
    hWa hVLa hVRa hGc hVLc hVRc hG hσ hz hδ hsafe
  convert hh using 1
  funext t ω
  by_cases h : ω ∈ G
  · simp only [h, ↓reduceIte]
    exact couplingMean_eq_meanCan (hGc ω h) (singleton_subset_iff.2 hz) (hsafe ω h) hδ
      (min_le_right t (σ ω)) (mem_singleton z) (hordL ω h _ (min_le_right _ _))
      (hordR ω h _ (min_le_right _ _)) (hu ω _)
  · simp only [h, ↓reduceIte]

/-- Arbitrary bounded harmonic extensions give a continuous mean before swallowing. -/
theorem continuousOn_couplingMean_before_swallow
    {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    (hw : Continuous w) (hvLc : ∀ i, Continuous (vL i)) (hvRc : ∀ i, Continuous (vR i))
    (hordL : ∀ t i, vL i t ≤ w t) (hordR : ∀ t i, w t ≤ vR i t)
    (U : ℝ≥0 → ℂ → ℝ)
    (hu : ∀ t, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => vL i t - w t) (fun i => vR i t - w t))
      (forceJumpSet (fun i => vL i t - w t) (fun i => vR i t - w t)) (U t))
    (hz : 0 < z.im) :
    ContinuousOn (fun t : ℝ≥0 => couplingMean κ (fun s : ℝ => w s.toNNReal) t (U t) z)
      {t | (t : ℝ≥0∞) < QuantumZipper.swallowTime (fun s : ℝ => w s.toNNReal) z} := by
  intro s hs
  obtain ⟨T, hsT, hT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
  have hsT' : s < T := ENNReal.coe_lt_coe.1 hsT
  have hzT : z ∈ QuantumZipper.H \ QuantumZipper.fwdHull (rpath w) T := by
    refine ⟨hz, fun h => ?_⟩
    have hle := h.2
    rw [ENNReal.ofReal_coe_nnreal] at hle
    exact (not_lt_of_ge hle) hT
  have hwp : Continuous (rpath w) := hw.comp continuous_real_toNNReal
  have hδ : 0 < (QuantumZipper.fwdMap (rpath w) T z).im :=
    im_fwdMap_pos hwp T.coe_nonneg hzT ⟨T.coe_nonneg, le_rfl⟩
  have hsafe : IsSafeAt {z} (QuantumZipper.fwdMap (rpath w) T z).im T T ⊤ w T := by
    refine ⟨ENNReal.coe_lt_top, le_rfl, le_rfl, ?_⟩
    intro y hy
    obtain rfl := mem_singleton_iff.1 hy
    exact ⟨exists_isForwardSol_of_mem T.coe_nonneg hzT, le_rfl⟩
  have hc := hsafe.continuousOn_meanCan_time (κ := κ) (ρL := ρL) (ρR := ρR)
    hw.continuousOn (fun i => (hvLc i).continuousOn) (fun i => (hvRc i).continuousOn)
    (singleton_subset_iff.2 hz) hδ (mem_singleton z)
  have hraw : ContinuousOn
      (fun t : ℝ≥0 => couplingMean κ (rpath w) t (U t) z) (Iic T) := by
    apply hc.congr
    intro t ht
    exact couplingMean_eq_meanCan hw.continuousOn (singleton_subset_iff.2 hz) hsafe hδ ht
      (mem_singleton z) (hordL t) (hordR t) (hu t)
  exact (hraw.continuousAt (Iic_mem_nhds hsT')).continuousWithinAt

end InteractingSLE.Sec2.T24Bridge
