import HigherDimLQGMetric.Amplify.TrialNormalize
import HigherDimLQGMetric.Amplify.TrialMeas
import HigherDimLQGMetric.WNSplit.LawUnique

/-! Law transfer for all full-field trials and all Gaussian windows at once. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Filter Set
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The full-field certificate used to transfer the amplification estimate
from the white-noise realization to an arbitrary LGF. -/
def AmpGoodTrial {M N : ℕ} (D Dt : DistRd d → ContMetric d)
    (ξ Q cs c1 ℓ δ s r K : ℝ) (w : Fin M → Fin N → Rd d) :
    Set (DistRd d) :=
  {X | (∀ i, ∃ k, X ∈ TrialEvent D Dt ξ Q cs c1 ℓ δ s (r • w i k)) ∧
    (∀ i k, |sphereAvg X s (r • w i k) - sphereAvg X r 0| ≤ K)}

/-- The certificate is measurable after completion under every LGF law. -/
theorem amplify_nullMeasurableSet_goodTrial
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    {M N : ℕ} (cs c1 ℓ δ s r K : ℝ)
    (w : Fin M → Fin N → Rd d) :
    NullMeasurableSet (AmpGoodTrial D Dt ξ Q cs c1 ℓ δ s r K w)
      (P.map h) := by
  have hhmap := hh.map_id
  let T : Set (DistRd d) :=
    {X | ∀ i : Fin M, ∃ k : Fin N,
      X ∈ TrialEvent D Dt ξ Q cs c1 ℓ δ s (r • w i k)}
  let G : Set (DistRd d) :=
    {X | ∀ i : Fin M, ∀ k : Fin N,
      |sphereAvg X s (r • w i k) - sphereAvg X r 0| ≤ K}
  have hT : NullMeasurableSet T (P.map h) := by
    have heq : T = ⋂ i : Fin M,
        ⋃ k : Fin N, TrialEvent D Dt ξ Q cs c1 ℓ δ s (r • w i k) := by
      ext X
      simp only [T, mem_ofPred_eq, mem_iInter, mem_iUnion]
    rw [heq]
    apply NullMeasurableSet.iInter
    intro i
    apply NullMeasurableSet.iUnion
    intro k
    exact amplify_nullMeasurableSet_trialEvent (P.map h) id hhmap.isLGFPlusCont
      hD hDt cs c1 ℓ δ s (r • w i k)
  have hG : MeasurableSet G := by
    have heqG : G = ⋂ i : Fin M, ⋂ k : Fin N,
        {X : DistRd d |
          |sphereAvg X s (r • w i k) - sphereAvg X r 0| ≤ K} := by
      ext X
      simp only [G, mem_ofPred_eq, mem_iInter]
    rw [heqG]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro k
    exact measurableSet_le
      ((((measurable_sphereAvg_left s (r • w i k)).sub
        (measurable_sphereAvg_left r 0)).abs)) measurable_const
  have heq : AmpGoodTrial D Dt ξ Q cs c1 ℓ δ s r K w = T ∩ G := by
    ext X
    rfl
  rw [heq]
  exact hT.inter hG.nullMeasurableSet

/-- The probability of the entire finite certificate is independent of the
LGF realization, including all correlations between trials and increments. -/
theorem amplify_goodTrial_law_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (h : Ω → DistRd d) (h' : Ω' → DistRd d)
    (hh : IsWholeSpaceLGF h P) (hh' : IsWholeSpaceLGF h' P')
    {ξ Q : ℝ} {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hd : 2 ≤ d) {M N : ℕ} (cs c1 ℓ δ : ℝ)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (K : ℝ) (w : Fin M → Fin N → Rd d) :
    P (h ⁻¹' AmpGoodTrial D Dt ξ Q cs c1 ℓ δ s r K w) =
      P' (h' ⁻¹' AmpGoodTrial D Dt ξ Q cs c1 ℓ δ s r K w) := by
  let N₀ : Ω → DistRd d :=
    fun ω => addConst (h ω) (-sphereAvg (h ω) 1 0)
  let N₁ : Ω' → DistRd d :=
    fun ω => addConst (h' ω) (-sphereAvg (h' ω) 1 0)
  have hN₀ : IsWholeSpaceLGF N₀ P := hh.addConst
    (((measurable_sphereAvg_left (d := d) 1 0).comp hh.measurable).neg)
  have hN₁ : IsWholeSpaceLGF N₁ P' := hh'.addConst
    (((measurable_sphereAvg_left (d := d) 1 0).comp hh'.measurable).neg)
  let E := AmpGoodTrial D Dt ξ Q cs c1 ℓ δ s r K w
  have hE₀ : NullMeasurableSet E (P.map N₀) :=
    amplify_nullMeasurableSet_goodTrial P N₀ hN₀ hD hDt cs c1 ℓ δ s r K w
  have hE₁ : NullMeasurableSet E (P'.map N₁) :=
    amplify_nullMeasurableSet_goodTrial P' N₁ hN₁ hD hDt cs c1 ℓ δ s r K w
  have htrial₀ : ∀ᵐ ω ∂P, ∀ i : Fin M, ∀ k : Fin N,
      h ω ∈ TrialEvent D Dt ξ Q cs c1 ℓ δ s (r • w i k) ↔
      N₀ ω ∈ TrialEvent D Dt ξ Q cs c1 ℓ δ s (r • w i k) := by
    exact eventually_all.mpr fun i => eventually_all.mpr fun k =>
      amplify_ae_trial_normalize hD hDt hd h hh cs c1 ℓ δ hs (r • w i k)
  have htrial₁ : ∀ᵐ ω ∂P', ∀ i : Fin M, ∀ k : Fin N,
      h' ω ∈ TrialEvent D Dt ξ Q cs c1 ℓ δ s (r • w i k) ↔
      N₁ ω ∈ TrialEvent D Dt ξ Q cs c1 ℓ δ s (r • w i k) := by
    exact eventually_all.mpr fun i => eventually_all.mpr fun k =>
      amplify_ae_trial_normalize hD hDt hd h' hh' cs c1 ℓ δ hs (r • w i k)
  have hcert₀ : h ⁻¹' E =ᵐ[P] N₀ ⁻¹' E := by
    filter_upwards [htrial₀, amplify_ae_increment_normalize hd h hh]
      with ω ht hi
    apply propext
    constructor
    · rintro ⟨htr, hgauss⟩
      refine ⟨fun i => ?_, fun i k => ?_⟩
      · obtain ⟨k, hk⟩ := htr i
        exact ⟨k, (ht i k).1 hk⟩
      · simpa only [N₀, hi s r hs hr (r • w i k)] using hgauss i k
    · rintro ⟨htr, hgauss⟩
      refine ⟨fun i => ?_, fun i k => ?_⟩
      · obtain ⟨k, hk⟩ := htr i
        exact ⟨k, (ht i k).2 hk⟩
      · simpa only [N₀, hi s r hs hr (r • w i k)] using hgauss i k
  have hcert₁ : h' ⁻¹' E =ᵐ[P'] N₁ ⁻¹' E := by
    filter_upwards [htrial₁, amplify_ae_increment_normalize hd h' hh']
      with ω ht hi
    apply propext
    constructor
    · rintro ⟨htr, hgauss⟩
      refine ⟨fun i => ?_, fun i k => ?_⟩
      · obtain ⟨k, hk⟩ := htr i
        exact ⟨k, (ht i k).1 hk⟩
      · simpa only [N₁, hi s r hs hr (r • w i k)] using hgauss i k
    · rintro ⟨htr, hgauss⟩
      refine ⟨fun i => ?_, fun i k => ?_⟩
      · obtain ⟨k, hk⟩ := htr i
        exact ⟨k, (ht i k).2 hk⟩
      · simpa only [N₁, hi s r hs hr (r • w i k)] using hgauss i k
  calc
    P (h ⁻¹' E) = P (N₀ ⁻¹' E) := measure_congr hcert₀
    _ = (P.map N₀) E := (Measure.map_apply₀ hN₀.measurable.aemeasurable hE₀).symm
    _ = (P'.map N₁) E := by rw [map_normalizedLGF_eq hd hh hh']
    _ = P' (N₁ ⁻¹' E) := Measure.map_apply₀ hN₁.measurable.aemeasurable hE₁
    _ = P' (h' ⁻¹' E) := measure_congr hcert₁.symm

end HigherDimLQGMetric
