/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRNextMeas
import InteractingSLE.Spec.Supplement.GW4SafeRKernel
import InteractingSLE.Spec.Jordan.Coupling

/-!
# GW4: the exact component line input and its consequence

The new mathematical input is `HasComponentLines`: marked locality under the
conditional component law, and the finite-word mean identification there. The
Gaussian line kernels follow from marked locality by the already proved kernel
lemma. The line argument uses the component field, which is a GFF under the
conditional law; it makes no assertion that the ambient field remains a GFF.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField Restart Restart.DomainMarkov Restart.DomainMarkov.K2
  Sec7.PocketTraversal Restart.FCDet Supp8.Q3Stop Supp8.GB6.RelDrv Supp8.RelSafe Exist.StagedLaw

/-- The constant-record encoding used by the GW4 relative law. -/
abbrev componentPoint {Ω : Type*} (X : Ω → DistOn upperHalfPlaneOpens)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (ω : Ω) : Supp8.Q3Stop.CanonSpace :=
  (gw4Rec, relVar X R V ω)

/-- The geometric left coordinates of the component's typed word. -/
abbrev componentVL {Ω : Type*} (k : ℝ) (c₀ : BoundaryWord)
    (X : Ω → DistOn upperHalfPlaneOpens) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) :=
  fun i t ω => geomLW canonDrv (fun _ => typedXL k (wordType k c₀) c₀)
    i t (componentPoint X R V ω)

/-- The geometric right coordinates of the component's typed word. -/
abbrev componentVR {Ω : Type*} (k : ℝ) (c₀ : BoundaryWord)
    (X : Ω → DistOn upperHalfPlaneOpens) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) :=
  fun i t ω => geomRW canonDrv (fun _ => typedXR k (wordType k c₀) c₀)
    i t (componentPoint X R V ω)

/-- The two remaining mathematical assertions, for one actual conditional
component and one path-rule version: a marked local set at the physical lines
and its canonical finite-word mean. The witnesses have full definitions and no
law of the relative driver is assumed. -/
def HasComponentLines {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (k : ℝ) (c₀ : BoundaryWord) (F : Frame) (ν : Measure Ω)
    (X : Ω → DistOn upperHalfPlaneOpens) (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (hWm : ∀ r, Measurable (Wd r)) : Prop :=
  ∃ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω) (B : ℝ≥0 → Ω → Set ℂ),
    IsBoundedHarmonicExtension c₀.fn c₀.jumps u₀ ∧
    (∀ t, physFilt Frame.measurable_gw4Rec hWm ν t ≤ ℋ t) ∧
    (∀ t, ℋ t ≤ mΩ) ∧ (∀ t, Measurable[mΩ, hittingSigma] (B t)) ∧
    (∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω)) ∧
    (∀ t, IsHistoryAvoidanceLocal (ℋ t) (B t) (centredField X u₀) ν) ∧
    (∀ t, ∀ᵐ ω ∂ν, lineClock F Wd GT V t ω < V ω →
      H \ B t ω = H \ fwdHull (fun r : ℝ => R r.toNNReal ω)
        (lineClock F Wd GT V t ω).toNNReal) ∧
    ∀ t (g : Ω → DistOn upperHalfPlaneOpens), IsLocalSetMean (B t) (centredField X u₀) ν g →
      ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂ν, lineClock F Wd GT V t ω < V ω →
        Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => R r.toNNReal ω)
          (lineClock F Wd GT V t ω).toNNReal) →
        (g ω + smoothDist upperHalfPlaneOpens u₀) ψ =
          ∫ z, couplingMean k (fun r : ℝ => R r.toNNReal ω)
            (lineClock F Wd GT V t ω).toNNReal
            (bheProc k (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀)) R
              (componentVL k c₀ X R V) (componentVR k c₀ X R V) ω
              (lineClock F Wd GT V t ω).toNNReal) z * ψ z

/-- Identity chart transport, in the form used to specialize the line theorems. -/
theorem chartTransport_id_eq (k : ℝ) (f : DistOn upperHalfPlaneOpens) :
    Chart.chartTransport Chart.isConformal_id 1 0 k f = f :=
  ((isChartTransport_id k f).eq_chartTransport Chart.isConformal_id
    (Chart.locallyIntegrableOn_of_continuousOn continuousOn_const)).symm

/-- The canonical threshold is infinite when the component word's side partial
sums exceed `−2`. This holds for any measure, with the constant word and record. -/
theorem ae_canonStp_le_thr_component {k : ℝ} (c₀ : BoundaryWord)
    (hL : ∀ i : Fin (flowLineNL c₀.fn c₀.jumps 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL k c₀.fn c₀.jumps 0 0 l)
    (hR : ∀ i : Fin (flowLineNR c₀.fn c₀.jumps 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR k c₀.fn c₀.jumps 0 0 l)
    (μ : Measure Supp8.Q3Stop.CanonSpace) :
    ∀ᵐ y ∂μ, canonStp y ≤ thr (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀)) canonDrv
      (fun _ => typedXL k (wordType k c₀) c₀) (fun _ => typedXR k (wordType k c₀) c₀) y := by
  have hsL : ∀ i : Fin (wordType k c₀).1,
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), typedRhoL (wordType k c₀) l := by
    intro m
    have he : ∀ i, typedRhoL (wordType k c₀) i =
        flowLineRhoL k c₀.fn c₀.jumps 0 0 i := fun i => padFL_snd_fst_fin _ _ _ _ i
    simp only [he]
    exact hL m
  have hsR : ∀ i : Fin (wordType k c₀).2.1,
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), typedRhoR (wordType k c₀) l := by
    intro m
    have he : ∀ i, typedRhoR (wordType k c₀) i =
        flowLineRhoR k c₀.fn c₀.jumps 0 0 i := fun i => padFL_snd_snd_fin _ _ _ _ i
    simp only [he]
    exact hR m
  refine Eventually.of_forall fun y => ?_
  unfold thr
  rw [Sec7.Lemma725RefSafe.thresholdTime_eq_top_of_partialSums hsL hsR
    (fun t i => geomLW_le continuous_canonDrv _ y t i)
    (fun t => antitone_index_geomLW continuous_canonDrv (antitone_typedXL _ _ _) t)
    (fun t j => le_geomRW continuous_canonDrv _ y t j)
    (fun t => monotone_index_geomRW continuous_canonDrv (monotone_typedXR _ _ _) t)]
  exact le_top

end InteractingSLE.Theorem14.GW4Fix
