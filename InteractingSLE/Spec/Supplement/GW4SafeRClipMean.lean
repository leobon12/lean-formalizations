/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRClipLocal
import InteractingSLE.Spec.Supplement.GW4SafeRNextAssemble

/-!
# GW4: a fixed harmonic extension and one mean per test suffice

The finite word has a unique bounded harmonic extension, already proved in the
piecewise-constant boundary API. Local-set mean uniqueness reduces the required
identification for every mean to one mean for each test separately. The new
mathematical inputs remain explicit: live avoidance and this mean identification.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField Restart Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.RelSafe Supp8.Q3Stop

/-- The bounded harmonic extension of the actual component word. Existence
and uniqueness are the landed piecewise-constant boundary theorem. -/
def safeWordHarmonic (c₀ : BoundaryWord) : ℂ → ℝ :=
  Classical.choose (PiecewiseConstant.existsUnique_isBoundedHarmonicExtension
    c₀.isPiecewiseConstantBoundaryData)

theorem safeWordHarmonic_spec (c₀ : BoundaryWord) :
    IsBoundedHarmonicExtension c₀.fn c₀.jumps (safeWordHarmonic c₀) :=
  (Classical.choose_spec (PiecewiseConstant.existsUnique_isBoundedHarmonicExtension
    c₀.isPiecewiseConstantBoundaryData)).1

/-- The remaining finite-word mean calculation. For each line and test it
suffices to identify one local-set mean; its choice may depend on that test.
This proposition is an explicit mathematical hypothesis, not a proved theorem. -/
def SafeHullMean {Ω : Type*} [MeasurableSpace Ω] (k : ℝ) (c₀ : BoundaryWord)
    (F : Frame) (ν : Measure Ω) (X : Ω → DistOn upperHalfPlaneOpens)
    (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) : Prop :=
  ∀ t (ψ : TestOn upperHalfPlaneOpens), ∃ g : Ω → DistOn upperHalfPlaneOpens,
    IsLocalSetMean (safeHull F Wd GT R V t) (centredField X (safeWordHarmonic c₀)) ν g ∧
    ∀ᵐ ω ∂ν, lineClock F Wd GT V t ω < V ω →
      Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => R r.toNNReal ω)
        (lineClock F Wd GT V t ω).toNNReal) →
      (g ω + smoothDist upperHalfPlaneOpens (safeWordHarmonic c₀)) ψ =
        ∫ z, couplingMean k (fun r : ℝ => R r.toNNReal ω)
          (lineClock F Wd GT V t ω).toNNReal
          (bheProc k (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀)) R
            (componentVL k c₀ X R V) (componentVR k c₀ X R V) ω
            (lineClock F Wd GT V t ω).toNNReal) z * ψ z

/-- All random-set witnesses, harmonic-extension existence, and arbitrary-mean
quantifiers in `HasComponentLines` are discharged from the two displayed inputs. -/
theorem hasComponentLines_of_safeHull {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {k : ℝ} {c₀ : BoundaryWord} {F : Frame}
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps)
    {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {V : Ω → ℝ≥0∞} (hF : F.IsOk)
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) (hWm : ∀ r, Measurable (Wd r))
    (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂ν, ω ∈ GT)
    (hver : IsGW4RelVersionR ν Wd F.c F.C R V)
    (ha : SafeHullAvoidance F ν (centredField X (safeWordHarmonic c₀))
      (physFilt Frame.measurable_gw4Rec hWm ν) Wd GT R V)
    (hm : SafeHullMean k c₀ F ν X Wd GT R V) :
    HasComponentLines k c₀ F ν X Wd GT R V hWm := by
  have hBm : ∀ t, Measurable[mΩ, hittingSigma] (safeHull F Wd GT R V t) := fun t =>
    (Frame.measurable_safeHull hF hGT hWm hGTm hGTae hver t).mono
      ((physFilt Frame.measurable_gw4Rec hWm ν).le t) le_rfl
  refine ⟨safeWordHarmonic c₀, physFilt Frame.measurable_gw4Rec hWm ν,
    safeHull F Wd GT R V, safeWordHarmonic_spec c₀, fun _ => le_rfl,
    (physFilt Frame.measurable_gw4Rec hWm ν).le, hBm, ?_,
    isHistoryAvoidanceLocal_safeHull ha, ?_, ?_⟩
  · exact fun t ω => ⟨safeHull_subset_H F Wd GT R V t ω,
      Frame.isOpen_H_diff_safeHull hver t ω⟩
  · exact fun t => Eventually.of_forall fun ω hlt => H_diff_safeHull_of_lt F Wd GT R V t ω hlt
  · intro t g hg ψ
    obtain ⟨g₀, hg₀, he⟩ := hm t ψ
    filter_upwards [IsLocalSetMean.ae_apply_eq (hBm t)
      (measurable_centredField hX.1 _) hg hg₀ ψ, he] with ω hω hmean hlt hdis
    change g ω ψ + _ = _
    rw [hω]
    exact hmean hlt hdis

/-- The probability law consequence uses the landed line assembly. The only
new mathematical assumptions are live avoidance and the one-mean calculation. -/
theorem hasRelSafe_of_safeHull {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {k : ℝ} {c₀ : BoundaryWord} {F : Frame}
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps)
    {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {V : Ω → ℝ≥0∞} (hF : F.IsOk)
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) (hWm : ∀ r, Measurable (Wd r))
    (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂ν, ω ∈ GT)
    (hver : IsGW4RelVersionR ν Wd F.c F.C R V)
    (hL : ∀ i : Fin (flowLineNL c₀.fn c₀.jumps 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL k c₀.fn c₀.jumps 0 0 l)
    (hR : ∀ i : Fin (flowLineNR c₀.fn c₀.jumps 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR k c₀.fn c₀.jumps 0 0 l)
    (ha : SafeHullAvoidance F ν (centredField X (safeWordHarmonic c₀))
      (physFilt Frame.measurable_gw4Rec hWm ν) Wd GT R V)
    (hm : SafeHullMean k c₀ F ν X Wd GT R V) :
    HasRelSafe k (wordType k c₀) (fun _ => c₀) univ
      (ν.map fun ω => componentPoint X R V ω) :=
  hasRelSafe_of_componentLines hX hF hGT hWm hGTm hGTae hver hL hR
    (hasComponentLines_of_safeHull hX hF hGT hWm hGTm hGTae hver ha hm)

end InteractingSLE.Theorem14.GW4Fix
