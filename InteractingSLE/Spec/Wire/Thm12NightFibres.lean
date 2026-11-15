/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12NightInputs

/-!
# The corrected fibre cover from the newest glued rational-kernel interface

PROVE-WIRE-PARTA. The four independent mathematical inputs are the history/word/
path cover, joint kernel measurability, glued rectangle integrals, and raw member
identities. No unproved Gaussian or locality fact is stored as mere context.
-/

set_option autoImplicit false
noncomputable section
universe u
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real
namespace InteractingSLE.Wire.Night
open Sec4 Sec5 Sec5.Aux61Fib Sec5.Aux61FibK Sec5.Aux61R2 Sec5.Aux61Cov
open Sec5.Prop51G Sec5.Aux61Kernel Sec5.Cond44Ref Sec5.Aux61Act
open WangWu WholeField LocalSets Restart Exist.StagedLaw LocalExt Coupling LawUnique
open Restart.DomainMarkov (RatIdx dyT)
open Restart.FlowStopIdentCMI (CMCut)
open Sec5.Aux61Win (IsCutoffOn)

/-- Choices of records and cutoffs. The existing `FibData` includes mathematical
word and harmonic facts; existence of this data is counted as a mathematical input. -/
structure FibreRecords (X : Type u) [MeasurableSpace X] where
  ι : Type
  [countable : Countable ι]
  β : ι → Type u
  [mβ : ∀ i, MeasurableSpace (β i)]
  Z : ∀ i, X → β i
  Y : ι → X → FibCode
  B : ∀ i, Set (β i)
  data : ∀ i, β i → FibData
  I : ι → Set ℝ
  L : ι → Set FibCode
  G : ∀ i, Set (β i × FibCode)
  cutoff : ∀ i, β i → CMCut
  neighbourhood : ∀ i, β i → Set ℂ

attribute [instance] FibreRecords.countable FibreRecords.mβ

/-- The cover and its actual reference words and paths, before the kernel laws. -/
def FibreGeometry {X : Type u} [MeasurableSpace X] (μ : Measure X) (E : X → Prop)
    (D : FibreRecords X) : Prop :=
  (∀ i, Measurable (D.Z i)) ∧ (∀ i, Measurable (D.Y i)) ∧
  (∀ i, MeasurableSet (D.B i)) ∧ (∀ i, MeasurableSet (D.L i)) ∧
  (∀ i, ∀ s ∈ D.L i, ∃ v : ℝ≥0, (v : ℝ≥0∞) ≤ s.life ∧ ∃ y ∈ D.I i, s.trace v = (y : ℂ)) ∧
  (∀ i, ∀ z ∈ D.B i, RefWin (D.data i z).κ (D.data i z).bR (D.data i z).JR (D.I i)) ∧
  (∀ i, MeasurableSet (D.G i)) ∧
  (∀ i z s, z ∈ D.B i → (z, s) ∈ D.G i → PathGood (D.data i z) s) ∧
  (∀ i, ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → (D.Z i x, D.Y i x) ∈ D.G i) ∧
  (∀ᵐ x ∂μ, E x → ∃ i, D.Z i x ∈ D.B i) ∧
  (∀ i, ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → E x → D.Y i x ∈ D.L i) ∧
  ∀ i, ∀ z ∈ D.B i,
    IsCutoffOn (D.cutoff i z) (D.data i z).q (D.neighbourhood i z) (D.data i z).O₀ ∧
      (D.data i z).buffer ⊆ D.neighbourhood i z

/-- Joint measurability of the explicit rational Gaussian kernel. -/
def FibreMeas {X : Type u} [MeasurableSpace X] (D : FibreRecords X) : Prop :=
  ∀ i (n k : ℕ) (p : RatIdx), Measurable[(D.mβ i).prod (codeSigma.{u} n k)]
    (fun zs : D.β i × ULift.{u} FibCode =>
      (ratAvoid n k p).indicator (ratKer (D.data i zs.1) (D.cutoff i zs.1) n k p) zs.2)

/-- The characteristic-functional identity on glued history/code rectangles. -/
def FibreIntegral {X : Type u} [MeasurableSpace X] (μ : Measure X) (D : FibreRecords X) : Prop :=
  ∀ i (n k : ℕ) (p : RatIdx) (T : Finset (ℚ × ℚ × ℚ)) (B' : Set (D.β i)),
    MeasurableSet B' → B' ⊆ D.B i →
    ∫ x in D.Z i ⁻¹' B' ∩ (fun x => ULift.up.{u} (D.Y i x)) ⁻¹' ratPi fibW fibU (dyT n k) T,
      gluedInt (D.B i) (D.data i) (D.cutoff i) n k p (D.Z i x, ULift.up.{u} (D.Y i x)) ∂μ = 0

/-- Local member identities in each conditioned fibre, on raw code events. -/
def FibreMembers {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (D : FibreRecords X) : Prop :=
  ∀ i, ∀ᵐ x ∂μ, D.Z i x ∈ D.B i →
    FibMembersRaw (D.data i (D.Z i x))
      (condDistrib (fun x => ULift.up.{u} (D.Y i x)) (D.Z i) μ (D.Z i x))

/-- FIB2's assembled cover, with raw member identities converted by the landed adapter. -/
theorem hasDyCover_of_glued {X : Type u} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {E : X → Prop} (D : FibreRecords X) (hGeo : FibreGeometry μ E D)
    (hMeas : FibreMeas D) (hInt : FibreIntegral μ D) (hMem : FibreMembers μ D) :
    HasDyActFibreCover μ E RefWin := by
  obtain ⟨hZ, hY, hB, hL, hLv, hRef, hG, hGgood, hYG, hcover, hE, hcut⟩ := hGeo
  apply hasDyActFibreCover_of_glued D.Z hZ D.Y hY D.B hB D.data D.I D.L hL hLv hRef D.G hG
    hGgood hYG hcover hE D.cutoff D.neighbourhood hcut hMeas hInt
  intro i
  filter_upwards [hMem i] with x hx hxB
  exact fibMembers_of_raw _ _ (hx hxB)

/-- The actual small-gap source settings with countable records covering the window event. -/
def GluedFibreGeometryOn : Prop :=
  ∀ (t : ℚ) (c : WinCode), ∀ ht : 0 < t,
  ∀ κ : ℝ, ∀ (hκ : 0 < κ) (hκ4 : κ < 4), ∀ a b θ₁ θ₂ : ℝ, ∀ (h12 : θ₁ < θ₂) (hG : ¬ IsLargeGap κ θ₁ θ₂),
    ∀ (hb : sleLambda κ - θ₁ * chiC κ ≤ b)
    (ha : sleLambda κ - Real.pi * chiC κ + θ₂ * chiC κ ≤ a),
    ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
      (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ)),
      ∀ hfl : IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P h η ζ,
      ∀ {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
        ∀ hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂,
        ∀ hlaw : P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂,
        ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
          ∀ hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k,
          ∀ (s : ℚ) (hs : 0 < s),
            ∃ D, FibreGeometry (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
      ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))) (fun p => RestartWindowEvent
        (Prop411Q.cfDrv p.2) s (fun v : ℝ => η p.1 v.toNNReal) t c) D

def GluedFibreMeasOn (hGeo : GluedFibreGeometryOn.{u}) : Prop :=
  ∀ (t : ℚ) (c : WinCode), ∀ ht : 0 < t,
  ∀ κ : ℝ, ∀ (hκ : 0 < κ) (hκ4 : κ < 4), ∀ a b θ₁ θ₂ : ℝ, ∀ (h12 : θ₁ < θ₂) (hG : ¬ IsLargeGap κ θ₁ θ₂),
    ∀ (hb : sleLambda κ - θ₁ * chiC κ ≤ b)
    (ha : sleLambda κ - Real.pi * chiC κ + θ₂ * chiC κ ≤ a),
    ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
      (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ)),
      ∀ hfl : IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P h η ζ,
      ∀ {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
        ∀ hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂,
        ∀ hlaw : P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂,
        ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
          ∀ hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k,
          ∀ (s : ℚ) (hs : 0 < s),
            FibreMeas (Classical.choose (hGeo t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw
              k hk s hs))

def GluedFibreIntegralOn (hGeo : GluedFibreGeometryOn.{u}) : Prop :=
  ∀ (t : ℚ) (c : WinCode), ∀ ht : 0 < t,
  ∀ κ : ℝ, ∀ (hκ : 0 < κ) (hκ4 : κ < 4), ∀ a b θ₁ θ₂ : ℝ, ∀ (h12 : θ₁ < θ₂) (hG : ¬ IsLargeGap κ θ₁ θ₂),
    ∀ (hb : sleLambda κ - θ₁ * chiC κ ≤ b)
    (ha : sleLambda κ - Real.pi * chiC κ + θ₂ * chiC κ ≤ a),
    ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
      (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ)),
      ∀ hfl : IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P h η ζ,
      ∀ {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
        ∀ hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂,
        ∀ hlaw : P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂,
        ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
          ∀ hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k,
          ∀ (s : ℚ) (hs : 0 < s),
            FibreIntegral (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
      ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))) (Classical.choose (hGeo t c ht κ hκ
        hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs))

def GluedFibreMembersOn (hGeo : GluedFibreGeometryOn.{u}) : Prop :=
  ∀ (t : ℚ) (c : WinCode), ∀ ht : 0 < t,
  ∀ κ : ℝ, ∀ (hκ : 0 < κ) (hκ4 : κ < 4), ∀ a b θ₁ θ₂ : ℝ, ∀ (h12 : θ₁ < θ₂) (hG : ¬ IsLargeGap κ θ₁ θ₂),
    ∀ (hb : sleLambda κ - θ₁ * chiC κ ≤ b)
    (ha : sleLambda κ - Real.pi * chiC κ + θ₂ * chiC κ ≤ a),
    ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
      (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ)),
      ∀ hfl : IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P h η ζ,
      ∀ {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
        ∀ hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂,
        ∀ hlaw : P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂,
        ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
          ∀ hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k,
          ∀ (s : ℚ) (hs : 0 < s),
            FibreMembers (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
      ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))) (Classical.choose (hGeo t c ht κ hκ
        hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs))

/-- All four newest fibre leaves assemble the old corrected dyadic-cover input. -/
theorem dyCover_of_glued (hGeo : GluedFibreGeometryOn.{u}) (hMeas : GluedFibreMeasOn hGeo)
    (hInt : GluedFibreIntegralOn hGeo) (hMem : GluedFibreMembersOn hGeo) :
    DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) RefWin := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P hP h η ζ hh hfl Ω₂ mΩ₂ P₂ hP₂ h₂ W₂ ζ₂ hcf hlaw k hK hk s hs
  exact hasDyCover_of_glued (Classical.choose (hGeo t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂
    hcf hlaw k hk s hs))
    (Classical.choose_spec (hGeo t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs))
    (hMeas t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)
    (hInt t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)
    (hMem t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

end InteractingSLE.Wire.Night
