/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61UnionKRestart
import InteractingSLE.Spec.Sec5.Aux61GInstAccessCode

/-! # Fibre covers using selected-access restart codes

The record assembly of `Aux61UnionKRestart` specialized to the successor
code. The analytic local-set and cutoff inputs retain their original types.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GInst

open Aux61UnionK

open Aux61Fib (FibCode FibData PathGood fibW fibU fibField)
open Aux61FibData (IsRestartSpec exitEv clr visitSet)
open Aux61Win (IsCutoffOn IsPC1)
open Restart.FlowStopIdentCMI (CMCut)

universe u

variable {X : Type u} [mX : MeasurableSpace X] {ι : Type} [Countable ι] {β : ι → Type u}
  [mβ : ∀ i, MeasurableSpace (β i)]

/-- **The records of the restart codes**: history `Z i`, code `accessExitCode` of the restart data of index `i`, history
event `B i`, data `d i`, reference interval `(p i, q i)`, visit set, path-fact set and cutoffs. -/
def accessRestartRecords (Z : ∀ i, X → β i) (B : ∀ i, Set (β i)) (Er : ι → Set X) (c : ι → X → Chart)
    (ρ : ι → X → ℝ≥0 → ℂ) (T : ι → X → ℝ≥0∞) (V : ι → Set ℂ) (h : X → DistOn upperHalfPlaneOpens) (a k : ℝ)
    (d : ∀ i, β i → FibData) (p q : ι → ℝ) (F₀ : ∀ i, β i → CMCut) (N₀ : ∀ i, β i → Set ℂ) :
    Wire.Night.FibreRecords X where
  ι := ι
  countable := ‹Countable ι›
  β := β
  mβ := mβ
  Z := Z
  Y := fun i => accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h
  B := B
  data := d
  I := fun i => Ioo (p i) (q i)
  L := fun i => visitSet (p i) (q i)
  G := fun i => {s : β i × FibCode | PathGood (d i s.1) s.2}
  cutoff := F₀
  neighbourhood := N₀

/-- **`FibreGeometry` of the restart records** from the restart data (FIBDATA's code facts). -/
theorem fibreGeometry_accessRestartRecords {μ : Measure X} {E : X → Prop}
    (Z : ∀ i, X → β i) (hZ : ∀ i, Measurable (Z i)) (B : ∀ i, Set (β i)) (hB : ∀ i, MeasurableSet (B i))
    (Er : ι → Set X) (c : ι → X → Chart) (ρ : ι → X → ℝ≥0 → ℂ) (T : ι → X → ℝ≥0∞)
    (hs : ∀ i, IsRestartSpec (Er i) (c i) (ρ i) (T i)) (V : ι → Set ℂ) (hVo : ∀ i, IsOpen (V i))
    (hV0 : ∀ i, (0 : ℂ) ∈ V i) (hland : ∀ i, HasAccessLanding (Er i) (c i) (ρ i) (T i) (V i))
    (hinj : ∀ i, ∀ x ∈ Er i, InjOn (ρ i x) {u | (u : ℝ≥0∞) < T i x})
    (hliftc : ∀ i, ∀ x ∈ Er i, ContinuousOn (c i x).2.2 (c i x).dom)
    (h : X → DistOn upperHalfPlaneOpens) (hh : Measurable h) (a k : ℝ)
    (d : ∀ i, β i → FibData) (hdV : ∀ i z, (d i z).V = V i) (hdℓ : ∀ i z, (d i z).ℓ = clr (V i))
    (p q : ι → ℝ) (hRef : ∀ i, ∀ z ∈ B i, Aux61Cov.RefWin (d i z).κ (d i z).bR (d i z).JR (Ioo (p i) (q i)))
    (hexit : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → x ∈ exitEv (Er i) (c i) (ρ i) (T i) (V i))
    (hcover : ∀ᵐ x ∂μ, E x → ∃ i, Z i x ∈ B i)
    (hE : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → E x →
      accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x ∈ visitSet (p i) (q i))
    (F₀ : ∀ i, β i → CMCut) (N₀ : ∀ i, β i → Set ℂ)
    (hcut : ∀ i, ∀ z ∈ B i, IsCutoffOn (F₀ i z) (d i z).q (N₀ i z) (d i z).O₀ ∧ (d i z).buffer ⊆ N₀ i z) :
    Wire.Night.FibreGeometry μ E (accessRestartRecords Z B Er c ρ T V h a k d p q F₀ N₀) := by
  refine ⟨hZ, fun i => measurable_accessExitCode (hs i) (hVo i) (hV0 i) (hland i) (hinj i) (hliftc i) hh, hB,
    fun i => Aux61FibData.measurableSet_visitSet _ _, fun i s hs' => hs', hRef,
    fun i => @Aux61FibData.measurableSet_pathGood_family (β i) (mβ i) (d i) (V i) (hdV i) (hdℓ i) (hVo i),
    fun i z s _ hzs => hzs,
    fun i => ?_, hcover, hE, hcut⟩
  filter_upwards [hexit i] with x hx hxB
  exact pathGood_accessExitCode (hs i) (hVo i) (hV0 i) (hland i) (hinj i) (d i (Z i x)) (hdV i _) (hdℓ i _) (hx hxB)

/-- **The fibre-local cover from the restart codes**: the restart data, the fixed reference words with measurable
data and cutoffs, and at every fibre time `r` a harmonic part `h₁ i r` for which the chart field of the restart code
has the conditional local-set decomposition with the canonical (PC1) mean. -/
theorem hasFibreLocalCover_of_accessRestart {μ : Measure X} {E : X → Prop}
    (Z : ∀ i, X → β i) (hZ : ∀ i, Measurable (Z i)) (B : ∀ i, Set (β i)) (hB : ∀ i, MeasurableSet (B i))
    (Er : ι → Set X) (c : ι → X → Chart) (ρ : ι → X → ℝ≥0 → ℂ) (T : ι → X → ℝ≥0∞)
    (hs : ∀ i, IsRestartSpec (Er i) (c i) (ρ i) (T i)) (V : ι → Set ℂ) (hVo : ∀ i, IsOpen (V i))
    (hV0 : ∀ i, (0 : ℂ) ∈ V i) (hland : ∀ i, HasAccessLanding (Er i) (c i) (ρ i) (T i) (V i))
    (hinj : ∀ i, ∀ x ∈ Er i, InjOn (ρ i x) {u | (u : ℝ≥0∞) < T i x})
    (hliftc : ∀ i, ∀ x ∈ Er i, ContinuousOn (c i x).2.2 (c i x).dom)
    (h : X → DistOn upperHalfPlaneOpens) (hh : Measurable h) (a k : ℝ)
    (d : ∀ i, β i → FibData) (hdV : ∀ i z, (d i z).V = V i) (hdℓ : ∀ i z, (d i z).ℓ = clr (V i))
    (p q : ι → ℝ) (hRef : ∀ i, ∀ z ∈ B i, Aux61Cov.RefWin (d i z).κ (d i z).bR (d i z).JR (Ioo (p i) (q i)))
    (hexit : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → x ∈ exitEv (Er i) (c i) (ρ i) (T i) (V i))
    (hcover : ∀ᵐ x ∂μ, E x → ∃ i, Z i x ∈ B i)
    (hE : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → E x →
      accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x ∈ visitSet (p i) (q i))
    (F₀ : ∀ i, β i → CMCut) (N₀ : ∀ i, β i → Set ℂ)
    (hcut : ∀ i, ∀ z ∈ B i, IsCutoffOn (F₀ i z) (d i z).q (N₀ i z) (d i z).O₀ ∧ (d i z).buffer ⊆ N₀ i z)
    (κ₀ : ι → ℝ) (bR₀ : ι → ℝ → ℝ) (JR₀ : ι → Finset ℝ)
    (hword : ∀ i z, (d i z).κ = κ₀ i ∧ (d i z).bR = bR₀ i ∧ (d i z).JR = JR₀ i)
    (hqm : ∀ i, Measurable fun p : β i × ℂ => (d i p.1).q p.2)
    (hfm : ∀ i, Measurable fun p : β i × ℂ => (F₀ i p.1).f p.2)
    (hsrc : ∀ i, Measurable fun p : β i × ℂ => QuantumZipper.K3.greenDensity (F₀ i p.1).f p.2)
    (h₁ : ι → ℝ≥0 → X → DistOn upperHalfPlaneOpens)
    (hL : ∀ i (r : ℝ≥0), IsChartLocalAt μ (Z i) (B i) (accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h) r
      (fun x => canonMean (d i (Z i x)) (F₀ i (Z i x))
        (ULift.up.{u} (accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x)) r) (h₁ i r)) :
    HasFibreLocalCover μ E :=
  ⟨accessRestartRecords Z B Er c ρ T V h a k d p q F₀ N₀, κ₀, bR₀, JR₀, h₁,
    fibreGeometry_accessRestartRecords Z hZ B hB Er c ρ T hs V hVo hV0 hland hinj hliftc h hh a k d hdV hdℓ p q hRef hexit
      hcover hE F₀ N₀ hcut, ⟨hword, hqm, hfm, hsrc⟩, hL⟩

/-- **The fibre-local cover from the restart codes, with (K-a) and (K-b) separate**: the local-set decomposition with
some mean `M i r` satisfying Aux. lemma 61's (PC1) at every fibre time before the lifetime. -/
theorem hasFibreLocalCover_of_accessRestart_pc1 {μ : Measure X} {E : X → Prop}
    (Z : ∀ i, X → β i) (hZ : ∀ i, Measurable (Z i)) (B : ∀ i, Set (β i)) (hB : ∀ i, MeasurableSet (B i))
    (Er : ι → Set X) (c : ι → X → Chart) (ρ : ι → X → ℝ≥0 → ℂ) (T : ι → X → ℝ≥0∞)
    (hs : ∀ i, IsRestartSpec (Er i) (c i) (ρ i) (T i)) (V : ι → Set ℂ) (hVo : ∀ i, IsOpen (V i))
    (hV0 : ∀ i, (0 : ℂ) ∈ V i) (hland : ∀ i, HasAccessLanding (Er i) (c i) (ρ i) (T i) (V i))
    (hinj : ∀ i, ∀ x ∈ Er i, InjOn (ρ i x) {u | (u : ℝ≥0∞) < T i x})
    (hliftc : ∀ i, ∀ x ∈ Er i, ContinuousOn (c i x).2.2 (c i x).dom)
    (h : X → DistOn upperHalfPlaneOpens) (hh : Measurable h) (a k : ℝ)
    (d : ∀ i, β i → FibData) (hdV : ∀ i z, (d i z).V = V i) (hdℓ : ∀ i z, (d i z).ℓ = clr (V i))
    (p q : ι → ℝ) (hRef : ∀ i, ∀ z ∈ B i, Aux61Cov.RefWin (d i z).κ (d i z).bR (d i z).JR (Ioo (p i) (q i)))
    (hexit : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → x ∈ exitEv (Er i) (c i) (ρ i) (T i) (V i))
    (hcover : ∀ᵐ x ∂μ, E x → ∃ i, Z i x ∈ B i)
    (hE : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → E x →
      accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x ∈ visitSet (p i) (q i))
    (F₀ : ∀ i, β i → CMCut) (N₀ : ∀ i, β i → Set ℂ)
    (hcut : ∀ i, ∀ z ∈ B i, IsCutoffOn (F₀ i z) (d i z).q (N₀ i z) (d i z).O₀ ∧ (d i z).buffer ⊆ N₀ i z)
    (κ₀ : ι → ℝ) (bR₀ : ι → ℝ → ℝ) (JR₀ : ι → Finset ℝ)
    (hword : ∀ i z, (d i z).κ = κ₀ i ∧ (d i z).bR = bR₀ i ∧ (d i z).JR = JR₀ i)
    (hqm : ∀ i, Measurable fun p : β i × ℂ => (d i p.1).q p.2)
    (hfm : ∀ i, Measurable fun p : β i × ℂ => (F₀ i p.1).f p.2)
    (hsrc : ∀ i, Measurable fun p : β i × ℂ => QuantumZipper.K3.greenDensity (F₀ i p.1).f p.2)
    (M : ι → ℝ≥0 → X → ℂ → ℝ) (h₁ : ι → ℝ≥0 → X → DistOn upperHalfPlaneOpens)
    (hL : ∀ i (r : ℝ≥0), IsChartLocalAt μ (Z i) (B i) (accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h) r (M i r)
      (h₁ i r))
    (hPC : ∀ i (r : ℝ≥0), ∀ᵐ x ∂μ, Z i x ∈ B i →
      (r : ℝ≥0∞) < (accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x).life →
      IsPC1 (d i (Z i x)).κ
        (Aux61FibK.canonExt (d i (Z i x)) (ULift.up.{u} (accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x)) r)
        (Ito.rpath fun t => fibW t (ULift.up.{u} (accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x))) r
        (d i (Z i x)).q (d i (Z i x)).O₀ (M i r x)) :
    HasFibreLocalCover μ E := by
  have hg := fibreGeometry_accessRestartRecords (μ := μ) (E := E) Z hZ B hB Er c ρ T hs V hVo hV0 hland hinj hliftc h hh
    a k d hdV hdℓ p q hRef hexit hcover hE F₀ N₀ hcut
  have hgood : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → PathGood (d i (Z i x)) (accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x) :=
    fun i => (hg.2.2.2.2.2.2.2.2.1 i).mono fun x hx hxB => hx hxB
  exact hasFibreLocalCover_of_accessRestart Z hZ B hB Er c ρ T hs V hVo hV0 hland hinj hliftc h hh a k d hdV hdℓ p q hRef
    hexit hcover hE F₀ N₀ hcut κ₀ bR₀ JR₀ hword hqm hfm hsrc h₁ fun i r =>
      (hL i r).canon_of_isPC1 (d i) (F₀ i) (N₀ i) (hcut i) (hgood i) (hPC i r)

end InteractingSLE.Sec5.Aux61GInst
