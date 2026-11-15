/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCPlumbBase
import InteractingSLE.Spec.Restart.FCDetTransfer
import InteractingSLE.Spec.Restart.FCBridge
import InteractingSLE.Spec.Restart.ClockGeom
import InteractingSLE.Spec.Sec7.Lemma71CClock

/-!
# First-contact continuation assembly

This module builds the frozen segment driver and its natural word/driver filtration, glues deterministic-line
kernels over a countable box cover, names the geometric locality input for the shifted first-contact union, and
assembles these inputs with the any-space K2 transfer and the driver-to-path bridge.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE

namespace Restart.FCPlumb

open Chart DomainMarkov DomainMarkov.Aux79 K2 WholeField Sec7.PocketTraversal
open Coupling Sec2.Assembly

universe u

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The time at which the first-contact segment driver is held fixed. Infinite lifetime means no freeze. -/
def fcDriverStopTime (U : Ω → ℝ≥0∞) (q : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  if U ω = ⊤ then q else min q (U ω).toNNReal

/-- The continuation driver on the measurable good event, frozen at its capacity lifetime and zero elsewhere. -/
noncomputable def fcSegmentDriver (E : Set Ω) (Γ : Ω → ℝ≥0 → ℂ) (U : Ω → ℝ≥0∞)
    (q : ℝ≥0) (ω : Ω) : ℝ := by
  classical
  exact if ω ∈ E then Sec7.Lemma71C.segDriver (InteractingSLE.Restart.realPath (Γ ω))
    (fcDriverStopTime U q ω) else 0

/-- Measurability of the frozen branch gives measurability of the driver on the measurable good event. -/
theorem measurable_fcSegmentDriver {E : Set Ω} (hE : MeasurableSet E)
    {Γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞}
    (hseg : ∀ q : ℝ≥0, Measurable fun ω =>
      Sec7.Lemma71C.segDriver (InteractingSLE.Restart.realPath (Γ ω)) (fcDriverStopTime U q ω)) :
    ∀ q : ℝ≥0, Measurable (fcSegmentDriver E Γ U q) := by
  classical
  intro q
  change Measurable (fun ω => if ω ∈ E then
    Sec7.Lemma71C.segDriver (InteractingSLE.Restart.realPath (Γ ω))
      (fcDriverStopTime U q ω) else 0)
  exact Measurable.ite hE (hseg q) measurable_const

/-- The measurable coordinate family used to form the segment-driver filtration. -/
theorem fcSegmentDriverMeasurable {E : Set Ω} (hE : MeasurableSet E)
    {Γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞}
    (hseg : ∀ q : ℝ≥0, Measurable fun ω =>
      Sec7.Lemma71C.segDriver (InteractingSLE.Restart.realPath (Γ ω)) (fcDriverStopTime U q ω)) :
    ∀ q : ℝ≥0, Measurable (fun ω => fcSegmentDriver E Γ U q ω) := measurable_fcSegmentDriver hE hseg

/-- The frozen segment driver starts at zero whenever its good paths are segment curves. -/
theorem fcSegmentDriver_zero {E : Set Ω} {Γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞}
    (hseg : ∀ ω ∈ E, Sec7.Lemma71C.IsSegCurve (InteractingSLE.Restart.realPath (Γ ω))) :
    ∀ ω, fcSegmentDriver E Γ U 0 ω = 0 := by
  classical
  intro ω
  by_cases hω : ω ∈ E
  · change (if ω ∈ E then _ else 0) = 0
    rw [if_pos hω]
    simpa [fcDriverStopTime] using (hseg ω hω).segDriver_spec.1
  · simp [fcSegmentDriver, hω]

/-- The continuation's stochastic driver, with the bad event set to the zero path. -/
def fcSegmentProcess (E : Set Ω) (Γ : Ω → ℝ≥0 → ℂ) (U : Ω → ℝ≥0∞) :
    ℝ≥0 → Ω → ℝ := fun q ω => fcSegmentDriver E Γ U q ω

/-- The force-point positions read from a fixed first-contact word type. -/
def fcWordLeftPositions (κ θ : ℝ) (nL nR : ℕ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (β : Ω → BoundaryWord) : Ω → Fin nL → ℝ := fun ω =>
  FCDet.typeXL κ θ nL nR ρL ρR (β ω)

/-- The right force-point positions read from a fixed first-contact word type. -/
def fcWordRightPositions (κ θ : ℝ) (nL nR : ℕ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (β : Ω → BoundaryWord) : Ω → Fin nR → ℝ := fun ω =>
  FCDet.typeXR κ θ nL nR ρL ρR (β ω)

/-- The K2 lifetime for the first-contact segment driver is the force-point threshold. -/
def fcSegmentThreshold (κ θ : ℝ) (nL nR : ℕ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (E : Set Ω) (Γ : Ω → ℝ≥0 → ℂ) (U : Ω → ℝ≥0∞) (β : Ω → BoundaryWord) : Ω → ℝ≥0∞ :=
  FCDet.thr ρL ρR (fcSegmentProcess E Γ U)
    (fcWordLeftPositions κ θ nL nR ρL ρR β) (fcWordRightPositions κ θ nL nR ρL ρR β)

/-- Continuity of the stopped driver up to a finite terminal capacity time. This is the endpoint-continuity input
needed in addition to `IsSegCurve.segDriver_spec`, whose continuity is stated only strictly before capLife. -/
def FCStoppedDriverContinuous (E : Set Ω) (Γ : Ω → ℝ≥0 → ℂ) (U : Ω → ℝ≥0∞) : Prop :=
  ∀ ω ∈ E, Continuous fun q : ℝ≥0 =>
    Sec7.Lemma71C.segDriver (InteractingSLE.Restart.realPath (Γ ω)) (fcDriverStopTime U q ω)

/-- The globally continuous version of the driver follows from continuity on the good event and its zero value
elsewhere. -/
theorem continuous_fcSegmentDriver {E : Set Ω} {Γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞}
    (hcont : FCStoppedDriverContinuous E Γ U) :
    ∀ ω, Continuous fun q => fcSegmentDriver E Γ U q ω := by
  classical
  intro ω
  by_cases hω : ω ∈ E
  · simpa [fcSegmentDriver, hω] using hcont ω hω
  · simpa [fcSegmentDriver, hω] using continuous_const

/-- The filtration generated by the initial word and the driver up to the current time. -/
def fcDriverFiltration {β : Type*} [MeasurableSpace β] (word : Ω → β)
    (W : ℝ≥0 → Ω → ℝ) (hword : Measurable word) (hW : ∀ q, Measurable (W q)) :
    Filtration ℝ≥0 mΩ where
  seq q := MeasurableSpace.comap word inferInstance ⊔
    ⨆ r : ℝ≥0, ⨆ (_ : r ≤ q), MeasurableSpace.comap (W r) inferInstance
  mono' q q' hqq' := by
    refine sup_le_sup_left ?_ _
    refine iSup₂_le fun r hr => ?_
    exact le_iSup₂_of_le
      (f := fun r (_ : r ≤ q') => MeasurableSpace.comap (W r) inferInstance)
      r (hr.trans hqq') le_rfl
  le' q := by
    refine sup_le hword.comap_le (iSup₂_le fun r _ => ?_)
    exact (hW r).comap_le

/-- The natural filtration contains the word at time zero. -/
theorem fcDriverFiltration_word_le {β : Type*} [MeasurableSpace β] (word : Ω → β)
    (W : ℝ≥0 → Ω → ℝ) (hword : Measurable word) (hW : ∀ q, Measurable (W q)) (q : ℝ≥0) :
    MeasurableSpace.comap word inferInstance ≤ fcDriverFiltration word W hword hW q := le_sup_left

/-- The natural filtration contains every driver coordinate through its current time. -/
theorem fcDriverFiltration_coord_le {β : Type*} [MeasurableSpace β] (word : Ω → β)
    (W : ℝ≥0 → Ω → ℝ) (hword : Measurable word) (hW : ∀ q, Measurable (W q))
    {r q : ℝ≥0} (hr : r ≤ q) :
    MeasurableSpace.comap (W r) inferInstance ≤ fcDriverFiltration word W hword hW q :=
  le_sup_of_le_right (le_iSup₂_of_le (f := fun r (_ : r ≤ q) =>
    MeasurableSpace.comap (W r) inferInstance) r hr le_rfl)

/-- The word is measurable at time zero and the driver is strongly adapted to its natural filtration. -/
theorem fcDriverFiltration_adapted {β : Type*} [MeasurableSpace β] [TopologicalSpace β]
    (word : Ω → β) (W : ℝ≥0 → Ω → ℝ) (hword : Measurable word)
    (hW : ∀ q, Measurable (W q)) :
    Measurable[fcDriverFiltration word W hword hW 0] word ∧
      StronglyAdapted (fcDriverFiltration word W hword hW) W := by
  constructor
  · exact Measurable.of_comap_le (fcDriverFiltration_word_le word W hword hW 0)
  · intro q
    exact (Measurable.of_comap_le (fcDriverFiltration_coord_le word W hword hW le_rfl)).stronglyMeasurable

/-- The natural filtration of the first-contact word and its measurable segment driver. -/
def fcSegmentNaturalFiltration {E : Set Ω} {Γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞}
    (word : Ω → BoundaryWord) (hword : Measurable word) (hE : MeasurableSet E)
    (hseg : ∀ q : ℝ≥0, Measurable fun ω =>
      Sec7.Lemma71C.segDriver (InteractingSLE.Restart.realPath (Γ ω)) (fcDriverStopTime U q ω)) :
    Filtration ℝ≥0 mΩ :=
  fcDriverFiltration word (fcSegmentProcess E Γ U) hword (fcSegmentDriverMeasurable hE hseg)

/-- A boxwise version of the deterministic-line Gaussian kernel. In the first-contact application, each instance is
supplied by `exists_shUnion_marked_of_isFlowLine` after restricting to a capped first-contact box and identifying
that cap's complementary domain with the chart image of the driver-hull complement. -/
def FCBoxKernelStatement {P : Measure Ω} {F : Set Ω} {Qc : ℝ≥0 → Ω → ℝ≥0}
    {c : Ω → Chart} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → DistOn upperHalfPlaneOpens} (𝒢L : ℝ≥0 → MeasurableSpace Ω)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens) (E : ℕ → Set Ω) : Prop :=
  ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens) (m : ℕ), ∀ᵐ ω ∂P,
    ω ∈ E m → ω ∈ F → (Qc t ω : ℝ≥0∞) < ζ ω →
      tsupport φ ⊆ (c ω).2.1 ''
        (H \ QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω)) →
          P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢L t] ω =
            Complex.exp (Complex.I * (M t ω φ : ℂ) -
              (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov
                ((c ω).2.1 ''
                  (H \ QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω))) φ φ : ℝ) : ℂ))

/-- Countable box gluing for the first-contact line kernel. The proof is the countable almost-everywhere union step;
the mathematical kernel on each box is the `FCBoxKernelStatement` input. -/
theorem fcLineKernel_of_boxwise {P : Measure Ω} {F : Set Ω} {Qc : ℝ≥0 → Ω → ℝ≥0}
    {c : Ω → Chart} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → DistOn upperHalfPlaneOpens} (𝒢L : ℝ≥0 → MeasurableSpace Ω)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens) (E : ℕ → Set Ω)
    (hcover : ∀ t ω, ω ∈ F → (Qc t ω : ℝ≥0∞) < ζ ω → ∃ m, ω ∈ E m)
    (hbox : FCBoxKernelStatement (P := P) (F := F) (Qc := Qc) (c := c) (W := W)
      (ζ := ζ) (h := h) 𝒢L M E) :
    FCLineKernelStatement (P := P) (F := F) (Qc := Qc) (c := c) (W := W)
      (ζ := ζ) (h := h) 𝒢L M := by
  intro t φ
  have hboxes : ∀ m : ℕ, ∀ᵐ ω ∂P, ω ∈ E m → ω ∈ F → (Qc t ω : ℝ≥0∞) < ζ ω →
      tsupport φ ⊆ (c ω).2.1 '' (H \ QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω)) →
        P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢L t] ω =
          Complex.exp (Complex.I * (M t ω φ : ℂ) -
            (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov
              ((c ω).2.1 ''
                (H \ QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω))) φ φ : ℝ) : ℂ)) :=
    fun m => hbox t φ m
  filter_upwards [ae_all_iff.2 hboxes] with ω hω hF hζ hsupp
  obtain ⟨m, hωm⟩ := hcover t ω hF hζ
  exact hω m hωm hF hζ hsupp

/-- The exact geometric inputs still needed to apply the (L) adapter to the first-contact shifted union. -/
structure FCShUnionLineLocality {P : Measure Ω} {F : Set Ω} {Qc : ℝ≥0 → Ω → ℝ≥0}
    {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {c : Ω → Chart}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (ℋ : Filtration ℝ≥0 mΩ)
    (η₁ η₂ : Ω → ℝ≥0 → ℂ) where
  openComplement : ∀ t ω, IsOpen (H \ shUnion η₁ η₂ t 0 ω)
  markedLocal : ∀ t, IsHistoryAvoidanceLocal (ℋ t) (shUnion η₁ η₂ t 0)
    (centredField h u₀) P
  chartDomain : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (Qc t ω : ℝ≥0∞) < ζ ω →
    H \ shUnion η₁ η₂ t 0 ω = (c ω).2.1 ''
      (H \ QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω))

/-- **First-contact canonical conditional determination from the line mean.** The driver is the segment driver on
the measurable good event and is zero off that event; its natural word-and-driver filtration supplies the adapted
continuation. The box inputs are the capped specializations of
`exists_shUnion_marked_of_isFlowLine`; `fcLineKernel_of_boxwise` glues them before the K2 (S)/(L) adapters are
applied. The hypotheses `hthreshold`, `htrace`, and `hjoint` record the remaining lifetime, generating-trace, and
conditional-law facts of the first-contact construction. -/
theorem firstContactCanonCondDet_of_lineMean
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓖 : Filtration ℝ≥0 mΩ} {live E : Set Ω}
    (hliveMeas : MeasurableSet live) (hliveG0 : MeasurableSet[𝓖 0] live)
    (β : Ω → BoundaryWord) (hβ : Measurable β)
    (hType : ∀ ω ∈ live, β ω ∈ FCDet.typeSet κ θ nL nR ρL ρR)
    (hE : MeasurableSet E)
    {Γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞}
    (hseg : ∀ ω ∈ E, Sec7.Lemma71C.IsSegCurve (InteractingSLE.Restart.realPath (Γ ω)))
    (hsegMeas : ∀ q : ℝ≥0, Measurable fun ω =>
      Sec7.Lemma71C.segDriver (InteractingSLE.Restart.realPath (Γ ω))
        (fcDriverStopTime U q ω))
    (hLiveNatural : MeasurableSet[fcSegmentNaturalFiltration β hβ hE hsegMeas 0] live)
    (hstopCont : FCStoppedDriverContinuous E Γ U)
    (hthreshold : ∀ᵐ ω ∂P, ω ∈ live →
      U ω = fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β ω)
    (htrace : ∀ᵐ ω ∂P, ω ∈ live →
      IsGeneratingTrace (fun t => fcSegmentProcess E Γ U t ω)
        (fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β ω) (Γ ω))
    (Qc : ℝ≥0 → Ω → ℝ≥0)
    (hQcCont : ∀ ω, Continuous fun t => Qc t ω)
    (hQcMono : ∀ ω, Monotone fun t => Qc t ω)
    (hQc0 : ∀ ω, Qc 0 ω = 0)
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t))
    (hcapMeas : ∀ q D, MeasurableSet[fcSegmentNaturalFiltration β hβ hE hsegMeas q] D → ∀ t,
      MeasurableSet[𝓖 t] (D ∩ {ω | q ≤ Qc t ω}))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ live →
      (q : ℝ≥0∞) < fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β ω → ∃ t, q ≤ Qc t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ live → IsForceReg (fcSegmentProcess E Γ U)
      (geomLW (fcSegmentProcess E Γ U) (fcWordLeftPositions κ θ nL nR ρL ρR β))
      (geomRW (fcSegmentProcess E Γ U) (fcWordRightPositions κ θ nL nR ρL ρR β))
      (fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β) ω)
    (hSline : ∀ (ψ : TestOn upperHalfPlaneOpens) t,
      MeasurableSet[𝓖 t] (lineSafe Qc (fcSegmentProcess E Γ U)
        (fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β) (tsupport ψ) t))
    (hSball : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t,
      MeasurableSet[𝓖 t] (lineSafe Qc (fcSegmentProcess E Γ U)
        (fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β) (ballsK Fb) t))
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom)
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (Hc : Ω → DistOn upperHalfPlaneOpens) (hHc : Measurable Hc)
    (htransport : ∀ ω, Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω) =
      Exist.flowField 0 (θ * chiC κ) (Hc ω))
    (hint : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω) φ) (P.restrict live))
    (hseed : ∀ᵐ ω ∂P, ω ∈ live → ¬ ForceWord.ThresholdCondition ρL ρR 0
      (fcWordLeftPositions κ θ nL nR ρL ρR β ω) (fcWordRightPositions κ θ nL nR ρL ρR β ω))
    {S : Type} [mS : MeasurableSpace S] (X : Ω → S) (hX : Measurable X)
    (Hs : S → DistOn upperHalfPlaneOpens) (hHs : Measurable Hs)
    (Γs : S → ℝ≥0 → ℂ) (Us : S → ℝ≥0∞)
    (hΓsCont : ∀ s, ContinuousOn (Γs s) {t | (t : ℝ≥0∞) ≤ Us s})
    (Ws : ℝ≥0 → S → ℝ) (Ls : S → ℝ≥0∞)
    (hWsCont : ∀ s, ContinuousOn (fun t => Ws t s) {t | (t : ℝ≥0∞) < Ls s})
    (hHsState : ∀ ω, Hs (X ω) = Hc ω)
    (hΓState : ∀ ω, Γs (X ω) = Γ ω)
    (hUState : ∀ ω, Us (X ω) = U ω)
    (hWState : ∀ t ω, Ws t (X ω) = fcSegmentProcess E Γ U t ω)
    (hLState : ∀ ω, Ls (X ω) = fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β ω)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ}
    (hηc₁ : ∀ ω, Continuous (η₁ ω)) (hηc₂ : ∀ ω, Continuous (η₂ ω))
    (hηm₁ : ∀ t, Measurable fun ω => η₁ ω t) (hηm₂ : ∀ t, Measurable fun ω => η₂ ω t)
    {ℋlocal : Filtration ℝ≥0 mΩ}
    (hGlocal : ∀ t, 𝓖 t ≤ ℋlocal t) (hlocalLe : ∀ t, ℋlocal t ≤ mΩ)
    (hLocal : FCShUnionLineLocality (P := P) (F := live) (Qc := Qc) (h := h) (u₀ := u₀)
      (c := c) (W := fcSegmentProcess E Γ U)
      (ζ := fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β) ℋlocal η₁ η₂)
    {𝒢L : ℝ≥0 → MeasurableSpace Ω}
    (h𝓖L : ∀ t, 𝓖 t ≤ 𝒢L t) (h𝓖Lm : ∀ t, 𝒢L t ≤ mΩ)
    (Mline : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (B : ℕ → Set Ω)
    (hcover : ∀ t ω, ω ∈ live →
      (Qc t ω : ℝ≥0∞) < fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β ω → ∃ m, ω ∈ B m)
    (hbox : FCBoxKernelStatement (P := P) (F := live) (Qc := Qc) (c := c)
      (W := fcSegmentProcess E Γ U)
      (ζ := fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β) (h := h) 𝒢L Mline B)
    (hlineMean : FCLineMeanStatement (P := P) (κ := κ) (ρL := ρL) (ρR := ρR)
      (F := live) (Qc := Qc) (c := c) (W := fcSegmentProcess E Γ U)
      (VL := geomLW (fcSegmentProcess E Γ U) (fcWordLeftPositions κ θ nL nR ρL ρR β))
      (VR := geomRW (fcSegmentProcess E Γ U) (fcWordRightPositions κ θ nL nR ρL ρR β))
      (ζ := fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β) hc (θ * chiC κ) Mline)
    {Fcode : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFcode : IsCanonicalFlowCode κ θ Fcode)
    {Gcode : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hGcode : IsCanonicalDriverCode κ θ Gcode)
    {K : Kernel BoundaryWord S} [IsMarkovKernel K]
    (hjoint : (P.restrict live).map (fun ω => (β ω, X ω)) = (P.restrict live).map β ⊗ₘ K)
    (hgff : ∀ᵐ b ∂(P.restrict live).map β,
      b.IsSorted ∧ IsGFFWithBoundaryData (K b) Hs b.fn b.jumps) :
    ∀ᵐ ω ∂P, ω ∈ live →
      IsCodeMatch (Fcode ((β ω, 0), Hc ω)) (Γ ω) (U ω) := by
  classical
  let W : ℝ≥0 → Ω → ℝ := fcSegmentProcess E Γ U
  let ζ : Ω → ℝ≥0∞ := fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β
  let xL : Ω → Fin nL → ℝ := fcWordLeftPositions κ θ nL nR ρL ρR β
  let xR : Ω → Fin nR → ℝ := fcWordRightPositions κ θ nL nR ρL ρR β
  let 𝓗 : Filtration ℝ≥0 mΩ := fcSegmentNaturalFiltration β hβ hE hsegMeas
  let hWmeas : ∀ t, Measurable (W t) := by
    intro t
    change Measurable (fun ω => fcSegmentDriver E Γ U t ω)
    exact fcSegmentDriverMeasurable hE hsegMeas t
  have hW0 : ∀ ω, W 0 ω = 0 := fcSegmentDriver_zero hseg
  have hWcont : ∀ ω, Continuous fun t => W t ω := continuous_fcSegmentDriver hstopCont
  have hNatural : 𝓗 = fcDriverFiltration β W hβ hWmeas := by rfl
  have hFilAdapt := fcDriverFiltration_adapted β W hβ hWmeas
  have hWadapt : StronglyAdapted 𝓗 W := by
    rw [hNatural]
    exact hFilAdapt.2
  have hβadapt : Measurable[𝓗 0] β := by
    rw [hNatural]
    exact hFilAdapt.1
  have hxL0 : Measurable[𝓗 0] xL := by
    change Measurable[𝓗 0] (fun ω => FCDet.typeXL κ θ nL nR ρL ρR (β ω))
    exact (FCDet.measurable_typeXL κ θ nL nR ρL ρR).comp hβadapt
  have hxR0 : Measurable[𝓗 0] xR := by
    change Measurable[𝓗 0] (fun ω => FCDet.typeXR κ θ nL nR ρL ρR (β ω))
    exact (FCDet.measurable_typeXR κ θ nL nR ρL ρR).comp hβadapt
  have hker := fcLineKernel_of_boxwise (P := P) (F := live) (Qc := Qc) (c := c)
    (W := W) (ζ := ζ) (h := h) 𝒢L Mline B hcover hbox
  have hSafeLaw := hasSafeLaw_of_FCLineMean (P := P) (κ := κ) (ρL := ρL) (ρR := ρR)
    (𝓖 := 𝓖) (𝓗' := 𝓗) (F := live) hliveG0 (hc := hc) hdom hfwd hliftm hliftc
    (h := h) hhm (θ * chiC κ) hQcCont hQcMono hQc0 hQa hcapMeas hreach hreg hSline
    𝒢L h𝓖L h𝓖Lm Mline hker hlineMean
  have hSafeMembers := hasSafeMembers_of_FCShUnion (P := P) (nL := nL) (nR := nR)
    (𝓖 := 𝓖) (𝓗' := 𝓗) (F := live) (Qc := Qc) (W := W) (ζ := ζ) (VL := geomLW W xL)
    (VR := geomRW W xR) (h := h) hhm hu₀ hh0 hc hdom hfwd hliftm hliftc hlift
    (θ * chiC κ) (chiC κ) hQcCont hQcMono hQc0 hQa hcapMeas hreach hreg hSball η₁ η₂
    hηc₁ hηc₂ hηm₁ hηm₂ ℋlocal hGlocal hlocalLe hLocal.openComplement hLocal.markedLocal
    hLocal.chartDomain
  have hSafeLaw' : HasSafeLaw κ ρL ρR P 𝓗 live ζ W (geomLW W xL) (geomRW W xR)
      (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) := by
    simpa only [htransport] using hSafeLaw
  have hSafeMembers' : HasSafeMembers P 𝓗 live ζ W
      (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) := by
    simpa only [htransport] using hSafeMembers
  have hdriver := FCDet.ae_driverCodeMatch_of_hasSafeLaw_on (P := P) hκ
    (𝓗 := 𝓗) (M := live) hLiveNatural hβadapt hType hW0 hWcont hWadapt
    (Hc := Hc) hHc hint hseed hSafeLaw' hSafeMembers' hGcode
  have hdriverζ : ∀ᵐ ω ∂P, ω ∈ live →
      IsDriverCodeMatch (Gcode (β ω, Hc ω)) (fun t => W t ω) (ζ ω) := by
    filter_upwards [hdriver] with ω hdrv hωlive
    change IsDriverCodeMatch (Gcode (β ω, Hc ω)) (fun t => W t ω)
      (FCDet.thr ρL ρR W (fun ω => FCDet.typeXL κ θ nL nR ρL ρR (β ω))
        (fun ω => FCDet.typeXR κ θ nL nR ρL ρR (β ω)) ω)
    exact hdrv hωlive
  have hdriverState : ∀ᵐ ω ∂P, ω ∈ live →
      IsDriverCodeMatch (Gcode (β ω, Hs (X ω))) (fun t => Ws t (X ω)) (Ls (X ω)) := by
    filter_upwards [hdriverζ] with ω hdrv hωlive
    have hWfun : (fun t => Ws t (X ω)) = (fun t => W t ω) := funext fun t => by
      exact hWState t ω
    simpa only [hHsState ω, hWfun, hLState ω] using hdrv hωlive
  have hWzero : ∀ᵐ ω ∂P, ω ∈ live → Ws 0 (X ω) = 0 := by
    filter_upwards [ae_of_all _ fun ω => hW0 ω] with ω hzero hωlive
    rw [hWState 0 ω]
    exact hzero
  have htraceState : ∀ᵐ ω ∂P, ω ∈ live →
      IsGeneratingTrace (fun t => Ws t (X ω)) (Ls (X ω)) (Γs (X ω)) := by
    filter_upwards [htrace] with ω htr hωlive
    have hWfun : (fun t => Ws t (X ω)) = (fun t => W t ω) := funext fun t => by
      exact hWState t ω
    simpa only [hWfun, hLState ω, hΓState ω] using htr hωlive
  have hUL : ∀ᵐ ω ∂P, ω ∈ live → Us (X ω) = Ls (X ω) := by
    filter_upwards [hthreshold] with ω hω hωlive
    calc
      Us (X ω) = U ω := hUState ω
      _ = ζ ω := hω hωlive
      _ = Ls (X ω) := (hLState ω).symm
  have hbridge := InteractingSLE.Restart.ae_codeMatch_of_driverCodeMatch_of_generatingTrace
    (Ω := Ω) (C := BoundaryWord) (S := S) (P := P) (M := live) hliveMeas hβ hX
    (K := K) hjoint (w := id) measurable_id (H := Hs) hHs (Γ := Γs) (U := Us)
    hΓsCont (W := Ws) (L := Ls) hWsCont
    (κ := κ) (θ := θ) (F := Fcode) hFcode (G := Gcode) hGcode hgff hdriverState
    hWzero htraceState hUL
  filter_upwards [hbridge] with ω hmatch hωlive
  simpa only [hHsState ω, hΓState ω, hUState ω, id_eq] using hmatch hωlive

end Restart.FCPlumb

end InteractingSLE
