/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R2Fibre
import InteractingSLE.Spec.Sec5.Aux61WinGlue

/-!
# `RestartWindowNullQOn` from a cover by restart fibres over the reference word (R2, corrected form)

Packet PROVE-AUX61-R2. The corrected form of PROVE-AUX61-WIN's glue (`Aux61WinGlue`): the fibres are
`Aux61R2.RefFibre`s (base mean = the reference word's canonical mean, so that `q = M − M^c` vanishes at the seed and
on the comparison interval; see `Aux61R2Fibre` and `Aux61R2Obstruction` for why WIN's `RestartFibre` cannot carry the
window event). Astra's follow-up 4 L258–L262: "The reference's zero endpoint probability transfers by positivity of
the density. Disintegrate over the retained history and integrate; no measurable choice of fresh couplings is
necessary."

* `RefFibre.TiltData.Clock` — the clock and locality data of the tilted fibre (the fields of
  `Aux61R45.ReferenceSetting` other than `kernel`, which is `TiltData.isCouplingCharFun_tilt`);
  `Clock.toReferenceSetting`, `Clock.exists_isStoppedFlowLine` (R45's converse), **`Clock.ae_of_stoppedFlowLine`**
  (every a.s. property of the reference's stopped flow lines holds a.s. for the fibre's path under the fibre's law);
* `HasRefFibreCover μ E Ref`: `Aux61Win.HasFibreCover` with `RefFibre`s; **`ae_not_of_hasRefFibreCover`**;
* `RefFibreCoverOn G Ref`: the cover of the window event on the glued space of `Prop51G.GluedQ`;
  **`restartWindowNullQOn_of_refCover`**, **`fwdNoEastCrosscutTgtQOn_of_refCover_smallGap`**: R23's named input and
  (E1) in target-component form from the corrected R2 and R5 (`Aux61Win.IsAvoidingRef`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61R2

open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open Sec7.PocketTraversal
open Aux61Win (IsAvoidingRef)

universe u

namespace RefFibre

variable {S : Type u} [mS : MeasurableSpace S] {D : RefFibre S}

namespace TiltData

/-- **The clock and locality data of the tilted fibre** (the fields of `Aux61R45.ReferenceSetting` other than its
kernel). -/
structure Clock (T : D.TiltData) where
  Γ : S → ℝ≥0 → ℂ
  tilt_prob : IsProbabilityMeasure T.tilt
  rightContinuous : D.filt.IsRightContinuous
  adapted : StronglyAdapted D.filt D.W
  stopping : IsStoppingTime D.filt fun ω => (D.e ω : WithTop ℝ≥0)
  nullSets : ∀ A, MeasurableSet A → T.tilt A = 0 → MeasurableSet[D.filt 0] A
  Tn : ℕ → S → ℝ≥0
  announcing : Coupling.IsAnnouncingSeq D.filt T.tilt D.e Tn
  killed : IsMeasurableKilledDriving D.W (geomLW D.W fun _ => flowLineXL D.bR D.JR 0)
    (geomRW D.W fun _ => flowLineXR D.bR D.JR 0) D.e
  driving_le : drivingFiltration T.tilt killed ≤ D.filt
  σ : ℕ → S → ℝ≥0
  referenceAnnouncing : Coupling.IsAnnouncingSeq (drivingFiltration T.tilt killed) T.tilt D.e σ
  threshold : ∀ᵐ ω ∂T.tilt, D.e ω ≤ MartChar.thresholdTime
    (flowLineRhoL D.κ D.bR D.JR 0 0) (flowLineRhoR D.κ D.bR D.JR 0 0) (D.W · ω)
    (fun i t => geomLW D.W (fun _ => flowLineXL D.bR D.JR 0) i t ω)
    (fun j t => geomRW D.W (fun _ => flowLineXR D.bR D.JR 0) j t ω)
  locality : ∀ (τ : S → WithTop ℝ≥0) (_ : IsStoppingTime D.filt τ),
    (∀ᵐ ω ∂T.tilt, (τ ω : ℝ≥0∞) < D.e ω) →
    IsLocalSet (fun ω => fwdHull (Ito.rpath (D.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) D.chartField T.tilt
  trace : ∀ᵐ ω ∂T.tilt, IsGeneratingTrace (D.W · ω) (D.e ω) (fun t => Γ ω t - 0)

variable {T : D.TiltData}

/-- **The tilted fibre as a reference setting** (the input of PROVE-AUX61-R45's general-mean converse). -/
def Clock.toReferenceSetting (K : T.Clock) : Aux61R45.ReferenceSetting S where
  κ := D.κ
  κ_pos := D.κ_pos
  b := D.bR
  J := D.JR
  y := 0
  θ := 0
  P := T.tilt
  prob := K.tilt_prob
  field := D.chartField
  chartField := D.chartField
  measurable_field := D.measurable_chartField
  translate := fun ω => Aux61Win.RestartFibre.Comparison.isTranslateAddConst_zero D.κ (D.chartField ω)
  Γ := K.Γ
  e := D.e
  W := D.W
  zero := D.zero
  continuous := D.continuous
  filt := D.filt
  rightContinuous := K.rightContinuous
  adapted := K.adapted
  stopping := K.stopping
  nullSets := K.nullSets
  T := K.Tn
  announcing := K.announcing
  killed := K.killed
  driving_le := K.driving_le
  σ := K.σ
  referenceAnnouncing := K.referenceAnnouncing
  threshold := K.threshold
  kernel := T.isCouplingCharFun_tilt
  locality := K.locality
  trace := K.trace

/-- **R4 for the tilted fibre**: on an independent Brownian enlargement, the path stopped at `e` is a stopped flow
line of the reference word from `0`. -/
theorem Clock.exists_isStoppedFlowLine (K : T.Clock) :
    ∃ (ν : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure ν),
      Restart.StoppedExtend.IsStoppedFlowLine D.κ D.bR D.JR 0 0 (T.tilt.prod ν)
        (fun p => D.chartField p.1) (fun p => K.Γ p.1) (fun p => D.e p.1) :=
  K.toReferenceSetting.exists_isStoppedFlowLine

/-- **Transfer of almost-sure path properties from the stopped reference to the fibre**: if every stopped flow line of
the reference word, on every probability space, almost surely has the property `Φ` of its path and clock, then the
fibre's path and clock have `Φ` almost surely under the fibre's own law. -/
theorem Clock.ae_of_stoppedFlowLine (K : T.Clock) {Φ : (ℝ≥0 → ℂ) → ℝ≥0∞ → Prop}
    (hΦ : ∀ {Ω : Type u} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (e : Ω → ℝ≥0∞),
      Restart.StoppedExtend.IsStoppedFlowLine D.κ D.bR D.JR 0 0 Q h η e → ∀ᵐ ω ∂Q, Φ (η ω) (e ω)) :
    ∀ᵐ ω ∂D.P, Φ (K.Γ ω) (D.e ω) := by
  let _ := K.tilt_prob
  obtain ⟨ν, hν, hst⟩ := K.exists_isStoppedFlowLine
  have hprod := hΦ (T.tilt.prod ν) _ _ _ hst
  have h2 : ∀ᵐ ω ∂T.tilt, ∀ᵐ x ∂ν, Φ (K.Γ ω) (D.e ω) := Measure.ae_ae_of_ae_prod hprod
  have h3 : ∀ᵐ ω ∂T.tilt, Φ (K.Γ ω) (D.e ω) := h2.mono fun ω hω => by
    obtain ⟨_, hx⟩ := hω.exists
    exact hx
  exact T.tilt_equivalent.2.ae_le h3

end TiltData

end RefFibre

/-! ### The fibre cover -/

/-- **The fibre cover of an event by restart fibres over reference words** (piece R2 at one restart and one window
code, corrected form): countably many measurable history pieces `A i`; on each, `μ(A i ∩ E) ≤ ∫_{A i} κ_i(x)(L_i)`
for a kernel `κ_i` into a fibre space `S`; for `μ`-a.e. `x ∈ A i` the fibre `κ_i(x)` carries a `RefFibre` with tilt
and clock data whose reference word is admissible (`Ref`) with avoided set `I`, and `L_i` lies in the event "the
fibre's path visits `I` before its clock". -/
def HasRefFibreCover {X : Type u} [MeasurableSpace X] (μ : Measure X) (E : X → Prop)
    (Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop) : Prop :=
  ∃ (ι : Type) (_ : Countable ι) (A : ι → Set X) (S : Type u) (_ : MeasurableSpace S) (κ : ι → Kernel X S)
    (L : ι → Set S),
    (∀ i, MeasurableSet (A i)) ∧ (∀ᵐ x ∂μ, E x → ∃ i, x ∈ A i) ∧
    (∀ i, μ (A i ∩ {x | E x}) ≤ ∫⁻ x in A i, κ i x (L i) ∂μ) ∧
    ∀ i, ∀ᵐ x ∂μ, x ∈ A i → ∃ (D : RefFibre S) (T : D.TiltData) (K : T.Clock) (I : Set ℝ),
      D.P = κ i x ∧ Ref D.κ D.bR D.JR I ∧
      ∀ ω ∈ L i, ∃ v : ℝ≥0, (v : ℝ≥0∞) ≤ D.e ω ∧ ∃ y ∈ I, K.Γ ω v = (y : ℂ)

/-- **A fibre cover and reference avoidance make the event null** (corrected R2 + R3 + R4 + R5). -/
theorem ae_not_of_hasRefFibreCover {X : Type u} [MeasurableSpace X] {μ : Measure X} {E : X → Prop}
    {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop} (hcov : HasRefFibreCover μ E Ref)
    (hR5 : ∀ κ bR JR I, Ref κ bR JR I → IsAvoidingRef.{u} κ bR JR I) : ∀ᵐ x ∂μ, ¬ E x := by
  obtain ⟨ι, hι, A, S, mS, κ, L, hAm, hcover, hdis, hfib⟩ := hcov
  have hnull : ∀ i, ∀ᵐ x ∂μ, x ∈ A i → κ i x (L i) = 0 := by
    intro i
    filter_upwards [hfib i] with x hx hxA
    obtain ⟨D, T, K, I, hP, hRef, hL⟩ := hx hxA
    have hav := K.ae_of_stoppedFlowLine
      (Φ := fun Γ e => ∀ v : ℝ≥0, (v : ℝ≥0∞) ≤ e → ∀ y ∈ I, Γ v ≠ (y : ℂ))
      (fun Q _ h η e hst => hR5 _ _ _ _ hRef Q h η e hst)
    rw [← hP]
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hav)
    obtain ⟨v, hv, y, hy, hΓ⟩ := hL ω hω
    simp only [Set.mem_ofPred_eq, not_forall, not_not]
    exact ⟨v, hv, y, hy, hΓ⟩
  have hpiece : ∀ i, μ (A i ∩ {x | E x}) = 0 := fun i => by
    refine le_antisymm ((hdis i).trans (le_of_eq ?_)) zero_le
    have h0 : ∀ᵐ x ∂μ.restrict (A i), κ i x (L i) = 0 := (ae_restrict_iff' (hAm i)).2 (hnull i)
    exact (lintegral_congr_ae h0).trans lintegral_zero
  rw [ae_iff]
  simp only [not_not]
  have hsub : {x | E x} ⊆ (⋃ i, A i ∩ {x | E x}) ∪ {x | ¬ (E x → ∃ i, x ∈ A i)} := fun x hx => by
    by_cases h : ∃ i, x ∈ A i
    · obtain ⟨i, hi⟩ := h
      exact Or.inl (mem_iUnion.2 ⟨i, hi, hx⟩)
    · exact Or.inr fun h' => h (h' hx)
  exact measure_mono_null hsub (measure_union_null (measure_iUnion_null hpiece) (ae_iff.1 hcover))

/-! ### The glued space of Proposition 5.1 in the chart `Q` -/

section Glued

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique Cond44Ref Prop51Q CfAvoidLeftQ Prop51G Aux61Kernel
open QuantumZipper (chiC)

/-- **Piece R2 on the glued space, corrected form** (Astra's follow-up 4 §§1.1–1.3 at one separated rational
restart): on the glued space of `Cond44Ref.Prop51QStatement` (the `GluedQ` binders), on the regime `G`, for every
rational restart `t > 0`, window code `c` and counterflow time `s > 0`, the window event has a cover by restart fibres
over admissible reference words (`Ref`). Same binders as `Aux61Win.RestartFibreCoverOn`. -/
def RefFibreCoverOn (G : ℝ → ℝ → ℝ → Prop) (Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop) : Prop :=
  ∀ (t : ℚ) (c : WinCode), 0 < t →
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ a b θ₁ θ₂ : ℝ, θ₁ < θ₂ → G κ θ₁ θ₂ →
    sleLambda κ - θ₁ * chiC κ ≤ b → sleLambda κ - Real.pi * chiC κ + θ₂ * chiC κ ≤ a →
    ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
      (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ)),
      IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P h η ζ →
      ∀ {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
        IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ →
        P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂ →
        ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
          P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k →
          ∀ s : ℚ, 0 < s →
            HasRefFibreCover.{u} (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
                ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)))
              (fun p => RestartWindowEvent (Prop411Q.cfDrv p.2) s (fun u : ℝ => η p.1 u.toNNReal) t c) Ref

/-- **R23's named input from the corrected R2 (fibre cover) and R5 (reference avoidance).** -/
theorem restartWindowNullQOn_of_refCover {G : ℝ → ℝ → ℝ → Prop} {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop}
    (hcov : RefFibreCoverOn.{u} G Ref) (hR5 : ∀ κ bR JR I, Ref κ bR JR I → IsAvoidingRef.{u} κ bR JR I) :
    RestartWindowNullQOn.{u} G := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  exact ae_not_of_hasRefFibreCover (hcov t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw
    k hk s hs) hR5

/-- **(E1) in target-component form for every angle pair** from the corrected R2 below the critical gap and R5 (R23's
wiring, its proved large-gap case, and the counterflow regularity from Part A). -/
theorem fwdNoEastCrosscutTgtQOn_of_refCover_smallGap {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop}
    (hreg : Prop51Q.CfLineRegularQStatement.{u})
    (hcov : RefFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) Ref)
    (hR5 : ∀ κ bR JR I, Ref κ bR JR I → IsAvoidingRef.{u} κ bR JR I) :
    FwdNoEastCrosscutTgtQOn.{u} fun _ _ _ => True :=
  fwdNoEastCrosscutTgtQOn_of_window_smallGap hreg (restartWindowNullQOn_of_refCover hcov hR5)

end Glued

end InteractingSLE.Sec5.Aux61R2
