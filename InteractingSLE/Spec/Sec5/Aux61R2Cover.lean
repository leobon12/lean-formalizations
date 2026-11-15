/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R2Clock

/-!
# The restart-fibre cover with automatic tilt and clock (the remaining R2 target, corrected form)

Packet PROVE-AUX61-R2. Combines the corrected fibre (`Aux61R2Fibre`), its canonical Cameron–Martin data
(`Aux61R2TiltData`, R2e proved) and the clock from PROVE-AUX61-R45's reference clock (`Aux61R2Clock`, R2f up to
locality) into the cover notion that the remaining pieces have to produce: per fibre, a `RefFibre` (its kernel is
R2a + R2c relative to the reference word), a clock source started at `0` with the fibre's law and a reference clock
whose driver, clock and filtration are the fibre's (R2b; R45's `exists_referenceClock` builds it from the fibre's
path), and locality of the pre-clock hulls for the shifted field under the canonical tilt (R2f's last field).

* `RefFibre.canonTilt`: the canonical tilt `(E e^{−Λ})⁻¹ e^{−Λ} · P` (`= (tiltData he0).tilt`);
* `HasRefClockFibreCover μ E Ref`; **`hasRefFibreCover_of_clock`**;
* `RefClockFibreCoverOn G Ref` (same binders as `RefFibreCoverOn`); **`refFibreCoverOn_of_clock`**,
  **`restartWindowNullQOn_of_refClockCover`**, **`fwdNoEastCrosscutTgtQOn_of_refClockCover_smallGap`**.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61R2

open QuantumZipper (fwdHull)
open LQGMetric (DistOn)
open Sec7.PocketTraversal
open Aux61Win (IsAvoidingRef)

universe u

namespace RefFibre

variable {S : Type u} [mS : MeasurableSpace S] (D : RefFibre S)

/-- **The canonical tilt** `(E e^{−Λ})⁻¹ e^{−Λ} · P` of a fibre. -/
def canonTilt : Measure S :=
  D.P.withDensity fun ω => ENNReal.ofReal ((∫ ω', Real.exp (-D.Λ ω') ∂D.P)⁻¹ * Real.exp (-D.Λ ω))

theorem tiltData_tilt (he0 : ∀ᵐ ω ∂D.P, 0 < D.e ω) : (tiltData he0).tilt = D.canonTilt := rfl

/-- **Locality of the pre-clock hulls under the canonical tilt** (the last field of R2f): at every stop `τ < e` of the
fibre's filtration, the hull is a local set of the shifted field `h + (Fq − q)` under the canonical tilt. -/
def IsTiltLocal : Prop :=
  ∀ (τ : S → WithTop ℝ≥0) (_ : IsStoppingTime D.filt τ), (∀ᵐ ω ∂D.canonTilt, (τ ω : ℝ≥0∞) < D.e ω) →
    IsLocalSet (fun ω => fwdHull (Ito.rpath (D.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) D.chartField D.canonTilt

end RefFibre

/-- **The fibre cover with clocks from reference clocks** (the remaining R2 target, corrected form): as
`HasRefFibreCover`, but each fibre is a `RefFibre` on a clock source started at `0` with the fibre's law, whose
driver, clock and filtration are those of a reference clock of the fibre's reference word (angle `0`), with the
pre-clock hulls local under the canonical tilt; `L i` lies in the event "the source's path visits `I` before the
clock". -/
def HasRefClockFibreCover {X : Type u} [MeasurableSpace X] (μ : Measure X) (E : X → Prop)
    (Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop) : Prop :=
  ∃ (ι : Type) (_ : Countable ι) (A : ι → Set X) (S : Type u) (_ : MeasurableSpace S) (κ : ι → Kernel X S)
    (L : ι → Set S),
    (∀ i, MeasurableSet (A i)) ∧ (∀ᵐ x ∂μ, E x → ∃ i, x ∈ A i) ∧
    (∀ i, μ (A i ∩ {x | E x}) ≤ ∫⁻ x in A i, κ i x (L i) ∂μ) ∧
    ∀ i, ∀ᵐ x ∂μ, x ∈ A i → ∃ (D : RefFibre S) (CS : Aux61R45.ClockSource S) (V : Set ℂ)
      (RC : Aux61R45.ReferenceClock CS D.κ D.bR D.JR 0 V) (I : Set ℝ),
      D.P = κ i x ∧ CS.y = 0 ∧ D.P = CS.P ∧ D.W = RC.W ∧ D.e = RC.e ∧ D.filt = CS.driving ∧ D.IsTiltLocal ∧
      Ref D.κ D.bR D.JR I ∧
      ∀ ω ∈ L i, ∃ v : ℝ≥0, (v : ℝ≥0∞) ≤ D.e ω ∧ ∃ y ∈ I, CS.Γ ω v = (y : ℂ)

/-- **The tilt and the clock are automatic**: a cover with clocks from reference clocks is a `HasRefFibreCover`
(canonical tilt, `RefFibre.tiltData`; clock, `TiltData.clockOfReferenceClock`). -/
theorem hasRefFibreCover_of_clock {X : Type u} [MeasurableSpace X] {μ : Measure X} {E : X → Prop}
    {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop} (hcov : HasRefClockFibreCover μ E Ref) :
    HasRefFibreCover μ E Ref := by
  obtain ⟨ι, hι, A, S, mS, κ, L, hAm, hcover, hdis, hfib⟩ := hcov
  refine ⟨ι, hι, A, S, mS, κ, L, hAm, hcover, hdis, fun i => ?_⟩
  filter_upwards [hfib i] with x hx hxA
  obtain ⟨D, CS, V, RC, I, hPx, hy, hP, hW, he, hfilt, hloc, hRef, hL⟩ := hx hxA
  have he0 : ∀ᵐ ω ∂D.P, 0 < D.e ω := by
    rw [hP, he]
    exact (RC.announcing.2.2.1 0).mono fun _ h => lt_of_le_of_lt bot_le h
  let T := RefFibre.tiltData he0
  have hloc' : ∀ (τ : S → WithTop ℝ≥0) (_ : IsStoppingTime D.filt τ),
      (∀ᵐ ω ∂T.tilt, (τ ω : ℝ≥0∞) < D.e ω) →
      IsLocalSet (fun ω => fwdHull (Ito.rpath (D.W · ω)) ((τ ω).untopD 0 : ℝ≥0)) D.chartField T.tilt := hloc
  let K := T.clockOfReferenceClock CS hy RC hP hW he hfilt (RefFibre.isProbabilityMeasure_tilt he0) hloc'
  exact ⟨D, T, K, I, hPx, hRef, hL⟩

/-! ### On the glued space -/

section Glued

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique Cond44Ref Prop51Q CfAvoidLeftQ Prop51G Aux61Kernel
open QuantumZipper (chiC)

/-- **The remaining R2 target on the glued space** (corrected form, tilt and clock automatic): the window event has a
cover by restart fibres over admissible reference words with clocks from reference clocks. Same binders as
`Aux61Win.RestartFibreCoverOn`. -/
def RefClockFibreCoverOn (G : ℝ → ℝ → ℝ → Prop) (Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop) : Prop :=
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
            HasRefClockFibreCover.{u}
              (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
                ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)))
              (fun p => RestartWindowEvent (Prop411Q.cfDrv p.2) s (fun u : ℝ => η p.1 u.toNNReal) t c) Ref

theorem refFibreCoverOn_of_clock {G : ℝ → ℝ → ℝ → Prop} {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop}
    (hcov : RefClockFibreCoverOn.{u} G Ref) : RefFibreCoverOn.{u} G Ref := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  exact hasRefFibreCover_of_clock (hcov t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw
    k hk s hs)

/-- **R23's named input from the remaining R2 target and R5.** -/
theorem restartWindowNullQOn_of_refClockCover {G : ℝ → ℝ → ℝ → Prop}
    {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop} (hcov : RefClockFibreCoverOn.{u} G Ref)
    (hR5 : ∀ κ bR JR I, Ref κ bR JR I → IsAvoidingRef.{u} κ bR JR I) : RestartWindowNullQOn.{u} G :=
  restartWindowNullQOn_of_refCover (refFibreCoverOn_of_clock hcov) hR5

/-- **(E1) in target-component form for every angle pair** from the remaining R2 target below the critical gap and
R5 (with the counterflow regularity from Part A). -/
theorem fwdNoEastCrosscutTgtQOn_of_refClockCover_smallGap {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop}
    (hreg : Prop51Q.CfLineRegularQStatement.{u})
    (hcov : RefClockFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) Ref)
    (hR5 : ∀ κ bR JR I, Ref κ bR JR I → IsAvoidingRef.{u} κ bR JR I) :
    FwdNoEastCrosscutTgtQOn.{u} fun _ _ _ => True :=
  fwdNoEastCrosscutTgtQOn_of_refCover_smallGap hreg (refFibreCoverOn_of_clock hcov) hR5

end Glued

end InteractingSLE.Sec5.Aux61R2
