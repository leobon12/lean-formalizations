/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61WinFibreRef
import InteractingSLE.Spec.Sec5.Aux61KernelTop

/-!
# `RestartWindowNullQOn` from a fibre cover (R2) and reference avoidance (R5)

Packet PROVE-AUX61-WIN. Astra's follow-up 4 L258–L262 ("The reference's zero endpoint probability transfers by
positivity of the density. Disintegrate over the retained history and integrate; no measurable choice of fresh
couplings is necessary") and specification Aux. lemma 64's covering (p. 265: "Countably many rational choices of the
seed neighborhood, distance and radius cover the event").

* `IsAvoidingRef κ b̂ Ĵ I` (**piece R5**, the reference side): every stopped flow line of the reference word `b̂` from
  `0` (angle `0`), on every probability space, almost surely never visits a point of `I ⊆ ℝ` up to its clock. For
  Aux. lemma 64's word (`−λ | λ` with height `b ≥ λ − πχ` on the comparison interval) this is GB7a for a stopped flow
  line (PROVE-AUX61-R45); on the negative side, Aux. lemma 22's all-upper-high alternative in the `J`-chart (Astra
  L196–L213).
* `HasFibreCover μ E Ref` (**piece R2**, the conditional side, at one restart and one window code): the event `E` is
  covered by countably many measurable history pieces `A i`; on each, `μ(A i ∩ E) ≤ ∫_{A i} κ_i(x)(L_i) dμ(x)` for a
  kernel `κ_i` into a fibre space `S`, and for `μ`-a.e. `x ∈ A i` the fibre `κ_i(x)` carries a restart fibre with
  comparison and clock data (`RestartFibre`, `Comparison`, `Clock`) whose reference word is admissible (`Ref`) with
  avoided interval `I`, and `L_i` lies in the event "the fibre's path visits `I` before its clock".
* **`ae_not_of_hasFibreCover`**: `HasFibreCover` and R5 for the admissible words give `μ(E) = 0` (R3 and R4 are the
  proved fibre transfer `RestartFibre.Comparison.Clock.ae_of_stoppedFlowLine`).
* `RestartFibreCoverOn G Ref`: `HasFibreCover` for the window event `RestartWindowEvent` at every rational restart and
  window code, on the glued space of `Prop51G.GluedQ`, on the regime `G`;
* **`restartWindowNullQOn_of_cover`**: `RestartFibreCoverOn G Ref` and R5 for `Ref` give R23's named input
  `Aux61Kernel.RestartWindowNullQOn G`; **`fwdNoEastCrosscutTgtQOn_of_cover_smallGap`**: hence (E1) in target-component
  form for every angle pair (R23's wiring and its large-gap case).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Win

open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)

universe u

/-- **R5 for one reference word**: every stopped flow line of `b̂` from `0` (angle `0`), on every probability space,
almost surely never visits a point of `I` up to its clock. -/
def IsAvoidingRef (κ : ℝ) (bR : ℝ → ℝ) (JR : Finset ℝ) (I : Set ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (e : Ω → ℝ≥0∞),
    Restart.StoppedExtend.IsStoppedFlowLine κ bR JR 0 0 Q h η e →
      ∀ᵐ ω ∂Q, ∀ v : ℝ≥0, (v : ℝ≥0∞) ≤ e ω → ∀ y ∈ I, η ω v ≠ (y : ℂ)

/-- **The fibre cover of an event** (piece R2 at one restart and one window code): see the module docstring. -/
def HasFibreCover {X : Type u} [MeasurableSpace X] (μ : Measure X) (E : X → Prop)
    (Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop) : Prop :=
  ∃ (ι : Type) (_ : Countable ι) (A : ι → Set X) (S : Type u) (_ : MeasurableSpace S) (κ : ι → Kernel X S)
    (L : ι → Set S),
    (∀ i, MeasurableSet (A i)) ∧ (∀ᵐ x ∂μ, E x → ∃ i, x ∈ A i) ∧
    (∀ i, μ (A i ∩ {x | E x}) ≤ ∫⁻ x in A i, κ i x (L i) ∂μ) ∧
    ∀ i, ∀ᵐ x ∂μ, x ∈ A i → ∃ (D : RestartFibre S) (C : D.Comparison) (K : C.Clock) (I : Set ℝ),
      D.P = κ i x ∧ Ref D.κ C.bR C.JR I ∧
      ∀ ω ∈ L i, ∃ v : ℝ≥0, (v : ℝ≥0∞) ≤ D.e ω ∧ ∃ y ∈ I, K.Γ ω v = (y : ℂ)

/-- **A fibre cover and reference avoidance make the event null** (R2 + R3 + R4 + R5). -/
theorem ae_not_of_hasFibreCover {X : Type u} [MeasurableSpace X] {μ : Measure X} {E : X → Prop}
    {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop} (hcov : HasFibreCover μ E Ref)
    (hR5 : ∀ κ bR JR I, Ref κ bR JR I → IsAvoidingRef.{u} κ bR JR I) : ∀ᵐ x ∂μ, ¬ E x := by
  obtain ⟨ι, hι, A, S, mS, κ, L, hAm, hcover, hdis, hfib⟩ := hcov
  -- each fibre gives its piece of the future null
  have hnull : ∀ i, ∀ᵐ x ∂μ, x ∈ A i → κ i x (L i) = 0 := by
    intro i
    filter_upwards [hfib i] with x hx hxA
    obtain ⟨D, C, K, I, hP, hRef, hL⟩ := hx hxA
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

/-- **Piece R2 on the glued space** (Astra's follow-up 4 §§1.1–1.3 at one separated rational restart): on the glued
space of `Cond44Ref.Prop51QStatement` (the `GluedQ` binders), on the regime `G`, for every rational restart `t > 0`,
window code `c` and counterflow time `s > 0`, the window event has a fibre cover by restart fibres whose reference
words are admissible (`Ref`). -/
def RestartFibreCoverOn (G : ℝ → ℝ → ℝ → Prop) (Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop) : Prop :=
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
            HasFibreCover.{u} (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
                ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)))
              (fun p => RestartWindowEvent (Prop411Q.cfDrv p.2) s (fun u : ℝ => η p.1 u.toNNReal) t c) Ref

/-- **R23's named input from R2 (fibre cover) and R5 (reference avoidance)** (R3 and R4 proved: the fibre transfer). -/
theorem restartWindowNullQOn_of_cover {G : ℝ → ℝ → ℝ → Prop} {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop}
    (hcov : RestartFibreCoverOn.{u} G Ref) (hR5 : ∀ κ bR JR I, Ref κ bR JR I → IsAvoidingRef.{u} κ bR JR I) :
    RestartWindowNullQOn.{u} G := by
  intro t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  exact ae_not_of_hasFibreCover (hcov t c ht κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw
    k hk s hs) hR5

/-- **(E1) in target-component form for every angle pair** from R2 below the critical gap and R5 (R23's wiring, its
proved large-gap case, and the counterflow regularity from Part A). -/
theorem fwdNoEastCrosscutTgtQOn_of_cover_smallGap {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop}
    (hreg : Prop51Q.CfLineRegularQStatement.{u})
    (hcov : RestartFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) Ref)
    (hR5 : ∀ κ bR JR I, Ref κ bR JR I → IsAvoidingRef.{u} κ bR JR I) :
    FwdNoEastCrosscutTgtQOn.{u} fun _ _ _ => True :=
  fwdNoEastCrosscutTgtQOn_of_window_smallGap hreg (restartWindowNullQOn_of_cover hcov hR5)

end Glued

end InteractingSLE.Sec5.Aux61Win
