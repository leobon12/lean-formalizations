/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCM
import InteractingSLE.Spec.Restart.FlowStopIdentCMFill

/-!
# (L1) for Cameron–Martin shift pairs, restricted to buffers over one real interval (ruling R60)

Packet PROVE-G3SRC. Source: Lemma G3, hypothesis 4 and proof (supplement §7.3, `source/spec/p481-528.md` L290–L320,
pp. 492–493: "The closure of `U` meets the real line only in two disjoint intervals on which the respective canonical
seed germs just stated hold […] Each future is stopped on exiting `U₀` or on its first new old-boundary contact").

PROVE-L1-CM's named input `FlowStopIdentCM.FlowLineStopIdentCMStatement` allows a buffer `V` whose closure meets `ℝ`
in several components of the agreement set `O`. A flow line inside such a buffer can touch `ℝ` near another component
and swallow real points off `O`, where the two data differ; the frozen hull coupling says nothing about the field in a
swallowed pocket, so the Cameron–Martin tilt cannot be computed there (`planning/handoffs/PROVE-L1-CM.md` §4.2). The
source avoids this case by stopping each future at its first new boundary contact.

Here the buffer's real points lie in **one closed interval `[a, c] ⊆ O`** (a "per-seed buffer"). Every hull of the
stopped path then lies in the compact set `shiftHullSet V a c` (`FlowStopIdentCM.subset_shiftHullSet`), whose real
points lie over `O`, and the shift `T` is required to vanish on a neighbourhood `N` of it. This is the only geometry the
Cameron–Martin argument of G3's proof uses: the source of the shift is supported off every hull.

* `FlowLineStopIdentCMIntervalStatement` (**named input**): (L1) with the lifetime clause, for shift pairs, on the
  enlargement, for buffers over one interval;
* `flowLineStopIdentCMIntervalStatement_of_CM`: it is implied by PROVE-L1-CM's unrestricted input (so it is no
  stronger);
* `FlowLocalityShiftIntervalStatement`: flow locality for shift pairs and buffers over one interval;
* **`flowLocalityShiftIntervalStatement_of_CMInterval`** (and `…_through`): flow locality for such buffers from the
  restricted input, Aux. lemma 54 for Galmarino stops (or the WFS kernel target) and Theorems 1.2–1.3 (the proof of
  `FlowStopIdentCM.flowLocalityShiftStatement_of_CM`, run for the restricted buffers in both directions).

R43/R48: Theorems 1.2–1.3 are hypotheses; these results serve Theorem 1.5 (Lemma G3) only.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

namespace FlowStopIdentCM

open LawUnique StoppedExtend StoppedExtendWF FlowStopIdentG Exist.Staged ConverseBefore

/-! ### The restricted named input -/

/-- **Named input: (L1) with the lifetime clause, for Cameron–Martin shift pairs, on the enlargement, for buffers over
one real interval** (Lemma G3's proof, pp. 492–493, with its hypothesis 4; ruling R60). As
`FlowLineStopIdentCMStatement`, with the additional hypotheses that the real points of `closure V` lie in a closed
interval `[a, c] ⊆ O` and that the shift vanishes near the compact set `shiftHullSet V a c` (the filling of
`closure V ∩ ℍ̄` and `[a, c]`, which contains every hull of a path stopped on exiting `V`):
`shiftHullSet V a c ⊆ N`. -/
def FlowLineStopIdentCMIntervalStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b bR : ℝ → ℝ) (J Ĵ : Finset ℝ), IsPiecewiseConstantBoundaryData b J →
    IsPiecewiseConstantBoundaryData bR Ĵ → ∀ O : Set ℝ, IsOpen O → (∀ x ∈ O, b x = bR x) →
    ∀ N : Set ℂ, IsOpen N → (∀ z ∈ N, z.im = 0 → z.re ∈ O) →
    ∀ V : Set ℂ, IsOpen V → Bornology.IsBounded V → closure V ⊆ N →
    ∀ a c : ℝ, Icc a c ⊆ O → (∀ z ∈ closure V, z.im = 0 → z.re ∈ Icc a c) → shiftHullSet V a c ⊆ N →
    ∀ y θ : ℝ,
    ∀ {S : Type u} [MeasurableSpace S] (Q₀ Q : Measure S) [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q],
      Q₀ ≪ Q → Q ≪ Q₀ →
    ∀ (H₀ Ĥ : S → DistOn upperHalfPlaneOpens) (T : DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q₀ H₀ b J →
      IsGFFWithBoundaryData Q Ĥ bR Ĵ → (∀ x, Ĥ x = H₀ x + T) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ N → T φ = 0) →
    ∀ (Γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞), IsFlowLine κ b J y θ Q₀ H₀ Γ U →
      ∃ (ν : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure ν),
        IsStoppedFlowLineL κ bR Ĵ y θ V (Q.prod ν) (fun p => Ĥ p.1) (fun p => Γ p.1)
          fun p => RLC.exitTime V (Γ p.1) (U p.1)

/-- **The unrestricted input implies the restricted one** (it only drops hypotheses). -/
theorem flowLineStopIdentCMIntervalStatement_of_CM (hCM : FlowLineStopIdentCMStatement.{u}) :
    FlowLineStopIdentCMIntervalStatement.{u} := by
  intro κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN _a _c _haO _hVa _hsN y θ S _ Q₀ Q _ _ hQ₀Q hQQ₀
    H₀ Ĥ T hH₀ hĤ hsh hT0 Γ U hΓ
  exact hCM κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN y θ Q₀ Q hQ₀Q hQQ₀ H₀ Ĥ T hH₀ hĤ hsh hT0 Γ U hΓ

/-- **The stopped match for a shift pair, from the restricted input** (`ae_stopMatch_of_CM` for buffers over one
interval). -/
theorem ae_stopMatch_of_CMInterval (hCM : FlowLineStopIdentCMIntervalStatement.{u})
    (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → StoppedHullExtendGKStatement.{u} κ) (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b bR : ℝ → ℝ} {J Ĵ : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hbR : IsPiecewiseConstantBoundaryData bR Ĵ) {O : Set ℝ}
    (hO : IsOpen O) (hbO : ∀ x ∈ O, b x = bR x) {N : Set ℂ} (hN : IsOpen N) (hNO : ∀ z ∈ N, z.im = 0 → z.re ∈ O)
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hVN : closure V ⊆ N) {a c : ℝ} (haO : Icc a c ⊆ O)
    (hVa : ∀ z ∈ closure V, z.im = 0 → z.re ∈ Icc a c) (hsN : shiftHullSet V a c ⊆ N) (y θ : ℝ) {S : Type u}
    [MeasurableSpace S] {Q₀ Q : Measure S} [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q] (hQ₀Q : Q₀ ≪ Q)
    (hQQ₀ : Q ≪ Q₀) {H₀ Ĥ : S → DistOn upperHalfPlaneOpens} {T : DistOn upperHalfPlaneOpens}
    (hH₀ : IsGFFWithBoundaryData Q₀ H₀ b J) (hĤ : IsGFFWithBoundaryData Q Ĥ bR Ĵ) (hsh : ∀ x, Ĥ x = H₀ x + T)
    (hT0 : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ N → T φ = 0) {Γ : S → ℝ≥0 → ℂ} {U : S → ℝ≥0∞}
    (hΓ : IsFlowLine κ b J y θ Q₀ H₀ Γ U) :
    ∀ᵐ x ∂Q, IsStopMatch (flowDetCode h12p hκ bR Ĵ y θ (Ĥ x)) (Γ x) (RLC.exitTime V (Γ x) (U x)) := by
  obtain ⟨ν, hν, hL⟩ := hCM κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN a c haO hVa hsN y θ Q₀ Q hQ₀Q
    hQQ₀ H₀ Ĥ T hH₀ hĤ hsh hT0 Γ U hΓ
  have hfacts : ∀ᵐ p ∂(Q.prod ν), FlowPathFacts κ b J y θ (Γ p.1) (U p.1) :=
    ae_fst_of_ae (P₀ := ν) (q := fun x => FlowPathFacts κ b J y θ (Γ x) (U x)) (hQQ₀.ae_le (ae_flowPathFacts hΓ))
  have hG := isStoppedFlowLineG_of_L hV hfacts hL
  have m := hG.ae_stopMatch_of_extendGK (hext κ hκ hκ4) h13 hκ (isFlowDet_flowDetCode h12p hκ bR Ĵ y θ)
  exact ae_of_ae_fst (P₀ := ν)
    (q := fun x => IsStopMatch (flowDetCode h12p hκ bR Ĵ y θ (Ĥ x)) (Γ x) (RLC.exitTime V (Γ x) (U x))) m

/-! ### Flow locality for shift pairs, buffers over one interval -/

/-- **Flow-line locality for Cameron–Martin shift pairs and buffers over one real interval**
(`FlowLocalityShiftStatement` with the hypotheses of `FlowLineStopIdentCMIntervalStatement` on `V`). -/
def FlowLocalityShiftIntervalStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b bR : ℝ → ℝ) (J Ĵ : Finset ℝ), IsPiecewiseConstantBoundaryData b J →
    IsPiecewiseConstantBoundaryData bR Ĵ → ∀ O : Set ℝ, IsOpen O → (∀ x ∈ O, b x = bR x) →
    ∀ N : Set ℂ, IsOpen N → (∀ z ∈ N, z.im = 0 → z.re ∈ O) →
    ∀ V : Set ℂ, IsOpen V → Bornology.IsBounded V → closure V ⊆ N →
    ∀ a c : ℝ, Icc a c ⊆ O → (∀ z ∈ closure V, z.im = 0 → z.re ∈ Icc a c) → shiftHullSet V a c ⊆ N →
    ∀ y θ : ℝ,
    ∀ {S : Type u} [MeasurableSpace S] (Q₀ Q : Measure S) [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q],
      Q₀ ≪ Q → Q ≪ Q₀ →
    ∀ (H₀ Ĥ : S → DistOn upperHalfPlaneOpens) (T : DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q₀ H₀ b J →
      IsGFFWithBoundaryData Q Ĥ bR Ĵ → (∀ x, Ĥ x = H₀ x + T) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ N → T φ = 0) →
    ∀ (Γ α : S → ℝ≥0 → ℂ) (U ζ : S → ℝ≥0∞), IsFlowLine κ b J y θ Q₀ H₀ Γ U →
      IsFlowLine κ bR Ĵ y θ Q Ĥ α ζ → ∀ᵐ x ∂Q₀, RLC.StoppedAgree V (Γ x) (U x) (α x) (ζ x)

/-- **Flow locality for shift pairs and buffers over one interval, from the restricted input**, Aux. lemma 54 for
Galmarino stops and Theorems 1.2–1.3: the restricted input is applied to the pair and to the reversed pair
`(Ĥ, Q, bR) → (H₀, Q₀, b)` with the shift `−T` (the buffer hypotheses do not involve the data), and
`StoppedExtend.stoppedAgree_of_matches` concludes. -/
theorem flowLocalityShiftIntervalStatement_of_CMInterval (hCM : FlowLineStopIdentCMIntervalStatement.{u})
    (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → StoppedHullExtendGKStatement.{u} κ) (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : FlowLocalityShiftIntervalStatement.{u} := by
  intro κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN a c haO hVa hsN y θ S _ Q₀ Q _ _ hQ₀Q hQQ₀ H₀ Ĥ T
    hH₀ hĤ hsh hT0 Γ α U ζ hΓ hα
  have m1 := ae_stopMatch_of_CMInterval hCM hext h12p h13 hκ hκ4 hb hbR hO hbO hN hNO hV hVb hVN haO hVa hsN y θ
    hQ₀Q hQQ₀ hH₀ hĤ hsh hT0 hΓ
  have hsh' : ∀ x, H₀ x = Ĥ x + -T := fun x => by rw [hsh x, add_neg_cancel_right]
  have hT0' : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ N → (-T) φ = 0 := fun φ hφ => by
    show -(T φ) = 0
    rw [hT0 φ hφ, neg_zero]
  have m2 := ae_stopMatch_of_CMInterval hCM hext h12p h13 hκ hκ4 hbR hb hO (fun z hz => (hbO z hz).symm) hN hNO hV
    hVb hVN haO hVa hsN y θ hQQ₀ hQ₀Q hĤ hH₀ hsh' hT0' hα
  have c1 := isFlowDet_flowDetCode h12p hκ bR Ĵ y θ Q Ĥ α ζ hα
  have c2 := isFlowDet_flowDetCode h12p hκ b J y θ Q₀ H₀ Γ U hΓ
  filter_upwards [hQ₀Q.ae_le m1, hQ₀Q.ae_le c1, m2, c2] with z e1 e2 e3 e4
  exact stoppedAgree_of_matches e1 e2 e3 e4

/-- **Flow locality for shift pairs and buffers over one interval, from the restricted input, the WFS kernel target
and Theorems 1.2–1.3.** -/
theorem flowLocalityShiftIntervalStatement_of_CMInterval_through (hCM : FlowLineStopIdentCMIntervalStatement.{u})
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{u, u} κ) (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : FlowLocalityShiftIntervalStatement.{u} :=
  flowLocalityShiftIntervalStatement_of_CMInterval hCM (fun _ hκ hκ4 => WFS.stoppedHullExtendGKStatement_of_through hκ
    (hT _ hκ hκ4)) h12p h13

end FlowStopIdentCM

end Restart

end InteractingSLE
