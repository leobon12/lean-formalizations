/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB7aCmp
import InteractingSLE.Spec.Supplement.G12Low
import InteractingSLE.Spec.Supplement.RLCGJump
import InteractingSLE.Spec.Restart.FCK2BdryVisit
import InteractingSLE.Spec.Exist.StagedLawData
import InteractingSLE.Spec.Supplement.S10Main
import InteractingSLE.Spec.Theorem15Inputs

/-!
# Real contacts of the live lower-angle path at critical angles: only the pocket corner remains

Packet PROVE-RC-HIT (ruling R124 (a)). Setting of `RealContact.G7GB7aFirstHitRealStatement`: `η₁` the angle-`θ₁`
flow line from `x₁`, `η₂` the angle-`θ₂` flow line from `x₂ ≤ x₁`, one field, `0 < κ < 4`, and the weight hypothesis
(7.12D.1) `κ/2 − 2 ≤ cumWeightRight κ (−λ − θ₁χ + θ₂χ)`, i.e. `(θ₂ − θ₁)χ ≥ λκ/2`.

At a real point `q` both paths see the same original boundary datum `b`, and the angle gap shifts the two flow-line
weights by `D = (θ₂ − θ₁)χ/λ ≥ κ/2`. This file proves, **without any conditional law**, that a real common point
`η₁(x) = η₂(t) = q` with `x < ζ₁` (the first path still available) and `t > 0` forces `t = ζ₂` and `q < x₂`:

* `q ≥ x₁`, `q > x₂`: the live first path has the right incident bound `−λ < b(q⁺) + θ₁χ`
  (`Restart.FCPlumb.ae_live_real_incident_bounds`), so the second path's outward right cumulative weight there exceeds
  `D − 2 ≥ κ/2 − 2`. GB7a (`Supp8.gb7aFlowStatement`, off the jumps) or G12 (`Supp7.g12FlowStatement`, at a jump)
  excludes every visit of `q` by `η₂`, terminal endpoint included;
* `x₂ < q < x₁`: a jump of `b` is never visited by the live first path (`RLC.jumpVisitStatement`); off the jumps GB7a
  for `η₁` (left) gives `b(q) + θ₁χ > λ(1 − κ/2)`, so the second path's right weight is `> D − κ/2 ≥ 0 ≥ κ/2 − 2`,
  and GB7a for `η₂` excludes the visit;
* `q = x₂`: for `x₂ < x₁` G12 for `η₁` at the fixed point `x₂` (its left weight exceeds `−2 > κ/2 − 4` by the incident
  bound); for `x₂ = x₁` Aux. lemma 25 (`η₂` injective on `[0, ζ₂]`) gives `t = 0`;
* `q < x₂`: as before `q` is no jump and `b(q) + θ₁χ > λ(1 − κ/2)`, so `b(q) + θ₂χ > λ`; a live visit of `η₂` would
  have the left incident bound `b(q) + θ₂χ < λ`. Hence `t = ζ₂`.

The remaining configuration (`q < x₂`, `t = ζ₂`) is the **pocket corner**: `η₁` touches `ℝ` at `q` left of `x₂`,
closing a bounded pocket of `ℍ \ η₁([0, x])` in which `η₂` is trapped, and `η₂` ends exactly at the corner `q`.

## Main results

* `realContact_cases` (pathwise) and **`ae_realContact_cases`** (almost surely, closed): every real common point
  `η₁ x = η₂ t = q` with `x < ζ₁`, `0 < t ≤ ζ₂` has `t = ζ₂` and `q < x₂`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

open QuantumZipper (chiC)

universe u

namespace InteractingSLE.RealContact.Hit

open PiecewiseConstantBoundaryData (leftLim rightLim)

/-! ### Weight arithmetic -/

/-- (7.12D.1) as an angle gap: `κ/2 − 2 ≤ cumWeightRight κ (−λ − θ₁χ + θ₂χ)` gives `λκ/2 ≤ (θ₂ − θ₁)χ`. -/
theorem gap_ge {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ)
    (hD : κ / 2 - 2 ≤ Sec4.cumWeightRight κ ((-sleLambda κ - θ₁ * chiC κ) + θ₂ * chiC κ)) :
    sleLambda κ * (κ / 2) ≤ (θ₂ - θ₁) * chiC κ := by
  have hl := Sec4.sleLambda_pos hκ
  unfold Sec4.cumWeightRight at hD
  have h1 : κ / 2 - 1 ≤ ((-sleLambda κ - θ₁ * chiC κ) + θ₂ * chiC κ) / sleLambda κ := by linarith
  rw [le_div_iff₀ hl] at h1
  have e : (κ / 2 - 1) * sleLambda κ = sleLambda κ * (κ / 2) - sleLambda κ := by ring
  have e' : (θ₂ - θ₁) * chiC κ = θ₂ * chiC κ - θ₁ * chiC κ := by ring
  linarith

/-- A right incident bound `−λ < v + θ₁χ` of the first path gives the second path a right weight `> κ/2 − 2`. -/
theorem cumWeightRight_snd_gt {κ θ₁ θ₂ v : ℝ} (hκ : 0 < κ)
    (hgap : sleLambda κ * (κ / 2) ≤ (θ₂ - θ₁) * chiC κ) (hv : -sleLambda κ < v + θ₁ * chiC κ) :
    κ / 2 - 2 < Sec4.cumWeightRight κ (v + θ₂ * chiC κ) := by
  have hl := Sec4.sleLambda_pos hκ
  unfold Sec4.cumWeightRight
  rw [lt_sub_iff_add_lt, lt_div_iff₀ hl]
  have e : (κ / 2 - 2 + 1) * sleLambda κ = sleLambda κ * (κ / 2) - sleLambda κ := by ring
  have e' : (θ₂ - θ₁) * chiC κ = θ₂ * chiC κ - θ₁ * chiC κ := by ring
  linarith

/-- A left weight of the first path below `κ/2 − 2` (GB7a) gives `v > λ(1 − κ/2)`. -/
theorem lt_of_not_le_cumWeightLeft {κ v : ℝ} (hκ : 0 < κ) (h : ¬ κ / 2 - 2 ≤ Sec4.cumWeightLeft κ v) :
    sleLambda κ * (1 - κ / 2) < v := by
  have hl := Sec4.sleLambda_pos hκ
  unfold Sec4.cumWeightLeft at h
  have h := not_le.1 h
  have h1 : -v / sleLambda κ < κ / 2 - 1 := by linarith
  rw [div_lt_iff₀ hl] at h1
  have e : (κ / 2 - 1) * sleLambda κ = -(sleLambda κ * (1 - κ / 2)) := by ring
  linarith

/-- From `v + θ₁χ > λ(1 − κ/2)` the second path's right weight is at least `κ/2 − 2` (it exceeds `D − κ/2 ≥ 0`). -/
theorem cumWeightRight_snd_ge_of_left {κ θ₁ θ₂ v : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hgap : sleLambda κ * (κ / 2) ≤ (θ₂ - θ₁) * chiC κ)
    (hv : sleLambda κ * (1 - κ / 2) < v + θ₁ * chiC κ) :
    κ / 2 - 2 ≤ Sec4.cumWeightRight κ (v + θ₂ * chiC κ) := by
  have hl := Sec4.sleLambda_pos hκ
  unfold Sec4.cumWeightRight
  rw [le_sub_iff_add_le, le_div_iff₀ hl]
  have e : (κ / 2 - 2 + 1) * sleLambda κ = sleLambda κ * (κ / 2) - sleLambda κ := by ring
  have e' : (θ₂ - θ₁) * chiC κ = θ₂ * chiC κ - θ₁ * chiC κ := by ring
  have e'' : sleLambda κ * (1 - κ / 2) = sleLambda κ - sleLambda κ * (κ / 2) := by ring
  have hk : sleLambda κ * (κ / 2) < sleLambda κ * 2 := mul_lt_mul_of_pos_left (by linarith) hl
  linarith

/-- From `v + θ₁χ > λ(1 − κ/2)` the second path's height `v + θ₂χ` exceeds `λ` (left weight `< −2`). -/
theorem lambda_lt_snd_of_left {κ θ₁ θ₂ v : ℝ} (hgap : sleLambda κ * (κ / 2) ≤ (θ₂ - θ₁) * chiC κ)
    (hv : sleLambda κ * (1 - κ / 2) < v + θ₁ * chiC κ) : sleLambda κ < v + θ₂ * chiC κ := by
  have e' : (θ₂ - θ₁) * chiC κ = θ₂ * chiC κ - θ₁ * chiC κ := by ring
  have e'' : sleLambda κ * (1 - κ / 2) = sleLambda κ - sleLambda κ * (κ / 2) := by ring
  linarith

/-! ### The case analysis at one outcome -/

section Pathwise

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}

/-- **A real contact of the live first path at a positive second time is a pocket corner** (pathwise). From the
almost-sure facts at one outcome (seeds, Aux. lemma 25 for the second path, the live incident bounds of both paths,
GB7a for both paths, no live jump visit of the first path, G12 for the second path at the jumps and for the first path
at the second seed): a real common point `η₁ x = η₂ t = q` with `x < ζ₁`, `0 < t ≤ ζ₂` has `t = ζ₂` and `q < x₂`. -/
theorem realContact_cases (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hx : x₂ ≤ x₁) (hgap : sleLambda κ * (κ / 2) ≤ (θ₂ - θ₁) * chiC κ)
    (h0₁ : η₁ 0 = x₁) (h0₂ : η₂ 0 = x₂) (hinj₂ : InjOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂})
    (hinc₁ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₁ → ∀ y : ℝ, η₁ t = y →
      (y ≤ x₁ → leftLim b y + θ₁ * chiC κ < sleLambda κ) ∧
        (x₁ ≤ y → -sleLambda κ < rightLim b y + θ₁ * chiC κ))
    (hinc₂ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₂ → ∀ y : ℝ, η₂ t = y →
      (y ≤ x₂ → leftLim b y + θ₂ * chiC κ < sleLambda κ) ∧
        (x₂ ≤ y → -sleLambda κ < rightLim b y + θ₂ * chiC κ))
    (hGB₁ : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₁ → ∀ y ∉ jumps,
      (x₁ < y → κ / 2 - 2 ≤ Sec4.cumWeightRight κ (b y + θ₁ * chiC κ) → η₁ t ≠ y) ∧
        (y < x₁ → κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (b y + θ₁ * chiC κ) → η₁ t ≠ y))
    (hGB₂ : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ → ∀ y ∉ jumps,
      (x₂ < y → κ / 2 - 2 ≤ Sec4.cumWeightRight κ (b y + θ₂ * chiC κ) → η₂ t ≠ y) ∧
        (y < x₂ → κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (b y + θ₂ * chiC κ) → η₂ t ≠ y))
    (hJ₁ : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ₁ → ∀ y ∈ jumps, y ≠ x₁ → η₁ t ≠ y)
    (hG₂ : ∀ y ∈ jumps, x₂ < y → κ / 2 - 4 < Sec4.cumWeightRight κ (rightLim b y + θ₂ * chiC κ) →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ → η₂ t ≠ y)
    (hG₁ : x₂ < x₁ → κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim b x₂ + θ₁ * chiC κ) →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₁ → η₁ t ≠ x₂)
    {x t : ℝ≥0} {q : ℝ} (hxζ : (x : ℝ≥0∞) < ζ₁) (htζ : (t : ℝ≥0∞) ≤ ζ₂) (ht0 : 0 < t)
    (h₁ : η₁ x = q) (h₂ : η₂ t = q) :
    (t : ℝ≥0∞) = ζ₂ ∧ q < x₂ := by
  obtain ⟨hL₁, hR₁⟩ := hinc₁ x hxζ q h₁
  -- the first time is positive at a point other than the first seed
  have hpos : q ≠ x₁ → 0 < x := by
    intro hq
    rcases eq_or_ne x 0 with h | h
    · subst h
      rw [h0₁] at h₁
      exact absurd (Complex.ofReal_injective h₁) hq.symm
    · exact pos_iff_ne_zero.2 h
  -- off the jumps, left of the first seed: GB7a for the first path bounds its height from below
  have hleft : q < x₁ → q ∉ jumps → sleLambda κ * (1 - κ / 2) < b q + θ₁ * chiC κ := fun hq hqJ =>
    lt_of_not_le_cumWeightLeft hκ fun hw => (hGB₁ x hxζ.le q hqJ).2 hq hw h₁
  rcases lt_trichotomy q x₂ with hq | hq | hq
  · -- `q < x₂`: the pocket corner
    have hq₁ : q < x₁ := hq.trans_le hx
    by_cases hqJ : q ∈ jumps
    · exact absurd h₁ (hJ₁ x (hpos hq₁.ne) hxζ q hqJ hq₁.ne)
    · refine ⟨?_, hq⟩
      by_contra hne
      have hbad := (hinc₂ t (lt_of_le_of_ne htζ hne) q h₂).1 hq.le
      rw [Exist.StagedLaw.leftLim_eq_of_notMem hb hqJ] at hbad
      exact absurd hbad (not_lt.2 (lambda_lt_snd_of_left hgap (hleft hq₁ hqJ)).le)
  · -- `q = x₂`
    subst hq
    exfalso
    rcases hx.lt_or_eq with hlt | heq
    · have hw : κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim b q + θ₁ * chiC κ) := by
        have := (Restart.FCPlumb.cumWeightLeft_gt_iff hκ).2 (hL₁ hx)
        linarith
      exact hG₁ hlt hw x hxζ.le h₁
    · have h0 : (0 : ℝ≥0) ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ₂} := by
        show ((0 : ℝ≥0) : ℝ≥0∞) ≤ ζ₂
        simp
      have := hinj₂ htζ h0 (h₂.trans h0₂.symm)
      exact ht0.ne' this
  · -- `x₂ < q`
    exfalso
    by_cases hq₁ : x₁ ≤ q
    · have hw := cumWeightRight_snd_gt hκ hgap (hR₁ hq₁)
      by_cases hqJ : q ∈ jumps
      · exact hG₂ q hqJ hq (by linarith) t htζ h₂
      · rw [Exist.StagedLaw.rightLim_eq_of_notMem hb hqJ] at hw
        exact (hGB₂ t htζ q hqJ).1 hq hw.le h₂
    · have hq₁' : q < x₁ := lt_of_not_ge hq₁
      by_cases hqJ : q ∈ jumps
      · exact hJ₁ x (hpos hq₁'.ne) hxζ q hqJ hq₁'.ne h₁
      · exact (hGB₂ t htζ q hqJ).1 hq (cumWeightRight_snd_ge_of_left hκ hκ4 hgap (hleft hq₁' hqJ)) h₂

end Pathwise

/-! ### Almost surely -/

section Random

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
  {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **Real contacts of the live first path are pocket corners, almost surely** (closed). In the setting of
`RealContact.G7GB7aFirstHitRealStatement`, almost surely every real common point `η₁ x = η₂ t = q` with `x < ζ₁` and
`0 < t ≤ ζ₂` has `t = ζ₂` (the second path ends there) and `q < x₂` (left of the second seed). -/
theorem ae_realContact_cases (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hx : x₂ ≤ x₁)
    (hD : κ / 2 - 2 ≤ Sec4.cumWeightRight κ ((-sleLambda κ - θ₁ * chiC κ) + θ₂ * chiC κ))
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ∀ (x t : ℝ≥0) (q : ℝ), (x : ℝ≥0∞) < ζ₁ ω → (t : ℝ≥0∞) ≤ ζ₂ ω → 0 < t →
      η₁ ω x = q → η₂ ω t = q → (t : ℝ≥0∞) = ζ₂ ω ∧ q < x₂ := by
  have hgap := gap_ge hκ hD
  -- G12 for the second path at the jumps of `b`
  have hG₂ : ∀ᵐ ω ∂P, ∀ y ∈ jumps, x₂ < y →
      κ / 2 - 4 < Sec4.cumWeightRight κ (rightLim b y + θ₂ * chiC κ) →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → η₂ ω t ≠ y := by
    refine (Filter.eventually_all_finset jumps).2 fun y _ => ?_
    by_cases hc : x₂ < y ∧ κ / 2 - 4 < Sec4.cumWeightRight κ (rightLim b y + θ₂ * chiC κ)
    · filter_upwards [(Supp7.g12FlowStatement κ hκ hκ4 b jumps hb x₂ θ₂ y P h hh η₂ ζ₂ hη₂).1 hc.1 hc.2]
        with ω hω _ _ using hω
    · exact Filter.Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hc
  -- G12 for the first path at the second seed
  have hG₁ : ∀ᵐ ω ∂P, x₂ < x₁ → κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim b x₂ + θ₁ * chiC κ) →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₁ ω → η₁ ω t ≠ x₂ := by
    by_cases hc : x₂ < x₁ ∧ κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim b x₂ + θ₁ * chiC κ)
    · filter_upwards [(Supp7.g12FlowStatement κ hκ hκ4 b jumps hb x₁ θ₁ x₂ P h hh η₁ ζ₁ hη₁).2 hc.1 hc.2]
        with ω hω _ _ using hω
    · exact Filter.Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hc
  filter_upwards [Supp10.ae_apply_zero_of_isFlowLine hη₁, Supp10.ae_apply_zero_of_isFlowLine hη₂,
    Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂,
    Restart.FCPlumb.ae_live_real_incident_bounds hκ hκ4 hb hh hη₁,
    Restart.FCPlumb.ae_live_real_incident_bounds hκ hκ4 hb hh hη₂,
    Supp8.GB7aFlowStatement.ae_forall Supp8.gb7aFlowStatement hκ hκ4 hb hh hη₁,
    Supp8.GB7aFlowStatement.ae_forall Supp8.gb7aFlowStatement hκ hκ4 hb hh hη₂,
    RLC.jumpVisitStatement κ hκ hκ4 b jumps hb x₁ θ₁ P h hh η₁ ζ₁ hη₁, hG₂, hG₁]
    with ω h0₁ h0₂ hinj₂ hinc₁ hinc₂ hGB₁ hGB₂ hJ₁ hG₂ω hG₁ω
  intro x t q hxζ htζ ht0 h₁ h₂
  exact realContact_cases hκ hκ4 hb hx hgap h0₁ h0₂ hinj₂ hinc₁ hinc₂ hGB₁ hGB₂ hJ₁ hG₂ω hG₁ω hxζ htζ ht0 h₁ h₂

end Random

end InteractingSLE.RealContact.Hit
