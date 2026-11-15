/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB7aCmp
import InteractingSLE.Spec.Supplement.G12Low

/-!
# Aux. lemmas 64 and 66 at all admissible boundary points at once

Packet PROVE-LEMMA76C. Specification §7.2, Aux. lemma 64 (an untouched right boundary interval of height
`b ≥ λ − πχ` is not a first new endpoint, p. 264) and Aux. lemma 66 (an admissible right junction, p. 266), in the
form Lemma 7.6's proof uses them (p. 269–270): after the restart in the chart of the joint domain, the forbidden side
is a *random* interval and junction of the chart datum, so the exclusion is needed simultaneously at every boundary
point that is admissible for the datum. For piecewise-constant data both exclusions are landed for one fixed interval
(Lemma GB7a, `Supp8.gb7aFlowStatement`) and one fixed point (Lemma G12, `g12FlowStatement`); here:

* `IsAdmissibleRight κ θ b J y`: `y ∉ J` with interval weight `cumWeightRight κ (b y + θχ) ≥ κ/2 − 2` (GB7a), or `y ∈ J`
  with junction weight `cumWeightRight κ (b(y⁺) + θχ) > κ/2 − 4` (G12, Aux. 66); `IsAdmissibleLeft` reflected;
* **`ae_avoid_admissible`**: almost surely the flow line visits no admissible point on either side of its seed, at any
  time up to and including its available lifetime (countably many rational intervals for GB7a, the finitely many
  jumps for G12);
* the heights of Lemma 7.6 are admissible: the right side `λ + (θ₂ − θ₁)χ` of the first path
  (`isAdmissibleRight_side`: `θ₁ ≤ θ₂ + π`, i.e. `b_* ≥ λ − πχ`) and the junction `R = c + θ₂χ` with `c + θ₁χ > −λ`
  (`cumWeightRight_junction`: `R > −λ − πχ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

open QuantumZipper (chiC)

universe u

namespace InteractingSLE

namespace Sec7

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

/-- **An admissible boundary point right of the seed** for the angle-`θ` flow line of data `(b, J)`: an interior point
of a constancy interval of interval weight `≥ κ/2 − 2` (Aux. 64 / GB7a), or a jump point of junction weight
`> κ/2 − 4` (Aux. 66 / G12). -/
def IsAdmissibleRight (κ θ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (y : ℝ) : Prop :=
  (y ∉ J ∧ κ / 2 - 2 ≤ Sec4.cumWeightRight κ (b y + θ * chiC κ)) ∨
    (y ∈ J ∧ κ / 2 - 4 < Sec4.cumWeightRight κ (rightLim b y + θ * chiC κ))

/-- **An admissible boundary point left of the seed** (the reflection of `IsAdmissibleRight`). -/
def IsAdmissibleLeft (κ θ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (y : ℝ) : Prop :=
  (y ∉ J ∧ κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (b y + θ * chiC κ)) ∨
    (y ∈ J ∧ κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim b y + θ * chiC κ))

/-! ### All admissible points at once -/

section Avoid

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {x θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- The rational intervals right of the seed on which GB7a applies. -/
def GoodRightRat (κ θ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (x : ℝ) (q : ℚ × ℚ) : Prop :=
  x ≤ q.1 ∧ (∀ z ∈ J, z ∉ Ioo (q.1 : ℝ) q.2) ∧ (q.1 : ℝ) < q.2 ∧
    κ / 2 - 2 ≤ Sec4.cumWeightRight κ (b (((q.1 : ℝ) + q.2) / 2) + θ * chiC κ)

/-- The rational intervals left of the seed on which GB7a applies. -/
def GoodLeftRat (κ θ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (x : ℝ) (q : ℚ × ℚ) : Prop :=
  (q.2 : ℝ) ≤ x ∧ (∀ z ∈ J, z ∉ Ioo (q.1 : ℝ) q.2) ∧ (q.1 : ℝ) < q.2 ∧
    κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (b (((q.1 : ℝ) + q.2) / 2) + θ * chiC κ)

theorem mid_mem_Ioo {a c : ℝ} (h : a < c) : (a + c) / 2 ∈ Ioo a c := ⟨by linarith, by linarith⟩

theorem ae_avoid_goodRightRat (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hh : IsGFFWithBoundaryData P h b J) (hη : IsFlowLine κ b J x θ P h η ζ) :
    ∀ᵐ ω ∂P, ∀ q : ℚ × ℚ, GoodRightRat κ θ b J x q →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → ∀ y ∈ Ioo (q.1 : ℝ) q.2, η ω t ≠ y := by
  refine ae_all_iff.2 fun q => ?_
  by_cases hq : GoodRightRat κ θ b J x q
  · obtain ⟨hxq, hJ, hlt, hw⟩ := hq
    have hv : ∀ y ∈ Ioo (q.1 : ℝ) q.2, y ∉ J → b y = b (((q.1 : ℝ) + q.2) / 2) := fun y hy _ =>
      Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb hJ (mid_mem_Ioo hlt) hy
    filter_upwards [(Supp8.gb7aFlowStatement κ hκ hκ4 b J hb x θ q.1 q.2 _ hv P h hh η ζ hη).1 hxq hw]
      with ω hω _ using hω
  · exact Eventually.of_forall fun ω h' => absurd h' hq

theorem ae_avoid_goodLeftRat (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hh : IsGFFWithBoundaryData P h b J) (hη : IsFlowLine κ b J x θ P h η ζ) :
    ∀ᵐ ω ∂P, ∀ q : ℚ × ℚ, GoodLeftRat κ θ b J x q →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → ∀ y ∈ Ioo (q.1 : ℝ) q.2, η ω t ≠ y := by
  refine ae_all_iff.2 fun q => ?_
  by_cases hq : GoodLeftRat κ θ b J x q
  · obtain ⟨hxq, hJ, hlt, hw⟩ := hq
    have hv : ∀ y ∈ Ioo (q.1 : ℝ) q.2, y ∉ J → b y = b (((q.1 : ℝ) + q.2) / 2) := fun y hy _ =>
      Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb hJ (mid_mem_Ioo hlt) hy
    filter_upwards [(Supp8.gb7aFlowStatement κ hκ hκ4 b J hb x θ q.1 q.2 _ hv P h hh η ζ hη).2 hxq hw]
      with ω hω _ using hω
  · exact Eventually.of_forall fun ω h' => absurd h' hq

theorem ae_avoid_jumps (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hh : IsGFFWithBoundaryData P h b J) (hη : IsFlowLine κ b J x θ P h η ζ) :
    ∀ᵐ ω ∂P, ∀ y ∈ J,
      (x < y → κ / 2 - 4 < Sec4.cumWeightRight κ (rightLim b y + θ * chiC κ) →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y) ∧
      (y < x → κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim b y + θ * chiC κ) →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y) := by
  refine (ae_ball_iff J.countable_toSet).2 fun y _ => ?_
  have hG := Supp7.g12FlowStatement κ hκ hκ4 b J hb x θ y P h hh η ζ hη
  by_cases hxy : x < y
  · by_cases hS : κ / 2 - 4 < Sec4.cumWeightRight κ (rightLim b y + θ * chiC κ)
    · filter_upwards [hG.1 hxy hS] with ω hω
      exact ⟨fun _ _ => hω, fun h' => absurd h' (not_lt.2 hxy.le)⟩
    · exact Eventually.of_forall fun ω => ⟨fun _ h' => absurd h' hS, fun h' => absurd h' (not_lt.2 hxy.le)⟩
  · by_cases hyx : y < x
    · by_cases hS : κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim b y + θ * chiC κ)
      · filter_upwards [hG.2 hyx hS] with ω hω
        exact ⟨fun h' => absurd h' hxy, fun _ _ => hω⟩
      · exact Eventually.of_forall fun ω => ⟨fun h' => absurd h' hxy, fun _ h' => absurd h' hS⟩
    · exact Eventually.of_forall fun ω => ⟨fun h' => absurd h' hxy, fun h' => absurd h' hyx⟩

/-- **Aux. lemmas 64 and 66 at every admissible point at once**: almost surely the angle-`θ` flow line of a GFF with
piecewise-constant data visits no admissible boundary point (right of its seed: `IsAdmissibleRight`; left:
`IsAdmissibleLeft`) at any time up to and including its available lifetime. -/
theorem ae_avoid_admissible (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hh : IsGFFWithBoundaryData P h b J) (hη : IsFlowLine κ b J x θ P h η ζ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → ∀ y : ℝ,
      (x < y → IsAdmissibleRight κ θ b J y → η ω t ≠ y) ∧ (y < x → IsAdmissibleLeft κ θ b J y → η ω t ≠ y) := by
  filter_upwards [ae_avoid_goodRightRat hκ hκ4 hb hh hη, ae_avoid_goodLeftRat hκ hκ4 hb hh hη,
    ae_avoid_jumps hκ hκ4 hb hh hη] with ω hR hL hJ t ht y
  refine ⟨fun hxy hy => ?_, fun hyx hy => ?_⟩
  · rcases hy with ⟨hyJ, hw⟩ | ⟨hyJ, hw⟩
    · obtain ⟨q₁, q₂, hyq, hqJ, hx1, -⟩ := Supp8.exists_rat_Ioo_avoid J hyJ hxy.ne
      have hlt : (q₁ : ℝ) < q₂ := hyq.1.trans hyq.2
      have hJ' : ∀ z ∈ J, z ∉ Ioo (q₁ : ℝ) q₂ := fun z hz hz' => hqJ z hz' hz
      have hbv : b y = b (((q₁ : ℝ) + q₂) / 2) :=
        Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb hJ' (mid_mem_Ioo hlt) hyq
      exact hR (q₁, q₂) ⟨hx1 hxy, hJ', hlt, by rw [← hbv]; exact hw⟩ t ht y hyq
    · exact (hJ y hyJ).1 hxy hw t ht
  · rcases hy with ⟨hyJ, hw⟩ | ⟨hyJ, hw⟩
    · obtain ⟨q₁, q₂, hyq, hqJ, -, hx2⟩ := Supp8.exists_rat_Ioo_avoid J hyJ hyx.ne'
      have hlt : (q₁ : ℝ) < q₂ := hyq.1.trans hyq.2
      have hJ' : ∀ z ∈ J, z ∉ Ioo (q₁ : ℝ) q₂ := fun z hz hz' => hqJ z hz' hz
      have hbv : b y = b (((q₁ : ℝ) + q₂) / 2) :=
        Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb hJ' (mid_mem_Ioo hlt) hyq
      exact hL (q₁, q₂) ⟨hx2 hyx, hJ', hlt, by rw [← hbv]; exact hw⟩ t ht y hyq
    · exact (hJ y hyJ).2 hyx hw t ht

end Avoid

/-! ### The heights of Lemma 7.6 are admissible -/

/-- **The exposed right side of the first path is admissible for the second** (Aux. 64's hypothesis
`b_* = λ + (θ₂ − θ₁)χ ≥ λ − πχ`, p. 269): if `θ₁ ≤ θ₂ + π` then the interval weight of the height `λ − θ₁χ` for the
angle-`θ₂` path is at least `κ/2 − 2`. -/
theorem cumWeightRight_side {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ ≤ θ₂ + Real.pi) :
    κ / 2 - 2 ≤ Sec4.cumWeightRight κ ((sleLambda κ - θ₁ * chiC κ) + θ₂ * chiC κ) := by
  unfold Sec4.cumWeightRight
  have hl := Sec4.sleLambda_pos hκ
  have hc := Sec4.chiC_pos hκ hκ4
  have hpi := Sec4.pi_mul_chiC hκ
  have h1 : -Real.pi * chiC κ ≤ (θ₂ - θ₁) * chiC κ := mul_le_mul_of_nonneg_right (by linarith) hc.le
  rw [le_sub_iff_add_le, le_div_iff₀ hl]
  nlinarith

/-- **The junction of the first path's right side is admissible for the second** (Aux. 66's hypothesis
`R = c + θ₂χ > −λ − πχ`, p. 269): if the first path continued past its rightmost swallowed real point (`c + θ₁χ > −λ`,
its swallowed right force sum exceeds `−2`) and `θ₁ < θ₂ + π`, the junction weight of `c` for the angle-`θ₂` path
exceeds `κ/2 − 4`. -/
theorem cumWeightRight_junction {κ θ₁ θ₂ c : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂ + Real.pi)
    (hcont : -sleLambda κ < c + θ₁ * chiC κ) :
    κ / 2 - 4 < Sec4.cumWeightRight κ (c + θ₂ * chiC κ) := by
  unfold Sec4.cumWeightRight
  have hl := Sec4.sleLambda_pos hκ
  have hc := Sec4.chiC_pos hκ hκ4
  have hpi := Sec4.pi_mul_chiC hκ
  have h1 : -Real.pi * chiC κ < (θ₂ - θ₁) * chiC κ := mul_lt_mul_of_pos_right (by linarith) hc
  rw [lt_sub_iff_add_lt, lt_div_iff₀ hl]
  nlinarith

/-- The side height `λ − θ₁χ` off the jumps is an admissible right point for the angle-`θ₂` path. -/
theorem isAdmissibleRight_side {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ ≤ θ₂ + Real.pi)
    {b : ℝ → ℝ} {J : Finset ℝ} {y : ℝ} (hyJ : y ∉ J) (hby : b y = sleLambda κ - θ₁ * chiC κ) :
    IsAdmissibleRight κ θ₂ b J y :=
  Or.inl ⟨hyJ, by rw [hby]; exact cumWeightRight_side hκ hκ4 hθ⟩

/-- A junction `y ∈ J` with right value `c`, `c + θ₁χ > −λ`, is an admissible right point for the angle-`θ₂`
path. -/
theorem isAdmissibleRight_junction {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂ + Real.pi)
    {b : ℝ → ℝ} {J : Finset ℝ} {y : ℝ} (hyJ : y ∈ J) (hcont : -sleLambda κ < rightLim b y + θ₁ * chiC κ) :
    IsAdmissibleRight κ θ₂ b J y :=
  Or.inr ⟨hyJ, cumWeightRight_junction hκ hκ4 hθ hcont⟩

end Sec7

end InteractingSLE
