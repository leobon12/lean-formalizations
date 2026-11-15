/- Provenance (PROVE-GEO-JORDAN, ruling R21): ported, through an intermediate copy, from an earlier mating-of-trees
formalization; only the module and namespace prefixes were changed (now `InteractingSLE.Foundations.Topology` and
`InteractingSLE.Foundations`), and declaration names are unchanged. -/
import InteractingSLE.Foundations.Topology.Jordan.StepB2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # Jordan curve theorem (Maehara's proof), part: main theorem

Ported from github.com/rkirov/jordan_pick (Apache-2.0, R. Kirov), commit
`b3c9b7cf7358bf81a077d78ad67e6e8247869ddd`, file `JordanPick/JordanCurve.lean`, lines 2549–2645.
Original proofs kept; changed only where our pin (Lean v4.34.0-rc2, mathlib a4c8ef0a) forces
it. Namespace `JordanCurve` → `InteractingSLE.Foundations.Jordan`; `private` dropped so that the original
file can be split into modules. Source: H. Maehara, *The Jordan curve theorem via the Brouwer
fixed point theorem*, Amer. Math. Monthly 91 (1984) 641–643. -/

namespace InteractingSLE.Foundations.Jordan

open Metric Set Function Bornology

/-- **Maehara Step B (geometric core).** Bounded components of `ℝ²∖J` are unique.
Reduced to the normalized version `step_B_normalized` via the farthest-pair
similarity `T`. -/
theorem step_B_bounded_unique (hbr : BrouwerFPT)
    {r : sphere (0 : Plane) 1 → Plane} (hcont : Continuous r) (hinj : Injective r) :
    ∀ x ∈ (range r)ᶜ, ∀ y ∈ (range r)ᶜ,
      IsBounded (connectedComponentIn (range r)ᶜ x) →
      IsBounded (connectedComponentIn (range r)ᶜ y) →
      connectedComponentIn (range r)ᶜ x = connectedComponentIn (range r)ᶜ y := by
  intro x hx y hy hxb hyb
  obtain ⟨a, ha, b, hb, hfar0, hab⟩ := exists_farthest_pair hcont hinj
  obtain ⟨T, hscale, hTa, hTb⟩ := exists_similarity hab
  have hdpos : 0 < dist a b := dist_pos.mpr hab
  have hcpos : (0:ℝ) < 2 / dist a b := by positivity
  set r' : sphere (0 : Plane) 1 → Plane := fun p => T (r p) with hr'
  have hr'cont : Continuous r' := T.continuous.comp hcont
  have hr'inj : Injective r' := T.injective.comp hinj
  have hrange : range r' = T '' range r := by
    rw [hr', show (fun p => T (r p)) = (T : Plane → Plane) ∘ r from rfl, Set.range_comp]
  have himg : (T '' range r)ᶜ = T '' (range r)ᶜ :=
    (Set.image_compl_eq (f := (T : Plane → Plane)) T.bijective).symm
  have hrc : (range r')ᶜ = (T : Plane → Plane) '' (range r)ᶜ := by rw [hrange, himg]
  have hm' : (!₂[(-1:ℝ), 0] : Plane) ∈ range r' := by
    rw [hrange, ← hTa]; exact mem_image_of_mem _ ha
  have hp' : (!₂[(1:ℝ), 0] : Plane) ∈ range r' := by
    rw [hrange, ← hTb]; exact mem_image_of_mem _ hb
  have hfar' : ∀ z ∈ range r', ∀ w ∈ range r', dist z w ≤ 2 := by
    rw [hrange]
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [hscale]
    calc 2 / dist a b * dist z w
        ≤ 2 / dist a b * dist a b :=
          mul_le_mul_of_nonneg_left (hfar0 z hz w hw) hcpos.le
      _ = 2 := by field_simp
  -- transport the two components forward by `T`
  have hTx : T x ∈ (range r')ᶜ := by rw [hrc]; exact mem_image_of_mem _ hx
  have hTy : T y ∈ (range r')ᶜ := by rw [hrc]; exact mem_image_of_mem _ hy
  have hccx : connectedComponentIn (range r')ᶜ (T x)
      = T '' connectedComponentIn (range r)ᶜ x := by
    rw [hrc]; exact (T.image_connectedComponentIn hx).symm
  have hccy : connectedComponentIn (range r')ᶜ (T y)
      = T '' connectedComponentIn (range r)ᶜ y := by
    rw [hrc]; exact (T.image_connectedComponentIn hy).symm
  have hTxb : IsBounded (connectedComponentIn (range r')ᶜ (T x)) := by
    rw [hccx]; exact (isBounded_image_scaling hcpos hscale _).mpr hxb
  have hTyb : IsBounded (connectedComponentIn (range r')ᶜ (T y)) := by
    rw [hccy]; exact (isBounded_image_scaling hcpos hscale _).mpr hyb
  have hEq := step_B_normalized hbr hr'cont hr'inj hm' hp' hfar'
    (T x) hTx (T y) hTy hTxb hTyb
  rw [hccx, hccy] at hEq
  exact Set.image_injective.mpr T.injective hEq

/-- The Jordan curve theorem reduced to Brouwer (Maehara). The eval `jordan_curve`
follows by discharging `BrouwerFPT`. Given the two geometric core facts — existence
(`step_A_exists_bounded`) and uniqueness (`step_B_bounded_unique`) of a bounded
component — together with the unique unbounded component (`exists_unbounded_component`,
`unbounded_component_unique`), the complement has exactly two components. -/
theorem jordan_curve_of_brouwer (hbr : BrouwerFPT)
    (r : sphere (0 : Plane) 1 → Plane)
    (hcont : Continuous r) (hinj : Injective r) :
    Nat.card (ConnectedComponents ((range r)ᶜ : Set Plane)) = 2 := by
  -- The unbounded component `x₀` and a bounded component `x₁`.
  obtain ⟨x₀, hx₀S, hx₀u⟩ := exists_unbounded_component r hcont
  obtain ⟨x₁, hx₁S, hx₁b⟩ := step_A_exists_bounded hbr hcont hinj
  set a : ↥((range r)ᶜ) := ⟨x₀, hx₀S⟩ with ha
  set b : ↥((range r)ᶜ) := ⟨x₁, hx₁S⟩ with hb
  -- The two components are distinct: one unbounded, one bounded.
  have hne : connectedComponentIn (range r)ᶜ x₀ ≠ connectedComponentIn (range r)ᶜ x₁ := by
    intro heq
    exact hx₀u (heq ▸ hx₁b)
  have hab : ConnectedComponents.mk a ≠ ConnectedComponents.mk b :=
    (Counting.connectedComponents_subtype_eq_iff hx₀S hx₁S).not.mpr hne
  -- Every component is either the bounded one (`= b`) or the unbounded one (`= a`).
  have hcover : ∀ z : ↥((range r)ᶜ),
      ConnectedComponents.mk z = ConnectedComponents.mk a
        ∨ ConnectedComponents.mk z = ConnectedComponents.mk b := by
    intro z
    by_cases hzb : IsBounded (connectedComponentIn (range r)ᶜ z.val)
    · right
      exact (Counting.connectedComponents_subtype_eq_iff z.2 hx₁S).mpr
        (step_B_bounded_unique hbr hcont hinj z.val z.2 x₁ hx₁S hzb hx₁b)
    · left
      exact (Counting.connectedComponents_subtype_eq_iff z.2 hx₀S).mpr
        (unbounded_component_unique r hcont hzb hx₀u)
  exact Counting.nat_card_connectedComponents_eq_two a b hab hcover

/-- **Jordan curve theorem** (the eval statement). -/
theorem jordan_curve
    (r : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2))
    (_hcont : Continuous r) (_hinj : Injective r) :
    Nat.card (ConnectedComponents ((range r)ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) = 2 := by
  -- Brouwer FPT for the plane, built from scratch in `JordanCurve.Brouwer`
  -- (circle non-nullhomotopy via Mathlib's covering-space lifting → no-retraction
  -- → disk Brouwer → convex-compact).
  have hbr : BrouwerFPT := Brouwer.brouwerFPT
  exact jordan_curve_of_brouwer hbr r _hcont _hinj


end InteractingSLE.Foundations.Jordan
