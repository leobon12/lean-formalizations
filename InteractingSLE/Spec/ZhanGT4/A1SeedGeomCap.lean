/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1SeedGeomOrder
import InteractingSLE.Spec.ZhanGT4.DualSeedCloseMarks
import InteractingSLE.Spec.ZhanGT4.DualSeedRemoteD10

/-!
# Zhan's A.1 (R80): `SeedImageGeometry` for A22's seeded capacity coordinates

Packet PROVE-A1-SEEDGEOM. A22 defines the actual capacity coordinates of a seeded image path by the inverse of the
quadratic capacity clock (`seedCapacityDriver`, `seedCapacityForce`, `seedCapacityHorizon`, `DualSeedCloseCoords`) and
proves their force equations for seeds (`seedCapacitySeed_integrated`). PROVE-A1-FAMILY's `FamilyRect.ofRect` needs the
full deterministic geometry `SeedImageGeometry` of these coordinates (its `hgeom`); "the ordering and seed conditions
are not yet proved for seeded coordinates".

Here the geometry is proved from own-time data: for every image index `k` (the other tip `0`, the marks `m.succ`) the
own-time image force equation `X_t = X_0 + ∫₀ᵗ 2A₁²/(X − A₀)` (A22: `SeedData.integrated_other_tip`,
`SeedData.integrated_image_marks`, `SeedData.capacity_image_seed`), the positive-time sides of the image forces with
respect to the image driver `A₀`, and the initial order. The capacity substitution (`OwnData.capacity_force_equation`)
transports the equations; the order fields come from `A1SeedGeom.seedImageGeometry_of_forces` (non-crossing of
Loewner force points).

## Main results

* `seedCapacityTime_pos`: positive capacity times come from positive own times;
* **`seedCapacityForce_integrated`**: the force equation and reciprocal-gap integrability of every capacity force point
  up to the horizon, from the own-time image equation of its index;
* **`seedImageGeometry_seedCapacity`**: `SeedImageGeometry` of the seeded capacity coordinates, for any identification
  `e : Fin nL ⊕ Fin nR ≃ Fin (n + 1)` of the image word;
* `ownImageEq_otherTip`, `ownImageEq_mark`: the own-time image equations of the other tip and of the marks from A22's
  inputs.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4.A1SeedGeom

open Sec2

/-! ### Own-time image equations from A22's inputs -/

section Own

variable {n : ℕ} (s : SeedData n) {T : ℝ}

/-- **The other tip's own-time image equation** (index `0`), from its forward solution and its protected gap
(A22's `SeedData.integrated_other_tip`). -/
theorem ownImageEq_otherTip {A : Set ℂ} (h : OwnData s.W A s.φ T s.a s.W') {v₀ : ℝ → ℂ}
    (hv₀ : QuantumZipper.IsForwardSol s.W' s.ζ₀ (s.a T) v₀) (hne : ∀ u ∈ Icc (0 : ℝ) T, s.A20 u ≠ s.A 0 u) :
    ∀ t ∈ Icc (0 : ℝ) T,
      IntervalIntegrable (fun u => 2 * s.A 1 u ^ 2 / (s.imageForce u 0 - s.A 0 u)) volume 0 t ∧
        s.imageForce t 0 = s.imageForce 0 0 +
          ∫ u in (0 : ℝ)..t, 2 * s.A 1 u ^ 2 / (s.imageForce u 0 - s.A 0 u) := by
  intro t ht
  simpa only [SeedData.imageForce, Fin.cases_zero] using s.integrated_other_tip h hv₀ hne ht

/-- **A mark's own-time image equation** (index `m.succ`), from the positive-time rate and the entrance integrability
(A22's `SeedData.integrated_image_marks`, `SeedData.ImageEntranceIntegrable`). -/
theorem ownImageEq_mark (hc : ∀ m, ContinuousOn (fun t => s.B0 t m) (Icc 0 T))
    (hd : ∀ m u, u ∈ Ioc (0 : ℝ) T →
      HasDerivWithinAt (fun t => s.B0 t m) (2 * s.A 1 u ^ 2 / (s.B0 u m - s.A 0 u)) (Ioc 0 T) u)
    (hi : s.ImageEntranceIntegrable T) (m : Fin n) :
    ∀ t ∈ Icc (0 : ℝ) T,
      IntervalIntegrable (fun u => 2 * s.A 1 u ^ 2 / (s.imageForce u m.succ - s.A 0 u)) volume 0 t ∧
        s.imageForce t m.succ = s.imageForce 0 m.succ +
          ∫ u in (0 : ℝ)..t, 2 * s.A 1 u ^ 2 / (s.imageForce u m.succ - s.A 0 u) := by
  intro t ht
  simp only [SeedData.imageForce, Fin.cases_succ]
  exact ⟨hi m t ht, s.integrated_image_marks hc hd hi m t ht⟩

/-- **A seed mark's own-time image equation** (index `m.succ`), from A22's protected seed geometry
(`SeedData.imageEntranceIntegrable_of_seed`, `SeedData.integrated_image_seed`). -/
theorem ownImageEq_seed {A : Set ℂ} {r L₀ : ℝ} {I : ℝ → Set ℝ} (h : OwnData s.W A s.φ T s.a s.W') (hr : 0 < r)
    (hI : ∀ t ∈ Icc (0 : ℝ) T, Convex ℝ (I t)) (hWI : ∀ t ∈ Icc (0 : ℝ) T, s.W t ∈ I t)
    (hVI : ∀ t ∈ Icc (0 : ℝ) T, ∀ m, s.V m t ∈ I t)
    (hclear : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ I t, Disjoint (Metric.ball (x : ℂ) r)
      ((fun z => QuantumZipper.fwdMap s.W t z + s.W t) '' A))
    (hb : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ I t, deriv (s.F 0 t) x ∈ Icc (Real.exp (-L₀)) (Real.exp L₀))
    (hseed : ∀ m, IsSeedCoordinate s.W (s.V m) T) (m : Fin n) :
    ∀ t ∈ Icc (0 : ℝ) T,
      IntervalIntegrable (fun u => 2 * s.A 1 u ^ 2 / (s.imageForce u m.succ - s.A 0 u)) volume 0 t ∧
        s.imageForce t m.succ = s.imageForce 0 m.succ +
          ∫ u in (0 : ℝ)..t, 2 * s.A 1 u ^ 2 / (s.imageForce u m.succ - s.A 0 u) := by
  intro t ht
  simp only [SeedData.imageForce, Fin.cases_succ]
  exact ⟨s.imageEntranceIntegrable_of_seed h hr hI hWI hVI hclear hb hseed m t ht,
    s.integrated_image_seed h hr hI hWI hVI hclear hb hseed m t ht⟩

/-- **The own-time map is strictly increasing on a protected real interval**: a derivative in
`[e^{−L₀}, e^{L₀}]` on a convex `I` (A22's protected bound `hb`) forces differentiability and strict monotonicity. -/
theorem strictMonoOn_F {t L₀ : ℝ} {I : Set ℝ} (hI : Convex ℝ I)
    (hb : ∀ x ∈ I, deriv (s.F 0 t) x ∈ Icc (Real.exp (-L₀)) (Real.exp L₀)) : StrictMonoOn (s.F 0 t) I := by
  have hpos (x : ℝ) (hx : x ∈ I) : 0 < deriv (s.F 0 t) x := (Real.exp_pos _).trans_le (hb x hx).1
  have hd (x : ℝ) (hx : x ∈ I) : DifferentiableAt ℝ (s.F 0 t) x :=
    differentiableAt_of_deriv_ne_zero (hpos x hx).ne'
  exact strictMonoOn_of_deriv_pos hI (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    fun x hx => hpos x (interior_subset hx)

/-- The image driver is the own-time map at the driver: `A₀(t) = F_t(W_t)`. -/
theorem A_zero_eq_F (t : ℝ) : s.A 0 t = s.F 0 t (s.W t) := rfl

/-- **A mark left of the driver has its image left of the image driver** (protected interval). -/
theorem B0_lt_A0 {t L₀ : ℝ} {I : Set ℝ} (hI : Convex ℝ I)
    (hb : ∀ x ∈ I, deriv (s.F 0 t) x ∈ Icc (Real.exp (-L₀)) (Real.exp L₀)) (hW : s.W t ∈ I) {m : Fin n}
    (hV : s.V m t ∈ I) (hlt : s.V m t < s.W t) : s.B0 t m < s.A 0 t :=
  (strictMonoOn_F s hI hb) hV hW hlt

/-- **A mark right of the driver has its image right of the image driver** (protected interval). -/
theorem A0_lt_B0 {t L₀ : ℝ} {I : Set ℝ} (hI : Convex ℝ I)
    (hb : ∀ x ∈ I, deriv (s.F 0 t) x ∈ Icc (Real.exp (-L₀)) (Real.exp L₀)) (hW : s.W t ∈ I) {m : Fin n}
    (hV : s.V m t ∈ I) (hlt : s.W t < s.V m t) : s.A 0 t < s.B0 t m :=
  (strictMonoOn_F s hI hb) hW hV hlt

/-- A continuous nonvanishing function on a preconnected set keeps the sign it has at one point. -/
theorem pos_of_isPreconnected {f : ℝ → ℝ} {D : Set ℝ} (hD : IsPreconnected D) (hf : ContinuousOn f D)
    (hne : ∀ x ∈ D, f x ≠ 0) {a : ℝ} (ha : a ∈ D) (hfa : 0 < f a) : ∀ x ∈ D, 0 < f x := by
  intro x hx
  by_contra hcon
  obtain ⟨r, hr, hr0⟩ := hD.intermediate_value hx ha hf ⟨not_lt.1 hcon, hfa.le⟩
  exact hne r hr hr0

/-- **The other tip keeps its side of the image driver** on `[0, T]`: its protected gap never vanishes (A22's
`hsep`), so its sign is the initial one. -/
theorem A0_lt_A20 {A : Set ℂ} (h : OwnData s.W A s.φ T s.a s.W') (hc : ContinuousOn s.A20 (Icc 0 T))
    (hne : ∀ u ∈ Icc (0 : ℝ) T, s.A 0 u ≠ s.A20 u) (h0 : s.A 0 0 < s.A20 0) :
    ∀ t ∈ Icc (0 : ℝ) T, s.A 0 t < s.A20 t := by
  have hT : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, h.pos.le⟩
  intro t ht
  have := pos_of_isPreconnected isPreconnected_Icc (hc.sub (h.continuousOn_frzA 0))
    (fun u hu => sub_ne_zero.2 (hne u hu).symm) hT (sub_pos.2 h0) t ht
  exact sub_pos.1 this

/-- The mirror of `A0_lt_A20`: an other tip initially left of the image driver stays left of it. -/
theorem A20_lt_A0 {A : Set ℂ} (h : OwnData s.W A s.φ T s.a s.W') (hc : ContinuousOn s.A20 (Icc 0 T))
    (hne : ∀ u ∈ Icc (0 : ℝ) T, s.A 0 u ≠ s.A20 u) (h0 : s.A20 0 < s.A 0 0) :
    ∀ t ∈ Icc (0 : ℝ) T, s.A20 t < s.A 0 t := by
  have hT : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, h.pos.le⟩
  intro t ht
  have := pos_of_isPreconnected isPreconnected_Icc ((h.continuousOn_frzA 0).sub hc)
    (fun u hu => sub_ne_zero.2 (hne u hu)) hT (sub_pos.2 h0) t ht
  exact sub_pos.1 this

end Own

/-! ### The capacity coordinates -/

section Capacity

variable {Ω : Type*} {n nL nR : ℕ} {d : Ω → SeedData n} {S : Ω → ℝ≥0} {A : Ω → Set ℂ} {c : ℝ}
  (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W')
  (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d S) ω))
  (hCs : ∀ ω, StrictMono (seedQuadClock (seedCapacityCoeff d S) ω))
  (hc : 0 < c) (hlb : ∀ ω r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) ω r)

include hown hCc hCs hc hlb

/-- **Positive capacity times come from positive own times** (the capacity clock is strictly increasing from `0`). -/
theorem seedCapacityTime_pos (ω : Ω) {u : ℝ≥0} (hu0 : 0 < u) (hu : u ≤ seedCapacityHorizon d S ω) :
    0 < seedCapacityTime d S u ω := by
  obtain ⟨-, hat⟩ := seedCapacityTime_spec hown hCc hCs hc hlb ω hu
  rcases eq_or_lt_of_le (zero_le (a := seedCapacityTime d S u ω)) with h | h
  · rw [← h, NNReal.coe_zero, (hown ω).a0] at hat
    exact absurd hat (by exact_mod_cast hu0.ne)
  · exact h

/-- **The capacity force equation of every image index up to the horizon**, from its own-time image equation
(capacity substitution, `OwnData.capacity_force_equation`). Seeds need no positive lower bound on their gap. -/
theorem seedCapacityForce_integrated (ω : Ω) (k : Fin (n + 1))
    (himg : ∀ t ∈ Icc (0 : ℝ) (S ω),
      IntervalIntegrable (fun u => 2 * (d ω).A 1 u ^ 2 / ((d ω).imageForce u k - (d ω).A 0 u)) volume 0 t ∧
        (d ω).imageForce t k = (d ω).imageForce 0 k +
          ∫ u in (0 : ℝ)..t, 2 * (d ω).A 1 u ^ 2 / ((d ω).imageForce u k - (d ω).A 0 u))
    {u : ℝ≥0} (hu : u ≤ seedCapacityHorizon d S ω) :
    IntervalIntegrable (fun t : ℝ => (seedCapacityDriver d S t.toNNReal ω -
      seedCapacityForce d S k t.toNNReal ω)⁻¹) volume 0 u ∧
      seedCapacityForce d S k u ω = seedCapacityForce d S k 0 ω +
        ∫ t in (0 : ℝ)..u, 2 / (seedCapacityForce d S k t.toNNReal ω - seedCapacityDriver d S t.toNNReal ω) := by
  have hle (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (S ω)) : t.toNNReal ≤ S ω := by
    simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal ht.2
  have hW (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (S ω)) :
      seedCapacityDriver d S ((d ω).a t).toNNReal ω = (d ω).A 0 t - (d ω).A 0 0 := by
    simpa only [Real.coe_toNNReal _ ht.1] using seedCapacityDriver_at_capacity hown hCc hCs hc hlb ω (hle t ht)
  have hV (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (S ω)) :
      seedCapacityForce d S k ((d ω).a t).toNNReal ω = (d ω).imageForce t k - (d ω).A 0 0 := by
    simpa only [Real.coe_toNNReal _ ht.1] using seedCapacityForce_at_capacity hown hCc hCs hc hlb ω k (hle t ht)
  obtain ⟨ht, hat⟩ := seedCapacityTime_spec hown hCc hCs hc hlb ω hu
  have htm : ((seedCapacityTime d S u ω : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) (S ω) := ⟨NNReal.coe_nonneg _, ht⟩
  have hh := (hown ω).capacity_force_equation htm (w := fun t : ℝ => seedCapacityDriver d S t.toNNReal ω)
    (v := fun t : ℝ => seedCapacityForce d S k t.toNNReal ω) hW hV (himg _ htm).1 (himg _ htm).2
  simpa only [hat, Real.toNNReal_coe, Real.toNNReal_zero] using hh

omit hown in
/-- The capacity force points are continuous when the own-time image forces are continuous on `[0, S]`. -/
theorem continuous_seedCapacityForce_at (ω : Ω) (k : Fin (n + 1))
    (hV : ContinuousOn (fun t => (d ω).imageForce t k) (Icc 0 (S ω))) :
    Continuous (seedCapacityForce d S k · ω) := by
  refine Continuous.sub ?_ continuous_const
  apply hV.comp_continuous (continuous_subtype_val.comp (continuous_seedCapacityTime hCc hCs hc hlb ω))
  intro u
  exact ⟨(seedCapacityTime d S u ω).coe_nonneg, min_le_right _ _⟩

/-- A positive-time own side transfers to the capacity coordinates: `X_t < A₀(t)` at positive own times gives
`v_u < w_u` at positive capacity times up to the horizon. -/
theorem seedCapacityForce_lt_driver (ω : Ω) (k : Fin (n + 1))
    (hlt : ∀ t ∈ Ioc (0 : ℝ) (S ω), (d ω).imageForce t k < (d ω).A 0 t) {u : ℝ≥0} (hu0 : 0 < u)
    (hu : u ≤ seedCapacityHorizon d S ω) : seedCapacityForce d S k u ω < seedCapacityDriver d S u ω := by
  have hp := seedCapacityTime_pos hown hCc hCs hc hlb ω hu0 hu
  have hle := (seedCapacityTime_spec hown hCc hCs hc hlb ω hu).1
  have h := hlt _ ⟨by exact_mod_cast hp, by exact_mod_cast hle⟩
  exact sub_lt_sub_right h _

/-- The mirror of `seedCapacityForce_lt_driver` for the right side. -/
theorem seedCapacityDriver_lt_force (ω : Ω) (k : Fin (n + 1))
    (hgt : ∀ t ∈ Ioc (0 : ℝ) (S ω), (d ω).A 0 t < (d ω).imageForce t k) {u : ℝ≥0} (hu0 : 0 < u)
    (hu : u ≤ seedCapacityHorizon d S ω) : seedCapacityDriver d S u ω < seedCapacityForce d S k u ω := by
  have hp := seedCapacityTime_pos hown hCc hCs hc hlb ω hu0 hu
  have hle := (seedCapacityTime_spec hown hCc hCs hc hlb ω hu).1
  have h := hgt _ ⟨by exact_mod_cast hp, by exact_mod_cast hle⟩
  exact sub_lt_sub_right h _

/-- **`SeedImageGeometry` of the seeded capacity coordinates.** For an identification `e` of the image word
(left marks `e (inl i)`, right marks `e (inr j)` among the other tip `0` and the marks), the actual capacity driver and
force points up to the actual horizon satisfy the deterministic image equations, from:

* `hcont`, `himg`: continuity and the own-time image equation of every image index on `[0, S]`;
* `hltL`, `hgtR`: the positive-time sides of the image forces relative to the image driver `A₀`;
* `hxL`, `hxR`, `hordL`, `hordR`: the initial sides and order; `hsL`, `hsR`: at most one image force per side at
  the driver's initial position;
* `hseedL`, `hseedR`: the seed sums of the initial capacity word. -/
theorem seedImageGeometry_seedCapacity (e : Fin nL ⊕ Fin nR ≃ Fin (n + 1)) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (ω : Ω) (hcont : ∀ k, ContinuousOn (fun t => (d ω).imageForce t k) (Icc 0 (S ω)))
    (himg : ∀ k, ∀ t ∈ Icc (0 : ℝ) (S ω),
      IntervalIntegrable (fun u => 2 * (d ω).A 1 u ^ 2 / ((d ω).imageForce u k - (d ω).A 0 u)) volume 0 t ∧
        (d ω).imageForce t k = (d ω).imageForce 0 k +
          ∫ u in (0 : ℝ)..t, 2 * (d ω).A 1 u ^ 2 / ((d ω).imageForce u k - (d ω).A 0 u))
    (hltL : ∀ i, ∀ t ∈ Ioc (0 : ℝ) (S ω), (d ω).imageForce t (e (.inl i)) < (d ω).A 0 t)
    (hgtR : ∀ j, ∀ t ∈ Ioc (0 : ℝ) (S ω), (d ω).A 0 t < (d ω).imageForce t (e (.inr j)))
    (hxL : ∀ i, (d ω).imageForce 0 (e (.inl i)) ≤ (d ω).A 0 0)
    (hxR : ∀ j, (d ω).A 0 0 ≤ (d ω).imageForce 0 (e (.inr j)))
    (hordL : Antitone fun i => (d ω).imageForce 0 (e (.inl i)))
    (hordR : Monotone fun j => (d ω).imageForce 0 (e (.inr j)))
    (hsL : ∀ i i', (d ω).imageForce 0 (e (.inl i)) = (d ω).imageForce 0 (e (.inl i')) →
      (d ω).imageForce 0 (e (.inl i)) = (d ω).A 0 0 → i = i')
    (hsR : ∀ j j', (d ω).imageForce 0 (e (.inr j)) = (d ω).imageForce 0 (e (.inr j')) →
      (d ω).imageForce 0 (e (.inr j)) = (d ω).A 0 0 → j = j')
    (hseedL : -2 < seedSum (fun i => seedCapacityForce d S (e (.inl i)) 0 ω) ρL)
    (hseedR : -2 < seedSum (fun j => seedCapacityForce d S (e (.inr j)) 0 ω) ρR) :
    SeedImageGeometry (fun i => seedCapacityForce d S (e (.inl i)) 0 ω)
      (fun j => seedCapacityForce d S (e (.inr j)) 0 ω) ρL ρR (seedCapacityDriver d S · ω)
      (fun i u => seedCapacityForce d S (e (.inl i)) u ω) (fun j u => seedCapacityForce d S (e (.inr j)) u ω)
      (seedCapacityHorizon d S ω) := by
  have h0 (k : Fin (n + 1)) := seedCapacityForce_zero hown hCc hCs hc hlb ω k
  have hint (k : Fin (n + 1)) {u : ℝ≥0} (hu : u ≤ seedCapacityHorizon d S ω) :=
    seedCapacityForce_integrated hown hCc hCs hc hlb ω k (himg k) hu
  apply seedImageGeometry_of_forces (seedCapacityDriver_zero hown hCc hCs hc hlb ω) (fun _ => rfl) (fun _ => rfl)
    (continuous_seedCapacityDriver hown hCc hCs hc hlb ω)
    (fun i => continuous_seedCapacityForce_at hCc hCs hc hlb ω _ (hcont _))
    (fun j => continuous_seedCapacityForce_at hCc hCs hc hlb ω _ (hcont _))
    (fun t ht i => (hint _ ht).1) (fun t ht j => (hint _ ht).1) (fun t ht i => (hint _ ht).2)
    (fun t ht j => (hint _ ht).2)
    (fun t hp ht i => seedCapacityForce_lt_driver hown hCc hCs hc hlb ω _ (hltL i) hp ht)
    (fun t hp ht j => seedCapacityDriver_lt_force hown hCc hCs hc hlb ω _ (hgtR j) hp ht)
  · intro i; rw [h0]; linarith [hxL i]
  · intro j; rw [h0]; linarith [hxR j]
  · intro i i' hii'; simp only [h0]; linarith [hordL hii']
  · intro j j' hjj'; simp only [h0]; linarith [hordR hjj']
  · intro i i' hx hx0
    simp only [h0] at hx hx0
    exact hsL i i' (by linarith) (by linarith)
  · intro j j' hx hx0
    simp only [h0] at hx hx0
    exact hsR j j' (by linarith) (by linarith)
  · exact hseedL
  · exact hseedR

end Capacity

end InteractingSLE.ZhanGT4.A1SeedGeom
