/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Prop61BExplored

/-!
# Remark 6.7: Proposition 6.1 for three flow lines — the configuration and the stopped identification

Packet PROVE-LEMMA71F (specification §6.1, Remark 6.7, `source/spec/p145-192.md` L566–L583, pp. 169–171). Remark 6.7
conditions on the two complete outer curves `α = η_{θ₁}`, `β = η_{θ₂}` and the middle prefix `γ|_{[0, τ]}`, `γ = η`, for
"any stopping time for the filtration `𝓕_t = σ(η(s) : s ≤ t, η_{θ₁}, η_{θ₂})`", with `A(τ) = α ∪ γ([0, τ]) ∪ β`.

This file puts that configuration into the `Fin k` form of Lemma 6.2 and of the landed Proposition 6.1 core
(`Prop61BExplored.lean`): the three curves are ordered **outer curves first** (`β`, `α`, `γ`), both outer curves run
in full (`τ = ∞`), and the middle curve is stopped at `τ = S(β, α, γ)` for a measurable path functional `S` of the two
complete outer curves and the middle path with Galmarino's property in the middle path — exactly a stopping time of
`𝓕_t` in path form (ruling R37). Then:

* `explored_threeStops`, `explored_threeTop`, `explored_threeOuter`: the explored sets are `A(τ)`, the full union
  `α ∪ γ ∪ β`, and the outer union `α ∪ β` (intersected with `ℍ`);
* `isGalmarino_threeRule`, `measurable_threeRule`, `threeStops_eq_threeRule`: the hypotheses of Lemma 6.2 on the stopping
  rule, from those of `S`;
* **`ae_eqOn_three_of_tendsto`** (Remark 6.7, stopped, the identification of the mean): on every component of
  `ℍ ∖ A(τ)` (bounded or not), `𝒞_{A(τ)} + F = 𝔥_C = G ∘ φ_C − χ L`, as soon as every prime end outside a finite set
  either lies on `A(τ) ∪ ℝ` where the full union is contained in `A(τ)` nearby and the **full three-curve mean** has the
  boundary values of `𝔥_C` ("every earlier point on `γ([0, τ))` has positive distance from the remaining compact tail …
  compare `A(τ) ⊆ A`"), or lies on `α ∪ β ∪ ℝ` where `A(τ)` is contained in the outer union nearby and the **outer-union
  mean** has those boundary values ("along the exposed outer-curve suffixes … the stopped middle prefix has positive
  distance, so comparison with the two outer curves gives the prescribed boundary values");
* **`ae_condExp_exp_eq_three_of_tendsto`**: the corresponding Gaussian law given the germs of `A(τ)` and the ordered
  labeled curves `(β, α, γ|_{[0, τ]})`;
* **`ae_eq_on_three_full_of_avoid`** (Remark 6.7, full curves: "In a component to the right of `γ`, adding `β` to
  `α ∪ γ` does not change the conditional mean, by Proposition 3.9"): on a union `C` of components of `ℍ ∖ (α ∪ γ)`
  avoided by `β` (measurable in `σ(α ∪ γ)`), `𝒞_{α ∪ γ ∪ β} = 𝒞_{α ∪ γ}`; likewise on the left with `α` and `β` swapped
  (`ae_eq_on_three_full_of_avoid_left`); both from `ae_eq_on_explored_union_of_avoid` (Proposition 3.9 for explored
  sets with deterministic stops, any number of curves).

The remaining inputs of the remark are the prime-end boundary values of the comparison means (the two-curve and
single-curve laws in each component's chart, with the branch of the supplement's §2.3 normalization) and the hypotheses
of Lemma 6.2 for the three flow lines (continuity, field determination, history-sensitive locality, transience).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal Real

namespace InteractingSLE.Sec6.Three

open QuantumZipper (H)
open LQGMetric (DistOn TestOn CondIndepEv)
open SupercriticalConformalCovariance (IsConformalBijection)
open LocalSets

/-! ### The configuration -/

section Config

variable {Ω : Type*}

/-- The three curves, outer curves first: `β = η_{θ₂}` (left flank), `α = η_{θ₁}` (right flank), `γ = η` (middle). -/
def threeCurves (β α γ : Ω → ℝ≥0 → ℂ) : Fin 3 → Ω → ℝ≥0 → ℂ := ![β, α, γ]

/-- The stopping times of Remark 6.7: both outer curves in full, the middle curve stopped at `τ`. -/
def threeStops (τ : Ω → ℝ≥0∞) : Fin 3 → Ω → ℝ≥0∞ := ![fun _ => ⊤, fun _ => ⊤, τ]

/-- The stopping rule in path form: `∞` for the outer curves, `S(β, α, γ)` for the middle curve (`S` reads the two
complete outer histories and the middle path). -/
def threeRule (S : Hist → Hist → (ℚ≥0 → ℂ) → ℝ≥0∞) : Fin 3 → (Fin 3 → Hist) → (ℚ≥0 → ℂ) → ℝ≥0∞ :=
  ![fun _ _ => ⊤, fun _ _ => ⊤, fun p c => S (p 0) (p 1) c]

/-- The deterministic stops of the outer union (the middle curve at time `0`). -/
def outerStops : Fin 3 → ℝ≥0∞ := ![⊤, ⊤, 0]

@[simp] theorem threeCurves_zero (β α γ : Ω → ℝ≥0 → ℂ) : threeCurves β α γ 0 = β := rfl
@[simp] theorem threeCurves_one (β α γ : Ω → ℝ≥0 → ℂ) : threeCurves β α γ 1 = α := rfl
@[simp] theorem threeCurves_two (β α γ : Ω → ℝ≥0 → ℂ) : threeCurves β α γ 2 = γ := rfl

theorem forall_fin_three {p : Fin 3 → Prop} : (∀ i, p i) ↔ p 0 ∧ p 1 ∧ p 2 := by
  refine ⟨fun h => ⟨h 0, h 1, h 2⟩, fun h i => ?_⟩
  fin_cases i
  exacts [h.1, h.2.1, h.2.2]

theorem iUnion_fin_three (s : Fin 3 → Set ℂ) : (⋃ i, s i) = s 0 ∪ s 1 ∪ s 2 := by
  ext z
  simp only [mem_iUnion, mem_union]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    exacts [Or.inl (Or.inl hi), Or.inl (Or.inr hi), Or.inr hi]
  · rintro ((h | h) | h)
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]

theorem setOf_le_top : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ⊤} = univ :=
  eq_univ_of_forall fun t => show (t : ℝ≥0∞) ≤ ⊤ from le_top

/-- The explored set of Remark 6.7: `A(τ) = β ∪ α ∪ γ([0, τ])` (in `ℍ`). -/
theorem explored_threeStops (β α γ : Ω → ℝ≥0 → ℂ) (τ : Ω → ℝ≥0∞) (ω : Ω) :
    explored (threeCurves β α γ) (threeStops τ) ω =
      (range (β ω) ∪ range (α ω) ∪ γ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ τ ω}) ∩ H := by
  unfold explored
  rw [iUnion_fin_three]
  simp only [threeCurves, threeStops, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, setOf_le_top, image_univ]

/-- The explored set of the complete curves: `α ∪ γ ∪ β` (in `ℍ`). -/
theorem explored_threeTop (β α γ : Ω → ℝ≥0 → ℂ) (ω : Ω) :
    explored (threeCurves β α γ) (fun _ _ => ⊤) ω = (range (β ω) ∪ range (α ω) ∪ range (γ ω)) ∩ H := by
  unfold explored
  rw [iUnion_fin_three]
  simp only [threeCurves, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, setOf_le_top, image_univ]

/-- The explored set of the outer union: `α ∪ β` (in `ℍ`), when the middle curve starts on `ℝ`. -/
theorem explored_threeOuter (β α γ : Ω → ℝ≥0 → ℂ) (ω : Ω) (hγ0 : (γ ω 0).im = 0) :
    explored (threeCurves β α γ) (fun i _ => outerStops i) ω = (range (β ω) ∪ range (α ω)) ∩ H := by
  unfold explored
  rw [iUnion_fin_three]
  have h0 : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ 0} = {0} := by
    ext t
    simp only [mem_ofPred_eq, nonpos_iff_eq_zero, ENNReal.coe_eq_zero, mem_singleton_iff]
  simp only [threeCurves, outerStops, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, setOf_le_top, image_univ, h0, image_singleton]
  ext z
  simp only [mem_inter_iff, mem_union, mem_singleton_iff]
  constructor
  · rintro ⟨(h | h) | rfl, hz⟩
    · exact ⟨Or.inl h, hz⟩
    · exact ⟨Or.inr h, hz⟩
    · exact absurd hz (by show ¬ 0 < (γ ω 0).im; rw [hγ0]; exact lt_irrefl 0)
  · rintro ⟨h | h, hz⟩
    · exact ⟨Or.inl (Or.inl h), hz⟩
    · exact ⟨Or.inl (Or.inr h), hz⟩

/-- The deterministic outer stops lie below the stops of Remark 6.7. -/
theorem outerStops_le (τ : Ω → ℝ≥0∞) (i : Fin 3) (ω : Ω) : outerStops i ≤ threeStops τ i ω := by
  fin_cases i
  · exact le_rfl
  · exact le_rfl
  · exact zero_le

/-- Galmarino's property of the stopping rule, from that of `S` in the middle path. -/
theorem isGalmarino_threeRule {S : Hist → Hist → (ℚ≥0 → ℂ) → ℝ≥0∞}
    (hSg : ∀ x y c c', (∀ q : ℚ≥0, (((q : ℝ≥0) : ℝ≥0∞) ≤ S x y c) → c q = c' q) → S x y c' = S x y c)
    (j : Fin 3) : IsGalmarino (threeRule S j) := by
  fin_cases j
  · exact fun _ _ _ _ => rfl
  · exact fun _ _ _ _ => rfl
  · exact fun p c c' h => hSg (p 0) (p 1) c c' h

/-- Measurability of the stopping rule, from that of `S`. -/
theorem measurable_threeRule {S : Hist → Hist → (ℚ≥0 → ℂ) → ℝ≥0∞}
    (hSm : Measurable fun z : (Hist × Hist) × (ℚ≥0 → ℂ) => S z.1.1 z.1.2 z.2) (j : Fin 3) :
    Measurable (Function.uncurry (threeRule S j)) := by
  fin_cases j
  · exact measurable_const
  · exact measurable_const
  · show Measurable fun z : (Fin 3 → Hist) × (ℚ≥0 → ℂ) => S (z.1 0) (z.1 1) z.2
    have h01 : Measurable fun z : (Fin 3 → Hist) × (ℚ≥0 → ℂ) => (z.1 0, z.1 1) :=
      ((measurable_pi_apply 0).comp measurable_fst).prodMk ((measurable_pi_apply 1).comp measurable_fst)
    exact hSm.comp (h01.prodMk measurable_snd)

/-- The stops of Remark 6.7 satisfy the path-form recursion of Lemma 6.2 when `τ = S(β, α, γ)`. -/
theorem threeStops_eq_threeRule {β α γ : Ω → ℝ≥0 → ℂ} {τ : Ω → ℝ≥0∞} {S : Hist → Hist → (ℚ≥0 → ℂ) → ℝ≥0∞}
    (hτ : ∀ ω, τ ω = S (histOf (pathCoord (β ω)) ⊤) (histOf (pathCoord (α ω)) ⊤) (pathCoord (γ ω))) :
    ∀ j ω, threeStops τ j ω = threeRule S j
      (prevHist (fun i => pathCoord (threeCurves β α γ i ω)) (fun i => threeStops τ i ω) j)
      (pathCoord (threeCurves β α γ j ω)) := by
  intro j ω
  fin_cases j
  · rfl
  · rfl
  · show τ ω = S (prevHist (fun i => pathCoord (threeCurves β α γ i ω)) (fun i => threeStops τ i ω) 2 0)
      (prevHist (fun i => pathCoord (threeCurves β α γ i ω)) (fun i => threeStops τ i ω) 2 1) (pathCoord (γ ω))
    have h0 : prevHist (fun i => pathCoord (threeCurves β α γ i ω)) (fun i => threeStops τ i ω) 2 0 =
        histOf (pathCoord (β ω)) ⊤ := by
      unfold prevHist
      rw [ite_eq_left (show (0 : Fin 3) < 2 by decide)]
      rfl
    have h1 : prevHist (fun i => pathCoord (threeCurves β α γ i ω)) (fun i => threeStops τ i ω) 2 1 =
        histOf (pathCoord (α ω)) ⊤ := by
      unfold prevHist
      rw [ite_eq_left (show (1 : Fin 3) < 2 by decide)]
      rfl
    rw [h0, h1]
    exact hτ ω

end Config

/-! ### Remark 6.7, the stopped three-curve identification -/

section Assembly

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {β α γ : Ω → ℝ≥0 → ℂ} {τ : Ω → ℝ≥0∞}
  {S : Hist → Hist → (ℚ≥0 → ℂ) → ℝ≥0∞}

/-- **Remark 6.7, stopped: the identification of the mean** (pp. 170–171). Let `h` be a zero-boundary GFF on `ℍ` and
`F` a bounded harmonic function (the field is `h + F`); let `β, α, γ` be continuous transient curves from `0` in the
closed half-plane with the hypotheses of Lemma 6.2 (measurable, determined by `h`, history-sensitively local), and let
`τ = S(β, α, γ)` be a stopping time of `𝓕_t = σ(γ(s) : s ≤ t, α, β)` in path form. For versions `gS, gL, gT` of the
local-set means of `A(τ)`, of the full union `α ∪ γ ∪ β` and of the outer union `α ∪ β`: almost surely, for every
component `C` of `ℍ ∖ A(τ)` and every chart `(f, φ_C, G, L)` of Aux. lemma 28 with finite exceptional set such that
every other prime end has an impression `p` either on `A(τ) ∪ ℝ` with the full union inside `A(τ)` near `p` and the
full-union mean there with the boundary values of `𝔥_C = G ∘ φ_C − χ L`, or on the outer union `∪ ℝ` with `A(τ)` inside
the outer union near `p` and the outer-union mean there with those boundary values: `𝒞_{A(τ)} + F = 𝔥_C` on `C`. -/
theorem ae_eqOn_three_of_tendsto
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hc : ∀ i ω, Continuous (threeCurves β α γ i ω)) (h0 : ∀ i ω, threeCurves β α γ i ω 0 = 0)
    (him : ∀ i ω t, 0 ≤ (threeCurves β α γ i ω t).im)
    (hηm : ∀ i t, Measurable fun ω => threeCurves β α γ i ω t)
    (hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => threeCurves β α γ i ω t) =ᵐ[P] fun ω => f (h ω))
    (hloc : ∀ i, IsEntranceHistoryLocal (threeCurves β α γ i) h P)
    (htr : ∀ᵐ ω ∂P, ∀ i, Tendsto (threeCurves β α γ i ω) atTop (Bornology.cobounded ℂ))
    (hSm : Measurable fun z : (Hist × Hist) × (ℚ≥0 → ℂ) => S z.1.1 z.1.2 z.2)
    (hSg : ∀ x y c c', (∀ q : ℚ≥0, (((q : ℝ≥0) : ℝ≥0∞) ≤ S x y c) → c q = c' q) → S x y c' = S x y c)
    (hτ : ∀ ω, τ ω = S (histOf (pathCoord (β ω)) ⊤) (histOf (pathCoord (α ω)) ⊤) (pathCoord (γ ω)))
    {gS gL gT : Ω → DistOn upperHalfPlaneOpens}
    (hgS : IsLocalSetMean (explored (threeCurves β α γ) (threeStops τ)) h P gS)
    (hgL : IsLocalSetMean (explored (threeCurves β α γ) fun _ _ => ⊤) h P gL)
    (hgT : IsLocalSetMean (explored (threeCurves β α γ) fun i _ => outerStops i) h P gT) {F : ℂ → ℝ}
    (hF : InnerProductSpace.HarmonicOnNhd F H) (hFb : ∃ M : ℝ, ∀ z ∈ H, |F z| ≤ M) (χ : ℝ) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ explored (threeCurves β α γ) (threeStops τ) ω,
      ∀ v vL vT : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ explored (threeCurves β α γ) (threeStops τ) ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ explored (threeCurves β α γ) (threeStops τ) ω →
        gS ω ψ = ∫ x, v x * ψ x) →
      InnerProductSpace.HarmonicOnNhd vL (H \ explored (threeCurves β α γ) (fun _ _ => ⊤) ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ explored (threeCurves β α γ) (fun _ _ => ⊤) ω →
        gL ω ψ = ∫ x, vL x * ψ x) →
      InnerProductSpace.HarmonicOnNhd vT (H \ explored (threeCurves β α γ) (fun i _ => outerStops i) ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens,
        tsupport ψ ⊆ H \ explored (threeCurves β α γ) (fun i _ => outerStops i) ω → gT ω ψ = ∫ x, vT x * ψ x) →
      ∀ (f φc : ℂ → ℂ) (G Lc : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1)
        (connectedComponentIn (H \ explored (threeCurves β α γ) (threeStops τ) ω) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ explored (threeCurves β α γ) (threeStops τ) ω) z₀)
        {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn Lc (connectedComponentIn (H \ explored (threeCurves β α γ) (threeStops τ) ω) z₀) →
      (∀ z ∈ connectedComponentIn (H \ explored (threeCurves β α γ) (threeStops τ) ω) z₀,
        deriv φc z = ‖deriv φc z‖ * exp (Lc z * I)) →
      E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E → ∃ p : ℂ, Tendsto f (𝓝[ball 0 1] q) (𝓝 p) ∧
        ((p ∈ explored (threeCurves β α γ) (threeStops τ) ω ∪ {z : ℂ | z.im = 0} ∧
            (∃ r > 0, explored (threeCurves β α γ) (fun _ _ => ⊤) ω ∩ ball p r ⊆
              explored (threeCurves β α γ) (threeStops τ) ω) ∧
            Tendsto (fun ζ => (vL (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * Lc (f ζ)))
              (𝓝[ball 0 1] q) (𝓝 0)) ∨
          (p ∈ explored (threeCurves β α γ) (fun i _ => outerStops i) ω ∪ {z : ℂ | z.im = 0} ∧
            (∃ r > 0, explored (threeCurves β α γ) (threeStops τ) ω ∩ ball p r ⊆
              explored (threeCurves β α γ) (fun i _ => outerStops i) ω) ∧
            Tendsto (fun ζ => (vT (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * Lc (f ζ)))
              (𝓝[ball 0 1] q) (𝓝 0)))) →
      ∀ z ∈ connectedComponentIn (H \ explored (threeCurves β α γ) (threeStops τ) ω) z₀,
        v z + F z = G (φc z) - χ * Lc z :=
  ae_eqOn_explored_of_tendsto (x := fun _ => 0) hh hc h0 (fun _ => Complex.zero_im) him hηm hdet hloc htr
    (measurable_threeRule hSm) (isGalmarino_threeRule hSg) (threeStops_eq_threeRule hτ) outerStops
    (outerStops_le τ) hgS hgL hgT hF hFb χ

/-- **Remark 6.7, stopped: the conditional law given the labeled curves.** Under the hypotheses of
`ae_eqOn_three_of_tendsto`, for a test function `φ`: almost surely, for every component `C` of `ℍ ∖ A(τ)` containing the
support of `φ` and every chart satisfying the prime-end premise, given the germs of `A(τ)` and the ordered labeled curves
`(β, α, γ|_{[0, τ]})`, the field `h + F` paired with `φ` has the conditional characteristic function of
`(𝔥_C, φ) + GFF_C(φ)`. -/
theorem ae_condExp_exp_eq_three_of_tendsto
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hc : ∀ i ω, Continuous (threeCurves β α γ i ω)) (h0 : ∀ i ω, threeCurves β α γ i ω 0 = 0)
    (him : ∀ i ω t, 0 ≤ (threeCurves β α γ i ω t).im)
    (hηm : ∀ i t, Measurable fun ω => threeCurves β α γ i ω t)
    (hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => threeCurves β α γ i ω t) =ᵐ[P] fun ω => f (h ω))
    (hloc : ∀ i, IsEntranceHistoryLocal (threeCurves β α γ i) h P)
    (htr : ∀ᵐ ω ∂P, ∀ i, Tendsto (threeCurves β α γ i ω) atTop (Bornology.cobounded ℂ))
    (hSm : Measurable fun z : (Hist × Hist) × (ℚ≥0 → ℂ) => S z.1.1 z.1.2 z.2)
    (hSg : ∀ x y c c', (∀ q : ℚ≥0, (((q : ℝ≥0) : ℝ≥0∞) ≤ S x y c) → c q = c' q) → S x y c' = S x y c)
    (hτ : ∀ ω, τ ω = S (histOf (pathCoord (β ω)) ⊤) (histOf (pathCoord (α ω)) ⊤) (pathCoord (γ ω)))
    {gS gL gT : Ω → DistOn upperHalfPlaneOpens}
    (hgS : IsLocalSetMean (explored (threeCurves β α γ) (threeStops τ)) h P gS)
    (hgL : IsLocalSetMean (explored (threeCurves β α γ) fun _ _ => ⊤) h P gL)
    (hgT : IsLocalSetMean (explored (threeCurves β α γ) fun i _ => outerStops i) h P gT) {F : ℂ → ℝ}
    (hF : InnerProductSpace.HarmonicOnNhd F H) (hFb : ∃ M : ℝ, ∀ z ∈ H, |F z| ≤ M) (χ : ℝ)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ explored (threeCurves β α γ) (threeStops τ) ω,
      tsupport φ ⊆ connectedComponentIn (H \ explored (threeCurves β α γ) (threeStops τ) ω) z₀ →
      ∀ v vL vT : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ explored (threeCurves β α γ) (threeStops τ) ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ explored (threeCurves β α γ) (threeStops τ) ω →
        gS ω ψ = ∫ x, v x * ψ x) →
      InnerProductSpace.HarmonicOnNhd vL (H \ explored (threeCurves β α γ) (fun _ _ => ⊤) ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ explored (threeCurves β α γ) (fun _ _ => ⊤) ω →
        gL ω ψ = ∫ x, vL x * ψ x) →
      InnerProductSpace.HarmonicOnNhd vT (H \ explored (threeCurves β α γ) (fun i _ => outerStops i) ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens,
        tsupport ψ ⊆ H \ explored (threeCurves β α γ) (fun i _ => outerStops i) ω → gT ω ψ = ∫ x, vT x * ψ x) →
      ∀ (f φc : ℂ → ℂ) (G Lc : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1)
        (connectedComponentIn (H \ explored (threeCurves β α γ) (threeStops τ) ω) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ explored (threeCurves β α γ) (threeStops τ) ω) z₀)
        {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn Lc (connectedComponentIn (H \ explored (threeCurves β α γ) (threeStops τ) ω) z₀) →
      (∀ z ∈ connectedComponentIn (H \ explored (threeCurves β α γ) (threeStops τ) ω) z₀,
        deriv φc z = ‖deriv φc z‖ * exp (Lc z * I)) →
      E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E → ∃ p : ℂ, Tendsto f (𝓝[ball 0 1] q) (𝓝 p) ∧
        ((p ∈ explored (threeCurves β α γ) (threeStops τ) ω ∪ {z : ℂ | z.im = 0} ∧
            (∃ r > 0, explored (threeCurves β α γ) (fun _ _ => ⊤) ω ∩ ball p r ⊆
              explored (threeCurves β α γ) (threeStops τ) ω) ∧
            Tendsto (fun ζ => (vL (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * Lc (f ζ)))
              (𝓝[ball 0 1] q) (𝓝 0)) ∨
          (p ∈ explored (threeCurves β α γ) (fun i _ => outerStops i) ω ∪ {z : ℂ | z.im = 0} ∧
            (∃ r > 0, explored (threeCurves β α γ) (threeStops τ) ω ∩ ball p r ⊆
              explored (threeCurves β α γ) (fun i _ => outerStops i) ω) ∧
            Tendsto (fun ζ => (vT (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * Lc (f ζ)))
              (𝓝[ball 0 1] q) (𝓝 0)))) →
      P[fun ω' => cexp (I * ((h ω' φ + ∫ x, F x * φ x : ℝ) : ℂ)) |
          germSigma (explored (threeCurves β α γ) (threeStops τ)) h ⊔
            stoppedHistSigma (threeCurves β α γ) (threeStops τ)] ω =
        cexp (I * ((∫ x, (G (φc x) - χ * Lc x) * φ x : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov
            (connectedComponentIn (H \ explored (threeCurves β α γ) (threeStops τ) ω) z₀) φ φ) : ℝ) : ℂ) :=
  ae_condExp_exp_eq_explored_of_tendsto (x := fun _ => 0) hh hc h0 (fun _ => Complex.zero_im) him hηm hdet hloc
    htr (measurable_threeRule hSm) (isGalmarino_threeRule hSg) (threeStops_eq_threeRule hτ) outerStops
    (outerStops_le τ) hgS hgL hgT hF hFb χ φ

end Assembly

/-! ### Remark 6.7, the complete curves: Proposition 3.9 -/

section Full

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Proposition 3.9 for explored sets with deterministic stops.** Under the curve hypotheses of Lemma 6.2 (any number
of curves), for deterministic stops `τ₁, τ₂` and a union `C` of components of `ℍ ∖ A₁` (`A₁ = A(τ₁)`, `ℍ ∖ C` measurable
in `σ(A₁)`) avoided by `A₂ = A(τ₂)`: almost surely the mean of `A(max τ₁ τ₂) = A₁ ∪ A₂` agrees with that of `A₁` on
`C`. -/
theorem ae_eq_on_explored_union_of_avoid {k : ℕ} {η : Fin k → Ω → ℝ≥0 → ℂ} {x : Fin k → ℂ}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hc : ∀ i ω, Continuous (η i ω)) (h0 : ∀ i ω, η i ω 0 = x i) (hηm : ∀ i t, Measurable fun ω => η i ω t)
    (hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η i ω t) =ᵐ[P] fun ω => f (h ω))
    (hloc : ∀ i, IsEntranceHistoryLocal (η i) h P)
    (htr : ∀ᵐ ω ∂P, ∀ i, Tendsto (η i ω) atTop (Bornology.cobounded ℂ))
    (τ₁ τ₂ : Fin k → ℝ≥0∞) {C : Ω → Set ℂ}
    (hCm : Measurable[MeasurableSpace.comap (explored η fun i _ => τ₁ i) hittingSigma, hittingSigma]
      fun ω => H \ C ω)
    (hC : ∀ᵐ ω ∂P, C ω ⊆ H \ explored η (fun i _ => τ₁ i) ω ∧
      ∀ z ∈ C ω, connectedComponentIn (H \ explored η (fun i _ => τ₁ i) ω) z ⊆ C ω)
    (hCA₂ : ∀ᵐ ω ∂P, Disjoint (C ω) (explored η (fun i _ => τ₂ i) ω))
    {g g₁ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (explored η fun i _ => max (τ₁ i) (τ₂ i)) h P g)
    (hg₁ : IsLocalSetMean (explored η fun i _ => τ₁ i) h P g₁) :
    ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ C ω → g ω φ = g₁ ω φ := by
  have hl : ∀ τ' : Fin k → ℝ≥0∞, IsLocalSet (explored η fun i _ => τ' i) h P := fun τ' =>
    isLocalSet_explored_of_tendsto (S := fun j _ _ => τ' j) hh hc h0 hηm hdet hloc htr
      (fun _ => measurable_const) (fun j => isGalmarino_const (τ' j)) (fun _ _ => rfl)
  have hm : ∀ τ' : Fin k → ℝ≥0∞, Measurable[mΩ, hittingSigma] (explored η fun i _ => τ' i) :=
    fun τ' => measurable_explored hc hηm fun _ => measurable_const
  have hd : ∀ τ' : Fin k → ℝ≥0∞, MeasurableSpace.comap (explored η fun i _ => τ' i) hittingSigma ≤
      aeSigma (MeasurableSpace.comap h inferInstance) P := fun τ' =>
    comap_explored_le_aeSigma (S := fun j _ _ => τ' j) hc hdet (fun _ => measurable_const)
      (fun j => isGalmarino_const (τ' j)) (fun _ _ => rfl)
  have hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (explored η fun i _ => τ₁ i) hittingSigma)
      (MeasurableSpace.comap (explored η fun i _ => τ₂ i) hittingSigma) P :=
    condIndepEv_of_le_aeSigma hh.measurable.comap_le (hm τ₂).comap_le (hd τ₁)
  have hU : (fun ω => explored η (fun i _ => τ₁ i) ω ∪ explored η (fun i _ => τ₂ i) ω) =
      explored η fun i _ => max (τ₁ i) (τ₂ i) :=
    funext fun ω => explored_union_eq_max η _ _ ω
  have hg' : IsLocalSetMean (fun ω => explored η (fun i _ => τ₁ i) ω ∪
      explored η (fun i _ => τ₂ i) ω) h P g := by rw [hU]; exact hg
  exact IsLocalSetMean.ae_eq_on_of_union hh (hm τ₁) (hm τ₂) hci (hl τ₁) (hl τ₂) hCm hC hCA₂ hg' hg₁

/-- The stops of the right pair `α ∪ γ` (the left flank stopped at `0`). -/
def rightPairStops : Fin 3 → ℝ≥0∞ := ![0, ⊤, ⊤]

/-- The stops of the left flank alone. -/
def leftFlankStops : Fin 3 → ℝ≥0∞ := ![⊤, 0, 0]

/-- The stops of the left pair `β ∪ γ` (the right flank stopped at `0`). -/
def leftPairStops : Fin 3 → ℝ≥0∞ := ![⊤, 0, ⊤]

/-- The stops of the right flank alone. -/
def rightFlankStops : Fin 3 → ℝ≥0∞ := ![0, ⊤, 0]

omit mΩ in
theorem max_rightPair_leftFlank :
    (fun (i : Fin 3) (_ : Ω) => max (rightPairStops i) (leftFlankStops i)) = fun _ _ => ⊤ := by
  funext i ω
  fin_cases i <;> simp [rightPairStops, leftFlankStops]

omit mΩ in
theorem max_leftPair_rightFlank :
    (fun (i : Fin 3) (_ : Ω) => max (leftPairStops i) (rightFlankStops i)) = fun _ _ => ⊤ := by
  funext i ω
  fin_cases i <;> simp [leftPairStops, rightFlankStops]

/-- **Remark 6.7, complete curves, right side** ("In a component to the right of `γ`, adding `β` to `α ∪ γ` does not
change the conditional mean, by Proposition 3.9"). Under the curve hypotheses of Lemma 6.2 for `β, α, γ`, on a union `C`
of components of `ℍ ∖ (α ∪ γ)` (measurable in `σ(α ∪ γ)`) avoided by `β`, the mean of the full union `α ∪ γ ∪ β` agrees
with the mean of the pair `α ∪ γ` (Proposition 6.1 for that pair). -/
theorem ae_eq_on_three_full_of_avoid {β α γ : Ω → ℝ≥0 → ℂ}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hc : ∀ i ω, Continuous (threeCurves β α γ i ω)) (h0 : ∀ i ω, threeCurves β α γ i ω 0 = 0)
    (hηm : ∀ i t, Measurable fun ω => threeCurves β α γ i ω t)
    (hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => threeCurves β α γ i ω t) =ᵐ[P] fun ω => f (h ω))
    (hloc : ∀ i, IsEntranceHistoryLocal (threeCurves β α γ i) h P)
    (htr : ∀ᵐ ω ∂P, ∀ i, Tendsto (threeCurves β α γ i ω) atTop (Bornology.cobounded ℂ)) {C : Ω → Set ℂ}
    (hCm : Measurable[MeasurableSpace.comap (explored (threeCurves β α γ) fun i _ => rightPairStops i)
      hittingSigma, hittingSigma] fun ω => H \ C ω)
    (hC : ∀ᵐ ω ∂P, C ω ⊆ H \ explored (threeCurves β α γ) (fun i _ => rightPairStops i) ω ∧
      ∀ z ∈ C ω, connectedComponentIn (H \ explored (threeCurves β α γ) (fun i _ => rightPairStops i) ω) z ⊆ C ω)
    (hCβ : ∀ᵐ ω ∂P, Disjoint (C ω) (explored (threeCurves β α γ) (fun i _ => leftFlankStops i) ω))
    {g g₁ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (explored (threeCurves β α γ) fun _ _ => ⊤) h P g)
    (hg₁ : IsLocalSetMean (explored (threeCurves β α γ) fun i _ => rightPairStops i) h P g₁) :
    ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ C ω → g ω φ = g₁ ω φ := by
  have hg' : IsLocalSetMean (explored (threeCurves β α γ) fun i _ =>
      max (rightPairStops i) (leftFlankStops i)) h P g := by
    rw [max_rightPair_leftFlank]; exact hg
  exact ae_eq_on_explored_union_of_avoid (x := fun _ => 0) hh hc h0 hηm hdet hloc htr rightPairStops
    leftFlankStops hCm hC hCβ hg' hg₁

/-- **Remark 6.7, complete curves, left side**: on a union of components of `ℍ ∖ (β ∪ γ)` avoided by `α`, the mean of
the full union agrees with the mean of the pair `β ∪ γ`. -/
theorem ae_eq_on_three_full_of_avoid_left {β α γ : Ω → ℝ≥0 → ℂ}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hc : ∀ i ω, Continuous (threeCurves β α γ i ω)) (h0 : ∀ i ω, threeCurves β α γ i ω 0 = 0)
    (hηm : ∀ i t, Measurable fun ω => threeCurves β α γ i ω t)
    (hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => threeCurves β α γ i ω t) =ᵐ[P] fun ω => f (h ω))
    (hloc : ∀ i, IsEntranceHistoryLocal (threeCurves β α γ i) h P)
    (htr : ∀ᵐ ω ∂P, ∀ i, Tendsto (threeCurves β α γ i ω) atTop (Bornology.cobounded ℂ)) {C : Ω → Set ℂ}
    (hCm : Measurable[MeasurableSpace.comap (explored (threeCurves β α γ) fun i _ => leftPairStops i)
      hittingSigma, hittingSigma] fun ω => H \ C ω)
    (hC : ∀ᵐ ω ∂P, C ω ⊆ H \ explored (threeCurves β α γ) (fun i _ => leftPairStops i) ω ∧
      ∀ z ∈ C ω, connectedComponentIn (H \ explored (threeCurves β α γ) (fun i _ => leftPairStops i) ω) z ⊆ C ω)
    (hCα : ∀ᵐ ω ∂P, Disjoint (C ω) (explored (threeCurves β α γ) (fun i _ => rightFlankStops i) ω))
    {g g₁ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (explored (threeCurves β α γ) fun _ _ => ⊤) h P g)
    (hg₁ : IsLocalSetMean (explored (threeCurves β α γ) fun i _ => leftPairStops i) h P g₁) :
    ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ C ω → g ω φ = g₁ ω φ := by
  have hg' : IsLocalSetMean (explored (threeCurves β α γ) fun i _ =>
      max (leftPairStops i) (rightFlankStops i)) h P g := by
    rw [max_leftPair_rightFlank]; exact hg
  exact ae_eq_on_explored_union_of_avoid (x := fun _ => 0) hh hc h0 hηm hdet hloc htr leftPairStops
    rightFlankStops hCm hC hCα hg' hg₁

end Full

end InteractingSLE.Sec6.Three
