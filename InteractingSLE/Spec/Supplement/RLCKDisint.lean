/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCKLift
import InteractingSLE.Spec.Supplement.RLCFAvg

/-!
# Lemma G8: the disintegration of the good-frame event and the choice of one datum

Packet PROVE-RLC-K, item (e) of `planning/handoffs/PROVE-RLC-G.md`. Source: proof of Lemma G8, "Small-gap frames and
disintegration" (supplement pp. 500–501): "For any prescribed `ε > 0`, continuity before the contact and a countable
union give fixed rational own times `s, t` at which the history-measurable good-frame event
`0 < v_R − w_α < ε(w_α − w_β)` has positive probability, with both tips interior and active. Retain only these two
stopped histories […] The conditional original pair remains ordered because that was an unconditional probability-one
property of the reference […] G7 supplies the stopped conditional continuation laws. Choose one datum in this
positive-probability set where all those conditional assertions hold."

* `G8DatumStatement`: Lemma G8 at chart coordinates with one coupling (the conditional pair of one datum);
  **`g8ChartRefStatement_of_datum`**, **`g8FrameStatement_of_datum`**: with Lemma 7.5 (`isRefFrame_of_one`) and the
  affine normalization (`g8FrameStatement_of_chartRef`) it gives `G8FrameStatement`;
* `seedCollars_of_seedGerm`: certified seed germs give seed collars;
* `retHistStop`, `histSigma`: the retained histories and their σ-algebra; `RetainedPairRestartCondStatement`
  (**named**): G7's retained-pair restart **conditionally on the retained histories** (the restart kernel is the
  conditional law of the chart continuations given every history event of the ordinary event), with
  `retainedPairRestartUntouchedStatement_of_cond` (it implies RLC-E's input);
* `IsGoodFrame`, `G8PositivityStatement` (**named**, G8's positivity: the swallow, GB1 and the joint activity);
* **`exists_good_datum`**: the choice of one datum from a conditional law on a positive-probability event;
* **`g8DatumStatement_of_parts`**: `G8DatumStatement` from Proposition 7.4's complete ordered reference
  (`Prop74RefStatement`), the conditional restart, the positivity and Lemma G9 (`G9LiftStatement`).

**Why the conditional form.** `RetainedPairRestartUntouchedStatement` gives a kernel `K` disintegrating the law of
(datum, chart continuations) only on an event `M` that contains the ordinary event and is otherwise unspecified; on
`M` minus the ordinary event its chart continuations are not related to the reference curves. G8 conditions on a
positive-probability *history* event (the good frame) on which G9 holds pathwise; the datum-level kernel of an
uncontrolled `M` mixes it with the rest of `M`, so only "`K c` has positive probability of the completion property"
would follow. The source's G7 is the conditional law given the retained histories, which is the stated form.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Theorem15D5 Sec2.Assembly Supp7 Supp9D Restart

/-! ### Lemma G8 with one coupling -/

/-- **Lemma G8 at chart coordinates, for one coupling** (the conditional pair of one retained datum): as
`G8ChartRefStatement`, with the reference property for one coupling of the GFF with the two flows. -/
def G8DatumStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ C ε : ℝ, θ₁ < θ₂ → 0 < ε →
    -2 < Sec4.cumWeightRight κ (C + θ₁ * QuantumZipper.chiC κ) →
    Sec4.cumWeightRight κ (C + θ₁ * QuantumZipper.chiC κ) < κ / 2 - 2 →
    ∃ (c : ℝ → ℝ) (Ĵ : Finset ℝ) (w v δ : ℝ), 0 < w ∧ w < v ∧ v < w + ε * w ∧ 0 < δ ∧
      IsPiecewiseConstantBoundaryData c Ĵ ∧ SeedCollars κ θ₁ θ₂ c Ĵ 0 w δ ∧
      (∀ x, v < x → c x = C ∧ x ∉ Ĵ) ∧
      ∃ (S₀ : Type u) (_ : MeasurableSpace S₀) (Q₀ : Measure S₀) (_ : IsProbabilityMeasure Q₀)
        (H₀ : S₀ → LQGMetric.DistOn upperHalfPlaneOpens) (Γ₁ Γ₂ : S₀ → ℝ≥0 → ℂ) (U₁ U₂ : S₀ → ℝ≥0∞),
        IsGFFWithBoundaryData Q₀ H₀ c Ĵ ∧ IsFlowLine κ c Ĵ w θ₁ Q₀ H₀ Γ₁ U₁ ∧
        IsFlowLine κ c Ĵ 0 θ₂ Q₀ H₀ Γ₂ U₂ ∧ ∀ᵐ x ∂Q₀, RefCompletable (Ioi v) (Γ₁ x) (U₁ x) (Γ₂ x) (U₂ x)

/-- **Lemma G8 at chart coordinates from one coupling**, by Lemma 7.5 (`isRefFrame_of_one`). -/
theorem g8ChartRefStatement_of_datum (h75 : Theorem15.Lemma75Statement.{u}) (hD : G8DatumStatement.{u}) :
    G8ChartRefStatement.{u} := by
  intro κ hκ hκ4 θ₁ θ₂ C ε hθ hε hr₁ hr₂
  obtain ⟨c, Ĵ, w, v, δ, hw, hwv, hvε, hδ, hc, hS, hC, S₀, _, Q₀, _, H₀, Γ₁, Γ₂, U₁, U₂, hH, h₁, h₂, href⟩ :=
    hD κ hκ hκ4 θ₁ θ₂ C ε hθ hε hr₁ hr₂
  exact ⟨c, Ĵ, w, v, δ, hw, hwv, hvε, hδ, hc, hS, hC,
    isRefFrame_of_one h75 hκ hκ4 hc Q₀ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂ href⟩

/-- **Lemma G8 (with G9)** from its one-coupling chart form, Lemma 7.5 and the affine normalization. -/
theorem g8FrameStatement_of_datum (h75 : Theorem15.Lemma75Statement.{u}) (hD : G8DatumStatement.{u}) :
    G8FrameStatement.{u} :=
  g8FrameStatement_of_chartRef (g8ChartRefStatement_of_datum h75 hD)

/-! ### Seed collars from certified seed germs -/

/-- **Certified seed germs give seed collars** of radius `min q (min (w − q₁) (q₂ − w))`. -/
theorem seedCollars_of_seedGerm {κ θ₁ θ₂ q q₁ q₂ w : ℝ} {c : BoundaryWord} (hκ : 0 < κ)
    (h : SeedGerm κ θ₁ θ₂ q q₁ q₂ c w) :
    0 < min q (min (w - q₁) (q₂ - w)) ∧ SeedCollars κ θ₁ θ₂ c.fn c.jumps 0 w (min q (min (w - q₁) (q₂ - w))) := by
  obtain ⟨h0, h1, h2, h3, -⟩ := id h
  set δ := min q (min (w - q₁) (q₂ - w)) with hδ
  have e1 : δ ≤ q := min_le_left _ _
  have e2 : δ ≤ w - q₁ := (min_le_right _ _).trans (min_le_left _ _)
  have e3 : δ ≤ q₂ - w := (min_le_right _ _).trans (min_le_right _ _)
  have hδ0 : 0 < δ := lt_min h0 (lt_min (by linarith) (by linarith))
  refine ⟨hδ0, fun x hx1 hx2 => h.fn_neg (by linarith) hx2, fun x hx1 hx2 => h.fn_pos hx1 (by linarith),
    fun x hx1 hx2 => h.fn_left (by linarith) hx2, fun x hx1 hx2 => h.fn_right hx1 (by linarith), ?_, ?_⟩
  · intro x hx hxd
    rw [sub_zero, abs_lt] at hxd
    rcases (h.mem_jumps_iff hκ (Or.inl ⟨by linarith, by linarith⟩)).1 hx with h' | h'
    · exact h'
    · exfalso; rw [h'] at hxd; linarith [hxd.2]
  · intro x hx hxd
    rw [abs_lt] at hxd
    rcases (h.mem_jumps_iff hκ (Or.inr ⟨by linarith, by linarith⟩)).1 hx with h' | h'
    · exfalso; rw [h'] at hxd; linarith [hxd.1]
    · exact h'

/-! ### The conditional restart -/

/-- The retained histories: the two prefixes, stopped at their cutoffs. -/
def retHistStop {Ω : Type*} (d : RetData Ω) (ω : Ω) : (ℝ≥0 → ℂ) × (ℝ≥0 → ℂ) :=
  (fun t => d.η₁ ω (min t d.u), fun t => d.η₂ ω (min t d.r))

/-- **The σ-algebra of the retained histories**: generated by the stopped prefixes and the good event. -/
abbrev histSigma {Ω : Type*} (d : RetData Ω) : MeasurableSpace Ω :=
  MeasurableSpace.comap (retHistStop d) inferInstance ⊔ MeasurableSpace.generateFrom {d.G}

/-- **Named input: Lemma G7's retained-pair restart conditionally on the retained histories** (supplement
pp. 497–498; proof of Lemma G8, p. 501: "Retain only these two stopped histories […] G7 supplies the stopped
conditional continuation laws"). `RetainedPairRestartUntouchedStatement`, and moreover the restart kernel is the
conditional law of the chart continuations given the retained histories on the ordinary event: for every event `B` of
the retained histories (`histSigma d`) contained almost surely in the ordinary event, the law of (datum, continuations)
restricted to `B` is the law of the datum on `B` composed with `K`. **Not proved in Lean.** -/
def RetainedPairRestartCondStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∃ (S : Type) (_ : MeasurableSpace S) (H : S → LQGMetric.DistOn upperHalfPlaneOpens) (Γ₁ Γ₂ : S → ℝ≥0 → ℂ)
      (U₁ U₂ : S → ℝ≥0∞) (M : Set Ω) (β : Ω → BoundaryWord × ℝ) (X : Ω → S)
      (K : Kernel (BoundaryWord × ℝ) S),
      IsRestartCoordinates H Γ₁ Γ₂ U₁ U₂ ∧ MeasurableSet M ∧ Measurable β ∧ Measurable X ∧
      IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K ∧
      (∀ᵐ c ∂(P.restrict M).map β, 0 < c.2 ∧ IsGFFWithBoundaryData (K c) H c.1.fn c.1.jumps ∧
        IsFlowLine κ c.1.fn c.1.jumps c.2 θ₁ (K c) H Γ₁ U₁ ∧ IsFlowLine κ c.1.fn c.1.jumps 0 θ₂ (K c) H Γ₂ U₂) ∧
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        ω ∈ M ∧ H (X ω) = hd.chartField κ h ω ∧
        IsRetainedClock (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω)
          (Γ₁ (X ω)) (U₁ (X ω)) ∧
        IsRetainedClock (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω)
          (Γ₂ (X ω)) (U₂ (X ω)) ∧
        IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1) ∧
      ∀ B : Set Ω, MeasurableSet[histSigma d] B →
        (∀ᵐ ω ∂P, ω ∈ B → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r) →
        (P.restrict B).map (fun ω => (β ω, X ω)) = (P.restrict B).map β ⊗ₘ K

/-- The conditional restart implies RLC-E's retained-pair restart with the untouched word. -/
theorem retainedPairRestartUntouchedStatement_of_cond (hR : RetainedPairRestartCondStatement.{u}) :
    RetainedPairRestartUntouchedStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag
  obtain ⟨S, mS, H, Γ₁, Γ₂, U₁, U₂, M, β, X, K, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ :=
    hR κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag
  exact ⟨S, mS, H, Γ₁, Γ₂, U₁, U₂, M, β, X, K, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ### The good frame and its positivity -/

/-- **The good frame** at a retained pair with chart inverse `ψ` (proof of G8, pp. 500–501): if `w` is the chart
coordinate of the first tip (`ψ w = α(u)`), every chart real point beyond `w + εw` lies over a positive original real
point off the retained union (the right junction `v_R` lies before `w + εw`, i.e. `0 < v_R − w_α < ε(w_α − w_β)` with
`w_β = 0`, and `(v_R, ∞)` is untouched original real boundary). -/
def IsGoodFrame (ε : ℝ) (α : ℝ≥0 → ℂ) (u : ℝ≥0) (β : ℝ≥0 → ℂ) (r : ℝ≥0) (ψ : ℂ → ℂ) : Prop :=
  ∀ w : ℝ, ψ w = α u → ∀ y : ℝ, w + ε * w < y →
    (ψ y).im = 0 ∧ 0 < (ψ y).re ∧ ψ y ∉ α '' Icc 0 u ∪ β '' Icc 0 r

/-- **Named input: the positivity part of Lemma G8's proof** (supplement pp. 499–501: "a reference and a
positive-probability swallow", the final interior approach, GB1, Aux. lemmas 85 and 90). For the reference of
Proposition 7.4 with data `−a` on `ℝ₋`, `C` on `ℝ₊` (`a = 2λ + θ₂χ`) and its complete ordered pair, and every
`ε > 0`, there are deterministic own times `(u, r)` such that for every retained datum at these cutoffs the event of
the retained histories on which the pair is ordinary and the frame is good has positive probability. **Not proved in
Lean** (landed pieces: the swallow `RLCJ.ae_flowLine_swallow_landing`, GB1 `GB1.frequently_ratio_lt`, the tip
avoidance `RLCJ.ae_flowLine_ne_tip_of_restart`). -/
def G8PositivityStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ C : ℝ, θ₁ < θ₂ →
    -2 < Sec4.cumWeightRight κ (C + θ₁ * QuantumZipper.chiC κ) →
    Sec4.cumWeightRight κ (C + θ₁ * QuantumZipper.chiC κ) < κ / 2 - 2 →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h (Sec7.prop74Data (2 * sleLambda κ + θ₂ * QuantumZipper.chiC κ) C)
        ((({0} : Finset ℝ)) : Set ℝ) →
    ∀ (α β : Ω → ℝ≥0 → ℂ) (ζα ζβ : Ω → ℝ≥0∞),
      IsFlowLine κ (Sec7.prop74Data (2 * sleLambda κ + θ₂ * QuantumZipper.chiC κ) C) {0} 0 θ₁ P h α ζα →
      IsFlowLine κ (Sec7.prop74Data (2 * sleLambda κ + θ₂ * QuantumZipper.chiC κ) C) {0} 0 θ₂ P h β ζβ →
      (∀ᵐ ω ∂P, ζα ω = ⊤ ∧ ζβ ω = ⊤ ∧ Sec7.Prop74Order.IsCompleteOrderedPair (α ω) (β ω)) →
    ∀ ε : ℝ, 0 < ε → ∃ u r : ℝ≥0, ∀ d : RetData Ω, d.IsMeasGood → d.u = u → d.r = r →
      (∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζα ω → (r : ℝ≥0∞) < ζβ ω → ω ∈ d.G ∧
        (∀ s ≤ u, d.η₁ ω s = α ω s) ∧ ∀ t ≤ r, d.η₂ ω t = β ω t) →
      ∃ B : Set Ω, MeasurableSet[histSigma d] B ∧ P B ≠ 0 ∧
        ∀ᵐ ω ∂P, ω ∈ B → IsOrdinaryRetainedPair (α ω) (ζα ω) u (β ω) (ζβ ω) r ∧
          IsGoodFrame ε (α ω) u (β ω) r (d.inv ω)

/-! ### Choosing one datum -/

/-- **Choosing one datum from a conditional law on a positive-probability event.** If on `B` (`P(B) > 0`, `B ⊆ M`
almost surely) the law of `(β, X)` is the law of `β` composed with `K`, the event `E` is universally measurable and
holds almost surely on `B`, a datum property holds almost surely on `B`, and a kernel property holds for almost every
datum of `M`, then one datum has all three: the kernel property, the datum property, and `E` under `K c`. -/
theorem exists_good_datum {Ω C S : Type*} [MeasurableSpace Ω] [MeasurableSpace C] [MeasurableSpace S]
    {P : Measure Ω} [IsFiniteMeasure P] {M B : Set Ω} (hB : MeasurableSet B) {β : Ω → C} {X : Ω → S}
    (hβ : Measurable β) (hX : Measurable X) {K : Kernel C S} [IsMarkovKernel K]
    (hlawB : (P.restrict B).map (fun ω => (β ω, X ω)) = (P.restrict B).map β ⊗ₘ K)
    (hBM : ∀ᵐ ω ∂P, ω ∈ B → ω ∈ M) (hBpos : P B ≠ 0) {R : C → Prop} (hR : ∀ᵐ c ∂(P.restrict M).map β, R c)
    {Dat : C → Prop} (hDat : ∀ᵐ ω ∂P, ω ∈ B → Dat (β ω)) {E : Set (C × S)} (hE : LQGMetric.UMeasurableSet E)
    (hEB : ∀ᵐ ω ∂P, ω ∈ B → (β ω, X ω) ∈ E) :
    ∃ c, R c ∧ Dat c ∧ ∀ᵐ s ∂(K c), (c, s) ∈ E := by
  set ν := (P.restrict B).map β with hν
  -- `E` holds almost surely under `ν ⊗ K`
  have h1 : ∀ᵐ p ∂(ν ⊗ₘ K), p ∈ E := by
    have hlaw' : (ν ⊗ₘ K).map id = (P.restrict B).map (fun ω => (β ω, X ω)) := by
      rw [Measure.map_id, hlawB]
    have := ae_mem_of_map_eq_of_uMeasurable hE (hβ.prodMk hX) measurable_id hlaw'
      ((ae_restrict_iff'₀ hB.nullMeasurableSet).2 hEB)
    simpa using this
  have h2 : ∀ᵐ c ∂ν, ∀ᵐ s ∂(K c), (c, s) ∈ E := Measure.ae_ae_of_ae_compProd h1
  -- the kernel property passes to `ν`
  have hle : P.restrict B ≤ P.restrict M := Measure.restrict_mono_ae hBM
  have hac : ν ≪ (P.restrict M).map β := Measure.absolutelyContinuous_of_le (Measure.map_mono hle hβ)
  have h3 : ∀ᵐ c ∂ν, R c := hac.ae_le hR
  have h4 : ∀ᵐ ω ∂(P.restrict B), R (β ω) ∧ ∀ᵐ s ∂(K (β ω)), (β ω, s) ∈ E :=
    ae_of_ae_map hβ.aemeasurable (h3.and h2)
  have h5 : ∀ᵐ ω ∂(P.restrict B), Dat (β ω) := (ae_restrict_iff'₀ hB.nullMeasurableSet).2 hDat
  have hne : P.restrict B ≠ 0 := by
    intro h0
    apply hBpos
    have := congrArg (fun μ : Measure Ω => μ univ) h0
    simpa [Measure.restrict_apply MeasurableSet.univ] using this
  have : (ae (P.restrict B)).NeBot := ae_neBot.2 hne
  obtain ⟨ω, ⟨hRω, hEω⟩, hDω⟩ := (h4.and h5).exists
  exact ⟨β ω, hRω, hDω, hEω⟩

end RLC

end InteractingSLE
