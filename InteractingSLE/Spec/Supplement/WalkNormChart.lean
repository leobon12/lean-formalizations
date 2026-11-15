/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkNormFacts

/-!
# Theorem 1.4's walk leaves: normalized component charts up to the choice of the logarithm

Packet PROVE-T14-WALKNORM. Lemma GW3, proof (p. 636): "The final component uniformizer therefore reflects with positive
derivative across this single connected interval. Choose its logarithm to have argument zero there." The lift of a
component chart is a continuous branch of `arg c.1′`, determined up to an additive constant in `2πℤ`; the normalization
of PROVE-T14-WALKBDRY's `IsNormChart` (lift differences tending to `0`) is the choice of that constant. This file
separates the choice from the geometry:

* `liftShift c n`: the chart `c` with its lift shifted by `2πn` — again a component chart
  (`isComponentChart_liftShift`);
* `IsPieceMatchLoc`, `IsRealMatchLoc`, `IsNormChartLoc … n`: `IsPieceMatch`, `IsRealMatch`, `IsNormChart` with
  * the transition in its local form (the inverse of the component chart maps an upper half-disc at `x` into the
    prefix chart's domain, and the transition has the limit `y` at `x`), and
  * the lift difference tending to `2πn` (resp. the lift tending to `−2πn` at a real match) for **one** integer `n`
    common to all matches of the component;
* **`isNormChart_of_loc`**: `IsNormChartLoc … t n → IsNormChart … (liftShift t.1 n, t.2)`;
* **`WalkNormChartLocStatement`** (named input, with the between-region path facts `WalkBetweenFacts` as an almost
  sure hypothesis) and **`walkNormChartStatement_of_loc`** (from it and the six statements giving those facts).

What remains in `WalkNormChartLocStatement` is the geometry of the matches and the coherence of the integers along the
whole boundary of the component (GW3: "Increase the retained prefixes. Their component logarithms agree on one
previously fixed compact incident collar, so agree everywhere"). At each single match the lift difference tends to
*some* `2πm` once the transition has real limits on a disc (`exists_int_tendsto_lift_sub`). Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Complex Metric
open scoped Real NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkNorm

open WalkLaw GW3Between LocalSets WalkMean WalkBdry

/-! ### Shifting the lift -/

/-- The chart `c` with its lift shifted by `2πn`. -/
def liftShift (c : Chart) (n : ℤ) : Chart := (c.1, c.2.1, fun z => c.2.2 z + 2 * π * n)

@[simp] theorem liftShift_fst (c : Chart) (n : ℤ) : (liftShift c n).1 = c.1 := rfl

@[simp] theorem liftShift_inv (c : Chart) (n : ℤ) : (liftShift c n).2.1 = c.2.1 := rfl

@[simp] theorem liftShift_lift (c : Chart) (n : ℤ) (z : ℂ) : (liftShift c n).2.2 z = c.2.2 z + 2 * π * n := rfl

/-- A component chart with its lift shifted by `2πn` is a component chart. -/
theorem isComponentChart_liftShift {R L C : Set ℂ} {c : Chart} (hc : IsComponentChart R L C c) (n : ℤ) :
    IsComponentChart R L C (liftShift c n) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc
  refine ⟨h1, h2, h3, h4, h5, h6.add continuousOn_const, fun z hz => ?_⟩
  change deriv c.1 z = (‖deriv c.1 z‖ : ℂ) * Complex.exp (((c.2.2 z + 2 * π * n : ℝ) : ℂ) * Complex.I)
  rw [h7 z hz]
  have he : Complex.exp (((c.2.2 z + 2 * π * n : ℝ) : ℂ) * Complex.I) = Complex.exp ((c.2.2 z : ℂ) * Complex.I) := by
    exact Complex.exp_eq_exp_iff_exists_int.mpr ⟨n, by push_cast; ring⟩
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]

/-! ### Matches with one integer -/

/-- **Prefix match, local form, with integer `n`**: `IsPieceMatch` with the transition `c'.1 ∘ c.2.1` given by its
germ (the prefix chart `c'` is conformal, the inverse of `c` maps `ℍ ∩ B(x, δ)` into the domain of the prefix
chart `c'`, and the transition tends to `y` at `x`) and the lift difference tending to `2πn`. -/
def IsPieceMatchLoc (s s' : ExplState) (left : Bool) (c : Chart) (x : ℝ) (n : ℤ) : Prop :=
  ∃ (pre post : List Piece) (pc : Piece) (τ : ℚ≥0) (y : ℝ) (p : ℂ) (r δ : ℝ),
    s.1 = pre ++ pc :: post ∧ (((τ : ℝ≥0)) : ℝ≥0∞) < pc.2.2 ∧
    (if left then IsLeftSidePt pc τ y else IsRightSidePt pc τ y) ∧
    Tendsto (prefixChart pc τ).2.1 (𝓝[H] (y : ℂ)) (𝓝 p) ∧ p ∈ wsetOf s ∪ {z : ℂ | z.im = 0} ∧
    0 < r ∧ wsetOf s ∩ ball p r ⊆ prefixSet pre pc τ ∧ wsetOf s' ∩ ball p r ⊆ wsetOf s ∧
    (prefixChart pc τ).IsConformal ∧
    0 < δ ∧ (∀ w ∈ H ∩ ball (x : ℂ) δ, c.2.1 w ∈ (prefixChart pc τ).dom) ∧
    Tendsto (fun w => (prefixChart pc τ).1 (c.2.1 w)) (𝓝[H] (x : ℂ)) (𝓝 (y : ℂ)) ∧
    Tendsto (fun w => (prefixChart pc τ).2.2 (c.2.1 w) - c.2.2 (c.2.1 w)) (𝓝[H] (x : ℂ)) (𝓝 (2 * π * n))

/-- **Real match with integer `n`**: `IsRealMatch` with the lift tending to `−2πn`. -/
def IsRealMatchLoc (sR sL : ExplState) (b : ℝ → ℝ) (jumps : Finset ℝ) (c : Chart) (x bx : ℝ) (n : ℤ) : Prop :=
  ∃ (a r : ℝ), a ∉ (jumps : Set ℝ) ∧ 0 < r ∧ Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (a : ℂ)) ∧
    Disjoint (ball (a : ℂ) r) (wsetOf sR ∪ wsetOf sL) ∧
    Tendsto (fun w => c.2.2 (c.2.1 w)) (𝓝[H] (x : ℂ)) (𝓝 (-(2 * π * n))) ∧ bx = b a

/-- **Normalized chart up to the logarithm**: `IsNormChart` with the local matches of one integer `n`. -/
def IsNormChartLoc (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (r : ExplState × ExplState) (C : Set ℂ)
    (t : Chart × (ℝ → ℝ) × Finset ℝ) (n : ℤ) : Prop :=
  IsComponentChart (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) r.1)
      (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) r.2) C t.1 ∧
    IsPiecewiseConstantBoundaryData t.2.1 t.2.2 ∧
    IsComponentBoundaryData κ b (ordOf r.1) (ordOf r.2) t.1.2.1 t.2.1 t.2.2 ∧
    ∃ Eℝ : Set ℝ, Eℝ.Finite ∧ ∀ x : ℝ, x ∉ Eℝ →
      (0 < x → (IsPieceMatchLoc r.1 r.2 true t.1 x n ∧ t.2.1 x = -bigLambda κ) ∨
        IsRealMatchLoc r.1 r.2 b jumps t.1 x (t.2.1 x) n) ∧
      (x < 0 → (IsPieceMatchLoc r.2 r.1 false t.1 x n ∧ t.2.1 x = bigLambda κ) ∨
        IsRealMatchLoc r.1 r.2 b jumps t.1 x (t.2.1 x) n)

theorem isPieceMatch_of_loc {s s' : ExplState} {left : Bool} {c : Chart} {x : ℝ} {n : ℤ}
    (h : IsPieceMatchLoc s s' left c x n) : IsPieceMatch s s' left (liftShift c n) x := by
  obtain ⟨pre, post, pc, τ, y, p, r, δ, h1, h2, h3, h4, h5, h6, h7, h8, hc', hδ, hsub, hT, hlift⟩ := h
  refine ⟨pre, post, pc, τ, y, p, r, h1, h2, h3, h4, h5, h6, h7, h8, hT,
    eventually_transition (c₁ := c) hc' hδ hsub, ?_⟩
  have := hlift.sub_const (2 * π * n)
  rw [sub_self] at this
  refine this.congr fun w => ?_
  simp only [liftShift_inv, liftShift_lift]
  ring

theorem isRealMatch_of_loc {sR sL : ExplState} {b : ℝ → ℝ} {jumps : Finset ℝ} {c : Chart} {x bx : ℝ} {n : ℤ}
    (h : IsRealMatchLoc sR sL b jumps c x bx n) : IsRealMatch sR sL b jumps (liftShift c n) x bx := by
  obtain ⟨a, r, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨a, r, h1, h2, h3, h4, ?_, h6⟩
  have := h5.add_const (2 * π * n)
  rw [neg_add_cancel] at this
  exact this

/-- **A normalized chart up to the logarithm gives a normalized chart** (shift the lift by `2πn`). -/
theorem isNormChart_of_loc {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {r : ExplState × ExplState} {C : Set ℂ}
    {t : Chart × (ℝ → ℝ) × Finset ℝ} {n : ℤ} (h : IsNormChartLoc κ b jumps r C t n) :
    IsNormChart κ b jumps r C (liftShift t.1 n, t.2) := by
  obtain ⟨h1, h2, h3, Eℝ, hE, hx⟩ := h
  refine ⟨isComponentChart_liftShift h1 n, h2, h3, Eℝ, hE, fun x hxE => ⟨fun hx0 => ?_, fun hx0 => ?_⟩⟩
  · rcases (hx x hxE).1 hx0 with ⟨hm, hv⟩ | hm
    · exact Or.inl ⟨isPieceMatch_of_loc hm, hv⟩
    · exact Or.inr (isRealMatch_of_loc hm)
  · rcases (hx x hxE).2 hx0 with ⟨hm, hv⟩ | hm
    · exact Or.inl ⟨isPieceMatch_of_loc hm, hv⟩
    · exact Or.inr (isRealMatch_of_loc hm)

/-! ### The named input -/

/-- **Named input: every component between the walks has a normalized chart up to the logarithm**:
`WalkBdry.WalkNormChartStatement` with `IsNormChart` replaced by `∃ n, IsNormChartLoc … n`, and with the
between-region path facts (`WalkBetweenFacts`: proper parametrizations, contact order, simple pieces, no common
continuum, the GW3 geometry — all derived in the wiring independently of this leaf) as an almost sure hypothesis. -/
def WalkNormChartLocStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
      (∀ᵐ ω ∂P, WalkBetweenFacts κ b jumps E ω) →
      ∀ᵐ ω ∂P, ∀ C ∈ betweenComponents
          (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1)
          (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2),
        ∃ (t : Chart × (ℝ → ℝ) × Finset ℝ) (n : ℤ), IsNormChartLoc κ b jumps (walkRuns κ b jumps E ω) C t n

/-- **`WalkBdry.WalkNormChartStatement` from its form up to the logarithm.** -/
theorem walkNormChartStatement_of_loc (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u}) (hCO : GW4BarrierSelf.WalkContactOrderRegStatement.{u})
    (hS : GW1Z.GW1PieceSimpleStatement.{u}) (hNC : WalkCont.WalkNoCommonContinuumRegStatement.{u})
    (hG : GW3Sided.GW3GeometryRegStatement.{u}) (hN : WalkNormChartLocStatement.{u}) :
    WalkNormChartStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR hreg
  filter_upwards [hN κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR hreg
    (ae_walkBetweenFacts hPR hPL hCO hS hNC hG hκ hκ4 hb hh hcf hζ' hE hR hreg)] with ω hω C hC
  obtain ⟨t, n, ht⟩ := hω C hC
  exact ⟨_, isNormChart_of_loc ht⟩

end InteractingSLE.Theorem14.WalkNorm
