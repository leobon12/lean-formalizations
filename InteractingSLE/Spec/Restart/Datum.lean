/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Topology.Germ
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import InteractingSLE.Spec.Theorem15Inputs

/-!
# The chart boundary datum of the first-contact restart

Packet PROVE-RESTART-CPL (Lemma 7.8 / Theorem W8 under the conditional law; design sketch in
`planning/handoffs/PROVE-SUPP10-B.md`). The conditional field in the first-contact chart is a GFF on `ℍ` whose boundary
data is a finite piecewise-constant word (supplement p. 541: "A filled real base is an interval; its two exterior ends
and the finitely many original marks create only finitely many genuine height changes"). The restart needs this word
as a **measurable** random datum, so it lives in a standard Borel space.

* `BoundaryWord = ℕ × (ℕ → ℝ) × (ℕ → ℝ)`: a length `n`, jump positions `p 0, …, p (n-1)` and heights
  `q 0, …, q n` (the later entries are ignored). It is a countable product of Polish spaces, hence standard Borel
  (instances found automatically).
* `BoundaryWord.fn c`: the boundary function, `q k` at `y` where `k` is the number of positions `p i < y`;
  `BoundaryWord.jumps c`: the positions. Every word is piecewise-constant data
  (`BoundaryWord.isPiecewiseConstantBoundaryData`), whether or not its positions are sorted.
* `BoundaryWord.exists_fn_eq` (**representation**): every finite piecewise-constant datum `(b, jumps)` is the datum of
  a word off `jumps`, with the same jump set.
* **Congruence**: the frozen predicates see the boundary function only off the jump set
  (`isGFFWithBoundaryData_congr`) and through its one-sided limits (`isFlowLine_congr`), and functions that agree off
  a finite set have the same one-sided limits (`leftLim_congr`, `rightLim_congr`). So a word represents its datum
  for every frozen predicate used in Theorem 1.5 (`isFlowLine_fn_iff`, `isGFFWithBoundaryData_fn_iff`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

/-! ### One-sided limits and the frozen predicates -/

/-- Functions that agree off a finite set are eventually equal on every punctured left neighbourhood. -/
theorem eventuallyEq_nhdsLT_of_eqOn_compl {b b' : ℝ → ℝ} {J : Finset ℝ} (hb : ∀ y ∉ J, b' y = b y)
    (y : ℝ) : b' =ᶠ[𝓝[<] y] b := by
  have hall : ∀ᶠ z in 𝓝[<] y, ∀ j ∈ J, z ≠ j := by
    refine (eventually_all_finset J).2 fun j _ => ?_
    by_cases hj : j = y
    · subst hj
      exact eventually_nhdsWithin_of_forall fun z hz => ne_of_lt hz
    · exact (eventually_ne_nhds (Ne.symm hj)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hall] with z hz
  exact hb z fun hzJ => hz z hzJ rfl

/-- Functions that agree off a finite set are eventually equal on every punctured right neighbourhood. -/
theorem eventuallyEq_nhdsGT_of_eqOn_compl {b b' : ℝ → ℝ} {J : Finset ℝ} (hb : ∀ y ∉ J, b' y = b y)
    (y : ℝ) : b' =ᶠ[𝓝[>] y] b := by
  have hall : ∀ᶠ z in 𝓝[>] y, ∀ j ∈ J, z ≠ j := by
    refine (eventually_all_finset J).2 fun j _ => ?_
    by_cases hj : j = y
    · subst hj
      exact eventually_nhdsWithin_of_forall fun z hz => ne_of_gt hz
    · exact (eventually_ne_nhds (Ne.symm hj)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hall] with z hz
  exact hb z fun hzJ => hz z hzJ rfl

/-- Functions that agree off a finite set have the same left limits everywhere. -/
theorem leftLim_congr {b b' : ℝ → ℝ} {J : Finset ℝ} (hb : ∀ y ∉ J, b' y = b y) :
    PiecewiseConstantBoundaryData.leftLim b' = PiecewiseConstantBoundaryData.leftLim b := by
  funext y
  show lim ((𝓝[<] y).map b') = lim ((𝓝[<] y).map b)
  rw [Filter.map_congr (eventuallyEq_nhdsLT_of_eqOn_compl hb y)]

/-- Functions that agree off a finite set have the same right limits everywhere. -/
theorem rightLim_congr {b b' : ℝ → ℝ} {J : Finset ℝ} (hb : ∀ y ∉ J, b' y = b y) :
    PiecewiseConstantBoundaryData.rightLim b' = PiecewiseConstantBoundaryData.rightLim b := by
  funext y
  show lim ((𝓝[>] y).map b') = lim ((𝓝[>] y).map b)
  rw [Filter.map_congr (eventuallyEq_nhdsGT_of_eqOn_compl hb y)]

/-- A bounded harmonic extension sees the boundary data only off the exceptional set. -/
theorem isBoundedHarmonicExtension_congr {g g' : ℝ → ℝ} {S : Set ℝ} (hg : ∀ y ∉ S, g' y = g y)
    (u : ℂ → ℝ) : IsBoundedHarmonicExtension g' S u ↔ IsBoundedHarmonicExtension g S u := by
  unfold IsBoundedHarmonicExtension
  refine and_congr_right' (and_congr_right' (forall₂_congr fun y hy => ?_))
  rw [hg y hy]

/-- `IsGFFWithBoundaryData` sees the boundary data only off the exceptional set. -/
theorem isGFFWithBoundaryData_congr {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) {g g' : ℝ → ℝ} {S : Set ℝ}
    (hg : ∀ y ∉ S, g' y = g y) :
    IsGFFWithBoundaryData P h g' S ↔ IsGFFWithBoundaryData P h g S := by
  unfold IsGFFWithBoundaryData
  simp only [isBoundedHarmonicExtension_congr hg]

/-- The body of the frozen `IsFlowLine`, written through the jump set `S` and the one-sided limits `L`, `R` of the
boundary data: `IsFlowLine κ b jumps = flowLineOf κ (jumpSet b jumps) (leftLim b) (rightLim b)` by definition
(`isFlowLine_eq_flowLineOf`). -/
def flowLineOf (κ : ℝ) (S : Finset ℝ) (L R : ℝ → ℝ) (x θ : ℝ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ)
    (ζ : Ω → ℝ≥0∞) : Prop :=
  ∃ (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin ((S.filter (· < x)).card + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin ((S.filter (x < ·)).card + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
    (∀ ω, IsTranslateAddConst x (θ * QuantumZipper.chiC κ) (h ω) (h' ω)) ∧
    IsOptionalHullCoupling κ
      (Fin.cons 0 fun i => (S.filter (· < x)).orderEmbOfFin rfl (Fin.rev i) - x)
      (Fin.cons 0 fun i => (S.filter (x < ·)).orderEmbOfFin rfl i - x)
      (Fin.cons (-(L x + θ * QuantumZipper.chiC κ) / sleLambda κ - 1) fun i =>
        let y := (S.filter (· < x)).orderEmbOfFin rfl (Fin.rev i)
        (R y - L y) / sleLambda κ)
      (Fin.cons ((R x + θ * QuantumZipper.chiC κ) / sleLambda κ - 1) fun i =>
        let y := (S.filter (x < ·)).orderEmbOfFin rfl i
        (R y - L y) / sleLambda κ)
      P 𝓕 W VL VR B ζ h' ∧
    ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η ω t - x)

theorem isFlowLine_eq_flowLineOf (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (x θ : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) :
    IsFlowLine κ b jumps x θ P h η ζ =
      flowLineOf κ (PiecewiseConstantBoundaryData.jumpSet b jumps)
        (PiecewiseConstantBoundaryData.leftLim b) (PiecewiseConstantBoundaryData.rightLim b) x θ P h η ζ :=
  rfl

/-- `IsFlowLine` sees the boundary data only through its jump set and its one-sided limits. -/
theorem isFlowLine_congr {κ : ℝ} {b b' : ℝ → ℝ} {jumps jumps' : Finset ℝ} {x θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hJ : PiecewiseConstantBoundaryData.jumpSet b' jumps' = PiecewiseConstantBoundaryData.jumpSet b jumps)
    (hL : PiecewiseConstantBoundaryData.leftLim b' = PiecewiseConstantBoundaryData.leftLim b)
    (hR : PiecewiseConstantBoundaryData.rightLim b' = PiecewiseConstantBoundaryData.rightLim b) :
    IsFlowLine κ b' jumps' x θ P h η ζ ↔ IsFlowLine κ b jumps x θ P h η ζ := by
  rw [isFlowLine_eq_flowLineOf, isFlowLine_eq_flowLineOf, hJ, hL, hR]

/-- For functions agreeing off a common finite set of possible jumps, the genuine jump sets agree. -/
theorem jumpSet_congr {b b' : ℝ → ℝ} {jumps : Finset ℝ} (hb : ∀ y ∉ jumps, b' y = b y) :
    PiecewiseConstantBoundaryData.jumpSet b' jumps = PiecewiseConstantBoundaryData.jumpSet b jumps := by
  unfold PiecewiseConstantBoundaryData.jumpSet
  rw [leftLim_congr hb, rightLim_congr hb]

/-- `IsFlowLine` for functions agreeing off the common finite set of possible jumps. -/
theorem isFlowLine_congr_of_eqOn {κ : ℝ} {b b' : ℝ → ℝ} {jumps : Finset ℝ} {x θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hb : ∀ y ∉ jumps, b' y = b y) :
    IsFlowLine κ b' jumps x θ P h η ζ ↔ IsFlowLine κ b jumps x θ P h η ζ :=
  isFlowLine_congr (jumpSet_congr hb) (leftLim_congr hb) (rightLim_congr hb)

/-! ### Boundary words -/

/-- A finite boundary word: a length `n`, jump positions `p 0, …, p (n-1)` and heights `q 0, …, q n`; entries
beyond these are ignored. A countable product of Polish spaces, hence a standard Borel space. -/
abbrev BoundaryWord : Type := ℕ × (ℕ → ℝ) × (ℕ → ℝ)

namespace BoundaryWord

/-- The number of jump positions strictly left of `y`. -/
def index (c : BoundaryWord) (y : ℝ) : ℕ := ((Finset.range c.1).filter fun i => c.2.1 i < y).card

/-- The boundary function of a word: the height `q k` at `y`, where `k` positions lie strictly left of `y`. -/
def fn (c : BoundaryWord) (y : ℝ) : ℝ := c.2.2 (c.index y)

/-- The jump positions of a word. -/
def jumps (c : BoundaryWord) : Finset ℝ := (Finset.range c.1).image c.2.1

theorem mem_jumps {c : BoundaryWord} {y : ℝ} : y ∈ c.jumps ↔ ∃ i < c.1, c.2.1 i = y := by
  simp [jumps]

/-- Off the jump positions, the index is locally constant. -/
theorem eventually_index_eq {c : BoundaryWord} {y : ℝ} (hy : y ∉ c.jumps) :
    ∀ᶠ z in 𝓝 y, c.index z = c.index y := by
  have hall : ∀ᶠ z in 𝓝 y, ∀ i ∈ Finset.range c.1, (c.2.1 i < z ↔ c.2.1 i < y) := by
    refine (eventually_all_finset _).2 fun i hi => ?_
    have hne : c.2.1 i ≠ y := fun he => hy (mem_jumps.2 ⟨i, Finset.mem_range.1 hi, he⟩)
    rcases hne.lt_or_gt with hlt | hgt
    · filter_upwards [lt_mem_nhds hlt] with z hz
      exact iff_of_true hz hlt
    · filter_upwards [gt_mem_nhds hgt] with z hz
      exact iff_of_false (not_lt.2 hz.le) (not_lt.2 hgt.le)
  filter_upwards [hall] with z hz
  unfold index
  congr 1
  exact Finset.filter_congr fun i hi => hz i hi

/-- **Every word is finite piecewise-constant boundary data.** -/
theorem isPiecewiseConstantBoundaryData (c : BoundaryWord) :
    IsPiecewiseConstantBoundaryData c.fn c.jumps := by
  intro y hy
  filter_upwards [eventually_index_eq hy] with z hz
  simp only [fn, hz]

theorem index_le (c : BoundaryWord) (y : ℝ) : c.index y ≤ c.1 :=
  (Finset.card_filter_le _ _).trans (Finset.card_range _).le

/-- For sorted positions, the first `index y` positions are exactly those strictly left of `y`. -/
theorem lt_index_iff {c : BoundaryWord} (hmono : StrictMonoOn c.2.1 (Iio c.1)) {y : ℝ} {i : ℕ}
    (hi : i < c.1) : i < c.index y ↔ c.2.1 i < y := by
  constructor
  · intro h
    by_contra hy
    have hsub : (Finset.range c.1).filter (fun j => c.2.1 j < y) ⊆ Finset.range i := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_range] at hj
      rw [Finset.mem_range]
      by_contra hji
      have hle : c.2.1 i ≤ c.2.1 j := hmono.monotoneOn hi hj.1 (not_lt.1 hji)
      exact hy (lt_of_le_of_lt hle hj.2)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    unfold index at h
    omega
  · intro h
    have hsub : Finset.range (i + 1) ⊆ (Finset.range c.1).filter (fun j => c.2.1 j < y) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, lt_of_le_of_lt ?_ h⟩
      exact hmono.monotoneOn (show j < c.1 by omega) hi (by omega)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    unfold index
    omega

/-- **Representation of piecewise-constant data by a word.** Every finite piecewise-constant datum `(b, J)` is, off
`J`, the boundary function of a word whose jump positions are `J` (sorted increasingly), with heights the values of
`b` at one point of each complementary interval. -/
theorem exists_fn_eq {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) :
    ∃ c : BoundaryWord, c.jumps = J ∧ ∀ y ∉ J, c.fn y = b y := by
  set n := J.card with hn
  set e := J.orderEmbOfFin rfl with he
  let p : ℕ → ℝ := fun i => if h : i < n then e ⟨i, h⟩ else 0
  have hp : ∀ i (hi : i < n), p i = e ⟨i, hi⟩ := fun i hi => by simp only [p, hi, ↓reduceDIte]
  have hpJ : ∀ i < n, p i ∈ J := fun i hi => by rw [hp i hi]; exact J.orderEmbOfFin_mem rfl _
  have hJp : ∀ z ∈ J, ∃ i < n, p i = z := by
    intro z hz
    obtain ⟨⟨i, hi⟩, rfl⟩ : z ∈ Set.range e := by rw [he, Finset.range_orderEmbOfFin]; exact hz
    exact ⟨i, hi, hp i hi⟩
  have hmono : StrictMonoOn p (Iio n) := by
    intro i hi j hj hij
    rw [hp i hi, hp j hj]
    exact e.strictMono (Fin.mk_lt_mk.2 hij)
  let s : ℕ → ℝ := fun k =>
    if k = 0 then p 0 - 1 else if k < n then (p (k - 1) + p k) / 2 else p (n - 1) + 1
  let c : BoundaryWord := (n, p, fun k => b (s k))
  refine ⟨c, ?_, ?_⟩
  · ext y
    simp only [c, jumps, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hpJ i hi
    · intro hy
      exact hJp y hy
  · intro y hy
    have hmono' : StrictMonoOn c.2.1 (Iio c.1) := hmono
    set k := c.index y with hk
    have hkn : k ≤ n := c.index_le y
    let I : Set ℝ := {z | (0 < k → p (k - 1) < z) ∧ (k < n → z < p k)}
    have hyI : y ∈ I := by
      refine ⟨fun hk0 => ?_, fun hkn' => ?_⟩
      · exact (lt_index_iff hmono' (show k - 1 < c.1 by simp only [c]; omega)).1 (by omega)
      · have hnot : ¬ c.2.1 k < y := fun hlt =>
          (lt_irrefl k) ((lt_index_iff hmono' (show k < c.1 from hkn')).2 hlt)
        have hne : y ≠ p k := fun he' => hy (he' ▸ hpJ k hkn')
        exact lt_of_le_of_ne (not_lt.1 hnot) hne
    have hsI : s k ∈ I := by
      by_cases hk0 : k = 0
      · refine ⟨fun h => absurd hk0 (Nat.pos_iff_ne_zero.1 h), fun _ => ?_⟩
        simp only [s, hk0, ↓reduceIte]
        linarith
      · by_cases hkn' : k < n
        · have hlt : p (k - 1) < p k := hmono (show k - 1 < n by omega) hkn' (by omega)
          simp only [s, hk0, hkn', ↓reduceIte]
          exact ⟨fun _ => by linarith, fun _ => by linarith⟩
        · have hkeq : k = n := le_antisymm hkn (not_lt.1 hkn')
          simp only [s, hk0, hkn', ↓reduceIte]
          refine ⟨fun _ => ?_, fun h => absurd h hkn'⟩
          rw [hkeq]
          linarith
    have hIJ : ∀ z ∈ I, z ∉ J := by
      intro z hz hzJ
      obtain ⟨i, hi, rfl⟩ := hJp z hzJ
      by_cases hik : i < k
      · have hle : p i ≤ p (k - 1) := hmono.monotoneOn hi (show k - 1 < n by omega) (by omega)
        exact absurd (lt_of_le_of_lt hle (hz.1 (by omega))) (lt_irrefl _)
      · have hkn' : k < n := lt_of_le_of_lt (not_lt.1 hik) hi
        have hle : p k ≤ p i := hmono.monotoneOn hkn' hi (not_lt.1 hik)
        exact absurd (lt_of_lt_of_le (hz.2 hkn') hle) (lt_irrefl _)
    have hIc : IsPreconnected I := by
      refine OrdConnected.isPreconnected ⟨fun a ha a' ha' z hz => ?_⟩
      exact ⟨fun h => lt_of_lt_of_le (ha.1 h) hz.1, fun h => lt_of_le_of_lt hz.2 (ha'.2 h)⟩
    have hconst : b (s k) = b y :=
      eq_of_germ_isConstant_on (fun z hz => ⟨b z, hb z (hIJ z hz)⟩) hIc hsI hyI
    exact hconst

/-- The word given by `exists_fn_eq` represents its datum for `IsGFFWithBoundaryData`. -/
theorem isGFFWithBoundaryData_fn_iff {b : ℝ → ℝ} {J : Finset ℝ} {c : BoundaryWord}
    (hcJ : c.jumps = J) (hcb : ∀ y ∉ J, c.fn y = b y) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) :
    IsGFFWithBoundaryData P h c.fn c.jumps ↔ IsGFFWithBoundaryData P h b J := by
  subst hcJ
  exact isGFFWithBoundaryData_congr P h fun y hy => hcb y (by exact_mod_cast hy)

/-- The word given by `exists_fn_eq` represents its datum for `IsFlowLine`. -/
theorem isFlowLine_fn_iff {b : ℝ → ℝ} {J : Finset ℝ} {c : BoundaryWord} (hcJ : c.jumps = J)
    (hcb : ∀ y ∉ J, c.fn y = b y) {κ x θ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} :
    IsFlowLine κ c.fn c.jumps x θ P h η ζ ↔ IsFlowLine κ b J x θ P h η ζ := by
  subst hcJ
  exact isFlowLine_congr_of_eqOn hcb

end BoundaryWord

end Restart

end InteractingSLE
