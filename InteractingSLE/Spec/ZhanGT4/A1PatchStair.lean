/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualCols
import InteractingSLE.Spec.ZhanGT4.DualFubiniOuter
import InteractingSLE.Spec.ZhanGT4.A1CoreInputs
import InteractingSLE.Spec.ZhanGT4.A1LawPatch

/-!
# A.1's finite seeded patches: the staircase coupling of finitely many protected rectangles

Packet PROVE-A1-PATCH (R80, input (I1) of `A1Law.PatchInput`). Sources: Astra, *Follow-up proofs* §A.1.4
(`ig1_followup_proofs.txt` L363–L407): the staircase density (D11) of finitely many protected rectangles, its adapted
verification (D12), "Thus `M*(s, t̄)` is a bounded martingale. Reflection of the construction proves the corresponding
martingale in the other coordinate. In particular `M*(∞, ∞)` is a positive probability density with unchanged marginal
laws, and its restriction to each stopped rectangle has density `M(S₁ᵐ, S₂ᵐ)`"; *Follow-up 4* §2.5 item 4
(`ig1_followup4_audited.txt` L789–L796): "the staircase density (D11)–(D12) … uses only coordinate martingales and their
axis values. … Each finite patch therefore has the two prescribed marginals and the prescribed joint stopped law on each
included rectangle. One way to check the latter identity is to condition first at the first curve's enclosure stop
while keeping the entire second path fixed, and then condition at the second enclosure stop while keeping the first
path fixed. Separate optional sampling reduces the terminal patched density to `M(S₁, S₂)` on that rectangle";
*Follow-up 5* §1.3 (L203–L211): "a continuous joint density `M(s, t)`, bounded above and below by positive constants,
with axis values one and the two coordinate martingale identities".

Setting: two probability laws `P₁` on `X` (curve `1`) and `P₂` on `Y` (curve `2`) with filtrations `𝓕₁`, `𝓕₂`, and a
two-time field `N ω s t` on `X × Y` (the source's normalized density `M(s, t)` of the pair of paths `ω`). A protected
rectangle (`IsRectField`) is a pair of bounded stopping times `S₁ : X → ℝ≥0`, `S₂ : Y → ℝ≥0` on which `N` is bounded
above and below by positive constants and has the two coordinate martingale identities:

* with the whole second path `y` fixed, `s ↦ N((x, y), s ∧ S₁ x, S₂ y)` is a `P₁`-martingale (A14's frozen-height
  process; the second hull frozen at its exit);
* with the whole first path `x` fixed, `t ↦ N((x, y), a, t ∧ S₂ y)` is a `P₂`-martingale for every `a ≤ S₁ x` (the first
  hull frozen at a time `a` before its exit).

For finitely many protected rectangles the patched field `stairField N S₁ S₂ ω s t` (A14's (D11) `patch` of `N ω` over
the staircase of the rectangles of `ω`) defines the coupling `stairCoupling = M*(U, U) · (P₁ ⊗ P₂)`.

## Main results

* `measurable_stairField`: the patched field at measurable random times is measurable (`IsFieldMeas`);
* `setLIntegral_stairField_col`, `setLIntegral_stairField_row`: the two optional samplings (A14's column martingale
  with the second path fixed; its reflection with the first path fixed);
* **`stairCoupling_map_fst`**, **`stairCoupling_map_snd`**, `isProbabilityMeasure_stairCoupling`: the coupling has the
  two unchanged marginals;
* **`rectDens_stairCoupling`**: on every rectangle `i`, the density identity (1.7) `RectDens` for the two stopped
  σ-algebras `𝓕¹_{S₁ i} ⊗ 𝓕²_{S₂ i}` with density `N(S₁ i, S₂ i)`.
-/

set_option autoImplicit false

noncomputable section

open Set Finset Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Patch

open A1Law

/-! ### The field, its staircase and measurability -/

section Field

variable {X Y : Type*} {ι : Type*}

/-- **The patched field (D11)** of the two-time field `N` over the staircase of the rectangles
`[0, S₁ i x] × [0, S₂ i y]` of the pair of paths `ω = (x, y)`. -/
def stairField [Fintype ι] (N : X × Y → ℝ → ℝ → ℝ) (S₁ : ι → X → ℝ≥0) (S₂ : ι → Y → ℝ≥0) (ω : X × Y)
    (s t : ℝ) : ℝ :=
  patch (fun i => (S₁ i ω.1 : ℝ)) (fun i => (S₂ i ω.2 : ℝ)) (N ω) s t

/-- **Measurability of the field on the rectangles**: `N` is measurable at every pair of measurable random times that
lies, for every `ω`, in one of the rectangles `[0, S₁ i ω.1] × [0, S₂ i ω.2]`. (Joint measurability of `N` gives it:
`isFieldMeas_of_measurable`.) -/
def IsFieldMeas [MeasurableSpace X] [MeasurableSpace Y] (N : X × Y → ℝ → ℝ → ℝ) (S₁ : ι → X → ℝ≥0)
    (S₂ : ι → Y → ℝ≥0) : Prop :=
  ∀ U V : X × Y → ℝ, Measurable U → Measurable V → (∀ ω, 0 ≤ U ω) → (∀ ω, 0 ≤ V ω) →
    (∀ ω, ∃ i, U ω ≤ S₁ i ω.1 ∧ V ω ≤ S₂ i ω.2) → Measurable fun ω => N ω (U ω) (V ω)

variable [MeasurableSpace X] [MeasurableSpace Y]

/-- A jointly measurable field is measurable on the rectangles. -/
theorem isFieldMeas_of_measurable {N : X × Y → ℝ → ℝ → ℝ}
    (hN : Measurable fun q : (X × Y) × ℝ × ℝ => N q.1 q.2.1 q.2.2) (S₁ : ι → X → ℝ≥0) (S₂ : ι → Y → ℝ≥0) :
    IsFieldMeas N S₁ S₂ := fun _ _ hU hV _ _ _ =>
  hN.comp (measurable_id.prodMk (hU.prodMk hV))

/-- Measurability on the rectangles passes to a subfamily of rectangles. -/
theorem IsFieldMeas.comp {ι' : Type*} {N : X × Y → ℝ → ℝ → ℝ} {S₁ : ι → X → ℝ≥0} {S₂ : ι → Y → ℝ≥0}
    (h : IsFieldMeas N S₁ S₂) (e : ι' → ι) : IsFieldMeas N (fun j => S₁ (e j)) (fun j => S₂ (e j)) :=
  fun U V hU hV hU0 hV0 hUV => h U V hU hV hU0 hV0 fun ω => by
    obtain ⟨j, h1, h2⟩ := hUV ω
    exact ⟨e j, h1, h2⟩

variable [Fintype ι]

/-- **The patched field at measurable random times is measurable**: `patchLog` is a weighted sum over the indices
(`sum_stairCols_eq`) of differences of `log N` at random points of the staircase (`inStair_args`). -/
theorem measurable_stairField {N : X × Y → ℝ → ℝ → ℝ} {S₁ : ι → X → ℝ≥0} {S₂ : ι → Y → ℝ≥0}
    (hS₁ : ∀ i, Measurable fun x => (S₁ i x : ℝ)) (hS₂ : ∀ i, Measurable fun y => (S₂ i y : ℝ))
    (hN : IsFieldMeas N S₁ S₂) {s t : X × Y → ℝ} (hs : Measurable s) (ht : Measurable t) (hs0 : ∀ ω, 0 ≤ s ω)
    (ht0 : ∀ ω, 0 ≤ t ω) : Measurable fun ω => stairField N S₁ S₂ ω (s ω) (t ω) := by
  classical
  have hA : ∀ i, Measurable fun ω : X × Y => (S₁ i ω.1 : ℝ) := fun i => (hS₁ i).comp measurable_fst
  have hB : ∀ i, Measurable fun ω : X × Y => (S₂ i ω.2 : ℝ) := fun i => (hS₂ i).comp measurable_snd
  have hH : ∀ i, Measurable fun ω : X × Y =>
      stairH (fun j => (S₁ j ω.1 : ℝ)) (fun j => (S₂ j ω.2 : ℝ)) (S₁ i ω.1) := fun i =>
    measurable_stairH hA hB (hA i)
  have hP : ∀ i, Measurable fun ω : X × Y => prevIn (stairCols fun j => (S₁ j ω.1 : ℝ)) (S₁ i ω.1) := fun i =>
    measurable_prevIn_stairCols hA (hA i)
  have hpt : ∀ ω : X × Y, ∀ i, InStair (fun j => (S₁ j ω.1 : ℝ)) (fun j => (S₂ j ω.2 : ℝ))
      (min (S₁ i ω.1 : ℝ) (s ω)) (min (stairH (fun j => (S₁ j ω.1 : ℝ)) (fun j => (S₂ j ω.2 : ℝ)) (S₁ i ω.1))
        (t ω)) ∧
      InStair (fun j => (S₁ j ω.1 : ℝ)) (fun j => (S₂ j ω.2 : ℝ))
        (min (prevIn (stairCols fun j => (S₁ j ω.1 : ℝ)) (S₁ i ω.1)) (s ω))
        (min (stairH (fun j => (S₁ j ω.1 : ℝ)) (fun j => (S₂ j ω.2 : ℝ)) (S₁ i ω.1)) (t ω)) := fun ω i =>
    inStair_args (fun j => (S₂ j ω.2).coe_nonneg) (mem_stairCols i) (S₁ i ω.1).coe_nonneg _ _
  have hN1 : ∀ i, Measurable fun ω : X × Y => Real.log (N ω (min (S₁ i ω.1 : ℝ) (s ω))
      (min (stairH (fun j => (S₁ j ω.1 : ℝ)) (fun j => (S₂ j ω.2 : ℝ)) (S₁ i ω.1)) (t ω))) := fun i =>
    Real.measurable_log.comp (hN _ _ ((hA i).min hs) ((hH i).min ht)
      (fun ω => le_min (S₁ i ω.1).coe_nonneg (hs0 ω)) (fun ω => le_min (stairH_nonneg _) (ht0 ω))
      (fun ω => (hpt ω i).1))
  have hN2 : ∀ i, Measurable fun ω : X × Y => Real.log (N ω
      (min (prevIn (stairCols fun j => (S₁ j ω.1 : ℝ)) (S₁ i ω.1)) (s ω))
      (min (stairH (fun j => (S₁ j ω.1 : ℝ)) (fun j => (S₂ j ω.2 : ℝ)) (S₁ i ω.1)) (t ω))) := fun i =>
    Real.measurable_log.comp (hN _ _ ((hP i).min hs) ((hH i).min ht)
      (fun ω => le_min (prevIn_nonneg _ _) (hs0 ω)) (fun ω => le_min (stairH_nonneg _) (ht0 ω))
      (fun ω => (hpt ω i).2))
  have e : (fun ω => stairField N S₁ S₂ ω (s ω) (t ω)) = fun ω => Real.exp (∑ i,
      (Real.log (N ω (min (S₁ i ω.1 : ℝ) (s ω))
          (min (stairH (fun j => (S₁ j ω.1 : ℝ)) (fun j => (S₂ j ω.2 : ℝ)) (S₁ i ω.1)) (t ω))) -
        Real.log (N ω (min (prevIn (stairCols fun j => (S₁ j ω.1 : ℝ)) (S₁ i ω.1)) (s ω))
          (min (stairH (fun j => (S₁ j ω.1 : ℝ)) (fun j => (S₂ j ω.2 : ℝ)) (S₁ i ω.1)) (t ω)))) /
      ((univ.filter fun j => (S₁ j ω.1 : ℝ) = S₁ i ω.1).card : ℝ)) := by
    funext ω
    unfold stairField patch patchLog
    rw [sum_stairCols_eq (fun i => (S₁ i ω.1 : ℝ)) fun c =>
      Real.log (N ω (min c (s ω)) (min (stairH (fun j => (S₁ j ω.1 : ℝ)) (fun j => (S₂ j ω.2 : ℝ)) c) (t ω))) -
        Real.log (N ω (min (prevIn (stairCols fun j => (S₁ j ω.1 : ℝ)) c) (s ω))
          (min (stairH (fun j => (S₁ j ω.1 : ℝ)) (fun j => (S₂ j ω.2 : ℝ)) c) (t ω)))]
  rw [e]
  exact Real.measurable_exp.comp (Finset.measurable_sum _ fun i _ =>
    ((hN1 i).sub (hN2 i)).div (measurable_card_filter_eq hA i))

end Field

/-! ### A protected rectangle of the field -/

section Rect

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **A protected rectangle of the two-time field `N`** (follow-up 5 §1.3; §A.1.3 (D9), §A.1.4 (D12)): bounded stopping
times `S₁` of curve `1` and `S₂` of curve `2`; `N` is bounded above and below by positive constants on the rectangle
`[0, S₁ x] × [0, S₂ y]`; and the two coordinate martingale identities hold — with the second path `y` fixed,
`s ↦ N((x, y), s ∧ S₁ x, S₂ y)` is a continuous `(𝓕₁, P₁)`-martingale, and with the first path `x` fixed,
`t ↦ N((x, y), a, t ∧ S₂ y)` is a continuous `(𝓕₂, P₂)`-martingale for every `0 ≤ a ≤ S₁ x`. -/
structure IsRectField (P₁ : Measure X) (P₂ : Measure Y) (𝓕₁ : Filtration ℝ≥0 mX) (𝓕₂ : Filtration ℝ≥0 mY)
    (S₁ : X → ℝ≥0) (S₂ : Y → ℝ≥0) (N : X × Y → ℝ → ℝ → ℝ) : Prop where
  stop₁ : IsStoppingTime 𝓕₁ fun x => (S₁ x : WithTop ℝ≥0)
  stop₂ : IsStoppingTime 𝓕₂ fun y => (S₂ y : WithTop ℝ≥0)
  bdd : ∃ U : ℝ≥0, (∀ x, S₁ x ≤ U) ∧ ∀ y, S₂ y ≤ U
  bound : ∃ c C : ℝ, 0 < c ∧ ∀ x y (s t : ℝ), 0 ≤ s → s ≤ S₁ x → 0 ≤ t → t ≤ S₂ y →
    c ≤ N (x, y) s t ∧ N (x, y) s t ≤ C
  col : ∀ y, Martingale (fun (s : ℝ≥0) x => N (x, y) (min (s : ℝ) (S₁ x)) (S₂ y)) 𝓕₁ P₁
  col_cont : ∀ x y, Continuous fun s : ℝ≥0 => N (x, y) (min (s : ℝ) (S₁ x)) (S₂ y)
  row : ∀ x (a : ℝ), 0 ≤ a → a ≤ S₁ x → Martingale (fun (t : ℝ≥0) y => N (x, y) a (min (t : ℝ) (S₂ y))) 𝓕₂ P₂
  row_cont : ∀ x y (a : ℝ), 0 ≤ a → a ≤ S₁ x → Continuous fun t : ℝ≥0 => N (x, y) a (min (t : ℝ) (S₂ y))

variable {P₁ : Measure X} {P₂ : Measure Y} {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY}

/-- **The hypotheses are consistent**: the trivial field `N ≡ 1` is a protected rectangle field for any bounded
stopping times (its coordinate processes are constant martingales). -/
theorem isRectField_one [IsFiniteMeasure P₁] [IsFiniteMeasure P₂] {S₁ : X → ℝ≥0} {S₂ : Y → ℝ≥0}
    (h₁ : IsStoppingTime 𝓕₁ fun x => (S₁ x : WithTop ℝ≥0)) (h₂ : IsStoppingTime 𝓕₂ fun y => (S₂ y : WithTop ℝ≥0))
    (hU : ∃ U : ℝ≥0, (∀ x, S₁ x ≤ U) ∧ ∀ y, S₂ y ≤ U) :
    IsRectField P₁ P₂ 𝓕₁ 𝓕₂ S₁ S₂ fun _ _ _ => 1 where
  stop₁ := h₁
  stop₂ := h₂
  bdd := hU
  bound := ⟨1, 1, one_pos, fun _ _ _ _ _ _ _ _ => ⟨le_rfl, le_rfl⟩⟩
  col _ := martingale_const 𝓕₁ P₁ 1
  col_cont _ _ := continuous_const
  row _ _ _ _ := martingale_const 𝓕₂ P₂ 1
  row_cont _ _ _ _ _ := continuous_const

end Rect

/-! ### The two coordinate martingales of the patched field -/

section Mart

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {ι : Type*} [Fintype ι]
  {P₁ : Measure X} {P₂ : Measure Y} {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY}
  {S₁ : ι → X → ℝ≥0} {S₂ : ι → Y → ℝ≥0} {N : X × Y → ℝ → ℝ → ℝ}

omit mX mY in
theorem stairField_pos (N : X × Y → ℝ → ℝ → ℝ) (S₁ : ι → X → ℝ≥0) (S₂ : ι → Y → ℝ≥0) (ω : X × Y) (s t : ℝ) :
    0 < stairField N S₁ S₂ ω s t :=
  patch_pos s t

/-- One pair of bounds for finitely many protected rectangles. -/
theorem exists_bound_of_isRectField [Nonempty ι] (h : ∀ i, IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ i) (S₂ i) N) :
    ∃ c C : ℝ, 0 < c ∧ ∀ i x y (s t : ℝ), 0 ≤ s → s ≤ S₁ i x → 0 ≤ t → t ≤ S₂ i y →
      c ≤ N (x, y) s t ∧ N (x, y) s t ≤ C := by
  choose c C hc hb using fun i => (h i).bound
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨univ.inf' ⟨i₀, mem_univ _⟩ c, univ.sup' ⟨i₀, mem_univ _⟩ C, ?_, fun i x y s t hs hsi ht hti => ?_⟩
  · exact (Finset.lt_inf'_iff _).2 fun i _ => hc i
  · obtain ⟨h1, h2⟩ := hb i x y s t hs hsi ht hti
    exact ⟨(Finset.inf'_le _ (mem_univ i)).trans h1, h2.trans (Finset.le_sup' _ (mem_univ i))⟩

/-- One deterministic bound for the stopping times of finitely many protected rectangles. -/
theorem exists_bdd_of_isRectField (h : ∀ i, IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ i) (S₂ i) N) :
    ∃ U : ℝ≥0, (∀ i x, S₁ i x ≤ U) ∧ ∀ i y, S₂ i y ≤ U := by
  choose U hU using fun i => (h i).bdd
  exact ⟨univ.sup U, fun i x => ((hU i).1 x).trans (le_sup (mem_univ i)),
    fun i y => ((hU i).2 y).trans (le_sup (mem_univ i))⟩

omit mX mY in
/-- **The column product is the patched field** (`patch_eq_prod`). -/
theorem colProd_eq_stairField (hpos : ∀ ω s t, 0 < N ω s t) (y : Y) {tb : ℝ} (htb : 0 ≤ tb) (s : ℝ≥0) (x : X) :
    colProd (fun x => N (x, y)) S₁ (fun i => (S₂ i y : ℝ)) tb s x = stairField N S₁ S₂ (x, y) s tb :=
  (patch_eq_prod (M := N (x, y)) (fun i => (S₁ i x).coe_nonneg) (fun i => (S₂ i y).coe_nonneg)
    (fun _ _ _ _ _ => hpos _ _ _) s.coe_nonneg htb).symm

omit mX mY in
/-- **The reflected column product is the patched field** (`patch_symm`, axis values one). -/
theorem rowProd_eq_stairField (hpos : ∀ ω s t, 0 < N ω s t) (hax₁ : ∀ ω t, N ω 0 t = 1)
    (hax₂ : ∀ ω s, N ω s 0 = 1) (x : X) {sb : ℝ} (hsb : 0 ≤ sb) (t : ℝ≥0) (y : Y) :
    colProd (fun y t s => N (x, y) s t) S₂ (fun i => (S₁ i x : ℝ)) sb t y = stairField N S₁ S₂ (x, y) sb t := by
  unfold stairField
  rw [patch_symm (fun i => (S₁ i x).coe_nonneg) (fun i => (S₂ i y).coe_nonneg) (hax₁ (x, y)) (hax₂ (x, y)) hsb
    t.coe_nonneg]
  exact (patch_eq_prod (M := fun t s => N (x, y) s t) (fun i => (S₂ i y).coe_nonneg)
    (fun i => (S₁ i x).coe_nonneg) (fun _ _ _ _ _ => hpos _ _ _) t.coe_nonneg hsb).symm

variable [Nonempty ι]

/-- **The column martingale** (A14, (D12) with the second path fixed): for every second path `y`, `s ↦ M*(s, U)` is a
right-continuous `(𝓕₁, P₁)`-martingale. -/
theorem stairField_col [IsFiniteMeasure P₁] (h : ∀ i, IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ i) (S₂ i) N)
    (hpos : ∀ ω s t, 0 < N ω s t) {U : ℝ≥0} (hU : ∀ i y, S₂ i y ≤ U) (y : Y) :
    Martingale (fun (s : ℝ≥0) x => stairField N S₁ S₂ (x, y) s U) 𝓕₁ P₁ ∧
      ∀ x (s : ℝ≥0), ContinuousWithinAt (fun s : ℝ≥0 => stairField N S₁ S₂ (x, y) s U) (Ici s) s := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨c, C, hc, hb⟩ := exists_bound_of_isRectField h
  have hY : ∀ i, frzHeightProc (fun x => N (x, y)) S₁ (fun i => (S₂ i y : ℝ)) U i =
      fun (s : ℝ≥0) x => N (x, y) (min (s : ℝ) (S₁ i x)) (S₂ i y) := fun i => by
    funext s x
    simp only [frzHeightProc, min_eq_left (NNReal.coe_le_coe.2 (hU i y))]
  have hm := martingale_colProd (fun i => (h i).stop₁) (fun i => (S₂ i y).coe_nonneg) i₀
    (fun x => hpos (x, y)) (U : ℝ) (fun i => by rw [hY i]; exact (h i).col y)
    (fun i x t => by rw [hY i]; exact ((h i).col_cont x y).continuousWithinAt) hc
    (fun i s x => by
      rw [hY i]
      exact hb i x y _ _ (le_min s.coe_nonneg (S₁ i x).coe_nonneg) (min_le_right _ _)
        (S₂ i y).coe_nonneg le_rfl)
  have e : colProd (fun x => N (x, y)) S₁ (fun i => (S₂ i y : ℝ)) U =
      fun (s : ℝ≥0) x => stairField N S₁ S₂ (x, y) s U :=
    funext fun s => funext fun x => colProd_eq_stairField hpos y U.coe_nonneg s x
  rw [e] at hm
  exact ⟨hm.1, fun x s => hm.2.1 x s⟩

/-- **The row martingale** (the reflected construction, with the first path fixed): for every first path `x` and every
`sb ≥ 0`, `t ↦ M*(sb, t)` is a right-continuous `(𝓕₂, P₂)`-martingale. -/
theorem stairField_row [IsFiniteMeasure P₂] (h : ∀ i, IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ i) (S₂ i) N)
    (hpos : ∀ ω s t, 0 < N ω s t) (hax₁ : ∀ ω t, N ω 0 t = 1) (hax₂ : ∀ ω s, N ω s 0 = 1) (x : X) {sb : ℝ}
    (hsb : 0 ≤ sb) :
    Martingale (fun (t : ℝ≥0) y => stairField N S₁ S₂ (x, y) sb t) 𝓕₂ P₂ ∧
      ∀ y (t : ℝ≥0), ContinuousWithinAt (fun t : ℝ≥0 => stairField N S₁ S₂ (x, y) sb t) (Ici t) t := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨c, C, hc, hb⟩ := exists_bound_of_isRectField h
  have ha0 : ∀ i, 0 ≤ min (S₁ i x : ℝ) sb := fun i => le_min (S₁ i x).coe_nonneg hsb
  have hY : ∀ i, frzHeightProc (fun y t s => N (x, y) s t) S₂ (fun i => (S₁ i x : ℝ)) sb i =
      fun (t : ℝ≥0) y => N (x, y) (min (S₁ i x : ℝ) sb) (min (t : ℝ) (S₂ i y)) := fun i => rfl
  have hm := martingale_colProd (fun i => (h i).stop₂) (fun i => (S₁ i x).coe_nonneg) i₀
    (fun y t s => hpos (x, y) s t) sb
    (fun i => by rw [hY i]; exact (h i).row x _ (ha0 i) (min_le_left _ _))
    (fun i y t => by
      rw [hY i]; exact ((h i).row_cont x y _ (ha0 i) (min_le_left _ _)).continuousWithinAt) hc
    (fun i t y => by
      rw [hY i]
      exact hb i x y _ _ (ha0 i) (min_le_left _ _) (le_min t.coe_nonneg (S₂ i y).coe_nonneg) (min_le_right _ _))
  have e : colProd (fun y t s => N (x, y) s t) S₂ (fun i => (S₁ i x : ℝ)) sb =
      fun (t : ℝ≥0) y => stairField N S₁ S₂ (x, y) sb t :=
    funext fun t => funext fun y => rowProd_eq_stairField hpos hax₁ hax₂ x hsb t y
  rw [e] at hm
  exact ⟨hm.1, fun y t => hm.2.1 y t⟩

end Mart

/-! ### The two optional samplings -/

section Sampling

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {ι : Type*} [Fintype ι] [Nonempty ι]
  {P₁ : Measure X} {P₂ : Measure Y} {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY}
  {S₁ : ι → X → ℝ≥0} {S₂ : ι → Y → ℝ≥0} {N : X × Y → ℝ → ℝ → ℝ}

/-- **Optional sampling in the first coordinate, second path fixed** (follow-up 4 §2.5 item 4: "condition first at the
first curve's enclosure stop while keeping the entire second path fixed"): for a stopping time `σ ≤ U` of curve `1`
and `A ∈ 𝓕¹_σ`, `∫_A M*(U, U) dP₁ = ∫_A M*(σ, U) dP₁`. -/
theorem setLIntegral_stairField_col [IsFiniteMeasure P₁] (h : ∀ i, IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ i) (S₂ i) N)
    (hpos : ∀ ω s t, 0 < N ω s t) {U : ℝ≥0} (hU : ∀ i y, S₂ i y ≤ U) (y : Y) {σ : X → ℝ≥0}
    (hσ : IsStoppingTime 𝓕₁ fun x => (σ x : WithTop ℝ≥0)) (hσU : ∀ x, σ x ≤ U) {A : Set X}
    (hA : MeasurableSet[hσ.measurableSpace] A) :
    ∫⁻ x in A, ENNReal.ofReal (stairField N S₁ S₂ (x, y) U U) ∂P₁ =
      ∫⁻ x in A, ENNReal.ofReal (stairField N S₁ S₂ (x, y) (σ x) U) ∂P₁ := by
  obtain ⟨hM, hMrc⟩ := stairField_col h hpos hU y
  have e := A1Core.lintegral_ofReal_stoppedValue_eq hM (fun x s => hMrc x s)
    (fun t x => (stairField_pos N S₁ S₂ (x, y) t U).le) hσ (isStoppingTime_const 𝓕₁ U)
    (fun x => WithTop.coe_le_coe.2 (hσU x)) (T := U) (fun _ => le_rfl) hA
  simpa only [stoppedValue, WithTop.untopA, WithTop.untopD_coe] using e

/-- **Optional sampling in the second coordinate, first path fixed** (the reflected construction): for `sb ≥ 0`, a
stopping time `τ ≤ U` of curve `2` and `B ∈ 𝓕²_τ`, `∫_B M*(sb, U) dP₂ = ∫_B M*(sb, τ) dP₂`. -/
theorem setLIntegral_stairField_row [IsFiniteMeasure P₂] (h : ∀ i, IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ i) (S₂ i) N)
    (hpos : ∀ ω s t, 0 < N ω s t) (hax₁ : ∀ ω t, N ω 0 t = 1) (hax₂ : ∀ ω s, N ω s 0 = 1) {U : ℝ≥0} (x : X)
    {sb : ℝ} (hsb : 0 ≤ sb) {τ : Y → ℝ≥0} (hτ : IsStoppingTime 𝓕₂ fun y => (τ y : WithTop ℝ≥0))
    (hτU : ∀ y, τ y ≤ U) {B : Set Y} (hB : MeasurableSet[hτ.measurableSpace] B) :
    ∫⁻ y in B, ENNReal.ofReal (stairField N S₁ S₂ (x, y) sb U) ∂P₂ =
      ∫⁻ y in B, ENNReal.ofReal (stairField N S₁ S₂ (x, y) sb (τ y)) ∂P₂ := by
  obtain ⟨hM, hMrc⟩ := stairField_row h hpos hax₁ hax₂ x hsb
  have e := A1Core.lintegral_ofReal_stoppedValue_eq hM (fun y t => hMrc y t)
    (fun t y => (stairField_pos N S₁ S₂ (x, y) sb t).le) hτ (isStoppingTime_const 𝓕₂ U)
    (fun y => WithTop.coe_le_coe.2 (hτU y)) (T := U) (fun _ => le_rfl) hB
  simpa only [stoppedValue, WithTop.untopA, WithTop.untopD_coe] using e

end Sampling

/-! ### The staircase coupling -/

section Coupling

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {ι : Type*} [Fintype ι]

/-- **The staircase coupling** `M*(U, U) · (P₁ ⊗ P₂)` of finitely many protected rectangles (§A.1.4, "`M*(∞, ∞)` is a
positive probability density"; `U` bounds every stopping time, so `M*(U, U) = M*(∞, ∞)`). -/
def stairCoupling (P₁ : Measure X) (P₂ : Measure Y) (N : X × Y → ℝ → ℝ → ℝ) (S₁ : ι → X → ℝ≥0)
    (S₂ : ι → Y → ℝ≥0) (U : ℝ≥0) : Measure (X × Y) :=
  (P₁.prod P₂).withDensity fun ω => ENNReal.ofReal (stairField N S₁ S₂ ω U U)

omit [Fintype ι] in
/-- Tonelli on a measurable rectangle, second coordinate outside. -/
theorem setLIntegral_prod_eq_snd {P₁ : Measure X} {P₂ : Measure Y} [SFinite P₁] [SFinite P₂] {f : X × Y → ℝ≥0∞}
    (hf : Measurable f) (A : Set X) (B : Set Y) :
    ∫⁻ ω in A ×ˢ B, f ω ∂(P₁.prod P₂) = ∫⁻ y in B, ∫⁻ x in A, f (x, y) ∂P₁ ∂P₂ := by
  rw [← Measure.prod_restrict, lintegral_prod_symm _ hf.aemeasurable]

omit [Fintype ι] in
/-- Tonelli on a measurable rectangle, first coordinate outside. -/
theorem setLIntegral_prod_eq_fst {P₁ : Measure X} {P₂ : Measure Y} [SFinite P₁] [SFinite P₂] {f : X × Y → ℝ≥0∞}
    (hf : Measurable f) (A : Set X) (B : Set Y) :
    ∫⁻ ω in A ×ˢ B, f ω ∂(P₁.prod P₂) = ∫⁻ x in A, ∫⁻ y in B, f (x, y) ∂P₂ ∂P₁ := by
  rw [← Measure.prod_restrict, lintegral_prod _ hf.aemeasurable]

variable [Nonempty ι] {P₁ : Measure X} {P₂ : Measure Y} {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY}
  {S₁ : ι → X → ℝ≥0} {S₂ : ι → Y → ℝ≥0} {N : X × Y → ℝ → ℝ → ℝ}

omit [Nonempty ι] in
/-- The density of the staircase coupling is measurable. -/
theorem measurable_stairCoupling_dens (h : ∀ i, IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ i) (S₂ i) N)
    (hmeas : IsFieldMeas N S₁ S₂) (U : ℝ≥0) :
    Measurable fun ω => ENNReal.ofReal (stairField N S₁ S₂ ω U U) :=
  ENNReal.measurable_ofReal.comp (measurable_stairField (fun i => measurable_coe_of_isStoppingTime (h i).stop₁)
    (fun i => measurable_coe_of_isStoppingTime (h i).stop₂) hmeas measurable_const measurable_const
    (fun _ => U.coe_nonneg) fun _ => U.coe_nonneg)

/-- **The second marginal is unchanged** (column mass one, A14: `M*(0, U) = 1`). -/
theorem stairCoupling_map_snd [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (h : ∀ i, IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ i) (S₂ i) N) (hpos : ∀ ω s t, 0 < N ω s t)
    (hmeas : IsFieldMeas N S₁ S₂) {U : ℝ≥0} (hU : ∀ i y, S₂ i y ≤ U) :
    (stairCoupling P₁ P₂ N S₁ S₂ U).map Prod.snd = P₂ := by
  ext B hB
  have hD := measurable_stairCoupling_dens h hmeas U
  have he : Prod.snd ⁻¹' B = (univ : Set X) ×ˢ B := by ext ω; simp
  rw [Measure.map_apply measurable_snd hB, stairCoupling, withDensity_apply _ (measurable_snd hB), he,
    setLIntegral_prod_eq_snd hD, ← setLIntegral_one]
  refine lintegral_congr fun y => ?_
  rw [Measure.restrict_univ]
  have e := setLIntegral_stairField_col h hpos hU y (isStoppingTime_const 𝓕₁ (0 : ℝ≥0)) (fun _ => zero_le)
    (A := univ) MeasurableSet.univ
  simp only [Measure.restrict_univ, NNReal.coe_zero] at e
  rw [e]
  simp only [stairField, patch_zero_left (fun i => (S₁ i _).coe_nonneg), ENNReal.ofReal_one, lintegral_one,
    measure_univ]

/-- **The first marginal is unchanged** (row mass one, the reflected construction: `M*(U, 0) = 1`). -/
theorem stairCoupling_map_fst [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (h : ∀ i, IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ i) (S₂ i) N) (hpos : ∀ ω s t, 0 < N ω s t)
    (hax₁ : ∀ ω t, N ω 0 t = 1) (hax₂ : ∀ ω s, N ω s 0 = 1) (hmeas : IsFieldMeas N S₁ S₂) (U : ℝ≥0) :
    (stairCoupling P₁ P₂ N S₁ S₂ U).map Prod.fst = P₁ := by
  ext A hA
  have hD := measurable_stairCoupling_dens h hmeas U
  have he : Prod.fst ⁻¹' A = A ×ˢ (univ : Set Y) := by ext ω; simp
  rw [Measure.map_apply measurable_fst hA, stairCoupling, withDensity_apply _ (measurable_fst hA), he,
    setLIntegral_prod_eq_fst hD, ← setLIntegral_one]
  refine lintegral_congr fun x => ?_
  rw [Measure.restrict_univ]
  have e := setLIntegral_stairField_row h hpos hax₁ hax₂ (U := U) x U.coe_nonneg
    (isStoppingTime_const 𝓕₂ (0 : ℝ≥0)) (fun _ => zero_le) (B := univ) MeasurableSet.univ
  simp only [Measure.restrict_univ, NNReal.coe_zero] at e
  rw [e]
  simp only [stairField, patch_zero_right (hax₂ _), ENNReal.ofReal_one, lintegral_one, measure_univ]

/-- The staircase coupling is a probability measure. -/
theorem isProbabilityMeasure_stairCoupling [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (h : ∀ i, IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ i) (S₂ i) N) (hpos : ∀ ω s t, 0 < N ω s t)
    (hax₁ : ∀ ω t, N ω 0 t = 1) (hax₂ : ∀ ω s, N ω s 0 = 1) (hmeas : IsFieldMeas N S₁ S₂) (U : ℝ≥0) :
    IsProbabilityMeasure (stairCoupling P₁ P₂ N S₁ S₂ U) := by
  have hi : IsProbabilityMeasure ((stairCoupling P₁ P₂ N S₁ S₂ U).map Prod.fst) := by
    rw [stairCoupling_map_fst h hpos hax₁ hax₂ hmeas U]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable

omit [Fintype ι] [Nonempty ι] in
/-- The rectangle density `N(S₁ i, S₂ i)` is measurable. -/
theorem measurable_rectDens (h : ∀ i, IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ i) (S₂ i) N) (hmeas : IsFieldMeas N S₁ S₂)
    (i : ι) : Measurable fun ω : X × Y => ENNReal.ofReal (N ω (S₁ i ω.1) (S₂ i ω.2)) :=
  ENNReal.measurable_ofReal.comp (hmeas _ _ ((measurable_coe_of_isStoppingTime (h i).stop₁).comp measurable_fst)
    ((measurable_coe_of_isStoppingTime (h i).stop₂).comp measurable_snd) (fun ω => (S₁ i ω.1).coe_nonneg)
    (fun ω => (S₂ i ω.2).coe_nonneg) fun _ => ⟨i, le_rfl, le_rfl⟩)

/-- **The stopped rectangle law** (follow-up 4 §2.5 item 4: "Separate optional sampling reduces the terminal patched
density to `M(S₁, S₂)` on that rectangle"): for `A ∈ 𝓕¹_{S₁ i}` and `B ∈ 𝓕²_{S₂ i}`, the staircase coupling gives
`A × B` the mass `∫_{A × B} N(S₁ i, S₂ i) d(P₁ ⊗ P₂)`. -/
theorem stairCoupling_rect [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (h : ∀ i, IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ i) (S₂ i) N) (hpos : ∀ ω s t, 0 < N ω s t)
    (hax₁ : ∀ ω t, N ω 0 t = 1) (hax₂ : ∀ ω s, N ω s 0 = 1) (hmeas : IsFieldMeas N S₁ S₂) {U : ℝ≥0}
    (hU₁ : ∀ i x, S₁ i x ≤ U) (hU₂ : ∀ i y, S₂ i y ≤ U) (i : ι) {A : Set X} {B : Set Y}
    (hA : MeasurableSet[(h i).stop₁.measurableSpace] A) (hB : MeasurableSet[(h i).stop₂.measurableSpace] B) :
    stairCoupling P₁ P₂ N S₁ S₂ U (A ×ˢ B) =
      ∫⁻ ω in A ×ˢ B, ENNReal.ofReal (N ω (S₁ i ω.1) (S₂ i ω.2)) ∂(P₁.prod P₂) := by
  have hAm : MeasurableSet A := (h i).stop₁.measurableSpace_le _ hA
  have hBm : MeasurableSet B := (h i).stop₂.measurableSpace_le _ hB
  have hS₁ : ∀ j, Measurable fun x => (S₁ j x : ℝ) := fun j => measurable_coe_of_isStoppingTime (h j).stop₁
  have hS₂ : ∀ j, Measurable fun y => (S₂ j y : ℝ) := fun j => measurable_coe_of_isStoppingTime (h j).stop₂
  have hF₁ := measurable_stairCoupling_dens h hmeas U
  have hF₂ : Measurable fun ω => ENNReal.ofReal (stairField N S₁ S₂ ω (S₁ i ω.1) U) :=
    ENNReal.measurable_ofReal.comp (measurable_stairField hS₁ hS₂ hmeas ((hS₁ i).comp measurable_fst)
      measurable_const (fun ω => (S₁ i ω.1).coe_nonneg) fun _ => U.coe_nonneg)
  have hF₄ := measurable_rectDens h hmeas i
  have hcorner : ∀ x y, stairField N S₁ S₂ (x, y) (S₁ i x) (S₂ i y) = N (x, y) (S₁ i x) (S₂ i y) := fun x y =>
    patch_eq_of_inStair (fun j => (S₁ j x).coe_nonneg) (hax₁ (x, y)) (S₁ i x).coe_nonneg le_rfl le_rfl
      (hpos _ _ _)
  rw [stairCoupling, withDensity_apply _ (hAm.prod hBm)]
  calc ∫⁻ ω in A ×ˢ B, ENNReal.ofReal (stairField N S₁ S₂ ω U U) ∂(P₁.prod P₂)
      = ∫⁻ y in B, ∫⁻ x in A, ENNReal.ofReal (stairField N S₁ S₂ (x, y) U U) ∂P₁ ∂P₂ :=
        setLIntegral_prod_eq_snd hF₁ A B
    _ = ∫⁻ y in B, ∫⁻ x in A, ENNReal.ofReal (stairField N S₁ S₂ (x, y) (S₁ i x) U) ∂P₁ ∂P₂ :=
        lintegral_congr fun y => setLIntegral_stairField_col h hpos hU₂ y (h i).stop₁ (hU₁ i) hA
    _ = ∫⁻ x in A, ∫⁻ y in B, ENNReal.ofReal (stairField N S₁ S₂ (x, y) (S₁ i x) U) ∂P₂ ∂P₁ := by
        rw [← setLIntegral_prod_eq_snd hF₂ A B, setLIntegral_prod_eq_fst hF₂ A B]
    _ = ∫⁻ x in A, ∫⁻ y in B, ENNReal.ofReal (N (x, y) (S₁ i x) (S₂ i y)) ∂P₂ ∂P₁ := by
        refine lintegral_congr fun x => ?_
        rw [setLIntegral_stairField_row h hpos hax₁ hax₂ x (S₁ i x).coe_nonneg (h i).stop₂ (hU₂ i) hB]
        exact lintegral_congr fun y => by rw [hcorner]
    _ = ∫⁻ ω in A ×ˢ B, ENNReal.ofReal (N ω (S₁ i ω.1) (S₂ i ω.2)) ∂(P₁.prod P₂) :=
        (setLIntegral_prod_eq_fst hF₄ A B).symm

/-- **(1.7) on every rectangle of the staircase coupling**: for every test measurable for the product of the two
stopped σ-algebras `𝓕¹_{S₁ i} ⊗ 𝓕²_{S₂ i}`, the staircase coupling integrates as the density `N(S₁ i, S₂ i)` times
`P₁ ⊗ P₂` (rectangles by `stairCoupling_rect`, then Dynkin: A1CORE's `lintegral_eq_of_rect`). -/
theorem rectDens_stairCoupling [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (h : ∀ i, IsRectField P₁ P₂ 𝓕₁ 𝓕₂ (S₁ i) (S₂ i) N) (hpos : ∀ ω s t, 0 < N ω s t)
    (hax₁ : ∀ ω t, N ω 0 t = 1) (hax₂ : ∀ ω s, N ω s 0 = 1) (hmeas : IsFieldMeas N S₁ S₂) {U : ℝ≥0}
    (hU₁ : ∀ i x, S₁ i x ≤ U) (hU₂ : ∀ i y, S₂ i y ≤ U) (i : ι) :
    RectDens (h i).stop₁.measurableSpace (h i).stop₂.measurableSpace P₁ P₂ (stairCoupling P₁ P₂ N S₁ S₂ U)
      fun ω => ENNReal.ofReal (N ω (S₁ i ω.1) (S₂ i ω.2)) := by
  have := isProbabilityMeasure_stairCoupling h hpos hax₁ hax₂ hmeas U
  intro f hf
  exact A1Core.lintegral_eq_of_rect (P₁ := P₁) (P₂ := P₂) (h i).stop₁.measurableSpace_le
    (h i).stop₂.measurableSpace_le (measurable_rectDens h hmeas i)
    (fun A B hA hB => stairCoupling_rect h hpos hax₁ hax₂ hmeas hU₁ hU₂ i hA hB) hf

end Coupling

end InteractingSLE.ZhanGT4.A1Patch
