/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution
import InteractingSLE.Frozen.Spec.IsGeneratingTrace
import InteractingSLE.Frozen.Spec.IsOrderedForceWord
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Baire.Lemmas

/-!
# Lemma GB10: no simple-arc time interval for a finite-force counterflow

Packet PROVE-T14-GW4R. Supplement §13, **Lemma GB10** (`source/spec/p529-576.md` L629–L635, p. 555):

> "Let `k > 4` and let `η` be a continuous finite-force trace, up to its available lifetime, with its original
> strictly increasing capacity clock. Almost surely no nontrivial original-time interval of `η` is contained in a
> simple arc. The proposed arc may depend on the whole field."

It is used three times in Theorem GW4's proof (pp. 637–638, through GB11): an interval of the traversal outside `C̄`
would lie in the two simple sewn walks; an interval without open-`C` visits likewise; a relative constancy interval
would lie in the old range or in one of the two walks — each time with Baire's theorem on the time interval.

## Main definitions

* `IsSimpleArc A`: `A` is a compact simple arc (a continuous injective image of `[0, 1]`);
* `NoSimpleArcInterval γ ζ`: the pathwise conclusion of GB10 (no nontrivial time interval before `ζ` is mapped into a
  compact simple arc);
* **`GB10Statement`** (named input, exact): for every `k > 4` and every integrated finite-force `SLE_k(ρ)` evolution
  (the frozen `IsIntegratedSLEEvolution`, any ordered force word), almost surely every continuous generating trace
  up to the lifetime satisfies `NoSimpleArcInterval` — the arc is quantified inside the almost-sure event ("the
  proposed arc may depend on the whole field").

## Main results (proved)

* **`exists_Icc_subset_of_image_subset_iUnion`** (Baire's theorem on a time interval): if `γ([a, b])`, `a < b`, lies
  in a countable union of closed sets, one of them contains `γ([a', b'])` for a nontrivial subinterval;
* `IsSimpleArc.isClosed`, `isSimpleArc_image_Icc` (compact sub-arcs of a continuous injective curve);
* **`NoSimpleArcInterval.not_image_subset_iUnion`**: under GB10's conclusion no nontrivial interval maps into a
  countable union of compact simple arcs; **`NoSimpleArcInterval.not_image_subset_union_range`**: nor into the union of
  the ranges of two continuous injective curves `[0, ∞) → ℂ` (the source's "two compact simple ranges" covering an
  interval, GB11's and GW4's Baire step), nor with an extra closed set that contains no time interval.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GB10

/-! ### Simple arcs and the pathwise conclusion -/

/-- `A` is a **compact simple arc**: the image of `[0, 1]` under a continuous map injective on `[0, 1]`. -/
def IsSimpleArc (A : Set ℂ) : Prop :=
  ∃ α : ℝ → ℂ, ContinuousOn α (Icc 0 1) ∧ InjOn α (Icc 0 1) ∧ α '' Icc 0 1 = A

/-- **The pathwise conclusion of Lemma GB10**: no nontrivial time interval `[a, b]` before `ζ` is mapped by `γ` into
a compact simple arc. -/
def NoSimpleArcInterval (γ : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) : Prop :=
  ∀ a b : ℝ≥0, a < b → (b : ℝ≥0∞) < ζ → ∀ A : Set ℂ, IsSimpleArc A → ¬ γ '' Icc a b ⊆ A

/-- **Named input: Lemma GB10** (supplement p. 555, `source/spec/p529-576.md` L629–L635). For `k > 4` and an
integrated finite-force `SLE_k(ρ)` evolution (any ordered force word, the frozen `IsIntegratedSLEEvolution`, on any
probability space), almost surely every continuous generating trace up to the lifetime ("a continuous finite-force
trace, up to its available lifetime, with its original strictly increasing capacity clock") has no nontrivial time
interval contained in a compact simple arc. The arc is quantified inside the almost-sure event ("The proposed arc may
depend on the whole field").

Source proof (not formalized here): at rational times with an interior tip all force gaps are nonzero, so on bounded
localizations the evolution is locally absolutely continuous with ordinary `SLE_k`, whose own-mapped future has real
contacts arbitrarily soon (Aux. 42); a trace interval inside a simple arc would give a rational restart whose
own-mapped future stays in the open half-plane for a positive time. -/
def GB10Statement : Prop :=
  ∀ (k : ℝ), 4 < k → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ →
      ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ → NoSimpleArcInterval γ (ζ ω)

/-! ### Baire's theorem on a time interval -/

/-- **Baire's theorem on a time interval.** If `γ` is continuous on `[a, b]` with `a < b` and `γ([a, b])` lies in
a countable union of closed sets `F n`, then some `F n` contains `γ([a', b'])` for a nontrivial subinterval
`[a', b'] ⊆ [a, b]`. -/
theorem exists_Icc_subset_of_image_subset_iUnion {γ : ℝ≥0 → ℂ} {a b : ℝ≥0} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b)) {F : ℕ → Set ℂ} (hF : ∀ n, IsClosed (F n))
    (hsub : γ '' Icc a b ⊆ ⋃ n, F n) :
    ∃ n, ∃ a' b' : ℝ≥0, a ≤ a' ∧ a' < b' ∧ b' ≤ b ∧ γ '' Icc a' b' ⊆ F n := by
  have : Nonempty (Icc a b) := ⟨⟨a, le_rfl, hab.le⟩⟩
  have hc : Continuous fun x : Icc a b => γ x := hγ.domRestrict
  set f : ℕ → Set (Icc a b) := fun n => (fun x : Icc a b => γ x) ⁻¹' F n with hf
  have hfc : ∀ n, IsClosed (f n) := fun n => (hF n).preimage hc
  have hU : ⋃ n, f n = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn⟩ := mem_iUnion.1 (hsub ⟨x, x.2, rfl⟩)
    exact mem_iUnion.2 ⟨n, hn⟩
  obtain ⟨n, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hfc hU
  have hnhds : interior (f n) ∈ 𝓝 x := isOpen_interior.mem_nhds hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  set δ : ℝ≥0 := ⟨ε / 2, (half_pos hε).le⟩ with hδ
  have hδpos : 0 < δ := by rw [← NNReal.coe_pos]; exact half_pos hε
  have hδε : (δ : ℝ) < ε := by show ε / 2 < ε; linarith
  obtain ⟨hxa, hxb⟩ := x.2
  refine ⟨n, max a ((x : ℝ≥0) - δ), min b ((x : ℝ≥0) + δ), le_max_left _ _, ?_, min_le_left _ _, ?_⟩
  · rcases lt_or_eq_of_le hxb with hxb' | hxb'
    · calc max a ((x : ℝ≥0) - δ) ≤ x := max_le hxa tsub_le_self
        _ < min b ((x : ℝ≥0) + δ) := lt_min hxb' (lt_add_of_pos_right _ hδpos)
    · have hax : a < (x : ℝ≥0) := lt_of_lt_of_eq hab hxb'.symm
      calc max a ((x : ℝ≥0) - δ) < x := max_lt hax (tsub_lt_self (lt_of_le_of_lt zero_le hax) hδpos)
        _ = min b ((x : ℝ≥0) + δ) := by rw [hxb']; exact (min_eq_left (le_add_of_nonneg_right zero_le)).symm
  · rintro _ ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
    have hya : a ≤ y := (le_max_left _ _).trans hy₁
    have hyb : y ≤ b := hy₂.trans (min_le_left _ _)
    have hdist : dist (⟨y, hya, hyb⟩ : Icc a b) x < ε := by
      rw [Subtype.dist_eq, NNReal.dist_eq]
      have h1 : (x : ℝ≥0) - δ ≤ y := (le_max_right _ _).trans hy₁
      have h2 : y ≤ (x : ℝ≥0) + δ := hy₂.trans (min_le_right _ _)
      have h1' : ((x : ℝ≥0) : ℝ) - δ ≤ y := by
        have := NNReal.coe_le_coe.2 h1
        rw [NNReal.coe_sub_def] at this
        exact (le_max_left _ _).trans this
      have h2' : (y : ℝ) ≤ ((x : ℝ≥0) : ℝ) + δ := by exact_mod_cast h2
      show |(y : ℝ) - ((x : ℝ≥0) : ℝ)| < ε
      rw [abs_sub_lt_iff]
      constructor <;> linarith
    exact (interior_subset (hball hdist) : (⟨y, hya, hyb⟩ : Icc a b) ∈ f n)

/-! ### Simple arcs -/

theorem IsSimpleArc.isCompact {A : Set ℂ} (hA : IsSimpleArc A) : IsCompact A := by
  obtain ⟨α, hc, -, rfl⟩ := hA
  exact isCompact_Icc.image_of_continuousOn hc

theorem IsSimpleArc.isClosed {A : Set ℂ} (hA : IsSimpleArc A) : IsClosed A := hA.isCompact.isClosed

/-- A compact sub-arc `α([p, q])`, `p < q`, of a curve continuous and injective on `[p, q]` is a simple arc. -/
theorem isSimpleArc_image_Icc {α : ℝ → ℂ} {p q : ℝ} (hpq : p < q) (hc : ContinuousOn α (Icc p q))
    (hi : InjOn α (Icc p q)) : IsSimpleArc (α '' Icc p q) := by
  set e : ℝ → ℝ := fun s => p + (q - p) * s with he
  have hmaps : MapsTo e (Icc 0 1) (Icc p q) := by
    intro s hs
    have hqp : 0 < q - p := sub_pos.2 hpq
    constructor
    · show p ≤ p + (q - p) * s
      nlinarith [hs.1]
    · show p + (q - p) * s ≤ q
      nlinarith [hs.2]
  have himg : e '' Icc 0 1 = Icc p q := by
    refine le_antisymm (image_subset_iff.2 hmaps) fun t ht => ?_
    have hqp : 0 < q - p := sub_pos.2 hpq
    refine ⟨(t - p) / (q - p), ⟨div_nonneg (by linarith [ht.1]) hqp.le, ?_⟩, ?_⟩
    · rw [div_le_one hqp]; linarith [ht.2]
    · show p + (q - p) * ((t - p) / (q - p)) = t
      field_simp
      ring
  have heinj : InjOn e (Icc 0 1) := by
    intro s _ s' _ hss'
    have hqp : q - p ≠ 0 := (sub_pos.2 hpq).ne'
    have : (q - p) * s = (q - p) * s' := by simpa [he] using hss'
    exact mul_left_cancel₀ hqp this
  refine ⟨α ∘ e, hc.comp (by fun_prop) hmaps, hi.comp heinj hmaps, ?_⟩
  rw [image_comp, himg]

/-- A compact sub-arc `β([p, q])`, `p < q`, of a continuous injective curve `β : [0, ∞) → ℂ` is a simple arc. -/
theorem isSimpleArc_image_Icc_nnreal {β : ℝ≥0 → ℂ} (hβ : Continuous β) (hβi : Function.Injective β) {p q : ℝ≥0}
    (hpq : p < q) : IsSimpleArc (β '' Icc p q) := by
  have h := isSimpleArc_image_Icc (α := fun r : ℝ => β r.toNNReal) (p := p) (q := q) (by exact_mod_cast hpq)
    (hβ.comp continuous_real_toNNReal).continuousOn ?_
  · convert h using 1
    ext z
    constructor
    · rintro ⟨t, ⟨ht₁, ht₂⟩, rfl⟩
      exact ⟨t, ⟨NNReal.coe_le_coe.2 ht₁, NNReal.coe_le_coe.2 ht₂⟩, by simp⟩
    · rintro ⟨r, ⟨hr₁, hr₂⟩, rfl⟩
      have hr0 : 0 ≤ r := (NNReal.coe_nonneg p).trans hr₁
      refine ⟨r.toNNReal, ⟨?_, ?_⟩, rfl⟩
      · rw [← NNReal.coe_le_coe, Real.coe_toNNReal r hr0]; exact hr₁
      · rw [← NNReal.coe_le_coe, Real.coe_toNNReal r hr0]; exact hr₂
  · intro r hr r' hr' hrr'
    have hr0 : 0 ≤ r := (NNReal.coe_nonneg p).trans hr.1
    have hr0' : 0 ≤ r' := (NNReal.coe_nonneg p).trans hr'.1
    have := hβi hrr'
    rw [← Real.coe_toNNReal r hr0, ← Real.coe_toNNReal r' hr0', this]

/-! ### Consequences of the pathwise conclusion -/

/-- **No interval in a countable union of closed sets that contain no interval.** If no nontrivial subinterval of
`[a, b]` is mapped into any `F n` (closed), then `γ([a, b])` is not contained in `⋃ F n` (Baire). -/
theorem not_image_subset_iUnion_of_forall {γ : ℝ≥0 → ℂ} {a b : ℝ≥0} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b)) {F : ℕ → Set ℂ} (hF : ∀ n, IsClosed (F n))
    (hno : ∀ n, ∀ a' b' : ℝ≥0, a ≤ a' → a' < b' → b' ≤ b → ¬ γ '' Icc a' b' ⊆ F n) :
    ¬ γ '' Icc a b ⊆ ⋃ n, F n := by
  intro hsub
  obtain ⟨n, a', b', h₁, h₂, h₃, h₄⟩ := exists_Icc_subset_of_image_subset_iUnion hab hγ hF hsub
  exact hno n a' b' h₁ h₂ h₃ h₄

/-- **GB10's conclusion excludes intervals in countably many compact simple arcs.** -/
theorem NoSimpleArcInterval.not_image_subset_iUnion {γ : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} (h : NoSimpleArcInterval γ ζ)
    {a b : ℝ≥0} (hab : a < b) (hb : (b : ℝ≥0∞) < ζ) (hγ : ContinuousOn γ (Icc a b)) {A : ℕ → Set ℂ}
    (hA : ∀ n, IsSimpleArc (A n)) : ¬ γ '' Icc a b ⊆ ⋃ n, A n :=
  not_image_subset_iUnion_of_forall hab hγ (fun n => (hA n).isClosed) fun n _ _ _ h₂ h₃ =>
    h _ _ h₂ ((ENNReal.coe_le_coe.2 h₃).trans_lt hb) (A n) (hA n)

/-- The range of a continuous injective curve `β : [0, ∞) → ℂ` is the union of the compact simple arcs
`β([0, n + 1])`. -/
theorem range_eq_iUnion_image_Icc (β : ℝ≥0 → ℂ) : range β = ⋃ n : ℕ, β '' Icc 0 ((n : ℝ≥0) + 1) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨n, hn⟩ := exists_nat_gt t
    exact mem_iUnion.2 ⟨n, t, ⟨zero_le, hn.le.trans (le_add_of_nonneg_right zero_le_one)⟩, rfl⟩
  · intro hz
    obtain ⟨n, t, -, rfl⟩ := mem_iUnion.1 hz
    exact ⟨t, rfl⟩

/-- **GB10's conclusion excludes intervals in two simple curves and a closed set without intervals** (the Baire
step of GB11 and of Theorem GW4's proof: "the interval is covered by the closed sets `R_s, α_R, α_L`; Baire yields
either an interval in the fixed old range … or an interval in a simple arc, contradicting GB10"). Here `β₁`, `β₂` are
continuous injective curves `[0, ∞) → ℂ` and `F` is a closed set containing no `γ`-image of a nontrivial subinterval
of `[a, b]`. -/
theorem NoSimpleArcInterval.not_image_subset_union_range {γ : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} (h : NoSimpleArcInterval γ ζ)
    {a b : ℝ≥0} (hab : a < b) (hb : (b : ℝ≥0∞) < ζ) (hγ : ContinuousOn γ (Icc a b)) {β₁ β₂ : ℝ≥0 → ℂ}
    (hβ₁ : Continuous β₁) (hβ₁i : Function.Injective β₁) (hβ₂ : Continuous β₂) (hβ₂i : Function.Injective β₂)
    {F : Set ℂ} (hF : IsClosed F)
    (hFno : ∀ a' b' : ℝ≥0, a ≤ a' → a' < b' → b' ≤ b → ¬ γ '' Icc a' b' ⊆ F) :
    ¬ γ '' Icc a b ⊆ F ∪ range β₁ ∪ range β₂ := by
  -- index: `0 ↦ F`, `2n + 1 ↦ β₁([0, n + 1])`, `2n + 2 ↦ β₂([0, n + 1])`
  set A : ℕ → Set ℂ := fun m => if m = 0 then F else if m % 2 = 1 then β₁ '' Icc 0 (((m / 2 : ℕ) : ℝ≥0) + 1)
    else β₂ '' Icc 0 ((((m - 1) / 2 : ℕ) : ℝ≥0) + 1) with hA
  have hpos : ∀ n : ℕ, (0 : ℝ≥0) < (n : ℝ≥0) + 1 := fun n => add_pos_of_nonneg_of_pos zero_le one_pos
  have harc₁ : ∀ n : ℕ, IsSimpleArc (β₁ '' Icc 0 ((n : ℝ≥0) + 1)) := fun n =>
    isSimpleArc_image_Icc_nnreal hβ₁ hβ₁i (hpos n)
  have harc₂ : ∀ n : ℕ, IsSimpleArc (β₂ '' Icc 0 ((n : ℝ≥0) + 1)) := fun n =>
    isSimpleArc_image_Icc_nnreal hβ₂ hβ₂i (hpos n)
  have hcl : ∀ m, IsClosed (A m) := by
    intro m
    simp only [hA]
    split_ifs
    · exact hF
    · exact (harc₁ _).isClosed
    · exact (harc₂ _).isClosed
  have hno : ∀ m, ∀ a' b' : ℝ≥0, a ≤ a' → a' < b' → b' ≤ b → ¬ γ '' Icc a' b' ⊆ A m := by
    intro m a' b' h₁ h₂ h₃
    have hb' : (b' : ℝ≥0∞) < ζ := (ENNReal.coe_le_coe.2 h₃).trans_lt hb
    simp only [hA]
    split_ifs
    · exact hFno a' b' h₁ h₂ h₃
    · exact h a' b' h₂ hb' _ (harc₁ _)
    · exact h a' b' h₂ hb' _ (harc₂ _)
  intro hsub
  refine not_image_subset_iUnion_of_forall hab hγ hcl hno (hsub.trans ?_)
  rintro z ((hz | hz) | hz)
  · exact mem_iUnion.2 ⟨0, by simp only [hA, ↓reduceIte]; exact hz⟩
  · rw [range_eq_iUnion_image_Icc] at hz
    obtain ⟨n, hn⟩ := mem_iUnion.1 hz
    refine mem_iUnion.2 ⟨2 * n + 1, ?_⟩
    have h1 : 2 * n + 1 ≠ 0 := by omega
    have h2 : (2 * n + 1) % 2 = 1 := by omega
    have h3 : (2 * n + 1) / 2 = n := by omega
    simp only [hA, h1, h2, h3, ↓reduceIte]
    exact hn
  · rw [range_eq_iUnion_image_Icc] at hz
    obtain ⟨n, hn⟩ := mem_iUnion.1 hz
    refine mem_iUnion.2 ⟨2 * n + 2, ?_⟩
    have h1 : 2 * n + 2 ≠ 0 := by omega
    have h2 : ¬ (2 * n + 2) % 2 = 1 := by omega
    have h3 : (2 * n + 2 - 1) / 2 = n := by omega
    simp only [hA, h1, h2, h3, ↓reduceIte]
    exact hn

end GB10

end Theorem14

end InteractingSLE
