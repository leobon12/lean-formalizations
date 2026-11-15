/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ChartDataFibre
import InteractingSLE.Foundations.Complex.DerivLog
import InteractingSLE.Frozen.Spec.activeDomain
import InteractingSLE.Frozen.Spec.IsActiveChart

/-!
# The active chart at a first contact (pathwise)

Packet PROVE-RESTART-CPL3: the pathwise part of `Restart.FirstContactChartDataStatement` (Lemma 7.8, p. 290: "`φ : D →
ℍ` fix infinity"; Theorem W8, pp. 538–541; Aux. 80, p. 540; the active prime end of D.5, interface 2, follow-up note
L2318–L2320). Let `η₁`, `η₂` be continuous paths in `ℍ̄` from real points, with a common point `p = η₁(s₀) = η₂(t₀)`
not visited by either path before (a first contact), and let `D` be the unbounded component of
`ℍ \ (η₁[0, s₀] ∪ η₂[0, t₀])` (the frozen `activeDomain`). If `p ∈ closure D`, then `D` has a **common active chart**
`φ : D → ℍ` (frozen `IsActiveChart`: conformal onto `ℍ`, `φ → 0` at `p`, `φ → ∞` at `∞`), whose inverse `ψ` extends
continuously to `ℍ̄` with `ψ(0) = p` and real values in `∂D`, with a continuous branch of `arg φ'`, and with **forward
limits** along `D` at every point of `closure D` that lies in `D`, is `p`, or is a real point off the prefixes; there
the limit is the unique point of `ℍ̄` sent to that point by `ψ`.

Construction: `K = η₁[0, s₀] ∪ η₂[0, t₀]` is the range of one path (`joinPath`: `η₁` then `η₂` backwards), so
`D = ℍ \ fill(K)` (`activeDomain_eq`) and the inverse `F` of the mapping-out function `g` of `fill(K)` extends
continuously to `ℍ̄` (`YuanCharacterisation.exists_extension_symm`). `ℝ ∪ K` minus `p` (resp. minus a real point off
`K`) is unbounded-linked, so `p` has exactly one real preimage `x₀` (`eq_of_apply_eq_of_linked`) and `g → x₀` along
`D` at `p` (`exists_tendsto_of_fibre`). Then `φ = g − x₀`, `ψ = F(· + x₀)` on `ℍ̄`.

## Main results

* `activeDomain_eq`: `activeDomain η₁ s₀ η₂ t₀ = ℍ \ fill(η₁[0, s₀] ∪ η₂[0, t₀])` (closed prefixes);
* `image_joinPath`, `continuousOn_joinPath`: the prefixes are the range of one path;
* **`exists_firstContactChart`**: the chart, its inverse and lift, with forward limits.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal
open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Restart

/-! ### The prefixes as the range of one path -/

section Join

variable {η₁ η₂ : ℝ≥0 → ℂ} {s₀ t₀ : ℝ≥0}

/-- The union of the two prefixes `η₁([0, s₀]) ∪ η₂([0, t₀])`. -/
def prefixSet (η₁ : ℝ≥0 → ℂ) (s₀ : ℝ≥0) (η₂ : ℝ≥0 → ℂ) (t₀ : ℝ≥0) : Set ℂ :=
  η₁ '' Icc 0 s₀ ∪ η₂ '' Icc 0 t₀

/-- For closed prefixes, the active domain is the complement of the filling. -/
theorem activeDomain_eq (hK : IsClosed (prefixSet η₁ s₀ η₂ t₀)) :
    activeDomain η₁ s₀ η₂ t₀ = H \ fillH (prefixSet η₁ s₀ η₂ t₀) := by
  ext z
  simp only [activeDomain, unboundedPart, fillH, prefixSet] at hK ⊢
  rw [hK.closure_eq]
  constructor
  · rintro ⟨⟨hzH, hzK⟩, hb⟩
    exact ⟨hzH, fun ⟨_, h⟩ => h.elim hzK hb⟩
  · rintro ⟨hzH, hz⟩
    exact ⟨⟨hzH, fun h => hz ⟨hzH, Or.inl h⟩⟩, fun h => hz ⟨hzH, Or.inr h⟩⟩

/-- The concatenated path: `η₁` on `[0, s₀]`, then `η₂` backwards from `t₀` to `0` on `[s₀, s₀ + t₀]`. -/
def joinPath (η₁ : ℝ≥0 → ℂ) (s₀ : ℝ≥0) (η₂ : ℝ≥0 → ℂ) (t₀ : ℝ≥0) (r : ℝ) : ℂ :=
  if r ≤ s₀ then η₁ r.toNNReal else η₂ ((s₀ : ℝ) + t₀ - r).toNNReal

theorem joinPath_zero : joinPath η₁ s₀ η₂ t₀ 0 = η₁ 0 := by
  simp [joinPath]

theorem image_joinPath (hp : η₁ s₀ = η₂ t₀) :
    joinPath η₁ s₀ η₂ t₀ '' Icc 0 ((s₀ : ℝ) + t₀) = prefixSet η₁ s₀ η₂ t₀ := by
  ext z
  constructor
  · rintro ⟨r, hr, rfl⟩
    unfold joinPath
    split_ifs with h
    · exact Or.inl ⟨r.toNNReal, ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 h⟩, rfl⟩
    · refine Or.inr ⟨_, ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 ?_⟩, rfl⟩
      linarith [not_le.1 h]
  · rintro (⟨s, hs, rfl⟩ | ⟨t, ht, rfl⟩)
    · refine ⟨s, ⟨s.coe_nonneg, by exact_mod_cast hs.2.trans le_self_add⟩, ?_⟩
      simp [joinPath, show (s : ℝ) ≤ s₀ from hs.2]
    · have ht' : (t : ℝ) ≤ t₀ := ht.2
      refine ⟨(s₀ : ℝ) + t₀ - t, ⟨by linarith [s₀.coe_nonneg], by linarith [t.coe_nonneg]⟩, ?_⟩
      unfold joinPath
      split_ifs with h
      · have htt : t = t₀ := le_antisymm ht.2 (by exact_mod_cast (show (t₀ : ℝ) ≤ t by linarith))
        rw [htt, ← hp]
        congr 1
        rw [show (s₀ : ℝ) + t₀ - t₀ = s₀ by ring, Real.toNNReal_coe]
      · congr 1
        rw [show (s₀ : ℝ) + t₀ - ((s₀ : ℝ) + t₀ - t) = t by ring, Real.toNNReal_coe]

theorem continuousOn_joinPath (hc₁ : ContinuousOn η₁ (Icc 0 s₀)) (hc₂ : ContinuousOn η₂ (Icc 0 t₀))
    (hp : η₁ s₀ = η₂ t₀) : ContinuousOn (joinPath η₁ s₀ η₂ t₀) (Icc 0 ((s₀ : ℝ) + t₀)) := by
  have hsplit : Icc (0 : ℝ) ((s₀ : ℝ) + t₀) = Icc 0 (s₀ : ℝ) ∪ Icc (s₀ : ℝ) ((s₀ : ℝ) + t₀) :=
    (Icc_union_Icc_eq_Icc s₀.coe_nonneg (by linarith [t₀.coe_nonneg])).symm
  rw [hsplit]
  refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
  · have h1 : ContinuousOn (fun r : ℝ => η₁ r.toNNReal) (Icc 0 (s₀ : ℝ)) :=
      hc₁.comp continuous_real_toNNReal.continuousOn fun r hr =>
        ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hr.2⟩
    refine h1.congr fun r hr => ?_
    simp [joinPath, hr.2]
  · have h2 : ContinuousOn (fun r : ℝ => η₂ ((s₀ : ℝ) + t₀ - r).toNNReal) (Icc (s₀ : ℝ) ((s₀ : ℝ) + t₀)) :=
      hc₂.comp (continuous_real_toNNReal.comp (by fun_prop)).continuousOn fun r hr =>
        ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 (by linarith [hr.1])⟩
    refine h2.congr fun r hr => ?_
    unfold joinPath
    split_ifs with h
    · have hr0 : r = s₀ := le_antisymm h hr.1
      rw [hr0, Real.toNNReal_coe, hp]
      show η₂ t₀ = η₂ ((s₀ : ℝ) + t₀ - s₀).toNNReal
      rw [show (s₀ : ℝ) + t₀ - s₀ = t₀ by ring, Real.toNNReal_coe]
    · rfl

theorem mapsTo_joinPath (hH₁ : MapsTo η₁ (Icc 0 s₀) Hbar) (hH₂ : MapsTo η₂ (Icc 0 t₀) Hbar) :
    MapsTo (joinPath η₁ s₀ η₂ t₀) (Icc 0 ((s₀ : ℝ) + t₀)) Hbar := by
  intro r hr
  unfold joinPath
  split_ifs with h
  · exact hH₁ ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 h⟩
  · exact hH₂ ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 (by linarith [not_le.1 h])⟩

end Join

/-! ### The chart -/

section Chart

variable {η₁ η₂ : ℝ≥0 → ℂ} {s₀ t₀ : ℝ≥0}

/-- A **regular point** for the chart at `(s₀, t₀)`: a point of the active domain, or a point `z` such that every
point of `(ℝ ∪ K) \ {z}` (`K` the two prefixes) lies in an unbounded preconnected subset of `(ℝ ∪ K) \ {z}`
(then `z` has a single access from the active domain: `eq_of_apply_eq_of_linked`). The contact point is regular
(`isUnboundedLinked_firstContact`), so is every real point off the prefixes (`isUnboundedLinked_of_notMem`), and
every point at all when the prefixes are simple (`isUnboundedLinked_of_injOn`). -/
def IsChartRegularPoint (η₁ : ℝ≥0 → ℂ) (s₀ : ℝ≥0) (η₂ : ℝ≥0 → ℂ) (t₀ : ℝ≥0) (z : ℂ) : Prop :=
  z ∈ activeDomain η₁ s₀ η₂ t₀ ∨ IsUnboundedLinked (({w : ℂ | w.im = 0} ∪ prefixSet η₁ s₀ η₂ t₀) \ {z})

/-! #### Regular points -/

theorem joinPath_end (hp : η₁ s₀ = η₂ t₀) : joinPath η₁ s₀ η₂ t₀ ((s₀ : ℝ) + t₀) = η₂ 0 := by
  unfold joinPath
  split_ifs with h
  · have ht0 : (t₀ : ℝ) = 0 := le_antisymm (by linarith) t₀.coe_nonneg
    have ht0' : t₀ = 0 := by exact_mod_cast ht0
    rw [ht0, add_zero, Real.toNNReal_coe, hp, ht0']
  · rw [sub_self, Real.toNNReal_zero]

/-- **The contact point is regular**: `(ℝ ∪ K) \ {η₁(s₀)}` is unbounded-linked when neither path visits
`η₁(s₀) = η₂(t₀)` before (the pieces `η₁[0, s₀)`, `η₂[0, t₀)` contain the real seeds). -/
theorem isUnboundedLinked_firstContact (hc₁ : ContinuousOn η₁ (Icc 0 s₀))
    (hc₂ : ContinuousOn η₂ (Icc 0 t₀)) (h0₁ : (η₁ 0).im = 0) (h0₂ : (η₂ 0).im = 0) (hp : η₁ s₀ = η₂ t₀)
    (hne₁ : ∀ s < s₀, η₁ s ≠ η₁ s₀) (hne₂ : ∀ t < t₀, η₂ t ≠ η₁ s₀) :
    IsUnboundedLinked (({w : ℂ | w.im = 0} ∪ prefixSet η₁ s₀ η₂ t₀) \ {η₁ s₀}) := by
  refine isUnboundedLinked_of_forall fun z hz hzp => ?_
  rcases hz with ⟨s, hs, rfl⟩ | ⟨t, ht, rfl⟩
  · have hss : s < s₀ := lt_of_le_of_ne hs.2 fun h => hzp (by rw [h])
    refine ⟨η₁ '' Ico 0 s₀, fun w hw => ?_, (isPreconnected_Ico).image _ (hc₁.mono Ico_subset_Icc_self),
      ⟨s, ⟨zero_le, hss⟩, rfl⟩, ?_, η₁ 0, ⟨0, ⟨le_rfl, lt_of_le_of_lt zero_le hss⟩, rfl⟩, h0₁⟩
    · obtain ⟨s', hs', rfl⟩ := hw; exact Or.inl ⟨s', Ico_subset_Icc_self hs', rfl⟩
    · rintro ⟨s', hs', he⟩; exact hne₁ s' hs'.2 he
  · have htt : t < t₀ := lt_of_le_of_ne ht.2 fun h => hzp (by rw [h, hp])
    refine ⟨η₂ '' Ico 0 t₀, fun w hw => ?_, (isPreconnected_Ico).image _ (hc₂.mono Ico_subset_Icc_self),
      ⟨t, ⟨zero_le, htt⟩, rfl⟩, ?_, η₂ 0, ⟨0, ⟨le_rfl, lt_of_le_of_lt zero_le htt⟩, rfl⟩, h0₂⟩
    · obtain ⟨t', ht', rfl⟩ := hw; exact Or.inr ⟨t', Ico_subset_Icc_self ht', rfl⟩
    · rintro ⟨t', ht', he⟩; exact hne₂ t' ht'.2 he

/-- **Points off the prefixes are regular** (the prefixes form one preconnected set containing a real seed). -/
theorem isUnboundedLinked_of_notMem (hc₁ : ContinuousOn η₁ (Icc 0 s₀)) (hc₂ : ContinuousOn η₂ (Icc 0 t₀))
    (h0₁ : (η₁ 0).im = 0) (hp : η₁ s₀ = η₂ t₀) {q : ℂ} (hq : q ∉ prefixSet η₁ s₀ η₂ t₀) :
    IsUnboundedLinked (({w : ℂ | w.im = 0} ∪ prefixSet η₁ s₀ η₂ t₀) \ {q}) := by
  have hKpc : IsPreconnected (prefixSet η₁ s₀ η₂ t₀) :=
    ((isPreconnected_Icc).image _ hc₁).union (η₁ s₀) ⟨s₀, ⟨zero_le, le_rfl⟩, rfl⟩
      ⟨t₀, ⟨zero_le, le_rfl⟩, hp.symm⟩ ((isPreconnected_Icc).image _ hc₂)
  exact isUnboundedLinked_of_forall fun z hz _ =>
    ⟨_, subset_rfl, hKpc, hz, hq, η₁ 0, Or.inl ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩, h0₁⟩

/-- Two simple prefixes meeting only at their common final point form one simple path. -/
theorem injOn_joinPath (hi₁ : InjOn η₁ (Icc 0 s₀)) (hi₂ : InjOn η₂ (Icc 0 t₀))
    (hmeet : ∀ s t : ℝ≥0, s ≤ s₀ → t ≤ t₀ → η₁ s = η₂ t → s = s₀ ∧ t = t₀) :
    InjOn (joinPath η₁ s₀ η₂ t₀) (Icc 0 ((s₀ : ℝ) + t₀)) := by
  have key : ∀ r ∈ Icc (0 : ℝ) ((s₀ : ℝ) + t₀), ∀ r' ∈ Icc (0 : ℝ) ((s₀ : ℝ) + t₀), r ≤ s₀ → ¬ r' ≤ s₀ →
      joinPath η₁ s₀ η₂ t₀ r ≠ joinPath η₁ s₀ η₂ t₀ r' := by
    intro r hr r' hr' h h' he
    simp only [joinPath, h, h', ↓reduceIte] at he
    have := hmeet _ _ (Real.toNNReal_le_iff_le_coe.2 h)
      (Real.toNNReal_le_iff_le_coe.2 (by linarith [not_le.1 h'])) he
    have h2 := congrArg (fun x : ℝ≥0 => (x : ℝ)) this.2
    simp only [Real.coe_toNNReal _ (show (0 : ℝ) ≤ (s₀ : ℝ) + t₀ - r' by linarith [hr'.2])] at h2
    linarith [not_le.1 h']
  intro r hr r' hr' he
  by_cases h : r ≤ s₀ <;> by_cases h' : r' ≤ s₀
  · simp only [joinPath, h, h', ↓reduceIte] at he
    have := hi₁ ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 h⟩ ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 h'⟩ he
    have h2 := congrArg (fun x : ℝ≥0 => (x : ℝ)) this
    simpa only [Real.coe_toNNReal _ hr.1, Real.coe_toNNReal _ hr'.1] using h2
  · exact (key r hr r' hr' h h' he).elim
  · exact (key r' hr' r hr h' h he.symm).elim
  · simp only [joinPath, h, h', ↓reduceIte] at he
    have := hi₂ ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 (by linarith [not_le.1 h])⟩
      ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 (by linarith [not_le.1 h'])⟩ he
    have h2 := congrArg (fun x : ℝ≥0 => (x : ℝ)) this
    simp only [Real.coe_toNNReal _ (show (0 : ℝ) ≤ (s₀ : ℝ) + t₀ - r by linarith [hr.2]),
      Real.coe_toNNReal _ (show (0 : ℝ) ≤ (s₀ : ℝ) + t₀ - r' by linarith [hr'.2])] at h2
    linarith

/-- **Every point is regular for simple prefixes**: if the concatenated path is injective, then for every `q`,
`(ℝ ∪ K) \ {q}` is unbounded-linked (removing `q = ζ(r)` leaves `ζ[0, r)` and `ζ(r, S]`, which contain the two real
seeds). -/
theorem isUnboundedLinked_of_injOn (hc₁ : ContinuousOn η₁ (Icc 0 s₀)) (hc₂ : ContinuousOn η₂ (Icc 0 t₀))
    (h0₁ : (η₁ 0).im = 0) (h0₂ : (η₂ 0).im = 0) (hp : η₁ s₀ = η₂ t₀)
    (hi : InjOn (joinPath η₁ s₀ η₂ t₀) (Icc 0 ((s₀ : ℝ) + t₀))) (q : ℂ) :
    IsUnboundedLinked (({w : ℂ | w.im = 0} ∪ prefixSet η₁ s₀ η₂ t₀) \ {q}) := by
  by_cases hqK : q ∉ prefixSet η₁ s₀ η₂ t₀
  · exact isUnboundedLinked_of_notMem hc₁ hc₂ h0₁ hp hqK
  rw [not_not, ← image_joinPath hp] at hqK
  obtain ⟨r, hr, rfl⟩ := hqK
  set ζ := joinPath η₁ s₀ η₂ t₀ with hζ
  have hζc := continuousOn_joinPath hc₁ hc₂ hp
  refine isUnboundedLinked_of_forall fun z hz hzq => ?_
  rw [← image_joinPath hp] at hz
  obtain ⟨r', hr', rfl⟩ := hz
  have hrr : r' ≠ r := fun h => hzq (by rw [h])
  rcases lt_or_gt_of_ne hrr with hlt | hgt
  · refine ⟨ζ '' Ico 0 r, ?_, (isPreconnected_Ico).image _ (hζc.mono fun x hx => ⟨hx.1, hx.2.le.trans hr.2⟩),
      ⟨r', ⟨hr'.1, hlt⟩, rfl⟩, ?_, ζ 0, ⟨0, ⟨le_rfl, lt_of_le_of_lt hr'.1 hlt⟩, rfl⟩, by
        rw [hζ, joinPath_zero]; exact h0₁⟩
    · rw [← image_joinPath hp]; exact image_mono fun x hx => ⟨hx.1, hx.2.le.trans hr.2⟩
    · rintro ⟨x, hx, he⟩
      exact (ne_of_lt hx.2) (hi ⟨hx.1, hx.2.le.trans hr.2⟩ hr he)
  · refine ⟨ζ '' Ioc r ((s₀ : ℝ) + t₀), ?_,
      (isPreconnected_Ioc).image _ (hζc.mono fun x hx => ⟨hr.1.trans hx.1.le, hx.2⟩),
      ⟨r', ⟨hgt, hr'.2⟩, rfl⟩, ?_, ζ ((s₀ : ℝ) + t₀), ⟨(s₀ : ℝ) + t₀, ⟨hgt.trans_le hr'.2, le_rfl⟩, rfl⟩, by
        rw [hζ, joinPath_end hp]; exact h0₂⟩
    · rw [← image_joinPath hp]; exact image_mono fun x hx => ⟨hr.1.trans hx.1.le, hx.2⟩
    · rintro ⟨x, hx, he⟩
      exact (ne_of_gt hx.1) (hi ⟨hr.1.trans hx.1.le, hx.2⟩ hr he)

/-- **The pathwise chart at a first contact** `(s₀, t₀)`, with `D = activeDomain η₁ s₀ η₂ t₀`: `φ` is a common
active chart of `D` at `η₁(s₀)`; `ψ` is its inverse on `ℍ` (holomorphic, a bijection onto `D`), continuous on `ℍ̄`,
with `ψ(0) = η₁(s₀)`, values off `D` off `ℍ`, and bounded displacement; `lift` is a continuous branch of `arg φ′` on
`D`; at every regular point `z ∈ closure D` the chart has a forward limit `w` along `D`, and `w` is the only point of
`ℍ̄` with `ψ w = z` (the active prime end, Aux. 80). -/
def IsFirstContactChart (η₁ : ℝ≥0 → ℂ) (s₀ : ℝ≥0) (η₂ : ℝ≥0 → ℂ) (t₀ : ℝ≥0) (φ ψ : ℂ → ℂ)
    (lift : ℂ → ℝ) : Prop :=
  IsActiveChart (activeDomain η₁ s₀ η₂ t₀) (η₁ s₀) φ ∧ BijOn ψ H (activeDomain η₁ s₀ η₂ t₀) ∧
    (∀ w ∈ H, φ (ψ w) = w) ∧ (∀ w ∉ H, ψ w ∉ activeDomain η₁ s₀ η₂ t₀) ∧
    ContinuousOn lift (activeDomain η₁ s₀ η₂ t₀) ∧
    (∀ z ∈ activeDomain η₁ s₀ η₂ t₀, deriv φ z = (‖deriv φ z‖ : ℂ) * exp (I * (lift z : ℂ))) ∧
    DifferentiableOn ℂ ψ H ∧ ContinuousOn ψ Hbar ∧ ψ 0 = η₁ s₀ ∧ (∃ M : ℝ, ∀ w ∈ Hbar, ‖ψ w - w‖ ≤ M) ∧
    ∀ z ∈ closure (activeDomain η₁ s₀ η₂ t₀), IsChartRegularPoint η₁ s₀ η₂ t₀ z →
      ∃ w ∈ Hbar, Tendsto φ (𝓝[activeDomain η₁ s₀ η₂ t₀] z) (𝓝 w) ∧ ψ w = z ∧
        ∀ w' ∈ Hbar, ψ w' = z → w' = w

/-- `exp u = |exp u| e^{i Im u}`. -/
theorem exp_eq_norm_mul_exp_im (u : ℂ) : exp u = (‖exp u‖ : ℂ) * exp (I * (u.im : ℂ)) := by
  rw [norm_exp, ofReal_exp, ← exp_add]
  congr 1
  apply Complex.ext <;> simp

theorem mem_H_or_im_eq_zero {w : ℂ} (hw : w ∈ Hbar) : w ∈ H ∨ w.im = 0 :=
  (show (0 : ℝ) ≤ w.im from hw).lt_or_eq.imp id Eq.symm

theorem add_ofReal_mem_H {w : ℂ} (hw : w ∈ H) (x : ℝ) : w + x ∈ H := by
  show 0 < (w + x).im; simpa using (show 0 < w.im from hw)

theorem sub_ofReal_mem_H {w : ℂ} (hw : w ∈ H) (x : ℝ) : w - x ∈ H := by
  show 0 < (w - x).im; simpa using (show 0 < w.im from hw)

/-- **The active chart at a first contact** (pathwise; Lemma 7.8, p. 290; Aux. 80, p. 540). For continuous paths
`η₁`, `η₂` in `ℍ̄` from real points with a common point `η₁(s₀) = η₂(t₀)` that neither visits before, lying in the
closure of the active domain, there is a chart `IsFirstContactChart`. -/
theorem exists_isFirstContactChart (hc₁ : ContinuousOn η₁ (Icc 0 s₀)) (hc₂ : ContinuousOn η₂ (Icc 0 t₀))
    (hH₁ : MapsTo η₁ (Icc 0 s₀) Hbar) (hH₂ : MapsTo η₂ (Icc 0 t₀) Hbar) (h0₁ : (η₁ 0).im = 0)
    (h0₂ : (η₂ 0).im = 0) (hp : η₁ s₀ = η₂ t₀) (hne₁ : ∀ s < s₀, η₁ s ≠ η₁ s₀)
    (hne₂ : ∀ t < t₀, η₂ t ≠ η₁ s₀) (hcl : η₁ s₀ ∈ closure (activeDomain η₁ s₀ η₂ t₀)) :
    ∃ (φ ψ : ℂ → ℂ) (lift : ℂ → ℝ), IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift := by
  set K := prefixSet η₁ s₀ η₂ t₀ with hKdef
  set p := η₁ s₀ with hpdef
  have hS : (0 : ℝ) ≤ (s₀ : ℝ) + t₀ := by positivity
  have hζc := continuousOn_joinPath hc₁ hc₂ hp
  have hζH := mapsTo_joinPath (η₁ := η₁) (η₂ := η₂) hH₁ hH₂
  have hζ0 : (joinPath η₁ s₀ η₂ t₀ 0).im = 0 := by rw [joinPath_zero]; exact h0₁
  have himg : joinPath η₁ s₀ η₂ t₀ '' Icc 0 ((s₀ : ℝ) + t₀) = K := image_joinPath hp
  have hKc : IsCompact K := himg ▸ isCompact_Icc.image_of_continuousOn hζc
  have hAD : activeDomain η₁ s₀ η₂ t₀ = H \ fillH K := activeDomain_eq hKc.isClosed
  have hA : IsHPHull (fillH K) := himg ▸ YuanCharacterisation.isHPHull_fillH_image_of_im hζc hS hζ0
  obtain ⟨F, hF1, hF2, hFd, hFc, hFi, -, hFinf, hFbd, M, hM⟩ :=
    YuanCharacterisation.exists_extension_symm hS hζc hζH hζ0
  rw [himg] at hF1 hF2 hFbd
  set A := fillH K with hAdef
  set D := H \ A with hDdef
  set g := ConformalImage.mapOut A with hgdef
  have hg : IsMapOut A g := ConformalImage.isMapOut_mapOut hA
  obtain ⟨M', hM'⟩ := hg.exists_norm_sub_le hA
  have hDo : IsOpen D := hA.isOpen
  have hDH : D ⊆ H := sdiff_subset
  have hFD : MapsTo F H D := fun w hw => (hF1 w hw).1
  have hFs : SurjOn F H D := fun z hz => ⟨g z, hg.1.2.mapsTo hz, hF2 z hz⟩
  have hGD : ∀ z ∈ D, g z ∈ H ∧ F (g z) = z := fun z hz => ⟨hg.1.2.mapsTo hz, hF2 z hz⟩
  set E : Set ℂ := {z : ℂ | z.im = 0} ∪ K with hEdef
  have hDE : Disjoint D E := by
    refine Set.disjoint_left.2 fun z hzD hzE => ?_
    rcases hzE with h | h
    · exact (ne_of_gt (show 0 < z.im from hzD.1)) h
    · exact hzD.2 ⟨hzD.1, Or.inl (subset_closure h)⟩
  have hfrE : frontier D ⊆ E := by
    have := frontier_H_diff_fillH_subset hKc.isBounded (A := K)
    rwa [hKc.isClosed.closure_eq] at this
  have hfrD : ∀ w ∈ frontier D, w ∉ D := fun w hw hwD => by
    rw [hDo.frontier_eq] at hw; exact hw.2 hwD
  have hpK : p ∈ K := Or.inl ⟨s₀, ⟨zero_le, le_rfl⟩, rfl⟩
  have hpD : p ∉ D := fun h => Set.disjoint_left.1 hDE h (Or.inr hpK)
  have hqp : IsUnboundedLinked (E \ {p}) :=
    isUnboundedLinked_firstContact hc₁ hc₂ h0₁ h0₂ hp hne₁ hne₂
  have hfib : ∀ q : ℂ, IsUnboundedLinked (E \ {q}) → ∀ x y : ℝ, F x = q → F y = q → x = y :=
    fun q hq x y hx hy => eq_of_apply_eq_of_linked hDo hFd hFc hFi hFD hFs hFbd hFinf hDE hfrE hq hx hy
  rw [hAD] at hcl
  obtain ⟨x₀, hFx₀, hgx₀⟩ := exists_tendsto_of_fibre hFc hFD hGD hM' hcl hpD (hfib p hqp)
  unfold IsFirstContactChart
  rw [hAD]
  set φ : ℂ → ℂ := fun z => g z - x₀ with hφdef
  set ψ : ℂ → ℂ := fun w => if 0 ≤ w.im then F (w + x₀) else w with hψdef
  have hψH : ∀ w ∈ Hbar, ψ w = F (w + x₀) := fun w hw => by
    simp only [hψdef, show (0 : ℝ) ≤ w.im from hw, ↓reduceIte]
  have hφd : DifferentiableOn ℂ φ D := hg.1.1.sub_const _
  have hφH : ∀ z ∈ D, φ z ∈ H := fun z hz => sub_ofReal_mem_H (hg.1.2.mapsTo hz) x₀
  have hφinj : InjOn φ D := fun z hz z' hz' h => hg.1.2.injOn hz hz' (sub_left_inj.1 h)
  have hψφ : ∀ z ∈ D, ψ (φ z) = z := fun z hz => by
    rw [hψH _ (QuantumZipper.H_subset_Hbar (hφH z hz)), hφdef, sub_add_cancel]; exact hF2 z hz
  have hφψ : ∀ w ∈ H, φ (ψ w) = w := fun w hw => by
    rw [hψH _ (QuantumZipper.H_subset_Hbar hw)]
    show g (F (w + x₀)) - x₀ = w
    rw [(hF1 _ (add_ofReal_mem_H hw x₀)).2, add_sub_cancel_right]
  -- the preimages under `ψ` in `ℍ̄` of a point of `D` and of a boundary point with one real preimage
  have hreal_off : ∀ w ∈ Hbar, w.im = 0 → ψ w ∉ D := fun w hw him => by
    rw [hψH w hw]
    refine hfrD _ (hFbd ⟨show (0 : ℝ) ≤ (w + x₀).im by simp [him], fun h => ?_⟩)
    have : (0 : ℝ) < (w + x₀).im := h
    simp [him] at this
  have huniqD : ∀ z ∈ D, ∀ w' ∈ Hbar, ψ w' = z → w' = φ z := by
    intro z hz w' hw' hψz
    rcases mem_H_or_im_eq_zero hw' with h | h
    · have h1 : F (w' + x₀) = F (g z) := by rw [← hψH w' hw', hψz, hF2 z hz]
      have := hFi (add_ofReal_mem_H h x₀) (hg.1.2.mapsTo hz) h1
      show w' = g z - x₀
      rw [← this, add_sub_cancel_right]
    · exact absurd (hψz ▸ hz) (hreal_off w' hw' h)
  have hbdry : ∀ q ∈ closure D, q ∉ D → (∀ x y : ℝ, F x = q → F y = q → x = y) →
      ∃ w ∈ Hbar, Tendsto φ (𝓝[D] q) (𝓝 w) ∧ ψ w = q ∧ ∀ w' ∈ Hbar, ψ w' = q → w' = w := by
    intro q hq hqD hfq
    obtain ⟨x₁, hFx₁, hgx₁⟩ := exists_tendsto_of_fibre hFc hFD hGD hM' hq hqD hfq
    have hw : ((x₁ - x₀ : ℝ) : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((x₁ - x₀ : ℝ) : ℂ).im by simp
    refine ⟨((x₁ - x₀ : ℝ) : ℂ), hw, ?_, ?_, ?_⟩
    · have := hgx₁.sub_const (x₀ : ℂ)
      rwa [← ofReal_sub] at this
    · rw [hψH _ hw, ← ofReal_add, sub_add_cancel, hFx₁]
    · intro w' hw' hψw'
      rcases mem_H_or_im_eq_zero hw' with h | h
      · exact absurd (hψw' ▸ hψH w' hw' ▸ hFD (add_ofReal_mem_H h x₀)) hqD
      · have hw'r : w' = ((w'.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h])
        have h1 : F ((w'.re + x₀ : ℝ) : ℂ) = q := by
          rw [ofReal_add, ← hw'r, ← hψH w' hw', hψw']
        have h2 := hfq _ _ h1 hFx₁
        rw [hw'r, show w'.re = x₁ - x₀ by linarith]
  -- the lift
  have hφne : ∀ z ∈ D, deriv φ z ≠ 0 := fun z hz =>
    QuantumZipper.CA.deriv_ne_zero_of_injOn hDo hφd hφinj hz
  obtain ⟨L, hLd, hL⟩ := exists_isDerivLog hDo hA.2.2.2 hφd hφne
  refine ⟨φ, ψ, fun z => (L z).im, ⟨⟨fun z hz => hφH z hz, hφinj, fun w hw => ?_⟩, hφd, ?_, ?_⟩,
    ⟨fun w hw => ?_, fun w hw w' hw' h => ?_, fun z hz => ⟨φ z, hφH z hz, hψφ z hz⟩⟩, hφψ, ?_,
    Complex.continuous_im.comp_continuousOn hLd.continuousOn, fun z hz => ?_, ?_, ?_, ?_,
    ⟨M + |x₀|, fun w hw => ?_⟩, ?_⟩
  · -- `φ` is onto `ℍ`
    obtain ⟨z, hz, hgz⟩ := hg.1.2.surjOn (add_ofReal_mem_H hw x₀)
    exact ⟨z, hz, show g z - x₀ = w by rw [hgz, add_sub_cancel_right]⟩
  · -- `φ → 0` at the contact point
    have := hgx₀.sub_const (x₀ : ℂ)
    rwa [sub_self] at this
  · -- `φ → ∞` at `∞`
    have h1 : Tendsto (fun z : ℂ => ‖z‖ - (M' + |x₀|)) (Bornology.cobounded ℂ ⊓ 𝓟 D) atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_norm_cobounded_atTop.mono_left inf_le_left)
    refine tendsto_norm_atTop_iff_cobounded.1 (tendsto_atTop_mono' _ ?_ h1)
    filter_upwards [mem_inf_of_right (mem_principal_self D)] with z hz
    have h2 := hM' z hz
    have h3 : ‖φ z‖ ≥ ‖z‖ - ‖g z - z‖ - ‖(x₀ : ℂ)‖ := by
      have : φ z = z + (g z - z) - x₀ := show g z - x₀ = _ by ring
      rw [this]
      have := norm_sub_norm_le (z + (g z - z)) (x₀ : ℂ)
      have := norm_sub_norm_le z (-(g z - z))
      rw [sub_neg_eq_add] at this
      linarith [norm_neg (g z - z)]
    rw [norm_real, Real.norm_eq_abs] at h3
    linarith
  · -- `ψ` maps `ℍ` into `D`
    rw [hψH w (QuantumZipper.H_subset_Hbar hw)]; exact hFD (add_ofReal_mem_H hw x₀)
  · -- `ψ` is injective on `ℍ`
    rw [hψH w (QuantumZipper.H_subset_Hbar hw), hψH w' (QuantumZipper.H_subset_Hbar hw')] at h
    exact add_left_injective (x₀ : ℂ) (hFi (add_ofReal_mem_H hw x₀) (add_ofReal_mem_H hw' x₀) h)
  · -- off `ℍ`, `ψ` takes values off `D`
    intro w hw
    by_cases hw0 : 0 ≤ w.im
    · exact hreal_off w hw0 (le_antisymm (not_lt.1 hw) hw0)
    · simp only [hψdef, hw0, ↓reduceIte]; exact fun h => hw (hDH h)
  · -- the lift is a branch of `arg φ′`
    rw [← hL z hz]
    exact exp_eq_norm_mul_exp_im (L z)
  · -- `ψ` is holomorphic on `ℍ`
    refine (hFd.comp (differentiableOn_id.add_const _) fun w hw => add_ofReal_mem_H hw x₀).congr ?_
    intro w hw; exact hψH w (QuantumZipper.H_subset_Hbar hw)
  · -- `ψ` is continuous on `ℍ̄`
    refine (hFc.comp ((by fun_prop : Continuous fun w : ℂ => w + (x₀ : ℂ)).continuousOn) fun w hw => ?_).congr ?_
    · show (0 : ℝ) ≤ (w + x₀).im; simpa using (show (0 : ℝ) ≤ w.im from hw)
    · intro w hw; exact hψH w hw
  · -- `ψ 0 = η₁ s₀`
    rw [hψH 0 (show (0 : ℝ) ≤ (0 : ℂ).im by simp), zero_add, hFx₀]
  · -- bounded displacement
    rw [hψH w hw]
    have h1 := hM (w + x₀) (show (0 : ℝ) ≤ (w + x₀).im by simpa using (show (0 : ℝ) ≤ w.im from hw))
    calc ‖F (w + x₀) - w‖ = ‖(F (w + x₀) - (w + x₀)) + x₀‖ := by ring_nf
      _ ≤ ‖F (w + x₀) - (w + x₀)‖ + ‖(x₀ : ℂ)‖ := norm_add_le _ _
      _ ≤ M + |x₀| := by rw [norm_real, Real.norm_eq_abs]; linarith
  · -- forward limits at the regular points
    intro z hz hreg
    by_cases hzD : z ∈ D
    · exact ⟨φ z, QuantumZipper.H_subset_Hbar (hφH z hzD), (hφd.continuousOn z hzD).tendsto.mono_left le_rfl,
        hψφ z hzD, fun w' hw' h => huniqD z hzD w' hw' h⟩
    · rcases hreg with hzD' | hlink
      · rw [hAD] at hzD'; exact (hzD hzD').elim
      · exact hbdry z hz hzD (hfib z hlink)

end Chart

end Restart

end InteractingSLE
