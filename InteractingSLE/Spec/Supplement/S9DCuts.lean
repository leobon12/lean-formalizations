/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9DActivity
import InteractingSLE.Spec.Supplement.S9Frontier
import InteractingSLE.Spec.Supplement.G7Carrier
import InteractingSLE.Spec.Sec2.AssemblyCode
import InteractingSLE.Spec.Restart.ChartDataChart

/-!
# Supplement §9: dyadic interior cuts and the ordinary retained pair of Lemmas W1, W2 and W2a

Packet PROVE-W5-REST. Sources: Lemma W1 and its proof (`source/spec/p529-576.md` L28–L56, pp. 529–530), Lemma W2's
proof (L62–L68, p. 531), Lemma W2a's proof (L130–L139, p. 533).

The proofs of W2 and W2a condition on a **rational** pair of own cuts `(r, s)` at which the old prefixes form an
ordinary retained pair (interior tips, each off the other prefix, jointly active, ordered completions), and whose
fresh portions contain two contacts `p = α(a) = β(t)`, `q = α(b) = β(v)` with `a < b`, `v < t` and no contact in the
lower rectangle `[r, b) × [s, t)` ("Their common first point would therefore have first parameter at most `a` and
second parameter at most `v`, contradicting (W1.1)"). This file proves, pathwise:

* `exists_mem_H_of_isGeneratingTrace`: a generating trace has no real subarc ("Such choices exist because a
  nontrivial real subarc would have zero capacity"), hence `exists_dyad_mem_H`: dyadic interior cuts are dense;
* `isOrdinaryRetainedPair_of_cuts`: the verification of `Supp7.IsOrdinaryRetainedPair` at cuts with the fresh
  contact structure (the opposite-hull exclusion of W1 and Aux. lemma 90, `Supp9D.aux90`);
* `IsFreshLowerRectangle`: the configuration that Lemma 7.7 excludes at an ordinary retained pair.

The countable family of cuts is the set `dyadSet` of dyadic times.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex Bornology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE

namespace Supp9D

open HalfPlaneSep Supp9B Sec2.Assembly

/-! ### Dyadic times -/

/-- The countable set of dyadic times `k / 2ⁿ`. -/
def dyadSet : Set ℝ≥0 := range fun p : ℕ × ℕ => dyad p.1 p.2

theorem countable_dyadSet : dyadSet.Countable := countable_range _

theorem exists_dyadSet_btwn {x y : ℝ≥0} (h : x < y) : ∃ r ∈ dyadSet, x < r ∧ r < y := by
  obtain ⟨n, k, h1, h2⟩ := exists_dyad_btwn (ζ := (y : ℝ≥0∞)) (ENNReal.coe_lt_coe.2 h)
  exact ⟨dyad n k, ⟨(n, k), rfl⟩, h1, ENNReal.coe_lt_coe.1 h2⟩

/-! ### No real subarc -/

/-- Fillings only see the part of a closed set in `ℍ`. -/
theorem fillH_eq_of_inter_H_eq {A A' : Set ℂ} (hA : IsClosed A) (hA' : IsClosed A')
    (h : A ∩ H = A' ∩ H) : fillH A = fillH A' := by
  have hd : H \ A = H \ A' := by
    ext z
    constructor
    · rintro ⟨hz, hzA⟩
      exact ⟨hz, fun hzA' => hzA (h.symm ▸ ⟨hzA', hz⟩ : z ∈ A ∩ H).1⟩
    · rintro ⟨hz, hzA'⟩
      exact ⟨hz, fun hzA => hzA' (h ▸ ⟨hzA, hz⟩ : z ∈ A' ∩ H).1⟩
  ext z
  simp only [fillH, hA.closure_eq, hA'.closure_eq, hd, mem_ofPred_eq]
  constructor
  · rintro ⟨hz, h1 | h1⟩
    · exact ⟨hz, Or.inl (h ▸ ⟨h1, hz⟩ : z ∈ A' ∩ H).1⟩
    · exact ⟨hz, Or.inr h1⟩
  · rintro ⟨hz, h1 | h1⟩
    · exact ⟨hz, Or.inl (h.symm ▸ ⟨h1, hz⟩ : z ∈ A ∩ H).1⟩
    · exact ⟨hz, Or.inr h1⟩

/-- **A generating trace has no real subarc** (proof of Lemma W1, p. 530: "a nontrivial real subarc would have zero
capacity"): if `η((x, y)) ⊆ ℝ` with `y < T`, the hulls at times `x < m < y` would coincide, while `hcap(K_t) = 2t`
(`fwdHull_ne_of_lt`, for the driver frozen after a time in `(m, T)`). -/
theorem exists_mem_H_of_isGeneratingTrace {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w T η) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0)
    {x y : ℝ≥0} (hxy : x < y) (hy : (y : ℝ≥0∞) < T) : ∃ z ∈ Ioo x y, η z ∈ H := by
  by_contra hno
  push Not at hno
  obtain ⟨m, hxm, hmy⟩ := exists_between hxy
  have hm : (m : ℝ≥0∞) < T := lt_trans (ENNReal.coe_lt_coe.2 hmy) hy
  have hx : (x : ℝ≥0∞) < T := lt_trans (ENNReal.coe_lt_coe.2 hxy) hy
  have hcont : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T → IsCompact (η '' Icc 0 s) := fun s hs =>
    isCompact_Icc.image_of_continuousOn (hη.2.1.mono fun t ht =>
      (ENNReal.coe_le_coe.2 ht.2).trans hs.le)
  have hAeq : (η '' Icc 0 x) ∩ H = (η '' Icc 0 m) ∩ H := by
    ext z
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hz⟩
      exact ⟨⟨t, ⟨ht.1, ht.2.trans hxm.le⟩, rfl⟩, hz⟩
    · rintro ⟨⟨t, ht, rfl⟩, hz⟩
      refine ⟨⟨t, ⟨ht.1, not_lt.1 fun hxt => hno t ⟨hxt, ht.2.trans_lt hmy⟩ hz⟩, rfl⟩, hz⟩
  have hfill := fillH_eq_of_inter_H_eq (hcont x hx).isClosed (hcont m hm).isClosed hAeq
  have hF1 := (isFilling_iff_inter_H_eq_fillH (hcont x hx).isBounded (hcont x hx).isClosed).1 (hη.2.2 x hx)
  have hF2 := (isFilling_iff_inter_H_eq_fillH (hcont m hm).isBounded (hcont m hm).isClosed).1 (hη.2.2 m hm)
  rw [inter_eq_left.2 (fun _ hz => hz.1)] at hF1 hF2
  obtain ⟨t₂, hmt₂, ht₂T⟩ := exists_real_btwn_of_lt hm
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg m).trans hmt₂.le
  have hW₂c : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hw ht₂T
  have hW₂0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂, hw0]
  have heq : ∀ r ∈ Icc (0 : ℝ) t₂, (fun s : ℝ => w s.toNNReal) r = frozenDrive w t₂ r := fun r hr =>
    (frozenDrive_eq hr).symm
  have hxt₂ : (x : ℝ) < t₂ := lt_trans (by exact_mod_cast hxm) hmt₂
  rw [fwdHull_eq_of_eqOn (NNReal.coe_nonneg x) hxt₂ heq] at hF1
  rw [fwdHull_eq_of_eqOn (NNReal.coe_nonneg m) hmt₂ heq] at hF2
  exact fwdHull_ne_of_lt hW₂c hW₂0 (NNReal.coe_nonneg x) (by exact_mod_cast hxm)
    (hF1.trans (hfill.trans hF2.symm))

/-- **Dyadic interior cuts are dense** along a path without real subarcs: between `x < y` (inside the open available
interval, where the path is continuous) there is a dyadic time with an interior point. -/
theorem exists_dyad_mem_H {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} (hc : ContinuousOn η {t | (t : ℝ≥0∞) ≤ ζ})
    (hno : ∀ x y : ℝ≥0, x < y → (y : ℝ≥0∞) < ζ → ∃ z ∈ Ioo x y, η z ∈ H) {x y : ℝ≥0} (hxy : x < y)
    (hy : (y : ℝ≥0∞) < ζ) : ∃ r ∈ dyadSet, x < r ∧ r < y ∧ η r ∈ H := by
  obtain ⟨z, hz, hzH⟩ := hno x y hxy hy
  have hzζ : (z : ℝ≥0∞) < ζ := lt_trans (ENNReal.coe_lt_coe.2 hz.2) hy
  have hca : ContinuousAt η z :=
    hc.continuousAt (mem_of_superset ((Supp9.isOpen_setOf_coe_lt ζ).mem_nhds hzζ)
      fun t (ht : (t : ℝ≥0∞) < ζ) => (le_of_lt ht : (t : ℝ≥0∞) ≤ ζ))
  have hU : ∀ᶠ t in 𝓝 z, η t ∈ H ∧ t ∈ Ioo x y :=
    (hca.eventually (QuantumZipper.isOpen_H.mem_nhds hzH)).and (isOpen_Ioo.mem_nhds hz)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hU
  obtain ⟨r, hr, hzr, hrz⟩ := exists_dyadSet_btwn (show z < z + ⟨ε / 2, by positivity⟩ from
    lt_add_of_pos_right z (by show (0 : ℝ) < ε / 2; positivity))
  have hd : dist r z < ε := by
    rw [NNReal.dist_eq]
    have h1 : (z : ℝ) < r := by exact_mod_cast hzr
    have h2 : (r : ℝ) < z + ε / 2 := by exact_mod_cast hrz
    rw [abs_of_pos (by linarith)]
    linarith
  obtain ⟨h1, h2⟩ := hball hd
  exact ⟨r, hr, h2.1, h2.2, h1⟩

/-- A flow line has, almost surely, no real subarc strictly before its lifetime (its translate is a generating trace
of the driver, which is continuous before the lifetime with `W 0 = 0`). -/
theorem ae_exists_mem_H_of_isFlowLine {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₀ θ : ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hη : IsFlowLine κ b jumps x₀ θ P h η ζ) :
    ∀ᵐ ω ∂P, ∀ x y : ℝ≥0, x < y → (y : ℝ≥0∞) < ζ ω → ∃ z ∈ Ioo x y, η ω z ∈ H := by
  obtain ⟨h', 𝓕, W, VL, VR, B, -, hcoup, htr⟩ := hη
  filter_upwards [htr, hcoup.1.2.2.2.2] with ω hωt hωp
  intro x y hxy hy
  obtain ⟨z, hz, hzH⟩ := exists_mem_H_of_isGeneratingTrace hωt hωp.2.2.2.1 hωp.1 hxy hy
  refine ⟨z, hz, ?_⟩
  have : (η ω z - x₀).im = (η ω z).im := by simp
  show 0 < (η ω z).im
  rw [← this]
  exact hzH

/-! ### The configuration excluded by Lemma 7.7 at a retained pair -/

/-- **A fresh lower rectangle at the cuts `(u, r)`** (proofs of W2, p. 531, and W2a, p. 533): the fresh portions
`α([u, b])`, `β([r, t])` avoid the retained union `A = α([0, u]) ∪ β([0, r])` strictly after the cuts, contain the two
contacts `α(a) = β(t)` and `α(b) = β(v)` with `u < a < b`, `r < v < t` (within the available lifetimes), and have no
contact in the lower rectangle `[u, b) × [r, t)`. Lemma 7.7, applied to the canonical continuations at the retained
pair, says their common first contact would lie in this empty rectangle. -/
def IsFreshLowerRectangle (α : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (u : ℝ≥0) (β : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) (r : ℝ≥0) :
    Prop :=
  ∃ a t b v : ℝ≥0, u < a ∧ a < b ∧ (b : ℝ≥0∞) ≤ ζ₁ ∧ r < v ∧ v < t ∧ (t : ℝ≥0∞) ≤ ζ₂ ∧
    α a = β t ∧ α b = β v ∧
    (∀ x : ℝ≥0, u < x → x < b → α x ∉ α '' Icc 0 u ∪ β '' Icc 0 r) ∧
    (∀ y : ℝ≥0, r < y → y < t → β y ∉ α '' Icc 0 u ∪ β '' Icc 0 r) ∧
    ∀ x y : ℝ≥0, u ≤ x → x < b → r ≤ y → y < t → α x ≠ β y

/-- **The ordinary retained pair at the cuts of W1 / W2a** (proof of W1, p. 530: "The point `p` is a future unvisited
point of `β` after `s`, and `q` is a future unvisited point of `α` after `r`. Such a point is outside the older
individual filled hull. […] The connected fresh arc from `α(r)` to `p` avoids the second old range. […] Aux. lemma 90
therefore gives joint activity of both interior tips"). At cuts `(r, s)` with interior tips, ordered completions, and
fresh portions `α([r, b])`, `β([s, t])` off the other old prefix that contain contacts `α(a) = β(t)`, `α(b) = β(v)`
(`a ≤ b`, `v ≤ t`; the two contacts may coincide), the pair is an ordinary retained pair. -/
theorem isOrdinaryRetainedPair_of_cuts {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {r s a t b v : ℝ≥0}
    (h0 : (α 0).im = 0) (hβ0 : (β 0).im = 0) (hseed : (β 0).re ≤ (α 0).re)
    (hcomp : HasOrderedProperCompletions α r β s) (hαc : ContinuousOn α (Icc 0 b))
    (hβc : ContinuousOn β (Icc 0 t))
    (hαcomp : ∀ x, r < x → x < b → ∃ α', IsProperCompletion α x α')
    (hβcomp : ∀ y, s < y → y < t → ∃ β', IsProperCompletion β y β')
    (hαim : ∀ x ≤ b, 0 ≤ (α x).im) (hβim : ∀ y ≤ t, 0 ≤ (β y).im)
    (hra : r < a) (hab : a ≤ b) (hsv : s < v) (hvt : v ≤ t) (hp : α a = β t) (hq : α b = β v)
    (hαH : α r ∈ H) (hβH : β s ∈ H)
    (hαfresh : ∀ x ∈ Icc r b, α x ∉ β '' Icc 0 s) (hβfresh : ∀ y ∈ Icc s t, β y ∉ α '' Icc 0 r)
    (hrζ : (r : ℝ≥0∞) < ζ₁) (hsζ : (s : ℝ≥0∞) < ζ₂) :
    Supp7.IsOrdinaryRetainedPair α ζ₁ r β ζ₂ s := by
  obtain ⟨αn, βn, hαn, hβn, hord⟩ := hcomp
  have hcB : IsCompact (β '' Icc 0 s) := by
    rw [show β '' Icc 0 s = βn '' Icc 0 s from image_congr fun y hy => (hβn.2.2.2.2 y hy.2).symm]
    exact isCompact_Icc.image hβn.1
  have hcA : IsCompact (α '' Icc 0 r) := by
    rw [show α '' Icc 0 r = αn '' Icc 0 r from image_congr fun x hx => (hαn.2.2.2.2 x hx.2).symm]
    exact isCompact_Icc.image hαn.1
  -- the opposite-hull exclusions
  have hpacc : β t ∈ closure (H \ fillH (β '' Icc 0 s)) :=
    mem_closure_of_later (hsv.trans_le hvt) ((hβc t ⟨zero_le, le_rfl⟩).mono fun y hy => ⟨zero_le, hy.2.le⟩)
      hβcomp
  have hqacc : α b ∈ closure (H \ fillH (α '' Icc 0 r)) :=
    mem_closure_of_later (hra.trans_le hab) ((hαc b ⟨zero_le, le_rfl⟩).mono fun x hx => ⟨zero_le, hx.2.le⟩)
      hαcomp
  have hαout : α r ∈ H \ fillH (β '' Icc 0 s) := by
    refine mem_H_diff_fillH_of_arc hcB.isClosed (X := α '' Icc r a)
      (isPreconnected_Icc.image _ (hαc.mono fun x hx => ⟨zero_le, hx.2.trans hab⟩)) ?_
      ⟨a, ⟨hra.le, le_rfl⟩, rfl⟩ (by rw [hp]; exact hpacc) ⟨r, ⟨le_rfl, hra.le⟩, rfl⟩ hαH
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hαim x (hx.2.trans hab), hαfresh x ⟨hx.1, hx.2.trans hab⟩⟩
  have hβout : β s ∈ H \ fillH (α '' Icc 0 r) := by
    refine mem_H_diff_fillH_of_arc hcA.isClosed (X := β '' Icc s v)
      (isPreconnected_Icc.image _ (hβc.mono fun y hy => ⟨zero_le, hy.2.trans hvt⟩)) ?_
      ⟨v, ⟨hsv.le, le_rfl⟩, rfl⟩ (by rw [← hq]; exact hqacc) ⟨s, ⟨le_rfl, hsv.le⟩, rfl⟩ hβH
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨hβim y (hy.2.trans hvt), hβfresh y ⟨hy.1, hy.2.trans hvt⟩⟩
  obtain ⟨hact₁, hact₂⟩ := aux90 hαn hβn hord h0 hβ0 hseed
  have hD : activeDomain α r β s = H \ fillH (α '' Icc 0 r ∪ β '' Icc 0 s) :=
    Restart.activeDomain_eq (hcA.union hcB).isClosed
  refine ⟨hrζ, hsζ, hαH, hβH, hβfresh s ⟨le_rfl, hsv.le.trans hvt⟩,
    hαfresh r ⟨le_rfl, hra.le.trans hab⟩, ?_, ?_, ⟨αn, βn, hαn, hβn, hord⟩⟩
  · rw [hD]; exact hact₁ hαout
  · rw [hD]; exact hact₂ hβout

/-! ### Dyadic cuts in a contact-free box -/

section Box

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}

/-- **Dyadic interior cuts in a matched contact-free gap.** Let the contacts of `α((r, b])` and `β((s, t])` be only
`α(a) = β(t)` and `α(b) = β(v)` (`r < a < b`, `s < v < t`), let the fresh portions `α((r, b])`, `β((s, t])` avoid the
other old prefix, and let every pair of cuts in `[r, a) × [s, v)` have ordered proper completions. Then there are
dyadic cuts `r' ∈ (r, a)`, `s' ∈ (s, v)` with interior tips at which the pair is an ordinary retained pair with a
fresh lower rectangle (proofs of W1 and W2a: "Choose `r ∈ (a₋, a)` and `s ∈ (v₋, v)` rational at interior trace
points"). -/
theorem exists_dyad_cuts_of_box (hαc : ContinuousOn α {x | (x : ℝ≥0∞) ≤ ζ₁})
    (hβc : ContinuousOn β {y | (y : ℝ≥0∞) ≤ ζ₂}) (hαi : InjOn α {x | (x : ℝ≥0∞) ≤ ζ₁})
    (hβi : InjOn β {y | (y : ℝ≥0∞) ≤ ζ₂}) (hαim : ∀ x : ℝ≥0, (x : ℝ≥0∞) ≤ ζ₁ → 0 ≤ (α x).im)
    (hβim : ∀ y : ℝ≥0, (y : ℝ≥0∞) ≤ ζ₂ → 0 ≤ (β y).im)
    (hαno : ∀ x y : ℝ≥0, x < y → (y : ℝ≥0∞) < ζ₁ → ∃ z ∈ Ioo x y, α z ∈ H)
    (hβno : ∀ x y : ℝ≥0, x < y → (y : ℝ≥0∞) < ζ₂ → ∃ z ∈ Ioo x y, β z ∈ H)
    (h0 : (α 0).im = 0) (hβ0 : (β 0).im = 0) (hseed : (β 0).re ≤ (α 0).re)
    {r s a t b v : ℝ≥0} (hra : r < a) (hab : a < b) (hbζ : (b : ℝ≥0∞) ≤ ζ₁) (hsv : s < v) (hvt : v < t)
    (htζ : (t : ℝ≥0∞) ≤ ζ₂) (hp : α a = β t) (hq : α b = β v)
    (hbox : ∀ x ∈ Ioc r b, ∀ y ∈ Ioc s t, α x = β y → (x = a ∧ y = t) ∨ (x = b ∧ y = v))
    (hold1 : ∀ x ∈ Ioc r b, α x ∉ β '' Icc 0 s) (hold2 : ∀ y ∈ Ioc s t, β y ∉ α '' Icc 0 r)
    (hE : ∀ r' s' : ℝ≥0, r < r' → r' < a → s < s' → s' < v → HasOrderedProperCompletions α r' β s')
    (hαcomp : ∀ x, r < x → x < b → ∃ α', IsProperCompletion α x α')
    (hβcomp : ∀ y, s < y → y < t → ∃ β', IsProperCompletion β y β') :
    ∃ r' ∈ dyadSet, ∃ s' ∈ dyadSet, Supp7.IsOrdinaryRetainedPair α ζ₁ r' β ζ₂ s' ∧
      IsFreshLowerRectangle α ζ₁ r' β ζ₂ s' := by
  have haζ : (a : ℝ≥0∞) < ζ₁ := lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hab) hbζ
  have hvζ : (v : ℝ≥0∞) < ζ₂ := lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hvt) htζ
  obtain ⟨r', hr'D, hrr', hr'a, hr'H⟩ := exists_dyad_mem_H hαc hαno hra haζ
  obtain ⟨s', hs'D, hss', hs'v, hs'H⟩ := exists_dyad_mem_H hβc hβno hsv hvζ
  have hle₁ : ∀ x : ℝ≥0, x ≤ b → (x : ℝ≥0∞) ≤ ζ₁ := fun x hx => (ENNReal.coe_le_coe.2 hx).trans hbζ
  have hle₂ : ∀ y : ℝ≥0, y ≤ t → (y : ℝ≥0∞) ≤ ζ₂ := fun y hy => (ENNReal.coe_le_coe.2 hy).trans htζ
  -- the fresh portions after the perturbed cuts avoid the other old prefix
  have hαfresh : ∀ x ∈ Icc r' b, α x ∉ β '' Icc 0 s' := by
    rintro x hx ⟨y, hy, hyx⟩
    by_cases hys : y ≤ s
    · exact hold1 x ⟨hrr'.trans_le hx.1, hx.2⟩ ⟨y, ⟨zero_le, hys⟩, hyx⟩
    · rcases hbox x ⟨hrr'.trans_le hx.1, hx.2⟩ y ⟨not_le.1 hys, hy.2.trans (hs'v.trans hvt).le⟩ hyx.symm with
        h | h
      · exact absurd (h.2 ▸ hy.2) (not_le.2 (hs'v.trans hvt))
      · exact absurd (h.2 ▸ hy.2) (not_le.2 hs'v)
  have hβfresh : ∀ y ∈ Icc s' t, β y ∉ α '' Icc 0 r' := by
    rintro y hy ⟨x, hx, hxy⟩
    by_cases hxr : x ≤ r
    · exact hold2 y ⟨hss'.trans_le hy.1, hy.2⟩ ⟨x, ⟨zero_le, hxr⟩, hxy⟩
    · rcases hbox x ⟨not_le.1 hxr, hx.2.trans (hr'a.trans hab).le⟩ y ⟨hss'.trans_le hy.1, hy.2⟩ hxy with
        h | h
      · exact absurd (h.1 ▸ hx.2) (not_le.2 hr'a)
      · exact absurd (h.1 ▸ hx.2) (not_le.2 (hr'a.trans hab))
  refine ⟨r', hr'D, s', hs'D, ?_, ?_⟩
  · refine isOrdinaryRetainedPair_of_cuts h0 hβ0 hseed (hE r' s' hrr' hr'a hss' hs'v)
      (hαc.mono fun x hx => hle₁ x hx.2) (hβc.mono fun y hy => hle₂ y hy.2)
      (fun x hx hxb => hαcomp x (hrr'.trans hx) hxb) (fun y hy hyt => hβcomp y (hss'.trans hy) hyt)
      (fun x hx => hαim x (hle₁ x hx)) (fun y hy => hβim y (hle₂ y hy)) hr'a hab.le hs'v hvt.le hp hq hr'H
      hs'H
      hαfresh hβfresh (lt_trans (ENNReal.coe_lt_coe.2 hr'a) haζ) (lt_trans (ENNReal.coe_lt_coe.2 hs'v) hvζ)
  · refine ⟨a, t, b, v, hr'a, hab, hbζ, hs'v, hvt, htζ, hp, hq, ?_, ?_, ?_⟩
    · rintro x hrx hxb (⟨x', hx', hxx'⟩ | hxβ)
      · have := hαi (hle₁ x' (hx'.2.trans (hr'a.trans hab).le)) (hle₁ x hxb.le) hxx'
        exact absurd (this ▸ hx'.2) (not_le.2 hrx)
      · exact hαfresh x ⟨hrx.le, hxb.le⟩ hxβ
    · rintro y hsy hyt (hyα | ⟨y', hy', hyy'⟩)
      · exact hβfresh y ⟨hsy.le, hyt.le⟩ hyα
      · have := hβi (hle₂ y' (hy'.2.trans (hs'v.trans hvt).le)) (hle₂ y hyt.le) hyy'
        exact absurd (this ▸ hy'.2) (not_le.2 hsy)
    · intro x y hrx hxb hsy hyt hxy
      rcases hbox x ⟨hrr'.trans_le hrx, hxb.le⟩ y ⟨hss'.trans_le hsy, hyt.le⟩ hxy with h | h
      · exact absurd h.2 hyt.ne
      · exact absurd h.1 hxb.ne

end Box

/-! ### The three configurations -/

section Config

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}

/-- The pathwise hypotheses available for the two flow lines of W5 on an almost-sure event: continuity, injectivity
(Aux. lemma 25), values in `ℍ̄`, no real subarcs, real ordered seeds, and the seed alternative (a common seed, or
neither path visits the other seed: W0a). -/
structure PathFacts (α : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (β : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) : Prop where
  αc : ContinuousOn α {x | (x : ℝ≥0∞) ≤ ζ₁}
  βc : ContinuousOn β {y | (y : ℝ≥0∞) ≤ ζ₂}
  αi : InjOn α {x | (x : ℝ≥0∞) ≤ ζ₁}
  βi : InjOn β {y | (y : ℝ≥0∞) ≤ ζ₂}
  αim : ∀ x : ℝ≥0, (x : ℝ≥0∞) ≤ ζ₁ → 0 ≤ (α x).im
  βim : ∀ y : ℝ≥0, (y : ℝ≥0∞) ≤ ζ₂ → 0 ≤ (β y).im
  αno : ∀ x y : ℝ≥0, x < y → (y : ℝ≥0∞) < ζ₁ → ∃ z ∈ Ioo x y, α z ∈ H
  βno : ∀ x y : ℝ≥0, x < y → (y : ℝ≥0∞) < ζ₂ → ∃ z ∈ Ioo x y, β z ∈ H
  α0 : (α 0).im = 0
  β0 : (β 0).im = 0
  seed : (β 0).re ≤ (α 0).re
  seedv : 0 < ζ₁ → 0 < ζ₂ → α 0 = β 0 ∨
    ((∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ → β t ≠ α 0) ∧ ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ → α s ≠ β 0)

/-- The first path meets the second seed only at time `0` (W0a, or a common seed and injectivity). -/
theorem PathFacts.eq_zero_of_eq_β0 (hF : PathFacts α ζ₁ β ζ₂) (h₁ : 0 < ζ₁) (h₂ : 0 < ζ₂) {x : ℝ≥0}
    (hx : (x : ℝ≥0∞) ≤ ζ₁) (hxe : α x = β 0) : x = 0 := by
  rcases hF.seedv h₁ h₂ with h | h
  · exact hF.αi hx (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ ζ₁ by simp) (hxe.trans h.symm)
  · exact absurd hxe (h.2 x hx)

/-- The second path meets the first seed only at time `0`. -/
theorem PathFacts.eq_zero_of_eq_α0 (hF : PathFacts α ζ₁ β ζ₂) (h₁ : 0 < ζ₁) (h₂ : 0 < ζ₂) {y : ℝ≥0}
    (hy : (y : ℝ≥0∞) ≤ ζ₂) (hye : β y = α 0) : y = 0 := by
  rcases hF.seedv h₁ h₂ with h | h
  · exact hF.βi hy (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ ζ₂ by simp) (hye.trans h)
  · exact absurd hye (h.1 y hy)

theorem completion_left_of_le {A c x : ℝ≥0} (h : HasOrderedProperCompletions α A β c) (hx : x ≤ A) :
    ∃ α', IsProperCompletion α x α' := by
  obtain ⟨α', -, hα', -, -⟩ := Supp9.HasOrderedProperCompletions.mono_left h hx
  exact ⟨α', hα'⟩

theorem completion_right_of_le {A c y : ℝ≥0} (h : HasOrderedProperCompletions α A β c) (hy : y ≤ c) :
    ∃ β', IsProperCompletion β y β' := by
  obtain ⟨-, β', -, hβ', -⟩ := Supp9.HasOrderedProperCompletions.mono_right h hy
  exact ⟨β', hβ'⟩

/-- **The cuts of Lemma W1** (pp. 529–530) at dyadic interior times: the W1 configuration gives an ordinary
retained pair with a fresh lower rectangle. -/
theorem exists_dyad_cuts_of_isW1Configuration (hF : PathFacts α ζ₁ β ζ₂)
    (hW1 : Supp9.IsW1Configuration α ζ₁ β ζ₂) :
    ∃ r ∈ dyadSet, ∃ s ∈ dyadSet, Supp7.IsOrdinaryRetainedPair α ζ₁ r β ζ₂ s ∧
      IsFreshLowerRectangle α ζ₁ r β ζ₂ s := by
  obtain ⟨A, t, a, b₀, v₀, hA, ht, hE, hp, hq₀, ha0, hab₀, hb₀A, hv₀t, -, -, -⟩ := hW1
  have ht0 : 0 < t := lt_of_le_of_lt zero_le hv₀t
  have h₁ : 0 < ζ₁ := lt_of_lt_of_le (ENNReal.coe_pos.2 (ha0.trans (hab₀.trans_le hb₀A))) hA
  have h₂ : 0 < ζ₂ := lt_of_lt_of_le (ENNReal.coe_pos.2 ht0) ht
  have hleA : ∀ x : ℝ≥0, x ≤ A → (x : ℝ≥0∞) ≤ ζ₁ := fun x hx => (ENNReal.coe_le_coe.2 hx).trans hA
  have hlet : ∀ y : ℝ≥0, y ≤ t → (y : ℝ≥0∞) ≤ ζ₂ := fun y hy => (ENNReal.coe_le_coe.2 hy).trans ht
  have hinc := Supp9.earlierContactsIncreasing_of_contactOrder Supp9B.orderedContactOrderStatement hF.α0 hF.β0
    hF.seed hE
  have hβ0' : ∀ x ∈ Icc 0 A, α x = β 0 → x = 0 := fun x hx hxe =>
    hF.eq_zero_of_eq_β0 h₁ h₂ (hleA x hx.2) hxe
  obtain ⟨r, s, b, v, -, -, hra, hab, hbA, hsv, hvt, hq, -, hbox, -, h1, h2, -, -⟩ :=
    Supp9.w1_cuts (Supp9.HasOrderedProperCompletions.continuousOn_left (hE 0 ht0))
      (hF.βc.mono fun y hy => hlet y hy.2) (Supp9.HasOrderedProperCompletions.injOn_left (hE 0 ht0))
      (hF.βi.mono fun y hy => hlet y hy.2) hinc ha0 (hab₀.trans_le hb₀A).le hp hab₀ hb₀A hv₀t hq₀ hβ0'
      dense_univ dense_univ
  refine exists_dyad_cuts_of_box hF.αc hF.βc hF.αi hF.βi hF.αim hF.βim hF.αno hF.βno hF.α0 hF.β0 hF.seed
    hra hab ((ENNReal.coe_le_coe.2 hbA).trans hA) hsv hvt ht hp hq
    (fun x hx y hy hxy => hbox x (Ioc_subset_Icc_self hx) y (Ioc_subset_Icc_self hy) hxy)
    (fun x hx hxβ => Set.disjoint_left.1 h1 ⟨x, hx, rfl⟩ hxβ)
    (fun y hy hyα => Set.disjoint_left.1 h2 ⟨y, hy, rfl⟩ hyα)
    (fun r' s' _ hr'a _ hs'v => Supp9.HasOrderedProperCompletions.mono (hE s' (hs'v.trans hvt))
      (hr'a.le.trans (hab.le.trans hbA)) le_rfl)
    (fun x _ hxb => completion_left_of_le (hE 0 ht0) (hxb.le.trans hbA))
    (fun y _ hyt => completion_right_of_le (hE y hyt) le_rfl)

/-- The earlier contacts in the exchanged orientation are increasing (contact order of the ordered completions). -/
theorem earlierContactsIncreasing_swap (hF : PathFacts α ζ₁ β ζ₂) {T B : ℝ≥0} (hB : (B : ℝ≥0∞) ≤ ζ₂)
    (hE : ∀ u < T, HasOrderedProperCompletions α u β B) : Supp9.EarlierContactsIncreasing β B α T := by
  intro p hp q hq hpT hqT hpq
  rcases lt_trichotomy p.2 q.2 with h | h | h
  · exact h
  · exfalso
    have hle : ∀ y : ℝ≥0, y ≤ B → (y : ℝ≥0∞) ≤ ζ₂ := fun y hy => (ENNReal.coe_le_coe.2 hy).trans hB
    have := hF.βi (hle _ hp.1.2) (hle _ hq.1.2) (by rw [hp.2.2, h, ← hq.2.2])
    exact hpq.ne this
  · exfalso
    obtain ⟨α', β', hα', hβ', hside⟩ := hE (max p.2 q.2) (max_lt hpT hqT)
    have e0α : α' 0 = α 0 := hα'.2.2.2.2 0 zero_le
    have e0β : β' 0 = β 0 := hβ'.2.2.2.2 0 zero_le
    have := Supp9B.orderedContactOrderStatement α' β' (Supp9.isProperCompletion_self_zero hα')
      (Supp9.isProperCompletion_self_zero hβ') (by rw [e0α]; exact hF.α0) (by rw [e0β]; exact hF.β0)
      (by rw [e0α, e0β]; exact hF.seed) hside q.2 p.2 q.1 p.1
      (by rw [hα'.2.2.2.2 _ (le_max_right _ _), hβ'.2.2.2.2 _ hq.1.2, hq.2.2])
      (by rw [hα'.2.2.2.2 _ (le_max_left _ _), hβ'.2.2.2.2 _ hp.1.2, hp.2.2]) h
    exact absurd hpq (not_lt.2 this.le)

/-- **The cuts of Lemma W1 with the paths exchanged** (p. 530: "The same conclusion holds with the paths and
left/right orientations exchanged") at dyadic interior times. -/
theorem exists_dyad_cuts_of_isW1ConfigurationSwap (hF : PathFacts α ζ₁ β ζ₂)
    (hW1 : Supp9.IsW1ConfigurationSwap α ζ₁ β ζ₂) :
    ∃ r ∈ dyadSet, ∃ s ∈ dyadSet, Supp7.IsOrdinaryRetainedPair α ζ₁ r β ζ₂ s ∧
      IsFreshLowerRectangle α ζ₁ r β ζ₂ s := by
  obtain ⟨T, B, b, v, a, hT, hB, hE, hp, hq₀, hb0, hbv, hvB, haT, -, -, -⟩ := hW1
  have hT0 : 0 < T := lt_of_le_of_lt zero_le haT
  have h₁ : 0 < ζ₁ := lt_of_lt_of_le (ENNReal.coe_pos.2 hT0) hT
  have h₂ : 0 < ζ₂ := lt_of_lt_of_le (ENNReal.coe_pos.2 (hb0.trans (hbv.trans_le hvB))) hB
  have hleT : ∀ x : ℝ≥0, x ≤ T → (x : ℝ≥0∞) ≤ ζ₁ := fun x hx => (ENNReal.coe_le_coe.2 hx).trans hT
  have hleB : ∀ y : ℝ≥0, y ≤ B → (y : ℝ≥0∞) ≤ ζ₂ := fun y hy => (ENNReal.coe_le_coe.2 hy).trans hB
  have hinc := earlierContactsIncreasing_swap hF hB hE
  have hα0' : ∀ y ∈ Icc 0 B, β y = α 0 → y = 0 := fun y hy hye =>
    hF.eq_zero_of_eq_α0 h₁ h₂ (hleB y hy.2) hye
  obtain ⟨r, s, b', v', -, -, hrb, hbb', hb'B, hsv', hv'T, hq, -, hbox, -, h1, h2, -, -⟩ :=
    Supp9.w1_cuts (Supp9.HasOrderedProperCompletions.continuousOn_right (hE 0 hT0))
      (hF.αc.mono fun x hx => hleT x hx.2) (Supp9.HasOrderedProperCompletions.injOn_right (hE 0 hT0))
      (hF.αi.mono fun x hx => hleT x hx.2) hinc hb0 (hbv.le.trans hvB) hp.symm hbv hvB haT hq₀.symm hα0'
      dense_univ dense_univ
  refine exists_dyad_cuts_of_box hF.αc hF.βc hF.αi hF.βi hF.αim hF.βim hF.αno hF.βno hF.α0 hF.β0 hF.seed
    hsv' hv'T hT hrb hbb' ((ENNReal.coe_le_coe.2 hb'B).trans hB) hq.symm hp
    (fun x hx y hy hxy => (hbox y (Ioc_subset_Icc_self hy) x (Ioc_subset_Icc_self hx) hxy.symm).elim
      (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩))
    (fun x hx hxβ => Set.disjoint_left.1 h2 ⟨x, hx, rfl⟩ hxβ)
    (fun y hy hyα => Set.disjoint_left.1 h1 ⟨y, hy, rfl⟩ hyα)
    (fun r' s' _ hr'v _ hs'b => Supp9.HasOrderedProperCompletions.mono (hE r' (hr'v.trans hv'T)) le_rfl
      (hs'b.le.trans (hbv.le.trans hvB)))
    (fun x _ hxT => completion_left_of_le (hE x hxT) le_rfl)
    (fun y _ hyb => completion_right_of_le (hE 0 hT0) (hyb.le.trans hb'B))

/-- **The cuts of Lemma W2a's corner case** (p. 533: "Compactness therefore gives a last earlier common point, if
there is one, with a contact-free matched gap extending beyond `a, b`. Choose rational cuts inside this gap below
`a, b`") at dyadic interior times. -/
theorem exists_dyad_cuts_of_isW2aCornerConfiguration (hF : PathFacts α ζ₁ β ζ₂)
    (hC : Supp9.IsW2aCornerConfiguration α ζ₁ β ζ₂) :
    ∃ r ∈ dyadSet, ∃ s ∈ dyadSet, Supp7.IsOrdinaryRetainedPair α ζ₁ r β ζ₂ s ∧
      IsFreshLowerRectangle α ζ₁ r β ζ₂ s := by
  obtain ⟨A, B, a, b, hA, hB, hE, haA, hbB, hp, hq, hne, hearly⟩ := hC
  have hA0 : 0 < A := lt_of_le_of_lt zero_le haA
  have hB0 : 0 < B := lt_of_le_of_lt zero_le hbB
  have h₁ : 0 < ζ₁ := lt_of_lt_of_le (ENNReal.coe_pos.2 hA0) hA
  have h₂ : 0 < ζ₂ := lt_of_lt_of_le (ENNReal.coe_pos.2 hB0) hB
  have hleA : ∀ x : ℝ≥0, x ≤ A → (x : ℝ≥0∞) ≤ ζ₁ := fun x hx => (ENNReal.coe_le_coe.2 hx).trans hA
  have hleB : ∀ y : ℝ≥0, y ≤ B → (y : ℝ≥0∞) ≤ ζ₂ := fun y hy => (ENNReal.coe_le_coe.2 hy).trans hB
  -- the contacts on the two new edges are only the two new contacts
  have hedgeA : ∀ y : ℝ≥0, y ≤ B → α A = β y → y = b := fun y hy hye =>
    hF.βi (hleB y hy) (hleB b hbB.le) (hye.symm.trans hq)
  have hedgeB : ∀ x : ℝ≥0, x ≤ A → α x = β B → x = a := fun x hx hxe =>
    hF.αi (hleA x hx) (hleA a haA.le) (hxe.trans hp.symm)
  -- a contact in the closed rectangle is an earlier contact or one of the two new ones
  have hcases : ∀ x y : ℝ≥0, x ≤ A → y ≤ B → α x = β y →
      (x < a ∧ y < b) ∨ (x = a ∧ y = B) ∨ (x = A ∧ y = b) := by
    intro x y hx hy hxy
    rcases hx.lt_or_eq with hx' | hx'
    · rcases hy.lt_or_eq with hy' | hy'
      · exact Or.inl (hearly x y hx' hy' hxy)
      · exact Or.inr (Or.inl ⟨hedgeB x hx (hy' ▸ hxy), hy'⟩)
    · exact Or.inr (Or.inr ⟨hx', hedgeA y hy (hx' ▸ hxy)⟩)
  have hαcA : ContinuousOn α (Icc 0 A) := hF.αc.mono fun x hx => hleA x hx.2
  have hβcB : ContinuousOn β (Icc 0 B) := hF.βc.mono fun y hy => hleB y hy.2
  -- the lower ends of the matched gap: every earlier contact is at or below `(r₀, s₀)`
  obtain ⟨r₀, s₀, hr₀a, hs₀b, hlow⟩ : ∃ r₀ s₀ : ℝ≥0, r₀ < a ∧ s₀ < b ∧
      ∀ x y : ℝ≥0, x < a → y < b → α x = β y → x ≤ r₀ ∧ y ≤ s₀ := by
    set C := Sec7.contactSet α a β b with hCdef
    rcases C.eq_empty_or_nonempty with hCe | hCne
    · have hnoc : ∀ x y : ℝ≥0, x < a → y < b → α x ≠ β y := fun x y hx hy hxy => by
        have : (x, y) ∈ C := ⟨⟨zero_le, hx.le⟩, ⟨zero_le, hy.le⟩, hxy⟩
        rw [hCe] at this
        exact this
      have ha0 : 0 < a := by
        refine pos_iff_ne_zero.2 fun ha => ?_
        have hb' := hF.eq_zero_of_eq_α0 h₁ h₂ (hleB B le_rfl) (by rw [← hp, ha])
        exact absurd (hb' ▸ hbB) (not_lt.2 zero_le)
      have hb0 : 0 < b := by
        refine pos_iff_ne_zero.2 fun hb => ?_
        have ha' := hF.eq_zero_of_eq_β0 h₁ h₂ (hleA A le_rfl) (by rw [hq, hb])
        exact absurd (ha' ▸ haA) (not_lt.2 zero_le)
      exact ⟨0, 0, ha0, hb0, fun x y hx hy hxy => absurd hxy (hnoc x y hx hy)⟩
    · have hCc : IsCompact C := Sec7.isCompact_contactSet (hαcA.mono (Icc_subset_Icc_right haA.le))
        (hβcB.mono (Icc_subset_Icc_right hbB.le))
      obtain ⟨⟨r₀, y₀⟩, ⟨hr₀, hy₀, hry⟩, hmax₁⟩ := hCc.exists_isMaxOn hCne continuous_fst.continuousOn
      obtain ⟨⟨x₀, s₀⟩, ⟨hx₀, hs₀, hxs⟩, hmax₂⟩ := hCc.exists_isMaxOn hCne continuous_snd.continuousOn
      change r₀ ∈ Icc 0 a at hr₀
      change y₀ ∈ Icc 0 b at hy₀
      change α r₀ = β y₀ at hry
      change x₀ ∈ Icc 0 a at hx₀
      change s₀ ∈ Icc 0 b at hs₀
      change α x₀ = β s₀ at hxs
      refine ⟨r₀, s₀, ?_, ?_, fun x y hx hy hxy => ?_⟩
      · refine lt_of_le_of_ne hr₀.2 fun he => ?_
        have : y₀ = B := hF.βi (hleB y₀ (hy₀.2.trans hbB.le)) (hleB B le_rfl) (by rw [← hry, he, hp])
        exact absurd (this ▸ hy₀.2) (not_le.2 hbB)
      · refine lt_of_le_of_ne hs₀.2 fun he => ?_
        have : x₀ = A := hF.αi (hleA x₀ (hx₀.2.trans haA.le)) (hleA A le_rfl) (by rw [hxs, he, hq])
        exact absurd (this ▸ hx₀.2) (not_le.2 haA)
      · exact ⟨hmax₁ (show (x, y) ∈ C from ⟨⟨zero_le, hx.le⟩, ⟨zero_le, hy.le⟩, hxy⟩),
          hmax₂ (show (x, y) ∈ C from ⟨⟨zero_le, hx.le⟩, ⟨zero_le, hy.le⟩, hxy⟩)⟩
  have hcases : ∀ x y : ℝ≥0, x ≤ A → y ≤ B → α x = β y →
      (x < a ∧ y < b) ∨ (x = a ∧ y = B) ∨ (x = A ∧ y = b) := by
    intro x y hx hy hxy
    rcases hx.lt_or_eq with hx' | hx'
    · rcases hy.lt_or_eq with hy' | hy'
      · exact Or.inl (hearly x y hx' hy' hxy)
      · exact Or.inr (Or.inl ⟨hedgeB x hx (hy' ▸ hxy), hy'⟩)
    · exact Or.inr (Or.inr ⟨hx', hedgeA y hy (hx' ▸ hxy)⟩)
  refine exists_dyad_cuts_of_box hF.αc hF.βc hF.αi hF.βi hF.αim hF.βim hF.αno hF.βno hF.α0 hF.β0 hF.seed
    hr₀a haA hA hs₀b hbB hB hp hq ?_ ?_ ?_
    (fun r' s' _ hr'a _ hs'b => hE r' s' (hr'a.trans haA) (hs'b.trans hbB))
    (fun x _ hxA => completion_left_of_le (hE x 0 hxA hB0) le_rfl)
    (fun y _ hyB => completion_right_of_le (hE 0 y hA0 hyB) le_rfl)
  · intro x hx y hy hxy
    rcases hcases x y hx.2 hy.2 hxy with h | h | h
    · exact absurd (hlow x y h.1 h.2 hxy).1 (not_le.2 hx.1)
    · exact Or.inl h
    · exact Or.inr h
  · rintro x hx ⟨y, hy, hyx⟩
    rcases hcases x y hx.2 (hy.2.trans (hs₀b.trans hbB).le) hyx.symm with h | h | h
    · exact absurd (hlow x y h.1 h.2 hyx.symm).1 (not_le.2 hx.1)
    · exact absurd (h.2 ▸ hy.2) (not_le.2 (hs₀b.trans hbB))
    · exact absurd (h.2 ▸ hy.2) (not_le.2 hs₀b)
  · rintro y hy ⟨x, hx, hxy⟩
    rcases hcases x y (hx.2.trans (hr₀a.trans haA).le) hy.2 hxy with h | h | h
    · exact absurd (hlow x y h.1 h.2 hxy).2 (not_le.2 hy.1)
    · exact absurd (h.1 ▸ hx.2) (not_le.2 hr₀a)
    · exact absurd (h.1 ▸ hx.2) (not_le.2 (hr₀a.trans haA))

end Config

end Supp9D

end InteractingSLE
