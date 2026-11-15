/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop411QSide

/-!
# Lemma 4.7 in Lemma 4.5's chart `Q`: containment and reverse chronological order from first contacts

Packet PROVE-SEC5-O. Specification §4.2, Lemma 4.7 and its proof (`source/spec/p097-144.md#lem-4.7`, pp. 117–119):

> "Then `η′` almost surely first hits `∂_L𝒮 ∪ η([0, τ])` at `η(τ)`. In particular, `η′` contains `η` and hits the
> points of `η` in reverse chronological order: if `s < t` then `η′` hits `η(t)` before `η(s)`." … "Apply the
> strict-before-contact assertion to a countable dense set of stopped flow-line times. Their images lie in the completed
> counterflow range; its closedness gives containment" … "Given arbitrary `s < t`, choose a rational `q ∈ (s, t)` and
> rational `q_n ↓ …` … A subsequence and continuity show …"

In the chart `Q` the flow line `η` is a proper arc of `ℍ` from `0` to `∞`, and the counterflow line is `η′ = R ∘ β`,
`R(z) = −1/z`, for a curve `β` of the chart `R` with `β(0) = 0` (so `η′` starts at `∞`). The first-contact property at
a flow time `q` (`IsFirstHitQ η β q`) says: at some counterflow time `u > 0`, `η′(u) = η(q)`, and before `u` the
counterflow avoids `η((0, q])`.

* `exists_eq_of_isFirstHitQ` (the "in particular" of Lemma 4.7, for the order used by Proposition 4.9's no-wrap step):
  if the first-contact property holds at every positive rational time, and the counterflow visits `η(t₁)` at time
  `v₁`, then it visits every later point `η(t)`, `t > t₁`, at some time in `(0, v₁]`.
* `mem_negInv_fwdHull_of_isFirstHitQ`: hence `η` stays in the counterflow hull `R(K_s)` after a contact with
  `η′((0, s])` (the hypothesis `hpost` of `negInv_notMem_leftSideOf_of_exit`).
* `mem_closure_range_of_isFirstHitQ`: containment, `η(q)` lies in the closure of the counterflow at positive rational
  times.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Sec5.Prop411Q

open WangWu hiding ratPt exists_ratPt_dist_lt

variable {η β : ℝ → ℂ}

/-- **The first-contact property of Lemma 4.7 at the flow time `q`** in the chart `Q`: the counterflow `η′ = R ∘ β`
hits `η(q)` at some time `u > 0` and avoids `η((0, q])` before `u`. -/
def IsFirstHitQ (η β : ℝ → ℂ) (q : ℝ) : Prop :=
  ∃ u : ℝ, 0 < u ∧ negInv (β u) = η q ∧ ∀ v ∈ Ioo 0 u, negInv (β v) ∉ η '' Ioc 0 q

theorem negInv_eq_iff {a b : ℂ} : negInv a = b ↔ a = negInv b := by
  constructor
  · rintro rfl; simp
  · rintro rfl; simp

/-- **Reverse chronological order** (Lemma 4.7, "in particular"). If the first-contact property holds at every
positive rational flow time and the counterflow visits `η(t₁)`, `t₁ > 0`, at time `v₁ > 0`, then it visits every later
point `η(t)` at some time in `(0, v₁]`. -/
theorem exists_eq_of_isFirstHitQ (hη : IsProperArc η) (hβc : ContinuousOn β (Ici 0)) (hβ0 : β 0 = 0)
    (hhit : ∀ q : ℚ, 0 < q → IsFirstHitQ η β q) {t₁ v₁ t : ℝ} (ht₁ : 0 < t₁) (hv₁ : 0 < v₁)
    (he : η t₁ = negInv (β v₁)) (ht : t₁ < t) : ∃ v ∈ Ioc 0 v₁, η t = negInv (β v) := by
  have ht0 : 0 < t := ht₁.trans ht
  -- rational times `q n ↓ t`
  have hq : ∀ n : ℕ, ∃ q : ℚ, t < q ∧ (q : ℝ) < t + 1 / ((n : ℝ) + 1) := fun n =>
    exists_rat_btwn (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                        linarith)
  choose q hq₁ hq₂ using hq
  have hqt : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 t) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => (hq₁ n).le)
      (fun n => (hq₂ n).le)
    have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using tendsto_const_nhds.add this
  have hqpos : ∀ n, 0 < (q n : ℚ) := fun n => by exact_mod_cast ht0.trans (hq₁ n)
  choose u hu0 hue hubefore using fun n => hhit (q n) (hqpos n)
  -- every first visit happens no later than `v₁`
  have huv : ∀ n, u n ≤ v₁ := fun n => by
    by_contra h
    push Not at h
    exact hubefore n v₁ ⟨hv₁, h⟩ ⟨t₁, ⟨ht₁, (ht.trans (hq₁ n)).le⟩, he⟩
  -- a convergent subsequence of the visiting times
  obtain ⟨u', hu'mem, φ, hφ, hlim⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := v₁)).tendsto_subseq
    (x := u) fun n => ⟨(hu0 n).le, huv n⟩
  have hηt : η t ∈ H := hη.mem_H t ht0
  have hηc : ContinuousAt η t := hη.cont.continuousAt (Ici_mem_nhds ht0)
  -- `β(u n) = R(η(q n)) → R(η(t))`
  have h1 : Tendsto (fun n => β (u (φ n))) atTop (𝓝 (negInv (η t))) := by
    have h2 : Tendsto (fun n => negInv (η (q (φ n)))) atTop (𝓝 (negInv (η t))) :=
      (continuousAt_negInv (ne_zero_of_mem_H hηt)).tendsto.comp
        (hηc.tendsto.comp (hqt.comp hφ.tendsto_atTop))
    refine h2.congr fun n => ?_
    exact (negInv_eq_iff.1 (hue (φ n))).symm
  have h3 : Tendsto (fun n => β (u (φ n))) atTop (𝓝 (β u')) := by
    have hc : ContinuousWithinAt β (Ici 0) u' := hβc u' hu'mem.1
    exact hc.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => (hu0 (φ n)).le⟩)
  have hβu : β u' = negInv (η t) := tendsto_nhds_unique h3 h1
  have hu'pos : 0 < u' := by
    rcases eq_or_lt_of_le hu'mem.1 with h | h
    · exfalso
      rw [← h, hβ0] at hβu
      exact ne_zero_of_mem_H (negInv_mem_H hηt) hβu.symm
    · exact h
  exact ⟨u', ⟨hu'pos, hu'mem.2⟩, by rw [hβu]; simp⟩

/-- **After a contact with the counterflow prefix the flow line stays in the counterflow hull** (Proposition 4.9's
proof: "`η′` absorbs the points of `η` in reverse chronological order by Lemma 4.7"). If the counterflow is a Loewner
trace of `w` and visits `η(t₀)` at a time in `(0, s]`, then `η(t) ∈ R(K_s)` for every `t ≥ t₀`. -/
theorem mem_negInv_fwdHull_of_isFirstHitQ {w : ℝ → ℝ} {s t₀ v₀ : ℝ} (hη : IsProperArc η)
    (hβ : IsLoewnerTrace w β) (hhit : ∀ q : ℚ, 0 < q → IsFirstHitQ η β q) (hs : 0 ≤ s) (ht₀ : 0 < t₀)
    (hv₀ : v₀ ∈ Ioc 0 s) (he : η t₀ = negInv (β v₀)) {t : ℝ} (ht : t₀ ≤ t) :
    η t ∈ negInv '' fwdHull w s := by
  have hmem : ∀ v ∈ Icc 0 s, ∀ t', 0 < t' → η t' = negInv (β v) → η t' ∈ negInv '' fwdHull w s := by
    intro v hv t' ht' e
    have hH : β v ∈ H := by rw [negInv_eq_iff.1 e.symm]; exact negInv_mem_H (hη.mem_H t' ht')
    refine ⟨β v, ?_, e.symm⟩
    rw [hβ.2.2 s hs]
    exact ⟨hH, Or.inl (subset_closure ⟨v, hv, rfl⟩)⟩
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h]; exact hmem v₀ ⟨hv₀.1.le, hv₀.2⟩ t₀ ht₀ he
  · obtain ⟨v, hv, e⟩ := exists_eq_of_isFirstHitQ hη hβ.2.1 hβ.1 hhit ht₀ hv₀.1 he h
    exact hmem v ⟨hv.1.le, hv.2.trans hv₀.2⟩ t (ht₀.trans h) e

/-- **Containment** (Lemma 4.7: "Their images lie in the completed counterflow range"). If the counterflow visits a
point `p = R(β(u))` at a time `u > 0` with `β(u) ≠ 0`, then `p` is in the closure of any `f : ℚ → ℂ` that agrees with
the counterflow at positive rational times. -/
theorem mem_closure_range_of_pos {u : ℝ} (hβc : ContinuousOn β (Ici 0)) (hu : 0 < u) (hβu : β u ≠ 0)
    {f : ℚ → ℂ} (hf : ∀ r : ℚ, 0 < r → f r = negInv (β r)) : negInv (β u) ∈ closure (range f) := by
  have hr : ∀ n : ℕ, ∃ r : ℚ, u < r ∧ (r : ℝ) < u + 1 / ((n : ℝ) + 1) := fun n =>
    exists_rat_btwn (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                        linarith)
  choose r hr₁ hr₂ using hr
  have hrt : Tendsto (fun n => (r n : ℝ)) atTop (𝓝 u) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => (hr₁ n).le)
      (fun n => (hr₂ n).le)
    have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using tendsto_const_nhds.add this
  have hβat : ContinuousAt β u := hβc.continuousAt (Ici_mem_nhds hu)
  have hlim : Tendsto (fun n => f (r n)) atTop (𝓝 (negInv (β u))) := by
    have h := (continuousAt_negInv hβu).tendsto.comp (hβat.tendsto.comp hrt)
    refine h.congr fun n => ?_
    simp only [Function.comp_apply]
    exact (hf (r n) (by exact_mod_cast hu.trans (hr₁ n))).symm
  exact mem_closure_of_tendsto hlim (Eventually.of_forall fun n => ⟨r n, rfl⟩)

/-- **Containment at a flow time with the first-contact property**: `η(q)` lies in the closure of the counterflow at
positive rational times. -/
theorem mem_closure_range_of_isFirstHitQ (hη : IsProperArc η) (hβc : ContinuousOn β (Ici 0)) {q : ℝ}
    (hq : 0 < q) (hhit : IsFirstHitQ η β q) {f : ℚ → ℂ} (hf : ∀ r : ℚ, 0 < r → f r = negInv (β r)) :
    η q ∈ closure (range f) := by
  obtain ⟨u, hu, he, -⟩ := hhit
  have hβu : β u ≠ 0 := fun h => by
    rw [h] at he
    exact ne_zero_of_mem_H (hη.mem_H q hq) (by rw [← he]; simp [negInv])
  rw [← he]
  exact mem_closure_range_of_pos hβc hu hβu hf

end InteractingSLE.Sec5.Prop411Q
