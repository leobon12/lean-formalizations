/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ChartMeas
import InteractingSLE.Spec.Supplement.G7Carrier

/-!
# Lemma G7: the active chart at the second tip of a retained pair (deterministic)

Packet PROVE-G7. Source: Lemma G7 (`source/spec/p481-528.md` L403–L422, pp. 497–498): "Retain a marked union `A`
of two finite original flow histories and its canonical conditional field in the joint unbounded component `D`.
Assume its inherited hydrodynamic chart `φ : D → ℍ` […] Suppose one current tip `p` is an interior physical point, is
disjoint from the other retained prefix, and is active."

At own cutoffs `(u, r)` with `A = η₁([0, u]) ∪ η₂([0, r])` and `p = η₂(r)`, the hydrodynamic chart is
`φ = g − x₀`, `g` the mapping-out function of `fill A` and `x₀ = lim_{z → p, z ∈ D} g(z)`. This file obtains it, with
its inverse and all of CPL3's chart properties, **from the first-contact chart theorem**
(`Restart.exists_isFirstContactChart_mapOut`) applied to a *fake first contact*: the path

  `retPath η₁ u η₂`: `η₁` forward on `[0, u]`, back to its seed on `[u, 2u]`, the real segment from the first seed to
  the second on `[2u, 2u + 1]`, then `η₂` forward,

which ends at the second tip at time `2u + 1 + r`, paired with `η₂` itself stopped at `r`. Their union is `A` plus a
real segment, which changes neither `ℍ \ A`, nor the filling, nor the regular points, so the first-contact chart of
the fake pair is the hydrodynamic chart of the retained pair at `p` (`IsRetChart`).

## Main results

* `retPath`, `continuousOn_retPath`, `retPath_end`, `prefixSet_retPath_union_real`;
* `activeDomain_eq_of_union_real`, `fillH_eq_of_union_real` (adding real points changes nothing);
* **`exists_retChart`**: the hydrodynamic chart at the second tip exists (`IsRetChart`), with forward limit `x₀`;
* the API of `IsRetChart`: `isActiveChart`, `bijOn`, `fwd_inv`, `inv_notMem`, `continuousOn_inv`, `inv_zero`,
  `exists_tendsto_of_regular`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Supp7

open Restart

/-! ### Real points change nothing -/

/-- The real line. -/
def realLine : Set ℂ := {z : ℂ | z.im = 0}

theorem isClosed_realLine : IsClosed realLine :=
  isClosed_eq Complex.continuous_im continuous_const

theorem notMem_realLine_of_mem_H {z : ℂ} (hz : z ∈ H) : z ∉ realLine := fun h =>
  (ne_of_gt (show (0 : ℝ) < z.im from hz)) h

theorem H_diff_eq_of_union_real {K K' : Set ℂ} (h : K ∪ realLine = K' ∪ realLine) : H \ K = H \ K' := by
  ext z
  constructor
  · rintro ⟨hzH, hzK⟩
    refine ⟨hzH, fun hzK' => ?_⟩
    have : z ∈ K ∪ realLine := h ▸ Or.inl hzK'
    exact this.elim hzK (notMem_realLine_of_mem_H hzH)
  · rintro ⟨hzH, hzK'⟩
    refine ⟨hzH, fun hzK => ?_⟩
    have : z ∈ K' ∪ realLine := h ▸ Or.inl hzK
    exact this.elim hzK' (notMem_realLine_of_mem_H hzH)

theorem fillH_eq_of_union_real {K K' : Set ℂ} (h : K ∪ realLine = K' ∪ realLine) : fillH K = fillH K' := by
  have hc : closure K ∪ realLine = closure K' ∪ realLine := by
    have h1 := congrArg closure h
    rwa [closure_union, closure_union, isClosed_realLine.closure_eq] at h1
  have hd := H_diff_eq_of_union_real hc
  ext z
  simp only [fillH, mem_ofPred_eq]
  constructor
  · rintro ⟨hzH, h' | h'⟩
    · refine ⟨hzH, Or.inl ?_⟩
      have : z ∈ closure K' ∪ realLine := hc ▸ Or.inl h'
      exact this.resolve_right (notMem_realLine_of_mem_H hzH)
    · exact ⟨hzH, Or.inr (hd ▸ h')⟩
  · rintro ⟨hzH, h' | h'⟩
    · refine ⟨hzH, Or.inl ?_⟩
      have : z ∈ closure K ∪ realLine := hc ▸ Or.inl h'
      exact this.resolve_right (notMem_realLine_of_mem_H hzH)
    · exact ⟨hzH, Or.inr (hd ▸ h')⟩

theorem activeDomain_eq_of_union_real {α β α' β' : ℝ≥0 → ℂ} {a b a' b' : ℝ≥0}
    (h : prefixSet α a β b ∪ realLine = prefixSet α' a' β' b' ∪ realLine) :
    activeDomain α a β b = activeDomain α' a' β' b' := by
  unfold activeDomain
  have := H_diff_eq_of_union_real h
  unfold prefixSet at this
  rw [this]

theorem isChartRegularPoint_iff_of_union_real {α β α' β' : ℝ≥0 → ℂ} {a b a' b' : ℝ≥0}
    (h : prefixSet α a β b ∪ realLine = prefixSet α' a' β' b' ∪ realLine) (z : ℂ) :
    IsChartRegularPoint α a β b z ↔ IsChartRegularPoint α' a' β' b' z := by
  unfold IsChartRegularPoint
  rw [activeDomain_eq_of_union_real h]
  have he : ({w : ℂ | w.im = 0} ∪ prefixSet α a β b) = ({w : ℂ | w.im = 0} ∪ prefixSet α' a' β' b') := by
    have h' : realLine ∪ prefixSet α a β b = realLine ∪ prefixSet α' a' β' b' := by
      rw [union_comm, h, union_comm]
    exact h'
  rw [he]

/-! ### The concatenated path -/

/-- **The fake first path**: `η₁` forward on `[0, u]`, back to `η₁(0)` on `[u, 2u]`, the real segment from `Re η₁(0)`
to `Re η₂(0)` on `[2u, 2u + 1]`, then `η₂(· − (2u + 1))`. -/
def retPath (η₁ : ℝ≥0 → ℂ) (u : ℝ≥0) (η₂ : ℝ≥0 → ℂ) (s : ℝ≥0) : ℂ :=
  if s ≤ u then η₁ s
  else if s ≤ 2 * u then η₁ (2 * u - s)
  else if s ≤ 2 * u + 1 then (((η₁ 0).re + ((s : ℝ) - 2 * u) * ((η₂ 0).re - (η₁ 0).re) : ℝ) : ℂ)
  else η₂ (s - (2 * u + 1))

/-- The length of the fake first path. -/
def retLen (u r : ℝ≥0) : ℝ≥0 := 2 * u + 1 + r

variable {η₁ η₂ : ℝ≥0 → ℂ} {u r : ℝ≥0}

theorem eq_ofReal_re_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : ((z.re : ℝ) : ℂ) = z :=
  Complex.ext (by simp) (by simp [hz])

theorem two_mul_sub_self (u : ℝ≥0) : 2 * u - u = u := by
  rw [two_mul, add_tsub_cancel_right]

theorem continuousOn_Icc_union {f : ℝ≥0 → ℂ} {a b c : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : ContinuousOn f (Icc a b)) (h2 : ContinuousOn f (Icc b c)) : ContinuousOn f (Icc a c) := by
  rw [← Icc_union_Icc_eq_Icc hab hbc]
  exact h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc

theorem retPath_apply_le {s : ℝ≥0} (hs : s ≤ u) : retPath η₁ u η₂ s = η₁ s := by
  simp [retPath, hs]

theorem retPath_apply_back {s : ℝ≥0} (hs : u ≤ s) (hs' : s ≤ 2 * u) :
    retPath η₁ u η₂ s = η₁ (2 * u - s) := by
  unfold retPath
  split_ifs with h
  · rw [le_antisymm h hs, two_mul_sub_self]
  · rfl

theorem retPath_apply_seg (h0₁ : (η₁ 0).im = 0) {s : ℝ≥0} (hs : 2 * u ≤ s) (hs' : s ≤ 2 * u + 1) :
    retPath η₁ u η₂ s = (((η₁ 0).re + ((s : ℝ) - 2 * u) * ((η₂ 0).re - (η₁ 0).re) : ℝ) : ℂ) := by
  have hsR : (2 * u : ℝ) ≤ s := by exact_mod_cast hs
  unfold retPath
  split_ifs with h h'
  · have hR : (s : ℝ) ≤ u := by exact_mod_cast h
    have hu : (u : ℝ) = 0 := le_antisymm (by linarith [u.coe_nonneg]) u.coe_nonneg
    have hs0 : (s : ℝ) = 0 := le_antisymm (by linarith) s.coe_nonneg
    have hs0' : s = 0 := by exact_mod_cast hs0
    rw [hs0']
    simp [hu, eq_ofReal_re_of_im_eq_zero h0₁]
  · have hs2 : s = 2 * u := le_antisymm h' hs
    rw [hs2, tsub_self]
    have : ((2 * u : ℝ≥0) : ℝ) - 2 * u = 0 := by push_cast; ring
    rw [this, zero_mul, add_zero, eq_ofReal_re_of_im_eq_zero h0₁]
  · rfl

theorem retPath_apply_fwd (h0₂ : (η₂ 0).im = 0) {s : ℝ≥0} (hs : 2 * u + 1 ≤ s) :
    retPath η₁ u η₂ s = η₂ (s - (2 * u + 1)) := by
  have hsR : (2 * u + 1 : ℝ) ≤ s := by exact_mod_cast hs
  unfold retPath
  have h1 : ¬ s ≤ u := fun h => by
    have hR : (s : ℝ) ≤ u := by exact_mod_cast h
    linarith [u.coe_nonneg]
  have h2 : ¬ s ≤ 2 * u := fun h => by
    have hR : (s : ℝ) ≤ 2 * u := by exact_mod_cast h
    linarith
  simp only [h1, h2, ↓reduceIte]
  split_ifs with h3
  · have hs3 : s = 2 * u + 1 := le_antisymm h3 hs
    rw [hs3, tsub_self]
    have : ((2 * u + 1 : ℝ≥0) : ℝ) - 2 * u = 1 := by push_cast; ring
    rw [this, one_mul, add_sub_cancel, eq_ofReal_re_of_im_eq_zero h0₂]
  · rfl

theorem continuousOn_retPath (hc₁ : ContinuousOn η₁ (Icc 0 u)) (hc₂ : ContinuousOn η₂ (Icc 0 r))
    (h0₁ : (η₁ 0).im = 0) (h0₂ : (η₂ 0).im = 0) : ContinuousOn (retPath η₁ u η₂) (Icc 0 (retLen u r)) := by
  have hu2 : u ≤ 2 * u := by rw [two_mul]; exact le_add_self
  have h21 : 2 * u ≤ 2 * u + 1 := le_self_add
  have h1L : 2 * u + 1 ≤ retLen u r := le_self_add
  refine continuousOn_Icc_union (zero_le.trans h21) h1L
    (continuousOn_Icc_union (zero_le.trans hu2) h21 (continuousOn_Icc_union zero_le hu2 ?_ ?_) ?_) ?_
  · exact hc₁.congr fun s hs => retPath_apply_le hs.2
  · have hm : MapsTo (fun s : ℝ≥0 => 2 * u - s) (Icc u (2 * u)) (Icc 0 u) := fun s hs =>
      ⟨zero_le, tsub_le_iff_right.2 (by rw [two_mul]; exact add_le_add_right hs.1 u)⟩
    exact (hc₁.comp (continuous_const.sub continuous_id).continuousOn hm).congr fun s hs =>
      retPath_apply_back hs.1 hs.2
  · have hcont : Continuous fun s : ℝ≥0 =>
        (((η₁ 0).re + ((s : ℝ) - 2 * u) * ((η₂ 0).re - (η₁ 0).re) : ℝ) : ℂ) := by fun_prop
    exact hcont.continuousOn.congr fun s hs => retPath_apply_seg h0₁ hs.1 hs.2
  · have hm : MapsTo (fun s : ℝ≥0 => s - (2 * u + 1)) (Icc (2 * u + 1) (retLen u r)) (Icc 0 r) := fun s hs =>
      ⟨zero_le, tsub_le_iff_left.2 hs.2⟩
    exact (hc₂.comp (continuous_id.sub continuous_const).continuousOn hm).congr fun s hs =>
      retPath_apply_fwd h0₂ hs.1

/-- The fake path ends at the second tip. -/
theorem retPath_end (h0₂ : (η₂ 0).im = 0) : retPath η₁ u η₂ (retLen u r) = η₂ r := by
  rw [retLen, retPath_apply_fwd h0₂ le_self_add, add_tsub_cancel_left]

/-- Every value of the fake path is a point of the first prefix, a real point, or a point of the second prefix
(strictly before `r` if the time is strictly before the end). -/
theorem retPath_cases (h0₂ : (η₂ 0).im = 0) {s : ℝ≥0} (hs : s ≤ retLen u r) :
    retPath η₁ u η₂ s ∈ η₁ '' Icc 0 u ∨ (retPath η₁ u η₂ s).im = 0 ∨
      ∃ t ≤ r, (s < retLen u r → t < r) ∧ retPath η₁ u η₂ s = η₂ t := by
  by_cases h1 : s ≤ u
  · exact Or.inl ⟨s, ⟨zero_le, h1⟩, (retPath_apply_le h1).symm⟩
  by_cases h2 : s ≤ 2 * u
  · refine Or.inl ⟨2 * u - s, ⟨zero_le, tsub_le_iff_right.2 ?_⟩, (retPath_apply_back (not_le.1 h1).le h2).symm⟩
    rw [two_mul]; exact add_le_add_right (not_le.1 h1).le u
  by_cases h3 : s ≤ 2 * u + 1
  · refine Or.inr (Or.inl ?_)
    unfold retPath
    simp only [h1, h2, h3, ↓reduceIte, ofReal_im]
  · refine Or.inr (Or.inr ⟨s - (2 * u + 1), tsub_le_iff_left.2 hs, fun hsL => ?_,
      retPath_apply_fwd h0₂ (not_le.1 h3).le⟩)
    exact (tsub_lt_iff_left (not_le.1 h3).le).2 hsL

theorem mapsTo_retPath (hH₁ : MapsTo η₁ (Icc 0 u) Hbar) (hH₂ : MapsTo η₂ (Icc 0 r) Hbar)
    (h0₂ : (η₂ 0).im = 0) : MapsTo (retPath η₁ u η₂) (Icc 0 (retLen u r)) Hbar := by
  intro s hs
  rcases retPath_cases (η₁ := η₁) h0₂ hs.2 with ⟨s', hs', he⟩ | him | ⟨t, ht, -, he⟩
  · rw [← he]; exact hH₁ hs'
  · show (0 : ℝ) ≤ _; rw [him]
  · rw [he]; exact hH₂ ⟨zero_le, ht⟩

/-- The fake pair has the retained union up to real points. -/
theorem prefixSet_retPath_union_real (h0₂ : (η₂ 0).im = 0) :
    prefixSet (retPath η₁ u η₂) (retLen u r) η₂ r ∪ realLine = prefixSet η₁ u η₂ r ∪ realLine := by
  apply Subset.antisymm
  · rintro z ((⟨s, hs, rfl⟩ | hz) | hz)
    · rcases retPath_cases (η₁ := η₁) h0₂ hs.2 with h | h | ⟨t, ht, -, he⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · rw [he]; exact Or.inl (Or.inr ⟨t, ⟨zero_le, ht⟩, rfl⟩)
    · exact Or.inl (Or.inr hz)
    · exact Or.inr hz
  · rintro z ((⟨s, hs, rfl⟩ | hz) | hz)
    · refine Or.inl (Or.inl ⟨s, ⟨zero_le, hs.2.trans ?_⟩, retPath_apply_le hs.2⟩)
      exact (le_trans (by rw [two_mul]; exact le_add_self) le_self_add : u ≤ 2 * u + 1).trans le_self_add
    · exact Or.inl (Or.inr hz)
    · exact Or.inr hz

/-! ### The retained chart -/

/-- **The hydrodynamic chart of a retained pair at the second tip** `η₂(r)`: the first-contact chart of the fake pair
(`retPath η₁ u η₂` up to `2u + 1 + r`, `η₂` up to `r`), which by `prefixSet_retPath_union_real` has the active
domain `activeDomain η₁ u η₂ r`, the filling `fill(η₁([0, u]) ∪ η₂([0, r]))` and the same regular points. -/
def IsRetChart (η₁ : ℝ≥0 → ℂ) (u : ℝ≥0) (η₂ : ℝ≥0 → ℂ) (r : ℝ≥0) (φ ψ : ℂ → ℂ) (lift : ℂ → ℝ) : Prop :=
  IsFirstContactChart (retPath η₁ u η₂) (retLen u r) η₂ r φ ψ lift

theorem activeDomain_retPath (h0₂ : (η₂ 0).im = 0) :
    activeDomain (retPath η₁ u η₂) (retLen u r) η₂ r = activeDomain η₁ u η₂ r :=
  activeDomain_eq_of_union_real (prefixSet_retPath_union_real h0₂)

theorem fillH_retPath (h0₂ : (η₂ 0).im = 0) :
    fillH (prefixSet (retPath η₁ u η₂) (retLen u r) η₂ r) = fillH (prefixSet η₁ u η₂ r) :=
  fillH_eq_of_union_real (prefixSet_retPath_union_real h0₂)

/-- **The retained chart exists** (Lemma G7's "inherited hydrodynamic chart", with the active tip at `0`): if the
second tip `η₂(r)` is interior, off the first prefix, not visited earlier by `η₂`, and adherent to the active domain,
then the mapping-out function of the filled union has a real forward limit `x₀` at the tip and, for every continuous
branch of `arg φ′`, `φ = g − x₀` is a retained chart. -/
theorem exists_retChart (hc₁ : ContinuousOn η₁ (Icc 0 u)) (hc₂ : ContinuousOn η₂ (Icc 0 r))
    (hH₁ : MapsTo η₁ (Icc 0 u) Hbar) (hH₂ : MapsTo η₂ (Icc 0 r) Hbar) (h0₁ : (η₁ 0).im = 0)
    (h0₂ : (η₂ 0).im = 0) (hpH : η₂ r ∈ H) (hp₁ : η₂ r ∉ η₁ '' Icc 0 u) (hne₂ : ∀ t < r, η₂ t ≠ η₂ r)
    (hcl : η₂ r ∈ closure (activeDomain η₁ u η₂ r)) :
    ∃ x₀ : ℝ, Tendsto (ConformalImage.mapOut (fillH (prefixSet η₁ u η₂ r)))
      (𝓝[activeDomain η₁ u η₂ r] (η₂ r)) (𝓝 (x₀ : ℂ)) ∧
    ∀ lift : ℂ → ℝ, ContinuousOn lift (activeDomain η₁ u η₂ r) →
      (∀ z ∈ activeDomain η₁ u η₂ r,
        deriv (fun z => ConformalImage.mapOut (fillH (prefixSet η₁ u η₂ r)) z - x₀) z =
          (‖deriv (fun z => ConformalImage.mapOut (fillH (prefixSet η₁ u η₂ r)) z - x₀) z‖ : ℂ) *
            exp (I * (lift z : ℂ))) →
      ∃ ψ : ℂ → ℂ, IsRetChart η₁ u η₂ r (fun z => ConformalImage.mapOut (fillH (prefixSet η₁ u η₂ r)) z - x₀)
        ψ lift := by
  have hend := retPath_end (η₁ := η₁) (u := u) (r := r) h0₂
  have hdom := activeDomain_retPath (η₁ := η₁) (u := u) (r := r) h0₂
  have hfill := fillH_retPath (η₁ := η₁) (u := u) (r := r) h0₂
  have hne₁ : ∀ s < retLen u r, retPath η₁ u η₂ s ≠ retPath η₁ u η₂ (retLen u r) := by
    intro s hs he
    rw [hend] at he
    rcases retPath_cases (η₁ := η₁) h0₂ hs.le with h | h | ⟨t, -, ht, he'⟩
    · exact hp₁ (he ▸ h)
    · exact (ne_of_gt (show (0 : ℝ) < (η₂ r).im from hpH)) (he ▸ h)
    · exact hne₂ t (ht hs) (he'.symm.trans he)
  have h0₁' : (retPath η₁ u η₂ 0).im = 0 := by rw [retPath_apply_le zero_le]; exact h0₁
  obtain ⟨x₀, hx₀, hψ⟩ := exists_isFirstContactChart_mapOut (continuousOn_retPath hc₁ hc₂ h0₁ h0₂) hc₂
    (mapsTo_retPath hH₁ hH₂ h0₂) hH₂ h0₁' h0₂ hend hne₁ (fun t ht => hend ▸ hne₂ t ht)
    (by rw [hend, hdom]; exact hcl)
  rw [hfill, hdom, hend] at hx₀
  refine ⟨x₀, hx₀, fun lift hlc hlift => ?_⟩
  rw [← hdom] at hlc hlift
  rw [← hfill] at hlift ⊢
  exact hψ lift hlc hlift

/-! ### The API of the retained chart -/

namespace IsRetChart

variable {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ} (hC : IsRetChart η₁ u η₂ r φ ψ lift) (h0₂ : (η₂ 0).im = 0)
include hC h0₂

theorem isActiveChart : IsActiveChart (activeDomain η₁ u η₂ r) (η₂ r) φ := by
  have h := hC.1
  rwa [activeDomain_retPath h0₂, retPath_end h0₂] at h

theorem bijOn : BijOn ψ H (activeDomain η₁ u η₂ r) := by
  have h := hC.2.1
  rwa [activeDomain_retPath h0₂] at h

omit h0₂ in
theorem fwd_inv : ∀ w ∈ H, φ (ψ w) = w := hC.2.2.1

theorem inv_notMem : ∀ w ∉ H, ψ w ∉ activeDomain η₁ u η₂ r := by
  have h := hC.2.2.2.1
  rwa [activeDomain_retPath h0₂] at h

theorem continuousOn_lift : ContinuousOn lift (activeDomain η₁ u η₂ r) := by
  have h := hC.2.2.2.2.1
  rwa [activeDomain_retPath h0₂] at h

theorem deriv_eq : ∀ z ∈ activeDomain η₁ u η₂ r,
    deriv φ z = (‖deriv φ z‖ : ℂ) * exp (I * (lift z : ℂ)) := by
  have h := hC.2.2.2.2.2.1
  rwa [activeDomain_retPath h0₂] at h

omit h0₂ in
theorem differentiableOn_inv : DifferentiableOn ℂ ψ H := hC.2.2.2.2.2.2.1

omit h0₂ in
theorem continuousOn_inv : ContinuousOn ψ Hbar := hC.2.2.2.2.2.2.2.1

theorem inv_zero : ψ 0 = η₂ r := by
  rw [hC.2.2.2.2.2.2.2.2.1, retPath_end h0₂]

/-- Forward limits with unique preimages at the regular points of the closure of the active domain. -/
theorem exists_tendsto_of_regular {z : ℂ} (hz : z ∈ closure (activeDomain η₁ u η₂ r))
    (hreg : IsChartRegularPoint η₁ u η₂ r z) :
    ∃ w ∈ Hbar, Tendsto φ (𝓝[activeDomain η₁ u η₂ r] z) (𝓝 w) ∧ ψ w = z ∧
      ∀ w' ∈ Hbar, ψ w' = z → w' = w := by
  have h := hC.2.2.2.2.2.2.2.2.2.2 z
  rw [activeDomain_retPath h0₂] at h
  exact h hz ((isChartRegularPoint_iff_of_union_real (prefixSet_retPath_union_real h0₂) z).2 hreg)

end IsRetChart

end Supp7

end InteractingSLE
