/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Theorem15D5Inputs

/-!
# The rational-cut collar of Theorem 7.12D at real contacts and at the second terminal time

Packet PROVE-RC-ORD (ruling R124 (b)). The interior collar `Theorem15D5.notMem_H_of_firstHit_strict` turns a strict
interior contact into a retained pair `(u, r)` with a first new hit `η₁(x*) ∈ ℍ`, `x* < u`. Here the contact
`α(s) = β(t)` may be a real point and `t` may be the second path's terminal time; the first-hit exclusion is the real
one (`RealContact.G7GB7aFirstHitRealStatement`, hit allowed in `∂ℍ` and at `t ≤ ζ₂`).

The only new point is `x* < u`. At an interior contact strictly before both lifetimes it follows from the strict
contact order applied to `(s, t)`; when `t = ζ₂` that order is not available at `(s, t)`. Instead take **two cutoffs**
`s < u₀ < u₁ < ζ₁` and one time `r ∈ (0, t)` with `β(r) ∉ α([0, u₁])` (W0b). Let `T_i ∈ (r, t]` be the first hit of
`A_i = α([0, u_i])` after `r`, at `α(x_i)`, `x_i ≤ u_i`. If `x_i < u_i` the first-hit exclusion applies. Otherwise both
hits are at the cutoff tips: `β(T_i) = α(u_i)`. Then `T₁ ≤ T₀` (`A₀ ⊆ A₁`), `T₀ < t` (at `T₀ = t`, injectivity of `α`
gives `u₀ = s`), so both contacts `(u₀, T₀)`, `(u₁, T₁)` are strictly before both lifetimes, and the strict contact
order gives `T₀ < T₁`, a contradiction.

## Main results

* `exists_firstHit_Icc`: the first hit of a compact prefix after a time off it (compactness);
* `false_of_contact_of_firstHitReal`: **no contact `α(s) = β(t)` with `s < ζ₁`, `0 < t ≤ ζ₂`** for continuous paths
  with `α` injective, the strict contact order, W0b in second-arc form and the real first-hit exclusion.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal

namespace InteractingSLE

namespace RealContact

open Theorem15D5

/-- **The first hit of a prefix after a time off it.** For continuous paths, a cutoff `u < ζ₁`, a contact
`α(s) = β(t)` with `s ≤ u`, `t ≤ ζ₂`, and a time `r < t` with `β(r) ∉ α([0, u])`, there is a least time `T ∈ (r, t]`
with `β(T) ∈ α([0, u])`; it is `β(T) = α(x)` with `x ≤ u`, and `β` avoids `α([0, u])` on `(r, T)`. -/
theorem exists_firstHit_Icc {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}
    (hcα : ContinuousOn α {s | (s : ℝ≥0∞) ≤ ζ₁}) (hcβ : ContinuousOn β {t | (t : ℝ≥0∞) ≤ ζ₂})
    {u r t s : ℝ≥0} (hu : (u : ℝ≥0∞) < ζ₁) (ht : (t : ℝ≥0∞) ≤ ζ₂) (hrt : r < t) (hsu : s ≤ u)
    (hst : α s = β t) (hr : β r ∉ α '' Icc 0 u) :
    ∃ T x : ℝ≥0, r < T ∧ T ≤ t ∧ x ≤ u ∧ β T = α x ∧
      ∀ t' : ℝ≥0, r < t' → t' < T → β t' ∉ α '' Icc 0 u := by
  have hAc : IsClosed (α '' Icc 0 u) :=
    (isCompact_Icc.image_of_continuousOn
      (hcα.mono fun s (hs : s ∈ Icc 0 u) => (ENNReal.coe_le_coe.mpr hs.2).trans hu.le)).isClosed
  have hβIcc : ContinuousOn β (Icc r t) :=
    hcβ.mono fun t' (ht' : t' ∈ Icc r t) => (ENNReal.coe_le_coe.mpr ht'.2).trans ht
  have hSc : IsCompact (Icc r t ∩ β ⁻¹' (α '' Icc 0 u)) :=
    isCompact_Icc.of_isClosed_subset (hβIcc.preimage_isClosed_of_isClosed isClosed_Icc hAc)
      inter_subset_left
  have hSne : (Icc r t ∩ β ⁻¹' (α '' Icc 0 u)).Nonempty :=
    ⟨t, ⟨hrt.le, le_rfl⟩, ⟨s, ⟨zero_le, hsu⟩, hst⟩⟩
  obtain ⟨T, ⟨⟨hrT, hTt⟩, x, hx, hβx⟩, hleast⟩ := hSc.exists_isLeast hSne
  have hrT' : r < T := lt_of_le_of_ne hrT fun h => by
    subst h
    exact hr ⟨x, hx, hβx⟩
  exact ⟨T, x, hrT', hTt, hx.2, hβx.symm, fun t' h1 h2 hmem =>
    not_le.mpr h2 (hleast ⟨⟨h1.le, h2.le.trans hTt⟩, hmem⟩)⟩

/-- **The rational-cut collar at real contacts and at the second terminal time** (Theorem 7.12D's construction,
specification pp. 543–544, extended to `∂ℍ` and to `t = ζ₂`). For continuous available paths `α`, `β` with `α`
injective, the increasing order of the strict contacts, W0b in second-arc form (no open arc of `β` before `c < ζ₂` lies
on `α([0, a])`, `a < ζ₁`) and the real first-hit exclusion at retained pairs, there is no contact `α(s) = β(t)` with
`s < ζ₁` and `0 < t ≤ ζ₂`. -/
theorem false_of_contact_of_firstHitReal {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}
    (hcα : ContinuousOn α {s | (s : ℝ≥0∞) ≤ ζ₁}) (hcβ : ContinuousOn β {t | (t : ℝ≥0∞) ≤ ζ₂})
    (hiα : InjOn α {s | (s : ℝ≥0∞) ≤ ζ₁}) (hCI : StrictContactsIncreasing α ζ₁ β ζ₂)
    (hW0b : ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → (c : ℝ≥0∞) < ζ₂ →
      ¬ ∃ y₁ y₂ : ℝ≥0, y₁ < y₂ ∧ y₂ ≤ c ∧ β '' Ioo y₁ y₂ ⊆ α '' Icc 0 a)
    (hFH : ∀ u r : ℝ≥0, (u : ℝ≥0∞) < ζ₁ → (r : ℝ≥0∞) < ζ₂ → β r ∉ α '' Icc 0 u →
      ∀ t x : ℝ≥0, r < t → (t : ℝ≥0∞) ≤ ζ₂ → x < u → β t = α x →
        (∀ t' : ℝ≥0, r < t' → t' < t → β t' ∉ α '' Icc 0 u) → False)
    {s t : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ₁) (ht : (t : ℝ≥0∞) ≤ ζ₂) (ht0 : 0 < t) (hst : α s = β t) :
    False := by
  -- two cutoffs `s < u₀ < u₁ < ζ₁`
  obtain ⟨u₁, hsu₁, hu₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hs
  have hsu₁' : s < u₁ := ENNReal.coe_lt_coe.mp hsu₁
  obtain ⟨u₀, hsu₀, hu₀u₁⟩ := exists_between hsu₁'
  have hu₀ : (u₀ : ℝ≥0∞) < ζ₁ := (ENNReal.coe_lt_coe.mpr hu₀u₁).trans hu₁
  -- a time `r ∈ (0, c)`, `c < t`, off the larger prefix (W0b)
  obtain ⟨c, hc0, hct⟩ := exists_between ht0
  have hc : (c : ℝ≥0∞) < ζ₂ := (ENNReal.coe_lt_coe.mpr hct).trans_le ht
  obtain ⟨r, hrI, hr⟩ : ∃ r ∈ Ioo 0 c, β r ∉ α '' Icc 0 u₁ := by
    by_contra hcon
    push Not at hcon
    refine hW0b u₁ c hu₁ hc ⟨0, c, hc0, le_rfl, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact hcon r hr
  have hrt : r < t := hrI.2.trans hct
  have hrζ : (r : ℝ≥0∞) < ζ₂ := (ENNReal.coe_lt_coe.mpr hrt).trans_le ht
  have hr₀ : β r ∉ α '' Icc 0 u₀ := fun hm => hr (image_mono (Icc_subset_Icc le_rfl hu₀u₁.le) hm)
  -- the first hits of the two prefixes after `r`
  obtain ⟨T₀, x₀, hrT₀, hT₀t, hx₀, hβ₀, hgap₀⟩ := exists_firstHit_Icc hcα hcβ hu₀ ht hrt hsu₀.le hst hr₀
  obtain ⟨T₁, x₁, hrT₁, hT₁t, hx₁, hβ₁, hgap₁⟩ := exists_firstHit_Icc hcα hcβ hu₁ ht hrt hsu₁'.le hst hr
  -- the first-hit exclusion puts both hits at the cutoff tips
  have hx₀u : x₀ = u₀ := le_antisymm hx₀ (not_lt.1 fun hlt =>
    hFH u₀ r hu₀ hrζ hr₀ T₀ x₀ hrT₀ ((ENNReal.coe_le_coe.mpr hT₀t).trans ht) hlt hβ₀ hgap₀)
  have hx₁u : x₁ = u₁ := le_antisymm hx₁ (not_lt.1 fun hlt =>
    hFH u₁ r hu₁ hrζ hr T₁ x₁ hrT₁ ((ENNReal.coe_le_coe.mpr hT₁t).trans ht) hlt hβ₁ hgap₁)
  rw [hx₀u] at hβ₀
  rw [hx₁u] at hβ₁
  -- the larger prefix is hit no later
  have hT₁T₀ : T₁ ≤ T₀ := not_lt.1 fun hlt =>
    hgap₁ T₀ hrT₀ hlt ⟨u₀, ⟨zero_le, hu₀u₁.le⟩, hβ₀.symm⟩
  -- the smaller tip is hit strictly before `t` (injectivity of `α`)
  have hT₀t' : T₀ < t := lt_of_le_of_ne hT₀t fun he => by
    rw [he] at hβ₀
    exact hsu₀.ne' (hiα hu₀.le hs.le (hβ₀.symm.trans hst.symm))
  have hT₀ζ : (T₀ : ℝ≥0∞) < ζ₂ := (ENNReal.coe_lt_coe.mpr hT₀t').trans_le ht
  have hT₁ζ : (T₁ : ℝ≥0∞) < ζ₂ := (ENNReal.coe_le_coe.mpr hT₁T₀).trans_lt hT₀ζ
  exact absurd (hCI u₀ u₁ T₀ T₁ hu₀ hu₁ hT₀ζ hT₁ζ hβ₀.symm hβ₁.symm hu₀u₁) (not_lt.2 hT₁T₀)

end RealContact

end InteractingSLE
