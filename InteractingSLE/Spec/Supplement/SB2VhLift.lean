/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2TcRec

/-!
# SB2(1)'s version half: the S2 lift is the chart image of the flow at its good times

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108). The record's S2 lift `γ` is a priori a
chosen curve with `g ∘ γ = β'(t_L + ·)`. To build the version from the line marks it must be read from the flow:

* `eq_fwd_of_mem` (deterministic): a point `w ∈ ℍ̄` whose boundary-map image lies in the chart domain `ℍ \ fill A` is
  the forward chart image of it (`g` maps `ℝ` off the domain, `SB.g_ofReal_notMem`);
* **`lift_eq_fwd`**: in the record, `γ s = c'(η(t_L + s) − u)` (`c' = shiftChart c u m`) whenever
  `t_L + s` is before the horizon and the shifted flow is in the shifted domain at `t_L + s`;
* **`lift_eqOn_of_dense`**: two continuous curves agreeing on a dense set of times agree (so any two records' lifts
  agree below their common horizon once the good times are dense);
* `interior_eq_empty_of_subset_union`, **`interior_notMem_dom_eq_empty`**: the times after the entrance where the
  shifted flow is outside the chart domain have empty interior (no real arc, no common arc, S2's hull clause), so
  the good times are dense.

Deterministic in the data; nothing here replaces a source statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Vh

open Lv

/-- **A point of `ℍ̄` whose boundary-map image lies in the chart domain is the forward image of it.** -/
theorem eq_fwd_of_mem {A : Set ℂ} {c : Chart} (hD : IsDomainChart (H \ fillH A) c) {g : ℂ → ℂ}
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) {w : ℂ} (hw : 0 ≤ w.im)
    (hgw : g w ∈ H \ fillH A) : c.1 (g w) = w := by
  have hwH : w ∈ H := by
    rcases hw.lt_or_eq with h | h
    · exact h
    · exfalso
      have he : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← h])
      rw [he] at hgw
      exact SB.g_ofReal_notMem hD hgc hgi w.re hgw
  rw [hgi hwH]
  exact hD.1.2.2 w hwH

/-- **The record's lift is the forward chart image of the shifted flow at its good times**: if `g ∘ γ = β'(t_L + ·)`,
`β' = η − u` before the horizon `t_L + S₁`, and `η(t_L + s) − u` lies in the shifted domain `ℍ \ fill A'`, then
`γ s = c'(η(t_L + s) − u)`. -/
theorem lift_eq_fwd {A' : Set ℂ} {c' : Chart} (hD : IsDomainChart (H \ fillH A') c') {g : ℂ → ℂ}
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c'.2.1 H) {β' γ η : ℝ≥0 → ℂ} {tL : ℝ≥0} {u S₁ : ℝ}
    (hγ : Supp9B.IsProperCurve γ) (hlift : ∀ s, g (γ s) = β' (tL + s))
    (hagree : ∀ t : ℝ≥0, (t : ℝ) < (tL : ℝ) + S₁ → β' t = η t - u) {s : ℝ≥0} (hs : (s : ℝ) < S₁)
    (hgood : η (tL + s) - u ∈ H \ fillH A') : γ s = c'.1 (η (tL + s) - u) := by
  have h1 : g (γ s) = η (tL + s) - u := by
    rw [hlift s, hagree (tL + s) (by push_cast; linarith)]
  rw [← h1]
  exact (eq_fwd_of_mem hD hgc hgi (hγ.2.2.1 s) (h1 ▸ hgood)).symm

/-- **Continuous curves agreeing on a dense set of times agree** on the closure of that set. -/
theorem lift_eqOn_of_dense {γ₁ γ₂ : ℝ≥0 → ℂ} (h₁ : Continuous γ₁) (h₂ : Continuous γ₂) {G : Set ℝ≥0}
    (hG : EqOn γ₁ γ₂ G) : EqOn γ₁ γ₂ (closure G) :=
  hG.closure h₁ h₂

/-- **Empty interior of a union with a relatively closed part**: if `R = I ∩ F` with `F` closed and both `R` and `B`
have empty interior, so does every subset of `I` inside `R ∪ B`. -/
theorem interior_eq_empty_of_subset_union {I F X B : Set ℝ} (hF : IsClosed F)
    (hR : interior (I ∩ F) = ∅) (hB : interior B = ∅) (hX : X ⊆ I) (hXRB : X ⊆ (I ∩ F) ∪ B) :
    interior X = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hne
  set U := interior X
  by_cases hUF : (U \ F).Nonempty
  · obtain ⟨y, hy⟩ := hUF
    have hsub : U \ F ⊆ B := fun z hz => by
      rcases hXRB (interior_subset hz.1) with h | h
      · exact absurd h.2 hz.2
      · exact h
    have hopen : IsOpen (U \ F) := isOpen_interior.sdiff hF
    have := interior_maximal hsub hopen hy
    rw [hB] at this
    exact this
  · have hsub : U ⊆ I ∩ F := fun z hz => ⟨hX (interior_subset hz), by
      by_contra hzF
      exact hUF ⟨z, hz, hzF⟩⟩
    have := interior_maximal hsub isOpen_interior hx
    rw [hR] at this
    exact this

/-- **The times where the shifted flow leaves the chart domain have empty interior** after the entrance: from no
real arc, no common arc with `A'`, and S2's hull clause (a point of `ℍ` after `t_L` off `A'` is in `ℍ \ fill A'`). -/
theorem interior_notMem_dom_eq_empty {A' : Set ℂ} {β' : ℝ≥0 → ℂ} (hβ' : Continuous β')
    (hβ'H : ∀ t, 0 ≤ (β' t).im) {tL : ℝ≥0} {S : ℝ}
    (hhull : ∀ t : ℝ≥0, tL < t → β' t ∈ H → β' t ∉ A' → β' t ∈ H \ fillH A')
    (hnR : interior {r ∈ Ioo (0 : ℝ) S | β' (tL + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅)
    (hnA : interior {r ∈ Ioo (0 : ℝ) S | β' (tL + r.toNNReal) ∈ closure A'} = ∅) :
    interior {r ∈ Ioo (0 : ℝ) S | β' (tL + r.toNNReal) ∉ H \ fillH A'} = ∅ := by
  have hc : Continuous fun r : ℝ => β' (tL + r.toNNReal) :=
    hβ'.comp (continuous_const.add continuous_real_toNNReal)
  have hF : IsClosed {r : ℝ | (β' (tL + r.toNNReal)).im = 0} :=
    isClosed_eq (Complex.continuous_im.comp hc) continuous_const
  refine interior_eq_empty_of_subset_union hF ?_ hnA (fun r hr => hr.1) fun r hr => ?_
  · have e : Ioo (0 : ℝ) S ∩ {r : ℝ | (β' (tL + r.toNNReal)).im = 0} =
        {r ∈ Ioo (0 : ℝ) S | β' (tL + r.toNNReal) ∈ {z : ℂ | z.im = 0}} := rfl
    rw [e]; exact hnR
  · by_cases hH : β' (tL + r.toNNReal) ∈ H
    · right
      refine ⟨hr.1, subset_closure ?_⟩
      by_contra hA
      have htL : tL < tL + r.toNNReal := lt_add_of_pos_right _ (Real.toNNReal_pos.2 hr.1.1)
      exact hr.2 (hhull _ htL hH hA)
    · left
      refine ⟨hr.1, ?_⟩
      have h0 := hβ'H (tL + r.toNNReal)
      have h1 : ¬ 0 < (β' (tL + r.toNNReal)).im := hH
      show (β' (tL + r.toNNReal)).im = 0
      linarith [not_lt.1 h1]

end InteractingSLE.Theorem14.SB.Vh
