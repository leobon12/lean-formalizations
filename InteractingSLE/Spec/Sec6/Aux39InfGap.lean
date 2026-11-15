/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux39InfPocket

/-!
# Propositions 1.5–1.6 with the junction at infinity, from the physical pocket

Ruling R41's note (`source/external/AstraIG1/ig1_ztip_elimination.txt` L230–L315), Propositions 1.5
(old and fresh start) and 1.6 (`p ∈ R_s`), in the case where the pocket junction is the original
target: "If the target junction is infinity, the two proper incoming arms give the same separation
directly ... The finite bounded path cannot use that point. In either case its endpoint gates
agree."

The pocket `C` is open with `∂C = α₁([c₁, ∞)) ∪ α₂([c₂, ∞))` (proper simple paths), far real points
are outside `C̄`, and at the chart time `r` the parts `α_i([c_i, u_i])` are not in `D_r` while the
prefixes `α_i((u_i, ∞))` are in `D_r` and disjoint. The lifted prefixes are compactified by a real
Möbius map `ψ_p` with `p` to the left of the gates and of the gap path (`Aux39InfArm`), and the gate
lemma at infinity (`Aux39Inf`) with the face identification (`Aux39InfPocket`) gives the gap
equality, for distinct or equal gates.

## Main results

* `psiArms_inter`: the two compactified arcs meet only at `0` or at a common gate;
* `ownFuture_gap_eq_of_pocket_inf`: **Propositions 1.5–1.6 at infinity**: for a gap `[a, b]` after
  the chart time `r` (old start, `a` a limit of `C`-visits) or at `r = a` (fresh start: `η(a)` a
  fresh interior attachment), `δ_s(a) = δ_s(b)` for `0 ≤ s ≤ r` and `η(a) = η(b)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec6

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- Two compactified arcs whose open parts are disjoint meet only at `0` or at a common start. -/
theorem psiArms_inter {b₁ b₂ : ℝ → ℂ} {x₁ x₂ : ℝ} (hb₁0 : b₁ 0 = x₁) (hb₂0 : b₂ 0 = x₂)
    (hb₁1 : b₁ 1 = 0) (hb₂1 : b₂ 1 = 0) (hb₁H : ∀ t ∈ Ioo (0 : ℝ) 1, b₁ t ∈ H)
    (hb₂H : ∀ t ∈ Ioo (0 : ℝ) 1, b₂ t ∈ H)
    (hdisj : ∀ w ∈ b₁ '' Ioo 0 1, w ∉ b₂ '' Ioo 0 1) {w : ℂ} (hw₁ : w ∈ b₁ '' Icc 0 1)
    (hw₂ : w ∈ b₂ '' Icc 0 1) : w = 0 ∨ (w = x₁ ∧ w = x₂) := by
  have hreal : ∀ {b : ℝ → ℂ}, (∀ t ∈ Ioo (0 : ℝ) 1, b t ∈ H) → ∀ w ∈ b '' Ioo 0 1, w ∈ H := by
    rintro b hbH _ ⟨t, ht, rfl⟩; exact hbH t ht
  rcases mem_arc_trichotomy hw₁ with h1 | h1 | h1 <;>
    rcases mem_arc_trichotomy hw₂ with h2 | h2 | h2
  · exact Or.inr ⟨h1.trans hb₁0, h2.trans hb₂0⟩
  · exact absurd (by have := hreal hb₂H w h2; rwa [h1, hb₁0] at this) (not_mem_H_ofReal x₁)
  · exact Or.inl (h2.trans hb₂1)
  · exact absurd (by have := hreal hb₁H w h1; rwa [h2, hb₂0] at this) (not_mem_H_ofReal x₂)
  · exact absurd h2 (hdisj w h1)
  · exact Or.inl (h2.trans hb₂1)
  · exact Or.inl (h1.trans hb₁1)
  · exact Or.inl (h1.trans hb₁1)
  · exact Or.inl (h1.trans hb₁1)

/-- **Propositions 1.5–1.6 with the junction at infinity, from the physical pocket.** The pocket
`C` is open with `∂C = α₁([c₁, ∞)) ∪ α₂([c₂, ∞))` (continuous, injective, proper), far real points
are outside `C̄`, and at the chart time `r` the parts `α_i([c_i, u_i])` are not in `D_r` while the
prefixes `α_i((u_i, ∞))` are in `D_r` and disjoint. Let `[a, b]` (`r ≤ a < b`) be a gap: the trace
avoids `C` and the unvisited prefixes on `[a, b]`, and `b` is a limit of `C`-visits after `r`.
Suppose either `a` is also such a limit (old start), or `r = a` and `η(a)` is a fresh interior
point equal to one of the current attachments `α_i(u_i)` (fresh start, Lemma 1.4). Then
`δ_s(a) = δ_s(b)` for every `0 ≤ s ≤ r`, and `η(a) = η(b)`. -/
theorem ownFuture_gap_eq_of_pocket_inf (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {C : Set ℂ} (hC : IsOpen C)
    (hCR : ∃ M, ∀ y : ℝ, M ≤ |y| → (y : ℂ) ∉ closure C) {α₁ α₂ : ℝ → ℂ} {c₁ u₁ c₂ u₂ : ℝ}
    (hcu₁ : c₁ ≤ u₁) (hcu₂ : c₂ ≤ u₂) (hα₁ : ContinuousOn α₁ (Ici c₁))
    (hα₂ : ContinuousOn α₂ (Ici c₂)) (hα₁i : InjOn α₁ (Ici c₁)) (hα₂i : InjOn α₂ (Ici c₂))
    (hα₁t : Tendsto (fun t => ‖α₁ t‖) atTop atTop) (hα₂t : Tendsto (fun t => ‖α₂ t‖) atTop atTop)
    (hfrC : frontier C = α₁ '' Ici c₁ ∪ α₂ '' Ici c₂)
    (h12 : ∀ v ∈ Ioi u₁, ∀ v' ∈ Ioi u₂, α₁ v ≠ α₂ v')
    {s r a b : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hra : r ≤ a) (hab : a < b)
    (hα₁D : ∀ v ∈ Ioi u₁, α₁ v ∈ H \ fwdHull W r) (hα₂D : ∀ v ∈ Ioi u₂, α₂ v ∈ H \ fwdHull W r)
    (hα₁K : ∀ v ∈ Icc c₁ u₁, α₁ v ∉ H \ fwdHull W r)
    (hα₂K : ∀ v ∈ Icc c₂ u₂, α₂ v ∉ H \ fwdHull W r)
    (hgap : ∀ t ∈ Icc a b, η t ∉ C) (hunv₁ : ∀ t ∈ Icc a b, ∀ v ∈ Ioi u₁, η t ≠ α₁ v)
    (hunv₂ : ∀ t ∈ Icc a b, ∀ v ∈ Ioi u₂, η t ≠ α₂ v)
    (hstart : a ∈ closure {t | r < t ∧ η t ∈ C} ∨
      (r = a ∧ 0 < a ∧ η a ∈ H ∧ η a ∉ η '' Ico 0 a ∧ (η a = α₁ u₁ ∨ η a = α₂ u₂)))
    (hb : b ∈ closure {t | r < t ∧ η t ∈ C}) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  have hr : 0 ≤ r := hs.trans hsr
  -- the two gates
  obtain ⟨q₁, hq₁, hlim₁⟩ := exists_tendsto_lift_right hη hW hW0 hr
    (hα₁.mono fun t ht => hcu₁.trans ht.1) (fun t ht => hα₁D t ht.1) (hα₁K u₁ ⟨hcu₁, le_rfl⟩)
  obtain ⟨q₂, hq₂, hlim₂⟩ := exists_tendsto_lift_right hη hW hW0 hr
    (hα₂.mono fun t ht => hcu₂.trans ht.1) (fun t ht => hα₂D t ht.1) (hα₂K u₂ ⟨hcu₂, le_rfl⟩)
  -- the start: a supplied gate or a limit of visits
  have hga : (trMap W r a 0 = q₁ ∨ trMap W r a 0 = q₂) ∨ a ∈ closure {t | r < t ∧ η t ∈ C} := by
    rcases hstart with h1 | ⟨hra', ha0, haH, hfresh, hatt⟩
    · exact Or.inr h1
    · subst hra'
      have hδa : trMap W r r 0 = 0 := YuanSimpleApprox.trMap_self hW r zero_mem_Hbar
      left
      rcases hatt with h1 | h1
      · left; rw [hδa, fresh_tip_fibre hη hW hW0 ha0 haH hfresh (hq₁.trans h1.symm), ofReal_zero]
      · right; rw [hδa, fresh_tip_fibre hη hW hW0 ha0 haH hfresh (hq₂.trans h1.symm), ofReal_zero]
  -- a pole `p` to the left of the gates and of the gap path
  have hδc : ContinuousOn (fun t => trMap W r t 0) (Icc a b) :=
    (YuanSimpleApprox.continuousOn_trMap_zero hη hW hW0 hr).mono fun t ht => hra.trans ht.1
  obtain ⟨B, hB⟩ := (isCompact_Icc.image_of_continuousOn hδc).isBounded.exists_norm_le
  set p : ℝ := min (min q₁ q₂) (-|B|) - 1 with hp
  have hpq₁ : p < q₁ := by
    have := min_le_left (min q₁ q₂) (-|B|); have := min_le_left q₁ q₂; linarith
  have hpq₂ : p < q₂ := by
    have := min_le_left (min q₁ q₂) (-|B|); have := min_le_right q₁ q₂; linarith
  have hδp : ∀ t ∈ Icc a b, trMap W r t 0 ≠ p := by
    intro t ht h'
    have h1 : ‖trMap W r t 0‖ ≤ B := hB _ ⟨t, ht, rfl⟩
    rw [h', norm_real, Real.norm_eq_abs] at h1
    have h2 : p ≤ -|B| - 1 := by have := min_le_right (min q₁ q₂) (-|B|); linarith
    have h3 : |B| + 1 ≤ |p| := by
      rw [abs_of_neg (show p < 0 by linarith [abs_nonneg B])]; linarith
    linarith [le_abs_self B]
  -- the compactified arms
  obtain ⟨b₁, hb₁c, hb₁i, hb₁0, hb₁1, hb₁H, hb₁img⟩ := exists_psiArm hW hW0 hr
    (hα₁.mono (Ici_subset_Ici.2 hcu₁)) (hα₁i.mono (Ici_subset_Ici.2 hcu₁)) hα₁D hα₁t hlim₁ hpq₁
  obtain ⟨b₂, hb₂c, hb₂i, hb₂0, hb₂1, hb₂H, hb₂img⟩ := exists_psiArm hW hW0 hr
    (hα₂.mono (Ici_subset_Ici.2 hcu₂)) (hα₂i.mono (Ici_subset_Ici.2 hcu₂)) hα₂D hα₂t hlim₂ hpq₂
  have hdisj : ∀ w ∈ b₁ '' Ioo 0 1, w ∉ b₂ '' Ioo 0 1 := by
    intro w hw₁ hw₂
    rw [hb₁img] at hw₁; rw [hb₂img] at hw₂
    obtain ⟨_, ⟨_, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩ := hw₁
    obtain ⟨_, ⟨_, ⟨v', hv', rfl⟩, rfl⟩, he⟩ := hw₂
    have h1 := QuantumZipper.FwdHolo.injOn_fwdMap hW hr (hα₂D v' hv') (hα₁D v hv)
      (psiMap_injective he)
    exact h12 v hv v' hv' h1.symm
  have hfin := fun heq : trMap W r a 0 = trMap W r b 0 =>
    ownFuture_and_trace_eq hη hW hW0 hs hsr hra (hra.trans hab.le) heq
  rcases lt_trichotomy q₁ q₂ with hq | hq | hq
  · obtain ⟨hlt, hneg⟩ := psiMap_ofReal_lt hpq₁ hq
    have h : IsArcPairInf (-(q₁ - p)⁻¹) (-(q₂ - p)⁻¹) b₁ b₂ :=
      ⟨hlt, hneg, hb₁c, hb₂c, hb₁i, hb₂i, hb₁0, hb₂0, hb₁1, hb₂1, hb₁H, hb₂H, fun w hw => by
        rcases psiArms_inter hb₁0 hb₂0 hb₁1 hb₂1 hb₁H hb₂H hdisj hw.1 hw.2 with h' | ⟨h1, h2⟩
        · exact h'
        · exact absurd (ofReal_injective (h1.symm.trans h2)) hlt.ne⟩
    exact hfin (ownFuture_eq_of_psiArms hη hW hW0 hr hC hCR hcu₁ hcu₂ hfrC hα₁D hα₂D hα₁K hα₂K
      h hpq₂ rfl rfl hb₁img hb₂img hra hab hδp hgap hunv₁ hunv₂ hga hb)
  · subst hq
    have hx0 : -(q₁ - p)⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 (by linarith))
    exact hfin (ownFuture_eq_of_psiArms_eq hη hW hW0 hr hC hCR hcu₁ hcu₂ hfrC hα₁D hα₂D hα₁K hα₂K
      hx0 hb₁c hb₂c hb₁i hb₂i hb₁0 hb₂0 hb₁1 hb₂1 hb₁H hb₂H (fun w hw => by
        rcases psiArms_inter hb₁0 hb₂0 hb₁1 hb₂1 hb₁H hb₂H hdisj hw.1 hw.2 with h' | ⟨h1, -⟩
        · exact Or.inr h'
        · exact Or.inl h1) hpq₁ rfl hb₁img hb₂img hra hab.le hδp hgap hunv₁ hunv₂
      (by rcases hga with (h1 | h1) | h1; exacts [Or.inl h1, Or.inl h1, Or.inr h1]) hb)
  · obtain ⟨hlt, hneg⟩ := psiMap_ofReal_lt hpq₂ hq
    have h : IsArcPairInf (-(q₂ - p)⁻¹) (-(q₁ - p)⁻¹) b₂ b₁ :=
      ⟨hlt, hneg, hb₂c, hb₁c, hb₂i, hb₁i, hb₂0, hb₁0, hb₂1, hb₁1, hb₂H, hb₁H, fun w hw => by
        rcases psiArms_inter hb₁0 hb₂0 hb₁1 hb₂1 hb₁H hb₂H hdisj hw.2 hw.1 with h' | ⟨h1, h2⟩
        · exact h'
        · exact absurd (ofReal_injective (h2.symm.trans h1)) hlt.ne⟩
    exact hfin (ownFuture_eq_of_psiArms hη hW hW0 hr hC hCR hcu₂ hcu₁ (by rw [hfrC, union_comm])
      hα₂D hα₁D hα₂K hα₁K h hpq₁ rfl rfl hb₂img hb₁img hra hab hδp hgap hunv₂ hunv₁
      (by rcases hga with (h1 | h1) | h1; exacts [Or.inl (Or.inr h1), Or.inl (Or.inl h1),
        Or.inr h1]) hb)

end InteractingSLE.Sec6
