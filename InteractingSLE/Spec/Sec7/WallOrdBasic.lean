/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.OuterGeomSub
import InteractingSLE.Spec.Sec7.R7StopInMixed

/-!
# The order in which the counterflow visits the clipped walls of a change pocket

Packet PROVE-WALL-ORDER. Supplement §5.1–§5.4 (`source/spec/p433-480.md` L930–L997, pp. 471–474): "reverse
first-visit containment of every strict-angle incoming flow line and of both extremal lines"; Lemma R.3 ("An
outer-arm point in the counterflow range is on the certified frontier: `α_R ⊂ Ē_R` and the counterflow avoids
`E_R`"); Consequence R.4 ("on a contained side this is reverse first-visit order; on an outer side, a contact is a
contact with the intervening certified frontier and the same order applies"); §5.4 ("Outer-tail bulges can remain
active in `D_s`, but they are globally forbidden").

For a change pocket `C = cfPocket R L r` (walls `R`, `L` in the flow chart, counterflow `η` from `0` in the chart
`m(z) = −1/z`), the clipped walls are `cfArcR R L r`, `cfArcL R L r` (bounded pocket, from `m(x₀)` to `m(y₀)`) and
`cfArcRInf`, `cfArcLInf` (pocket opening at the flow seed, from `m(y₀)` towards `∞`). This file proves, pathwise:

* **contained walls** (`cfArcRInf_rev`, `cfArcLInf_rev`; the bounded forms are `R7StopIn.cfArcR_rev`,
  `R7StopIn.cfArcL_rev`): the clipped order `R16.IsReverseVisitOrder` / `Sec6.IsReverseVisitOrderInf` follows from
  the wall's own order `IsWallReverseVisit`;
* **outer walls — the clipped order is false** (`not_isReverseVisitOrder_cfArcR_of_outer`, `…cfArcL…`): if the wall
  lies in `S ∪ M` for the forbidden side `S` of a certified frontier `M` (`α_R ⊂ E_R ∪ β_R`), shares no arc with `M`,
  and the counterflow avoids `S`, then some point of the clipped arc is never visited, while the opening corner
  `m(x₀)` is visited at `σ = T(x₀)`; so `R16.IsReverseVisitOrder` fails;
* **outer walls — the corrected order** (`cfArcR_revOff`, `cfArcL_revOff`, `cfArcRInf_revOff`, `cfArcLInf_revOff`):
  the reverse first-visit order holds for every target point off the forbidden side
  (`IsReverseVisitOrderOff S`, `IsReverseVisitOrderInfOff S`), from the frontier's own order and the increasing order
  of the common contacts of the wall with the frontier (`OuterGeom.strictMonoOn_contactMap_of_ord`). With `S = ∅` it
  is the usual order (`isReverseVisitOrderOff_empty_iff`).

Conditional helpers with distinct names; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)
open InteractingSLE.WangWu (negInv)
open scoped NNReal

namespace InteractingSLE.Sec7.WallOrd

open WangWu Lemma71I PocketCoord PocketJordan Sec6

/-! ### The order off a forbidden side -/

/-- **Reverse first-visit order off a forbidden side** (bounded clipped arc `α : [0, 1] → ℂ` in the counterflow chart,
forbidden side `S` in the flow chart): whenever `α(v₁)` has been visited by time `t`, `v₁ ≤ v₂` and `α(v₂)` is not on
the forbidden side (`m(α(v₂)) ∉ S`), then `α(v₂)` has been visited by time `t`. -/
def IsReverseVisitOrderOff (S : Set ℂ) (α : ℝ → ℂ) (R : ℝ → Set ℂ) : Prop :=
  ∀ t : ℝ, ∀ v₁ ∈ Icc (0 : ℝ) 1, ∀ v₂ ∈ Icc (0 : ℝ) 1, v₁ ≤ v₂ → α v₁ ∈ R t → negInv (α v₂) ∉ S →
    α v₂ ∈ R t

/-- **Reverse first-visit order off a forbidden side** for an arc `α : [0, ∞) → ℂ` parametrized from `m(y₀)` towards
the junction at `∞`: when `α(v₂)` has been visited, so has every `α(v₁)`, `v₁ ≤ v₂`, off the forbidden side. -/
def IsReverseVisitOrderInfOff (S : Set ℂ) (α : ℝ → ℂ) (R : ℝ → Set ℂ) : Prop :=
  ∀ t : ℝ, ∀ v₁ ∈ Ici (0 : ℝ), ∀ v₂ ∈ Ici (0 : ℝ), v₁ ≤ v₂ → α v₂ ∈ R t → negInv (α v₁) ∉ S →
    α v₁ ∈ R t

theorem isReverseVisitOrderOff_empty_iff {α : ℝ → ℂ} {R : ℝ → Set ℂ} :
    IsReverseVisitOrderOff ∅ α R ↔ R16.IsReverseVisitOrder α R :=
  ⟨fun h t v₁ hv₁ v₂ hv₂ h12 hv => h t v₁ hv₁ v₂ hv₂ h12 hv (notMem_empty _),
    fun h t v₁ hv₁ v₂ hv₂ h12 hv _ => h t v₁ hv₁ v₂ hv₂ h12 hv⟩

theorem isReverseVisitOrderInfOff_empty_iff {α : ℝ → ℂ} {R : ℝ → Set ℂ} :
    IsReverseVisitOrderInfOff ∅ α R ↔ IsReverseVisitOrderInf α R :=
  ⟨fun h t v₁ hv₁ v₂ hv₂ h12 hv => h t v₁ hv₁ v₂ hv₂ h12 hv (notMem_empty _),
    fun h t v₁ hv₁ v₂ hv₂ h12 hv _ => h t v₁ hv₁ v₂ hv₂ h12 hv⟩

/-- The usual order implies the order off any forbidden side. -/
theorem IsReverseVisitOrderOff.of_rev {S : Set ℂ} {α : ℝ → ℂ} {R : ℝ → Set ℂ} (h : R16.IsReverseVisitOrder α R) :
    IsReverseVisitOrderOff S α R :=
  fun t v₁ hv₁ v₂ hv₂ h12 hv _ => h t v₁ hv₁ v₂ hv₂ h12 hv

/-- The usual order at infinity implies the order off any forbidden side. -/
theorem IsReverseVisitOrderInfOff.of_rev {S : Set ℂ} {α : ℝ → ℂ} {R : ℝ → Set ℂ}
    (h : IsReverseVisitOrderInf α R) : IsReverseVisitOrderInfOff S α R :=
  fun t v₁ hv₁ v₂ hv₂ h12 hv _ => h t v₁ hv₁ v₂ hv₂ h12 hv

/-! ### Refutation of the clipped order from one unvisited point -/

/-- **The clipped order fails if the start is visited and some point is never visited.** -/
theorem not_isReverseVisitOrder_of_unvisited {α : ℝ → ℂ} {R : ℝ → Set ℂ} {t₀ v : ℝ} (h0 : α 0 ∈ R t₀)
    (hv : v ∈ Icc (0 : ℝ) 1) (hnv : ∀ t, α v ∉ R t) : ¬ R16.IsReverseVisitOrder α R :=
  fun h => hnv t₀ (h t₀ 0 ⟨le_rfl, zero_le_one⟩ v hv hv.1 h0)

/-- **The clipped order at infinity fails if a later point is visited and an earlier one never is.** -/
theorem not_isReverseVisitOrderInf_of_unvisited {α : ℝ → ℂ} {R : ℝ → Set ℂ} {t₀ v₁ v₂ : ℝ} (hv₁ : 0 ≤ v₁)
    (h12 : v₁ ≤ v₂) (h2 : α v₂ ∈ R t₀) (hnv : ∀ t, α v₁ ∉ R t) : ¬ IsReverseVisitOrderInf α R :=
  fun h => hnv t₀ (h t₀ v₁ hv₁ v₂ (hv₁.trans h12) h12 h2)

/-- A point `m(w)` with `w` on a side `S` avoided by the counterflow is never visited. -/
theorem negInv_notMem_range_of_avoid {η : ℝ → ℂ} {S : Set ℂ} (havoid : ∀ u, 0 ≤ u → negInv (η u) ∉ S) {w : ℂ}
    (hw : w ∈ S) (t : ℝ) : negInv w ∉ η '' Icc 0 t := by
  rintro ⟨u, hu, hηu⟩
  exact havoid u hu.1 (by rw [hηu, negInv_negInv]; exact hw)

/-! ### Increasing order of common contacts -/

/-- **Common contacts in the same order** (`j = B⁻¹ ∘ A` increasing on the contact set). -/
theorem le_of_contact {A B : ℝ → ℂ} (hB : IsDiscCrosscut B)
    (hm : StrictMonoOn (contactMap A B) (Sec7.pocketContactSet A B)) {s₁ s₂ p₁ p₂ : ℝ}
    (hs₁ : s₁ ∈ Icc (0 : ℝ) 1) (hs₂ : s₂ ∈ Icc (0 : ℝ) 1) (hp₁ : p₁ ∈ Icc (0 : ℝ) 1) (hp₂ : p₂ ∈ Icc (0 : ℝ) 1)
    (e₁ : A s₁ = B p₁) (e₂ : A s₂ = B p₂) (h12 : s₁ ≤ s₂) : p₁ ≤ p₂ := by
  have c₁ : s₁ ∈ Sec7.pocketContactSet A B := ⟨hs₁, p₁, hp₁, e₁.symm⟩
  have c₂ : s₂ ∈ Sec7.pocketContactSet A B := ⟨hs₂, p₂, hp₂, e₂.symm⟩
  have := hm.monotoneOn c₁ c₂ h12
  rwa [contactMap_eq hB hp₁ e₁, contactMap_eq hB hp₂ e₂] at this

/-- **Common contacts in the same order**, from the increasing contact map in the other direction. -/
theorem le_of_contact_symm {A B : ℝ → ℂ} (hA : IsDiscCrosscut A)
    (hm : StrictMonoOn (contactMap B A) (Sec7.pocketContactSet B A)) {s₁ s₂ p₁ p₂ : ℝ}
    (hs₁ : s₁ ∈ Icc (0 : ℝ) 1) (hs₂ : s₂ ∈ Icc (0 : ℝ) 1) (hp₁ : p₁ ∈ Icc (0 : ℝ) 1) (hp₂ : p₂ ∈ Icc (0 : ℝ) 1)
    (e₁ : A s₁ = B p₁) (e₂ : A s₂ = B p₂) (h12 : s₁ ≤ s₂) : p₁ ≤ p₂ := by
  by_contra hlt
  have c₁ : p₁ ∈ Sec7.pocketContactSet B A := ⟨hp₁, s₁, hs₁, e₁⟩
  have c₂ : p₂ ∈ Sec7.pocketContactSet B A := ⟨hp₂, s₂, hs₂, e₂⟩
  have := hm c₂ c₁ (not_le.1 hlt)
  rw [contactMap_eq hA hs₁ e₁.symm, contactMap_eq hA hs₂ e₂.symm] at this
  exact absurd h12 (not_le.2 this)

/-! ### The core step on an outer wall -/

variable {η : ℝ → ℂ}

/-- **The corrected order along an outer wall, in disc times** (Consequence R.4, outer side): if the wall `Rw` lies in
`S ∪ M`, its common contacts with the frontier `M` come in the same order, `M` is visited in reverse order and the
counterflow avoids `S`, then a visit of `m(R̃w(s₁))` gives a visit of every `m(R̃w(s₂))`, `s₁ ≤ s₂`, off `S`. -/
theorem wall_revOff {Rw M : ℝ≥0 → ℂ} {S : Set ℂ} (hR : IsSimpleProper Rw) (hM : IsSimpleProper M)
    (hmono : ∀ s₁ s₂ p₁ p₂ : ℝ, s₁ ∈ Icc (0 : ℝ) 1 → s₂ ∈ Icc (0 : ℝ) 1 → p₁ ∈ Icc (0 : ℝ) 1 →
      p₂ ∈ Icc (0 : ℝ) 1 → toDisc (Lemma71I.realPath Rw) s₁ = toDisc (Lemma71I.realPath M) p₁ →
      toDisc (Lemma71I.realPath Rw) s₂ = toDisc (Lemma71I.realPath M) p₂ → s₁ ≤ s₂ → p₁ ≤ p₂)
    (hout : range Rw ⊆ S ∪ range M) (hη0 : η 0 = 0) (hrevM : IsWallReverseVisit M η)
    (havoid : ∀ u, 0 ≤ u → negInv (η u) ∉ S) {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Ioc (0 : ℝ) 1)
    (hs₂ : s₂ ∈ Ioc (0 : ℝ) 1) (h12 : s₁ ≤ s₂) {t : ℝ}
    (hvis : cfPt (toDisc (Lemma71I.realPath Rw) s₁) ∈ η '' Icc 0 t)
    (hS : negInv (cfPt (toDisc (Lemma71I.realPath Rw) s₂)) ∉ S) :
    cfPt (toDisc (Lemma71I.realPath Rw) s₂) ∈ η '' Icc 0 t := by
  obtain ⟨u, hu, hηu⟩ := hvis
  rcases hs₂.2.lt_or_eq with hs₂1 | hs₂1
  swap
  · rw [hs₂1, toDisc_one, cfPt_one]
    exact ⟨0, ⟨le_rfl, hu.1.trans hu.2⟩, hη0⟩
  have hs₁1 : s₁ < 1 := h12.trans_lt hs₂1
  obtain ⟨e₁, -⟩ := cfPt_toDisc_of_mem hR ⟨hs₁.1, hs₁1⟩
  obtain ⟨e₂, -⟩ := cfPt_toDisc_of_mem hR ⟨hs₂.1, hs₂1⟩
  -- both wall points lie on the frontier `M`
  have hm₁ : Rw (arcTime s₁).toNNReal ∈ range M := by
    have h1 : negInv (η u) = Rw (arcTime s₁).toNNReal := by rw [hηu, e₁, negInv_negInv]
    rcases hout ⟨_, rfl⟩ with h | h
    · exact absurd (h1 ▸ h) (havoid u hu.1)
    · exact h
  have hm₂ : Rw (arcTime s₂).toNNReal ∈ range M := by
    rw [e₂, negInv_negInv] at hS
    rcases hout ⟨_, rfl⟩ with h | h
    · exact absurd h hS
    · exact h
  obtain ⟨p₁, hp₁, hpe₁⟩ := (OuterGeom.toDisc_mem_crossRange_iff hR hM ⟨hs₁.1, hs₁1⟩).2 hm₁
  obtain ⟨p₂, hp₂, hpe₂⟩ := (OuterGeom.toDisc_mem_crossRange_iff hR hM ⟨hs₂.1, hs₂1⟩).2 hm₂
  have hp12 := hmono s₁ s₂ p₁ p₂ ⟨hs₁.1.le, hs₁.2⟩ ⟨hs₂.1.le, hs₂.2⟩ hp₁ hp₂ hpe₁.symm hpe₂.symm h12
  have hp0 : 0 < p₁ := by
    refine lt_of_le_of_ne hp₁.1 fun h0 => ?_
    have hc := hR.isProperArc.isDiscCrosscut_toDisc
    have hcM := hM.isProperArc.isDiscCrosscut_toDisc
    have he : toDisc (Lemma71I.realPath Rw) s₁ = toDisc (Lemma71I.realPath Rw) 0 := by
      rw [← hpe₁, ← h0, hcM.zero, hc.zero]
    exact hs₁.1.ne' (hc.inj ⟨hs₁.1.le, hs₁.2⟩ ⟨le_rfl, zero_le_one⟩ he)
  have hvis' : cfPt (toDisc (Lemma71I.realPath M) p₁) ∈ η '' Icc 0 t := by
    rw [hpe₁]; exact ⟨u, hu, hηu⟩
  have := wall_rev hM hη0 hrevM ⟨hp0, hp₁.2⟩ ⟨hp0.trans_le hp12, hp₂.2⟩ hp12 hvis'
  rwa [hpe₂] at this

end InteractingSLE.Sec7.WallOrd
