/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux40Full
import InteractingSLE.Spec.Sec6.Aux39InfGap

/-!
# The reverse-contained pocket with its junction at the original target: (JP1), the chart, gaps

Specification §6.2, **Aux.** lemmas 34, 36, 37, 39–41 (`source/spec/p145-192.md` L869–L905,
`source/spec/p193-240.md` L36–L265) in the case where the pocket junction `x₀` is the original
target of the counterflow ("If `x₀` is the original target, its image is instead on the real
circle", p. 195; "If `σ = ∞`, reverse containment and transience imply that every incoming point
strictly after `x₀` is first visited at a finite time", p. 203), with ruling R41's note
(`source/external/AstraIG1/ig1_ztip_elimination.txt` §1.1–1.2, Propositions 1.5–1.6; the junction
at infinity: "the two proper incoming arms give the same separation directly").

In the half-plane chart of the counterflow `η` the original target is `∞`. The pocket `C ⊆ ℍ` is
open and connected with `∂C = α₁([0, ∞)) ∪ α₂([0, ∞))`, two proper simple paths in `ℍ` (except
possibly at `y₀ = α_i(0)`, an interior point or the original seed `0`), starting at the common
point `y₀` and tending to `∞` (the junction `x₀`), with disjoint open parts. **Orientation:** the
parameter `v` runs from `y₀` towards `x₀ = ∞`, against the flow-line time, so reverse first-visit
order says that the visited parameters at time `t` form an *initial* segment `[0, u(t)]`, with
`u(t) = max {v ≥ 0 : α(v) ∈ R_t}` (`lastVisit`). Both paths lie in the completed counterflow range
(Aux. lemma 34: "both paths are contained in the completed counterflow range and their points are
first visited in reverse path order"); `τ = T(y₀)`. The first visit `σ = T(x₀)` is `∞`.

Main results (namespace `IsReversePocketInf`):

* `mem_Ioi_of_mem` (**(JP1)**): the trace visits `C` only after `τ`;
* `chart` (**(JP2)** and the chart at `r ≥ τ`): `α([0, u(r)])` is visited, `α((u(r), ∞)) ⊆ D_r`;
* `lastVisit_eq_of_fresh` (**Lemma 1.4** for these arms): a fresh visit is the current attachment;
* `gap_eq`, `gap_eq_seed` (**Propositions 1.5–1.6 at infinity**), under **Aux. lemma 37's
  conclusion** `AttachmentConstancyInf` (the named input, as for the finite junction).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec6

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-! ### Last-visit parameters of a proper arm -/

/-- The **attachment parameter** of a proper incoming arm `α : [0, ∞) → ℂ` (parametrized from
`y₀` towards the junction at `∞`) at time `t`: `u(t) = max {v ≥ 0 : α(v) ∈ R_t}`. -/
def lastVisit (R : ℝ → Set ℂ) (α : ℝ → ℂ) (t : ℝ) : ℝ := sSup {v ∈ Ici (0 : ℝ) | α v ∈ R t}

/-- **Reverse first-visit order** for an arm parametrized from `y₀` towards `∞`: when a point of
`α` has been visited, so has every point between it and `y₀`. -/
def IsReverseVisitOrderInf (α : ℝ → ℂ) (R : ℝ → Set ℂ) : Prop :=
  ∀ t : ℝ, ∀ v₁ ∈ Ici (0 : ℝ), ∀ v₂ ∈ Ici (0 : ℝ), v₁ ≤ v₂ → α v₂ ∈ R t → α v₁ ∈ R t

section LastVisit

variable {R : ℝ → Set ℂ} {α : ℝ → ℂ}

/-- A proper arm meets a bounded set in a bounded parameter set. -/
theorem lastVisit_set_bddAbove (hα : Tendsto (fun v => ‖α v‖) atTop atTop) {t : ℝ}
    (hR : IsBounded (R t)) : BddAbove {v ∈ Ici (0 : ℝ) | α v ∈ R t} := by
  obtain ⟨M, hM⟩ := hR.exists_norm_le
  obtain ⟨V, hV⟩ := eventually_atTop.1 (hα.eventually (eventually_gt_atTop M))
  refine ⟨V, fun v hv => ?_⟩
  by_contra h
  push Not at h
  exact absurd (hM _ hv.2) (not_le.2 (hV v h.le))

theorem le_lastVisit (hα : Tendsto (fun v => ‖α v‖) atTop atTop) {t v : ℝ}
    (hR : IsBounded (R t)) (hv : v ∈ Ici (0 : ℝ)) (hvR : α v ∈ R t) : v ≤ lastVisit R α t :=
  le_csSup (lastVisit_set_bddAbove hα hR) ⟨hv, hvR⟩

/-- The maximum is attained (closed visited sets, continuous arm). -/
theorem lastVisit_mem (hαc : ContinuousOn α (Ici 0)) (hα : Tendsto (fun v => ‖α v‖) atTop atTop)
    {t : ℝ} (hR : IsCompact (R t)) (hne : ∃ v ∈ Ici (0 : ℝ), α v ∈ R t) :
    lastVisit R α t ∈ Ici (0 : ℝ) ∧ α (lastVisit R α t) ∈ R t := by
  have hcl : IsClosed {v ∈ Ici (0 : ℝ) | α v ∈ R t} :=
    hαc.preimage_isClosed_of_isClosed isClosed_Ici hR.isClosed
  obtain ⟨v, hv⟩ := hne
  exact hcl.csSup_mem ⟨v, hv⟩ (lastVisit_set_bddAbove hα hR.isBounded)

/-- Visited sets increase, so attachment parameters increase. -/
theorem lastVisit_mono (hα : Tendsto (fun v => ‖α v‖) atTop atTop) (hRm : Monotone R)
    {s t : ℝ} (hst : s ≤ t) (hR : IsBounded (R t)) (hne : ∃ v ∈ Ici (0 : ℝ), α v ∈ R s) :
    lastVisit R α s ≤ lastVisit R α t := by
  obtain ⟨v, hv⟩ := hne
  exact csSup_le_csSup (lastVisit_set_bddAbove hα hR) ⟨v, hv⟩ fun w hw => ⟨hw.1, hRm hst hw.2⟩

/-- **Lemma 1.2 (3) for proper arms**: if `α(u(a))` was already visited by `r ≤ a`, then
`u(r) = u(a)`. -/
theorem lastVisit_eq_of_visited (hαc : ContinuousOn α (Ici 0))
    (hα : Tendsto (fun v => ‖α v‖) atTop atTop) (hRm : Monotone R) {r a : ℝ} (hra : r ≤ a)
    (hRa : IsCompact (R a)) (hRr : IsBounded (R r)) (hne : ∃ v ∈ Ici (0 : ℝ), α v ∈ R a)
    (hvis : α (lastVisit R α a) ∈ R r) : lastVisit R α r = lastVisit R α a := by
  have hmem := lastVisit_mem hαc hα hRa hne
  exact le_antisymm (lastVisit_mono hα hRm hra hRa.isBounded ⟨_, hmem.1, hvis⟩)
    (le_lastVisit hα hRr hmem.1 hvis)

end LastVisit

/-- **Lemma 1.4 (first part) for proper arms**: a point `p = η(a) = α(v)` of an injective arm in
reverse first-visit order, visited for the first time at `a`, is the current attachment:
`u(a) = v`. -/
theorem lastVisit_eq_of_fresh {α : ℝ → ℂ} (hαc : ContinuousOn α (Ici 0)) (hαi : InjOn α (Ici 0))
    (hα : Tendsto (fun v => ‖α v‖) atTop atTop) (hη : ContinuousOn η (Ici 0))
    (hrev : IsReverseVisitOrderInf α fun t => η '' Icc 0 t) {a v : ℝ} (ha : 0 ≤ a)
    (hv : v ∈ Ici (0 : ℝ)) (hp : η a = α v) (hfresh : η a ∉ η '' Ico 0 a) :
    lastVisit (fun t => η '' Icc 0 t) α a = v := by
  have hRa : IsCompact (η '' Icc 0 a) :=
    isCompact_Icc.image_of_continuousOn (hη.mono fun _ h => h.1)
  have hvR : α v ∈ η '' Icc 0 a := ⟨a, ⟨ha, le_rfl⟩, hp⟩
  have hmem := lastVisit_mem (R := fun t => η '' Icc 0 t) hαc hα hRa ⟨v, hv, hvR⟩
  set u := lastVisit (fun t => η '' Icc 0 t) α a with hudef
  have hvu : v ≤ u := le_lastVisit (R := fun t => η '' Icc 0 t) hα hRa.isBounded hv hvR
  refine le_antisymm ?_ hvu
  by_contra hlt
  push Not at hlt
  obtain ⟨t, ht, hte⟩ := hmem.2
  have hne : η t ≠ η a := by
    rw [hte, hp]; exact fun h => hlt.ne' (hαi hmem.1 hv h)
  have hta : t < a := lt_of_le_of_ne ht.2 fun h => hne (by rw [h])
  obtain ⟨t', ht', ht'e⟩ := hrev t v hv u hmem.1 hlt.le ⟨t, ⟨ht.1, le_rfl⟩, hte⟩
  exact hfresh ⟨t', ⟨ht'.1, ht'.2.trans_lt hta⟩, ht'e.trans hp.symm⟩

/-! ### The pocket hypotheses -/

/-- **The pathwise hypotheses of Aux. lemmas 39–41 with the junction at the original target**
(Specification pp. 189–206; Aux. lemma 34's configuration, `x₀` the original target `∞`): `C` is a
connected open subset of `ℍ` (a complementary component of the two flow lines in the ambient
domain) bounded by two proper simple paths `α_i : [0, ∞) → ℂ` from the common point `y₀ = α_i(0)`
(an interior point or the original seed `0`) to `∞`, in `ℍ` after `y₀`, with disjoint open parts;
both paths lie in the completed counterflow range and are first visited in reverse order;
`τ = T(y₀)`. -/
structure IsReversePocketInf (W : ℝ → ℝ) (η : ℝ → ℂ) (C : Set ℂ) (α₁ α₂ : ℝ → ℂ) (τ : ℝ) :
    Prop where
  trace : IsLoewnerTrace W η
  continuous_W : Continuous W
  W_zero : W 0 = 0
  isOpen : IsOpen C
  isConnected : IsConnected C
  subset_H : C ⊆ H
  frontier_eq : frontier C = α₁ '' Ici 0 ∪ α₂ '' Ici 0
  cont₁ : ContinuousOn α₁ (Ici 0)
  cont₂ : ContinuousOn α₂ (Ici 0)
  inj₁ : InjOn α₁ (Ici 0)
  inj₂ : InjOn α₂ (Ici 0)
  tendsto₁ : Tendsto (fun v => ‖α₁ v‖) atTop atTop
  tendsto₂ : Tendsto (fun v => ‖α₂ v‖) atTop atTop
  seed : α₂ 0 = α₁ 0
  sides : ∀ v ∈ Ioi (0 : ℝ), ∀ v' ∈ Ioi (0 : ℝ), α₁ v ≠ α₂ v'
  mem_H₁ : ∀ v ∈ Ioi (0 : ℝ), α₁ v ∈ H
  mem_H₂ : ∀ v ∈ Ioi (0 : ℝ), α₂ v ∈ H
  mem_y : α₁ 0 ∈ H ∨ α₁ 0 = 0
  rev₁ : IsReverseVisitOrderInf α₁ fun t => η '' Icc 0 t
  rev₂ : IsReverseVisitOrderInf α₂ fun t => η '' Icc 0 t
  visited₁ : ∀ v ∈ Ici (0 : ℝ), ∃ t, α₁ v ∈ η '' Icc 0 t
  visited₂ : ∀ v ∈ Ici (0 : ℝ), ∃ t, α₂ v ∈ η '' Icc 0 t
  nonneg : 0 ≤ τ
  first_y : η τ = α₁ 0
  fresh_y : α₁ 0 ∉ η '' Ico 0 τ

/-- **Aux. lemma 37's conclusion at infinity** (the named input of these files): the attachment
parameters `u_i(t) = max {v : α_i(v) ∈ R_t}` are constant on every interval `[a, b] ⊆ [τ, ∞)` on
which the trace avoids `C` (Specification p. 197, with `σ = T(x₀) = ∞`). -/
def AttachmentConstancyInf (η : ℝ → ℂ) (C : Set ℂ) (α₁ α₂ : ℝ → ℂ) (τ : ℝ) : Prop :=
  ∀ a b : ℝ, τ ≤ a → a ≤ b → (∀ t ∈ Icc a b, η t ∉ C) →
    lastVisit (fun t => η '' Icc 0 t) α₁ b = lastVisit (fun t => η '' Icc 0 t) α₁ a ∧
      lastVisit (fun t => η '' Icc 0 t) α₂ b = lastVisit (fun t => η '' Icc 0 t) α₂ a

/-! ### The gap lemma at infinity with a supplied gate -/

/-- **Propositions 1.5–1.6 at infinity with a supplied gate**: `ownFuture_gap_eq_of_pocket_inf`
with its fresh start replaced by the conclusion it uses — at `r = a`, one of the lifted unvisited
prefixes ends at the real point `0 = δ_a(a)` (for a fresh interior tip by the fresh-tip lemma; at
the original seed `a = 0` because `R_0 = {0}`). -/
theorem ownFuture_gap_eq_of_pocket_inf_gate (hη : IsLoewnerTrace W η) (hW : Continuous W)
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
      (r = a ∧ ((∀ q : ℝ, trMap W 0 r q = α₁ u₁ → q = 0) ∨
        (∀ q : ℝ, trMap W 0 r q = α₂ u₂ → q = 0))))
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
    rcases hstart with h1 | ⟨hra', hg⟩
    · exact Or.inr h1
    · subst hra'
      have hδa : trMap W r r 0 = 0 := YuanSimpleApprox.trMap_self hW r zero_mem_Hbar
      left
      rcases hg with h1 | h1
      · left; rw [hδa, h1 q₁ hq₁, ofReal_zero]
      · right; rw [hδa, h1 q₂ hq₂, ofReal_zero]
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


namespace IsReversePocketInf

variable {C : Set ℂ} {α₁ α₂ : ℝ → ℂ} {τ : ℝ}

/-- The data of one incoming side, uniformly for both sides. -/
theorem arm (hP : IsReversePocketInf W η C α₁ α₂ τ) {α : ℝ → ℂ} (hα : α = α₁ ∨ α = α₂) :
    ContinuousOn α (Ici 0) ∧ InjOn α (Ici 0) ∧ Tendsto (fun v => ‖α v‖) atTop atTop ∧
      α 0 = α₁ 0 ∧ (∀ v ∈ Ioi (0 : ℝ), α v ∈ H) ∧
      IsReverseVisitOrderInf α (fun t => η '' Icc 0 t) ∧
      ∀ v ∈ Ici (0 : ℝ), ∃ t, α v ∈ η '' Icc 0 t := by
  rcases hα with rfl | rfl
  · exact ⟨hP.cont₁, hP.inj₁, hP.tendsto₁, rfl, hP.mem_H₁, hP.rev₁, hP.visited₁⟩
  · exact ⟨hP.cont₂, hP.inj₂, hP.tendsto₂, hP.seed, hP.mem_H₂, hP.rev₂, hP.visited₂⟩

theorem isCompact_range (hP : IsReversePocketInf W η C α₁ α₂ τ) (t : ℝ) :
    IsCompact (η '' Icc 0 t) :=
  isCompact_Icc.image_of_continuousOn (hP.trace.2.1.mono fun _ hs => hs.1)

/-- A visited point of a side forces `y₀` to be visited (reverse order). -/
theorem y_mem_of_mem (hP : IsReversePocketInf W η C α₁ α₂ τ) {t : ℝ} {α : ℝ → ℂ}
    (hα : α = α₁ ∨ α = α₂) {v : ℝ} (hv : v ∈ Ici (0 : ℝ)) (h : α v ∈ η '' Icc 0 t) :
    α₁ 0 ∈ η '' Icc 0 t := by
  obtain ⟨-, -, -, h0, -, hrev, -⟩ := hP.arm hα
  exact h0 ▸ hrev t 0 (mem_Ici.2 le_rfl) v hv hv h

theorem y_mem_of_mem_frontier (hP : IsReversePocketInf W η C α₁ α₂ τ) {t : ℝ} {z : ℂ}
    (hz : z ∈ frontier C) (hzt : z ∈ η '' Icc 0 t) : α₁ 0 ∈ η '' Icc 0 t := by
  rw [hP.frontier_eq] at hz
  rcases hz with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
  exacts [hP.y_mem_of_mem (Or.inl rfl) hv hzt, hP.y_mem_of_mem (Or.inr rfl) hv hzt]

theorem τ_le (hP : IsReversePocketInf W η C α₁ α₂ τ) {t : ℝ} (h : α₁ 0 ∈ η '' Icc 0 t) :
    τ ≤ t := le_of_fresh hP.fresh_y h

theorem y_mem (hP : IsReversePocketInf W η C α₁ α₂ τ) {t : ℝ} (ht : τ ≤ t) :
    α₁ 0 ∈ η '' Icc 0 t := ⟨τ, ⟨hP.nonneg, ht⟩, hP.first_y⟩

/-- A boundary point of the pocket other than `y₀` lies in `ℍ`. -/
theorem mem_H_of_mem_frontier (hP : IsReversePocketInf W η C α₁ α₂ τ) {z : ℂ}
    (hz : z ∈ frontier C) (hzy : z ≠ α₁ 0) : z ∈ H := by
  rw [hP.frontier_eq] at hz
  rcases hz with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
  · rcases eq_or_lt_of_le (mem_Ici.1 hv) with h | h
    · exact absurd (by rw [← h]) hzy
    · exact hP.mem_H₁ v h
  · rcases eq_or_lt_of_le (mem_Ici.1 hv) with h | h
    · exact absurd (by rw [← h, hP.seed]) hzy
    · exact hP.mem_H₂ v h

/-- The only real point of `C̄` is (possibly) `y₀`; in particular far real points avoid `C̄`. -/
theorem farReal (hP : IsReversePocketInf W η C α₁ α₂ τ) :
    ∃ M, ∀ y : ℝ, M ≤ |y| → (y : ℂ) ∉ closure C := by
  refine ⟨‖α₁ 0‖ + 1, fun y hy hcl => ?_⟩
  have hyC : (y : ℂ) ∉ C := fun h => not_mem_H_ofReal y (hP.subset_H h)
  have hfr : (y : ℂ) ∈ frontier C := ⟨hcl, by rwa [hP.isOpen.interior_eq]⟩
  by_cases hy0 : (y : ℂ) = α₁ 0
  · have : ‖(y : ℂ)‖ = |y| := by rw [norm_real, Real.norm_eq_abs]
    rw [← hy0] at hy
    linarith
  · exact not_mem_H_ofReal y (hP.mem_H_of_mem_frontier hfr hy0)

/-- The pocket is unbounded (its boundary contains the proper arm `α₁`). -/
theorem not_isBounded (hP : IsReversePocketInf W η C α₁ α₂ τ) : ¬ IsBounded C := by
  intro hb
  have hfb : IsBounded (frontier C) := hb.closure.subset frontier_subset_closure
  obtain ⟨M, hM⟩ := hfb.exists_norm_le
  obtain ⟨v, hv⟩ := ((hP.tendsto₁.eventually (eventually_gt_atTop M)).and
    (eventually_ge_atTop 0)).exists
  refine absurd (hM _ ?_) (not_le.2 hv.1)
  rw [hP.frontier_eq]; exact Or.inl ⟨v, hv.2, rfl⟩

/-- **(JP1) at infinity**: the trace visits `C` only after `τ = T(y₀)`. -/
theorem mem_Ioi_of_mem (hP : IsReversePocketInf W η C α₁ α₂ τ) {t : ℝ} (ht : 0 ≤ t)
    (htC : η t ∈ C) : τ < t := by
  have hη := hP.trace
  have hpre : IsPreconnected (η '' Icc 0 t) :=
    isPreconnected_Icc.image _ (hη.2.1.mono fun s hs => hs.1)
  obtain ⟨z, hzR, hzf⟩ : (η '' Icc 0 t ∩ frontier C).Nonempty := by
    by_contra hne
    have hsub := subset_of_isPreconnected_of_disjoint_frontier hpre hP.isOpen
      ⟨η t, ⟨t, ⟨ht, le_rfl⟩, rfl⟩, htC⟩ (Set.disjoint_iff_inter_eq_empty.2
        (Set.not_nonempty_iff_eq_empty.1 hne))
    have h0 := hP.subset_H (hsub ⟨0, ⟨le_rfl, ht⟩, rfl⟩)
    rw [hη.1] at h0
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h0)
  obtain ⟨t', ht', rfl⟩ := hzR
  have hτ := hP.τ_le (hP.y_mem_of_mem_frontier hzf ⟨t', ⟨ht'.1, le_rfl⟩, rfl⟩)
  refine lt_of_le_of_lt hτ (lt_of_le_of_ne ht'.2 fun h => ?_)
  rw [h] at hzf
  have := hzf.2
  rw [hP.isOpen.interior_eq] at this
  exact this htC

/-- A fresh visit to `∂C` at a positive time is a point of `ℍ`. -/
theorem mem_H_of_fresh (hP : IsReversePocketInf W η C α₁ α₂ τ) {a : ℝ} (ha0 : 0 < a)
    (hfr : η a ∈ frontier C) (hfresh : η a ∉ η '' Ico 0 a) : η a ∈ H := by
  by_cases hy : η a = α₁ 0
  · rcases hP.mem_y with h | h
    · rwa [hy]
    · exact absurd ⟨0, ⟨le_rfl, ha0⟩, by rw [hP.trace.1, hy, h]⟩ hfresh
  · exact hP.mem_H_of_mem_frontier hfr hy

/-- **(JP2) and the chart at `r ≥ τ`.** For each side `α`, with `u = u(r)` its attachment
parameter: `u ≥ 0`, the visited part `α([0, u])` is in `R_r` (hence not in `D_r`), and the open
prefix `α((u, ∞))` lies in `D_r`. -/
theorem chart (hP : IsReversePocketInf W η C α₁ α₂ τ) {r : ℝ} (hτr : τ ≤ r) {α : ℝ → ℂ}
    (hα : α = α₁ ∨ α = α₂) :
    0 ≤ lastVisit (fun t => η '' Icc 0 t) α r ∧
      (∀ v ∈ Icc 0 (lastVisit (fun t => η '' Icc 0 t) α r), α v ∈ η '' Icc 0 r) ∧
      (∀ v ∈ Icc 0 (lastVisit (fun t => η '' Icc 0 t) α r), α v ∉ H \ fwdHull W r) ∧
      (∀ v ∈ Ioi (lastVisit (fun t => η '' Icc 0 t) α r), α v ∈ H \ fwdHull W r) := by
  obtain ⟨hc, -, ht, h0, hH, hrev, -⟩ := hP.arm hα
  have hr0 : 0 ≤ r := hP.nonneg.trans hτr
  set u := lastVisit (fun t => η '' Icc 0 t) α r with hudef
  have hne : ∃ v ∈ Ici (0 : ℝ), α v ∈ η '' Icc 0 r := ⟨0, (mem_Ici.2 le_rfl), h0 ▸ hP.y_mem hτr⟩
  have hmem := lastVisit_mem (R := fun t => η '' Icc 0 t) hc ht (hP.isCompact_range r) hne
  have hvis : ∀ v ∈ Icc 0 u, α v ∈ η '' Icc 0 r := fun v hv =>
    hrev r v hv.1 u hmem.1 hv.2 hmem.2
  refine ⟨hmem.1, hvis, fun v hv => notMem_domain_of_mem_trace hP.trace hr0 (hvis v hv),
    fun v hv => ?_⟩
  have hu0 : (0 : ℝ) ≤ u := hmem.1
  refine subset_domain_of_not_isBounded hP.trace hr0 (S := α '' Ioi u)
    (isPreconnected_Ioi.image _ (hc.mono fun w hw => hu0.trans hw.le))
    (fun _ ⟨w, hw, h⟩ => h ▸ hH w (hu0.trans_lt hw)) ?_ ?_ ⟨v, hv, rfl⟩
  · refine Set.disjoint_left.2 ?_
    rintro _ ⟨w, hw, rfl⟩ hwR
    exact absurd (le_lastVisit (R := fun t => η '' Icc 0 t) ht (hP.isCompact_range r).isBounded
      (hu0.trans hw.le) hwR) (not_le.2 hw)
  · intro hb
    obtain ⟨M, hM⟩ := hb.exists_norm_le
    obtain ⟨w, hw⟩ := ((ht.eventually (eventually_gt_atTop M)).and
      (eventually_gt_atTop u)).exists
    exact absurd (hM _ ⟨w, hw.2, rfl⟩) (not_le.2 hw.1)

/-- **Lemma 1.4 (fresh boundary visit)** in the pocket at infinity: a fresh visit `η(a) ∈ ∂C` is
the current attachment of a side containing it. -/
theorem fresh_attach (hP : IsReversePocketInf W η C α₁ α₂ τ) {a : ℝ} (ha : 0 ≤ a)
    (haC : η a ∈ frontier C) (hfresh : η a ∉ η '' Ico 0 a) :
    η a = α₁ (lastVisit (fun t => η '' Icc 0 t) α₁ a) ∨
      η a = α₂ (lastVisit (fun t => η '' Icc 0 t) α₂ a) := by
  rw [hP.frontier_eq] at haC
  rcases haC with ⟨v, hv, hav⟩ | ⟨v, hv, hav⟩
  · left
    rw [lastVisit_eq_of_fresh hP.cont₁ hP.inj₁ hP.tendsto₁ hP.trace.2.1 hP.rev₁ ha hv hav.symm
      hfresh, hav]
  · right
    rw [lastVisit_eq_of_fresh hP.cont₂ hP.inj₂ hP.tendsto₂ hP.trace.2.1 hP.rev₂ ha hv hav.symm
      hfresh, hav]

/-- A limit of `C`-visits after `s ≥ 0` has its tip in `C̄`. -/
theorem mem_closure_of_mem_closure_visits (hP : IsReversePocketInf W η C α₁ α₂ τ) {s a : ℝ}
    (hs : 0 ≤ s) (ha : a ∈ closure {t | s < t ∧ η t ∈ C}) : η a ∈ closure C := by
  have hsub : {t | s < t ∧ η t ∈ C} ⊆ Ici 0 := fun t ht => hs.trans ht.1.le
  have ha0 : a ∈ Ici (0 : ℝ) := closure_minimal hsub isClosed_Ici ha
  have hc : ContinuousWithinAt η {t | s < t ∧ η t ∈ C} a := (hP.trace.2.1 a ha0).mono hsub
  exact closure_mono (image_subset_iff.2 fun t ht => ht.2) (hc.mem_closure_image ha)

/-- Under attachment constancy on a gap `[a, b]`, the open prefixes beyond the attachments at `a`
stay unvisited through `b`. -/
theorem notMem_prefix (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) {a b : ℝ} (hτa : τ ≤ a) (hab : a ≤ b)
    (hgap : ∀ t ∈ Icc a b, η t ∉ C) {α : ℝ → ℂ} (hα : α = α₁ ∨ α = α₂) :
    ∀ t ∈ Icc a b, ∀ v ∈ Ioi (lastVisit (fun t => η '' Icc 0 t) α a), η t ≠ α v := by
  intro t ht v hv h
  have hc : lastVisit (fun t => η '' Icc 0 t) α b = lastVisit (fun t => η '' Icc 0 t) α a := by
    rcases hα with rfl | rfl
    exacts [(hAC a b hτa hab hgap).1, (hAC a b hτa hab hgap).2]
  obtain ⟨-, -, htα, -⟩ := hP.arm hα
  have hu0 := (hP.chart hτa hα).1
  have hle := le_lastVisit (R := fun t => η '' Icc 0 t) htα (hP.isCompact_range b).isBounded
    (hu0.trans hv.le) ⟨t, ⟨(hP.nonneg.trans hτa).trans ht.1, ht.2⟩, h⟩
  rw [hc] at hle
  exact absurd hv (not_lt.2 hle)

theorem disjoint_prefixes (hP : IsReversePocketInf W η C α₁ α₂ τ) {u₁ u₂ : ℝ} (hu₁ : 0 ≤ u₁)
    (hu₂ : 0 ≤ u₂) : ∀ v ∈ Ioi u₁, ∀ v' ∈ Ioi u₂, α₁ v ≠ α₂ v' := fun v hv v' hv' =>
  hP.sides v (hu₁.trans_lt hv) v' (hu₂.trans_lt hv')

/-- **Propositions 1.5–1.6 for the pocket at infinity** (ruling R41's note, L233–L311; Specification
pp. 201–205, (GC1) and (RG2)). Let `[a, b] ⊆ [τ, ∞)` be a nondegenerate interval on which the trace
avoids `C`, whose left end is `τ` or a limit of `C`-visits after `s`, and whose right end is a
limit of later `C`-visits. Under Aux. lemma 37's attachment constancy, for every chart time
`0 ≤ s < a`: `δ_s(a) = δ_s(b)` and `η(a) = η(b)`. -/
theorem gap_eq (hP : IsReversePocketInf W η C α₁ α₂ τ) (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    {s a b : ℝ} (hs : 0 ≤ s) (hsa : s < a) (hτa : τ ≤ a) (hab : a < b)
    (hgap : ∀ t ∈ Icc a b, η t ∉ C) (ha : a = τ ∨ a ∈ closure {t | s < t ∧ η t ∈ C})
    (hb : b ∈ closure {t | a < t ∧ η t ∈ C}) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  have hη := hP.trace
  have hW := hP.continuous_W
  have hW0 := hP.W_zero
  have ha0 : 0 < a := hs.trans_lt hsa
  have hunv₁ := hP.notMem_prefix hAC hτa hab.le hgap (Or.inl rfl)
  have hunv₂ := hP.notMem_prefix hAC hτa hab.le hgap (Or.inr rfl)
  by_cases hfresh : η a ∈ η '' Ico 0 a
  · -- **old start**: a fixed chart after both attachment visits
    have haτ : a ≠ τ := fun h => hP.fresh_y (by rw [← hP.first_y, ← h]; exact hfresh)
    have ha' := ha.resolve_left haτ
    have hvis : ∀ {α : ℝ → ℂ}, (α = α₁ ∨ α = α₂) →
        ∃ t' ∈ Ico 0 a, η t' = α (lastVisit (fun t => η '' Icc 0 t) α a) := by
      intro α hα
      obtain ⟨hu0, hsuf, -, -⟩ := hP.chart hτa hα
      obtain ⟨t', ht', hpt'⟩ := hsuf _ ⟨hu0, le_rfl⟩
      rcases eq_or_lt_of_le ht'.2 with h | h
      · rw [h] at hpt'
        obtain ⟨t'', ht'', h''⟩ := hfresh
        exact ⟨t'', ht'', h''.trans hpt'⟩
      · exact ⟨t', ⟨ht'.1, h⟩, hpt'⟩
    obtain ⟨t₁, ht₁, hp₁⟩ := hvis (Or.inl rfl)
    obtain ⟨t₂, ht₂, hp₂⟩ := hvis (Or.inr rfl)
    set M := max s (max t₁ t₂) with hMdef
    have hMa : M < a := max_lt hsa (max_lt ht₁.2 ht₂.2)
    set r := (M + a) / 2 with hrdef
    have hMr : M < r := by rw [hrdef]; linarith
    have hra : r < a := by rw [hrdef]; linarith
    have hsr : s ≤ r := (le_max_left _ _).trans hMr.le
    have ht₁r : t₁ ≤ r := ((le_max_left _ _).trans (le_max_right _ _)).trans hMr.le
    have ht₂r : t₂ ≤ r := ((le_max_right _ _).trans (le_max_right _ _)).trans hMr.le
    have hτr : τ ≤ r := (hP.τ_le (hP.y_mem_of_mem (Or.inl rfl) (hP.chart hτa (Or.inl rfl)).1
      ⟨t₁, ⟨ht₁.1, le_rfl⟩, hp₁⟩)).trans ht₁r
    -- the attachment parameters at `r` and at `a` agree
    have heq : ∀ {α : ℝ → ℂ}, (α = α₁ ∨ α = α₂) → ∀ {t' : ℝ}, t' ∈ Ico 0 a → t' ≤ r →
        η t' = α (lastVisit (fun t => η '' Icc 0 t) α a) →
        lastVisit (fun t => η '' Icc 0 t) α r = lastVisit (fun t => η '' Icc 0 t) α a := by
      intro α hα t' ht' ht'r hp
      obtain ⟨hc, -, htα, h0, -⟩ := hP.arm hα
      exact lastVisit_eq_of_visited hc htα monotone_image_Icc hra.le (hP.isCompact_range a)
        (hP.isCompact_range r).isBounded ⟨0, mem_Ici.2 le_rfl, h0 ▸ hP.y_mem hτa⟩
        ⟨t', ⟨ht'.1, ht'r⟩, hp⟩
    have he₁ := heq (Or.inl rfl) ht₁ ht₁r hp₁
    have he₂ := heq (Or.inr rfl) ht₂ ht₂r hp₂
    obtain ⟨hu₁, -, hK₁, hD₁⟩ := hP.chart hτr (Or.inl rfl)
    obtain ⟨hu₂, -, hK₂, hD₂⟩ := hP.chart hτr (Or.inr rfl)
    rw [← he₁] at hunv₁
    rw [← he₂] at hunv₂
    exact ownFuture_gap_eq_of_pocket_inf_gate hη hW hW0 hP.isOpen hP.farReal hu₁ hu₂ hP.cont₁
      hP.cont₂ hP.inj₁ hP.inj₂ hP.tendsto₁ hP.tendsto₂ hP.frontier_eq
      (hP.disjoint_prefixes hu₁ hu₂) hs hsr hra.le hab hD₁ hD₂ hK₁ hK₂ hgap hunv₁ hunv₂
      (Or.inl (IsReversePocket.mem_closure_visits_of_lt ha' hra))
      (closure_mono (s := {t | a < t ∧ η t ∈ C}) (t := {t | r < t ∧ η t ∈ C})
        (fun t ht => ⟨hra.trans ht.1, ht.2⟩) hb)
  · -- **fresh start**: the chart at `a` and its gate (Lemma 1.4 and the fresh-tip lemma)
    have hfr : η a ∈ frontier C := by
      rcases ha with h | h
      · rw [h, hP.first_y, hP.frontier_eq]
        exact Or.inl ⟨0, mem_Ici.2 le_rfl, rfl⟩
      · refine ⟨hP.mem_closure_of_mem_closure_visits hs h, ?_⟩
        rw [hP.isOpen.interior_eq]
        exact hgap a ⟨le_rfl, hab.le⟩
    have haH := hP.mem_H_of_fresh ha0 hfr hfresh
    have hatt := hP.fresh_attach ha0.le hfr hfresh
    obtain ⟨hu₁, -, hK₁, hD₁⟩ := hP.chart hτa (Or.inl rfl)
    obtain ⟨hu₂, -, hK₂, hD₂⟩ := hP.chart hτa (Or.inr rfl)
    refine ownFuture_gap_eq_of_pocket_inf_gate hη hW hW0 hP.isOpen hP.farReal hu₁ hu₂ hP.cont₁
      hP.cont₂ hP.inj₁ hP.inj₂ hP.tendsto₁ hP.tendsto₂ hP.frontier_eq
      (hP.disjoint_prefixes hu₁ hu₂) hs hsa.le le_rfl hab hD₁ hD₂ hK₁ hK₂ hgap hunv₁ hunv₂
      (Or.inr ⟨rfl, ?_⟩) hb
    rcases hatt with h1 | h1
    · exact Or.inl fun q hq => fresh_tip_fibre hη hW hW0 ha0 haH hfresh (hq.trans h1.symm)
    · exact Or.inr fun q hq => fresh_tip_fibre hη hW hW0 ha0 haH hfresh (hq.trans h1.symm)

/-- **The initial gap at the original seed, junction at infinity** (ruling R41's note, L264–L266):
if `y₀ = η(0)` (`τ = 0`) and the trace avoids `C` on `[0, b]`, `b` a limit of later visits, then
`η(b) = η(0)`. In the chart at `0` (the identity) the lifted prefixes end at the gate `0 = δ_0(0)`,
since the only point visited by time `0` is `η(0) = 0`. -/
theorem gap_eq_seed (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) (hτ0 : τ = 0) {b : ℝ} (hb0 : 0 < b)
    (hgap : ∀ t ∈ Icc 0 b, η t ∉ C) (hb : b ∈ closure {t | 0 < t ∧ η t ∈ C}) : η 0 = η b := by
  have hη := hP.trace
  have hW := hP.continuous_W
  have hW0 := hP.W_zero
  have hunv₁ := hP.notMem_prefix hAC hτ0.le hb0.le hgap (Or.inl rfl)
  have hunv₂ := hP.notMem_prefix hAC hτ0.le hb0.le hgap (Or.inr rfl)
  obtain ⟨hu₁, hV₁, hK₁, hD₁⟩ := hP.chart hτ0.le (Or.inl rfl)
  obtain ⟨hu₂, -, hK₂, hD₂⟩ := hP.chart hτ0.le (Or.inr rfl)
  have hg : ∀ q : ℝ, trMap W 0 0 q = α₁ (lastVisit (fun t => η '' Icc 0 t) α₁ 0) → q = 0 := by
    intro q hq
    obtain ⟨t, ht, hte⟩ := hV₁ _ ⟨hu₁, le_rfl⟩
    rw [le_antisymm ht.2 ht.1, hη.1, ← hq, YuanSimpleApprox.trMap_self hW 0 (ofReal_mem_Hbar q)]
      at hte
    exact_mod_cast hte.symm
  exact (ownFuture_gap_eq_of_pocket_inf_gate hη hW hW0 hP.isOpen hP.farReal hu₁ hu₂ hP.cont₁
    hP.cont₂ hP.inj₁ hP.inj₂ hP.tendsto₁ hP.tendsto₂ hP.frontier_eq
    (hP.disjoint_prefixes hu₁ hu₂) le_rfl le_rfl le_rfl hb0 hD₁ hD₂ hK₁ hK₂ hgap hunv₁ hunv₂
    (Or.inr ⟨rfl, Or.inl hg⟩) hb).2

end IsReversePocketInf

end InteractingSLE.Sec6
