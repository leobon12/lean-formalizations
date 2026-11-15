/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Supplement §5.4 repaired: fixed-chart facts for the gap argument (Lemma 1.2(3) and the gate lemma's core)

Packet PROVE-R7. Ruling R41 replaces the gap paragraphs of supplement §5.4 ("Closed gaps have identical endpoints",
"Erasure, relative prime ends, and the relative driver", `source/spec/p433-480.md` L1000–L1018, pp. 473–474) by the
fixed-chart argument of `source/external/AstraIG1/ig1_ztip_elimination.txt` §§1.1–1.3 (Lemma 1.2, Lemma 1.3,
Propositions 1.5–1.6). This file proves the deterministic, chart-free parts of that argument.

* **Lemma 1.2(3)** (lines 70–72, proof lines 87–90): the first-visit parameter `u(t) = min{v : α(v) ∈ R_t}` of an
  incoming path is nonincreasing, and if it is constant on `[a, b]` and its point `p(a) = α(u(a))` was already visited
  at a time `r ≤ a`, it is constant on `[r, b]` (`firstVisitParam_eq_of_visited`). "This argument also applies to an
  outer arm; its attachment parameter need not be continuous": no continuity of `u` is used.
* **Lemma 1.3, the fixed-chart gate lemma** (lines 141–181), its point-set core:
  * the interval exclusion ("Each `v ∈ (q₁, q₂)` has a disk neighborhood whose open upper half-disk is contained in
    `F`. If `δ(a) = v`, continuity and avoidance of `F` put `δ` on `ℝ` on a nontrivial right time-neighborhood of `a`, a
    contradiction. […] The identical argument at an interior time shows that `δ` never visits `(q₁, q₂)` during the
    gap"): `false_of_mem_halfDisc`;
  * the endpoint classification ("Hence the endpoint values are on that interval […] Both endpoint values are
    therefore gates"): `eq_gate_of_mem_closure`;
  * the connectedness step ("Thus the allowed set containing the entire image of `δ` has two disjoint relatively closed
    sides, one containing each gate. A connected image cannot join the two gates"), with the two sides as a hypothesis
    (`IsGateSeparation`): `gate_eq_of_separation`, and the equal-gate case ("If `q₁ = q₂ = q` […] directly gives
    `δ(a) = δ(b) = q`"): `gate_eq_of_eq`;
  * the gate lemma with its two variants (endpoint in the closed face, or "the initial endpoint condition […] directly
    that `δ(a)` is one of the gates"): `gate_eq` and `gate_eq_of_initial_gate`.

**Not proved here:** that the central Jordan-face geometry of a selected pocket (two selected incoming arcs from the
junction `z` to the gates, and, for finite `z`, the exterior arm from `z` to infinity) supplies the separation
`IsGateSeparation` ("For a finite junction `z`, the union of the two selected arms is a crosscut from `q₁` to `q₂`. […]
The crosscut form of Jordan separation gives two exterior faces `U₁, U₂` […] their closures are disjoint away from the
removed incoming tree"). This is a θ-curve form of the Jordan curve theorem, not available in the tracked
`Foundations/Topology` (see `planning/handoffs/PROVE-R7.md`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric

namespace InteractingSLE

namespace R7

/-! ### Lemma 1.2(3): the first-visit parameter -/

section FirstVisit

variable {X : Type*}

/-- The first-visit parameter `u(t) = min{v ∈ [0, 1] : α(v) ∈ R_t}` of an incoming path `α` with respect to the
visited sets `R_t` (repair note, Lemma 1.2(3)). -/
def firstVisitParam (α : ℝ → X) (R : ℝ → Set X) (t : ℝ) : ℝ := sInf {v ∈ Icc (0 : ℝ) 1 | α v ∈ R t}

theorem bddBelow_firstVisitSet (α : ℝ → X) (R : ℝ → Set X) (t : ℝ) :
    BddBelow {v ∈ Icc (0 : ℝ) 1 | α v ∈ R t} :=
  ⟨0, fun _ hv => hv.1.1⟩

/-- "Monotonicity of the visited sets makes `u` nonincreasing." -/
theorem firstVisitParam_antitone {α : ℝ → X} {R : ℝ → Set X} (hR : Monotone R) {s t : ℝ} (hst : s ≤ t)
    (hne : {v ∈ Icc (0 : ℝ) 1 | α v ∈ R s}.Nonempty) : firstVisitParam α R t ≤ firstVisitParam α R s :=
  csInf_le_csInf (bddBelow_firstVisitSet α R t) hne fun _ hv => ⟨hv.1, hR hst hv.2⟩

/-- **Lemma 1.2(3)** (repair note, lines 70–72 and 87–90): if the first-visit parameter is constant on `[a, b]` and
its point `p(a) = α(u(a))` has already been visited by a time `r ≤ a`, then it is constant on `[r, b]`. "The inclusion
`p(a) ∈ R_r` gives `u(r) ≤ u(a)`, whereas `r ≤ a` gives `u(r) ≥ u(a)`. Therefore equality holds, and monotonicity
gives constancy through `b`." (The hypothesis `u(a) ∈ [0, 1]` holds whenever `u(a)` is an actual minimum. The
source's `r ≤ a` is not needed: for `r > a` the conclusion is part of the hypothesis.) -/
theorem firstVisitParam_eq_of_visited {α : ℝ → X} {R : ℝ → Set X} (hR : Monotone R) {a b r : ℝ}
    (hconst : ∀ t ∈ Icc a b, firstVisitParam α R t = firstVisitParam α R a)
    (hmem : firstVisitParam α R a ∈ Icc (0 : ℝ) 1) (hvis : α (firstVisitParam α R a) ∈ R r) :
    ∀ t ∈ Icc r b, firstVisitParam α R t = firstVisitParam α R a := by
  intro t ht
  rcases le_total t a with hta | hat
  · have hin : firstVisitParam α R a ∈ {v ∈ Icc (0 : ℝ) 1 | α v ∈ R t} := ⟨hmem, hR ht.1 hvis⟩
    refine le_antisymm (csInf_le (bddBelow_firstVisitSet α R t) hin) ?_
    exact firstVisitParam_antitone hR hta ⟨_, hin⟩
  · exact hconst t ⟨hat, ht.2⟩

end FirstVisit

/-! ### Lemma 1.3: the fixed-chart gate lemma, point-set core -/

section Gate

/-- The closed upper half-plane `{Im z ≥ 0}`, where the mapped paths `δ_r` take their values. -/
def closedUpper : Set ℂ := {z | 0 ≤ z.im}

/-- The open upper half-plane `{Im z > 0}`. -/
def openUpper : Set ℂ := {z | 0 < z.im}

/-- Hypothesis (2) of the gate lemma: `δ` has no nontrivial time interval in `ℝ` on `[a, b]`. -/
def NoRealInterval (δ : ℝ → ℂ) (a b : ℝ) : Prop :=
  ∀ c d : ℝ, a ≤ c → c < d → d ≤ b → ∃ s ∈ Icc c d, (δ s).im ≠ 0

variable {δ : ℝ → ℂ} {a b : ℝ} {F T : Set ℂ}

/-- **The interval exclusion of the gate lemma.** Let `δ` be continuous on `[a, b]` (`a < b`) with values in the
closed upper half-plane, avoiding `F` there and with no nontrivial real time interval. Then `δ` never visits a point
`v` having an open upper half-disc `B(v, ε) ∩ ℍ ⊆ F`: continuity puts `δ` in `B(v, ε)` on a one-sided time
neighbourhood, avoidance of `F` puts it on `ℝ` there. -/
theorem false_of_mem_halfDisc (hab : a < b) (hδc : ContinuousOn δ (Icc a b))
    (hδH : ∀ s ∈ Icc a b, δ s ∈ closedUpper) (hδF : ∀ s ∈ Icc a b, δ s ∉ F) (hδR : NoRealInterval δ a b)
    {t : ℝ} (ht : t ∈ Icc a b) {ε : ℝ} (hε : 0 < ε) (hdisc : ball (δ t) ε ∩ openUpper ⊆ F) : False := by
  obtain ⟨η, hη, hηball⟩ := Metric.continuousWithinAt_iff.1 (hδc t ht) ε hε
  -- on a time interval near `t` inside `[a, b]`, `δ` stays in the ball, hence on `ℝ`
  have hreal : ∀ s ∈ Icc a b, |s - t| < η → (δ s).im = 0 := by
    intro s hs hst
    have hb : δ s ∈ ball (δ t) ε := by
      rw [mem_ball]
      exact hηball hs (by rwa [Real.dist_eq])
    have hnot : δ s ∉ openUpper := fun hup => hδF s hs (hdisc ⟨hb, hup⟩)
    have h0 : 0 ≤ (δ s).im := hδH s hs
    simp only [openUpper, mem_ofPred_eq, not_lt] at hnot
    linarith
  rcases lt_or_eq_of_le ht.2 with htb | htb
  · -- a right time neighbourhood `[t, t + ε']`
    set d := min (t + η / 2) b with hd
    have htd : t < d := lt_min (by linarith) htb
    obtain ⟨s, hs, hne⟩ := hδR t d ht.1 htd (min_le_right _ _)
    refine hne (hreal s ⟨ht.1.trans hs.1, hs.2.trans (min_le_right _ _)⟩ ?_)
    rw [abs_lt]
    constructor
    · linarith [hs.1]
    · linarith [hs.2, min_le_left (t + η / 2) b]
  · -- `t = b`: a left time neighbourhood `[b − ε', b]`
    subst htb
    set c := max (t - η / 2) a with hc
    have hct : c < t := max_lt (by linarith) hab
    obtain ⟨s, hs, hne⟩ := hδR c t (le_max_right _ _) hct le_rfl
    refine hne (hreal s ⟨(le_max_right _ _).trans hs.1, hs.2⟩ ?_)
    rw [abs_lt]
    constructor
    · linarith [hs.1, le_max_left (t - η / 2) a]
    · linarith [hs.2]

/-- The real points `(q₁, q₂)` as a subset of `ℂ`. -/
def realIoo (q₁ q₂ : ℝ) : Set ℂ := ((↑) : ℝ → ℂ) '' Ioo q₁ q₂

/-- The real points `[q₁, q₂]` as a subset of `ℂ`. -/
def realIcc (q₁ q₂ : ℝ) : Set ℂ := ((↑) : ℝ → ℂ) '' Icc q₁ q₂

/-- The part of the central-face geometry used by the interval exclusion: the face lies in `ℍ`, its boundary off the
incoming tree `T` is the real interval `[q₁, q₂]`, and each `v ∈ (q₁, q₂)` has an open upper half-disc in `F`. -/
def IsGateFace (F T : Set ℂ) (q₁ q₂ : ℝ) : Prop :=
  F ⊆ openUpper ∧ closure F \ F ⊆ T ∪ realIcc q₁ q₂ ∧
    ∀ v ∈ Ioo q₁ q₂, ∃ ε > 0, ball (v : ℂ) ε ∩ openUpper ⊆ F

/-- **The endpoint classification.** Under the face description, a value of `δ` in the closed face is a gate:
"the endpoint values are on that interval [`[q₁, q₂]`]" and the interval exclusion leaves only `q₁, q₂`. -/
theorem eq_gate_of_mem_closure {q₁ q₂ : ℝ} (hF : IsGateFace F T q₁ q₂) (hab : a < b)
    (hδc : ContinuousOn δ (Icc a b)) (hδH : ∀ s ∈ Icc a b, δ s ∈ closedUpper)
    (hδF : ∀ s ∈ Icc a b, δ s ∉ F) (hδT : ∀ s ∈ Icc a b, δ s ∉ T) (hδR : NoRealInterval δ a b)
    {t : ℝ} (ht : t ∈ Icc a b) (hcl : δ t ∈ closure F) : δ t = q₁ ∨ δ t = q₂ := by
  obtain ⟨-, hfront, hdisc⟩ := hF
  rcases hfront ⟨hcl, hδF t ht⟩ with hT | ⟨x, hx, hxe⟩
  · exact absurd hT (hδT t ht)
  rcases eq_or_lt_of_le hx.1 with h1 | h1
  · exact Or.inl (by rw [← hxe, h1])
  rcases eq_or_lt_of_le hx.2 with h2 | h2
  · exact Or.inr (by rw [← hxe, h2])
  obtain ⟨ε, hε, hball⟩ := hdisc x ⟨h1, h2⟩
  rw [hxe] at hball
  exact (false_of_mem_halfDisc hab hδc hδH hδF hδR ht hε hball).elim

/-- Under the face description, `δ` never visits the open real interval `(q₁, q₂)` on `[a, b]`. -/
theorem not_mem_realIoo {q₁ q₂ : ℝ} (hF : IsGateFace F T q₁ q₂) (hab : a < b) (hδc : ContinuousOn δ (Icc a b))
    (hδH : ∀ s ∈ Icc a b, δ s ∈ closedUpper) (hδF : ∀ s ∈ Icc a b, δ s ∉ F) (hδR : NoRealInterval δ a b)
    {t : ℝ} (ht : t ∈ Icc a b) : δ t ∉ realIoo q₁ q₂ := by
  rintro ⟨x, hx, hxe⟩
  obtain ⟨ε, hε, hball⟩ := hF.2.2 x hx
  rw [hxe] at hball
  exact false_of_mem_halfDisc hab hδc hδH hδF hδR ht hε hball

/-- The allowed set of the gate lemma: the closed upper half-plane with the face, the incoming tree and the open gate
interval removed. -/
def gateAllowed (F T : Set ℂ) (q₁ q₂ : ℝ) : Set ℂ := closedUpper \ (F ∪ T ∪ realIoo q₁ q₂)

/-- **The two exterior sides** (the conclusion of the crosscut form of Jordan separation in the gate lemma's proof):
two closed sets covering the allowed set, disjoint on it, one containing each gate. -/
def IsGateSeparation (F T : Set ℂ) (q₁ q₂ : ℝ) (U₁ U₂ : Set ℂ) : Prop :=
  IsClosed U₁ ∧ IsClosed U₂ ∧ gateAllowed F T q₁ q₂ ⊆ U₁ ∪ U₂ ∧
    gateAllowed F T q₁ q₂ ∩ (U₁ ∩ U₂) = ∅ ∧ (q₁ : ℂ) ∈ U₁ ∧ (q₂ : ℂ) ∈ U₂

/-- **The connectedness step of the gate lemma.** If `δ([a, b])` lies in the allowed set, both endpoint values are
gates, the gates lie in the allowed set and the allowed set has the two separated sides, then the endpoint values
agree: "A connected image cannot join the two gates. […] its endpoint gates agree." -/
theorem gate_eq_of_separation {q₁ q₂ : ℝ} {U₁ U₂ : Set ℂ} (hsep : IsGateSeparation F T q₁ q₂ U₁ U₂)
    (hq₁ : (q₁ : ℂ) ∈ gateAllowed F T q₁ q₂) (hq₂ : (q₂ : ℂ) ∈ gateAllowed F T q₁ q₂) (hab : a ≤ b)
    (hδc : ContinuousOn δ (Icc a b)) (hδA : ∀ s ∈ Icc a b, δ s ∈ gateAllowed F T q₁ q₂)
    (hga : δ a = q₁ ∨ δ a = q₂) (hgb : δ b = q₁ ∨ δ b = q₂) : δ a = δ b := by
  obtain ⟨hU₁, hU₂, hcov, hdisj, hq₁U, hq₂U⟩ := hsep
  have hS : IsPreconnected (δ '' Icc a b) := isPreconnected_Icc.image δ hδc
  have hSA : δ '' Icc a b ⊆ gateAllowed F T q₁ q₂ := by
    rintro _ ⟨s, hs, rfl⟩
    exact hδA s hs
  have hsplit := (isPreconnected_iff_subset_of_disjoint_closed.1 hS) U₁ U₂ hU₁ hU₂ (hSA.trans hcov)
    (Set.eq_empty_of_subset_empty fun z ⟨hz, hzU⟩ => by
      rw [← hdisj]
      exact ⟨hSA hz, hzU⟩)
  have hq₂U₁ : (q₂ : ℂ) ∉ U₁ := fun h => by
    have : (q₂ : ℂ) ∈ gateAllowed F T q₁ q₂ ∩ (U₁ ∩ U₂) := ⟨hq₂, h, hq₂U⟩
    rw [hdisj] at this
    exact this
  have hq₁U₂ : (q₁ : ℂ) ∉ U₂ := fun h => by
    have : (q₁ : ℂ) ∈ gateAllowed F T q₁ q₂ ∩ (U₁ ∩ U₂) := ⟨hq₁, hq₁U, h⟩
    rw [hdisj] at this
    exact this
  have ha : δ a ∈ δ '' Icc a b := mem_image_of_mem δ ⟨le_rfl, hab⟩
  have hb : δ b ∈ δ '' Icc a b := mem_image_of_mem δ ⟨hab, le_rfl⟩
  rcases hsplit with h | h
  · -- the image lies in `U₁`, which misses `q₂`
    have ea : δ a = q₁ := hga.resolve_right fun e => hq₂U₁ (e ▸ h ha)
    have eb : δ b = q₁ := hgb.resolve_right fun e => hq₂U₁ (e ▸ h hb)
    rw [ea, eb]
  · have ea : δ a = q₂ := hga.resolve_left fun e => hq₁U₂ (e ▸ h ha)
    have eb : δ b = q₂ := hgb.resolve_left fun e => hq₁U₂ (e ▸ h hb)
    rw [ea, eb]

/-- **The equal-gate case** ("If `q₁ = q₂ = q` […] Endpoint membership […] directly gives `δ(a) = δ(b) = q`"). -/
theorem gate_eq_of_eq {q : ℝ} (hga : δ a = q ∨ δ a = q) (hgb : δ b = q ∨ δ b = q) : δ a = δ b := by
  rw [hga.elim id id, hgb.elim id id]

/-- `δ([a, b])` lies in the allowed set. -/
theorem mem_gateAllowed {q₁ q₂ : ℝ} (hF : IsGateFace F T q₁ q₂) (hab : a < b) (hδc : ContinuousOn δ (Icc a b))
    (hδH : ∀ s ∈ Icc a b, δ s ∈ closedUpper) (hδF : ∀ s ∈ Icc a b, δ s ∉ F) (hδT : ∀ s ∈ Icc a b, δ s ∉ T)
    (hδR : NoRealInterval δ a b) {t : ℝ} (ht : t ∈ Icc a b) : δ t ∈ gateAllowed F T q₁ q₂ := by
  refine ⟨hδH t ht, ?_⟩
  rintro ((h | h) | h)
  · exact hδF t ht h
  · exact hδT t ht h
  · exact not_mem_realIoo hF hab hδc hδH hδF hδR ht h

/-- **The fixed-chart gate lemma, initial-gate variant** (repair note Lemma 1.3, "For the initial endpoint condition
it is enough instead to know directly that `δ(a)` is one of the gates"), given the separated exterior sides when the
gates are distinct: `δ(a) = δ(b) ∈ {q₁, q₂}`. -/
theorem gate_eq_of_initial_gate {q₁ q₂ : ℝ} (hq : q₁ ≤ q₂) (hF : IsGateFace F T q₁ q₂)
    (hsep : q₁ < q₂ → ∃ U₁ U₂ : Set ℂ, IsGateSeparation F T q₁ q₂ U₁ U₂) (hq₁T : (q₁ : ℂ) ∉ T)
    (hq₂T : (q₂ : ℂ) ∉ T) (hab : a < b) (hδc : ContinuousOn δ (Icc a b))
    (hδH : ∀ s ∈ Icc a b, δ s ∈ closedUpper) (hδF : ∀ s ∈ Icc a b, δ s ∉ F) (hδT : ∀ s ∈ Icc a b, δ s ∉ T)
    (hδR : NoRealInterval δ a b) (hga : δ a = q₁ ∨ δ a = q₂) (hb : δ b ∈ closure F) :
    δ a = δ b ∧ (δ a = q₁ ∨ δ a = q₂) := by
  have hgb := eq_gate_of_mem_closure hF hab hδc hδH hδF hδT hδR ⟨hab.le, le_rfl⟩ hb
  refine ⟨?_, hga⟩
  rcases eq_or_lt_of_le hq with hqe | hqlt
  · subst hqe
    exact gate_eq_of_eq hga hgb
  obtain ⟨U₁, U₂, hs⟩ := hsep hqlt
  -- the gates are allowed points
  have hgate : ∀ q : ℝ, (q : ℂ) ∉ T → q ∉ Ioo q₁ q₂ → (q : ℂ) ∈ gateAllowed F T q₁ q₂ := by
    intro q hqT hqI
    refine ⟨by simp [closedUpper], ?_⟩
    rintro ((h | h) | ⟨x, hx, hxe⟩)
    · have := hF.1 h
      simp [openUpper] at this
    · exact hqT h
    · exact hqI (Complex.ofReal_injective hxe ▸ hx)
  exact gate_eq_of_separation hs (hgate q₁ hq₁T fun h => lt_irrefl _ h.1)
    (hgate q₂ hq₂T fun h => lt_irrefl _ h.2) hab.le hδc
    (fun s hs => mem_gateAllowed hF hab hδc hδH hδF hδT hδR hs) hga hgb

/-- **The fixed-chart gate lemma** (repair note Lemma 1.3), given the separated exterior sides when the gates are
distinct: if `δ` is continuous on `[a, b]` (`a < b`) with values in the closed upper half-plane, avoids the face and
the incoming tree, has no nontrivial real time interval, and both endpoint values lie in the closed face, then
`δ(a) = δ(b) ∈ {q₁, q₂}`. -/
theorem gate_eq {q₁ q₂ : ℝ} (hq : q₁ ≤ q₂) (hF : IsGateFace F T q₁ q₂)
    (hsep : q₁ < q₂ → ∃ U₁ U₂ : Set ℂ, IsGateSeparation F T q₁ q₂ U₁ U₂) (hq₁T : (q₁ : ℂ) ∉ T)
    (hq₂T : (q₂ : ℂ) ∉ T) (hab : a < b) (hδc : ContinuousOn δ (Icc a b))
    (hδH : ∀ s ∈ Icc a b, δ s ∈ closedUpper) (hδF : ∀ s ∈ Icc a b, δ s ∉ F) (hδT : ∀ s ∈ Icc a b, δ s ∉ T)
    (hδR : NoRealInterval δ a b) (ha : δ a ∈ closure F) (hb : δ b ∈ closure F) :
    δ a = δ b ∧ (δ a = q₁ ∨ δ a = q₂) :=
  gate_eq_of_initial_gate hq hF hsep hq₁T hq₂T hab hδc hδH hδF hδT hδR
    (eq_gate_of_mem_closure hF hab hδc hδH hδF hδT hδR ⟨le_rfl, hab.le⟩ ha) hb

end Gate

end R7

end InteractingSLE
