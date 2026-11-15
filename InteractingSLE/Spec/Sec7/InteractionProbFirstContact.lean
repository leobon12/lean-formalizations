import InteractingSLE.Spec.Sec7.InteractionFirstContact
import InteractingSLE.Frozen.Spec.sleLambda

/-!
# Lemma 7.7, "A common first contact": the reduction to Aux. lemmas 70 and 72

Packet PROVE-SEC7-B2 (Specification §7.2, Lemma 7.7, p. 282, and its proof paragraph "A common first contact",
`source/spec/p241-288.md`, page 282; Aux. lemmas 68, 70, 72, pp. 272–279).

The proof of Lemma 7.7's common first point reads: "Fix an integer `m ≥ 1` and stop both paths at `Tᵢ ∧ m`. Their
ranges are compact simple arcs […]. If they meet, Aux. lemma 68 applies. If their first intersection points were
distinct, its last assertion would give either a reverse common nondegenerate subarc or two adjacent minimal
contacts. Aux. lemma 70 excludes the first alternative, and Aux. lemma 72 excludes the second. Their first
intersection points therefore agree. This holds simultaneously for every integer `m`, by a countable intersection of
probability-one events."

This file proves that paragraph, deterministically per truncation and then almost surely, from the *conclusions*
of Aux. lemmas 70 and 72 at every integer truncation (the predicates `NoReverseMinimalArc` and
`NoAdjacentMinimalContacts`), with Aux. lemma 68 (landed, `InteractionContacts.lean`). The two conclusions are
probabilistic statements of §7.2 that are not proved in Lean (their inputs: the history-marked single-path GFF
kernels, Prop. 3.8's common-arc form, Aux. 57, 69 for Aux. 70; Lemma 7.6 and Aux. 71 for Aux. 72), so the main
theorems here are conditional helpers with distinct names; the Theorem 1.5 assembly does not use them.

Also: the height mismatch that closes Aux. lemma 70 (`sleLambda_sub_ne`, p. 275–276).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

variable {X : Type*}

/-! ### The truncations `ζ ∧ m` -/

/-- The truncation `ζ ∧ m` of an available lifetime at the integer horizon `m` (Lemma 7.7's proof, p. 282: "stop
both paths at `Tᵢ ∧ m`"), as a finite parameter. -/
def truncTime (ζ : ℝ≥0∞) (m : ℕ) : ℝ≥0 := (min ζ (m : ℝ≥0∞)).toNNReal

theorem coe_truncTime (ζ : ℝ≥0∞) (m : ℕ) : (truncTime ζ m : ℝ≥0∞) = min ζ (m : ℝ≥0∞) :=
  ENNReal.coe_toNNReal (min_le_right _ _ |>.trans_lt (ENNReal.natCast_lt_top m)).ne

theorem coe_truncTime_le (ζ : ℝ≥0∞) (m : ℕ) : (truncTime ζ m : ℝ≥0∞) ≤ ζ := by
  rw [coe_truncTime]
  exact min_le_left _ _

theorem Icc_truncTime_subset (ζ : ℝ≥0∞) (m : ℕ) :
    Icc 0 (truncTime ζ m) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ} := fun _ ht =>
  (ENNReal.coe_le_coe.2 ht.2).trans (coe_truncTime_le ζ m)

theorem le_truncTime {ζ : ℝ≥0∞} {t : ℝ≥0} {m : ℕ} (ht : (t : ℝ≥0∞) ≤ ζ) (hm : t ≤ (m : ℝ≥0)) :
    t ≤ truncTime ζ m := by
  rw [← ENNReal.coe_le_coe, coe_truncTime]
  refine le_min ht ?_
  rw [← ENNReal.coe_natCast]
  exact ENNReal.coe_le_coe.2 hm

theorem truncTime_mono (ζ : ℝ≥0∞) {m m' : ℕ} (h : m ≤ m') : truncTime ζ m ≤ truncTime ζ m' := by
  rw [← ENNReal.coe_le_coe, coe_truncTime, coe_truncTime]
  exact min_le_min_left _ (by exact_mod_cast h)

/-! ### The conclusions of Aux. lemmas 70 and 72 -/

/-- The conclusion of **Aux. lemma 70** (exclusion of a reverse minimal common arc, p. 274) for the stopped paths
`α|[0, A]`, `β|[0, B]`: "the first-coordinate projection of the set of minimal contacts from Aux. lemma 68 contains
no nondegenerate interval". -/
def NoReverseMinimalArc (α : ℝ≥0 → X) (A : ℝ≥0) (β : ℝ≥0 → X) (B : ℝ≥0) : Prop :=
  ∀ a c : ℝ≥0, a < c → ¬ Icc a c ⊆ Prod.fst '' minimalContacts α A β B

/-- The conclusion of **Aux. lemma 72** (a countable adapted witness for every minimal lens, p. 278) for the
stopped paths `α|[0, A]`, `β|[0, B]`: "there are no two adjacent minimal contacts with distinct points" (adjacent:
no minimal contact has its first coordinate strictly between theirs, Aux. lemma 68 (4)). -/
def NoAdjacentMinimalContacts (α : ℝ≥0 → X) (A : ℝ≥0) (β : ℝ≥0 → X) (B : ℝ≥0) : Prop :=
  ¬ ∃ a b c d : ℝ≥0, (a, b) ∈ minimalContacts α A β B ∧ (c, d) ∈ minimalContacts α A β B ∧ a < c ∧
    α a ≠ α c ∧ ∀ p ∈ minimalContacts α A β B, p.1 ∉ Ioo a c

/-! ### The common first contact -/

/-- **Lemma 7.7, "A common first contact", for one truncation** (p. 282). For continuous injective stopped paths
whose contact set is nonempty, the conclusions of Aux. lemmas 70 and 72 leave, by Aux. lemma 68's dichotomy, a
single minimal contact, which is therefore below every contact. -/
theorem exists_le_contactSet_of_noReverse_of_noAdjacent [TopologicalSpace X] [T2Space X]
    {α β : ℝ≥0 → X} {A B : ℝ≥0} (hα : ContinuousOn α (Icc 0 A)) (hβ : ContinuousOn β (Icc 0 B))
    (hαi : InjOn α (Icc 0 A)) (hβi : InjOn β (Icc 0 B)) (hC : (contactSet α A β B).Nonempty)
    (h70 : NoReverseMinimalArc α A β B) (h72 : NoAdjacentMinimalContacts α A β B) :
    ∃ p ∈ contactSet α A β B, ∀ q ∈ contactSet α A β B, p.1 ≤ q.1 ∧ p.2 ≤ q.2 := by
  refine (exists_minimalContacts_eq_singleton_iff hα hβ).1 ?_
  by_contra hP
  rcases minimalContacts_dichotomy hα hβ hαi hβi hC hP with ⟨a, c, hac, hsub⟩ | ⟨a, b, c, d, hab, hcd, hac, hgap⟩
  · exact h70 a c hac hsub
  · refine h72 ⟨a, b, c, d, hab, hcd, hac, fun he => hac.ne ?_, hgap⟩
    exact hαi hab.1.1 hcd.1.1 he

/-- **Lemma 7.7, "A common first contact"** (p. 282), deterministic form. Let `η₁`, `η₂` be continuous and
injective on their available intervals `{t | t ≤ ζᵢ}`. If, at every integer truncation `ζᵢ ∧ m`, the conclusions of
Aux. lemmas 70 and 72 hold, then whenever the available paths meet, they have a first contact (`IsFirstContact`:
both first-contact infima attained, at one common point). -/
theorem exists_isFirstContact_of_truncations {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}
    (hc₁ : ContinuousOn η₁ {s | (s : ℝ≥0∞) ≤ ζ₁}) (hc₂ : ContinuousOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂})
    (hi₁ : InjOn η₁ {s | (s : ℝ≥0∞) ≤ ζ₁}) (hi₂ : InjOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂})
    (h70 : ∀ m : ℕ, NoReverseMinimalArc η₁ (truncTime ζ₁ m) η₂ (truncTime ζ₂ m))
    (h72 : ∀ m : ℕ, NoAdjacentMinimalContacts η₁ (truncTime ζ₁ m) η₂ (truncTime ζ₂ m))
    (hmeet : ∃ s t : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ∧ (t : ℝ≥0∞) ≤ ζ₂ ∧ η₁ s = η₂ t) :
    ∃ s₀ t₀ : ℝ≥0, IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀ := by
  -- the least contact at a truncation containing a given contact
  have key : ∀ m : ℕ, (contactSet η₁ (truncTime ζ₁ m) η₂ (truncTime ζ₂ m)).Nonempty →
      ∃ p ∈ contactSet η₁ (truncTime ζ₁ m) η₂ (truncTime ζ₂ m),
        ∀ q ∈ contactSet η₁ (truncTime ζ₁ m) η₂ (truncTime ζ₂ m), p.1 ≤ q.1 ∧ p.2 ≤ q.2 :=
    fun m hC => exists_le_contactSet_of_noReverse_of_noAdjacent
      (hc₁.mono (Icc_truncTime_subset ζ₁ m)) (hc₂.mono (Icc_truncTime_subset ζ₂ m))
      (hi₁.mono (Icc_truncTime_subset ζ₁ m)) (hi₂.mono (Icc_truncTime_subset ζ₂ m)) hC (h70 m) (h72 m)
  -- a contact lies in every truncation beyond its parameters
  have hmem : ∀ (s t : ℝ≥0) (m : ℕ), (s : ℝ≥0∞) ≤ ζ₁ → (t : ℝ≥0∞) ≤ ζ₂ → η₁ s = η₂ t →
      s ≤ (m : ℝ≥0) → t ≤ (m : ℝ≥0) →
      (s, t) ∈ contactSet η₁ (truncTime ζ₁ m) η₂ (truncTime ζ₂ m) :=
    fun s t m hs ht hst hsm htm =>
      ⟨⟨zero_le, le_truncTime hs hsm⟩, ⟨zero_le, le_truncTime ht htm⟩, hst⟩
  obtain ⟨s, t, hs, ht, hst⟩ := hmeet
  obtain ⟨m, hm⟩ := exists_nat_ge (max s t)
  obtain ⟨p, hpC, hpmin⟩ := key m ⟨_, hmem s t m hs ht hst (le_max_left s t |>.trans hm)
    (le_max_right s t |>.trans hm)⟩
  refine ⟨p.1, p.2, (ENNReal.coe_le_coe.2 hpC.1.2).trans (coe_truncTime_le ζ₁ m),
    (ENNReal.coe_le_coe.2 hpC.2.1.2).trans (coe_truncTime_le ζ₂ m), hpC.2.2, ?_⟩
  intro s' t' hs' ht' hst'
  obtain ⟨m', hm'⟩ := exists_nat_ge (max (m : ℝ≥0) (max s' t'))
  have hmm' : m ≤ m' := by exact_mod_cast (le_max_left _ _).trans hm'
  have hq : (s', t') ∈ contactSet η₁ (truncTime ζ₁ m') η₂ (truncTime ζ₂ m') :=
    hmem s' t' m' hs' ht' hst' ((le_max_left s' t').trans ((le_max_right _ _).trans hm'))
      ((le_max_right s' t').trans ((le_max_right _ _).trans hm'))
  have hpC' : p ∈ contactSet η₁ (truncTime ζ₁ m') η₂ (truncTime ζ₂ m') :=
    ⟨⟨zero_le, hpC.1.2.trans (truncTime_mono ζ₁ hmm')⟩,
      ⟨zero_le, hpC.2.1.2.trans (truncTime_mono ζ₂ hmm')⟩, hpC.2.2⟩
  obtain ⟨p', hp'C, hp'min⟩ := key m' ⟨_, hq⟩
  -- `p' ≤ p`, so `p'` is a contact at the truncation `m`, hence `p ≤ p'`
  have hp'p := hp'min p hpC'
  have hp'Cm : p' ∈ contactSet η₁ (truncTime ζ₁ m) η₂ (truncTime ζ₂ m) :=
    ⟨⟨zero_le, hp'p.1.trans hpC.1.2⟩, ⟨zero_le, hp'p.2.trans hpC.2.1.2⟩, hp'C.2.2⟩
  have hpp' := hpmin p' hp'Cm
  have hp'q := hp'min _ hq
  exact ⟨hpp'.1.trans hp'q.1, hpp'.2.trans hp'q.2⟩

/-- **Lemma 7.7, "A common first contact"** (p. 282), almost sure form ("This holds simultaneously for every
integer `m`, by a countable intersection of probability-one events"). If almost surely the available paths are
continuous and injective, and for every integer `m` almost surely the conclusions of Aux. lemmas 70 and 72 hold at
the truncation `ζᵢ ∧ m`, then almost surely the available paths, when they meet, have a first contact. -/
theorem ae_exists_isFirstContact_of_truncations {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hc₁ : ∀ᵐ ω ∂P, ContinuousOn (η₁ ω) {s | (s : ℝ≥0∞) ≤ ζ₁ ω})
    (hc₂ : ∀ᵐ ω ∂P, ContinuousOn (η₂ ω) {t | (t : ℝ≥0∞) ≤ ζ₂ ω})
    (hi₁ : ∀ᵐ ω ∂P, InjOn (η₁ ω) {s | (s : ℝ≥0∞) ≤ ζ₁ ω})
    (hi₂ : ∀ᵐ ω ∂P, InjOn (η₂ ω) {t | (t : ℝ≥0∞) ≤ ζ₂ ω})
    (h70 : ∀ m : ℕ, ∀ᵐ ω ∂P, NoReverseMinimalArc (η₁ ω) (truncTime (ζ₁ ω) m) (η₂ ω) (truncTime (ζ₂ ω) m))
    (h72 : ∀ m : ℕ, ∀ᵐ ω ∂P,
      NoAdjacentMinimalContacts (η₁ ω) (truncTime (ζ₁ ω) m) (η₂ ω) (truncTime (ζ₂ ω) m)) :
    ∀ᵐ ω ∂P, (∃ s t : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω ∧ (t : ℝ≥0∞) ≤ ζ₂ ω ∧ η₁ ω s = η₂ ω t) →
      ∃ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ := by
  filter_upwards [hc₁, hc₂, hi₁, hi₂, ae_all_iff.2 h70, ae_all_iff.2 h72] with ω h₁ h₂ h₃ h₄ h₅ h₆
  exact exists_isFirstContact_of_truncations h₁ h₂ h₃ h₄ h₅ h₆

/-! ### The height mismatch of Aux. lemma 70 -/

/-- **The closing computation of Aux. lemma 70** (pp. 275–276). The heights `λ − θ₁χ` (right side of the first
trace) and `−λ − θ₂χ` (left side of the second trace) of one conditional harmonic function on a common exposed arc
cannot agree: equality would give `θ₁ − θ₂ = 2λ/χ = 4π/(4 − κ) > π`, "contrary to the assumed strict inequality"
`θ₁ < θ₂ + π`. -/
theorem sleLambda_sub_ne {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂ + Real.pi) :
    sleLambda κ - θ₁ * QuantumZipper.chiC κ ≠ -sleLambda κ - θ₂ * QuantumZipper.chiC κ := by
  intro heq
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  -- `2λ = (θ₁ − θ₂)χ`, multiplied by `2√κ`: `4π = (θ₁ − θ₂)(4 − κ)`
  have h2 : 2 * sleLambda κ = (θ₁ - θ₂) * QuantumZipper.chiC κ := by linarith
  have hlam : sleLambda κ * Real.sqrt κ = Real.pi := by
    unfold sleLambda
    field_simp
  have hchi : QuantumZipper.chiC κ * (2 * Real.sqrt κ) = 4 - κ := by
    unfold QuantumZipper.chiC
    field_simp
    rw [Real.sq_sqrt hκ.le]
    norm_num
  have h4 : 4 * Real.pi = (θ₁ - θ₂) * (4 - κ) := by
    calc 4 * Real.pi = 2 * sleLambda κ * (2 * Real.sqrt κ) := by rw [← hlam]; ring
      _ = (θ₁ - θ₂) * (QuantumZipper.chiC κ * (2 * Real.sqrt κ)) := by rw [h2]; ring
      _ = (θ₁ - θ₂) * (4 - κ) := by rw [hchi]
  have hd : θ₁ - θ₂ < Real.pi := by linarith
  have hk : 0 < 4 - κ := sub_pos.2 hκ4
  nlinarith [Real.pi_pos]

end Sec7

end InteractingSLE
