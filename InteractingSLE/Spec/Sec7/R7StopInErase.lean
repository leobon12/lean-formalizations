/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux40FullErase
import InteractingSLE.Spec.Sec7.PocketLife
import InteractingSLE.Spec.Sec7.R7Aux131Good

/-!
# Supplement §5.4: the erasure of a mixed or outer pocket from its gap and visit-interval facts

Packet PROVE-R7-STOPIN. Supplement §5.4, "Erasure, relative prime ends, and the relative driver"
(`source/spec/p433-480.md` L990–L996, p. 474):

> "Use the clock `ℓ(t) = ∫_τ^t e^{−v} 1_{η(v) ∈ C} dv`. Collapse every closed gap and then delete constant pauses.
> Equal gap endpoints give a continuous curve from `y_C` to `x_C` with exactly the original open-`C` range in its
> original order. The continuity proof at accumulating gaps is the uniform continuity argument of Aux. 39; it does not
> use attachment-parameter continuity."

The landed erasure (`Sec6.IsReversePocket.continuousOn_erasedPath`, Aux. lemma 40) is stated for a pocket whose two
sides are first visited in reverse order. A mixed or outer pocket of Theorem R.7 has an outer side that the
counterflow never visits away from the certified frontier, so `IsReversePocket` does not apply. The erasure itself
only uses four facts about the pocket, which this file isolates as `IsErasurePocket`:

* (JP1) every visit to the open pocket `C` happens in `(τ, σ)` (Consequence R.4, `τ = T(y_C)`, `σ = T(x_C)`);
* the first visits `η(τ) = y₀`, `η(σ) = x₀`, and `x₀` is not visited before `σ`;
* no terminal gap: every `[a, σ)`, `a ≥ τ`, contains a visit (R.4: "There is no positive terminal no-`C` interval
  before `σ` in a nondegenerate visited pocket");
* equal gap endpoints (§5.4, "Closed gaps have identical endpoints": `η(a) = η(b)` for every closed gap `[a, b]`).

From these, every result of Aux. lemma 40 follows by the landed proof (copied here with the four facts in place of the
reverse-visit argument): the clock reaches a positive terminal value, **the erased path is continuous on `[0, ℓ(σ)]`
from `y₀` to `x₀`** (`IsErasurePocket.continuousOn_erasedPath`), it stays in `C̄ ∖ {x₀}` before its end, and erasure
changes no range in `C` ((GC2), `erasedPath_image_inter`). Consequences for the relative traversal
`relCurve (ψ ∘ γ̂_C) ℓ(σ)` in a Jordan coordinate `ψ` (`x₀ ↦ ∞`, `y₀ ↦ 0`):

* **transience** (Theorem R.7's proof: "its relative trace is unbounded as completion is approached"):
  `tendsto_norm_relCurve`;
* points of `ℍ` of arbitrarily large modulus at visit times: `exists_relCurve_mem_H_lt_norm`;
* **a driven curve** from Aux. lemma 41's Loewner conclusion on every `[0, S']`, `S' < ℓ(σ)` (the remaining part of
  §5.4, "The same Loewner criterion used in Aux. 41 now gives a continuous relative driver"): `isDrivenCurve_relCurve`;
* **`GoodR7`** (`goodR7_relCurve`).

`Sec6.IsReversePocket.isErasurePocket` shows that the four facts hold for every reverse-contained pocket under Aux.
lemma 37's attachment constancy, so the abstraction covers the landed contained case.

Conditional helpers with distinct names; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R7StopIn

open Sec6 PocketTraversal Lemma71C PocketLife R7Aux131

/-! ### The erasure facts of a pocket -/

/-- **The pathwise facts of a pocket used by its erasure** (supplement §5.4, Aux. lemmas 39–40): the trace `η` is
continuous on `[0, ∞)`, `C` is open, `0 ≤ τ < σ`, every visit to `C` is in `(τ, σ)` ((JP1), Consequence R.4),
`η(τ) = y₀` and `η(σ) = x₀` with `x₀` fresh at `σ`, every `[a, σ)` with `a ≥ τ` contains a visit (no terminal gap),
and every closed gap `[a, b] ⊆ [τ, σ)` whose right end is a limit of later visits and whose left end is `τ` or a limit
of visits has equal endpoint values ("Closed gaps have identical endpoints"). -/
structure IsErasurePocket (η : ℝ → ℂ) (C : Set ℂ) (x₀ y₀ : ℂ) (τ σ : ℝ) : Prop where
  cont : ContinuousOn η (Ici 0)
  isOpen : IsOpen C
  nonneg : 0 ≤ τ
  lt : τ < σ
  mem_Ioo : ∀ t, 0 ≤ t → η t ∈ C → t ∈ Ioo τ σ
  first_y : η τ = y₀
  first_x : η σ = x₀
  fresh_x : x₀ ∉ η '' Ico 0 σ
  noFinal : ∀ a ∈ Ico τ σ, ∃ t ∈ Ioo a σ, η t ∈ C
  gap : ∀ a b : ℝ, τ ≤ a → a < b → b < σ → (∀ t ∈ Icc a b, η t ∉ C) →
    b ∈ closure {t | a < t ∧ η t ∈ C} → (a = τ ∨ a ∈ closure {t | τ < t ∧ η t ∈ C}) → η a = η b

namespace IsErasurePocket

variable {η : ℝ → ℂ} {C : Set ℂ} {x₀ y₀ : ℂ} {τ σ : ℝ}

theorem nonneg_σ (hP : IsErasurePocket η C x₀ y₀ τ σ) : 0 ≤ σ := hP.nonneg.trans hP.lt.le

/-! ### The clock -/

theorem isOpen_visitSet (hP : IsErasurePocket η C x₀ y₀ τ σ) : IsOpen (visitSet η C τ σ) :=
  (hP.cont.mono fun _ ht => hP.nonneg.trans ht.1.le).isOpen_inter_preimage isOpen_Ioo hP.isOpen

theorem continuous_clock (hP : IsErasurePocket η C x₀ y₀ τ σ) : Continuous (pocketClock η C τ σ) :=
  continuous_erasureClock hP.isOpen_visitSet.measurableSet

theorem monotone_clock (hP : IsErasurePocket η C x₀ y₀ τ σ) : Monotone (pocketClock η C τ σ) :=
  monotone_erasureClock hP.isOpen_visitSet.measurableSet

theorem clock_τ : pocketClock η C τ σ τ = 0 := intervalIntegral.integral_same

theorem clock_nonneg (hP : IsErasurePocket η C x₀ y₀ τ σ) {t : ℝ} (ht : τ ≤ t) : 0 ≤ pocketClock η C τ σ t :=
  clock_τ (η := η) (C := C) (σ := σ) ▸ hP.monotone_clock ht

theorem mem_visitSet (hP : IsErasurePocket η C x₀ y₀ τ σ) {t : ℝ} (ht : 0 ≤ t) (htC : η t ∈ C) :
    t ∈ visitSet η C τ σ := ⟨hP.mem_Ioo t ht htC, htC⟩

theorem clock_lt_of_mem (hP : IsErasurePocket η C x₀ y₀ τ σ) {a b t : ℝ} (hta : a < t) (htb : t < b)
    (htI : t ∈ visitSet η C τ σ) : pocketClock η C τ σ a < pocketClock η C τ σ b := by
  refine lt_of_le_of_ne (hP.monotone_clock (hta.trans htb).le) fun h => ?_
  have := (erasureClock_eq_iff hP.isOpen_visitSet (hta.trans htb)).1 h
  exact Set.disjoint_left.1 this ⟨hta, htb⟩ htI

theorem exists_mem_of_clock_lt (hP : IsErasurePocket η C x₀ y₀ τ σ) {a b : ℝ} (hab : a < b)
    (h : pocketClock η C τ σ a ≠ pocketClock η C τ σ b) : ∃ t ∈ Ioo a b, t ∈ visitSet η C τ σ := by
  by_contra hne
  push Not at hne
  exact h ((erasureClock_eq_iff hP.isOpen_visitSet hab).2 (Set.disjoint_left.2 fun t ht htI => hne t ht htI))

theorem clock_lt_of_mem_visitSet (hP : IsErasurePocket η C x₀ y₀ τ σ) {t t' : ℝ} (htI : t ∈ visitSet η C τ σ)
    (htt' : t < t') : pocketClock η C τ σ t < pocketClock η C τ σ t' := by
  obtain ⟨ε, hε, hεI⟩ := Metric.isOpen_iff.1 hP.isOpen_visitSet t htI
  set t'' := min (t + ε / 2) ((t + t') / 2) with ht''
  have h1 : t < t'' := lt_min (by linarith) (by linarith)
  have h2 : t'' < t' := (min_le_right _ _).trans_lt (by linarith)
  have h3 : t'' ∈ visitSet η C τ σ := hεI (by
    rw [mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
    exact (sub_le_sub_right (min_le_left _ _) t).trans_lt (by linarith))
  refine lt_of_lt_of_le ?_ (hP.monotone_clock h2.le)
  obtain ⟨δ, hδ, hδI⟩ := Metric.isOpen_iff.1 hP.isOpen_visitSet t'' h3
  set m := max ((t + t'') / 2) (t'' - δ / 2) with hm
  have hm1 : t < m := lt_max_of_lt_left (by linarith)
  have hm2 : m < t'' := max_lt (by linarith) (by linarith)
  refine hP.clock_lt_of_mem hm1 hm2 ?_
  exact hδI (by
    rw [mem_ball, Real.dist_eq, abs_of_neg (by linarith), neg_sub]
    have : t'' - δ / 2 ≤ m := le_max_right _ _
    linarith)

/-! ### Right endpoints of fibres -/

theorem fibre_mem (hP : IsErasurePocket η C x₀ y₀ τ σ) (v : ℝ) : pocketFibre η C τ σ v ∈ Icc τ σ :=
  fibreRight_mem hP.continuous_clock hP.lt.le v

theorem clock_fibre (hP : IsErasurePocket η C x₀ y₀ τ σ) {v : ℝ} (hv : v ∈ Icc 0 (pocketClock η C τ σ σ)) :
    pocketClock η C τ σ (pocketFibre η C τ σ v) = v :=
  clock_fibreRight hP.continuous_clock hP.lt.le (by rw [clock_τ]; exact hv)

theorem monotone_fibre (hP : IsErasurePocket η C x₀ y₀ τ σ) : Monotone (pocketFibre η C τ σ) :=
  monotone_fibreRight hP.lt.le

theorem lt_clock_of_fibre_lt (hP : IsErasurePocket η C x₀ y₀ τ σ) {v : ℝ} (hv : 0 ≤ v) {t : ℝ}
    (ht : t ∈ Ioc (pocketFibre η C τ σ v) σ) : v < pocketClock η C τ σ t := by
  by_contra h
  push Not at h
  have hτt : τ ≤ t := (hP.fibre_mem v).1.trans ht.1.le
  have := le_fibreRight (ℓ := pocketClock η C τ σ) (v := v) ⟨hτt, ht.2⟩ (by rw [clock_τ, max_eq_left hv]; exact h)
  exact absurd ht.1 (not_lt.2 this)

theorem mem_closure_of_right (hP : IsErasurePocket η C x₀ y₀ τ σ) {b : ℝ} (hbσ : b < σ)
    (h : ∀ t ∈ Ioc b σ, pocketClock η C τ σ b < pocketClock η C τ σ t) :
    b ∈ closure {t | b < t ∧ η t ∈ C} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set t := min (b + ε / 2) σ with htdef
  have hbt : b < t := lt_min (by linarith) hbσ
  obtain ⟨t', ht', ht'I⟩ := hP.exists_mem_of_clock_lt hbt (h t ⟨hbt, min_le_right _ _⟩).ne
  refine ⟨t', ⟨ht'.1, ht'I.2⟩, ?_⟩
  rw [Real.dist_eq, abs_of_neg (by linarith [ht'.1]), neg_sub]
  have : t ≤ b + ε / 2 := min_le_left _ _
  linarith [ht'.2]

theorem mem_closure_of_left (hP : IsErasurePocket η C x₀ y₀ τ σ) {s a : ℝ} (hsa : s < a)
    (h : ∀ t ∈ Ico s a, pocketClock η C τ σ t < pocketClock η C τ σ a) :
    a ∈ closure {t | s < t ∧ η t ∈ C} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set t := max (a - ε / 2) s with htdef
  have hta : t < a := max_lt (by linarith) hsa
  obtain ⟨t', ht', ht'I⟩ := hP.exists_mem_of_clock_lt hta (h t ⟨le_max_right _ _, hta⟩).ne
  refine ⟨t', ⟨(le_max_right _ _).trans_lt ht'.1, ht'I.2⟩, ?_⟩
  rw [Real.dist_eq, abs_of_pos (by linarith [ht'.2])]
  have : a - ε / 2 ≤ t := le_max_left _ _
  linarith [ht'.1]

theorem exists_mem_Ioo_of_mem (hP : IsErasurePocket η C x₀ y₀ τ σ) {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    (htI : t ∈ visitSet η C τ σ) : ∃ t' ∈ Ioo a b, t' ∈ visitSet η C τ σ := by
  obtain ⟨ε, hε, hεI⟩ := Metric.isOpen_iff.1 hP.isOpen_visitSet t htI
  rcases lt_or_eq_of_le ht.2 with htb | htb
  · set t' := min (t + ε / 2) ((t + b) / 2) with ht'
    have h1 : t < t' := lt_min (by linarith) (by linarith)
    refine ⟨t', ⟨ht.1.trans_lt h1, (min_le_right _ _).trans_lt (by linarith)⟩, hεI ?_⟩
    rw [mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
    exact (sub_le_sub_right (min_le_left _ _) t).trans_lt (by linarith)
  · set t' := max (t - ε / 2) ((a + t) / 2) with ht'
    have hat : a < t := by rw [htb]; exact hab
    have h1 : t' < t := max_lt (by linarith) (by linarith)
    refine ⟨t', ⟨lt_max_of_lt_right (by linarith), htb ▸ h1⟩, hεI ?_⟩
    rw [mem_ball, Real.dist_eq, abs_of_neg (by linarith), neg_sub]
    have : t - ε / 2 ≤ t' := le_max_left _ _
    linarith

/-- **A nondegenerate maximal clock fibre** `[a, b]` of `[s, S]` (as `Sec6.IsReversePocket.maximal_fibre`). -/
theorem maximal_fibre (hP : IsErasurePocket η C x₀ y₀ τ σ) {s S : ℝ} (hτs : τ ≤ s)
    (hS : ∀ t ∈ Ioc S σ, pocketClock η C τ σ S < pocketClock η C τ σ t) {a b : ℝ}
    (ha : a ∈ Icc s S) (hb : b ∈ Icc s S) (hab : a < b) (hbσ : b < σ)
    (hℓ : pocketClock η C τ σ a = pocketClock η C τ σ b)
    (hmax : ∀ t ∈ Icc s S, pocketClock η C τ σ t = pocketClock η C τ σ a → t ∈ Icc a b) :
    (∀ t ∈ Icc a b, η t ∉ C) ∧ b ∈ closure {t | a < t ∧ η t ∈ C} ∧
      (a = s ∨ a ∈ closure {t | s < t ∧ η t ∈ C}) := by
  refine ⟨fun t ht htC => ?_, ?_, ?_⟩
  · have htI := hP.mem_visitSet (hP.nonneg.trans (hτs.trans (ha.1.trans ht.1))) htC
    obtain ⟨t', ht', ht'I⟩ := hP.exists_mem_Ioo_of_mem hab ht htI
    exact (hP.clock_lt_of_mem ht'.1 ht'.2 ht'I).ne hℓ
  · refine closure_mono (s := {t | b < t ∧ η t ∈ C}) (t := {t | a < t ∧ η t ∈ C})
      (fun t ht => ⟨hab.trans ht.1, ht.2⟩) (hP.mem_closure_of_right hbσ ?_)
    intro t ht
    by_cases htS : t ≤ S
    · refine lt_of_le_of_ne (hP.monotone_clock ht.1.le) fun h => ?_
      have := hmax t ⟨hb.1.trans ht.1.le, htS⟩ (h.symm.trans hℓ.symm)
      exact absurd this.2 (not_le.2 ht.1)
    · push Not at htS
      exact (hP.monotone_clock hb.2).trans_lt (hS t ⟨htS, ht.2⟩)
  · rcases eq_or_lt_of_le ha.1 with h | h
    · exact Or.inl h.symm
    · refine Or.inr (hP.mem_closure_of_left h fun t ht => lt_of_le_of_ne (hP.monotone_clock ht.2.le) fun h' => ?_)
      have := hmax t ⟨ht.1, ht.2.le.trans ha.2⟩ h'
      exact absurd this.1 (not_le.2 ht.2)

/-- **There is no final gap**: `ℓ(a) < ℓ(σ)` for every `a ∈ [τ, σ)`. -/
theorem clock_lt_clock_σ (hP : IsErasurePocket η C x₀ y₀ τ σ) {a : ℝ} (ha : a ∈ Ico τ σ) :
    pocketClock η C τ σ a < pocketClock η C τ σ σ := by
  obtain ⟨t, ht, htC⟩ := hP.noFinal a ha
  exact hP.clock_lt_of_mem ht.1 ht.2 (hP.mem_visitSet (hP.nonneg.trans (ha.1.trans ht.1.le)) htC)

/-- The clock reaches a positive terminal value. -/
theorem clock_σ_pos (hP : IsErasurePocket η C x₀ y₀ τ σ) : 0 < pocketClock η C τ σ σ := by
  have := hP.clock_lt_clock_σ ⟨le_rfl, hP.lt⟩
  rwa [clock_τ] at this

theorem fibre_lt_σ (hP : IsErasurePocket η C x₀ y₀ τ σ) {v : ℝ} (hv : v ∈ Ico 0 (pocketClock η C τ σ σ)) :
    pocketFibre η C τ σ v < σ := by
  refine lt_of_le_of_ne (hP.fibre_mem v).2 fun h => ?_
  have := hP.clock_fibre ⟨hv.1, hv.2.le⟩
  rw [h] at this
  exact hv.2.ne this.symm

theorem fibre_clock_σ (hP : IsErasurePocket η C x₀ y₀ τ σ) :
    pocketFibre η C τ σ (pocketClock η C τ σ σ) = σ := by
  refine le_antisymm (hP.fibre_mem _).2 (not_lt.1 fun h => ?_)
  have h1 := hP.clock_fibre ⟨hP.clock_σ_pos.le, le_rfl⟩
  have h2 := hP.clock_lt_clock_σ ⟨(hP.fibre_mem _).1, h⟩
  rw [h1] at h2
  exact lt_irrefl _ h2

theorem fibre_clock_of_mem (hP : IsErasurePocket η C x₀ y₀ τ σ) {t : ℝ} (htI : t ∈ visitSet η C τ σ) :
    pocketFibre η C τ σ (pocketClock η C τ σ t) = t := by
  have htm : t ∈ Icc τ σ := ⟨htI.1.1.le, htI.1.2.le⟩
  refine le_antisymm (not_lt.1 fun h => ?_) (fibreRight_clock htm)
  have hm := fibreRight_mem_set (ℓ := pocketClock η C τ σ) hP.continuous_clock hP.lt.le (pocketClock η C τ σ t)
  rw [max_eq_left (hP.monotone_clock htm.1)] at hm
  · exact absurd hm.2 (not_le.2 (hP.clock_lt_of_mem_visitSet htI h))

theorem clock_lt_of_fibre (hP : IsErasurePocket η C x₀ y₀ τ σ) {v : ℝ} (hv : v ∈ Icc 0 (pocketClock η C τ σ σ)) :
    ∀ t ∈ Ioc (pocketFibre η C τ σ v) σ, pocketClock η C τ σ (pocketFibre η C τ σ v) < pocketClock η C τ σ t :=
  fun t ht => by rw [hP.clock_fibre hv]; exact hP.lt_clock_of_fibre_lt hv.1 ht

/-- **(GC1) for the erasure**: the trace takes the same value at the two ends of every nondegenerate maximal fibre
of the clock in `[τ, S]`. -/
theorem gc1 (hP : IsErasurePocket η C x₀ y₀ τ σ) {S : ℝ} (hSσ : S ≤ σ)
    (hS : ∀ t ∈ Ioc S σ, pocketClock η C τ σ S < pocketClock η C τ σ t) :
    ∀ a ∈ Icc τ S, ∀ b ∈ Icc τ S, a < b → pocketClock η C τ σ a = pocketClock η C τ σ b →
      (∀ t ∈ Icc τ S, pocketClock η C τ σ t = pocketClock η C τ σ a → t ∈ Icc a b) → η a = η b := by
  intro a ha b hb hab hℓ hmax
  have hbσ : b < σ := by
    refine lt_of_le_of_ne (hb.2.trans hSσ) fun h => ?_
    rw [h] at hℓ
    exact (hP.clock_lt_clock_σ ⟨ha.1, hab.trans_le (hb.2.trans hSσ)⟩).ne hℓ
  obtain ⟨hgap, hbcl, hacl⟩ := hP.maximal_fibre le_rfl hS ha hb hab hbσ hℓ hmax
  exact hP.gap a b ha.1 hab hbσ hgap hbcl hacl

/-- **Aux. lemma 40's continuous erasure for the pocket**: `γ̂_C` is continuous on `[0, ℓ(σ)]`. -/
theorem continuousOn_erasedPath (hP : IsErasurePocket η C x₀ y₀ τ σ) :
    ContinuousOn (erasedPath η C τ σ) (Icc 0 (pocketClock η C τ σ σ)) := by
  have h := continuousOn_comp_fibreRight hP.continuous_clock hP.monotone_clock hP.lt.le
    (hP.cont.mono fun t ht => hP.nonneg.trans ht.1) (hP.gc1 le_rfl fun t ht => absurd ht.2 (not_le.2 ht.1))
  rwa [clock_τ] at h

/-- The erased path starts at `y₀`. -/
theorem erasedPath_zero (hP : IsErasurePocket η C x₀ y₀ τ σ) : erasedPath η C τ σ 0 = y₀ := by
  have hpos := hP.clock_σ_pos
  have hm := hP.fibre_mem 0
  have hc0 := hP.clock_fibre ⟨le_rfl, hpos.le⟩
  rcases eq_or_lt_of_le hm.1 with h | h
  · rw [erasedPath, ← h, hP.first_y]
  · have hlt := hP.fibre_lt_σ ⟨le_rfl, hpos⟩
    rw [erasedPath, ← hP.first_y]
    refine (hP.gc1 hlt.le (hP.clock_lt_of_fibre ⟨le_rfl, hpos.le⟩) τ ⟨le_rfl, h.le⟩ _ ⟨h.le, le_rfl⟩ h
      (by rw [hc0, clock_τ]) fun t ht _ => ⟨ht.1, ht.2⟩).symm ▸ rfl

/-- The erased path ends at `x₀`. -/
theorem erasedPath_clock_σ (hP : IsErasurePocket η C x₀ y₀ τ σ) :
    erasedPath η C τ σ (pocketClock η C τ σ σ) = x₀ := by
  rw [erasedPath, hP.fibre_clock_σ, hP.first_x]

theorem mem_closure_of_mem_closure_visits (hP : IsErasurePocket η C x₀ y₀ τ σ) {s a : ℝ} (hs : 0 ≤ s)
    (ha : a ∈ closure {t | s < t ∧ η t ∈ C}) : η a ∈ closure C := by
  have hsub : {t | s < t ∧ η t ∈ C} ⊆ Ici 0 := fun t ht => hs.trans ht.1.le
  have ha0 : a ∈ Ici (0 : ℝ) := closure_minimal hsub isClosed_Ici ha
  have hc : ContinuousWithinAt η {t | s < t ∧ η t ∈ C} a := (hP.cont a ha0).mono hsub
  exact closure_mono (image_subset_iff.2 fun t ht => ht.2) (hc.mem_closure_image ha)

/-- Before its terminal time the erased path is in `C̄ ∖ {x₀}`. -/
theorem erasedPath_mem (hP : IsErasurePocket η C x₀ y₀ τ σ) {v : ℝ} (hv : v ∈ Ico 0 (pocketClock η C τ σ σ)) :
    erasedPath η C τ σ v ∈ closure C \ {x₀} := by
  have hlt := hP.fibre_lt_σ hv
  have hm := hP.fibre_mem v
  have h0 : 0 ≤ pocketFibre η C τ σ v := hP.nonneg.trans hm.1
  refine ⟨hP.mem_closure_of_mem_closure_visits h0
    (hP.mem_closure_of_right hlt (hP.clock_lt_of_fibre ⟨hv.1, hv.2.le⟩)), fun h => ?_⟩
  exact hP.fresh_x ⟨_, ⟨h0, hlt⟩, h⟩

/-- **(GC2)**: erasure changes no range in `C`: `γ̂_C([0, u]) ∩ C = R_{fR(u)} ∩ C`. -/
theorem erasedPath_image_inter (hP : IsErasurePocket η C x₀ y₀ τ σ) {u : ℝ}
    (hu : u ∈ Icc 0 (pocketClock η C τ σ σ)) :
    erasedPath η C τ σ '' Icc 0 u ∩ C = η '' Icc 0 (pocketFibre η C τ σ u) ∩ C := by
  ext z
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hz⟩
    exact ⟨⟨_, ⟨hP.nonneg.trans (hP.fibre_mem v).1, hP.monotone_fibre hv.2⟩, rfl⟩, hz⟩
  · rintro ⟨⟨t, ht, rfl⟩, hz⟩
    have htI := hP.mem_visitSet ht.1 hz
    refine ⟨⟨pocketClock η C τ σ t, ⟨hP.clock_nonneg htI.1.1.le, ?_⟩, ?_⟩, hz⟩
    · rw [← hP.clock_fibre hu]; exact hP.monotone_clock ht.2
    · rw [erasedPath, hP.fibre_clock_of_mem htI]

end IsErasurePocket

/-! ### The landed contained case -/

/-- **A reverse-contained pocket has the erasure facts** under Aux. lemma 37's attachment constancy (the landed
Aux. lemmas 39–40: (JP1), no final gap, and Propositions 1.5–1.6's gap equality). -/
theorem isErasurePocket_of_isReversePocket {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ β : ℝ → ℂ} {τ σ : ℝ}
    (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ) :
    IsErasurePocket η C (α₁ 0) (α₁ 1) τ σ := by
  refine ⟨hP.trace.2.1, hP.isOpen, hP.nonneg, hP.τ_lt_σ, fun t ht htC => hP.mem_Ioo_of_mem ht htC, hP.first_y,
    hP.first_x, hP.fresh_x, fun a ha => ?_, fun a b hτa hab hbσ hgap hb ha => ?_⟩
  · obtain ⟨t, ht, htI⟩ := hP.exists_mem_of_clock_lt ha.2 (hP.clock_lt_clock_σ hAC ha).ne
    exact ⟨t, ht, htI.2⟩
  · rcases eq_or_lt_of_le (hP.nonneg.trans hτa) with h0 | h0
    · have hτ0 : τ = 0 := le_antisymm (h0 ▸ hτa) hP.nonneg
      subst h0
      exact hP.gap_eq_seed hAC hτ0 hab hbσ hgap hb
    · have ha' : a = τ ∨ a ∈ closure {t | 0 < t ∧ η t ∈ C} := ha.imp_right fun h =>
        closure_mono (s := {t | τ < t ∧ η t ∈ C}) (t := {t | 0 < t ∧ η t ∈ C})
          (fun t ht => ⟨hP.nonneg.trans_lt ht.1, ht.2⟩) h
      exact (hP.gap_eq hAC le_rfl h0 hτa hab hbσ hgap ha' hb).2

/-! ### The relative traversal -/

section Traversal

variable {η : ℝ → ℂ} {C : Set ℂ} {x₀ y₀ : ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}

/-- **The relative traversal** of the pocket in a coordinate `ψ`: the erased path read in `ψ`, on `[0, ∞)` through
the relative clock `u ↦ ℓ(σ) u/(1 + u)` (`relCurve`). -/
abbrev relTrav (η : ℝ → ℂ) (C : Set ℂ) (τ σ : ℝ) (ψ : ℂ → ℂ) : ℝ → ℂ :=
  relCurve (fun v => ψ (erasedPath η C τ σ v)) (pocketClock η C τ σ σ)

namespace IsErasurePocket

/-- The terminal point is not in the open pocket. -/
theorem notMem_x (hP : IsErasurePocket η C x₀ y₀ τ σ) : x₀ ∉ C := fun h =>
  (hP.mem_Ioo σ hP.nonneg_σ (hP.first_x ▸ h)).2.ne rfl

/-- **The erased path in the coordinate tends to `∞` at its terminal clock**, when `ψ → ∞` at `x₀` within
`C̄ ∖ {x₀}`. -/
theorem tendsto_ζ (hP : IsErasurePocket η C x₀ y₀ τ σ) (hψ : Tendsto ψ (𝓝[closure C \ {x₀}] x₀) (cobounded ℂ)) :
    Tendsto (fun v => ψ (erasedPath η C τ σ v)) (𝓝[<] (pocketClock η C τ σ σ)) (cobounded ℂ) := by
  set Lc := pocketClock η C τ σ σ with hLc
  have hL : 0 < Lc := hP.clock_σ_pos
  have hmem : Icc 0 Lc ∈ 𝓝[<] Lc := mem_of_superset (Ioo_mem_nhdsLT hL) Ioo_subset_Icc_self
  have hcw : ContinuousWithinAt (erasedPath η C τ σ) (Iio Lc) Lc :=
    (hP.continuousOn_erasedPath Lc ⟨hL.le, le_rfl⟩).mono_of_mem_nhdsWithin hmem
  have h1 : Tendsto (erasedPath η C τ σ) (𝓝[<] Lc) (𝓝 x₀) := by
    have := hcw.tendsto
    rwa [hP.erasedPath_clock_σ] at this
  have h2 : Tendsto (erasedPath η C τ σ) (𝓝[<] Lc) (𝓝[closure C \ {x₀}] x₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨h1, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT hL] with v hv
    exact hP.erasedPath_mem ⟨hv.1.le, hv.2⟩
  exact hψ.comp h2

/-- **Transience of the relative traversal** (Theorem R.7's proof: "its relative trace is unbounded as completion is
approached"). -/
theorem tendsto_norm_relTrav (hP : IsErasurePocket η C x₀ y₀ τ σ)
    (hψ : Tendsto ψ (𝓝[closure C \ {x₀}] x₀) (cobounded ℂ)) :
    Tendsto (fun u => ‖relTrav η C τ σ ψ u‖) atTop atTop :=
  tendsto_norm_atTop_iff_cobounded.2 ((hP.tendsto_ζ hψ).comp (tendsto_clockOf hP.clock_σ_pos))

/-- The relative traversal passes through `ψ(η t)` at an interior visit time `t`. -/
theorem relTrav_of_mem_visitSet (hP : IsErasurePocket η C x₀ y₀ τ σ) {t : ℝ} (htI : t ∈ visitSet η C τ σ) :
    0 ≤ pocketClock η C τ σ t / (pocketClock η C τ σ σ - pocketClock η C τ σ t) ∧
      relTrav η C τ σ ψ (pocketClock η C τ σ t / (pocketClock η C τ σ σ - pocketClock η C τ σ t)) = ψ (η t) := by
  have hL := hP.clock_σ_pos
  have hv0 := hP.clock_nonneg htI.1.1.le
  have hv := hP.clock_lt_clock_σ ⟨htI.1.1.le, htI.1.2⟩
  refine ⟨div_sub_nonneg hv0 hv, ?_⟩
  simp only [relTrav, relCurve, clockOf_div_sub hL hv, erasedPath, hP.fibre_clock_of_mem htI]

/-- **Points of `ℍ` of arbitrarily large modulus** on the relative traversal (proof of Aux. lemma 125: "`|X_C(s)| →
∞`"), at interior visit times close to `σ`. -/
theorem exists_relTrav_mem_H_lt_norm (hP : IsErasurePocket η C x₀ y₀ τ σ) (hψH : MapsTo ψ C H)
    (hψ : Tendsto ψ (𝓝[closure C \ {x₀}] x₀) (cobounded ℂ)) (M : ℝ) :
    ∃ u, 0 ≤ u ∧ relTrav η C τ σ ψ u ∈ H ∧ M < ‖relTrav η C τ σ ψ u‖ := by
  have hev : ∀ᶠ z in 𝓝[closure C \ {x₀}] x₀, M < ‖ψ z‖ :=
    (tendsto_norm_cobounded_atTop.comp hψ).eventually (eventually_gt_atTop M)
  obtain ⟨ε, hε, hεM⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
  have hηc : ContinuousWithinAt η (Ici 0) σ := hP.cont σ hP.nonneg_σ
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousWithinAt_iff.1 hηc ε hε
  set a := max τ (σ - δ / 2) with ha
  have haσ : a < σ := max_lt hP.lt (by linarith)
  obtain ⟨t, ht, htC⟩ := hP.noFinal a ⟨le_max_left _ _, haσ⟩
  have ht0 : 0 ≤ t := hP.nonneg.trans ((le_max_left _ _).trans ht.1.le)
  have htI := hP.mem_visitSet ht0 htC
  have hdt : dist t σ < δ := by
    rw [Real.dist_eq, abs_of_neg (by linarith [ht.2])]
    have : σ - δ / 2 ≤ a := le_max_right _ _
    linarith [ht.1]
  have hηt : dist (η t) x₀ < ε := by
    have := hδε ht0 hdt
    rwa [hP.first_x] at this
  have hne : η t ≠ x₀ := fun h => hP.notMem_x (h ▸ htC)
  have hMt : M < ‖ψ (η t)‖ := hεM hηt ⟨subset_closure htC, hne⟩
  obtain ⟨hu, he⟩ := hP.relTrav_of_mem_visitSet (ψ := ψ) htI
  exact ⟨_, hu, he ▸ hψH htC, he ▸ hMt⟩

/-- **The relative traversal is a driven curve** from Aux. lemma 41's Loewner conclusion on every `[0, S']`,
`0 < S' < ℓ(σ)` (§5.4: "The same Loewner criterion used in Aux. 41 now gives a continuous relative driver"), for a
coordinate continuous on `C̄ ∖ {x₀}` with `ψ(y₀) = 0`. -/
theorem isDrivenCurve_relTrav (hP : IsErasurePocket η C x₀ y₀ τ σ) (hψc : ContinuousOn ψ (closure C \ {x₀}))
    (hψ0 : ψ y₀ = 0)
    (hloc : ∀ S' : ℝ, 0 < S' → S' < pocketClock η C τ σ σ → ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧
      ∃ σ' : ℝ → ℝ, σ' 0 = 0 ∧ StrictMonoOn σ' (Icc 0 S') ∧ ContinuousOn σ' (Icc 0 S') ∧
      ∀ t ∈ Icc 0 S', QuantumZipper.fwdHull W (σ' t) = fillH ((fun v => ψ (erasedPath η C τ σ v)) '' Icc 0 t)) :
    IsDrivenCurve (relTrav η C τ σ ψ) :=
  PocketTraversal.isDrivenCurve_relCurve hP.clock_σ_pos
    (hψc.comp (hP.continuousOn_erasedPath.mono Ico_subset_Icc_self) fun _ hv => hP.erasedPath_mem hv)
    (by simp only [hP.erasedPath_zero, hψ0]) hloc

/-- **`GoodR7` for the relative traversal** (Theorem R.7: "In its entry-to-exit half-plane chart the relative trace
is continuous on `[0, ∞)` and tends to infinity"): with infinite capacity lifetime, the capacity reparametrization of
a driven relative traversal is a continuous generating trace on `[0, ∞)` tending to `∞`. -/
theorem goodR7_relTrav (hP : IsErasurePocket η C x₀ y₀ τ σ) (hγ : IsDrivenCurve (relTrav η C τ σ ψ))
    (hψ : Tendsto ψ (𝓝[closure C \ {x₀}] x₀) (cobounded ℂ)) (hL : capLife (relTrav η C τ σ ψ) = ⊤) :
    GoodR7 (fun t => segDriver (relTrav η C τ σ ψ) t) ⊤ :=
  goodR7_of_tendsto hγ (hP.tendsto_norm_relTrav hψ) hL

end IsErasurePocket

end Traversal

end InteractingSLE.Sec7.R7StopIn
