/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7StopInClip
import InteractingSLE.Spec.Sec6.Aux40InfLoewner

/-!
# Supplement §5.4 for a pocket opening at the flow seed: the erasure with `σ = ∞`

Packet PROVE-R7-STOPIN. Supplement §5.3–§5.4 (`source/spec/p433-480.md` L961–L996, pp. 472–474): "Set `τ = T(y_C)` and
`σ = T(x_C)` […] allowing the terminal original-target time for `σ`." When the selected pocket of Theorem R.7 opens at
the flow seed (in the counterflow chart `m(z) = −1/z` its junction `x_C` is the original target `∞`, as happens when the
two walls meet only at their common seed), the visit interval is `(τ, ∞)` and the erasure has a terminal clock value
`ℓ(∞)`. As for the bounded pocket (`IsErasurePocket`), the landed erasure at infinity
(`Sec6.IsReversePocketInf`, Aux. lemma 40 with `σ = ∞`) uses only four facts, isolated here as
**`IsErasurePocketInf`**: the visits are after `τ = T(y₀)` ((JP1) with `σ = ∞`), `η(τ) = y₀`, visits at arbitrarily
large times (no final gap at infinity), and equal endpoints of closed gaps.

Results (namespace `IsErasurePocketInf`): the clock and fibre API, (GC1), **the continuous erasure on `[0, ℓ(∞))`**
(`continuousOn_erasedPath`) from `y₀`, in `C̄`, (GC2); with a transient counterflow, **`γ̂_C → ∞` at `ℓ(∞)`** and, in a
Jordan coordinate at infinity, the transience of the relative traversal (`tendsto_norm_relTravInf`), points of `ℍ` of
large modulus, the driven curve from Aux. 41's Loewner conclusion and **`GoodR7`**.
`isErasurePocketInf_of_isReversePocketInf` recovers the landed contained case. `lt_of_frontier_visit` (Consequence
R.4 before `τ`, abstractly) and
`noFinalInf_of_attach` (no final gap at infinity from Aux. 37 along one barrier, the landed argument of
`Sec6.IsReversePocketInf.clock_lt_clockEnd`) supply two of the four facts for the actual pockets.

Conditional helpers with distinct names; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R7StopIn

open Sec6 PocketTraversal Lemma71C PocketLife R7Aux131

/-- **The pathwise facts of a pocket opening at the flow seed used by its erasure** (`σ = ∞`): `η` continuous on
`[0, ∞)`, `C` open, `0 ≤ τ`, every visit to `C` after `τ` ((JP1)), `η(τ) = y₀`, visits after every time
(no final gap at infinity), and equal endpoints of closed gaps (§5.4). -/
structure IsErasurePocketInf (η : ℝ → ℂ) (C : Set ℂ) (y₀ : ℂ) (τ : ℝ) : Prop where
  cont : ContinuousOn η (Ici 0)
  isOpen : IsOpen C
  nonneg : 0 ≤ τ
  mem_Ioi : ∀ t, 0 ≤ t → η t ∈ C → τ < t
  first_y : η τ = y₀
  noFinal : ∀ a, τ ≤ a → ∃ t > a, η t ∈ C
  gap : ∀ a b : ℝ, τ ≤ a → a < b → (∀ t ∈ Icc a b, η t ∉ C) →
    b ∈ closure {t | a < t ∧ η t ∈ C} → (a = τ ∨ a ∈ closure {t | τ < t ∧ η t ∈ C}) → η a = η b

namespace IsErasurePocketInf

variable {η : ℝ → ℂ} {C : Set ℂ} {y₀ : ℂ} {τ : ℝ}

theorem mem_closure_of_mem_closure_visits (hP : IsErasurePocketInf η C y₀ τ) {s a : ℝ} (hs : 0 ≤ s)
    (ha : a ∈ closure {t | s < t ∧ η t ∈ C}) : η a ∈ closure C := by
  have hsub : {t | s < t ∧ η t ∈ C} ⊆ Ici 0 := fun t ht => hs.trans ht.1.le
  have ha0 : a ∈ Ici (0 : ℝ) := closure_minimal hsub isClosed_Ici ha
  have hc : ContinuousWithinAt η {t | s < t ∧ η t ∈ C} a := (hP.cont a ha0).mono hsub
  exact closure_mono (image_subset_iff.2 fun t ht => ht.2) (hc.mem_closure_image ha)

theorem isOpen_visitSet (hP : IsErasurePocketInf η C y₀ τ) :
    IsOpen (visitSetInf η C τ) :=
  (hP.cont.mono fun _ ht => hP.nonneg.trans (le_of_lt ht)).isOpen_inter_preimage isOpen_Ioi
    hP.isOpen

theorem continuous_clock (hP : IsErasurePocketInf η C y₀ τ) :
    Continuous (pocketClockInf η C τ) :=
  continuous_erasureClock hP.isOpen_visitSet.measurableSet

theorem monotone_clock (hP : IsErasurePocketInf η C y₀ τ) :
    Monotone (pocketClockInf η C τ) :=
  monotone_erasureClock hP.isOpen_visitSet.measurableSet

theorem clock_τ : pocketClockInf η C τ τ = 0 := intervalIntegral.integral_same

theorem clock_nonneg (hP : IsErasurePocketInf η C y₀ τ) {t : ℝ} (ht : τ ≤ t) :
    0 ≤ pocketClockInf η C τ t := clock_τ (η := η) (C := C) ▸ hP.monotone_clock ht

/-- The clock is bounded by `e^{-τ}`. -/
theorem clock_le (hP : IsErasurePocketInf η C y₀ τ) (t : ℝ) :
    pocketClockInf η C τ t ≤ Real.exp (-τ) := by
  rcases le_total τ t with h | h
  · have h1 : pocketClockInf η C τ t ≤ ∫ s in τ..t, Real.exp (-s) :=
      intervalIntegral.integral_mono_on h
        (intervalIntegrable_indicator_exp hP.isOpen_visitSet.measurableSet τ t)
        ((Real.continuous_exp.comp continuous_neg).intervalIntegrable τ t)
        fun s _ => Set.indicator_le_self' (fun _ _ => (Real.exp_pos _).le) s
    have h2 : ∫ s in τ..t, Real.exp (-s) = Real.exp (-τ) - Real.exp (-t) := by
      rw [intervalIntegral.integral_comp_neg (fun s => Real.exp s), integral_exp]
    linarith [Real.exp_pos (-t)]
  · have := hP.monotone_clock h
    rw [clock_τ] at this
    linarith [Real.exp_pos (-τ)]

theorem bddAbove_clock (hP : IsErasurePocketInf η C y₀ τ) :
    BddAbove (range (pocketClockInf η C τ)) :=
  ⟨Real.exp (-τ), by rintro _ ⟨t, rfl⟩; exact hP.clock_le t⟩

theorem clock_le_clockEnd (hP : IsErasurePocketInf η C y₀ τ) (t : ℝ) :
    pocketClockInf η C τ t ≤ clockEnd η C τ :=
  le_ciSup hP.bddAbove_clock t

/-- Below the terminal value, the clock exceeds `v` at some time `T ≥ τ`. -/
theorem exists_clock_gt (hP : IsErasurePocketInf η C y₀ τ) {v : ℝ}
    (hv : v < clockEnd η C τ) : ∃ T, τ ≤ T ∧ v < pocketClockInf η C τ T := by
  obtain ⟨T, hT⟩ := exists_lt_of_lt_ciSup hv
  exact ⟨max T τ, le_max_right _ _, hT.trans_le (hP.monotone_clock (le_max_left _ _))⟩

/-- By (JP1) every visit to `C` is an interior-visit time. -/
theorem mem_visitSet (hP : IsErasurePocketInf η C y₀ τ) {t : ℝ} (ht : 0 ≤ t)
    (htC : η t ∈ C) : t ∈ visitSetInf η C τ := ⟨hP.mem_Ioi _ ht htC, htC⟩

/-- The clock increases strictly across a visit time. -/
theorem clock_lt_of_mem (hP : IsErasurePocketInf η C y₀ τ) {a b t : ℝ} (hta : a < t)
    (htb : t < b) (htI : t ∈ visitSetInf η C τ) :
    pocketClockInf η C τ a < pocketClockInf η C τ b := by
  refine lt_of_le_of_ne (hP.monotone_clock (hta.trans htb).le) fun h => ?_
  have := (erasureClock_eq_iff hP.isOpen_visitSet (hta.trans htb)).1 h
  exact Set.disjoint_left.1 this ⟨hta, htb⟩ htI

/-- If the clock increases on `[a, b]`, then `(a, b)` contains a visit time. -/
theorem exists_mem_of_clock_lt (hP : IsErasurePocketInf η C y₀ τ) {a b : ℝ} (hab : a < b)
    (h : pocketClockInf η C τ a ≠ pocketClockInf η C τ b) :
    ∃ t ∈ Ioo a b, t ∈ visitSetInf η C τ := by
  by_contra hne
  push Not at hne
  exact h ((erasureClock_eq_iff hP.isOpen_visitSet hab).2
    (Set.disjoint_left.2 fun t ht htI => hne t ht htI))

/-- A visit time is the right endpoint of its (singleton) clock fibre. -/
theorem clock_lt_of_mem_visitSet (hP : IsErasurePocketInf η C y₀ τ) {t t' : ℝ}
    (htI : t ∈ visitSetInf η C τ) (htt' : t < t') :
    pocketClockInf η C τ t < pocketClockInf η C τ t' := by
  obtain ⟨ε, hε, hεI⟩ := Metric.isOpen_iff.1 hP.isOpen_visitSet t htI
  set t'' := min (t + ε / 2) ((t + t') / 2) with ht''
  have h1 : t < t'' := lt_min (by linarith) (by linarith)
  have h2 : t'' < t' := (min_le_right _ _).trans_lt (by linarith)
  have h3 : t'' ∈ visitSetInf η C τ := hεI (by
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

/-- A visit time is before the terminal clock value. -/
theorem clock_lt_clockEnd_of_mem (hP : IsErasurePocketInf η C y₀ τ) {t : ℝ}
    (htI : t ∈ visitSetInf η C τ) : pocketClockInf η C τ t < clockEnd η C τ :=
  (hP.clock_lt_of_mem_visitSet htI (lt_add_one t)).trans_le (hP.clock_le_clockEnd _)

/-- A right endpoint `b` after which the clock increases is a limit of later visits. -/
theorem mem_closure_of_right (hP : IsErasurePocketInf η C y₀ τ) {b : ℝ}
    (h : ∀ t > b, pocketClockInf η C τ b < pocketClockInf η C τ t) :
    b ∈ closure {t | b < t ∧ η t ∈ C} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨t', ht', ht'I⟩ := hP.exists_mem_of_clock_lt (show b < b + ε / 2 by linarith)
    (h _ (by linarith)).ne
  refine ⟨t', ⟨ht'.1, ht'I.2⟩, ?_⟩
  rw [Real.dist_eq, abs_of_neg (by linarith [ht'.1]), neg_sub]
  linarith [ht'.2]

/-- A left endpoint `a > s` before which the clock is smaller is a limit of visits after `s`. -/
theorem mem_closure_of_left (hP : IsErasurePocketInf η C y₀ τ) {s a : ℝ} (hsa : s < a)
    (h : ∀ t ∈ Ico s a, pocketClockInf η C τ t < pocketClockInf η C τ a) :
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

/-- A visit time in `[a, b]` (`a < b`) gives a visit time in `(a, b)` (`I` is open). -/
theorem exists_mem_Ioo_of_mem (hP : IsErasurePocketInf η C y₀ τ) {a b t : ℝ} (hab : a < b)
    (ht : t ∈ Icc a b) (htI : t ∈ visitSetInf η C τ) :
    ∃ t' ∈ Ioo a b, t' ∈ visitSetInf η C τ := by
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

/-- **A nondegenerate maximal clock fibre** `[a, b]` of `[s, S]` (`τ ≤ s`, the clock increasing
after `S`): the trace avoids `C` on `[a, b]`, `b` is a limit of later visits, and `a = s` or `a`
is a limit of visits after `s`. -/
theorem maximal_fibre (hP : IsErasurePocketInf η C y₀ τ) {s S : ℝ} (hτs : τ ≤ s)
    (hS : ∀ t > S, pocketClockInf η C τ S < pocketClockInf η C τ t) {a b : ℝ}
    (ha : a ∈ Icc s S) (hb : b ∈ Icc s S) (hab : a < b)
    (hℓ : pocketClockInf η C τ a = pocketClockInf η C τ b)
    (hmax : ∀ t ∈ Icc s S, pocketClockInf η C τ t = pocketClockInf η C τ a → t ∈ Icc a b) :
    (∀ t ∈ Icc a b, η t ∉ C) ∧ b ∈ closure {t | a < t ∧ η t ∈ C} ∧
      (a = s ∨ a ∈ closure {t | s < t ∧ η t ∈ C}) := by
  refine ⟨fun t ht htC => ?_, ?_, ?_⟩
  · have htI := hP.mem_visitSet (hP.nonneg.trans (hτs.trans (ha.1.trans ht.1))) htC
    obtain ⟨t', ht', ht'I⟩ := hP.exists_mem_Ioo_of_mem hab ht htI
    exact (hP.clock_lt_of_mem ht'.1 ht'.2 ht'I).ne hℓ
  · refine closure_mono (s := {t | b < t ∧ η t ∈ C}) (t := {t | a < t ∧ η t ∈ C})
      (fun t ht => ⟨hab.trans ht.1, ht.2⟩) (hP.mem_closure_of_right ?_)
    intro t ht
    by_cases htS : t ≤ S
    · refine lt_of_le_of_ne (hP.monotone_clock (le_of_lt ht)) fun h => ?_
      have := hmax t ⟨hb.1.trans (le_of_lt ht), htS⟩ (h.symm.trans hℓ.symm)
      exact absurd this.2 (not_le.2 ht)
    · push Not at htS
      exact (hP.monotone_clock hb.2).trans_lt (hS t htS)
  · rcases eq_or_lt_of_le ha.1 with h | h
    · exact Or.inl h.symm
    · refine Or.inr (hP.mem_closure_of_left h fun t ht => lt_of_le_of_ne
        (hP.monotone_clock ht.2.le) fun h' => ?_)
      have := hmax t ⟨ht.1, ht.2.le.trans ha.2⟩ h'
      exact absurd this.1 (not_le.2 ht.2)

/-! ### Right endpoints of fibres -/

/-- The fibre endpoint on `[τ, ∞)` is the one in a window `[τ, T]` beyond which the clock
exceeds `v`. -/
theorem fibre_eq_fibreRight {v T : ℝ} (hv0 : 0 ≤ v)
    (hvT : ∀ t > T, v < pocketClockInf η C τ t) :
    pocketFibreInf η C τ v = fibreRight (pocketClockInf η C τ) τ T v := by
  unfold pocketFibreInf fibreRight
  congr 1
  ext t
  refine ⟨fun ht => ⟨⟨ht.1, not_lt.1 fun hTt => ?_⟩, ht.2⟩, fun ht => ⟨ht.1.1, ht.2⟩⟩
  have := ht.2
  rw [clock_τ, max_eq_left hv0] at this
  exact absurd this (not_le.2 (hvT t hTt))

theorem fibre_eq_fibreRight_of_lt (hP : IsErasurePocketInf η C y₀ τ) {v T : ℝ}
    (hv0 : 0 ≤ v) (hvT : v < pocketClockInf η C τ T) :
    pocketFibreInf η C τ v = fibreRight (pocketClockInf η C τ) τ T v :=
  fibre_eq_fibreRight hv0 fun _ ht => hvT.trans_le (hP.monotone_clock (le_of_lt ht))

theorem fibre_mem (hP : IsErasurePocketInf η C y₀ τ) {v : ℝ}
    (hv : v ∈ Ico 0 (clockEnd η C τ)) : τ ≤ pocketFibreInf η C τ v := by
  obtain ⟨T, hτT, hvT⟩ := hP.exists_clock_gt hv.2
  rw [hP.fibre_eq_fibreRight_of_lt hv.1 hvT]
  exact (fibreRight_mem hP.continuous_clock hτT v).1

theorem fibre_nonneg (hP : IsErasurePocketInf η C y₀ τ) {v : ℝ}
    (hv : v ∈ Ico 0 (clockEnd η C τ)) : 0 ≤ pocketFibreInf η C τ v :=
  hP.nonneg.trans (hP.fibre_mem hv)

theorem clock_fibre (hP : IsErasurePocketInf η C y₀ τ) {v : ℝ}
    (hv : v ∈ Ico 0 (clockEnd η C τ)) : pocketClockInf η C τ (pocketFibreInf η C τ v) = v := by
  obtain ⟨T, hτT, hvT⟩ := hP.exists_clock_gt hv.2
  rw [hP.fibre_eq_fibreRight_of_lt hv.1 hvT]
  exact clock_fibreRight hP.continuous_clock hτT (by rw [clock_τ]; exact ⟨hv.1, hvT.le⟩)

/-- After the right endpoint of the fibre of `v`, the clock exceeds `v`. -/
theorem lt_clock_of_fibre_lt (hP : IsErasurePocketInf η C y₀ τ) {v : ℝ}
    (hv : v ∈ Ico 0 (clockEnd η C τ)) {t : ℝ} (ht : pocketFibreInf η C τ v < t) :
    v < pocketClockInf η C τ t := by
  obtain ⟨T, hτT, hvT⟩ := hP.exists_clock_gt hv.2
  by_contra h
  push Not at h
  have hτt : τ ≤ t := (hP.fibre_mem hv).trans (le_of_lt ht)
  have hTt : t ≤ T := not_lt.1 fun hTt => absurd (hvT.trans_le (hP.monotone_clock hTt.le))
    (not_lt.2 h)
  rw [hP.fibre_eq_fibreRight_of_lt hv.1 hvT] at ht
  have := le_fibreRight (ℓ := pocketClockInf η C τ) (v := v) ⟨hτt, hTt⟩
    (by rw [clock_τ, max_eq_left hv.1]; exact h)
  exact absurd ht (not_lt.2 this)

/-- After the right endpoint of a fibre the clock increases. -/
theorem clock_lt_of_fibre (hP : IsErasurePocketInf η C y₀ τ) {v : ℝ}
    (hv : v ∈ Ico 0 (clockEnd η C τ)) :
    ∀ t > pocketFibreInf η C τ v,
      pocketClockInf η C τ (pocketFibreInf η C τ v) < pocketClockInf η C τ t := fun t ht => by
  rw [hP.clock_fibre hv]; exact hP.lt_clock_of_fibre_lt hv ht

theorem monotoneOn_fibre (hP : IsErasurePocketInf η C y₀ τ) :
    MonotoneOn (pocketFibreInf η C τ) (Ico 0 (clockEnd η C τ)) := by
  intro v hv w hw hvw
  obtain ⟨T, hτT, hwT⟩ := hP.exists_clock_gt hw.2
  rw [hP.fibre_eq_fibreRight_of_lt hv.1 (hvw.trans_lt hwT),
    hP.fibre_eq_fibreRight_of_lt hw.1 hwT]
  exact monotone_fibreRight hτT hvw

/-- A visit time is the right endpoint of its clock fibre. -/
theorem fibre_clock_of_mem (hP : IsErasurePocketInf η C y₀ τ) {t : ℝ}
    (htI : t ∈ visitSetInf η C τ) : pocketFibreInf η C τ (pocketClockInf η C τ t) = t := by
  have hv : pocketClockInf η C τ t ∈ Ico 0 (clockEnd η C τ) :=
    ⟨hP.clock_nonneg (le_of_lt htI.1), hP.clock_lt_clockEnd_of_mem htI⟩
  have hτt : τ ≤ t := le_of_lt htI.1
  rw [fibre_eq_fibreRight hv.1 fun t' ht' => hP.clock_lt_of_mem_visitSet htI ht']
  refine le_antisymm ?_ (fibreRight_clock ⟨hτt, le_rfl⟩)
  exact (fibreRight_mem hP.continuous_clock hτt _).2

/-! ### (GC1) and the continuous erasure -/

/-- **(GC1) for the erasure at infinity** (Aux. lemma 39 / Proposition 1.5): the trace takes the
same value at the two ends of every nondegenerate maximal fibre of the clock in `[τ, S]`, for `S`
after which the clock increases. -/
theorem gc1 (hP : IsErasurePocketInf η C y₀ τ) {S : ℝ} (hS : ∀ t > S, pocketClockInf η C τ S < pocketClockInf η C τ t) :
    ∀ a ∈ Icc τ S, ∀ b ∈ Icc τ S, a < b → pocketClockInf η C τ a = pocketClockInf η C τ b →
      (∀ t ∈ Icc τ S, pocketClockInf η C τ t = pocketClockInf η C τ a → t ∈ Icc a b) →
      η a = η b := by
  intro a ha b hb hab hℓ hmax
  obtain ⟨hgap, hbcl, hacl⟩ := hP.maximal_fibre le_rfl hS ha hb hab hℓ hmax
  exact hP.gap a b ha.1 hab hgap hbcl hacl

/-- **Aux. lemma 40, the continuous erasure at infinity**: `γ̂_C` is continuous on `[0, u]` for
every `u < ℓ(∞)`. -/
theorem continuousOn_erasedPath_Icc (hP : IsErasurePocketInf η C y₀ τ)
    {u : ℝ} (hu : u ∈ Ico 0 (clockEnd η C τ)) :
    ContinuousOn (erasedPathInf η C τ) (Icc 0 u) := by
  set S := pocketFibreInf η C τ u with hSdef
  have hτS : τ ≤ S := hP.fibre_mem hu
  have hℓS : pocketClockInf η C τ S = u := hP.clock_fibre hu
  have hS : ∀ t > S, pocketClockInf η C τ S < pocketClockInf η C τ t := hP.clock_lt_of_fibre hu
  have h := continuousOn_comp_fibreRight hP.continuous_clock hP.monotone_clock hτS
    (hP.cont.mono fun t ht => hP.nonneg.trans ht.1) (hP.gc1 hS)
  rw [clock_τ, hℓS] at h
  refine h.congr fun v hv => ?_
  simp only [erasedPathInf]
  rw [fibre_eq_fibreRight hv.1 fun t ht => hv.2.trans_lt (hℓS ▸ hS t ht)]

theorem continuousOn_erasedPath (hP : IsErasurePocketInf η C y₀ τ)
    :
    ContinuousOn (erasedPathInf η C τ) (Ico 0 (clockEnd η C τ)) := by
  intro v hv
  obtain ⟨w, hvw, hw⟩ := exists_between hv.2
  refine ((hP.continuousOn_erasedPath_Icc ⟨hv.1.trans hvw.le, hw⟩) v
    ⟨hv.1, hvw.le⟩).mono_of_mem_nhdsWithin ?_
  exact mem_nhdsWithin.2 ⟨Iio w, isOpen_Iio, hvw, fun x hx => ⟨hx.2.1, le_of_lt hx.1⟩⟩

/-- **`I ≠ ∅`**: the terminal clock value is positive (there is a visit after `τ`). -/
theorem clockEnd_pos (hP : IsErasurePocketInf η C y₀ τ) : 0 < clockEnd η C τ := by
  obtain ⟨t, ht, htC⟩ := hP.noFinal τ le_rfl
  have htI := hP.mem_visitSet (hP.nonneg.trans ht.le) htC
  have := (hP.clock_lt_of_mem ht (lt_add_one t) htI).trans_le (hP.clock_le_clockEnd _)
  rwa [clock_τ] at this

/-- The erased path starts at `y₀`. -/
theorem erasedPath_zero (hP : IsErasurePocketInf η C y₀ τ)
    : erasedPathInf η C τ 0 = y₀ := by
  have hv : (0 : ℝ) ∈ Ico 0 (clockEnd η C τ) := ⟨le_rfl, hP.clockEnd_pos⟩
  have hm := hP.fibre_mem hv
  have hc0 := hP.clock_fibre hv
  rcases eq_or_lt_of_le hm with h | h
  · rw [erasedPathInf, ← h, hP.first_y]
  · rw [erasedPathInf, ← hP.first_y]
    exact (hP.gc1 (hP.clock_lt_of_fibre hv) τ ⟨le_rfl, h.le⟩ _ ⟨h.le, le_rfl⟩ h
      (by rw [hc0, clock_τ]) fun t ht _ => ⟨ht.1, ht.2⟩).symm

/-- Before its terminal time the erased path is in `C̄`; its time is a limit of later visits. -/
theorem fibre_mem_closure (hP : IsErasurePocketInf η C y₀ τ) {v : ℝ}
    (hv : v ∈ Ico 0 (clockEnd η C τ)) :
    pocketFibreInf η C τ v ∈ closure {t | pocketFibreInf η C τ v < t ∧ η t ∈ C} :=
  hP.mem_closure_of_right (hP.clock_lt_of_fibre hv)

theorem erasedPath_mem (hP : IsErasurePocketInf η C y₀ τ) {v : ℝ}
    (hv : v ∈ Ico 0 (clockEnd η C τ)) : erasedPathInf η C τ v ∈ closure C :=
  hP.mem_closure_of_mem_closure_visits (hP.fibre_nonneg hv) (hP.fibre_mem_closure hv)

/-- **(GC2) at infinity** (Specification p. 203): erasure changes no range in `C`:
`γ̂_C([0, u]) ∩ C = R_{fR(u)} ∩ C`. -/
theorem erasedPath_image_inter (hP : IsErasurePocketInf η C y₀ τ) {u : ℝ}
    (hu : u ∈ Ico 0 (clockEnd η C τ)) :
    erasedPathInf η C τ '' Icc 0 u ∩ C = η '' Icc 0 (pocketFibreInf η C τ u) ∩ C := by
  ext z
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hz⟩
    have hv' : v ∈ Ico 0 (clockEnd η C τ) := ⟨hv.1, hv.2.trans_lt hu.2⟩
    exact ⟨⟨_, ⟨hP.fibre_nonneg hv', hP.monotoneOn_fibre hv' hu hv.2⟩, rfl⟩, hz⟩
  · rintro ⟨⟨t, ht, rfl⟩, hz⟩
    have htI := hP.mem_visitSet ht.1 hz
    refine ⟨⟨pocketClockInf η C τ t, ⟨hP.clock_nonneg (le_of_lt htI.1), ?_⟩, ?_⟩, hz⟩
    · rw [← hP.clock_fibre hu]; exact hP.monotone_clock ht.2
    · rw [erasedPathInf, hP.fibre_clock_of_mem htI]

/-! ### The terminal limit -/

/-- **No final gap at infinity**: `ℓ(a) < ℓ(∞)` for every `a ≥ τ`. -/
theorem clock_lt_clockEnd (hP : IsErasurePocketInf η C y₀ τ) {a : ℝ} (ha : τ ≤ a) :
    pocketClockInf η C τ a < clockEnd η C τ := by
  obtain ⟨t, ht, htC⟩ := hP.noFinal a ha
  have htI := hP.mem_visitSet ((hP.nonneg.trans ha).trans ht.le) htC
  exact (hP.clock_lt_of_mem ht (lt_add_one t) htI).trans_le (hP.clock_le_clockEnd _)

/-- The fibre endpoints tend to `∞` at the terminal clock value. -/
theorem tendsto_fibre (hP : IsErasurePocketInf η C y₀ τ) :
    Tendsto (pocketFibreInf η C τ) (𝓝[<] (clockEnd η C τ)) atTop := by
  rw [Filter.tendsto_atTop]
  intro T
  have hlt := hP.clock_lt_clockEnd (le_max_right T τ)
  filter_upwards [Ioo_mem_nhdsLT (max_lt hlt hP.clockEnd_pos)] with v hv
  have hv' : v ∈ Ico 0 (clockEnd η C τ) := ⟨(le_max_right _ _).trans hv.1.le, hv.2⟩
  by_contra h
  push Not at h
  have := hP.monotone_clock (h.le.trans (le_max_left T τ))
  rw [hP.clock_fibre hv'] at this
  linarith [le_max_left (pocketClockInf η C τ (max T τ)) 0, hv.1]

/-- With a transient counterflow, `γ̂_C(v) → ∞` as `v ↑ ℓ(∞)` (Aux. lemma 40 at infinity). -/
theorem tendsto_erasedPath (hP : IsErasurePocketInf η C y₀ τ) (htr : Tendsto (fun t => ‖η t‖) atTop atTop) :
    Tendsto (fun v => ‖erasedPathInf η C τ v‖) (𝓝[<] (clockEnd η C τ)) atTop :=
  htr.comp hP.tendsto_fibre

theorem tendsto_ζ (hP : IsErasurePocketInf η C y₀ τ) {ψ : ℂ → ℂ}
    (hψ : Tendsto ψ (cobounded ℂ ⊓ 𝓟 (closure C)) (cobounded ℂ)) (htr : Tendsto (fun t => ‖η t‖) atTop atTop) :
    Tendsto (fun v => ψ (erasedPathInf η C τ v)) (𝓝[<] (clockEnd η C τ)) (cobounded ℂ) := by
  refine hψ.comp (tendsto_inf.2 ⟨tendsto_norm_atTop_iff_cobounded.1 (hP.tendsto_erasedPath htr),
    tendsto_principal.2 ?_⟩)
  filter_upwards [Ioo_mem_nhdsLT hP.clockEnd_pos] with v hv
  exact hP.erasedPath_mem ⟨hv.1.le, hv.2⟩

end IsErasurePocketInf

/-! ### The landed contained case -/

/-- **A reverse-contained pocket at infinity has the erasure facts** under Aux. lemma 37's attachment constancy
at infinity. -/
theorem isErasurePocketInf_of_isReversePocketInf {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ : ℝ → ℂ} {τ : ℝ}
    (hP : IsReversePocketInf W η C α₁ α₂ τ) (hAC : AttachmentConstancyInf η C α₁ α₂ τ) :
    IsErasurePocketInf η C (α₁ 0) τ := by
  refine ⟨hP.trace.2.1, hP.isOpen, hP.nonneg, fun t ht htC => hP.mem_Ioi_of_mem ht htC, hP.first_y,
    fun a ha => ?_, fun a b hτa hab hgap hb ha => ?_⟩
  · have hlt := hP.clock_lt_clockEnd hAC ha
    obtain ⟨T, hτT, hT⟩ := hP.exists_clock_gt hlt
    have haT : a < T := by
      by_contra h
      push Not at h
      exact absurd (hP.monotone_clock h) (not_le.2 hT)
    obtain ⟨t, ht, htI⟩ := hP.exists_mem_of_clock_lt haT hT.ne
    exact ⟨t, ht.1, htI.2⟩
  · rcases eq_or_lt_of_le (hP.nonneg.trans hτa) with h0 | h0
    · have hτ0 : τ = 0 := le_antisymm (h0 ▸ hτa) hP.nonneg
      subst h0
      exact hP.gap_eq_seed hAC hτ0 hab hgap hb
    · have ha' : a = τ ∨ a ∈ closure {t | 0 < t ∧ η t ∈ C} := ha.imp_right fun h =>
        closure_mono (s := {t | τ < t ∧ η t ∈ C}) (t := {t | 0 < t ∧ η t ∈ C})
          (fun t ht => ⟨hP.nonneg.trans_lt ht.1, ht.2⟩) h
      exact (hP.gap_eq hAC le_rfl h0 hτa hab hgap ha' hb).2

/-! ### The relative traversal at infinity -/

section Traversal

variable {η : ℝ → ℂ} {C : Set ℂ} {y₀ : ℂ} {τ : ℝ} {ψ : ℂ → ℂ}

/-- **The relative traversal at infinity** in a coordinate `ψ`: `relCurve (ψ ∘ γ̂_C) ℓ(∞)`. -/
abbrev relTravInf (η : ℝ → ℂ) (C : Set ℂ) (τ : ℝ) (ψ : ℂ → ℂ) : ℝ → ℂ :=
  relCurve (fun v => ψ (erasedPathInf η C τ v)) (clockEnd η C τ)

namespace IsErasurePocketInf

/-- **Transience of the relative traversal at infinity**. -/
theorem tendsto_norm_relTravInf (hP : IsErasurePocketInf η C y₀ τ)
    (hψ : Tendsto ψ (cobounded ℂ ⊓ 𝓟 (closure C)) (cobounded ℂ)) (htr : Tendsto (fun t => ‖η t‖) atTop atTop) :
    Tendsto (fun u => ‖relTravInf η C τ ψ u‖) atTop atTop :=
  tendsto_norm_atTop_iff_cobounded.2 ((hP.tendsto_ζ hψ htr).comp (tendsto_clockOf hP.clockEnd_pos))

/-- The relative traversal at infinity passes through `ψ(η t)` at an interior visit time `t`. -/
theorem relTravInf_of_mem_visitSet (hP : IsErasurePocketInf η C y₀ τ) {t : ℝ} (htI : t ∈ visitSetInf η C τ) :
    0 ≤ pocketClockInf η C τ t / (clockEnd η C τ - pocketClockInf η C τ t) ∧
      relTravInf η C τ ψ (pocketClockInf η C τ t / (clockEnd η C τ - pocketClockInf η C τ t)) = ψ (η t) := by
  have hL := hP.clockEnd_pos
  have hv0 := hP.clock_nonneg (le_of_lt htI.1)
  have hv := hP.clock_lt_clockEnd_of_mem htI
  refine ⟨div_sub_nonneg hv0 hv, ?_⟩
  simp only [relTravInf, relCurve, clockOf_div_sub hL hv, erasedPathInf, hP.fibre_clock_of_mem htI]

/-- **Points of `ℍ` of arbitrarily large modulus** on the relative traversal at infinity (a transient counterflow,
`ψ → ∞` at `∞` within `C̄`). -/
theorem exists_relTravInf_mem_H_lt_norm (hP : IsErasurePocketInf η C y₀ τ) (hψH : MapsTo ψ C H)
    (hψ : Tendsto ψ (cobounded ℂ ⊓ 𝓟 (closure C)) (cobounded ℂ)) (htr : Tendsto (fun t => ‖η t‖) atTop atTop)
    (M : ℝ) : ∃ u, 0 ≤ u ∧ relTravInf η C τ ψ u ∈ H ∧ M < ‖relTravInf η C τ ψ u‖ := by
  have hev : ∀ᶠ z in cobounded ℂ ⊓ 𝓟 (closure C), M < ‖ψ z‖ :=
    (tendsto_norm_cobounded_atTop.comp hψ).eventually (eventually_gt_atTop M)
  rw [Filter.eventually_inf_principal] at hev
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 ((tendsto_norm_atTop_iff_cobounded.1 htr).eventually hev)
  obtain ⟨t, ht, htC⟩ := hP.noFinal (max T τ) (le_max_right _ _)
  have ht0 : 0 ≤ t := hP.nonneg.trans ((le_max_right _ _).trans ht.le)
  have htI := hP.mem_visitSet ht0 htC
  have hMt : M < ‖ψ (η t)‖ := hT t ((le_max_left _ _).trans ht.le) (subset_closure htC)
  obtain ⟨hu, he⟩ := hP.relTravInf_of_mem_visitSet (ψ := ψ) htI
  exact ⟨_, hu, he ▸ hψH htC, he ▸ hMt⟩

/-- **The relative traversal at infinity is a driven curve** from Aux. lemma 41's Loewner conclusion on every
`[0, S']`, `0 < S' < ℓ(∞)`, for a coordinate continuous on `C̄` with `ψ(y₀) = 0`. -/
theorem isDrivenCurve_relTravInf (hP : IsErasurePocketInf η C y₀ τ) (hψc : ContinuousOn ψ (closure C))
    (hψ0 : ψ y₀ = 0)
    (hloc : ∀ S' : ℝ, 0 < S' → S' < clockEnd η C τ → ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧
      ∃ σ' : ℝ → ℝ, σ' 0 = 0 ∧ StrictMonoOn σ' (Icc 0 S') ∧ ContinuousOn σ' (Icc 0 S') ∧
      ∀ t ∈ Icc 0 S', QuantumZipper.fwdHull W (σ' t) = fillH ((fun v => ψ (erasedPathInf η C τ v)) '' Icc 0 t)) :
    IsDrivenCurve (relTravInf η C τ ψ) :=
  PocketTraversal.isDrivenCurve_relCurve hP.clockEnd_pos
    (hψc.comp hP.continuousOn_erasedPath fun _ hv => hP.erasedPath_mem hv)
    (by simp only [hP.erasedPath_zero, hψ0]) hloc

/-- **`GoodR7` for the relative traversal at infinity**. -/
theorem goodR7_relTravInf (hP : IsErasurePocketInf η C y₀ τ) (hγ : IsDrivenCurve (relTravInf η C τ ψ))
    (hψ : Tendsto ψ (cobounded ℂ ⊓ 𝓟 (closure C)) (cobounded ℂ)) (htr : Tendsto (fun t => ‖η t‖) atTop atTop)
    (hL : capLife (relTravInf η C τ ψ) = ⊤) : GoodR7 (fun t => segDriver (relTravInf η C τ ψ) t) ⊤ :=
  goodR7_of_tendsto hγ (hP.tendsto_norm_relTravInf hψ htr) hL

end IsErasurePocketInf

end Traversal

/-! ### Consequence R.4 before `τ` and no final gap at infinity -/

section Facts

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {y₀ : ℂ} {τ : ℝ}

/-- **Consequence R.4 before `τ`** (abstractly): if every visited frontier point of `C` forces `y₀` to be visited by
then (on a contained side by reverse first-visit order, on an outer side through the certified frontier), every visit
to `C` is strictly after `τ = T(y₀)`. -/
theorem lt_of_frontier_visit (hη : IsLoewnerTrace W η) (hCo : IsOpen C) (hCH : C ⊆ H) (hτf : y₀ ∉ η '' Ico 0 τ)
    (hfr : ∀ s, 0 ≤ s → η s ∈ frontier C → y₀ ∈ η '' Icc 0 s) {t : ℝ} (ht : 0 ≤ t) (htC : η t ∈ C) : τ < t := by
  have hpre : IsPreconnected (η '' Icc 0 t) := isPreconnected_Icc.image _ (hη.2.1.mono fun s hs => hs.1)
  obtain ⟨z, hzR, hzf⟩ : (η '' Icc 0 t ∩ frontier C).Nonempty := by
    by_contra hne
    have hsub := subset_of_isPreconnected_of_disjoint_frontier hpre hCo ⟨η t, ⟨t, ⟨ht, le_rfl⟩, rfl⟩, htC⟩
      (Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hne))
    have h0 := hCH (hsub ⟨0, ⟨le_rfl, ht⟩, rfl⟩)
    rw [hη.1] at h0
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h0)
  obtain ⟨t', ht', rfl⟩ := hzR
  have hτ := le_of_fresh hτf (hfr t' ht'.1 hzf)
  refine lt_of_le_of_lt hτ (lt_of_le_of_ne ht'.2 fun h => ?_)
  rw [h] at hzf
  have := hzf.2
  rw [hCo.interior_eq] at this
  exact this htC

/-- **No final gap at infinity** from Aux. 37's attachment constancy along one barrier `B` from `y₀` (`v = 0`) to
`∞` (continuous, proper, reverse visited, every point visited): on a final gap `[a, ∞)` the last-visit parameter
`u(a)` would stay put, but `B(u(a) + 1)` is visited at some time (the landed argument of
`Sec6.IsReversePocketInf.clock_lt_clockEnd`). -/
theorem noFinalInf_of_attach (hηc : ContinuousOn η (Ici 0)) (hCo : IsOpen C) {B : ℝ → ℂ}
    (hBt : Tendsto (fun v => ‖B v‖) atTop atTop) (hB0 : B 0 = y₀)
    (hvis : ∀ v ∈ Ici (0 : ℝ), ∃ t, B v ∈ η '' Icc 0 t)
    (hAC : ∀ a b : ℝ, τ ≤ a → a ≤ b → (∀ t ∈ Icc a b, η t ∉ C) →
      lastVisit (fun t => η '' Icc 0 t) B b = lastVisit (fun t => η '' Icc 0 t) B a)
    (hτ0 : 0 ≤ τ) (hτ : η τ = y₀) : ∀ a, τ ≤ a → ∃ t > a, η t ∈ C := by
  intro a ha
  by_contra hno
  push Not at hno
  have ha0 : 0 ≤ a := hτ0.trans ha
  have hgap : ∀ t, a ≤ t → η t ∉ C := by
    intro t hat htC
    rcases eq_or_lt_of_le hat with hta | hta
    · obtain ⟨δ, hδ, hδC⟩ := Metric.mem_nhdsWithin_iff.1
        ((hηc t (ha0.trans hat)).preimage_mem_nhdsWithin (hCo.mem_nhds htC))
      refine hno (t + δ / 2) (by linarith) (hδC ⟨?_, (ha0.trans hat).trans (by linarith)⟩)
      rw [mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
      linarith
    · exact hno t hta htC
  have hcpt : ∀ s, IsCompact (η '' Icc 0 s) := fun s => isCompact_Icc.image_of_continuousOn (hηc.mono fun _ h => h.1)
  set u := lastVisit (fun t => η '' Icc 0 t) B a with hudef
  have hu0 : 0 ≤ u := le_lastVisit (R := fun t => η '' Icc 0 t) hBt (hcpt a).isBounded (mem_Ici.2 le_rfl)
    (by rw [hB0]; exact ⟨τ, ⟨hτ0, ha⟩, hτ⟩)
  obtain ⟨t, ht⟩ := hvis (u + 1) (mem_Ici.2 (by linarith))
  have hat : a ≤ t := by
    by_contra h
    push Not at h
    have := le_lastVisit (R := fun t => η '' Icc 0 t) hBt (hcpt a).isBounded (mem_Ici.2 (by linarith))
      (monotone_image_Icc h.le ht)
    linarith
  have hc := hAC a t ha hat fun t' ht' => hgap t' ht'.1
  have := le_lastVisit (R := fun t => η '' Icc 0 t) hBt (hcpt t).isBounded (mem_Ici.2 (by linarith)) ht
  rw [hc] at this
  linarith

end Facts

end InteractingSLE.Sec7.R7StopIn
