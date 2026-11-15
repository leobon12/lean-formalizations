/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux40Inf
import InteractingSLE.Spec.Sec6.Aux40FullErase

/-!
# The continuous pocket erasure with the junction at the original target (Aux. lemma 40, `σ = ∞`)

Specification §6.2, **Aux.** lemma 40 (`source/spec/p193-240.md` L187–L211, pp. 202–204) for the
pocket of `Aux40Inf` (`x₀` the original target, `σ = T(x₀) = ∞`): "This defines a continuous path
`γ_C` in `C̄` on `[τ, σ]`, with the terminal value interpreted as a limit if `σ = ∞`." The interior
visit times are `I = {t > τ : η(t) ∈ C}`, the clock `ℓ(t) = ∫_τ^t e^{-s} 1_I(s) ds` has the finite
terminal value `ℓ(∞) = sup ℓ` (`clockEnd`), and the erased path is `γ̂_C(v) = η(fR(v))`,
`fR(v) = max {t ≥ τ : ℓ(t) ≤ v}` for `v ∈ [0, ℓ(∞))`.

## Main results (namespace `IsReversePocketInf`)

* `clockEnd_pos`: `I ≠ ∅` (from attachment constancy and reverse containment);
* `gc1`: **(GC1)** on the clock fibres;
* `continuousOn_erasedPath`: the erased path is continuous on `[0, ℓ(∞))`, from `y₀`
  (`erasedPath_zero`), with values in `C̄` (`erasedPath_mem`);
* `erasedPath_image_inter`: **(GC2)**, erasure changes no range in `C`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec6

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- The interior-visit times `I = {t > τ : η(t) ∈ C}` (Aux. lemma 39 with `σ = ∞`). -/
def visitSetInf (η : ℝ → ℂ) (C : Set ℂ) (τ : ℝ) : Set ℝ := {t ∈ Ioi τ | η t ∈ C}

/-- The quotient clock `ℓ(t) = ∫_τ^t e^{-s} 1_I(s) ds` (Aux. lemma 40). -/
def pocketClockInf (η : ℝ → ℂ) (C : Set ℂ) (τ : ℝ) : ℝ → ℝ := erasureClock (visitSetInf η C τ) τ

/-- The terminal clock value `ℓ(∞) = sup_t ℓ(t)`. -/
def clockEnd (η : ℝ → ℂ) (C : Set ℂ) (τ : ℝ) : ℝ := ⨆ t, pocketClockInf η C τ t

/-- The right endpoint of the clock fibre of `v` in `[τ, ∞)`. -/
def pocketFibreInf (η : ℝ → ℂ) (C : Set ℂ) (τ : ℝ) (v : ℝ) : ℝ :=
  sSup {t ∈ Ici τ | pocketClockInf η C τ t ≤ max v (pocketClockInf η C τ τ)}

/-- **The erased path** `γ̂_C(v) = η(fR(v))` of Aux. lemma 40 with the junction at infinity. -/
def erasedPathInf (η : ℝ → ℂ) (C : Set ℂ) (τ : ℝ) (v : ℝ) : ℂ := η (pocketFibreInf η C τ v)

namespace IsReversePocketInf

variable {C : Set ℂ} {α₁ α₂ : ℝ → ℂ} {τ : ℝ}

/-! ### The clock -/

theorem isOpen_visitSet (hP : IsReversePocketInf W η C α₁ α₂ τ) :
    IsOpen (visitSetInf η C τ) :=
  (hP.trace.2.1.mono fun _ ht => hP.nonneg.trans (le_of_lt ht)).isOpen_inter_preimage isOpen_Ioi
    hP.isOpen

theorem continuous_clock (hP : IsReversePocketInf W η C α₁ α₂ τ) :
    Continuous (pocketClockInf η C τ) :=
  continuous_erasureClock hP.isOpen_visitSet.measurableSet

theorem monotone_clock (hP : IsReversePocketInf W η C α₁ α₂ τ) :
    Monotone (pocketClockInf η C τ) :=
  monotone_erasureClock hP.isOpen_visitSet.measurableSet

theorem clock_τ : pocketClockInf η C τ τ = 0 := intervalIntegral.integral_same

theorem clock_nonneg (hP : IsReversePocketInf W η C α₁ α₂ τ) {t : ℝ} (ht : τ ≤ t) :
    0 ≤ pocketClockInf η C τ t := clock_τ (η := η) (C := C) ▸ hP.monotone_clock ht

/-- The clock is bounded by `e^{-τ}`. -/
theorem clock_le (hP : IsReversePocketInf W η C α₁ α₂ τ) (t : ℝ) :
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

theorem bddAbove_clock (hP : IsReversePocketInf W η C α₁ α₂ τ) :
    BddAbove (range (pocketClockInf η C τ)) :=
  ⟨Real.exp (-τ), by rintro _ ⟨t, rfl⟩; exact hP.clock_le t⟩

theorem clock_le_clockEnd (hP : IsReversePocketInf W η C α₁ α₂ τ) (t : ℝ) :
    pocketClockInf η C τ t ≤ clockEnd η C τ :=
  le_ciSup hP.bddAbove_clock t

/-- Below the terminal value, the clock exceeds `v` at some time `T ≥ τ`. -/
theorem exists_clock_gt (hP : IsReversePocketInf W η C α₁ α₂ τ) {v : ℝ}
    (hv : v < clockEnd η C τ) : ∃ T, τ ≤ T ∧ v < pocketClockInf η C τ T := by
  obtain ⟨T, hT⟩ := exists_lt_of_lt_ciSup hv
  exact ⟨max T τ, le_max_right _ _, hT.trans_le (hP.monotone_clock (le_max_left _ _))⟩

/-- By (JP1) every visit to `C` is an interior-visit time. -/
theorem mem_visitSet (hP : IsReversePocketInf W η C α₁ α₂ τ) {t : ℝ} (ht : 0 ≤ t)
    (htC : η t ∈ C) : t ∈ visitSetInf η C τ := ⟨hP.mem_Ioi_of_mem ht htC, htC⟩

/-- The clock increases strictly across a visit time. -/
theorem clock_lt_of_mem (hP : IsReversePocketInf W η C α₁ α₂ τ) {a b t : ℝ} (hta : a < t)
    (htb : t < b) (htI : t ∈ visitSetInf η C τ) :
    pocketClockInf η C τ a < pocketClockInf η C τ b := by
  refine lt_of_le_of_ne (hP.monotone_clock (hta.trans htb).le) fun h => ?_
  have := (erasureClock_eq_iff hP.isOpen_visitSet (hta.trans htb)).1 h
  exact Set.disjoint_left.1 this ⟨hta, htb⟩ htI

/-- If the clock increases on `[a, b]`, then `(a, b)` contains a visit time. -/
theorem exists_mem_of_clock_lt (hP : IsReversePocketInf W η C α₁ α₂ τ) {a b : ℝ} (hab : a < b)
    (h : pocketClockInf η C τ a ≠ pocketClockInf η C τ b) :
    ∃ t ∈ Ioo a b, t ∈ visitSetInf η C τ := by
  by_contra hne
  push Not at hne
  exact h ((erasureClock_eq_iff hP.isOpen_visitSet hab).2
    (Set.disjoint_left.2 fun t ht htI => hne t ht htI))

/-- A visit time is the right endpoint of its (singleton) clock fibre. -/
theorem clock_lt_of_mem_visitSet (hP : IsReversePocketInf W η C α₁ α₂ τ) {t t' : ℝ}
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
theorem clock_lt_clockEnd_of_mem (hP : IsReversePocketInf W η C α₁ α₂ τ) {t : ℝ}
    (htI : t ∈ visitSetInf η C τ) : pocketClockInf η C τ t < clockEnd η C τ :=
  (hP.clock_lt_of_mem_visitSet htI (lt_add_one t)).trans_le (hP.clock_le_clockEnd _)

/-- A right endpoint `b` after which the clock increases is a limit of later visits. -/
theorem mem_closure_of_right (hP : IsReversePocketInf W η C α₁ α₂ τ) {b : ℝ}
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
theorem mem_closure_of_left (hP : IsReversePocketInf W η C α₁ α₂ τ) {s a : ℝ} (hsa : s < a)
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
theorem exists_mem_Ioo_of_mem (hP : IsReversePocketInf W η C α₁ α₂ τ) {a b t : ℝ} (hab : a < b)
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
theorem maximal_fibre (hP : IsReversePocketInf W η C α₁ α₂ τ) {s S : ℝ} (hτs : τ ≤ s)
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

theorem fibre_eq_fibreRight_of_lt (hP : IsReversePocketInf W η C α₁ α₂ τ) {v T : ℝ}
    (hv0 : 0 ≤ v) (hvT : v < pocketClockInf η C τ T) :
    pocketFibreInf η C τ v = fibreRight (pocketClockInf η C τ) τ T v :=
  fibre_eq_fibreRight hv0 fun _ ht => hvT.trans_le (hP.monotone_clock (le_of_lt ht))

theorem fibre_mem (hP : IsReversePocketInf W η C α₁ α₂ τ) {v : ℝ}
    (hv : v ∈ Ico 0 (clockEnd η C τ)) : τ ≤ pocketFibreInf η C τ v := by
  obtain ⟨T, hτT, hvT⟩ := hP.exists_clock_gt hv.2
  rw [hP.fibre_eq_fibreRight_of_lt hv.1 hvT]
  exact (fibreRight_mem hP.continuous_clock hτT v).1

theorem fibre_nonneg (hP : IsReversePocketInf W η C α₁ α₂ τ) {v : ℝ}
    (hv : v ∈ Ico 0 (clockEnd η C τ)) : 0 ≤ pocketFibreInf η C τ v :=
  hP.nonneg.trans (hP.fibre_mem hv)

theorem clock_fibre (hP : IsReversePocketInf W η C α₁ α₂ τ) {v : ℝ}
    (hv : v ∈ Ico 0 (clockEnd η C τ)) : pocketClockInf η C τ (pocketFibreInf η C τ v) = v := by
  obtain ⟨T, hτT, hvT⟩ := hP.exists_clock_gt hv.2
  rw [hP.fibre_eq_fibreRight_of_lt hv.1 hvT]
  exact clock_fibreRight hP.continuous_clock hτT (by rw [clock_τ]; exact ⟨hv.1, hvT.le⟩)

/-- After the right endpoint of the fibre of `v`, the clock exceeds `v`. -/
theorem lt_clock_of_fibre_lt (hP : IsReversePocketInf W η C α₁ α₂ τ) {v : ℝ}
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
theorem clock_lt_of_fibre (hP : IsReversePocketInf W η C α₁ α₂ τ) {v : ℝ}
    (hv : v ∈ Ico 0 (clockEnd η C τ)) :
    ∀ t > pocketFibreInf η C τ v,
      pocketClockInf η C τ (pocketFibreInf η C τ v) < pocketClockInf η C τ t := fun t ht => by
  rw [hP.clock_fibre hv]; exact hP.lt_clock_of_fibre_lt hv ht

theorem monotoneOn_fibre (hP : IsReversePocketInf W η C α₁ α₂ τ) :
    MonotoneOn (pocketFibreInf η C τ) (Ico 0 (clockEnd η C τ)) := by
  intro v hv w hw hvw
  obtain ⟨T, hτT, hwT⟩ := hP.exists_clock_gt hw.2
  rw [hP.fibre_eq_fibreRight_of_lt hv.1 (hvw.trans_lt hwT),
    hP.fibre_eq_fibreRight_of_lt hw.1 hwT]
  exact monotone_fibreRight hτT hvw

/-- A visit time is the right endpoint of its clock fibre. -/
theorem fibre_clock_of_mem (hP : IsReversePocketInf W η C α₁ α₂ τ) {t : ℝ}
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
theorem gc1 (hP : IsReversePocketInf W η C α₁ α₂ τ) (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    {S : ℝ} (hS : ∀ t > S, pocketClockInf η C τ S < pocketClockInf η C τ t) :
    ∀ a ∈ Icc τ S, ∀ b ∈ Icc τ S, a < b → pocketClockInf η C τ a = pocketClockInf η C τ b →
      (∀ t ∈ Icc τ S, pocketClockInf η C τ t = pocketClockInf η C τ a → t ∈ Icc a b) →
      η a = η b := by
  intro a ha b hb hab hℓ hmax
  obtain ⟨hgap, hbcl, hacl⟩ := hP.maximal_fibre le_rfl hS ha hb hab hℓ hmax
  have hacl' : a = τ ∨ a ∈ closure {t | 0 < t ∧ η t ∈ C} := hacl.imp_right fun h =>
    closure_mono (s := {t | τ < t ∧ η t ∈ C}) (t := {t | 0 < t ∧ η t ∈ C})
      (fun t ht => ⟨hP.nonneg.trans_lt ht.1, ht.2⟩) h
  rcases eq_or_lt_of_le (hP.nonneg.trans ha.1) with h0 | h0
  · -- the initial gap at the original seed (`a = τ = 0`)
    have hτ0 : τ = 0 := le_antisymm (h0 ▸ ha.1) hP.nonneg
    rw [← h0] at hab hgap hbcl ⊢
    exact hP.gap_eq_seed hAC hτ0 hab hgap hbcl
  · exact (hP.gap_eq hAC le_rfl h0 ha.1 hab hgap hacl' hbcl).2

/-- **Aux. lemma 40, the continuous erasure at infinity**: `γ̂_C` is continuous on `[0, u]` for
every `u < ℓ(∞)`. -/
theorem continuousOn_erasedPath_Icc (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) {u : ℝ} (hu : u ∈ Ico 0 (clockEnd η C τ)) :
    ContinuousOn (erasedPathInf η C τ) (Icc 0 u) := by
  set S := pocketFibreInf η C τ u with hSdef
  have hτS : τ ≤ S := hP.fibre_mem hu
  have hℓS : pocketClockInf η C τ S = u := hP.clock_fibre hu
  have hS : ∀ t > S, pocketClockInf η C τ S < pocketClockInf η C τ t := hP.clock_lt_of_fibre hu
  have h := continuousOn_comp_fibreRight hP.continuous_clock hP.monotone_clock hτS
    (hP.trace.2.1.mono fun t ht => hP.nonneg.trans ht.1) (hP.gc1 hAC hS)
  rw [clock_τ, hℓS] at h
  refine h.congr fun v hv => ?_
  simp only [erasedPathInf]
  rw [fibre_eq_fibreRight hv.1 fun t ht => hv.2.trans_lt (hℓS ▸ hS t ht)]

theorem continuousOn_erasedPath (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) :
    ContinuousOn (erasedPathInf η C τ) (Ico 0 (clockEnd η C τ)) := by
  intro v hv
  obtain ⟨w, hvw, hw⟩ := exists_between hv.2
  refine ((hP.continuousOn_erasedPath_Icc hAC ⟨hv.1.trans hvw.le, hw⟩) v
    ⟨hv.1, hvw.le⟩).mono_of_mem_nhdsWithin ?_
  exact mem_nhdsWithin.2 ⟨Iio w, isOpen_Iio, hvw, fun x hx => ⟨hx.2.1, le_of_lt hx.1⟩⟩

/-- **`I ≠ ∅`**: the terminal clock value is positive. Otherwise the trace never enters `C`;
attachment constancy keeps `u₁ ≡ u₁(τ) = 0`, so `α₁(1)` is never visited, against reverse
containment. -/
theorem clockEnd_pos (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) : 0 < clockEnd η C τ := by
  by_contra hle
  push Not at hle
  have hnv : ∀ t, η t ∈ C → t < 0 := by
    intro t htC
    by_contra h0
    push Not at h0
    have htI := hP.mem_visitSet h0 htC
    have := (hP.clock_lt_of_mem htI.1 (lt_add_one t) htI).trans_le (hP.clock_le_clockEnd _)
    rw [clock_τ] at this
    linarith
  have hu0 : lastVisit (fun t => η '' Icc 0 t) α₁ τ = 0 :=
    lastVisit_eq_of_fresh hP.cont₁ hP.inj₁ hP.tendsto₁ hP.trace.2.1 hP.rev₁ hP.nonneg
      (mem_Ici.2 le_rfl) hP.first_y (by rw [hP.first_y]; exact hP.fresh_y)
  obtain ⟨t₁, ht₁⟩ := hP.visited₁ 1 (mem_Ici.2 zero_le_one)
  have hτt : τ ≤ t₁ := hP.τ_le (hP.y_mem_of_mem (Or.inl rfl) (mem_Ici.2 zero_le_one) ht₁)
  have hc := (hAC τ t₁ le_rfl hτt fun t ht htC => absurd (hnv t htC)
    (not_lt.2 (hP.nonneg.trans ht.1))).1
  have h1 := le_lastVisit (R := fun t => η '' Icc 0 t) hP.tendsto₁
    (hP.isCompact_range t₁).isBounded (mem_Ici.2 zero_le_one) ht₁
  rw [hc, hu0] at h1
  linarith

/-- The erased path starts at `y₀`. -/
theorem erasedPath_zero (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) : erasedPathInf η C τ 0 = α₁ 0 := by
  have hv : (0 : ℝ) ∈ Ico 0 (clockEnd η C τ) := ⟨le_rfl, hP.clockEnd_pos hAC⟩
  have hm := hP.fibre_mem hv
  have hc0 := hP.clock_fibre hv
  rcases eq_or_lt_of_le hm with h | h
  · rw [erasedPathInf, ← h, hP.first_y]
  · rw [erasedPathInf, ← hP.first_y]
    exact (hP.gc1 hAC (hP.clock_lt_of_fibre hv) τ ⟨le_rfl, h.le⟩ _ ⟨h.le, le_rfl⟩ h
      (by rw [hc0, clock_τ]) fun t ht _ => ⟨ht.1, ht.2⟩).symm

/-- Before its terminal time the erased path is in `C̄`; its time is a limit of later visits. -/
theorem fibre_mem_closure (hP : IsReversePocketInf W η C α₁ α₂ τ) {v : ℝ}
    (hv : v ∈ Ico 0 (clockEnd η C τ)) :
    pocketFibreInf η C τ v ∈ closure {t | pocketFibreInf η C τ v < t ∧ η t ∈ C} :=
  hP.mem_closure_of_right (hP.clock_lt_of_fibre hv)

theorem erasedPath_mem (hP : IsReversePocketInf W η C α₁ α₂ τ) {v : ℝ}
    (hv : v ∈ Ico 0 (clockEnd η C τ)) : erasedPathInf η C τ v ∈ closure C :=
  hP.mem_closure_of_mem_closure_visits (hP.fibre_nonneg hv) (hP.fibre_mem_closure hv)

/-- **(GC2) at infinity** (Specification p. 203): erasure changes no range in `C`:
`γ̂_C([0, u]) ∩ C = R_{fR(u)} ∩ C`. -/
theorem erasedPath_image_inter (hP : IsReversePocketInf W η C α₁ α₂ τ) {u : ℝ}
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

end IsReversePocketInf

end InteractingSLE.Sec6
