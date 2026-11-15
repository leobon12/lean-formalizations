/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux40Full
import InteractingSLE.Spec.Sec6.Aux40Clock

/-!
# Aux. lemma 40: the continuous pocket erasure

Specification §6.2, **Aux.** lemma 40 (`source/spec/p193-240.md` L188–L211, pp. 203–204), with
(GC1) of Aux. lemma 39 and ruling R41's Propositions 1.5–1.6 (`IsReversePocket.gap_eq`).

For the pocket of `IsReversePocket` put `I = {t ∈ (τ, σ) : η(t) ∈ C}` (`visitSet`), the quotient
clock `ℓ(t) = ∫_τ^t e^{-s} 1_I(s) ds` (`pocketClock`), and the erased path
`γ̂_C(v) = η(fR(v))`, `fR(v)` the right endpoint of the clock fibre of `v` in `[τ, σ]`
(`erasedPath`). Under Aux. lemma 37's attachment constancy (`AttachmentConstancy`):

* `IsReversePocket.clock_lt_clock_σ`: there is no final gap (`ℓ(a) < ℓ(σ)` for `a < σ`); in
  particular `I ≠ ∅` and `ℓ(σ) > 0`;
* `IsReversePocket.continuousOn_erasedPath`: **the erased path is continuous on `[0, ℓ(σ)]`**, from
  `y₀` (`erasedPath_zero`) to `x₀` (`erasedPath_clock_σ`), in `C̄` and off `x₀` before `ℓ(σ)`;
* `IsReversePocket.erasedPath_image_inter`: **(GC2)** `γ̂_C([0, u]) ∩ C = R_{fR(u)} ∩ C`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec6

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- The interior-visit times `I = {t ∈ (τ, σ) : η(t) ∈ C}` (Aux. lemma 39). -/
def visitSet (η : ℝ → ℂ) (C : Set ℂ) (τ σ : ℝ) : Set ℝ := {t ∈ Ioo τ σ | η t ∈ C}

/-- The quotient clock `ℓ(t) = ∫_τ^t e^{-s} 1_I(s) ds` (Aux. lemma 40). -/
def pocketClock (η : ℝ → ℂ) (C : Set ℂ) (τ σ : ℝ) : ℝ → ℝ := erasureClock (visitSet η C τ σ) τ

/-- The right endpoint of the clock fibre of `v` in `[τ, σ]`. -/
def pocketFibre (η : ℝ → ℂ) (C : Set ℂ) (τ σ : ℝ) : ℝ → ℝ :=
  fibreRight (pocketClock η C τ σ) τ σ

/-- **The erased path** `γ̂_C(v) = η(fR(v))` of Aux. lemma 40: the trace with the complementary
intervals of the interior visits collapsed, after the pause-removing clock. -/
def erasedPath (η : ℝ → ℂ) (C : Set ℂ) (τ σ : ℝ) (v : ℝ) : ℂ := η (pocketFibre η C τ σ v)

/-- A strict hull-growth consequence: no nondegenerate interval of the trace stays in an earlier
range. -/
theorem not_image_subset_of_lt (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {c d : ℝ} (hc : 0 ≤ c) (hcd : c < d) : ¬ η '' Icc c d ⊆ η '' Icc 0 c := by
  intro h
  have heq : η '' Icc 0 d = η '' Icc 0 c := by
    refine Subset.antisymm ?_ (image_mono (Icc_subset_Icc_right hcd.le))
    rintro _ ⟨t, ht, rfl⟩
    rcases le_total t c with htc | hct
    · exact ⟨t, ⟨ht.1, htc⟩, rfl⟩
    · exact h ⟨t, ⟨hct, ht.2⟩, rfl⟩
  have hss := QuantumZipper.RS.fwdHull_ssubset hW hW0 hc hcd
  rw [hη.2.2 c hc, hη.2.2 d (hc.trans hcd.le), heq] at hss
  exact hss.ne rfl

namespace IsReversePocket

variable {C : Set ℂ} {α₁ α₂ β : ℝ → ℂ} {τ σ : ℝ}

/-! ### The clock -/

theorem isOpen_visitSet (hP : IsReversePocket W η C α₁ α₂ β τ σ) :
    IsOpen (visitSet η C τ σ) :=
  (hP.trace.2.1.mono fun _ ht => hP.nonneg.trans ht.1.le).isOpen_inter_preimage isOpen_Ioo
    hP.isOpen

theorem continuous_clock (hP : IsReversePocket W η C α₁ α₂ β τ σ) :
    Continuous (pocketClock η C τ σ) :=
  continuous_erasureClock hP.isOpen_visitSet.measurableSet

theorem monotone_clock (hP : IsReversePocket W η C α₁ α₂ β τ σ) :
    Monotone (pocketClock η C τ σ) :=
  monotone_erasureClock hP.isOpen_visitSet.measurableSet

theorem clock_τ : pocketClock η C τ σ τ = 0 := intervalIntegral.integral_same

theorem clock_nonneg (hP : IsReversePocket W η C α₁ α₂ β τ σ) {t : ℝ} (ht : τ ≤ t) :
    0 ≤ pocketClock η C τ σ t := clock_τ (η := η) (C := C) (σ := σ) ▸ hP.monotone_clock ht

/-- By (JP1) every visit to `C` is an interior-visit time. -/
theorem mem_visitSet (hP : IsReversePocket W η C α₁ α₂ β τ σ) {t : ℝ} (ht : 0 ≤ t)
    (htC : η t ∈ C) : t ∈ visitSet η C τ σ := ⟨hP.mem_Ioo_of_mem ht htC, htC⟩

/-- The clock increases strictly across a visit time. -/
theorem clock_lt_of_mem (hP : IsReversePocket W η C α₁ α₂ β τ σ) {a b t : ℝ} (hta : a < t)
    (htb : t < b) (htI : t ∈ visitSet η C τ σ) : pocketClock η C τ σ a < pocketClock η C τ σ b := by
  refine lt_of_le_of_ne (hP.monotone_clock (hta.trans htb).le) fun h => ?_
  have := (erasureClock_eq_iff hP.isOpen_visitSet (hta.trans htb)).1 h
  exact Set.disjoint_left.1 this ⟨hta, htb⟩ htI

/-- If the clock increases on `[a, b]`, then `(a, b)` contains a visit time. -/
theorem exists_mem_of_clock_lt (hP : IsReversePocket W η C α₁ α₂ β τ σ) {a b : ℝ} (hab : a < b)
    (h : pocketClock η C τ σ a ≠ pocketClock η C τ σ b) :
    ∃ t ∈ Ioo a b, t ∈ visitSet η C τ σ := by
  by_contra hne
  push Not at hne
  exact h ((erasureClock_eq_iff hP.isOpen_visitSet hab).2
    (Set.disjoint_left.2 fun t ht htI => hne t ht htI))

/-- A visit time is the right endpoint of its (singleton) clock fibre. -/
theorem clock_lt_of_mem_visitSet (hP : IsReversePocket W η C α₁ α₂ β τ σ) {t t' : ℝ}
    (htI : t ∈ visitSet η C τ σ) (htt' : t < t') :
    pocketClock η C τ σ t < pocketClock η C τ σ t' := by
  obtain ⟨ε, hε, hεI⟩ := Metric.isOpen_iff.1 hP.isOpen_visitSet t htI
  set t'' := min (t + ε / 2) ((t + t') / 2) with ht''
  have h1 : t < t'' := lt_min (by linarith) (by linarith)
  have h2 : t'' < t' := (min_le_right _ _).trans_lt (by linarith)
  have h3 : t'' ∈ visitSet η C τ σ := hεI (by
    rw [mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
    exact (sub_le_sub_right (min_le_left _ _) t).trans_lt (by linarith))
  refine lt_of_lt_of_le ?_ (hP.monotone_clock h2.le)
  -- a visit time strictly between `t` and `t''`
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

theorem fibre_mem (hP : IsReversePocket W η C α₁ α₂ β τ σ) (v : ℝ) :
    pocketFibre η C τ σ v ∈ Icc τ σ :=
  fibreRight_mem hP.continuous_clock hP.τ_lt_σ.le v

theorem clock_fibre (hP : IsReversePocket W η C α₁ α₂ β τ σ) {v : ℝ}
    (hv : v ∈ Icc 0 (pocketClock η C τ σ σ)) : pocketClock η C τ σ (pocketFibre η C τ σ v) = v :=
  clock_fibreRight hP.continuous_clock hP.τ_lt_σ.le (by rw [clock_τ]; exact hv)

theorem monotone_fibre (hP : IsReversePocket W η C α₁ α₂ β τ σ) :
    Monotone (pocketFibre η C τ σ) :=
  monotone_fibreRight hP.τ_lt_σ.le

/-- After the right endpoint of the fibre of `v`, the clock exceeds `v`. -/
theorem lt_clock_of_fibre_lt (hP : IsReversePocket W η C α₁ α₂ β τ σ) {v : ℝ} (hv : 0 ≤ v)
    {t : ℝ} (ht : t ∈ Ioc (pocketFibre η C τ σ v) σ) : v < pocketClock η C τ σ t := by
  by_contra h
  push Not at h
  have hτt : τ ≤ t := (hP.fibre_mem v).1.trans ht.1.le
  have := le_fibreRight (ℓ := pocketClock η C τ σ) (v := v) ⟨hτt, ht.2⟩
    (by rw [clock_τ, max_eq_left hv]; exact h)
  exact absurd ht.1 (not_lt.2 this)

/-- A right endpoint `b < σ` after which the clock increases is a limit of later visits. -/
theorem mem_closure_of_right (hP : IsReversePocket W η C α₁ α₂ β τ σ) {b : ℝ} (hbσ : b < σ)
    (h : ∀ t ∈ Ioc b σ, pocketClock η C τ σ b < pocketClock η C τ σ t) :
    b ∈ closure {t | b < t ∧ η t ∈ C} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set t := min (b + ε / 2) σ with htdef
  have hbt : b < t := lt_min (by linarith) hbσ
  obtain ⟨t', ht', ht'I⟩ := hP.exists_mem_of_clock_lt hbt
    (h t ⟨hbt, min_le_right _ _⟩).ne
  refine ⟨t', ⟨ht'.1, ht'I.2⟩, ?_⟩
  rw [Real.dist_eq, abs_of_neg (by linarith [ht'.1]), neg_sub]
  have : t ≤ b + ε / 2 := min_le_left _ _
  linarith [ht'.2]

/-- A left endpoint `a > s` before which the clock is smaller is a limit of visits after `s`. -/
theorem mem_closure_of_left (hP : IsReversePocket W η C α₁ α₂ β τ σ) {s a : ℝ} (hsa : s < a)
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

/-- A visit time in `[a, b]` (`a < b`) gives a visit time in `(a, b)` (`I` is open). -/
theorem exists_mem_Ioo_of_mem (hP : IsReversePocket W η C α₁ α₂ β τ σ) {a b t : ℝ} (hab : a < b)
    (ht : t ∈ Icc a b) (htI : t ∈ visitSet η C τ σ) : ∃ t' ∈ Ioo a b, t' ∈ visitSet η C τ σ := by
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

/-- **A nondegenerate maximal clock fibre** `[a, b]` of `[s, S]` (`τ ≤ s`, `S ≤ σ` with the clock
increasing after `S`, `b < σ`): the trace avoids `C` on `[a, b]`, `b` is a limit of later visits,
and `a = s` or `a` is a limit of visits after `s`. -/
theorem maximal_fibre (hP : IsReversePocket W η C α₁ α₂ β τ σ) {s S : ℝ} (hτs : τ ≤ s)
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
    · refine Or.inr (hP.mem_closure_of_left h fun t ht => lt_of_le_of_ne
        (hP.monotone_clock ht.2.le) fun h' => ?_)
      have := hmax t ⟨ht.1, ht.2.le.trans ha.2⟩ h'
      exact absurd this.1 (not_le.2 ht.2)

/-- **There is no final gap** (Specification p. 203: "There is no final interval of positive length
without interior visits before `σ`"): `ℓ(a) < ℓ(σ)` for every `a ∈ [τ, σ)`. On such an interval the
attachments would stay at `u(a) > 0`, so `α₁(u(a)/2)` would be first visited exactly at `σ`, where
the tip is `x₀ = α₁(0)`. -/
theorem clock_lt_clock_σ (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) {a : ℝ} (ha : a ∈ Ico τ σ) :
    pocketClock η C τ σ a < pocketClock η C τ σ σ := by
  refine lt_of_le_of_ne (hP.monotone_clock ha.2.le) fun hℓ => ?_
  have ha0 : 0 ≤ a := hP.nonneg.trans ha.1
  have hgap : ∀ t ∈ Ico a σ, η t ∉ C := fun t ht htC => by
    obtain ⟨t', ht', ht'I⟩ := hP.exists_mem_Ioo_of_mem ha.2 ⟨ht.1, ht.2.le⟩
      (hP.mem_visitSet (ha0.trans ht.1) htC)
    exact (hP.clock_lt_of_mem ht'.1 ht'.2 ht'I).ne hℓ
  obtain ⟨hu, hu', -, -, -⟩ := hP.chart ha.1 ha.2 (Or.inl rfl)
  set u := firstVisit (fun t => η '' Icc 0 t) α₁ a with hudef
  have hv : u / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  -- `α₁(u/2)` is not visited before `σ`
  have hnot : ∀ b ∈ Ico 0 σ, α₁ (u / 2) ∉ η '' Icc 0 b := by
    intro b hb hvis
    rcases le_or_gt b a with hba | hab
    · have := firstVisit_le (R := fun t => η '' Icc 0 t) (α := α₁) (t := a) hv
        (monotone_image_Icc hba hvis)
      rw [← hudef] at this
      linarith
    · have hc := (hAC a b ha.1 hab.le hb.2 fun t ht => hgap t ⟨ht.1, ht.2.trans_lt hb.2⟩).1
      have := firstVisit_le (R := fun t => η '' Icc 0 t) (α := α₁) (t := b) hv hvis
      rw [hc, ← hudef] at this
      linarith
  have hx : α₁ 0 ∈ η '' Icc 0 σ := ⟨σ, ⟨hP.nonneg_σ, le_rfl⟩, hP.first_x⟩
  obtain ⟨t, ht, hte⟩ := hP.mem_of_x_mem hx (Or.inl rfl) hv
  rcases lt_or_eq_of_le ht.2 with htσ | htσ
  · exact hnot t ⟨ht.1, htσ⟩ ⟨t, ⟨ht.1, le_rfl⟩, hte⟩
  · rw [htσ, hP.first_x] at hte
    have := hP.inj₁ ⟨le_rfl, zero_le_one⟩ hv hte
    linarith

/-- `I ≠ ∅`: the clock reaches a positive terminal value. -/
theorem clock_σ_pos (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) : 0 < pocketClock η C τ σ σ := by
  have := hP.clock_lt_clock_σ hAC ⟨le_rfl, hP.τ_lt_σ⟩
  rwa [clock_τ] at this

theorem fibre_lt_σ (hP : IsReversePocket W η C α₁ α₂ β τ σ) {v : ℝ} (hv : v ∈ Ico 0
    (pocketClock η C τ σ σ)) : pocketFibre η C τ σ v < σ := by
  refine lt_of_le_of_ne (hP.fibre_mem v).2 fun h => ?_
  have := hP.clock_fibre ⟨hv.1, hv.2.le⟩
  rw [h] at this
  exact hv.2.ne this.symm

theorem fibre_clock_σ (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) :
    pocketFibre η C τ σ (pocketClock η C τ σ σ) = σ := by
  refine le_antisymm (hP.fibre_mem _).2 (not_lt.1 fun h => ?_)
  have h1 := hP.clock_fibre ⟨(hP.clock_σ_pos hAC).le, le_rfl⟩
  have h2 := hP.clock_lt_clock_σ hAC ⟨(hP.fibre_mem _).1, h⟩
  rw [h1] at h2
  exact lt_irrefl _ h2

/-- A visit time is the right endpoint of its clock fibre. -/
theorem fibre_clock_of_mem (hP : IsReversePocket W η C α₁ α₂ β τ σ) {t : ℝ}
    (htI : t ∈ visitSet η C τ σ) : pocketFibre η C τ σ (pocketClock η C τ σ t) = t := by
  have htm : t ∈ Icc τ σ := ⟨htI.1.1.le, htI.1.2.le⟩
  refine le_antisymm (not_lt.1 fun h => ?_) (fibreRight_clock htm)
  have hm := fibreRight_mem_set (ℓ := pocketClock η C τ σ) hP.continuous_clock hP.τ_lt_σ.le
    (pocketClock η C τ σ t)
  rw [max_eq_left (hP.monotone_clock htm.1)] at hm
  · exact absurd hm.2 (not_le.2 (hP.clock_lt_of_mem_visitSet htI h))

/-- After the right endpoint of a fibre the clock increases (the hypothesis of `maximal_fibre`). -/
theorem clock_lt_of_fibre (hP : IsReversePocket W η C α₁ α₂ β τ σ) {v : ℝ}
    (hv : v ∈ Icc 0 (pocketClock η C τ σ σ)) :
    ∀ t ∈ Ioc (pocketFibre η C τ σ v) σ,
      pocketClock η C τ σ (pocketFibre η C τ σ v) < pocketClock η C τ σ t := fun t ht => by
  rw [hP.clock_fibre hv]; exact hP.lt_clock_of_fibre_lt hv.1 ht

/-- **(GC1) for the erasure** (Aux. lemma 39 / Proposition 1.5): the trace takes the same value at
the two ends of every nondegenerate maximal fibre of the clock in `[τ, S]`. -/
theorem gc1 (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    {S : ℝ} (hSσ : S ≤ σ)
    (hS : ∀ t ∈ Ioc S σ, pocketClock η C τ σ S < pocketClock η C τ σ t) :
    ∀ a ∈ Icc τ S, ∀ b ∈ Icc τ S, a < b → pocketClock η C τ σ a = pocketClock η C τ σ b →
      (∀ t ∈ Icc τ S, pocketClock η C τ σ t = pocketClock η C τ σ a → t ∈ Icc a b) →
      η a = η b := by
  intro a ha b hb hab hℓ hmax
  have hbσ : b < σ := by
    refine lt_of_le_of_ne (hb.2.trans hSσ) fun h => ?_
    rw [h] at hℓ
    exact (hP.clock_lt_clock_σ hAC ⟨ha.1, hab.trans_le (hb.2.trans hSσ)⟩).ne hℓ
  obtain ⟨hgap, hbcl, hacl⟩ := hP.maximal_fibre le_rfl hS ha hb hab hbσ hℓ hmax
  have hacl' : a = τ ∨ a ∈ closure {t | 0 < t ∧ η t ∈ C} := hacl.imp_right fun h =>
    closure_mono (s := {t | τ < t ∧ η t ∈ C}) (t := {t | 0 < t ∧ η t ∈ C})
      (fun t ht => ⟨hP.nonneg.trans_lt ht.1, ht.2⟩) h
  rcases eq_or_lt_of_le (hP.nonneg.trans ha.1) with h0 | h0
  · -- the initial gap at the original seed (`a = τ = 0`)
    have hτ0 : τ = 0 := le_antisymm (h0 ▸ ha.1) hP.nonneg
    rw [← h0] at hab hgap hbcl ⊢
    exact hP.gap_eq_seed hAC hτ0 hab hbσ hgap hbcl
  · exact (hP.gap_eq hAC le_rfl h0 ha.1 hab hbσ hgap hacl' hbcl).2

/-- **Aux. lemma 40, the continuous erasure**: `γ̂_C` is continuous on `[0, ℓ(σ)]`. -/
theorem continuousOn_erasedPath (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) :
    ContinuousOn (erasedPath η C τ σ) (Icc 0 (pocketClock η C τ σ σ)) := by
  have h := continuousOn_comp_fibreRight hP.continuous_clock hP.monotone_clock hP.τ_lt_σ.le
    (hP.trace.2.1.mono fun t ht => hP.nonneg.trans ht.1)
    (hP.gc1 hAC le_rfl fun t ht => absurd ht.2 (not_le.2 ht.1))
  rwa [clock_τ] at h

/-- The erased path starts at `y₀`. -/
theorem erasedPath_zero (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) : erasedPath η C τ σ 0 = α₁ 1 := by
  have hpos := hP.clock_σ_pos hAC
  have hm := hP.fibre_mem 0
  have hc0 := hP.clock_fibre ⟨le_rfl, hpos.le⟩
  rcases eq_or_lt_of_le hm.1 with h | h
  · rw [erasedPath, ← h, hP.first_y]
  · have hlt := hP.fibre_lt_σ ⟨le_rfl, hpos⟩
    rw [erasedPath, ← hP.first_y]
    refine (hP.gc1 hAC hlt.le (hP.clock_lt_of_fibre ⟨le_rfl, hpos.le⟩) τ ⟨le_rfl, h.le⟩ _
      ⟨h.le, le_rfl⟩ h (by rw [hc0, clock_τ]) fun t ht hℓ => ⟨ht.1, ht.2⟩).symm ▸ rfl

/-- The erased path ends at `x₀`. -/
theorem erasedPath_clock_σ (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) :
    erasedPath η C τ σ (pocketClock η C τ σ σ) = α₁ 0 := by
  rw [erasedPath, hP.fibre_clock_σ hAC, hP.first_x]

/-- Before its terminal time the erased path is in `C̄ \ {x₀}`. -/
theorem erasedPath_mem (hP : IsReversePocket W η C α₁ α₂ β τ σ) {v : ℝ}
    (hv : v ∈ Ico 0 (pocketClock η C τ σ σ)) : erasedPath η C τ σ v ∈ closure C \ {α₁ 0} := by
  have hlt := hP.fibre_lt_σ hv
  have hm := hP.fibre_mem v
  have h0 : 0 ≤ pocketFibre η C τ σ v := hP.nonneg.trans hm.1
  refine ⟨hP.mem_closure_of_mem_closure_visits h0
    (hP.mem_closure_of_right hlt (hP.clock_lt_of_fibre ⟨hv.1, hv.2.le⟩)), fun h => ?_⟩
  exact hP.fresh_x ⟨_, ⟨h0, hlt⟩, h⟩

/-- **(GC2)** (Specification p. 203): erasure changes no range in `C`:
`γ̂_C([0, u]) ∩ C = R_{fR(u)} ∩ C`. -/
theorem erasedPath_image_inter (hP : IsReversePocket W η C α₁ α₂ β τ σ) {u : ℝ}
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

end IsReversePocket

end InteractingSLE.Sec6
