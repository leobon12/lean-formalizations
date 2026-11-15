import InteractingSLE.Foundations.Loewner.CapacityEstimates
import InteractingSLE.Foundations.Loewner.Capacity
import InteractingSLE.Foundations.Topology.PathComplement

/-!
# Section 6.2: the criterion for a continuous Loewner driving function

Specification §6.2 (`source/spec/p193-240.md`, pp. 210–212): Proposition 6.12 and **Aux.** lemma 44.

A continuous path `η : [0, S] → ℍ̄` with `η 0 = 0` is studied through its filled hulls
`K_t = fillH (η '' Icc 0 t)`; `ℍ \ K_t` is the unbounded component of `ℍ \ η([0, t])`
(`H_diff_fillH`).

## Main definitions

* `HasSimpleApproxOn η S`: the specification's **non-crossing convention** (p. 211, "Precise
  convention for non-crossing in this criterion") on the compact parameter interval `[0, S]`: `η`
  is the uniform limit on `[0, S]` of injective continuous paths `γ_n` with `γ_n 0 = 0` and
  `γ_n ((0, S]) ⊆ ℍ`.
* `DrivingCriterionA η S`, `DrivingCriterionB η S`: hypotheses (a) and (b) of Proposition 6.12 on
  `[0, S]`.
* `YuanDriverInput`: the deterministic literature input of the proof of Proposition 6.12
  ([Yua22, Theorem 1.1, (iii) ⇒ (i)] with the Loewner transform of a locally growing family), in
  the compact-interval form the specification applies. It is **not proved here** (packet
  PROVE-GEO-YUAN); it is only used as the explicit hypothesis of the conditional helper
  `exists_driver_of_drivingCriteria_of_yuanDriverInput`.

## Main results

* `HasSimpleApproxOn.mono`, `DrivingCriterionA.mono`, `DrivingCriterionB.mono`: the hypotheses on
  `[0, S']` restrict to `[0, S]`, `S ≤ S'` (the source states them on `[0, T)` and applies the
  proposition on every `[0, S]`, `S < T`).
* `fillH_ssubset_of_drivingCriteria`: **strict growth** (the first step of the proof of
  Proposition 6.12): under (a) and (b) the filled hulls strictly increase, `K_s ⊊ K_t` for
  `0 ≤ s < t ≤ S`.
* `hasSimpleApproxOn_of_injOn`: **Aux. lemma 44**: a continuous injective path `[0, S] → ℍ̄` started
  at `0` has the uniform simple approximations of the non-crossing convention;
  `hasSimpleApproxOn_comp_of_injOn`: its last assertion (transport by a continuous injective map,
  such as a Jordan boundary homeomorphism).
* `eqOn_of_fwdHull_eq`, `eqOn_clock_and_driver_of_fwdHull_eq`: the hulls determine the driver and
  the capacity clock, so the drivers of the finite-interval forms agree on overlaps (proved).
* `exists_driver_of_drivingCriteria_of_yuanDriverInput`: Proposition 6.12 on `[0, S]`, conditional
  on `YuanDriverInput` (distinct name; the source theorem itself is not claimed).

## Reading of the source

Hypothesis (a) speaks of the closure of "the unbounded connected component of `ℍ \ η((0, t))`". As
`η 0 = 0 ∉ ℍ`, `ℍ \ η((0, t))` differs from `ℍ \ η([0, t])` at most by the point `η(t)`; both
unbounded components have the same closure, `closure (ℍ \ K_t)`, which is the form used here (and
in the source's proof: "`η(u)` in `K_r ∩ closure D_r`").
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec6

/-! ### The non-crossing convention and the two criteria -/

/-- The specification's **non-crossing convention** for Proposition 6.12 (p. 211) on the compact
parameter interval `[0, S]`: `η` is the uniform limit on `[0, S]` of injective continuous paths
`γ_n : [0, S] → ℍ̄` with `γ_n 0 = 0` and `γ_n ((0, S]) ⊆ ℍ`. -/
def HasSimpleApproxOn (η : ℝ → ℂ) (S : ℝ) : Prop :=
  ∃ γ : ℕ → ℝ → ℂ, (∀ n, ContinuousOn (γ n) (Icc 0 S) ∧ InjOn (γ n) (Icc 0 S) ∧ γ n 0 = 0 ∧
      MapsTo (γ n) (Ioc 0 S) H) ∧ TendstoUniformlyOn γ η atTop (Icc 0 S)

/-- **Criterion (a) of Proposition 6.12** on `[0, S]`: for every `t ∈ (0, S)`, `η((t, S])` lies in
the closure of the unbounded component `ℍ \ K_t` of `ℍ \ η([0, t])`. -/
def DrivingCriterionA (η : ℝ → ℂ) (S : ℝ) : Prop :=
  ∀ t ∈ Ioo 0 S, η '' Ioc t S ⊆ closure (H \ fillH (η '' Icc 0 t))

/-- **Criterion (b) of Proposition 6.12** on `[0, S]`: for every `t ∈ (0, S)`, the set of times
`u ∈ (t, S)` with `η(u) ∈ η([0, t]) ∪ ℝ` has empty interior. -/
def DrivingCriterionB (η : ℝ → ℂ) (S : ℝ) : Prop :=
  ∀ t ∈ Ioo 0 S, interior {u ∈ Ioo t S | η u ∈ η '' Icc 0 t ∨ (η u).im = 0} = ∅

/-- The non-crossing convention restricts to shorter compact intervals (so a path non-crossing on
`[0, T)` in the source's sense is non-crossing on each `[0, S]`, `S < T`). -/
theorem HasSimpleApproxOn.mono {η : ℝ → ℂ} {S S' : ℝ} (h : HasSimpleApproxOn η S') (hSS' : S ≤ S') :
    HasSimpleApproxOn η S := by
  obtain ⟨γ, hγ, hlim⟩ := h
  have hsub : Icc 0 S ⊆ Icc 0 S' := Icc_subset_Icc_right hSS'
  exact ⟨γ, fun n => ⟨(hγ n).1.mono hsub, (hγ n).2.1.mono hsub, (hγ n).2.2.1,
    (hγ n).2.2.2.mono_left (Ioc_subset_Ioc_right hSS')⟩, hlim.mono hsub⟩

/-- Criterion (a) restricts to shorter compact intervals. -/
theorem DrivingCriterionA.mono {η : ℝ → ℂ} {S S' : ℝ} (h : DrivingCriterionA η S') (hSS' : S ≤ S') :
    DrivingCriterionA η S := fun t ht =>
  (image_mono (Ioc_subset_Ioc_right hSS')).trans (h t ⟨ht.1, ht.2.trans_le hSS'⟩)

/-- Criterion (b) restricts to shorter compact intervals. -/
theorem DrivingCriterionB.mono {η : ℝ → ℂ} {S S' : ℝ} (h : DrivingCriterionB η S') (hSS' : S ≤ S') :
    DrivingCriterionB η S := fun t ht => by
  refine subset_empty_iff.1 ((h t ⟨ht.1, ht.2.trans_le hSS'⟩) ▸ interior_mono ?_)
  rintro u ⟨hu, h'⟩
  exact ⟨⟨hu.1, hu.2.trans_le hSS'⟩, h'⟩

/-! ### Strict growth of the filled hulls -/

/-- A point of `ℍ` in a filled hull `fillH A` (`A` closed and bounded) that is also in the closure
of the complement `ℍ \ fillH A` lies on `A` itself ("the boundary of a filled trace is contained in
its trace together with `ℝ`"). -/
theorem mem_of_mem_fillH_of_mem_closure {A : Set ℂ} (hA : IsClosed A) (hAb : Bornology.IsBounded A)
    {z : ℂ} (hz : z ∈ H) (hzK : z ∈ fillH A) (hzc : z ∈ closure (H \ fillH A)) : z ∈ A := by
  have hfr : z ∈ frontier (H \ fillH A) := by
    rw [(isOpen_H_diff_fillH hAb).frontier_eq]
    exact ⟨hzc, fun h => h.2 hzK⟩
  rcases frontier_H_diff_fillH_subset hAb hfr with h | h
  · exact absurd h (ne_of_gt (show 0 < z.im from hz))
  · rwa [hA.closure_eq] at h

variable {η : ℝ → ℂ} {S : ℝ}

theorem fillH_image_Icc_mono {s t : ℝ} (hst : s ≤ t) :
    fillH (η '' Icc 0 s) ⊆ fillH (η '' Icc 0 t) :=
  fillH_mono (image_mono (Icc_subset_Icc_right hst))

/-- **Strict growth** (Specification p. 211, first paragraph of the proof of Proposition 6.12):
under criteria (a) and (b) the filled hulls `K_t = fillH (η([0, t]))` strictly increase on
`[0, S]`. If `K_s = K_t` with `s < t`, then for `r = (s + t)/2` and `u ∈ (r, t)` criterion (a)
puts `η(u)` in `closure (ℍ \ K_r)`, while `η(u) ∈ K_t = K_r` unless `η(u)` is real; so
`η((r, t)) ⊆ η([0, r]) ∪ ℝ`, against criterion (b) at time `r`. -/
theorem fillH_ssubset_of_drivingCriteria (hc : ContinuousOn η (Icc 0 S))
    (ha : DrivingCriterionA η S) (hb : DrivingCriterionB η S) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s < t) (htS : t ≤ S) : fillH (η '' Icc 0 s) ⊂ fillH (η '' Icc 0 t) := by
  refine ssubset_iff_subset_ne.2 ⟨fillH_image_Icc_mono hst.le, fun heq => ?_⟩
  set r := (s + t) / 2 with hr
  have hsr : s < r := by rw [hr]; linarith
  have hrt : r < t := by rw [hr]; linarith
  have hr0 : r ∈ Ioo 0 S := ⟨by linarith, by linarith⟩
  have hKr : fillH (η '' Icc 0 r) = fillH (η '' Icc 0 t) :=
    (fillH_image_Icc_mono hrt.le).antisymm (heq ▸ fillH_image_Icc_mono hsr.le)
  have hcomp : IsCompact (η '' Icc 0 r) :=
    isCompact_Icc.image_of_continuousOn (hc.mono (Icc_subset_Icc_right (by linarith)))
  have hsub : Ioo r t ⊆ {u ∈ Ioo r S | η u ∈ η '' Icc 0 r ∨ (η u).im = 0} := by
    intro u hu
    refine ⟨⟨hu.1, by linarith [hu.2]⟩, ?_⟩
    have hcl : η u ∈ closure (H \ fillH (η '' Icc 0 r)) :=
      ha r hr0 ⟨u, ⟨hu.1, by linarith [hu.2]⟩, rfl⟩
    rcases eq_or_ne (η u).im 0 with h0 | h0
    · exact Or.inr h0
    left
    have hHbar : η u ∈ Hbar := by
      rw [← QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact closure_mono sdiff_subset hcl
    have hH : η u ∈ H := lt_of_le_of_ne (show (0 : ℝ) ≤ (η u).im from hHbar) h0.symm
    have hK : η u ∈ fillH (η '' Icc 0 r) := by
      rw [hKr]
      exact mem_fillH_of_mem_closure hH
        (subset_closure ⟨u, ⟨by linarith [hu.1], hu.2.le⟩, rfl⟩)
    exact mem_of_mem_fillH_of_mem_closure hcomp.isClosed hcomp.isBounded hH hK hcl
  have hne : (Ioo r t).Nonempty := nonempty_Ioo.2 hrt
  have hint := interior_mono hsub
  rw [isOpen_Ioo.interior_eq, hb r hr0] at hint
  exact hne.ne_empty (subset_empty_iff.1 hint)

/-- Strict growth in the order form used by [Yua22] Theorem 1.1. -/
theorem strictMonoOn_fillH_of_drivingCriteria (hc : ContinuousOn η (Icc 0 S))
    (ha : DrivingCriterionA η S) (hb : DrivingCriterionB η S) :
    StrictMonoOn (fun t => fillH (η '' Icc 0 t)) (Icc 0 S) :=
  fun _ hs _ ht hst => fillH_ssubset_of_drivingCriteria hc ha hb hs.1 hst ht.2

/-! ### Aux. lemma 44: simple approximations of an injective path

For `0 < s < S` and `ε > 0` the approximating path follows the vertical segment from `0` to `iε` on
`[0, s]` and then the translate `γ + iε`, reparametrized affinely from `[s, S]` onto `[0, S]`. -/

/-- The affine clock of Aux. lemma 44: `[s, S] → [0, S]`, constant `0` on `[0, s]`. -/
def approxClock (S s t : ℝ) : ℝ := S * (max t s - s) / (S - s)

/-- The approximating path of **Aux. lemma 44** (Specification p. 212): `t ↦ iεt/s` on `[0, s]` and
`t ↦ γ(S(t − s)/(S − s)) + iε` on `[s, S]` (one formula: `γ(0) = 0` makes the pieces agree). -/
def simpleApprox (γ : ℝ → ℂ) (S s ε t : ℝ) : ℂ :=
  γ (approxClock S s t) + ((ε * min (t / s) 1 : ℝ) : ℂ) * I

variable {s : ℝ}

theorem approxClock_of_le {t : ℝ} (ht : t ≤ s) : approxClock S s t = 0 := by
  simp [approxClock, max_eq_right ht]

theorem approxClock_mem (hs : 0 < s) (hsS : s < S) {t : ℝ} (ht : t ∈ Icc 0 S) :
    approxClock S s t ∈ Icc 0 S := by
  have hSs : 0 < S - s := sub_pos.2 hsS
  have h1 : 0 ≤ max t s - s := sub_nonneg.2 (le_max_right _ _)
  have h2 : max t s - s ≤ S - s := by
    have : max t s ≤ S := max_le ht.2 hsS.le
    linarith
  refine ⟨div_nonneg (mul_nonneg (hs.trans hsS).le h1) hSs.le, ?_⟩
  rw [approxClock, div_le_iff₀ hSs]
  exact mul_le_mul_of_nonneg_left h2 (hs.trans hsS).le

theorem abs_approxClock_sub_le (hs : 0 < s) (hsS : s < S) {t : ℝ} (ht : t ∈ Icc 0 S) :
    |approxClock S s t - t| ≤ s := by
  have hSs : 0 < S - s := sub_pos.2 hsS
  rcases le_total t s with hts | hst
  · rw [approxClock_of_le hts, zero_sub, abs_neg, abs_of_nonneg ht.1]; exact hts
  · have hc : approxClock S s t - t = -(s * (S - t) / (S - s)) := by
      rw [approxClock, max_eq_left hst]; field_simp; ring
    rw [hc, abs_neg, abs_of_nonneg (div_nonneg (mul_nonneg hs.le (sub_nonneg.2 ht.2)) hSs.le),
      div_le_iff₀ hSs]
    exact mul_le_mul_of_nonneg_left (by linarith) hs.le

theorem approxClock_injOn (hs : 0 < s) (hsS : s < S) : InjOn (approxClock S s) (Ici s) := by
  intro t ht t' ht' h
  have hSs : 0 < S - s := sub_pos.2 hsS
  simp only [approxClock, max_eq_left (show s ≤ t from ht), max_eq_left (show s ≤ t' from ht')] at h
  have h1 := mul_left_cancel₀ (hs.trans hsS).ne' ((div_left_inj' hSs.ne').1 h)
  linarith

theorem simpleApprox_of_le {γ : ℝ → ℂ} (h0 : γ 0 = 0) (ε : ℝ) {t : ℝ} (ht : t ≤ s) :
    simpleApprox γ S s ε t = ((ε * min (t / s) 1 : ℝ) : ℂ) * I := by
  rw [simpleApprox, approxClock_of_le ht, h0, zero_add]

theorem simpleApprox_of_ge {γ : ℝ → ℂ} (hs : 0 < s) (ε : ℝ) {t : ℝ} (ht : s ≤ t) :
    simpleApprox γ S s ε t = γ (approxClock S s t) + (ε : ℂ) * I := by
  rw [simpleApprox, min_eq_right ((one_le_div hs).2 ht), mul_one]

theorem simpleApprox_im (γ : ℝ → ℂ) (S s ε t : ℝ) :
    (simpleApprox γ S s ε t).im = (γ (approxClock S s t)).im + ε * min (t / s) 1 := by
  simp [simpleApprox]

theorem continuousOn_simpleApprox {γ : ℝ → ℂ} (hc : ContinuousOn γ (Icc 0 S)) (hs : 0 < s)
    (hsS : s < S) (ε : ℝ) : ContinuousOn (simpleApprox γ S s ε) (Icc 0 S) := by
  have hcl : Continuous (approxClock S s) := by unfold approxClock; fun_prop
  refine (hc.comp hcl.continuousOn fun t ht => approxClock_mem hs hsS ht).add ?_
  exact (Continuous.continuousOn (by fun_prop))

theorem simpleApprox_zero {γ : ℝ → ℂ} (h0 : γ 0 = 0) (hs : 0 < s) (ε : ℝ) :
    simpleApprox γ S s ε 0 = 0 := by
  rw [simpleApprox_of_le h0 ε hs.le]; simp

theorem simpleApprox_mem_H {γ : ℝ → ℂ} (hH : MapsTo γ (Icc 0 S) Hbar) (hs : 0 < s) (hsS : s < S)
    {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : t ∈ Ioc 0 S) : simpleApprox γ S s ε t ∈ H := by
  show 0 < (simpleApprox γ S s ε t).im
  rw [simpleApprox_im]
  have h1 : (0 : ℝ) ≤ (γ (approxClock S s t)).im :=
    hH (approxClock_mem hs hsS (Ioc_subset_Icc_self ht))
  have h2 : 0 < min (t / s) 1 := lt_min (div_pos ht.1 hs) one_pos
  nlinarith [mul_pos hε h2]

theorem injOn_simpleApprox {γ : ℝ → ℂ} (hinj : InjOn γ (Icc 0 S)) (h0 : γ 0 = 0)
    (hH : MapsTo γ (Icc 0 S) Hbar) (hs : 0 < s) (hsS : s < S) {ε : ℝ} (hε : 0 < ε) :
    InjOn (simpleApprox γ S s ε) (Icc 0 S) := by
  -- a point of the vertical segment strictly below height `ε` is not on the translated piece
  have hlow : ∀ t ∈ Icc 0 S, ∀ t' ∈ Icc 0 S, t < s → s ≤ t' →
      simpleApprox γ S s ε t ≠ simpleApprox γ S s ε t' := by
    intro t ht t' ht' hts hst' h
    have him := congrArg Complex.im h
    rw [simpleApprox_im, simpleApprox_im, approxClock_of_le hts.le, h0,
      min_eq_left ((div_le_one hs).2 hts.le), min_eq_right ((one_le_div hs).2 hst')] at him
    have h1 : (0 : ℝ) ≤ (γ (approxClock S s t')).im := hH (approxClock_mem hs hsS ht')
    have h2 : t / s < 1 := (div_lt_one hs).2 hts
    simp only [Complex.zero_im, zero_add] at him
    nlinarith
  intro t ht t' ht' h
  rcases lt_or_ge t s with hts | hst <;> rcases lt_or_ge t' s with hts' | hst'
  · rw [simpleApprox_of_le h0 ε hts.le, simpleApprox_of_le h0 ε hts'.le] at h
    have him := congrArg Complex.im h
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero] at him
    rw [min_eq_left ((div_le_one hs).2 hts.le), min_eq_left ((div_le_one hs).2 hts'.le)] at him
    have := mul_left_cancel₀ hε.ne' him
    field_simp at this
    exact this
  · exact absurd h (hlow t ht t' ht' hts hst')
  · exact absurd h.symm (hlow t' ht' t ht hts' hst)
  · rw [simpleApprox_of_ge hs ε hst, simpleApprox_of_ge hs ε hst', add_left_inj] at h
    exact approxClock_injOn hs hsS hst hst'
      (hinj (approxClock_mem hs hsS ht) (approxClock_mem hs hsS ht') h)

theorem dist_simpleApprox_le {γ : ℝ → ℂ} {ε : ℝ} (hε : 0 ≤ ε) (hs : 0 ≤ s) {t : ℝ} (ht : 0 ≤ t) :
    dist (γ t) (simpleApprox γ S s ε t) ≤ dist (γ t) (γ (approxClock S s t)) + ε := by
  rw [simpleApprox, dist_eq_norm, dist_eq_norm]
  have h3 : ‖((ε * min (t / s) 1 : ℝ) : ℂ) * I‖ ≤ ε := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hε (le_min (div_nonneg ht hs) zero_le_one))]
    exact mul_le_of_le_one_right hε (min_le_right _ _)
  calc ‖γ t - (γ (approxClock S s t) + ((ε * min (t / s) 1 : ℝ) : ℂ) * I)‖
      = ‖(γ t - γ (approxClock S s t)) - ((ε * min (t / s) 1 : ℝ) : ℂ) * I‖ := by ring_nf
    _ ≤ _ := (norm_sub_le _ _).trans (by linarith)

/-- **Aux. lemma 44** (simple paths that touch the boundary; Specification p. 212): a continuous
injective path `γ : [0, S] → ℍ̄` with `γ 0 = 0` and `S > 0` has the uniform simple approximations
required by the non-crossing convention of Proposition 6.12. The approximations are
`simpleApprox γ S (S/(n+2)) (1/(n+1))`: the vertical segment `[0, iε]` followed by the translate
`γ + iε`, reparametrized; their distance to `γ` is at most `ε` plus the oscillation of `γ` over
time steps `≤ S/(n+2)`. -/
theorem hasSimpleApproxOn_of_injOn {γ : ℝ → ℂ} (hS : 0 < S) (hc : ContinuousOn γ (Icc 0 S))
    (hinj : InjOn γ (Icc 0 S)) (h0 : γ 0 = 0) (hH : MapsTo γ (Icc 0 S) Hbar) :
    HasSimpleApproxOn γ S := by
  set s : ℕ → ℝ := fun n => S / ((n : ℝ) + 2) with hsdef
  set e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hedef
  have hs : ∀ n, 0 < s n := fun n => div_pos hS (by positivity)
  have hsS : ∀ n, s n < S := fun n => by
    rw [hsdef]; dsimp only
    rw [div_lt_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have he : ∀ n, 0 < e n := fun n => by positivity
  refine ⟨fun n => simpleApprox γ S (s n) (e n), fun n => ⟨continuousOn_simpleApprox hc (hs n)
    (hsS n) _, injOn_simpleApprox hinj h0 hH (hs n) (hsS n) (he n), simpleApprox_zero h0 (hs n) _,
    fun t ht => simpleApprox_mem_H hH (hs n) (hsS n) (he n) ht⟩, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (S / δ) (2 / ε))
  refine eventually_atTop.2 ⟨N, fun n hn t ht => ?_⟩
  have hnN : (N : ℝ) ≤ n := Nat.cast_le.2 hn
  have hsn : s n < δ := by
    have h1 : S / δ < (n : ℝ) + 2 := by linarith [le_max_left (S / δ) (2 / ε)]
    rw [div_lt_iff₀ hδ] at h1
    show S / ((n : ℝ) + 2) < δ
    rw [div_lt_iff₀ (by positivity)]; linarith
  have hen : e n < ε / 2 := by
    have h1 : 2 / ε < (n : ℝ) + 1 := by linarith [le_max_right (S / δ) (2 / ε)]
    rw [div_lt_iff₀ hε] at h1
    show 1 / ((n : ℝ) + 1) < ε / 2
    rw [div_lt_iff₀ (by positivity)]; linarith
  have hcl := approxClock_mem (hs n) (hsS n) ht
  have hd : dist (γ t) (γ (approxClock S (s n) t)) < ε / 2 := by
    refine hδε t ht _ hcl ?_
    rw [Real.dist_eq, abs_sub_comm]
    exact (abs_approxClock_sub_le (hs n) (hsS n) ht).trans_lt hsn
  have := dist_simpleApprox_le (γ := γ) (S := S) (he n).le (hs n).le ht.1
  show dist (γ t) (simpleApprox γ S (s n) (e n) t) < ε
  linarith


/-- The last assertion of **Aux. lemma 44**: a continuous injective map `Ψ` into `ℍ̄` (such as a
Jordan boundary homeomorphism) sends a continuous injective path to a path with the uniform simple
approximations of the non-crossing convention, provided the image starts at `0`. -/
theorem hasSimpleApproxOn_comp_of_injOn {γ : ℝ → ℂ} {Ψ : ℂ → ℂ} {E : Set ℂ} (hS : 0 < S)
    (hc : ContinuousOn γ (Icc 0 S)) (hinj : InjOn γ (Icc 0 S)) (hγE : MapsTo γ (Icc 0 S) E)
    (hΨc : ContinuousOn Ψ E) (hΨi : InjOn Ψ E) (hΨH : MapsTo Ψ E Hbar) (h0 : Ψ (γ 0) = 0) :
    HasSimpleApproxOn (Ψ ∘ γ) S :=
  hasSimpleApproxOn_of_injOn hS (hΨc.comp hc hγE) (hΨi.comp hinj hγE) h0 (hΨH.comp hγE)

/-! ### The driver is determined by the hulls -/

/-- **Drivers agree on overlaps** (proof of Proposition 6.12, last paragraph: "the resulting drivers
agree on overlaps by uniqueness of the hydrodynamically normalized maps"): two continuous drivers
started at `0` with the same chordal Loewner hulls on `[0, S]` agree on `[0, S]`. For a point `z`
outside the hulls the two mapping-out functions agree (`IsMapOut.eqOn`), so the integrated Loewner
equations give `∫₀ˢ (2/f_r(z) − 2/f'_r(z)) dr = 0` for all `s`; the fundamental theorem of calculus
makes the continuous integrand vanish, i.e. `g_s(z) − W_s = g_s(z) − W'_s`. -/
theorem eqOn_of_fwdHull_eq {W W' : ℝ → ℝ} (hW : Continuous W) (hW' : Continuous W')
    (hW0 : W 0 = 0) (hW0' : W' 0 = 0) {S : ℝ} (hS : 0 ≤ S)
    (h : ∀ s ∈ Icc 0 S, QuantumZipper.fwdHull W s = QuantumZipper.fwdHull W' s) :
    EqOn W W' (Icc 0 S) := by
  rcases hS.eq_or_lt with rfl | hS
  · intro s hs
    obtain rfl : s = 0 := le_antisymm hs.2 hs.1
    rw [hW0, hW0']
  -- a point outside the hulls
  obtain ⟨R, hR⟩ := (isBounded_fwdHull hW S).subset_ball 0
  set z : ℂ := ((|R| + 1 : ℝ) : ℂ) * I with hz
  have hz0 : 0 < z.im := by
    simp only [hz, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    positivity
  have hzH : z ∈ H := hz0
  have hzK : z ∉ QuantumZipper.fwdHull W S := fun hK => by
    have := mem_ball_zero_iff.1 (hR hK)
    rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)] at this
    linarith [le_abs_self R]
  have hzK' : z ∉ QuantumZipper.fwdHull W' S := by rw [← h S ⟨hS.le, le_rfl⟩]; exact hzK
  obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hS.le hzH hzK
  obtain ⟨u', hu'⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hS.le hzH hzK'
  -- the mapping-out functions agree at `z`
  have hG : ∀ s ∈ Icc 0 S, u s + W s = u' s + W' s := by
    intro s hs
    have h1 := isMapOut_fwdMap hW hW0 hs.1
    have h2 := isMapOut_fwdMap hW' hW0' hs.1
    rw [← h s hs] at h2
    have hzs : z ∈ H \ QuantumZipper.fwdHull W s :=
      ⟨hzH, fun hzs => hzK (QuantumZipper.fwdHull_mono.1 hs.2 hzs)⟩
    have := IsMapOut.eqOn (isHPHull_fwdHull hW hs.1) h1 h2 hzs
    simp only at this
    rwa [QuantumZipper.fwdMap_eq hW hz0 hu hs, QuantumZipper.fwdMap_eq hW' hz0 hu' hs] at this
  -- the integrated Loewner equations
  set ψ : ℝ → ℂ := fun r => 2 / u r - 2 / u' r with hψ
  have hc : ∀ v : ℝ → ℂ, QuantumZipper.IsForwardSol W z S v ∨ QuantumZipper.IsForwardSol W' z S v →
      ContinuousOn (fun r => 2 / v r) (Icc 0 S) := by
    rintro v (hv | hv) <;> exact continuousOn_const.div hv.1 fun r hr => (hv.2 r hr).1
  have hψc : ContinuousOn ψ (Icc 0 S) := (hc u (Or.inl hu)).sub (hc u' (Or.inr hu'))
  have hF : ∀ s ∈ Icc 0 S, ∫ r in (0 : ℝ)..s, ψ r = 0 := by
    intro s hs
    have hsub : uIcc 0 s ⊆ Icc 0 S := by rw [uIcc_of_le hs.1]; exact Icc_subset_Icc_right hs.2
    rw [hψ, intervalIntegral.integral_sub (((hc u (Or.inl hu)).mono hsub).intervalIntegrable)
      (((hc u' (Or.inr hu')).mono hsub).intervalIntegrable)]
    have e1 := (hu.2 s hs).2
    have e2 := (hu'.2 s hs).2
    linear_combination (-1 : ℂ) * e1 + e2 + hG s hs
  -- the integrand vanishes on `[0, S)`
  have hψ0 : ∀ s ∈ Ico 0 S, ψ s = 0 := by
    intro s hs
    have hIcc : Icc 0 S ∈ 𝓝[>] s :=
      mem_of_superset (Ioo_mem_nhdsGT hs.2) fun r hr => ⟨hs.1.trans hr.1.le, hr.2.le⟩
    have hint : IntervalIntegrable ψ MeasureTheory.volume 0 s := by
      refine (hψc.mono ?_).intervalIntegrable
      rw [uIcc_of_le hs.1]; exact Icc_subset_Icc_right hs.2.le
    have hmeas : StronglyMeasurableAtFilter ψ (𝓝[>] s) MeasureTheory.volume :=
      ⟨Ioo s S, Ioo_mem_nhdsGT hs.2,
        (hψc.mono fun r hr => ⟨hs.1.trans hr.1.le, hr.2.le⟩).aestronglyMeasurable measurableSet_Ioo⟩
    have hcont : ContinuousWithinAt ψ (Ioi s) s :=
      (hψc s ⟨hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin hIcc
    have h1 : HasDerivWithinAt (fun v => ∫ r in (0 : ℝ)..v, ψ r) (ψ s) (Ici s) s :=
      intervalIntegral.integral_hasDerivWithinAt_right hint hmeas hcont
    have h2 : HasDerivWithinAt (fun v => ∫ r in (0 : ℝ)..v, ψ r) 0 (Ici s) s :=
      (hasDerivWithinAt_const s (Ici s) (0 : ℂ)).congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (Ico_mem_nhdsGE hs.2)
          fun v hv => hF v ⟨hs.1.trans hv.1, hv.2.le⟩) (hF s ⟨hs.1, hs.2.le⟩)
    exact (uniqueDiffWithinAt_Ici s).eq_deriv _ h1 h2
  have hEq : EqOn W W' (Ico 0 S) := by
    intro s hs
    have hs' : s ∈ Icc 0 S := ⟨hs.1, hs.2.le⟩
    have h0 := hψ0 s hs
    simp only [hψ, sub_eq_zero] at h0
    have hu0 := (hu.2 s hs').1
    have hu0' := (hu'.2 s hs').1
    have huu : u s = u' s := by
      have := mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0)
        (show 2 * (u s)⁻¹ = 2 * (u' s)⁻¹ by simpa [div_eq_mul_inv] using h0)
      exact inv_inj.1 this
    have := hG s hs'
    rw [huu, add_right_inj] at this
    exact_mod_cast this
  exact hEq.of_subset_closure hW.continuousOn hW'.continuousOn Ico_subset_Icc_self
    (by rw [closure_Ico hS.ne])

/-- **The capacity clock and the driver are canonical** (proof of Proposition 6.12: the finite
interval forms "agree on overlaps"): if `W, σ` and `W', σ'` produce the same hulls on `[0, S]`,
`fwdHull W (σ t) = fwdHull W' (σ' t)`, with `σ` continuous and monotone from `σ 0 = 0` and `σ' ≥ 0`,
then `σ = σ'` on `[0, S]` (both are `hcap(K_t)/2`, `hcap_fwdHull`) and `W = W'` on `[0, σ S]`
(`eqOn_of_fwdHull_eq`; by the intermediate value theorem every capacity time `r ≤ σ S` is some
`σ t`). -/
theorem eqOn_clock_and_driver_of_fwdHull_eq {W W' σ σ' : ℝ → ℝ} (hW : Continuous W)
    (hW' : Continuous W') (hW0 : W 0 = 0) (hW0' : W' 0 = 0) {S : ℝ} (hS : 0 ≤ S)
    (hσ0 : σ 0 = 0) (hσm : MonotoneOn σ (Icc 0 S)) (hσc : ContinuousOn σ (Icc 0 S))
    (hσ' : ∀ t ∈ Icc 0 S, 0 ≤ σ' t)
    (h : ∀ t ∈ Icc 0 S, QuantumZipper.fwdHull W (σ t) = QuantumZipper.fwdHull W' (σ' t)) :
    EqOn σ σ' (Icc 0 S) ∧ EqOn W W' (Icc 0 (σ S)) := by
  have hσnn : ∀ t ∈ Icc 0 S, 0 ≤ σ t := fun t ht =>
    hσ0 ▸ hσm ⟨le_rfl, hS⟩ ht ht.1
  have hclock : EqOn σ σ' (Icc 0 S) := by
    intro t ht
    have h1 := hcap_fwdHull hW hW0 (hσnn t ht)
    have h2 := hcap_fwdHull hW' hW0' (hσ' t ht)
    have heq : (⟨QuantumZipper.fwdHull W (σ t), isHPHull_fwdHull hW (hσnn t ht)⟩ : HPHull) =
        ⟨QuantumZipper.fwdHull W' (σ' t), isHPHull_fwdHull hW' (hσ' t ht)⟩ :=
      Subtype.ext (h t ht)
    rw [heq, h2] at h1
    linarith
  refine ⟨hclock, eqOn_of_fwdHull_eq hW hW' hW0 hW0' (hσnn S ⟨hS, le_rfl⟩) fun r hr => ?_⟩
  have hivt := intermediate_value_Icc hS hσc
  rw [hσ0] at hivt
  obtain ⟨t, ht, rfl⟩ := hivt hr
  rw [h t ht, hclock ht]

/-! ### Proposition 6.12, conditional on Yuan's characterization -/

/-- **External input of the proof of Proposition 6.12** (not proved here; packet PROVE-GEO-YUAN):
[Yua22, Theorem 1.1, (iii) ⇒ (i)] (a continuous path started on `ℝ` whose filled hulls strictly
increase and which is a uniform limit of simple paths has the local growth property; [TY20,
Proposition 6.3]) together with the Loewner transform of a strictly increasing locally growing
family ([Yua22] §2: half-plane capacity is then a continuous strictly increasing parameter and the
driving function is continuous), in the compact-interval form the specification applies (p. 211,
"Its finite-interval form is obtained by restricting to any `[0, S]`"). The conclusion says that,
after the time change `σ` (`σ(t) = hcap(K_t)/2`, `hcap_fwdHull`), the hulls are those of the
chordal Loewner chain (QuantumZipper `fwdHull`, the solution of `∂_t g_t = 2/(g_t − W_t)`) of a
continuous driver `W`.

This is a nullary proposition: it is used only as the explicit hypothesis of the conditional helper
`exists_driver_of_drivingCriteria_of_yuanDriverInput`, never as a proved fact. -/
def YuanDriverInput : Prop :=
  ∀ (η : ℝ → ℂ) (S : ℝ), 0 < S → ContinuousOn η (Icc 0 S) → η 0 = 0 →
    StrictMonoOn (fun t => fillH (η '' Icc 0 t)) (Icc 0 S) → HasSimpleApproxOn η S →
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∃ σ : ℝ → ℝ, σ 0 = 0 ∧ StrictMonoOn σ (Icc 0 S) ∧
      ContinuousOn σ (Icc 0 S) ∧
      ∀ t ∈ Icc 0 S, QuantumZipper.fwdHull W (σ t) = fillH (η '' Icc 0 t)

/-- **Proposition 6.12 on `[0, S]`, conditional on `YuanDriverInput`** (distinct name: the source
proposition is not claimed until the input is proved). Let `η` be continuous on `[0, S]`,
`η 0 = 0`, non-crossing in the specification's sense, and satisfy criteria (a) and (b). Then the
filled hulls strictly increase (`fillH_ssubset_of_drivingCriteria`, proved), and after the
half-plane-capacity time change `σ` (continuous, strictly increasing, `σ 0 = 0`,
`hcap(K_t) = 2σ(t)`) the mapping-out functions `g_t` of `K_t = fillH (η([0, t]))` are
`f_{σ(t)} + W_{σ(t)}` for the chordal Loewner flow of a continuous driver `W`, i.e. they solve the
Loewner equation `∂_s g_s(z) = 2/(g_s(z) − W_s)`, `g_0(z) = z`. -/
theorem exists_driver_of_drivingCriteria_of_yuanDriverInput (hY : YuanDriverInput) (hS : 0 < S)
    (hc : ContinuousOn η (Icc 0 S)) (h0 : η 0 = 0) (hnc : HasSimpleApproxOn η S)
    (ha : DrivingCriterionA η S) (hb : DrivingCriterionB η S) :
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∃ σ : ℝ → ℝ, σ 0 = 0 ∧ StrictMonoOn σ (Icc 0 S) ∧
      ContinuousOn σ (Icc 0 S) ∧ ∀ t ∈ Icc 0 S, 0 ≤ σ t ∧
        QuantumZipper.fwdHull W (σ t) = fillH (η '' Icc 0 t) ∧
        IsMapOut (fillH (η '' Icc 0 t)) (fun z => QuantumZipper.fwdMap W (σ t) z + W (σ t)) := by
  obtain ⟨W, hW, hW0, σ, hσ0, hσm, hσc, hK⟩ :=
    hY η S hS hc h0 (strictMonoOn_fillH_of_drivingCriteria hc ha hb) hnc
  refine ⟨W, hW, hW0, σ, hσ0, hσm, hσc, fun t ht => ?_⟩
  have hσt : 0 ≤ σ t := hσ0 ▸ hσm.monotoneOn ⟨le_rfl, hS.le⟩ ht ht.1
  refine ⟨hσt, hK t ht, ?_⟩
  rw [← hK t ht]
  exact isMapOut_fwdMap hW hW0 hσt

end InteractingSLE.Sec6
