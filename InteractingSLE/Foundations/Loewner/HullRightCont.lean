/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtGChart
import QuantumZipper.Proofs.Loewner.CoreArc2

/-!
# Right-continuity of Loewner hulls on compact sets

Packet PROVE-LOCEXT-L. For a continuous driving function `W`, the hulls `K_t` are right-continuous in the following
sense: **a compact set `C ⊆ ℍ` that avoids `K_s` also avoids `K_{s+δ}` for some `δ > 0`**. The swallowing time is
lower semicontinuous on `ℍ` (QuantumZipper, `CoreArc.lowerSemicontinuousOn_swallowTime`), so it attains its minimum on
`C`; that minimum is `> s`, and every `t` below it has `C ∩ K_t = ∅`.

For a driving path `w : ℝ≥0 → ℝ` continuous before a lifetime `ζ > s` the same holds (the driver is clamped beyond a
time strictly between `s` and `ζ`, which changes no hull before that time).

## Main results

* `exists_pos_disjoint_fwdHull`: continuous drivers;
* **`exists_pos_disjoint_fwdHull_rpath`**: driving paths continuous before the lifetime, with `s + δ < ζ`;
* `eventually_disjoint_fwdHull_rpath`: the same as an eventual statement along `𝓝[≥] s`;
* `tendsto_indicator_disjoint_fwdHull_rpath`: for times `t_n ↓ s` (`t_n ≥ s`), the avoidance indicator converges.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

namespace HullRightCont

/-- **Right-continuity of the hulls of a continuous driver on compact sets.** -/
theorem exists_pos_disjoint_fwdHull {A : ℝ → ℝ} (hA : Continuous A) {C : Set ℂ} (hC : IsCompact C)
    (hCH : C ⊆ H) {s : ℝ} (hs : Disjoint C (fwdHull A s)) :
    ∃ δ > 0, Disjoint C (fwdHull A (s + δ)) := by
  rcases C.eq_empty_or_nonempty with hC0 | hCne
  · exact ⟨1, one_pos, by rw [hC0]; exact empty_disjoint _⟩
  obtain ⟨z₀, hz₀C, hmin⟩ :=
    (CoreArc.lowerSemicontinuousOn_swallowTime hA hCH).exists_isMinOn hCne hC
  have hz₀ : ENNReal.ofReal s < swallowTime A z₀ := by
    by_contra hle
    exact Set.disjoint_left.1 hs hz₀C ⟨hCH hz₀C, not_lt.1 hle⟩
  obtain ⟨r, -, hsr, hrσ⟩ := ENNReal.lt_iff_exists_real_btwn.1 hz₀
  have hs' : s < r := (ENNReal.ofReal_lt_ofReal_iff'.1 hsr).1
  refine ⟨r - s, sub_pos.2 hs', Set.disjoint_left.2 fun z hzC hzK => ?_⟩
  have h1 : swallowTime A z₀ ≤ swallowTime A z := hmin hzC
  have h2 : swallowTime A z ≤ ENNReal.ofReal (s + (r - s)) := hzK.2
  rw [add_sub_cancel] at h2
  exact absurd (hrσ.trans_le (h1.trans h2)) (lt_irrefl _)

/-- **Right-continuity of the hulls of a driving path continuous before its lifetime.** For `w` continuous on
`{t < ζ}`, `s < ζ` and a compact `C ⊆ ℍ` avoiding `K_s`, some `δ > 0` has `s + δ < ζ` and `C` avoids `K_t` for every
`t ≤ s + δ`. -/
theorem exists_pos_disjoint_fwdHull_rpath {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) {s : ℝ≥0} (hsζ : (s : ℝ≥0∞) < ζ) {C : Set ℂ} (hC : IsCompact C)
    (hCH : C ⊆ H) (hs : Disjoint C (fwdHull (Ito.rpath w) s)) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ((s + δ : ℝ≥0) : ℝ≥0∞) < ζ ∧
      ∀ t : ℝ≥0, t ≤ s + δ → Disjoint C (fwdHull (Ito.rpath w) t) := by
  obtain ⟨T, hsT, hTζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hsζ
  have hsT' : s < T := by exact_mod_cast hsT
  have hT0 : (0 : ℝ) ≤ T := T.coe_nonneg
  have hwT : ContinuousOn (Ito.rpath w) (Icc 0 (T : ℝ)) := Ito.continuousOn_rpath hw hTζ
  set A : ℝ → ℝ := Ito.clampDrv (Ito.rpath w) T with hAdef
  have hA : Continuous A := Ito.continuous_clampDrv hT0 hwT
  have hcongr : ∀ t : ℝ, 0 ≤ t → t < T → fwdHull (Ito.rpath w) t = fwdHull A t := fun t ht htT =>
    LocalExt.fwdHull_congr_of_eqOn_of_lt ht htT Ito.clampDrv_eqOn.symm
  have hsA : Disjoint C (fwdHull A s) := by
    rw [← hcongr s s.coe_nonneg (by exact_mod_cast hsT')]
    exact hs
  obtain ⟨δ, hδ, hδC⟩ := exists_pos_disjoint_fwdHull hA hC hCH hsA
  set δ' : ℝ≥0 := min (Real.toNNReal δ) ((T - s) / 2) with hδ'def
  have hTs : 0 < T - s := tsub_pos_of_lt hsT'
  have hδ'pos : 0 < δ' := lt_min (Real.toNNReal_pos.2 hδ) (half_pos hTs)
  have hδ'T : s + δ' < T := by
    have h1 : δ' ≤ (T - s) / 2 := min_le_right _ _
    have h2 : (T - s) / 2 < T - s := half_lt_self hTs
    calc s + δ' < s + (T - s) := by gcongr; exact h1.trans_lt h2
      _ = T := add_tsub_cancel_of_le hsT'.le
  have hδ'δ : ((s + δ' : ℝ≥0) : ℝ) ≤ (s : ℝ) + δ := by
    have : (δ' : ℝ) ≤ δ := by
      have := min_le_left (Real.toNNReal δ) ((T - s) / 2)
      calc (δ' : ℝ) ≤ (Real.toNNReal δ : ℝ) := by exact_mod_cast this
        _ = δ := Real.coe_toNNReal δ hδ.le
    push_cast
    linarith
  refine ⟨δ', hδ'pos, lt_of_lt_of_le (by exact_mod_cast hδ'T) hTζ.le, fun t ht => ?_⟩
  have htT : (t : ℝ) < T := by exact_mod_cast ht.trans_lt hδ'T
  rw [hcongr t t.coe_nonneg htT]
  refine hδC.mono_right ((fwdHull_mono (W := A)).1 ?_)
  exact (show (t : ℝ) ≤ ((s + δ' : ℝ≥0) : ℝ) by exact_mod_cast ht).trans hδ'δ

/-- **Right-continuity, eventual form**: under the hypotheses of `exists_pos_disjoint_fwdHull_rpath`, `C` avoids
`K_t` for all `t` close to `s` from the right. -/
theorem eventually_disjoint_fwdHull_rpath {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) {s : ℝ≥0} (hsζ : (s : ℝ≥0∞) < ζ) {C : Set ℂ} (hC : IsCompact C)
    (hCH : C ⊆ H) (hs : Disjoint C (fwdHull (Ito.rpath w) s)) :
    ∀ᶠ t : ℝ≥0 in 𝓝[≥] s, Disjoint C (fwdHull (Ito.rpath w) (t : ℝ)) := by
  obtain ⟨δ, hδ, -, hδC⟩ := exists_pos_disjoint_fwdHull_rpath hw hsζ hC hCH hs
  have hmem : Iio (s + δ) ∈ 𝓝[≥] s :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_add_of_pos_right s hδ))
  filter_upwards [hmem] with t ht
  exact hδC t ht.le

/-- **Right-continuity along a sequence**: for times `t n ≥ s` with `t n → s`, eventually `C` avoids `K_{t n}`. -/
theorem eventually_disjoint_fwdHull_rpath_of_tendsto {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) {s : ℝ≥0} (hsζ : (s : ℝ≥0∞) < ζ) {C : Set ℂ} (hC : IsCompact C)
    (hCH : C ⊆ H) (hs : Disjoint C (fwdHull (Ito.rpath w) s)) {t : ℕ → ℝ≥0} (hts : ∀ n, s ≤ t n)
    (ht : Tendsto t atTop (𝓝 s)) : ∀ᶠ n in atTop, Disjoint C (fwdHull (Ito.rpath w) (t n : ℝ)) := by
  have ht' : Tendsto t atTop (𝓝[≥] s) :=
    tendsto_nhdsWithin_iff.2 ⟨ht, Eventually.of_forall hts⟩
  exact ht'.eventually (eventually_disjoint_fwdHull_rpath hw hsζ hC hCH hs)

end HullRightCont

end InteractingSLE
