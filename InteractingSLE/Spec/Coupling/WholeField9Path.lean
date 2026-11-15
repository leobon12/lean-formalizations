/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField7Birth
import InteractingSLE.WangWu.CouplingBridge
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# The retained Green form along any continuous driver (the `κ`-free path lemmas)

Packet PROVE-WHOLEFIELD9 (PROVE-WHOLEFIELD8 handoff §5, item 2: the path lemmas of the `κ = 4` proof "use only
`w 0 = 0` and continuity before `ζ`").

Wang–Wu's retained-kernel library states its path lemmas for an integrated `SLE₄(ρ)` path
(`IsIntegratedSLEPath 4 …`). The retained kernel `G_{U_t}`, the retained Green form and the Loewner Green energy only
depend on the driver. A driver that is continuous on `[0, ∞)` with `w 0 = 0` is the driver of the integrated `SLE₄`
path **without force points** (`isIntegratedSLEPath_nil`: the threshold condition of the empty word never holds, and
`w = √4 · (w/2)`). A driver continuous before `ζ` agrees on `[0, T₂]`, `T₂ < ζ`, with the clamped driver
`t ↦ w (min t T₂)`. Through these two remarks the library lemmas hold for every continuous driver:

* `isIntegratedSLEPath_nil`, `clampAt`, `continuous_clampAt`, `retainedGreen_clampAt`, `loewnerGreenEnergy_clampAt`,
  `fwdHull_clampAt`;
* **`retainedGreenEnergy_lin_of_path`**, **`continuous_retainedGreenForm_min_of_path`**,
  **`retainedGreenEnergy_eq_loewnerGreenEnergy_of_path`**, `retainedGreen_le_greenH_of_path`,
  `exists_measurable_retainedGreen_of_path`;
* `retainedGreenEnergy_add_of_active`: the retained Green energy of an active test plus a test inside the hull is the
  sum of the two energies (the cross term vanishes).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open LQGMetric QuantumZipper

/-! ### The driver of an integrated `SLE₄` path without force points -/

section Nil

/-- **A continuous driver is the driver of the force-free integrated `SLE₄` path** (the empty word has no
threshold). -/
theorem isIntegratedSLEPath_nil {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    (xL xR ρL ρR : Fin 0 → ℝ) (vL vR : Fin 0 → ℝ≥0 → ℝ) :
    IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR (fun t => w t / 2) ⊤ := by
  have hthr : ∀ (a : ℝ) (uL uR : Fin 0 → ℝ), ¬ ForceWord.ThresholdCondition ρL ρR a uL uR := by
    intro a uL uR hc
    rcases hc with hc | hc <;> simp at hc <;> linarith
  refine ⟨hw0, fun i => i.elim0, fun i => i.elim0, hw.continuousOn, fun i => i.elim0, fun i => i.elim0,
    fun _ _ i => i.elim0, fun _ _ i => i.elim0, fun _ _ i => i.elim0, fun _ _ i => i.elim0,
    fun _ _ i => i.elim0, fun _ _ i => i.elim0, fun t _ => ?_, fun _ _ i => i.elim0, fun _ _ i => i.elim0,
    fun i => i.elim0, fun i => i.elim0, fun t _ => hthr _ _ _, fun h => absurd h ENNReal.top_ne_zero,
    fun T _ hT => absurd hT.symm ENNReal.top_ne_coe⟩
  rw [show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  ring

/-- The driver clamped at `T`: `t ↦ w (min t T)`. -/
def clampAt (w : ℝ≥0 → ℝ) (T : ℝ≥0) : ℝ≥0 → ℝ := fun t => w (min t T)

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

theorem continuous_clampAt (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) :
    Continuous (clampAt w T) := by
  refine hw.comp_continuous (continuous_id.min continuous_const) fun t => ?_
  exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right t T)) hT

theorem clampAt_zero (hw0 : w 0 = 0) (T : ℝ≥0) : clampAt w T 0 = 0 := by
  simp [clampAt, hw0]

/-- The clamped driver agrees with the driver on `[0, T]` (as functions of a real time). -/
theorem eqOn_rpath_clampAt (T : ℝ≥0) : EqOn (Ito.rpath w) (Ito.rpath (clampAt w T)) (Icc 0 (T : ℝ)) := by
  intro s hs
  simp only [Ito.rpath, clampAt]
  rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hs.2)]

theorem continuousOn_rpath_clampAt (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) < ζ) : ContinuousOn (Ito.rpath (clampAt w T)) (Icc 0 (T : ℝ)) :=
  ((continuous_clampAt hw hT).comp continuous_real_toNNReal).continuousOn

/-- A time `T₂ ∈ (t, ζ)`. -/
theorem exists_btwn_lt {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : ∃ T₂ : ℝ≥0, t < T₂ ∧ (T₂ : ℝ≥0∞) < ζ := by
  obtain ⟨c, hc1, hc2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  exact ⟨c, by exact_mod_cast hc1, hc2⟩

/-- **The retained kernel before `T₂` is that of the clamped driver.** -/
theorem retainedGreen_clampAt (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) {T₂ : ℝ≥0}
    (hT₂ : (T₂ : ℝ≥0∞) < ζ) {t : ℝ≥0} (ht : t < T₂) {a b : ℂ} (ha : a ∈ H) (hb : b ∈ H) :
    WangWu.retainedGreen w t a b = WangWu.retainedGreen (clampAt w T₂) t a b := by
  unfold WangWu.retainedGreen K3.VT
  rw [WangWu.VTe_eq_of_eqOn (show (t : ℝ) < T₂ by exact_mod_cast ht) (Ito.continuousOn_rpath hw hT₂)
    (continuousOn_rpath_clampAt hw hT₂) (eqOn_rpath_clampAt T₂) ha hb]

theorem retainedGreenForm_clampAt (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) {T₂ : ℝ≥0}
    (hT₂ : (T₂ : ℝ≥0∞) < ζ) {t : ℝ≥0} (ht : t < T₂) {φ ψ : ℂ → ℝ} (hφ : ∀ a, φ a ≠ 0 → a ∈ H)
    (hψ : ∀ a, ψ a ≠ 0 → a ∈ H) :
    WangWu.retainedGreenForm w t φ ψ = WangWu.retainedGreenForm (clampAt w T₂) t φ ψ := by
  unfold WangWu.retainedGreenForm
  refine integral_congr_ae (Eventually.of_forall fun a => integral_congr_ae
    (Eventually.of_forall fun b => ?_))
  show φ a * WangWu.retainedGreen w t a b * ψ b = φ a * WangWu.retainedGreen (clampAt w T₂) t a b * ψ b
  by_cases ha : φ a = 0
  · simp [ha]
  by_cases hb : ψ b = 0
  · simp [hb]
  rw [retainedGreen_clampAt hw hT₂ ht (hφ a ha) (hψ b hb)]

theorem retainedGreenEnergy_clampAt (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) {T₂ : ℝ≥0}
    (hT₂ : (T₂ : ℝ≥0∞) < ζ) {t : ℝ≥0} (ht : t < T₂) {φ : ℂ → ℝ} (hφ : ∀ a, φ a ≠ 0 → a ∈ H) :
    WangWu.retainedGreenEnergy w t φ = WangWu.retainedGreenEnergy (clampAt w T₂) t φ := by
  rw [WangWu.retainedGreenEnergy_eq_form, WangWu.retainedGreenEnergy_eq_form,
    retainedGreenForm_clampAt hw hT₂ ht hφ hφ]

theorem fwdHull_clampAt {T₂ : ℝ≥0} {t : ℝ≥0} (ht : t < T₂) :
    fwdHull (Ito.rpath w) (t : ℝ) = fwdHull (Ito.rpath (clampAt w T₂)) (t : ℝ) :=
  fwdHull_eq_of_eqOn t.coe_nonneg (show (t : ℝ) < T₂ by exact_mod_cast ht)
    fun r hr => eqOn_rpath_clampAt T₂ hr

theorem loewnerGreenEnergy_clampAt {T₂ : ℝ≥0} {t : ℝ≥0} (ht : t ≤ T₂) (φ : ℂ → ℝ) :
    loewnerGreenEnergy (Ito.rpath w) t φ = loewnerGreenEnergy (Ito.rpath (clampAt w T₂)) t φ := by
  unfold loewnerGreenEnergy
  have e : ∀ y : ℂ, fwdMap (Ito.rpath w) (t : ℝ) y = fwdMap (Ito.rpath (clampAt w T₂)) (t : ℝ) y :=
    fun y => Ito.fwdMap_congr_of_eqOn_of_le (eqOn_rpath_clampAt T₂) (by exact_mod_cast ht)
  simp only [e]

end Nil

/-! ### The library lemmas along any continuous driver -/

section Path

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **Polarization of the retained Green energy** along a driver continuous before `ζ` with `w 0 = 0`. -/
theorem retainedGreenEnergy_lin_of_path (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    {φ ψ : ℂ → ℝ} (hφ : WangWu.IsTestFn φ) (hψ : WangWu.IsTestFn ψ) {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ)
    (c d : ℝ) :
    WangWu.retainedGreenEnergy w T (fun a => c * φ a + d * ψ a) =
      c ^ 2 * WangWu.retainedGreenEnergy w T φ + 2 * c * d * WangWu.retainedGreenForm w T φ ψ +
        d ^ 2 * WangWu.retainedGreenEnergy w T ψ := by
  obtain ⟨T₂, hTT₂, hT₂ζ⟩ := exists_btwn_lt hT
  have hP := isIntegratedSLEPath_nil (continuous_clampAt hw hT₂ζ) (clampAt_zero hw0 T₂)
    Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 (fun i => i.elim0) (fun i => i.elim0)
  have hl := WangWu.retainedGreenEnergy_lin hP hφ hψ (T := T) ENNReal.coe_lt_top c d
  have hφH : ∀ a, φ a ≠ 0 → a ∈ H := fun a ha => hφ.mem_H ha
  have hψH : ∀ a, ψ a ≠ 0 → a ∈ H := fun a ha => hψ.mem_H ha
  have hlinH : ∀ a, c * φ a + d * ψ a ≠ 0 → a ∈ H := fun a ha => (hφ.lin hψ c d).mem_H ha
  rw [retainedGreenEnergy_clampAt hw hT₂ζ hTT₂ hlinH, retainedGreenEnergy_clampAt hw hT₂ζ hTT₂ hφH,
    retainedGreenEnergy_clampAt hw hT₂ζ hTT₂ hψH, retainedGreenForm_clampAt hw hT₂ζ hTT₂ hφH hψH]
  exact hl

/-- **Continuity in time of the retained Green form** along `t ↦ t ∧ σ`, `σ < ζ`, for any continuous driver. -/
theorem continuous_retainedGreenForm_min_of_path (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ) {φ ψ : ℂ → ℝ} (hφ : WangWu.IsTestFn φ) (hψ : WangWu.IsTestFn ψ) :
    Continuous fun t : ℝ≥0 => WangWu.retainedGreenForm w (min t σ) φ ψ := by
  obtain ⟨T₂, hσT₂, hT₂ζ⟩ := exists_btwn_lt hσ
  have hP := isIntegratedSLEPath_nil (continuous_clampAt hw hT₂ζ) (clampAt_zero hw0 T₂)
    Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 (fun i => i.elim0) (fun i => i.elim0)
  have hc := WangWu.continuous_retainedGreenForm_min hP (σ := σ) ENNReal.coe_lt_top hφ hψ
  refine hc.congr fun t => ?_
  exact (retainedGreenForm_clampAt hw hT₂ζ ((min_le_right t σ).trans_lt hσT₂)
    (fun a ha => hφ.mem_H ha) fun a ha => hψ.mem_H ha).symm

/-- **The retained Green energy of a test off the hull is the Loewner Green energy**, for any continuous driver. -/
theorem retainedGreenEnergy_eq_loewnerGreenEnergy_of_path (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hw0 : w 0 = 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {φ : ℂ → ℝ} (hφH : tsupport φ ⊆ H)
    (hdisj : Disjoint (tsupport φ) (fwdHull (Ito.rpath w) t)) :
    WangWu.retainedGreenEnergy w t φ = loewnerGreenEnergy (Ito.rpath w) t φ := by
  obtain ⟨T₂, htT₂, hT₂ζ⟩ := exists_btwn_lt ht
  have hP := isIntegratedSLEPath_nil (continuous_clampAt hw hT₂ζ) (clampAt_zero hw0 T₂)
    Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 (fun i => i.elim0) (fun i => i.elim0)
  have hφ' : ∀ a, φ a ≠ 0 → a ∈ H := fun a ha => hφH (subset_tsupport _ ha)
  rw [retainedGreenEnergy_clampAt hw hT₂ζ htT₂ hφ', loewnerGreenEnergy_clampAt htT₂.le]
  refine WangWu.retainedGreenEnergy_eq_loewnerGreenEnergy hP ENNReal.coe_lt_top hφH ?_
  rwa [← fwdHull_clampAt htT₂]

/-- The retained kernel is at most `G_ℍ` off the diagonal, for any continuous driver. -/
theorem retainedGreen_le_greenH_of_path (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {a b : ℂ} (ha : a ∈ H) (hb : b ∈ H) (hab : a ≠ b) :
    WangWu.retainedGreen w t a b ≤ greenH a b := by
  obtain ⟨T₂, htT₂, hT₂ζ⟩ := exists_btwn_lt ht
  have hP := isIntegratedSLEPath_nil (continuous_clampAt hw hT₂ζ) (clampAt_zero hw0 T₂)
    Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 (fun i => i.elim0) (fun i => i.elim0)
  rw [retainedGreen_clampAt hw hT₂ζ htT₂ ha hb]
  exact WangWu.retainedGreen_le_greenH hP (by simp) ha hb hab t

/-- A Borel version of the retained kernel at a time `t < ζ`, for any continuous driver. -/
theorem exists_measurable_retainedGreen_of_path (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    ∃ g : ℂ × ℂ → ℝ, Measurable g ∧ ∀ p : ℂ × ℂ, p.1 ∈ H → p.2 ∈ H →
      g p = WangWu.retainedGreen w t p.1 p.2 := by
  obtain ⟨T₂, htT₂, hT₂ζ⟩ := exists_btwn_lt ht
  have hP := isIntegratedSLEPath_nil (continuous_clampAt hw hT₂ζ) (clampAt_zero hw0 T₂)
    Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 (fun i => i.elim0) (fun i => i.elim0)
  obtain ⟨g, hg, hge⟩ := WangWu.exists_measurable_retainedGreen hP (T := t) ENNReal.coe_lt_top
  exact ⟨g, hg, fun p h1 h2 => by rw [hge p h1 h2, retainedGreen_clampAt hw hT₂ζ htT₂ h1 h2]⟩

/-- **The retained Green energy of an active test plus a test inside the hull is additive** (the cross term of the
retained kernel vanishes: `G_{U_t}(a, b) = 0` for `a` active, `b` in the hull). -/
theorem retainedGreenEnergy_add_of_active (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {ψA ψP : TestOn upperHalfPlaneOpens}
    (hA : IsActiveLabel w (tsupport ψA) t) (hPK : tsupport ψP ⊆ fwdHull (Ito.rpath w) (t : ℝ)) :
    WangWu.retainedGreenEnergy w t (⇑ψA + ⇑ψP) =
      WangWu.retainedGreenEnergy w t ψA + WangWu.retainedGreenEnergy w t ψP := by
  have hcross : WangWu.retainedGreenForm w t ψA ψP = 0 := by
    unfold WangWu.retainedGreenForm
    refine (integral_congr_ae (Eventually.of_forall fun a => ?_)).trans (integral_zero _ _)
    show (∫ b, ψA a * WangWu.retainedGreen w t a b * ψP b) = 0
    by_cases ha : ψA a = 0
    · simp [ha]
    refine (integral_congr_ae (Eventually.of_forall fun b => ?_)).trans (integral_zero _ _)
    show ψA a * WangWu.retainedGreen w t a b * ψP b = 0
    by_cases hb : ψP b = 0
    · simp [hb]
    have haS : a ∈ tsupport ψA := subset_tsupport _ ha
    have hbS : b ∈ tsupport ψP := subset_tsupport _ hb
    rw [retainedGreen_eq_zero_of_active hw ht
      ⟨ψA.tsupport_subset haS, fun hK => Set.disjoint_left.1 hA haS hK⟩ (hPK hbS)]
    ring
  have hl := retainedGreenEnergy_lin_of_path hw hw0 (isTestFn_of_testOn ψA) (isTestFn_of_testOn ψP) ht 1 1
  rw [hcross] at hl
  have e : (⇑ψA + ⇑ψP : ℂ → ℝ) = fun a => 1 * ψA a + 1 * ψP a := by
    funext a; simp only [Pi.add_apply]; ring
  rw [e, hl]; ring

/-- **A compact set of `ℍ` avoids the hull at some positive time**, for any driver continuous before `ζ > 0` with
`w 0 = 0`. -/
theorem exists_pos_disjoint_fwdHull_of_path (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    (hζ : 0 < ζ) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) :
    ∃ t : ℝ≥0, 0 < t ∧ (t : ℝ≥0∞) < ζ ∧ Disjoint K (fwdHull (Ito.rpath w) (t : ℝ)) := by
  obtain ⟨T₂, hT₂, hT₂ζ⟩ := exists_btwn_lt (t := 0) (by simpa using hζ)
  have hP := isIntegratedSLEPath_nil (continuous_clampAt hw hT₂ζ) (clampAt_zero hw0 T₂)
    Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0 (fun i => i.elim0) (fun i => i.elim0)
  obtain ⟨t, ht0, -, hd⟩ := exists_pos_disjoint_fwdHull hP (by simp) hK hKH
  refine ⟨min t (T₂ / 2), lt_min ht0 (by positivity), lt_of_le_of_lt ?_ hT₂ζ, ?_⟩
  · exact ENNReal.coe_le_coe.2 ((min_le_right _ _).trans (NNReal.half_le_self T₂))
  · have hlt : min t (T₂ / 2) < T₂ := (min_le_right _ _).trans_lt (NNReal.half_lt_self hT₂.ne')
    rw [fwdHull_clampAt hlt]
    exact hd.mono_right (WangWu.fwdHull_mono (by exact_mod_cast min_le_left t (T₂ / 2)))

end Path

end WholeField

end InteractingSLE
