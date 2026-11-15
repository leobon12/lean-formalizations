/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.CounterflowProb2Coding
import InteractingSLE.Spec.Coupling.SafeFamily
import InteractingSLE.Foundations.Loewner.YuanCorollary13Slit
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# Hull avoidance at a fixed time is an event of the raw filtration

Packet PROVE-LEMMA72D. The unit-modulus identification of the conditional clause (`Lemma72DUnit`) needs the event
`{t < ζ, φ supported off K_t}` in the **raw** σ-algebra `𝓐_t` (not only in its right-continuous augmentation). For a
driver `W` adapted before `ζ` to `𝓐` and continuous before `ζ`:

* `disjoint_closedBall_fwdHull_iff_real`: a closed disc `B̄(c, ε) ⊂ ℍ` misses `K_q` (`q ≥ 0` real) iff the tamed
  forward flows of its rational points stay high at the rational times of `[0, q]`
  (`Coding.disjoint_closedBall_fwdHull_iff`, for real times);
* `measurableSet_disjoint_closedBall_fwdHull_real`: hence the avoidance event is measurable for every σ-algebra for
  which the driver coordinates up to `q` are measurable;
* **`measurableSet_lt_disjoint_ballsK`**: `{t < ζ, F ∩ K_t = ∅}` is an event of `𝓐_t` for every finite union `F` of
  rational closed discs in `ℍ` (the driver frozen at `t`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

open QuantumZipper (H fwdHull fwdMap tamedZ drive)

namespace InteractingSLE.Sec7.Lemma72D

open Coding Ito Coupling

/-- Rational times are dense in `[0, q]` for a real `q ≥ 0`. -/
theorem Icc_subset_closure_rat {q : ℝ} (hq : 0 ≤ q) :
    Icc (0 : ℝ) q ⊆ closure {s : ℝ | ∃ r : ℚ, (r : ℝ) = s ∧ 0 ≤ s ∧ s ≤ q} := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  rcases eq_or_lt_of_le hx.2 with hxq | hxq
  · rcases eq_or_lt_of_le hq with hq0 | hq0
    · refine ⟨0, ⟨0, by simp, le_rfl, hq⟩, ?_⟩
      rw [hxq, ← hq0, dist_self]; exact hε
    · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (max_lt (sub_lt_self q hε) hq0)
      refine ⟨r, ⟨r, rfl, (le_max_right _ _).trans hr1.le, hr2.le⟩, ?_⟩
      rw [hxq, Real.dist_eq, abs_of_pos (by linarith)]
      linarith [le_max_left (q - ε) 0]
  · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (lt_min (lt_add_of_pos_right x hε) hxq)
    refine ⟨r, ⟨r, rfl, by linarith [hx.1], (hr2.trans_le (min_le_right _ _)).le⟩, ?_⟩
    rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith)]
    linarith [min_le_left (x + ε) q]

/-- **A closed disc misses `K_q` iff its rational points stay tamed-high up to `q`** (real `q ≥ 0`;
`Coding.disjoint_closedBall_fwdHull_iff` at real times). -/
theorem disjoint_closedBall_fwdHull_iff_real {W : ℝ → ℝ} (hW : Continuous W) {q : ℝ} (hq0 : 0 ≤ q) {c : ℂ}
    {ε : ℝ} (hε : 0 < ε) (hcε : ε < c.im) :
    Disjoint (closedBall c ε) (fwdHull W q) ↔
      ∃ k : ℕ, ∀ y : ℚ × ℚ, ratPt y ∈ closedBall c ε → ∀ s : ℚ, 0 ≤ (s : ℝ) → (s : ℝ) ≤ q →
        2 * (1 / ((k : ℝ) + 1)) ≤ (tamedZ W (1 / ((k : ℝ) + 1)) (ratPt y) s).im := by
  constructor
  · intro hdisj
    have hsub : closedBall c ε ⊆ H \ fwdHull W q := fun z hz =>
      ⟨closedBall_subset_H hcε hz, fun hzK => Set.disjoint_left.1 hdisj hz hzK⟩
    have hφ : ContinuousOn (fun z => (fwdMap W q z).im) (closedBall c ε) :=
      (Complex.continuous_im.comp_continuousOn
        (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hq0).continuousOn).mono hsub
    obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_closedBall c ε).exists_isMinOn
      ⟨c, mem_closedBall_self hε.le⟩ hφ
    obtain ⟨u₀, hu₀⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hq0 (hsub hx₀).1 (hsub hx₀).2
    have hm : 0 < (fwdMap W q x₀).im := by
      rw [QuantumZipper.F1.fwdMap_eq_of_isForwardSol hu₀ ⟨hq0, le_rfl⟩]
      exact QuantumZipper.FwdClock.sol_im_pos hW (hsub hx₀).1 hu₀ ⟨hq0, le_rfl⟩
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hm)
    have hk0 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    refine ⟨k, fun y hy s hs0 hsq => ?_⟩
    obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hq0 (hsub hy).1 (hsub hy).2
    have hanti := (QuantumZipper.K3.im_fwdMap_antitoneOn hW (hsub hy).1 ⟨u, hu⟩).1
    have hbound : ∀ s' ∈ Icc (0 : ℝ) q, 2 * (1 / ((k : ℝ) + 1)) ≤ (u s').im := by
      intro s' hs'
      have e1 : u s' = fwdMap W s' (ratPt y) := (QuantumZipper.F1.fwdMap_eq_of_isForwardSol hu hs').symm
      have h1 : (fwdMap W q (ratPt y)).im ≤ (fwdMap W s' (ratPt y)).im :=
        hanti hs' ⟨hq0, le_rfl⟩ hs'.2
      have h2 : (fwdMap W q x₀).im ≤ (fwdMap W q (ratPt y)).im := isMinOn_iff.1 hmin _ hy
      rw [e1]
      linarith
    have heq := QuantumZipper.tamedZ_eq_of_isForwardSol hW hk0 hq0 hu
      (fun s' hs' => by linarith [hbound s' hs']) s ⟨hs0, hsq⟩
    rw [heq]
    exact hbound s ⟨hs0, hsq⟩
  · rintro ⟨k, hk⟩
    set c' : ℝ := 1 / ((k : ℝ) + 1) with hc'
    have hc'0 : 0 < c' := by positivity
    have hIm : ∀ a b : ℂ, |a.im - b.im| ≤ dist a b := fun a b => by
      rw [Complex.dist_eq, ← Complex.sub_im]; exact Complex.abs_im_le_norm _
    have h1a : ∀ y : ℚ × ℚ, ratPt y ∈ closedBall c ε → ∀ s ∈ Icc (0 : ℝ) q,
        2 * c' ≤ (tamedZ W c' (ratPt y) s).im := by
      intro y hy s hs
      have hcont := QuantumZipper.continuousOn_tamedZ hW hc'0 hq0 (ratPt y)
      have hcl : IsClosed {z : ℂ | 2 * c' ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
      have hsubI : {s : ℝ | ∃ r : ℚ, (r : ℝ) = s ∧ 0 ≤ s ∧ s ≤ q} ⊆ Icc 0 q := fun s ⟨_, _, h0, h1⟩ => ⟨h0, h1⟩
      have hmem := ((hcont s hs).mono hsubI).mem_closure_image (Icc_subset_closure_rat hq0 hs)
      refine hcl.closure_subset_iff.2 ?_ hmem
      rintro _ ⟨s', ⟨r, rfl, h0, hq'⟩, rfl⟩
      exact hk y hy r h0 hq'
    have h1b : ∀ z ∈ closedBall c ε, ∀ s ∈ Icc (0 : ℝ) q, 2 * c' ≤ (tamedZ W c' z s).im := by
      intro z hz s hs
      by_contra hlt
      push Not at hlt
      have hgap : 0 < 2 * c' - (tamedZ W c' z s).im := by linarith
      have hL : 0 < Real.exp (4 * q / c' ^ 2) := Real.exp_pos _
      obtain ⟨y, hy, hzy⟩ := exists_ratPt_mem_closedBall hε hz (div_pos hgap hL)
      have h1 := h1a y hy s hs
      have h2 := dist_tamedZ_le hW hc'0 hq0 z (ratPt y) hs
      have h4 : dist z (ratPt y) * Real.exp (4 * q / c' ^ 2) < 2 * c' - (tamedZ W c' z s).im := by
        rwa [lt_div_iff₀ hL] at hzy
      linarith [(abs_le.1 (hIm (tamedZ W c' z s) (tamedZ W c' (ratPt y) s))).1]
    refine Set.disjoint_left.2 fun z hz hzK => ?_
    have hcontq := QuantumZipper.continuousOn_tamedZ hW hc'0 (show (0 : ℝ) ≤ q + 1 by linarith) z
    obtain ⟨δ, hδ, hδb⟩ := Metric.continuousOn_iff.1 hcontq q ⟨hq0, by linarith⟩ c' hc'0
    have hmin0 : 0 < min (δ / 2) 1 := lt_min (half_pos hδ) one_pos
    set q' : ℝ := q + min (δ / 2) 1 with hq'
    have hqq' : q < q' := by linarith
    have him : ∀ s ∈ Icc (0 : ℝ) q', c' ≤ (tamedZ W c' z s).im := by
      intro s hs
      by_cases hsq : s ≤ q
      · have := h1b z hz s ⟨hs.1, hsq⟩
        linarith
      · push Not at hsq
        have hs1 : s ∈ Icc (0 : ℝ) (q + 1) := ⟨hs.1, by linarith [hs.2, min_le_right (δ / 2) 1]⟩
        have hd : dist s q < δ := by
          rw [Real.dist_eq, abs_of_pos (by linarith)]
          linarith [hs.2, min_le_left (δ / 2) 1]
        have h1 := hδb s hs1 hd
        have h2 := h1b z hz q ⟨hq0, le_rfl⟩
        linarith [(abs_le.1 (hIm (tamedZ W c' z s) (tamedZ W c' z q))).1]
    have hsol := QuantumZipper.isForwardSol_tamedZ hW hc'0 (by linarith : (0 : ℝ) ≤ q') him
    have hsw : ENNReal.ofReal q' ≤ QuantumZipper.swallowTime W z :=
      le_sSup ⟨q', ⟨by linarith, _, hsol⟩, rfl⟩
    have hlt : ENNReal.ofReal q < ENNReal.ofReal q' :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hqq'
    exact absurd (lt_of_lt_of_le hlt hsw) (not_lt.2 hzK.2)

/-- **Avoidance of a closed disc by `K_q` is measurable** for every σ-algebra for which the driver coordinates up to
time `q` are measurable (continuous paths). -/
theorem measurableSet_disjoint_closedBall_fwdHull_real {Ω : Type*} {m : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}
    (hBc : ∀ ω, Continuous fun t => B t ω) {q : ℝ} (hq : 0 ≤ q)
    (hBm : ∀ r : ℝ≥0, (r : ℝ) ≤ q → Measurable[m] (B r)) {c : ℂ} {ε : ℝ} (hε : 0 < ε) (hcε : ε < c.im) :
    MeasurableSet[m] {ω | Disjoint (closedBall c ε) (fwdHull (drive 1 B ω) q)} := by
  let _ : MeasurableSpace Ω := m
  have e : {ω | Disjoint (closedBall c ε) (fwdHull (drive 1 B ω) q)} =
      ⋃ k : ℕ, ⋂ y : ℚ × ℚ, ⋂ (_ : ratPt y ∈ closedBall c ε), ⋂ s : ℚ, ⋂ (_ : 0 ≤ (s : ℝ) ∧ (s : ℝ) ≤ q),
        {ω | 2 * (1 / ((k : ℝ) + 1)) ≤ (tamedZ (drive 1 B ω) (1 / ((k : ℝ) + 1)) (ratPt y) s).im} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
    rw [disjoint_closedBall_fwdHull_iff_real (QuantumZipper.NonSwallow.continuous_drive_ns hBc 1 ω) hq hε hcε]
    exact exists_congr fun k => forall_congr' fun y => forall_congr' fun hy => forall_congr' fun s =>
      ⟨fun h hs => h hs.1 hs.2, fun h h0 h1 => h ⟨h0, h1⟩⟩
  rw [e]
  refine MeasurableSet.iUnion fun k => MeasurableSet.iInter fun y => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun s => MeasurableSet.iInter fun hs => ?_
  have hmeas := (QuantumZipper.measurable_tamed_drive 1 (c := 1 / ((k : ℝ) + 1)) (by positivity) B hBc hs.1
    (fun r hr => hBm r (hr.trans hs.2))).1
  exact measurableSet_le measurable_const
    (Complex.measurable_im.comp (hmeas.comp (measurable_const.prodMk measurable_id)))

/-- **Hull avoidance at a fixed time is an event of the raw filtration.** For a driver adapted before `ζ` to `𝓐`
and continuous before `ζ`, with `{t < ζ} ∈ 𝓐_t`, the event `{t < ζ, F ∩ K_t = ∅}` is in `𝓐_t` for every finite union
`F` of rational closed discs in `ℍ`. -/
theorem measurableSet_lt_disjoint_ballsK {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓐 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hWa : AdaptedBefore 𝓐 ζ W)
    (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω}) (t : ℝ≥0)
    (hζ : MeasurableSet[𝓐 t] {ω | (t : ℝ≥0∞) < ζ ω}) {F : Finset (ℚ × ℚ × ℚ)} (hFH : ballsK F ⊆ H) :
    MeasurableSet[𝓐 t] {ω | (t : ℝ≥0∞) < ζ ω ∧
      Disjoint (ballsK F) (fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ))} := by
  classical
  -- the driver frozen at `t`
  set Bc : ℝ≥0 → Ω → ℝ := fun s ω => if (t : ℝ≥0∞) < ζ ω then W (min s t) ω else 0 with hBc
  have hBcc : ∀ ω, Continuous fun s => Bc s ω := fun ω => by
    by_cases hω : (t : ℝ≥0∞) < ζ ω
    · simp only [hBc, hω, ↓reduceIte]
      refine (hc ω).comp_continuous (continuous_id.min continuous_const) fun s => ?_
      exact lt_of_le_of_lt (by exact_mod_cast min_le_right s t) hω
    · simp only [hBc, hω, ↓reduceIte]; exact continuous_const
  have hBcm : ∀ r : ℝ≥0, (r : ℝ) ≤ (t : ℝ) → Measurable[𝓐 t] (Bc r) := fun r hr => by
    have hrt : r ≤ t := by exact_mod_cast hr
    intro A hA
    have e : Bc r ⁻¹' A = ({ω | (t : ℝ≥0∞) < ζ ω} ∩ {ω | (r : ℝ≥0∞) < ζ ω ∧ W r ω ∈ A}) ∪
        ({ω | (t : ℝ≥0∞) < ζ ω}ᶜ ∩ {_ω | (0 : ℝ) ∈ A}) := by
      ext ω
      simp only [hBc, mem_preimage, mem_union, mem_inter_iff, mem_ofPred_eq, mem_compl_iff, min_eq_left hrt]
      by_cases hω : (t : ℝ≥0∞) < ζ ω
      · simp only [hω, ↓reduceIte, true_and, not_true_eq_false, false_and, or_false]
        exact ⟨fun h => ⟨lt_of_le_of_lt (by exact_mod_cast hrt) hω, h⟩, fun h => h.2⟩
      · simp [hω]
    rw [e]
    exact (hζ.inter (𝓐.mono hrt _ (hWa r A hA))).union (hζ.compl.inter (MeasurableSet.const _))
  -- the hull at `t` is that of the frozen driver
  have hhull : ∀ ω, (t : ℝ≥0∞) < ζ ω →
      fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ) = fwdHull (drive 1 Bc ω) (t : ℝ) := by
    intro ω hω
    obtain ⟨t₂, htt₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hω
    have htt₂' : (t : ℝ) < (t₂ : ℝ) := by exact_mod_cast htt₂
    have hcl := continuousOn_rpath (hc ω) ht₂ζ
    have hV := continuous_clampDrv (W := rpath (W · ω)) t₂.coe_nonneg hcl
    have e1 : fwdHull (rpath (W · ω)) (t : ℝ) = fwdHull (clampDrv (rpath (W · ω)) t₂) (t : ℝ) :=
      InteractingSLE.fwdHull_eq_of_eqOn t.coe_nonneg htt₂' fun r hr =>
        (clampDrv_eqOn (W := rpath (W · ω)) hr).symm
    show fwdHull (rpath (W · ω)) (t : ℝ) = _
    rw [e1]
    refine YuanCorollary13.fwdHull_eq_of_eqOn_Icc hV (QuantumZipper.NonSwallow.continuous_drive_ns hBcc 1 ω)
      t.coe_nonneg fun r hr => ?_
    have hr2 : r ∈ Icc (0 : ℝ) (t₂ : ℝ) := ⟨hr.1, hr.2.trans htt₂'.le⟩
    rw [clampDrv_eqOn (W := rpath (W · ω)) hr2]
    have hrt : r.toNNReal ≤ t := by
      rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
    simp only [rpath, QuantumZipper.drive, Real.sqrt_one, one_mul, hBc, hω, ↓reduceIte, min_eq_left hrt]
  -- the frozen hull avoids `F` measurably
  have hdisc : ∀ b ∈ F, closedBall (ratCentre b) (b.2.2 : ℝ) ⊆ H := fun b hb =>
    (subset_biUnion_of_mem (u := fun b => closedBall (ratCentre b) (b.2.2 : ℝ)) hb).trans hFH
  have hball : ∀ b ∈ F, MeasurableSet[𝓐 t]
      {ω | Disjoint (closedBall (ratCentre b) (b.2.2 : ℝ)) (fwdHull (drive 1 Bc ω) (t : ℝ))} := by
    intro b hb
    by_cases hr : (0 : ℝ) < (b.2.2 : ℝ)
    · have hcε : (b.2.2 : ℝ) < (ratCentre b).im := by
        by_contra hle
        push Not at hle
        have hmem : ratCentre b - ((b.2.2 : ℝ) : ℂ) * Complex.I ∈ closedBall (ratCentre b) (b.2.2 : ℝ) := by
          rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
        have := hdisc b hb hmem
        simp only [QuantumZipper.H, mem_ofPred_eq, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, mul_one] at this
        linarith
      exact measurableSet_disjoint_closedBall_fwdHull_real hBcc t.coe_nonneg hBcm hr hcε
    · have hempty : ∀ ω, Disjoint (closedBall (ratCentre b) (b.2.2 : ℝ)) (fwdHull (drive 1 Bc ω) (t : ℝ)) ∨
          closedBall (ratCentre b) (b.2.2 : ℝ) ⊆ {ratCentre b} := fun ω => by
        right
        intro z hz
        rw [mem_closedBall] at hz
        rw [mem_singleton_iff, ← dist_le_zero]
        exact hz.trans (not_lt.1 hr)
      -- a degenerate disc is a point (or empty): use a tiny disc around it
      by_cases hr0 : (b.2.2 : ℝ) < 0
      · have e : {ω | Disjoint (closedBall (ratCentre b) (b.2.2 : ℝ)) (fwdHull (drive 1 Bc ω) (t : ℝ))} = univ := by
          ext ω; simp [closedBall_eq_empty.2 hr0]
        rw [e]; exact MeasurableSet.univ
      · have hr00 : (b.2.2 : ℝ) = 0 := le_antisymm (not_lt.1 hr) (not_lt.1 hr0)
        have hcH0 : ratCentre b ∈ H := hdisc b hb (mem_closedBall_self (by rw [hr00]))
        have hcH : 0 < (ratCentre b).im := hcH0
        have e : {ω | Disjoint (closedBall (ratCentre b) (b.2.2 : ℝ)) (fwdHull (drive 1 Bc ω) (t : ℝ))} =
            ⋃ n : ℕ, {ω | Disjoint (closedBall (ratCentre b) ((ratCentre b).im / ((n : ℝ) + 2)))
              (fwdHull (drive 1 Bc ω) (t : ℝ))} := by
          ext ω
          simp only [mem_ofPred_eq, mem_iUnion, hr00, closedBall_zero, disjoint_singleton_left]
          constructor
          · intro hnot
            have hopen := QuantumZipper.FwdHolo.isOpen_compl_fwdHull
              (QuantumZipper.NonSwallow.continuous_drive_ns hBcc 1 ω)
              t.coe_nonneg
            obtain ⟨δ, hδ, hδs⟩ := Metric.isOpen_iff.1 hopen _ ⟨hcH0, hnot⟩
            obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hδ hcH)
            refine ⟨n, Set.disjoint_left.2 fun z hz hzK => (hδs ?_).2 hzK⟩
            rw [mem_closedBall] at hz
            rw [mem_ball]
            refine lt_of_le_of_lt hz ?_
            have h2 : (ratCentre b).im / ((n : ℝ) + 2) ≤ (ratCentre b).im / ((n : ℝ) + 1) :=
              div_le_div_of_nonneg_left hcH.le (by positivity) (by linarith)
            have h3 : (ratCentre b).im / ((n : ℝ) + 1) < δ := by
              have := mul_lt_mul_of_pos_left hn hcH
              rwa [mul_one_div, mul_div_cancel₀ _ hcH.ne'] at this
            linarith
          · rintro ⟨n, hn⟩ hmem
            exact Set.disjoint_left.1 hn (mem_closedBall_self (div_pos hcH (by positivity)).le) hmem
        rw [e]
        refine MeasurableSet.iUnion fun n => ?_
        have hpos : 0 < (ratCentre b).im / ((n : ℝ) + 2) := div_pos hcH (by positivity)
        have hlt : (ratCentre b).im / ((n : ℝ) + 2) < (ratCentre b).im := by
          exact div_lt_self hcH (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
        exact measurableSet_disjoint_closedBall_fwdHull_real hBcc t.coe_nonneg hBcm hpos hlt
  have e : {ω | (t : ℝ≥0∞) < ζ ω ∧ Disjoint (ballsK F) (fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ))} =
      {ω | (t : ℝ≥0∞) < ζ ω} ∩ ⋂ b ∈ F,
        {ω | Disjoint (closedBall (ratCentre b) (b.2.2 : ℝ)) (fwdHull (drive 1 Bc ω) (t : ℝ))} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
    constructor
    · rintro ⟨hω, hdis⟩
      refine ⟨hω, fun b hb => ?_⟩
      rw [← hhull ω hω]
      exact hdis.mono_left (subset_biUnion_of_mem (u := fun b => closedBall (ratCentre b) (b.2.2 : ℝ)) hb)
    · rintro ⟨hω, hdis⟩
      refine ⟨hω, ?_⟩
      rw [hhull ω hω, ballsK, Set.disjoint_iUnion₂_left]
      exact hdis
  rw [e]
  exact hζ.inter (Finset.measurableSet_biInter F fun b hb => hball b hb)

end InteractingSLE.Sec7.Lemma72D
