/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopWallsLaw
import InteractingSLE.Spec.Sec7.Lemma72DHull
import InteractingSLE.Spec.ZhanGT4.CrosscutA3Measurable
import InteractingSLE.WangWu.Prop420Ext

/-!
# The counterflow hull read through a regularized driver: measurability at random times

Packet PROVE-STRIPSYS41 (PROVE-STRIPSYS37 §5.2, blocker (d)). The coupling's driver `W` is continuous only almost
surely, so the avoidance events of its raw hull `K_t = fwdHull W t` need not be measurable. Here the driver is
replaced by its dyadic regularization (`ZhanGT4.A35.regPath` of the driver killed at `ζ`), which is continuous at every
sample, measurable at every time, and equal to `W` wherever `W` is continuous with `ζ = ∞`:

* `killedPath`, `regDrv`, `regHull`; `continuous_regDrv`, `measurable_regDrv_apply`, **`regHull_eq`**;
* **`measurableSet_disjoint_closedBall_regHull`**: `{B̄(c, ε) ∩ K̃_{T} = ∅}` is measurable for every measurable random
  time `T` (the tamed-flow criterion `Lemma72D.disjoint_closedBall_fwdHull_iff_real` at `q = T(ω)`);
* **`measurable_regHull`**: `ω ↦ K̃_{T(ω)}` is hitting-measurable (open sets of `ℍ` are countable unions of rational
  closed discs);
* `measurable_wallsHullAt_regHull`: the hitting measurability of `wallsHullAt Γ K̃ T` (the hypothesis `hE`).

Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull tamedZ drive)
open LQGMetric (DistOn)

namespace InteractingSLE.Sec7.PocketStopWallsFin

open Lemma72D Coding Coupling

section Reg

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The driver killed at `ζ` (zero from `ζ` on). -/
def killedPath (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0 → ℝ :=
  fun s => if (s : ℝ≥0∞) < ζ ω then W s ω else 0

/-- **The regularized driver**: the dyadic regularization of the killed driver (continuous at every sample). -/
def regDrv (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0 → ℝ := ZhanGT4.A35.regPath (killedPath W ζ ω)

/-- **The regularized hull** `K̃_t`: the hull of the regularized driver at time `t`. -/
def regHull (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : Set ℂ :=
  fwdHull (fun s : ℝ => regDrv W ζ ω s.toNNReal) (t : ℝ)

omit mΩ in
theorem continuous_regDrv (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : Continuous (regDrv W ζ ω) :=
  ZhanGT4.A35.continuous_regPath _

theorem measurable_killedPath {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hX : IsMeasurableKilledDriving W VL VR ζ) :
    Measurable (killedPath W ζ) := by
  refine measurable_pi_iff.2 fun s => fun A hA => ?_
  have hlt : MeasurableSet {ω | (s : ℝ≥0∞) < ζ ω} := by
    have := hX s univ MeasurableSet.univ
    simpa only [mem_univ, and_true] using this
  have hW : MeasurableSet {ω | (s : ℝ≥0∞) < ζ ω ∧ W s ω ∈ A} := by
    have := hX s (Prod.fst ⁻¹' A) (measurable_fst hA)
    simpa only [mem_preimage] using this
  have e : (fun ω => killedPath W ζ ω s) ⁻¹' A =
      {ω | (s : ℝ≥0∞) < ζ ω ∧ W s ω ∈ A} ∪ ({ω | (s : ℝ≥0∞) < ζ ω}ᶜ ∩ {_ω | (0 : ℝ) ∈ A}) := by
    ext ω
    simp only [killedPath, mem_preimage, mem_union, mem_ofPred_eq, mem_inter_iff, mem_compl_iff]
    by_cases hω : (s : ℝ≥0∞) < ζ ω
    · simp only [hω, ↓reduceIte, true_and, not_true_eq_false, false_and, or_false]
    · simp only [hω, ↓reduceIte, false_and, not_false_eq_true, true_and, false_or]
  rw [e]
  exact hW.union (hlt.compl.inter (MeasurableSet.const _))

theorem measurable_regDrv_apply {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hX : IsMeasurableKilledDriving W VL VR ζ) (t : ℝ≥0) :
    Measurable fun ω => regDrv W ζ ω t :=
  (ZhanGT4.A35.measurable_regPath_apply t).comp (measurable_killedPath hX)

omit mΩ in
/-- **The regularized driver is the driver** where the driver is continuous with infinite lifetime. -/
theorem regDrv_eq {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} (hc : Continuous fun s => W s ω) (hζ : ζ ω = ⊤) :
    regDrv W ζ ω = fun s => W s ω := by
  have e : killedPath W ζ ω = fun s => W s ω := funext fun s => by
    simp only [killedPath, hζ, ENNReal.coe_lt_top, ↓reduceIte]
  rw [regDrv, e, ZhanGT4.A35.regPath_of_continuous hc]

omit mΩ in
/-- **The regularized hull is the hull** where the driver is continuous with infinite lifetime. -/
theorem regHull_eq {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} (hc : Continuous fun s => W s ω) (hζ : ζ ω = ⊤)
    (t : ℝ≥0) : regHull W ζ t ω = fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ) := by
  rw [regHull, regDrv_eq hc hζ]

omit mΩ in
theorem regHull_mono (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : Monotone fun t => regHull W ζ t ω :=
  fun _ _ hab => WangWu.fwdHull_mono (by exact_mod_cast hab)

/-- **Closed-disc avoidance by the regularized hull at a random time is measurable.** -/
theorem measurableSet_disjoint_closedBall_regHull {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hX : IsMeasurableKilledDriving W VL VR ζ) {T : Ω → ℝ≥0}
    (hT : Measurable T) {c : ℂ} {ε : ℝ} (hε : 0 < ε) (hcε : ε < c.im) :
    MeasurableSet {ω | Disjoint (closedBall c ε) (regHull W ζ (T ω) ω)} := by
  set B : ℝ≥0 → Ω → ℝ := fun s ω => regDrv W ζ ω s with hB
  have hBc : ∀ ω, Continuous fun t => B t ω := fun ω => continuous_regDrv W ζ ω
  have hBm : ∀ r : ℝ≥0, Measurable (B r) := fun r => measurable_regDrv_apply hX r
  have hdr : ∀ ω, (fun s : ℝ => regDrv W ζ ω s.toNNReal) = drive 1 B ω := fun ω => funext fun s => by
    simp only [drive, Real.sqrt_one, one_mul, hB]
  clear_value B
  have e : {ω | Disjoint (closedBall c ε) (regHull W ζ (T ω) ω)} =
      ⋃ k : ℕ, ⋂ y : ℚ × ℚ, ⋂ (_ : ratPt y ∈ closedBall c ε), ⋂ s : ℚ, ⋂ (_ : 0 ≤ (s : ℝ)),
        ({ω | (s : ℝ) ≤ (T ω : ℝ)}ᶜ ∪
          {ω | 2 * (1 / ((k : ℝ) + 1)) ≤ (tamedZ (drive 1 B ω) (1 / ((k : ℝ) + 1)) (ratPt y) s).im}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, mem_union, mem_compl_iff, regHull, hdr ω]
    rw [disjoint_closedBall_fwdHull_iff_real (QuantumZipper.NonSwallow.continuous_drive_ns hBc 1 ω)
      (NNReal.coe_nonneg (T ω)) hε hcε]
    refine exists_congr fun k => forall_congr' fun y => forall_congr' fun hy => forall_congr' fun s =>
      forall_congr' fun hs0 => ?_
    constructor
    · intro h
      by_cases hs : (s : ℝ) ≤ (T ω : ℝ)
      · exact Or.inr (h hs)
      · exact Or.inl hs
    · rintro (h | h) h1
      · exact absurd h1 h
      · exact h
  rw [e]
  refine MeasurableSet.iUnion fun k => MeasurableSet.iInter fun y => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun s => MeasurableSet.iInter fun hs0 => MeasurableSet.union ?_ ?_
  · exact (measurableSet_le measurable_const (measurable_coe_nnreal_real.comp hT)).compl
  · have hmeas := (QuantumZipper.measurable_tamed_drive 1 (c := 1 / ((k : ℝ) + 1)) (by positivity) B hBc hs0
      (fun r _ => hBm r)).1
    have hm2 : Measurable fun ω => (tamedZ (drive 1 B ω) (1 / ((k : ℝ) + 1)) (ratPt y) (s : ℝ)).im :=
      Complex.measurable_im.comp (hmeas.comp ((measurable_const (a := ratPt y)).prodMk measurable_id))
    exact measurableSet_le measurable_const hm2

omit mΩ in
/-- `ω ↦ K̃_{T(ω)}` meets an open `U ⊆ ℍ` iff it meets some rational closed disc inside `U`. -/
theorem hitting_eq_iUnion_ratBall {K : Ω → Set ℂ} {U : Set ℂ} (hUo : IsOpen U) :
    K ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
      ⋃ β : WangWu.RatBall, ⋃ (_ : 0 < β.rad ∧ closedBall β.cen β.rad ⊆ U),
        {ω | ¬ Disjoint (closedBall β.cen β.rad) (K ω)} := by
  ext ω
  simp only [mem_preimage, mem_ofPred_eq, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨z, hzK, hzU⟩
    obtain ⟨β, hβ0, hβU, hzβ⟩ := WangWu.exists_rBall hUo hzU
    exact ⟨β, ⟨hβ0, hβU⟩, Set.not_disjoint_iff.2 ⟨z, ball_subset_closedBall hzβ, hzK⟩⟩
  · rintro ⟨β, ⟨-, hβU⟩, hd⟩
    obtain ⟨z, hzβ, hzK⟩ := Set.not_disjoint_iff.1 hd
    exact ⟨z, hzK, hβU hzβ⟩

/-- A closed disc of positive radius inside `ℍ` has its radius below its centre's height. -/
theorem rad_lt_im_of_closedBall_subset_H {c : ℂ} {ε : ℝ} (hε : 0 < ε) (h : closedBall c ε ⊆ H) : ε < c.im := by
  have hmem : c - (ε : ℂ) * Complex.I ∈ closedBall c ε := by
    rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  have := h hmem
  change 0 < (c - (ε : ℂ) * Complex.I).im at this
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
    Complex.I_re, mul_zero, add_zero] at this
  linarith

/-- **The regularized hull at a measurable random time is hitting-measurable.** -/
theorem measurable_regHull {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hX : IsMeasurableKilledDriving W VL VR ζ) {T : Ω → ℝ≥0}
    (hT : Measurable T) : Measurable[mΩ, hittingSigma] fun ω => regHull W ζ (T ω) ω := by
  refine @measurable_generateFrom Ω (Set ℂ) mΩ _ _ ?_
  rintro _ ⟨U, hUo, hUH, rfl⟩
  rw [hitting_eq_iUnion_ratBall hUo]
  refine MeasurableSet.iUnion fun β => MeasurableSet.iUnion fun hβ => ?_
  exact (measurableSet_disjoint_closedBall_regHull hX hT hβ.1
    (rad_lt_im_of_closedBall_subset_H hβ.1 (hβ.2.trans hUH))).compl

/-- **`wallsHullAt Γ K̃ T` is hitting-measurable** for hitting-measurable walls `Γ` and a measurable stop `T`. -/
theorem measurable_wallsHullAt_regHull {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hX : IsMeasurableKilledDriving W VL VR ζ) {Γ : Ω → Set ℂ}
    (hΓ : Measurable[mΩ, hittingSigma] Γ) {T : Ω → ℝ≥0∞} (hT : Measurable T) :
    Measurable[mΩ, hittingSigma] (PocketStopWalls.wallsHullAt Γ (regHull W ζ) T) := by
  refine @measurable_generateFrom Ω (Set ℂ) mΩ _ _ ?_
  rintro _ ⟨U, hUo, hUH, rfl⟩
  have hK := measurable_regHull hX (T := fun ω => (T ω).toNNReal) (ENNReal.measurable_toNNReal.comp hT)
  have hΓU : MeasurableSet (Γ ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty}) :=
    hΓ (LocalSets.measurableSet_hitting hUo hUH)
  have hKU : MeasurableSet ((fun ω => regHull W ζ (T ω).toNNReal ω) ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty}) :=
    hK (LocalSets.measurableSet_hitting hUo hUH)
  have hfin : MeasurableSet {ω | T ω < ⊤} := measurableSet_lt hT measurable_const
  have e : PocketStopWalls.wallsHullAt Γ (regHull W ζ) T ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
      ({ω | T ω < ⊤} ∩ (Γ ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} ∪
        (fun ω => regHull W ζ (T ω).toNNReal ω) ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty})) ∪
      ({ω | T ω < ⊤}ᶜ ∩ {_ω | (H ∩ U).Nonempty}) := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff,
      PocketStopWalls.wallsHullAt]
    by_cases hω : T ω < ⊤
    · simp only [hω, ↓reduceIte, true_and, not_true_eq_false, false_and, or_false]
      constructor
      · rintro ⟨z, ⟨-, hz | hz⟩, hzU⟩
        · exact Or.inl ⟨z, hz, hzU⟩
        · exact Or.inr ⟨z, hz, hzU⟩
      · rintro (⟨z, hz, hzU⟩ | ⟨z, hz, hzU⟩)
        · exact ⟨z, ⟨hUH hzU, Or.inl hz⟩, hzU⟩
        · exact ⟨z, ⟨hUH hzU, Or.inr hz⟩, hzU⟩
    · simp only [hω, ↓reduceIte, false_and, not_false_eq_true, true_and, false_or]
  rw [e]
  exact (hfin.inter (hΓU.union hKU)).union (hfin.compl.inter (MeasurableSet.const _))

end Reg

/-! ### The regularized hull of a frozen coupling -/

section CouplingReg

open WholeField

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕₀ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- An announcing sequence of the lifetime of a frozen coupling with almost surely infinite lifetime. -/
theorem exists_isAnnouncingSeq_of_coupling (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W VL VR B ζ h)
    (hκ : 0 < κ) (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    ∃ σ : ℕ → Ω → ℝ≥0, Coupling.IsAnnouncingSeq (drivingFiltration P hX) P ζ σ := by
  have hE := hC.1
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · exfalso
    have hF : ∀ᵐ ω ∂P, False := by
      filter_upwards [hE.2.2.2.2, hζ] with ω hp hω
      have h0 := WangWu.IsIntegratedSLEPath.lifetime_eq_zero_of_threshold hp hseed
      rw [hω] at h0
      exact ENNReal.top_ne_zero h0
    obtain ⟨_, hf⟩ := hF.exists
    exact hf
  · have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
    obtain ⟨σ, hσ, -⟩ := exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX) (B := B) (κ := κ)
      (xL := xL) (xR := xR) (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
      (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX))
      (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _)
        (Coupling.adaptedBefore_killedDriving_VL hX i))
      (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _)
        (Coupling.adaptedBefore_killedDriving_VR hX i))
      hE.2.2.2.2 (hE.ae_tendsto_threshold hκ) hseed
    exact ⟨σ, hσ⟩

omit [IsProbabilityMeasure P] in
/-- **The regularized hull is the hull almost surely.** -/
theorem ae_regHull_eq (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W VL VR B ζ h) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, regHull W ζ t ω = fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ) := by
  filter_upwards [hC.1.2.2.2.2, hζ] with ω hp hω t
  have hc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} := hp.2.2.2.1
  have huniv : {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} = univ := by
    ext s; simp only [hω, ENNReal.coe_lt_top, mem_ofPred_eq, mem_univ]
  rw [huniv] at hc
  exact regHull_eq (continuousOn_univ.1 hc) hω t

/-- A finite stopping time, read in `ℝ≥0`, is measurable. -/
theorem measurable_untopD_of_isStoppingTime {𝓕 : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓕 τ) (hfin : ∀ ω, τ ω ≠ ⊤) : Measurable fun ω => (τ ω).untopD 0 := by
  refine measurable_of_Iic fun r => ?_
  have e : (fun ω => (τ ω).untopD 0) ⁻¹' Iic r = {ω | τ ω ≤ r} := by
    ext ω
    simp only [mem_preimage, mem_Iic, mem_ofPred_eq]
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 (hfin ω)
    rw [← ht, WithTop.untopD_coe, WithTop.coe_le_coe]
  rw [e]
  exact 𝓕.le r _ (hτ r)

/-- **The regularized hull at a finite stopping time is history-measurable** (through
`WholeField.measurable_hull_stopping`: it is a hitting-measurable version of `K_τ`). -/
theorem measurable_regHull_stopping (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W VL VR B ζ h) (hκ : 0 < κ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hfin : ∀ ω, τ ω ≠ ⊤) :
    Measurable[hτ.measurableSpace, hittingSigma] fun ω => regHull W ζ ((τ ω).untopD 0) ω := by
  obtain ⟨σ, hσ⟩ := exists_isAnnouncingSeq_of_coupling hC hκ hX hζ
  refine measurable_hull_stopping hC.1 hX hσ hτ ?_ (measurable_regHull hX (measurable_untopD_of_isStoppingTime hτ hfin))
    ?_
  · filter_upwards [hζ] with ω hω
    rw [hω]
    exact lt_top_iff_ne_top.2 (by exact_mod_cast hfin ω)
  · filter_upwards [ae_regHull_eq hC hζ] with ω hω
    exact hω _

/-- `{K̃_τ ∩ U = ∅}` is an event of the stopped history, for open `U ⊆ ℍ`. -/
theorem measurableSet_disjoint_regHull_stopping (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W VL VR B ζ h)
    (hκ : 0 < κ) (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hfin : ∀ ω, τ ω ≠ ⊤) (U : Set ℂ) (hUo : IsOpen U)
    (hUH : U ⊆ H) :
    MeasurableSet[hτ.measurableSpace] {ω | Disjoint (regHull W ζ ((τ ω).untopD 0) ω) U} := by
  have hm := measurable_regHull_stopping hC hκ hX hζ hτ hfin (LocalSets.measurableSet_hitting hUo hUH)
  have e : {ω | Disjoint (regHull W ζ ((τ ω).untopD 0) ω) U} =
      ((fun ω => regHull W ζ ((τ ω).untopD 0) ω) ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty})ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, mem_preimage, Set.not_nonempty_iff_eq_empty,
      Set.disjoint_iff_inter_eq_empty]
  rw [e]
  exact hm.compl

/-- `{K̃_t ∩ U = ∅}` is an event of the driving filtration at time `t`. -/
theorem measurableSet_disjoint_regHull (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W VL VR B ζ h)
    (hκ : 0 < κ) (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (t : ℝ≥0) (U : Set ℂ)
    (hUo : IsOpen U) (hUH : U ⊆ H) :
    MeasurableSet[drivingFiltration P hX t] {ω | Disjoint (regHull W ζ t ω) U} := by
  have hc := isStoppingTime_const (drivingFiltration P hX) t
  have h := measurableSet_disjoint_regHull_stopping hC hκ hX hζ (fun _ => (t : WithTop ℝ≥0)) hc
    (fun _ => WithTop.coe_ne_top) U hUo hUH
  rw [IsStoppingTime.measurableSpace_const] at h
  simpa only [WithTop.untopD_coe] using h

/-- **The regularized hull is marked local at every finite stopping time** (Aux. lemmas 18–19 through the capacity
coding theorem, `WholeField.isHistoryAvoidanceLocal_hull`). -/
theorem isHistoryAvoidanceLocal_regHull (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hfin : ∀ ω, τ ω ≠ ⊤) :
    IsHistoryAvoidanceLocal hτ.measurableSpace (fun ω => regHull W ζ ((τ ω).untopD 0) ω) (centredField h u₀) P := by
  refine isHistoryAvoidanceLocal_hull hC hκ hu₀ hX hτ ?_
    (measurable_regHull hX (measurable_untopD_of_isStoppingTime hτ hfin)) ?_
  · filter_upwards [hζ] with ω hω
    rw [hω]
    exact lt_top_iff_ne_top.2 (by exact_mod_cast hfin ω)
  · filter_upwards [ae_regHull_eq hC hζ] with ω hω
    exact hω _

end CouplingReg

end InteractingSLE.Sec7.PocketStopWallsFin
