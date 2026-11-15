/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseSelFullWord
import InteractingSLE.Spec.Sec7.PhaseSel3

/-!
# §7.4, Aux. lemma 122 before a stopping lifetime, with a random initial word

Packet PROVE-STRIPSYS5 (specification §7.4, Aux. lemma 122, `source/spec/p385-432.md` L104–L131; the hypotheses (A1)
and (A3) of `planning/handoffs/PROVE-STRIPSYS4.md` §2 removed).

* `ae_lifetime_eq_zero_of_couplingMean_of_opposite`: Aux. lemmas 117 and 104 before a stopping lifetime `T`: if the
  explicit coupling means of a word whose seed parameters have opposite signs are local martingales before swallowing
  and before `T`, then `T = 0` almost surely (the initial word, including the distant marks, is random);
* `phase_eq_of_pos_before`: the phase is constant on `(0, T]` along one path (the landed `PhaseSel.phase_eq_of_pos`
  with the hypotheses only up to `T`);
* `ae_phase_eq_zero_before`: **Aux. lemma 122** (the phase selection) before a stopping lifetime, with a random word.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace PhaseSelFull

open MartChar Aux117 PhaseSel

section Exclusion

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- A process adapted to `𝓕` is adapted before a stopping time. -/
theorem adaptedBefore_of_stronglyAdapted' {X : ℝ≥0 → Ω → ℝ} (hX : StronglyAdapted 𝓕 X)
    {T : Ω → WithTop ℝ≥0} (hT : IsStoppingTime 𝓕 T) : AdaptedBefore 𝓕 (fun ω => (T ω : ℝ≥0∞)) X := by
  intro t A hA
  have h1 : MeasurableSet[𝓕 t] {ω | (t : WithTop ℝ≥0) < T ω} := by
    have := (hT t).compl
    convert this using 1
    ext ω; simp only [mem_ofPred_eq, mem_compl_iff, not_le]
  exact h1.inter ((hX t).measurable hA)

/-- **Aux. lemmas 117 and 104 before a stopping lifetime, with a random word.** If the seed parameters
`a = ρ^L_0 + 2` and `b = ρ^R_0 + 2` have opposite signs, both seeds start at `0`, the distant marks start strictly
away from `0` (at random positions), and every explicit coupling mean is a local martingale before swallowing and
before the stopping time `T`, then `T = 0` almost surely. -/
theorem ae_lifetime_eq_zero_of_couplingMean_of_opposite [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
    {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} (hseedL : ∀ ω, VL 0 0 ω = 0) (hseedR : ∀ ω, VR 0 0 ω = 0)
    (hxLd : ∀ ω (i : Fin nL), VL i.succ 0 ω < 0) (hxRd : ∀ ω (j : Fin nR), 0 < VR j.succ 0 ω)
    (hab : (0 < ρL 0 + 2 ∧ ρR 0 + 2 < 0) ∨ (0 < ρR 0 + 2 ∧ ρL 0 + 2 < 0))
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i))
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hpathL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpathR : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VR i t ω))
    (hantiL : ∀ ω i, Antitone fun t => VL i t ω) (hmonoR : ∀ ω j, Monotone fun t => VR j t ω)
    (hidxL : ∀ ω t, Antitone fun i => VL i t ω) (hidxR : ∀ ω t, Monotone fun j => VR j t ω)
    (hmergeL : ∀ ω i j s t, s ≤ t → VL i s ω = VL j s ω → VL i t ω = VL j t ω)
    (hmergeR : ∀ ω i j s t, s ≤ t → VR i s ω = VR j s ω → VR i t ω = VR j t ω)
    (hsep : ∀ ω t, 0 < t → ∀ i j, VL i t ω = W t ω → VR j t ω ≠ W t ω)
    {T : Ω → WithTop ℝ≥0} (hT : IsStoppingTime 𝓕 T)
    (hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
      (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
      (coupProc κ ρL ρR W VL VR z)) :
    ∀ᵐ ω ∂P, T ω = 0 := by
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓦, B, hB, -, -, hent⟩ := exists_isWordEntrance_before hκ hW0 hWc hWa hVLa hVRa
    hordL hordR hpathL hpathR hantiL hmonoR hidxL hidxR hmergeL hmergeR hsep hT hmart
  set Q : Measure (Ω × Ω₀) := P.prod P₀ with hQ
  set 𝓖₀ := WholeField.prodFiltration 𝓕 𝓦 with h𝓖₀
  set 𝓖 := usualAugmentation 𝓖₀ Q with h𝓖
  have hB𝓖 := Ito.isFilteredBrownianReal_usualAugmentation hB
  have h𝓖₀𝓖 : 𝓖₀ ≤ 𝓖 := Ito.le_usualAugmentation 𝓖₀ Q
  have hT' : IsStoppingTime 𝓖₀ fun p : Ω × Ω₀ => T p.1 := isStoppingTime_fst hT
  have had : ∀ X : ℝ≥0 → Ω → ℝ, StronglyAdapted 𝓕 X →
      AdaptedBefore 𝓖₀ (fun p : Ω × Ω₀ => (T p.1 : ℝ≥0∞)) fun t p => X t p.1 := fun X hX =>
    adaptedBefore_of_stronglyAdapted' (stronglyAdapted_fst hX) hT'
  have hρL : ρL 0 ≠ -2 := by rcases hab with ⟨h1, -⟩ | ⟨-, h2⟩ <;> intro h <;> linarith
  have hρR : ρR 0 ≠ -2 := by rcases hab with ⟨-, h1⟩ | ⟨h2, -⟩ <;> intro h <;> linarith
  set δ : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hδdef
  have hδ : ∀ m, 0 < δ m := fun m => by positivity
  have hcW : ∀ p : Ω × Ω₀, ∀ S : ℝ≥0∞, ContinuousOn (W · p.1) {t : ℝ≥0 | (t : ℝ≥0∞) < S} :=
    fun p S => (hWc p.1).continuousOn
  have hcL : ∀ p : Ω × Ω₀, ∀ S : ℝ≥0∞, ∀ i, ContinuousOn (fun t => VL i t p.1) {t : ℝ≥0 | (t : ℝ≥0∞) < S} :=
    fun p S i => (hpathL p.1 i).1.continuousOn
  have hcR : ∀ p : Ω × Ω₀, ∀ S : ℝ≥0∞, ∀ j, ContinuousOn (fun t => VR j t p.1) {t : ℝ≥0 | (t : ℝ≥0∞) < S} :=
    fun p S j => (hpathR p.1 j).1.continuousOn
  have hzero : ∀ m, ∀ᵐ p ∂Q, gapLoc (δ m) (W · p.1) (fun i t => VL i t p.1) (fun j t => VR j t p.1)
      (T p.1) = 0 := by
    intro m
    have hadW := adaptedBefore_gapLoc h𝓖₀𝓖 (had W hWa) (fun i => had _ (hVLa i)) (fun j => had _ (hVRa j))
      (δ m) (had W hWa)
    have hadL := fun i => adaptedBefore_gapLoc h𝓖₀𝓖 (had W hWa) (fun i => had _ (hVLa i))
      (fun j => had _ (hVRa j)) (δ m) (had _ (hVLa i))
    have hadR := fun j => adaptedBefore_gapLoc h𝓖₀𝓖 (had W hWa) (fun i => had _ (hVLa i))
      (fun j => had _ (hVRa j)) (δ m) (had _ (hVRa j))
    refine ae_lifetime_eq_zero_of_isWordEntrance (κ := κ) (B := B)
      (xL := fun p i => VL i 0 p.1) (xR := fun p j => VR j 0 p.1) hB𝓖 hadW hadL hadR hab ?_
      (Eventually.of_forall fun p => ⟨hseedL p.1, hseedR p.1, hxLd p.1, hxRd p.1⟩)
    filter_upwards [hent] with p hp
    refine hp _ gapLoc_le fun u _ hu => ?_
    obtain ⟨hgL, hgR⟩ := le_gap_of_lt_gapLoc (hcW p _) (hcL p _) (hcR p _) hu
    refine ⟨colliderNe_of_lt_gapLoc hρL (hδ m) fun i => (hgL i).trans (le_abs_self _), ?_⟩
    exact colliderNe_of_lt_gapLoc hρR (hδ m) fun j => by
      rw [abs_sub_comm]; exact (hgR j).trans (le_abs_self _)
  have hlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hprod : ∀ᵐ p ∂Q, T p.1 = 0 := by
    filter_upwards [ae_all_iff.2 hzero] with p hp
    by_contra hne
    have hTpos : (0 : ℝ≥0∞) < T p.1 := pos_iff_ne_zero.2 hne
    have hevL : ∀ᶠ m in atTop, ∀ i : Fin nL, δ m < -VL i.succ 0 p.1 :=
      Filter.eventually_all.2 fun i => hlim.eventually (gt_mem_nhds (by linarith [hxLd p.1 i]))
    have hevR : ∀ᶠ m in atTop, ∀ j : Fin nR, δ m < VR j.succ 0 p.1 :=
      Filter.eventually_all.2 fun j => hlim.eventually (gt_mem_nhds (hxRd p.1 j))
    obtain ⟨m, hmL, hmR⟩ := (hevL.and hevR).exists
    have hpos := gapLoc_pos (δ := δ m) hTpos (hcW p _) (hcL p _) (hcR p _)
      (fun i => by simp only [hW0, zero_sub]; exact hmL i)
      (fun j => by simp only [hW0, sub_zero]; exact hmR j)
    rw [hp m] at hpos
    exact lt_irrefl _ hpos
  rw [ae_iff] at hprod ⊢
  have e : {p : Ω × Ω₀ | ¬ T p.1 = 0} = {ω | ¬ T ω = 0} ×ˢ (univ : Set Ω₀) := by
    ext p; simp
  rw [e, hQ, Measure.prod_prod, measure_univ, mul_one] at hprod
  exact hprod

end Exclusion

section Const

variable {nL nR : ℕ}

/-- **The phase is constant on `(0, L]`** (the landed `PhaseSel.phase_eq_of_pos` with the boundary description
`d_t ∈ cℤ` only for `0 < t ≤ L` and the continuity of the actual mean only on `[0, T]`, `T ≤ L`). -/
theorem phase_eq_of_pos_before {k c : ℝ} (hc : c ≠ 0) {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ} (hwc : Continuous w)
    (hvLc : ∀ i, Continuous (vL i)) (hvRc : ∀ j, Continuous (vR j)) (hordL : ∀ t i, vL i t ≤ w t)
    (hordR : ∀ t j, w t ≤ vR j t) (hantiL : Antitone (vL 0))
    (hmonoR : Monotone (vR 0)) (hnull : volume {u : ℝ | 0 ≤ u ∧ vL 0 u.toNNReal = w u.toNNReal} = 0)
    {L : ℝ≥0∞} {d : ℝ≥0 → ℝ} (hd : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ L → ∃ n : ℤ, d t = n * c)
    {U : ℝ≥0 → ℂ → ℝ}
    (hU : ∀ t, IsBoundedHarmonicExtension
      (phaseData k ρL ρR (fun i => vL i t - w t) (fun j => vR j t - w t) (d t))
      (forceJumpSet (fun i => vL i t - w t) (fun j => vR j t - w t)) (U t))
    (hcont : ∀ (z : ℂ) (T : ℝ), 0 ≤ T → (T.toNNReal : ℝ≥0∞) ≤ L →
      z ∈ H \ QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) T →
      ContinuousOn (fun t : ℝ => couplingMean k (fun s : ℝ => w s.toNNReal) t (U t.toNNReal) z) (Icc 0 T))
    {s t : ℝ≥0} (hs : 0 < s) (ht : 0 < t) (hsL : (s : ℝ≥0∞) ≤ L) (htL : (t : ℝ≥0∞) ≤ L) : d s = d t := by
  set wr : ℝ → ℝ := fun r => w r.toNNReal with hwr
  have hwrc : Continuous wr := hwc.comp continuous_real_toNNReal
  set T : ℝ := max (s : ℝ) t with hT
  have hT0 : 0 ≤ T := le_max_of_le_left s.coe_nonneg
  have hTL : (T.toNNReal : ℝ≥0∞) ≤ L := by
    have : T.toNNReal = max s t := by
      rw [hT, ← NNReal.coe_max, Real.toNNReal_coe]
    rw [this, ENNReal.coe_max]
    exact max_le hsL htL
  -- a far point, not swallowed before `T`
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hwrc.continuousOn
  set z : ℂ := Complex.I * ((|K| + 3 * Real.sqrt T + 1 : ℝ) : ℂ) with hzdef
  have hzim : z.im = |K| + 3 * Real.sqrt T + 1 := by simp [hzdef]
  have hzH : z ∈ H := by
    show (0 : ℝ) < z.im
    rw [hzim]
    positivity
  have hznorm : |K| + 3 * Real.sqrt T < ‖z‖ := by
    have h1 := Complex.abs_im_le_norm z
    have h2 := le_abs_self z.im
    linarith
  have hz : z ∈ H \ QuantumZipper.fwdHull wr T :=
    mem_diff_fwdHull_of_norm hwrc hT0 (fun r hr => (Real.norm_eq_abs _ ▸ hK r hr).trans (le_abs_self K)) hzH
      hznorm
  -- the three continuous functions
  set X : ℝ → ℝ := fun r => couplingMean k wr r (U r.toNNReal) z with hX
  set X₀ : ℝ → ℝ := fun r => couplingMean k wr r
    (meanExt k ρL ρR (wr r) (fun i => vL i r.toNNReal) (fun j => vR j r.toNNReal)) z with hX₀
  set pw : ℝ → ℝ := fun r => phaseWindow (vL 0 r.toNNReal - wr r) (vR 0 r.toNNReal - wr r)
    (QuantumZipper.fwdMap wr r z) with hpw
  have hXc : ContinuousOn X (Icc 0 T) := hcont z T hT0 hTL hz
  have hX₀c : ContinuousOn X₀ (Icc 0 T) := by
    have hv : ∀ j, ContinuousOn (fun r : ℝ => jointV (fun i => vL i r.toNNReal) (fun i => vR i r.toNNReal) j)
        (Icc 0 T) := fun j => by
      cases j with
      | inl i => exact ((hvLc i).comp continuous_real_toNNReal).continuousOn
      | inr i => exact ((hvRc i).comp continuous_real_toNNReal).continuousOn
    have h := (continuousOn_const (c := Real.pi / Real.sqrt k * (1 + ∑ i, ρR i))).add
      (continuousOn_harmPart k (jointρ ρL ρR) hwrc hT0 hz hv)
    refine h.congr fun r hr => ?_
    have hf : QuantumZipper.fwdMap wr r z ∈ H := Ito.im_fwdMap_pos hwrc hT0 hz hr
    simp only [hX₀]
    rw [couplingMean_meanExt_eq k ρL ρR (fun i => hordL _ i) (fun j => hordR _ j) hf]
    rfl
  have hpwc : ContinuousOn pw (Icc 0 T) :=
    continuousOn_phaseWindow hwrc hT0 hz
      ((((hvLc 0).comp continuous_real_toNNReal).sub hwrc).continuousOn)
      ((((hvRc 0).comp continuous_real_toNNReal).sub hwrc).continuousOn)
  -- `d` is their combination on `(0, T]`
  have hpos : ∀ r ∈ Ioc (0 : ℝ) T, 0 < pw r := fun r hr => by
    have hsep : vL 0 r.toNNReal < vR 0 r.toNNReal :=
      seed_lt_seed hantiL hmonoR (fun t => hordL t 0) (fun t => hordR t 0) hnull
        (Real.toNNReal_pos.2 hr.1)
    exact (phaseWindow_mem_Ioo (by linarith) (Ito.im_fwdMap_pos hwrc hT0 hz (Ioc_subset_Icc_self hr))).1
  have hrep : EqOn (fun r : ℝ => d r.toNNReal) (fun r => (X r - X₀ r) / pw r) (Ioc 0 T) := fun r hr => by
    have hsep : vL 0 r.toNNReal < vR 0 r.toNNReal :=
      seed_lt_seed hantiL hmonoR (fun t => hordL t 0) (fun t => hordR t 0) hnull
        (Real.toNNReal_pos.2 hr.1)
    have hf : QuantumZipper.fwdMap wr r z ∈ H := Ito.im_fwdMap_pos hwrc hT0 hz (Ioc_subset_Icc_self hr)
    have h := couplingMean_sub_couplingMean_eq (k := k) (ρL := ρL) (ρR := ρR) (w := wr) (t := r)
      (vL := fun i => vL i r.toNNReal) (vR := fun j => vR j r.toNNReal) (d := d r.toNNReal) hsep (hU r.toNNReal) hf
    simp only [hX, hX₀, hpw]
    rw [h, mul_div_assoc, div_self (hpos r hr).ne', mul_one]
  have hdc : ContinuousOn (fun r : ℝ => d r.toNNReal) (Ioc 0 T) :=
    (((hXc.mono Ioc_subset_Icc_self).sub (hX₀c.mono Ioc_subset_Icc_self)).div (hpwc.mono Ioc_subset_Icc_self)
      fun r hr => (hpos r hr).ne').congr hrep
  have hmem : ∀ r ∈ Ioc (0 : ℝ) T, ∃ n : ℤ, d r.toNNReal = n * c := fun r hr => by
    refine hd _ (Real.toNNReal_pos.2 hr.1) (le_trans ?_ hTL)
    exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal hr.2)
  have hsT : (s : ℝ) ∈ Ioc (0 : ℝ) T := ⟨by exact_mod_cast hs, le_max_left _ _⟩
  have htT : (t : ℝ) ∈ Ioc (0 : ℝ) T := ⟨by exact_mod_cast ht, le_max_right _ _⟩
  have := eq_of_isPreconnected_of_continuousOn_of_mem_zmultiples isPreconnected_Ioc hdc hc hmem hsT htT
  simpa only [Real.toNNReal_coe] using this

end Const

section Main

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- A local martingale before `ζ` minus a constant, changed only after `ζ`, is a local martingale before `ζ`. -/
theorem isLocalMartingaleBefore_sub_const_before {Ω' : Type*} {m' : MeasurableSpace Ω'} {Q : Measure Ω'}
    [IsFiniteMeasure Q] {𝓖 : Filtration ℝ≥0 m'} {ζ : Ω' → WithTop ℝ≥0} {X Y : ℝ≥0 → Ω' → ℝ} (c : ℝ)
    (hX : IsLocalMartingaleBefore 𝓖 Q ζ X)
    (hY : ∀ (t : ℝ≥0) ω, (t : WithTop ℝ≥0) ≤ ζ ω → Y t ω = X t ω - c) : IsLocalMartingaleBefore 𝓖 Q ζ Y := by
  obtain ⟨σ, hσ, hσζ, hae, hmart⟩ := hX
  refine ⟨σ, hσ, hσζ, hae, fun n => ?_⟩
  have e : stoppedProcess Y (σ n) = stoppedProcess X (σ n) - fun _ _ => c := by
    funext t ω
    simp only [stoppedProcess, Pi.sub_apply]
    refine hY _ ω ?_
    rcases eq_or_ne (σ n ω) ⊤ with h | h
    · have hζ : ζ ω = ⊤ := top_le_iff.1 (h ▸ hσζ n ω)
      rw [hζ]; exact le_top
    · rw [coe_untopA_of_ne_top (ne_top_of_le_ne_top h (min_le_right _ _))]
      exact (min_le_right _ _).trans (hσζ n ω)
  rw [e]
  exact (hmart n).sub (martingale_const 𝓖 Q c)

end Main

end PhaseSelFull

end Sec7

end InteractingSLE
