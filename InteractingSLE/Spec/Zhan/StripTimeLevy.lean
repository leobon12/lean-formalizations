/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripTimeClock
import InteractingSLE.Stochastic.Martingale.OptionalSampling
import MathFin.Probability.Brownian.LevyCharacterization
import InteractingSLE.Spec.Sec2.TwoSeedExistsLevy

/-!
# The strip driver is `√κ` times a Brownian motion in the strip clock

Packet PROVE-ZHAN-A2 (Astra §3, "Complete proof of target change": "Time change and Lévy's characterization identify
the new martingale with `√κ` times Brownian motion in the time-changed filtration"; ruling R36). For an R36 strip
evolution with an almost surely unbounded strip clock on the strip life, the strip-time process

  `B̃_t = (Φ_{s(t)} − Φ_0)/√κ`

(`Φ` the strip martingale of `StripTimeObs.lean` along the evolution, `s(t)` the inverse strip clock `chordT`) is a
Brownian motion in the filtration `𝓗_t = 𝓖_{s(t)}` of the usual augmentation `𝓖` read at the stopping times `s(t)`
(`isFilteredBrownianReal_stripBM`).

Proof. `s(t)` is a stopping time of `𝓖`: `s(t) ≤ r` iff `t ≤ t(r ∧ σ_n)` for some `n`, the stopped strip clocks being
adapted (`isStoppingTime_chordS`). The times `ρ_n = t(σ_n)` are `𝓗`-stopping times (`σ_n ≤ s(t)` iff `ρ_n ≤ t`) and
localize: `B̃_{t ∧ ρ_n} = (M^n_{s(t)} − Φ_0)/√κ` and `B̃²_{t∧ρ_n} − t ∧ ρ_n = (N^n_{s(t)} − 2Φ_0 M^n_{s(t)} + Φ_0²)/κ` with
the chordal martingales `M^n = Φ_{·∧σ_n}`, `N^n = (Φ² − κ t)_{·∧σ_n}` of `StripTimeMart.lean`, which are bounded and
constant after `n`; optional sampling at the bounded stopping times `s(t) ∧ n` makes them `𝓗`-martingales. Lévy's
characterization (vendored `MathFin.LevyCharacterization`) concludes.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

open scoped Classical in
/-- The chordal time at strip time `t` on the good event (`0` off it). -/
def chordS (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  if ω ∈ G then chordT (W · ω) (VL (Fin.last nL) · ω) t else 0

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {pL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω}

section Stopped

variable (hgood : ∀ ω ∈ G, IsGoodStrip κ (Strip.wordXL pL) xR ρL ρR W VL VR B ζ ω)

include hgood in
/-- The stopped strip coordinates have continuous paths. -/
theorem continuous_coordS_stopped (n : ℕ) (ω : Ω) :
    Continuous fun t => coordS (Strip.wordXL pL) xR G W VL VR (min t (stripLoc G W VL VR B ζ n ω)) ω := by
  by_cases hω : ω ∈ G
  · have hF := (hgood ω hω).1.isForcePath
    have hlife := isStripLife_stripLoc (hgood ω hω) hω (n := n)
    set σ := stripLoc G W VL VR B ζ n ω
    have hsub : Iic σ ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs => (hlife.mono hs).1
    have hT : ContinuousOn (fun s : ℝ≥0 => Strip.stripClock (Strip.extPath (W · ω))
        (Strip.extPath (VL (Fin.last nL) · ω)) s) (Iic σ) := by
      have hc := intervalIntegral.continuousOn_primitive_interval'
        (intervalIntegrable_clockRate hF hlife) (left_mem_uIcc (a := (0 : ℝ)) (b := σ))
      refine hc.comp NNReal.continuous_coe.continuousOn fun s hs => ?_
      rw [uIcc_of_le σ.coe_nonneg]
      exact ⟨s.coe_nonneg, by exact_mod_cast hs⟩
    have hX : ContinuousOn (fun s => stripCoordAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s)
        (Iic σ) := (continuousOn_pi.2 fun i => (hF.continuousOn_vL i).mono hsub).prodMk
      ((continuousOn_pi.2 fun j => (hF.continuousOn_vR j).mono hsub).prodMk hT)
    simp only [coordS, hω, ↓reduceIte]
    exact hX.comp_continuous (continuous_id.min continuous_const) fun t => mem_Iic.2 (min_le_right _ _)
  · simp only [coordS, hω, ↓reduceIte]; exact continuous_const

include hgood in
theorem continuous_brownG_stopped (n : ℕ) (ω : Ω) :
    Continuous fun t => Sec2.TwoSeed.brownG G B (min t (stripLoc G W VL VR B ζ n ω)) ω :=
  (continuous_brownG_strip hgood ω).comp (continuous_id.min continuous_const)

end Stopped

theorem wordXL_last_lt (pL : Fin nL → ℝ) (i : Fin nL) :
    Strip.wordXL pL (Fin.last nL) < Strip.wordXL pL i.castSucc := by
  simp only [Strip.wordXL_last, Strip.wordXL_castSucc]
  linarith [Real.exp_pos (pL i)]

section Filt

variable (hE : IsIntegratedSLEEvolution κ (Strip.wordXL pL) xR ρL ρR P 𝓕 W VL VR B ζ)
  (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
  (hgood : ∀ ω ∈ G, IsGoodStrip κ (Strip.wordXL pL) xR ρL ρR W VL VR B ζ ω)

include hgood in
/-- On the good event, `s(t) ≤ r` iff `t ≤ t(r ∧ σ_n)` for some `n`. -/
theorem chordS_le_iff {ω : Ω} (hω : ω ∈ G) (t r : ℝ≥0) :
    chordS G W VL t ω ≤ r ↔ ∃ n : ℕ, (t : ℝ) ≤
      (coordS (Strip.wordXL pL) xR G W VL VR (min r (stripLoc G W VL VR B ζ n ω)) ω).2.2 := by
  have hg := hgood ω hω
  simp only [chordS, coordS, hω, ↓reduceIte, stripCoordAt]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := exists_le_stripLoc hgood (wordXL_last_lt pL) hω
      (isStripLife_chordT hg.1 hg.2.2.2 t)
    have hlife := (isStripLife_stripLoc hg hω (n := n)).mono (min_le_right r _)
    exact ⟨n, (chordT_le_iff hg.1 hg.2.2.2 hlife).1 (le_min h hn)⟩
  · rintro ⟨n, hn⟩
    have hlife := (isStripLife_stripLoc hg hω (n := n)).mono (min_le_right r _)
    exact ((chordT_le_iff hg.1 hg.2.2.2 hlife).2 hn).trans (min_le_left _ _)

include hE hGm hGc hgood in
/-- **The inverse strip clock is a stopping time of the usual augmentation.** -/
theorem isStoppingTime_chordS (t : ℝ≥0) :
    IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (chordS G W VL t ω : WithTop ℝ≥0) := by
  intro r
  have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) r
  have e : {ω | (chordS G W VL t ω : WithTop ℝ≥0) ≤ r} = Gᶜ ∪ (G ∩ ⋃ n : ℕ, {ω | (t : ℝ) ≤
      (coordS (Strip.wordXL pL) xR G W VL VR (min r (stripLoc G W VL VR B ζ n ω)) ω).2.2}) := by
    ext ω
    by_cases hω : ω ∈ G
    · simp only [mem_ofPred_eq, WithTop.coe_le_coe, mem_union, mem_compl_iff, hω,
        not_true_eq_false, false_or, mem_inter_iff, true_and, mem_iUnion]
      exact chordS_le_iff hgood hω t r
    · simp only [chordS, hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_compl_iff,
        not_false_eq_true, true_or, iff_true, WithTop.coe_zero]
      exact_mod_cast zero_le (a := r)
  rw [e]
  exact hG0.compl.union (hG0.inter (MeasurableSet.iUnion fun n =>
    measurableSet_le measurable_const (measurable_coordS_stopped hE hGm hGc hgood n r).snd.snd))

include hgood in
theorem chordS_mono {s t : ℝ≥0} (hst : s ≤ t) (ω : Ω) : chordS G W VL s ω ≤ chordS G W VL t ω := by
  by_cases hω : ω ∈ G
  · simp only [chordS, hω, ↓reduceIte]
    exact monotone_chordT (hgood ω hω).1 (hgood ω hω).2.2.2 hst
  · simp only [chordS, hω, ↓reduceIte, le_refl]

/-- **The strip-time filtration** `𝓗_t = 𝓖_{s(t)}`. -/
def stripFilt : Filtration ℝ≥0 mΩ where
  seq t := (isStoppingTime_chordS hE hGm hGc hgood t).measurableSpace
  mono' _ _ hst := IsStoppingTime.measurableSpace_mono _ _ fun ω =>
    WithTop.coe_le_coe.2 (chordS_mono hgood hst ω)
  le' t := (isStoppingTime_chordS hE hGm hGc hgood t).measurableSpace_le

theorem stripFilt_apply (t : ℝ≥0) :
    stripFilt hE hGm hGc hgood t = (isStoppingTime_chordS hE hGm hGc hgood t).measurableSpace := rfl

end Filt

/-! ### Optional sampling for martingales frozen after a fixed time -/

/-- **Optional sampling at unbounded stopping times** for a bounded continuous martingale that is constant after
`N`: `∫_A M_{τ₂} = ∫_A M_{τ₁}` for `τ₁ ≤ τ₂` and `A ∈ 𝓖_{τ₁}`. -/
theorem setIntegral_comp_eq_of_frozen [IsFiniteMeasure P] {𝓖 : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M 𝓖 P) (hMc : ∀ ω, Continuous (M · ω)) {C : ℝ} (hMb : ∀ r ω, |M r ω| ≤ C)
    (N : ℝ≥0) (hMN : ∀ r ω, M r ω = M (min r N) ω) {τ₁ τ₂ : Ω → ℝ≥0}
    (h1 : IsStoppingTime 𝓖 fun ω => (τ₁ ω : WithTop ℝ≥0))
    (h2 : IsStoppingTime 𝓖 fun ω => (τ₂ ω : WithTop ℝ≥0)) (h12 : ∀ ω, τ₁ ω ≤ τ₂ ω) {A : Set Ω}
    (hA : MeasurableSet[h1.measurableSpace] A) :
    ∫ ω in A, M (τ₂ ω) ω ∂P = ∫ ω in A, M (τ₁ ω) ω ∂P := by
  have hN := isStoppingTime_const 𝓖 N
  have hprog : IsStronglyProgressive 𝓖 M :=
    StronglyAdapted.isStronglyProgressive_of_continuous hM.stronglyAdapted hMc
  have hAm : MeasurableSet A := h1.measurableSpace_le A hA
  have hmeas : ∀ τ : Ω → ℝ≥0, (IsStoppingTime 𝓖 fun ω => (τ ω : WithTop ℝ≥0)) →
      Measurable fun ω => M (τ ω) ω := fun τ hτ => by
    have h := (measurable_stoppedValue hprog hτ).mono hτ.measurableSpace_le le_rfl
    have e : stoppedValue M (fun ω => (τ ω : WithTop ℝ≥0)) = fun ω => M (τ ω) ω := by
      funext ω; simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe]
    rwa [e] at h
  have hint : ∀ τ : Ω → ℝ≥0, (IsStoppingTime 𝓖 fun ω => (τ ω : WithTop ℝ≥0)) →
      IntegrableOn (fun ω => M (τ ω) ω) A P := fun τ hτ =>
    (Integrable.of_bound (hmeas τ hτ).aestronglyMeasurable C (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact hMb _ ω)).integrableOn
  set S : Set Ω := {ω | (τ₁ ω : WithTop ℝ≥0) ≤ (N : WithTop ℝ≥0)} with hSdef
  have hSm : MeasurableSet S := measurableSet_le h1.measurable' measurable_const
  -- on `A ∩ S`: optional sampling at the bounded times `τᵢ ∧ N`
  have hA1 : MeasurableSet[(h1.min hN).measurableSpace] (A ∩ S) :=
    IsStoppingTime.measurableSet_inter_le h1 hN A hA
  have hle : (fun ω => min (τ₁ ω : WithTop ℝ≥0) (N : WithTop ℝ≥0)) ≤
      fun ω => min (τ₂ ω : WithTop ℝ≥0) (N : WithTop ℝ≥0) := fun ω =>
    min_le_min (WithTop.coe_le_coe.2 (h12 ω)) le_rfl
  have hOS := setIntegral_stoppedValue_eq_of_rightContinuous hM
    (fun ω t => (hMc ω).continuousWithinAt) (h1.min hN) (h2.min hN) hle
    (T := N) (fun ω => min_le_right _ _) hA1
  have hsv : ∀ τ : Ω → ℝ≥0, stoppedValue M (fun ω => min (τ ω : WithTop ℝ≥0) (N : WithTop ℝ≥0)) =
      fun ω => M (τ ω) ω := fun τ => by
    funext ω
    simp only [stoppedValue, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe]
    exact (hMN _ ω).symm
  rw [hsv, hsv] at hOS
  -- on `A \ S`: both times exceed `N`
  have hdiff : ∫ ω in A \ S, M (τ₂ ω) ω ∂P = ∫ ω in A \ S, M (τ₁ ω) ω ∂P := by
    refine setIntegral_congr_fun (hAm.diff hSm) fun ω hω => ?_
    have h1N : N < τ₁ ω := by
      have := hω.2
      simp only [hSdef, mem_ofPred_eq, WithTop.coe_le_coe, not_le] at this
      exact this
    rw [hMN (τ₂ ω), hMN (τ₁ ω), min_eq_right h1N.le, min_eq_right (h1N.le.trans (h12 ω))]
  rw [← integral_inter_add_sdiff hSm (hint τ₂ h2), ← integral_inter_add_sdiff hSm (hint τ₁ h1), hOS,
    hdiff]

/-! ### The strip martingale along the evolution -/

/-- The strip observable along the evolution at chordal time `s` (on the good event; at the initial point off it). -/
def phiS (κ : ℝ) (pL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin nR → ℝ)
    (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  stripMartObs κ (Strip.wordXL pL) xR ρL ρR (coordS (Strip.wordXL pL) xR G W VL VR s ω,
    Sec2.TwoSeed.brownG G B s ω)

/-- **The strip Brownian motion**: `B̃_t = (Φ_{s(t)} − Φ_0)/√κ`. -/
def stripBM (κ : ℝ) (pL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin nR → ℝ)
    (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  (phiS κ pL xR ρL ρR G W VL VR B (chordS G W VL t ω) ω -
    stripMartObs κ (Strip.wordXL pL) xR ρL ρR (stripInit (Strip.wordXL pL) xR)) / Real.sqrt κ

/-- The strip-time localizing times `ρ_n = t(σ_n)`. -/
def stripRho (pL : Fin nL → ℝ) (xR : Fin nR → ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (n : ℕ) (ω : Ω) : ℝ≥0 :=
  ((coordS (Strip.wordXL pL) xR G W VL VR (stripLoc G W VL VR B ζ n ω) ω).2.2).toNNReal

section Proc

variable (hgood : ∀ ω ∈ G, IsGoodStrip κ (Strip.wordXL pL) xR ρL ρR W VL VR B ζ ω)

include hgood in
theorem mem_stripKc_coordS (n : ℕ) (s : ℝ≥0) (ω : Ω) :
    (coordS (Strip.wordXL pL) xR G W VL VR (min s (stripLoc G W VL VR B ζ n ω)) ω,
      Sec2.TwoSeed.brownG G B (min s (stripLoc G W VL VR B ζ n ω)) ω) ∈
      stripKc κ (Strip.wordXL pL) xR ρL ρR n := by
  by_cases hω : ω ∈ G
  · simpa only [coordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte] using
      mem_stripKc_of_le_stripLoc (hgood ω hω) hω hgood (min_le_right s _)
  · simp only [coordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
    exact mem_insert _ _

include hgood in
theorem phiS_zero (ω : Ω) : phiS κ pL xR ρL ρR G W VL VR B 0 ω =
    stripMartObs κ (Strip.wordXL pL) xR ρL ρR (stripInit (Strip.wordXL pL) xR) := by
  by_cases hω : ω ∈ G
  · simp only [phiS, coordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
    rw [stripCoordAt_zero_eq (hgood ω hω)]
  · simp only [phiS, coordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte, stripInit]

include hgood in
theorem chordS_zero (ω : Ω) : chordS G W VL 0 ω = 0 := by
  by_cases hω : ω ∈ G
  · have h := chordT_zero (vL := fun i t => VL i t ω) (w := (W · ω)) (hgood ω hω).1 (hgood ω hω).2.2.2
    simp only [chordS, hω, ↓reduceIte]
    exact h
  · simp only [chordS, hω, ↓reduceIte]

include hgood in
theorem stripBM_zero (ω : Ω) : stripBM κ pL xR ρL ρR G W VL VR B 0 ω = 0 := by
  simp only [stripBM, chordS_zero hgood, phiS_zero hgood, sub_self, zero_div]

include hgood in
/-- Eventually in `n`, the localized martingale at `s(t)` is the strip observable at `s(t)`. -/
theorem eventually_phiS_min (t : ℝ≥0) (ω : Ω) : ∀ᶠ n : ℕ in atTop,
    phiS κ pL xR ρL ρR G W VL VR B (min (chordS G W VL t ω) (stripLoc G W VL VR B ζ n ω)) ω =
      phiS κ pL xR ρL ρR G W VL VR B (chordS G W VL t ω) ω := by
  by_cases hω : ω ∈ G
  · have hg := hgood ω hω
    obtain ⟨n, hn⟩ := exists_le_stripLoc hgood (wordXL_last_lt pL) hω
      (isStripLife_chordT hg.1 hg.2.2.2 t)
    filter_upwards [eventually_ge_atTop n] with m hm
    have : chordS G W VL t ω ≤ stripLoc G W VL VR B ζ m ω := by
      simp only [chordS, hω, ↓reduceIte]
      exact hn.trans (stripLoc_mono hgood ω hm)
    rw [min_eq_left this]
  · refine Eventually.of_forall fun m => ?_
    simp only [chordS, hω, ↓reduceIte, zero_le, min_eq_left]

end Proc

/-! ### The localized identities -/

section Ident

variable (hgood : ∀ ω ∈ G, IsGoodStrip κ (Strip.wordXL pL) xR ρL ρR W VL VR B ζ ω)

include hgood in
/-- `s(t ∧ ρ_n) = s(t) ∧ σ_n`. -/
theorem chordS_min_stripRho (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    chordS G W VL (min t (stripRho pL xR G W VL VR B ζ n ω)) ω =
      min (chordS G W VL t ω) (stripLoc G W VL VR B ζ n ω) := by
  by_cases hω : ω ∈ G
  · have hg := hgood ω hω
    have h := chordT_min (vL := fun i t => VL i t ω) (w := (W · ω)) hg.1 hg.2.2.2
      (isStripLife_stripLoc hg hω (n := n)) t
    simp only [chordS, stripRho, coordS, hω, ↓reduceIte, stripCoordAt]
    exact h
  · simp only [chordS, hω, ↓reduceIte, stripLoc_of_not_mem hω n, min_self]

include hgood in
theorem stripBM_min_stripRho (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    stripBM κ pL xR ρL ρR G W VL VR B (min t (stripRho pL xR G W VL VR B ζ n ω)) ω =
      (phiS κ pL xR ρL ρR G W VL VR B (min (chordS G W VL t ω) (stripLoc G W VL VR B ζ n ω)) ω -
        stripMartObs κ (Strip.wordXL pL) xR ρL ρR (stripInit (Strip.wordXL pL) xR)) / Real.sqrt κ := by
  rw [stripBM, chordS_min_stripRho hgood]

include hgood in
/-- The clock coordinate at `s(t) ∧ σ_n` is `t ∧ ρ_n`. -/
theorem coordS_clock_min (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    (coordS (Strip.wordXL pL) xR G W VL VR (min (chordS G W VL t ω) (stripLoc G W VL VR B ζ n ω)) ω).2.2 =
      ((min t (stripRho pL xR G W VL VR B ζ n ω) : ℝ≥0) : ℝ) := by
  by_cases hω : ω ∈ G
  · have hg := hgood ω hω
    rw [← chordS_min_stripRho hgood]
    have h := clk_chordT (vL := fun i t => VL i t ω) (w := (W · ω)) hg.1 hg.2.2.2
      (min t (stripRho pL xR G W VL VR B ζ n ω))
    simp only [chordS, coordS, hω, ↓reduceIte, stripCoordAt]
    exact h
  · simp only [coordS, stripRho, hω, ↓reduceIte, Real.toNNReal_zero, min_zero, NNReal.coe_zero]

include hgood in
theorem stripBM_sq_min_stripRho (hκ : 0 < κ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    stripBM κ pL xR ρL ρR G W VL VR B (min t (stripRho pL xR G W VL VR B ζ n ω)) ω ^ 2 -
        ((min t (stripRho pL xR G W VL VR B ζ n ω) : ℝ≥0) : ℝ) =
      (stripMartObs2 κ (Strip.wordXL pL) xR ρL ρR
          (coordS (Strip.wordXL pL) xR G W VL VR (min (chordS G W VL t ω) (stripLoc G W VL VR B ζ n ω)) ω,
            Sec2.TwoSeed.brownG G B (min (chordS G W VL t ω) (stripLoc G W VL VR B ζ n ω)) ω) -
        2 * stripMartObs κ (Strip.wordXL pL) xR ρL ρR (stripInit (Strip.wordXL pL) xR) *
          phiS κ pL xR ρL ρR G W VL VR B (min (chordS G W VL t ω) (stripLoc G W VL VR B ζ n ω)) ω +
        stripMartObs κ (Strip.wordXL pL) xR ρL ρR (stripInit (Strip.wordXL pL) xR) ^ 2) / κ := by
  rw [stripBM_min_stripRho hgood, ← coordS_clock_min hgood n t ω]
  simp only [stripMartObs2, phiS]
  have hs : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have hs0 : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  field_simp
  rw [hs]
  ring

end Ident

/-! ### Martingales in strip time -/

section StripMart

variable (hE : IsIntegratedSLEEvolution κ (Strip.wordXL pL) xR ρL ρR P 𝓕 W VL VR B ζ)
  (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
  (hgood : ∀ ω ∈ G, IsGoodStrip κ (Strip.wordXL pL) xR ρL ρR W VL VR B ζ ω)

include hE hGm hGc hgood in
/-- **A frozen bounded continuous martingale read at the inverse strip clock is a martingale of the strip-time
filtration** (affine images included). -/
theorem martingale_comp_chordS {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M (usualAugmentation 𝓕 P) P)
    (hMc : ∀ ω, Continuous (M · ω)) {C : ℝ} (hMb : ∀ r ω, |M r ω| ≤ C) (N : ℝ≥0)
    (hMN : ∀ r ω, M r ω = M (min r N) ω) (c d : ℝ) :
    Martingale (fun t ω => c * M (chordS G W VL t ω) ω + d) (stripFilt hE hGm hGc hgood) P := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hprog : IsStronglyProgressive (usualAugmentation 𝓕 P) M :=
    StronglyAdapted.isStronglyProgressive_of_continuous hM.stronglyAdapted hMc
  have hτ := isStoppingTime_chordS hE hGm hGc hgood
  have hmeas : ∀ t, Measurable[stripFilt hE hGm hGc hgood t] fun ω => M (chordS G W VL t ω) ω := by
    intro t
    have h := measurable_stoppedValue hprog (hτ t)
    have e : stoppedValue M (fun ω => (chordS G W VL t ω : WithTop ℝ≥0)) =
        fun ω => M (chordS G W VL t ω) ω := by
      funext ω; simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe]
    rw [e] at h
    exact h
  have hadapt : StronglyAdapted (stripFilt hE hGm hGc hgood) fun t ω => c * M (chordS G W VL t ω) ω + d :=
    fun t => (((hmeas t).const_mul c).add_const d).stronglyMeasurable
  have hint : ∀ t, Integrable (fun ω => c * M (chordS G W VL t ω) ω + d) P := fun t =>
    Integrable.of_bound ((hadapt t).mono ((stripFilt hE hGm hGc hgood).le t)).aestronglyMeasurable
      (|c| * C + |d|) (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        calc |c * M (chordS G W VL t ω) ω + d| ≤ |c * M (chordS G W VL t ω) ω| + |d| := abs_add_le _ _
          _ ≤ |c| * C + |d| := by
            rw [abs_mul]; gcongr; exact hMb _ ω)
  refine ⟨hadapt, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((stripFilt hE hGm hGc hgood).le s) (hint t)
    (fun A _ _ => (hint s).integrableOn) (fun A hA _ => ?_)
    ((hadapt s).mono le_rfl).aestronglyMeasurable).symm
  have hAm : MeasurableSet A := (stripFilt hE hGm hGc hgood).le s A hA
  have hMint : ∀ u, Integrable (fun ω => M (chordS G W VL u ω) ω) P := fun u =>
    Integrable.of_bound ((hmeas u).mono ((stripFilt hE hGm hGc hgood).le u) le_rfl).aestronglyMeasurable
      C (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hMb _ ω)
  have hOS := setIntegral_comp_eq_of_frozen hM hMc hMb N hMN (hτ s) (hτ t)
    (fun ω => chordS_mono hgood hst ω) (A := A) hA
  rw [integral_add ((hMint t).const_mul c).integrableOn integrableOn_const,
    integral_add ((hMint s).const_mul c).integrableOn integrableOn_const, integral_const_mul,
    integral_const_mul, hOS]

end StripMart

/-! ### Localization in strip time and Lévy's characterization -/

section Levy

variable (hE : IsIntegratedSLEEvolution κ (Strip.wordXL pL) xR ρL ρR P 𝓕 W VL VR B ζ)
  (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
  (hgood : ∀ ω ∈ G, IsGoodStrip κ (Strip.wordXL pL) xR ρL ρR W VL VR B ζ ω)
  (h0 : stripInit (Strip.wordXL pL) xR ∈ stripMartRegion κ (Strip.wordXL pL) xR ρL ρR)

include hgood h0 in
theorem exists_bound_obs_stopped {F : SCoord nL nR × ℝ → ℝ}
    (hF : ContinuousOn F (stripMartRegion κ (Strip.wordXL pL) xR ρL ρR)) (n : ℕ) :
    ∃ C, ∀ s ω, |F (coordS (Strip.wordXL pL) xR G W VL VR (min s (stripLoc G W VL VR B ζ n ω)) ω,
      Sec2.TwoSeed.brownG G B (min s (stripLoc G W VL VR B ζ n ω)) ω)| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_stripKc κ (Strip.wordXL pL) xR ρL ρR n).exists_bound_of_continuousOn
    (hF.mono (stripKc_subset_region κ (Strip.wordXL pL) xR ρL ρR h0 n))
  exact ⟨C, fun s ω => by
    have := hC _ (mem_stripKc_coordS hgood n s ω); rwa [Real.norm_eq_abs] at this⟩

include hgood h0 in
theorem continuous_obs_stopped {F : SCoord nL nR × ℝ → ℝ}
    (hF : ContinuousOn F (stripMartRegion κ (Strip.wordXL pL) xR ρL ρR)) (n : ℕ) (ω : Ω) :
    Continuous fun s => F (coordS (Strip.wordXL pL) xR G W VL VR (min s (stripLoc G W VL VR B ζ n ω)) ω,
      Sec2.TwoSeed.brownG G B (min s (stripLoc G W VL VR B ζ n ω)) ω) :=
  hF.comp_continuous ((continuous_coordS_stopped hgood n ω).prodMk (continuous_brownG_stopped hgood n ω))
    fun s => stripKc_subset_region κ (Strip.wordXL pL) xR ρL ρR h0 n (mem_stripKc_coordS hgood n s ω)

theorem min_min_stripLoc (n : ℕ) (s : ℝ≥0) (ω : Ω) :
    min (min s (n : ℝ≥0)) (stripLoc G W VL VR B ζ n ω) = min s (stripLoc G W VL VR B ζ n ω) := by
  rw [min_assoc, min_eq_right (stripLoc_le n ω)]

include hgood in
theorem continuous_chordS (ω : Ω) : Continuous fun t => chordS G W VL t ω := by
  by_cases hω : ω ∈ G
  · simp only [chordS, hω, ↓reduceIte]
    exact continuous_chordT (vL := fun i t => VL i t ω) (w := (W · ω)) (hgood ω hω).1 (hgood ω hω).2.2.2
  · simp only [chordS, hω, ↓reduceIte]; exact continuous_const

include hE hGm hGc hgood in
/-- **The strip-time localizing sequence** `ρ_n = t(σ_n)`. -/
theorem isLocalizingSequence_stripRho :
    IsLocalizingSequence (stripFilt hE hGm hGc hgood)
      (fun n ω => (stripRho pL xR G W VL VR B ζ n ω : WithTop ℝ≥0)) P where
  isStoppingTime n := by
    intro t
    have hτ := isStoppingTime_chordS hE hGm hGc hgood t
    have hσ := isStoppingTime_stripLoc hE hGm hGc hgood n
    have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) 0
    have hGτ : MeasurableSet[hτ.measurableSpace] G := by
      refine (IsStoppingTime.measurableSet hτ G).2 ⟨(le_iSup (usualAugmentation 𝓕 P) 0) G hG0,
        fun i => ((usualAugmentation 𝓕 P).mono (zero_le (a := i)) _ hG0).inter (hτ i)⟩
    have e : {ω | (stripRho pL xR G W VL VR B ζ n ω : WithTop ℝ≥0) ≤ t} =
        Gᶜ ∪ (G ∩ {ω | (stripLoc G W VL VR B ζ n ω : WithTop ℝ≥0) ≤ (chordS G W VL t ω : WithTop ℝ≥0)}) := by
      ext ω
      by_cases hω : ω ∈ G
      · have hg := hgood ω hω
        have hlife := isStripLife_stripLoc hg hω (n := n)
        simp only [mem_ofPred_eq, WithTop.coe_le_coe, mem_union, mem_compl_iff, hω, not_true_eq_false,
          false_or, mem_inter_iff, true_and]
        simp only [stripRho, chordS, coordS, hω, ↓reduceIte, stripCoordAt]
        rw [le_chordT_iff (vL := fun i t => VL i t ω) (w := (W · ω)) hg.1 hg.2.2.2 hlife,
          Real.toNNReal_le_iff_le_coe]
        rfl
      · simp only [stripRho, coordS, hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_compl_iff,
          not_false_eq_true, true_or, iff_true, Real.toNNReal_zero, WithTop.coe_zero]
        exact_mod_cast zero_le (a := t)
    show MeasurableSet[hτ.measurableSpace] _
    rw [e]
    exact hGτ.compl.union (hGτ.inter (IsStoppingTime.measurableSet_stopping_time_le hσ hτ))
  mono := ae_of_all _ fun ω m n hmn => by
    by_cases hω : ω ∈ G
    · have hg := hgood ω hω
      simp only [stripRho, coordS, hω, ↓reduceIte, stripCoordAt, WithTop.coe_le_coe]
      refine Real.toNNReal_le_toNNReal ?_
      exact (clk_le_clk_iff (vL := fun i t => VL i t ω) (w := (W · ω)) hg.1
        (isStripLife_stripLoc hg hω (n := m)) (isStripLife_stripLoc hg hω (n := n))).2
        (stripLoc_mono hgood ω hmn)
    · simp only [stripRho, coordS, hω, ↓reduceIte, le_refl]
  tendsto_top := by
    filter_upwards [show ∀ᵐ ω ∂P, ω ∈ G from by rw [ae_iff]; exact hGc] with ω hω
    have hg := hgood ω hω
    rw [WithTop.tendsto_nhds_top_iff]
    intro x
    obtain ⟨S, hS, hxS⟩ := hg.2.2.2 ((x : ℝ) + 1)
    obtain ⟨n₀, hn₀⟩ := exists_le_stripLoc hgood (wordXL_last_lt pL) hω hS
    filter_upwards [eventually_ge_atTop n₀] with n hn
    have hle := (clk_le_clk_iff (vL := fun i t => VL i t ω) (w := (W · ω)) hg.1 hS
      (isStripLife_stripLoc hg hω (n := n))).2 (hn₀.trans (stripLoc_mono hgood ω hn))
    simp only [stripRho, coordS, hω, ↓reduceIte, stripCoordAt, WithTop.coe_lt_coe]
    rw [Real.lt_toNNReal_iff_coe_lt]
    have : (x : ℝ) + 1 ≤ clk (W · ω) (VL (Fin.last nL) · ω) (stripLoc G W VL VR B ζ n ω) :=
      hxS.trans hle
    simp only [clk] at this
    linarith

end Levy

/-! ### Lévy's characterization -/

section Main

variable (hE : IsIntegratedSLEEvolution κ (Strip.wordXL pL) xR ρL ρR P 𝓕 W VL VR B ζ)
  (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
  (hgood : ∀ ω ∈ G, IsGoodStrip κ (Strip.wordXL pL) xR ρL ρR W VL VR B ζ ω)
  (h0 : stripInit (Strip.wordXL pL) xR ∈ stripMartRegion κ (Strip.wordXL pL) xR ρL ρR) (hκ : 0 < κ)

theorem stoppedProcess_coe_apply (X : ℝ≥0 → Ω → ℝ) (ρ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    stoppedProcess X (fun ω => (ρ ω : WithTop ℝ≥0)) t ω = X (min t (ρ ω)) ω := by
  simp only [stoppedProcess, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe]

include hgood in
theorem exists_lt_stripRho {ω : Ω} (hω : ω ∈ G) (x : ℝ≥0) :
    ∃ n, x < stripRho pL xR G W VL VR B ζ n ω := by
  have hg := hgood ω hω
  obtain ⟨S, hS, hxS⟩ := hg.2.2.2 ((x : ℝ) + 1)
  obtain ⟨n, hn⟩ := exists_le_stripLoc hgood (wordXL_last_lt pL) hω hS
  refine ⟨n, ?_⟩
  have hle := (clk_le_clk_iff (vL := fun i t => VL i t ω) (w := (W · ω)) hg.1 hS
    (isStripLife_stripLoc hg hω (n := n))).2 hn
  simp only [stripRho, coordS, hω, ↓reduceIte, stripCoordAt]
  rw [Real.lt_toNNReal_iff_coe_lt]
  have : (x : ℝ) + 1 ≤ clk (W · ω) (VL (Fin.last nL) · ω) (stripLoc G W VL VR B ζ n ω) := hxS.trans hle
  simp only [clk] at this
  linarith

theorem stripRho_of_not_mem {ω : Ω} (hω : ω ∉ G) (n : ℕ) : stripRho pL xR G W VL VR B ζ n ω = 0 := by
  simp only [stripRho, coordS, hω, ↓reduceIte, Real.toNNReal_zero]

include hE hGm hGc hgood h0 hκ in
/-- `B̃` stopped at `ρ_n` is a martingale of the strip-time filtration. -/
theorem martingale_stripBM_stopped (n : ℕ) :
    Martingale (stoppedProcess (stripBM κ pL xR ρL ρR G W VL VR B)
      (fun ω => (stripRho pL xR G W VL VR B ζ n ω : WithTop ℝ≥0))) (stripFilt hE hGm hGc hgood) P := by
  have hM := martingale_stripMartObs hE hGm hGc hgood hκ.le h0 n
  have hF := (contDiffOn_stripMartObs κ (Strip.wordXL pL) xR ρL ρR (n := 0)).continuousOn
  obtain ⟨C, hC⟩ := exists_bound_obs_stopped hgood h0 hF n
  have hMart := martingale_comp_chordS hE hGm hGc hgood hM (continuous_obs_stopped hgood h0 hF n) hC n
    (fun r ω => by simp only [min_min_stripLoc]) (1 / Real.sqrt κ)
    (-(stripMartObs κ (Strip.wordXL pL) xR ρL ρR (stripInit (Strip.wordXL pL) xR) / Real.sqrt κ))
  convert hMart using 1
  funext t ω
  rw [stoppedProcess_coe_apply, stripBM_min_stripRho hgood]
  simp only [phiS]
  ring

include hE hGm hGc hgood h0 hκ in
/-- `B̃² − t` stopped at `ρ_n` is a martingale of the strip-time filtration. -/
theorem martingale_stripBM_sq_stopped (n : ℕ) :
    Martingale (stoppedProcess (fun t ω => stripBM κ pL xR ρL ρR G W VL VR B t ω ^ 2 - (t : ℝ))
      (fun ω => (stripRho pL xR G W VL VR B ζ n ω : WithTop ℝ≥0))) (stripFilt hE hGm hGc hgood) P := by
  set Φ₀ := stripMartObs κ (Strip.wordXL pL) xR ρL ρR (stripInit (Strip.wordXL pL) xR)
  have hM := martingale_stripMartObs hE hGm hGc hgood hκ.le h0 n
  have hN := martingale_stripMartObs2 hE hGm hGc hgood hκ.le h0 n
  have hF := (contDiffOn_stripMartObs κ (Strip.wordXL pL) xR ρL ρR (n := 0)).continuousOn
  have hF2 := (contDiffOn_stripMartObs2 κ (Strip.wordXL pL) xR ρL ρR (n := 0)).continuousOn
  obtain ⟨C, hC⟩ := exists_bound_obs_stopped hgood h0 hF n
  obtain ⟨C2, hC2⟩ := exists_bound_obs_stopped hgood h0 hF2 n
  have h1 := martingale_comp_chordS hE hGm hGc hgood hM (continuous_obs_stopped hgood h0 hF n) hC n
    (fun r ω => by simp only [min_min_stripLoc]) (-(2 * Φ₀) / κ) 0
  have h2 := martingale_comp_chordS hE hGm hGc hgood hN (continuous_obs_stopped hgood h0 hF2 n) hC2 n
    (fun r ω => by simp only [min_min_stripLoc]) (1 / κ) (Φ₀ ^ 2 / κ)
  convert h2.add h1 using 1
  funext t ω
  rw [stoppedProcess_coe_apply]
  simp only [Pi.add_apply]
  rw [stripBM_sq_min_stripRho hgood hκ]
  simp only [phiS]
  ring

include hgood in
theorem continuous_stripBM_stopped (h0' : stripInit (Strip.wordXL pL) xR ∈
    stripMartRegion κ (Strip.wordXL pL) xR ρL ρR) (n : ℕ) (ω : Ω) :
    Continuous fun t => stripBM κ pL xR ρL ρR G W VL VR B (min t (stripRho pL xR G W VL VR B ζ n ω)) ω := by
  have hF := (contDiffOn_stripMartObs κ (Strip.wordXL pL) xR ρL ρR (n := 0)).continuousOn
  have hc := (continuous_obs_stopped hgood h0' hF n ω).comp (continuous_chordS hgood ω)
  simp_rw [stripBM_min_stripRho hgood]
  exact (hc.sub continuous_const).div_const _

include hgood h0 in
theorem continuous_stripBM (ω : Ω) : Continuous fun t => stripBM κ pL xR ρL ρR G W VL VR B t ω := by
  by_cases hω : ω ∈ G
  · refine continuous_iff_continuousAt.2 fun t₀ => ?_
    obtain ⟨n, hn⟩ := exists_lt_stripRho hgood hω (t₀ + 1)
    have heq : (fun t => stripBM κ pL xR ρL ρR G W VL VR B (min t (stripRho pL xR G W VL VR B ζ n ω)) ω)
        =ᶠ[𝓝 t₀] fun t => stripBM κ pL xR ρL ρR G W VL VR B t ω := by
      filter_upwards [Iio_mem_nhds (lt_add_one t₀)] with t ht
      rw [min_eq_left (le_of_lt ((mem_Iio.1 ht).trans hn))]
    exact ((continuous_stripBM_stopped hgood h0 n ω).continuousAt).congr heq
  · have : (fun t => stripBM κ pL xR ρL ρR G W VL VR B t ω) = fun _ => 0 := by
      funext t
      have hz : chordS G W VL t ω = 0 := by simp only [chordS, hω, ↓reduceIte]
      simp only [stripBM, hz, phiS_zero hgood, sub_self, zero_div]
    rw [this]; exact continuous_const

include hE hGm hGc hgood h0 hκ in
theorem stronglyAdapted_stripBM :
    StronglyAdapted (stripFilt hE hGm hGc hgood) (stripBM κ pL xR ρL ρR G W VL VR B) := by
  intro t
  have hmeas : ∀ n : ℕ, Measurable[stripFilt hE hGm hGc hgood t] fun ω =>
      stripBM κ pL xR ρL ρR G W VL VR B (min t (stripRho pL xR G W VL VR B ζ n ω)) ω := fun n => by
    have := ((martingale_stripBM_stopped hE hGm hGc hgood h0 hκ n).stronglyAdapted t).measurable
    have e : stoppedProcess (stripBM κ pL xR ρL ρR G W VL VR B)
        (fun ω => (stripRho pL xR G W VL VR B ζ n ω : WithTop ℝ≥0)) t = fun ω =>
        stripBM κ pL xR ρL ρR G W VL VR B (min t (stripRho pL xR G W VL VR B ζ n ω)) ω :=
      funext fun ω => stoppedProcess_coe_apply _ _ t ω
    rw [e] at this
    exact this
  refine (@measurable_of_tendsto_metrizable Ω ℝ (stripFilt hE hGm hGc hgood t) _ _ _ _ _ _ hmeas
    (tendsto_pi_nhds.2 fun ω => ?_)).stronglyMeasurable
  refine tendsto_const_nhds.congr' ?_
  by_cases hω : ω ∈ G
  · obtain ⟨n, hn⟩ := exists_lt_stripRho hgood hω t
    have hmono : Monotone fun n => stripRho pL xR G W VL VR B ζ n ω := fun m k hmk => by
      have := (isLocalizingSequence_stripRho hE hGm hGc hgood).mono
      have hg := hgood ω hω
      simp only [stripRho, coordS, hω, ↓reduceIte, stripCoordAt]
      exact Real.toNNReal_le_toNNReal ((clk_le_clk_iff (vL := fun i t => VL i t ω) (w := (W · ω)) hg.1
        (isStripLife_stripLoc hg hω (n := m)) (isStripLife_stripLoc hg hω (n := k))).2
        (stripLoc_mono hgood ω hmk))
    filter_upwards [eventually_ge_atTop n] with k hk
    rw [min_eq_left (hn.trans_le (hmono hk)).le]
  · refine Eventually.of_forall fun k => ?_
    show stripBM κ pL xR ρL ρR G W VL VR B t ω =
      stripBM κ pL xR ρL ρR G W VL VR B (min t (stripRho pL xR G W VL VR B ζ k ω)) ω
    rw [stripRho_of_not_mem hω, min_zero]
    have hz : ∀ u, chordS G W VL u ω = 0 := fun u => by simp only [chordS, hω, ↓reduceIte]
    simp only [stripBM, hz]

include hE hGm hGc hgood h0 hκ in
/-- **The strip driver's martingale part is `√κ` times a Brownian motion in the strip clock**:
`B̃_t = (Φ_{s(t)} − Φ_0)/√κ` is a Brownian motion of the strip-time filtration `𝓗_t = 𝓖_{s(t)}`. -/
theorem isFilteredBrownianReal_stripBM :
    IsFilteredBrownianReal (stripFilt hE hGm hGc hgood) (stripBM κ pL xR ρL ρR G W VL VR B) P := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hB0 : ∀ ω, stripBM κ pL xR ρL ρR G W VL VR B 0 ω = 0 := stripBM_zero hgood
  have hBc := continuous_stripBM hgood h0
  have hBa := stronglyAdapted_stripBM hE hGm hGc hgood h0 hκ
  have hloc := isLocalizingSequence_stripRho hE hGm hGc hgood
  have hBloc : IsLocalMartingale (stripBM κ pL xR ρL ρR G W VL VR B) (stripFilt hE hGm hGc hgood) P := by
    refine ⟨_, hloc, fun n => ?_⟩
    rw [Sec2.TwoSeed.stoppedProcess_indicator_eq' hB0]
    refine ⟨martingale_stripBM_stopped hE hGm hGc hgood h0 hκ n, fun ω => ?_⟩
    have e : (fun t => stoppedProcess (stripBM κ pL xR ρL ρR G W VL VR B)
        (fun ω => (stripRho pL xR G W VL VR B ζ n ω : WithTop ℝ≥0)) t ω) =
        fun t => stripBM κ pL xR ρL ρR G W VL VR B (min t (stripRho pL xR G W VL VR B ζ n ω)) ω :=
      funext fun t => stoppedProcess_coe_apply _ _ t ω
    rw [e]
    exact (continuous_stripBM_stopped hgood h0 n ω).isCadlag
  have hB2loc : IsLocalMartingale (fun t ω => stripBM κ pL xR ρL ρR G W VL VR B t ω ^ 2 - (t : ℝ))
      (stripFilt hE hGm hGc hgood) P := by
    refine ⟨_, hloc, fun n => ?_⟩
    rw [Sec2.TwoSeed.stoppedProcess_indicator_eq' (X := fun t ω =>
      stripBM κ pL xR ρL ρR G W VL VR B t ω ^ 2 - (t : ℝ)) (fun ω => by simp [hB0])]
    refine ⟨martingale_stripBM_sq_stopped hE hGm hGc hgood h0 hκ n, fun ω => ?_⟩
    have e : (fun t => stoppedProcess (fun t ω => stripBM κ pL xR ρL ρR G W VL VR B t ω ^ 2 - (t : ℝ))
        (fun ω => (stripRho pL xR G W VL VR B ζ n ω : WithTop ℝ≥0)) t ω) =
        fun t => stripBM κ pL xR ρL ρR G W VL VR B (min t (stripRho pL xR G W VL VR B ζ n ω)) ω ^ 2 -
          ((min t (stripRho pL xR G W VL VR B ζ n ω) : ℝ≥0) : ℝ) :=
      funext fun t => stoppedProcess_coe_apply _ _ t ω
    rw [e]
    exact (((continuous_stripBM_stopped hgood h0 n ω).pow 2).sub
      (NNReal.continuous_coe.comp (continuous_id.min continuous_const))).isCadlag
  have hpre := MathFin.LevyCharacterization.isFilteredPreBrownian_of_localMartingale hBa hBc hB0
    hBloc hB2loc
  have hbm := MathFin.LevyCharacterization.isBrownianReal_of_localMartingale hBa hBc hB0
    hBloc hB2loc
  exact ⟨hbm, hBa.adapted, fun s t hst => hpre.indep s t hst⟩

end Main

end Zhan

end InteractingSLE
