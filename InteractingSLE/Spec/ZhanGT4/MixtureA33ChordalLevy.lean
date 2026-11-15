/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MixtureA33ChordalMart
import InteractingSLE.Spec.ZhanGT4.MixtureA33ChordalClock
import InteractingSLE.Spec.Zhan.StripTimeLevy

/-!
# Upper strip marks: the strip Brownian motion (Lévy's characterization in the strip clock)

Packet PROVE-ZHAN-A33. PROVE-ZHAN-A2's `StripTimeLevy.lean` for the word `upWordXL q` (the end mark `−1` innermost,
upper strip marks `−1 − e^{q_i}` beyond it) and right lower marks: on a good event the inverse strip clock `s(t)`
(`upChordS`) is a stopping time of the usual augmentation, `𝓗_t = 𝓖_{s(t)}` is a filtration (`upStripFilt`), and
`B̃_t = (Φ_{s(t)} − Φ_0)/√κ` (`upBM`) is an `𝓗`-Brownian motion (`isFilteredBrownianReal_upBM`): `B̃` and `B̃² − t` are
local martingales along `ρ_n = t(σ_n)`, and MathFin's Lévy characterization applies.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.UpMark

open Zhan

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

open scoped Classical in
/-- The chordal time at strip time `t` on the good event (`0` off it). -/
def upChordS (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  if ω ∈ G then chordT (W · ω) (VL 0 · ω) t else 0

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {pL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω}

section Stopped

variable (hgood : ∀ ω ∈ G, IsGoodUp κ (upWordXL pL) xR ρL ρR W VL VR B ζ ω)

include hgood in
/-- The stopped strip coordinates have continuous paths. -/
theorem continuous_upCoordS_stopped (n : ℕ) (ω : Ω) :
    Continuous fun t => upCoordS (upWordXL pL) xR G W VL VR (min t (upLoc G W VL VR B ζ n ω)) ω := by
  by_cases hω : ω ∈ G
  · have hF := (hgood ω hω).1.isForcePath
    have hlife := isStripLife_upLoc (hgood ω hω) hω (n := n)
    set σ := upLoc G W VL VR B ζ n ω
    have hsub : Iic σ ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs => (hlife.mono hs).1
    have hT : ContinuousOn (fun s : ℝ≥0 => Strip.stripClock (Strip.extPath (W · ω))
        (Strip.extPath (VL 0 · ω)) s) (Iic σ) := by
      have hc := intervalIntegral.continuousOn_primitive_interval'
        (intervalIntegrable_clockRate hF hlife) (left_mem_uIcc (a := (0 : ℝ)) (b := σ))
      refine hc.comp NNReal.continuous_coe.continuousOn fun s hs => ?_
      rw [uIcc_of_le σ.coe_nonneg]
      exact ⟨s.coe_nonneg, by exact_mod_cast hs⟩
    have hX : ContinuousOn (fun s => upCoordAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s)
        (Iic σ) := (continuousOn_pi.2 fun i => (hF.continuousOn_vL i).mono hsub).prodMk
      ((continuousOn_pi.2 fun j => (hF.continuousOn_vR j).mono hsub).prodMk hT)
    simp only [upCoordS, hω, ↓reduceIte]
    exact hX.comp_continuous (continuous_id.min continuous_const) fun t => mem_Iic.2 (min_le_right _ _)
  · simp only [upCoordS, hω, ↓reduceIte]; exact continuous_const

include hgood in
theorem continuous_brownG_stopped (n : ℕ) (ω : Ω) :
    Continuous fun t => Sec2.TwoSeed.brownG G B (min t (upLoc G W VL VR B ζ n ω)) ω :=
  (continuous_brownG_up hgood ω).comp (continuous_id.min continuous_const)

end Stopped

section Filt

variable (hE : IsIntegratedSLEEvolution κ (upWordXL pL) xR ρL ρR P 𝓕 W VL VR B ζ)
  (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
  (hgood : ∀ ω ∈ G, IsGoodUp κ (upWordXL pL) xR ρL ρR W VL VR B ζ ω)

include hgood in
/-- On the good event, `s(t) ≤ r` iff `t ≤ t(r ∧ σ_n)` for some `n`. -/
theorem upChordS_le_iff {ω : Ω} (hω : ω ∈ G) (t r : ℝ≥0) :
    upChordS G W VL t ω ≤ r ↔ ∃ n : ℕ, (t : ℝ) ≤
      (upCoordS (upWordXL pL) xR G W VL VR (min r (upLoc G W VL VR B ζ n ω)) ω).2.2 := by
  have hg := hgood ω hω
  simp only [upChordS, upCoordS, hω, ↓reduceIte, upCoordAt]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := exists_le_upLoc hgood (upWordXL_succ_lt pL) hω
      (isStripLife_chordT_up hg.1 (upWordXL_zero pL) hg.2.2.2 t)
    have hlife := (isStripLife_upLoc hg hω (n := n)).mono (min_le_right r _)
    exact ⟨n, (chordT_le_iff_up hg.1 (upWordXL_zero pL) hg.2.2.2 hlife).1 (le_min h hn)⟩
  · rintro ⟨n, hn⟩
    have hlife := (isStripLife_upLoc hg hω (n := n)).mono (min_le_right r _)
    exact ((chordT_le_iff_up hg.1 (upWordXL_zero pL) hg.2.2.2 hlife).2 hn).trans (min_le_left _ _)

include hE hGm hGc hgood in
/-- **The inverse strip clock is a stopping time of the usual augmentation.** -/
theorem isStoppingTime_upChordS (t : ℝ≥0) :
    IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (upChordS G W VL t ω : WithTop ℝ≥0) := by
  intro r
  have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) r
  have e : {ω | (upChordS G W VL t ω : WithTop ℝ≥0) ≤ r} = Gᶜ ∪ (G ∩ ⋃ n : ℕ, {ω | (t : ℝ) ≤
      (upCoordS (upWordXL pL) xR G W VL VR (min r (upLoc G W VL VR B ζ n ω)) ω).2.2}) := by
    ext ω
    by_cases hω : ω ∈ G
    · simp only [mem_ofPred_eq, WithTop.coe_le_coe, mem_union, mem_compl_iff, hω,
        not_true_eq_false, false_or, mem_inter_iff, true_and, mem_iUnion]
      exact upChordS_le_iff hgood hω t r
    · simp only [upChordS, hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_compl_iff,
        not_false_eq_true, true_or, iff_true, WithTop.coe_zero]
      exact_mod_cast zero_le (a := r)
  rw [e]
  exact hG0.compl.union (hG0.inter (MeasurableSet.iUnion fun n =>
    measurableSet_le measurable_const (measurable_upCoordS_stopped hE hGm hGc hgood n r).snd.snd))

include hgood in
theorem upChordS_mono {s t : ℝ≥0} (hst : s ≤ t) (ω : Ω) : upChordS G W VL s ω ≤ upChordS G W VL t ω := by
  by_cases hω : ω ∈ G
  · simp only [upChordS, hω, ↓reduceIte]
    exact monotone_chordT_up (hgood ω hω).1 (upWordXL_zero pL) (hgood ω hω).2.2.2 hst
  · simp only [upChordS, hω, ↓reduceIte, le_refl]

/-- **The strip-time filtration** `𝓗_t = 𝓖_{s(t)}`. -/
def upStripFilt : Filtration ℝ≥0 mΩ where
  seq t := (isStoppingTime_upChordS hE hGm hGc hgood t).measurableSpace
  mono' _ _ hst := IsStoppingTime.measurableSpace_mono _ _ fun ω =>
    WithTop.coe_le_coe.2 (upChordS_mono hgood hst ω)
  le' t := (isStoppingTime_upChordS hE hGm hGc hgood t).measurableSpace_le

theorem upStripFilt_apply (t : ℝ≥0) :
    upStripFilt hE hGm hGc hgood t = (isStoppingTime_upChordS hE hGm hGc hgood t).measurableSpace := rfl

end Filt

/-! ### The strip martingale along the evolution -/

/-- The strip observable along the evolution at chordal time `s` (on the good event; at the initial point off it). -/
def upPhiS (κ : ℝ) (pL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin nR → ℝ)
    (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  upObs κ (upWordXL pL) xR ρL ρR (upCoordS (upWordXL pL) xR G W VL VR s ω,
    Sec2.TwoSeed.brownG G B s ω)

/-- **The strip Brownian motion**: `B̃_t = (Φ_{s(t)} − Φ_0)/√κ`. -/
def upBM (κ : ℝ) (pL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin nR → ℝ)
    (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  (upPhiS κ pL xR ρL ρR G W VL VR B (upChordS G W VL t ω) ω -
    upObs κ (upWordXL pL) xR ρL ρR (stripInit (upWordXL pL) xR)) / Real.sqrt κ

/-- The strip-time localizing times `ρ_n = t(σ_n)`. -/
def upRho (pL : Fin nL → ℝ) (xR : Fin nR → ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (n : ℕ) (ω : Ω) : ℝ≥0 :=
  ((upCoordS (upWordXL pL) xR G W VL VR (upLoc G W VL VR B ζ n ω) ω).2.2).toNNReal

section Proc

variable (hgood : ∀ ω ∈ G, IsGoodUp κ (upWordXL pL) xR ρL ρR W VL VR B ζ ω)

include hgood in
theorem mem_upKc_upCoordS (n : ℕ) (s : ℝ≥0) (ω : Ω) :
    (upCoordS (upWordXL pL) xR G W VL VR (min s (upLoc G W VL VR B ζ n ω)) ω,
      Sec2.TwoSeed.brownG G B (min s (upLoc G W VL VR B ζ n ω)) ω) ∈
      upKc κ (upWordXL pL) xR ρL ρR n := by
  by_cases hω : ω ∈ G
  · simpa only [upCoordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte] using
      mem_upKc_of_le_upLoc (hgood ω hω) hω hgood (min_le_right s _)
  · simp only [upCoordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
    exact mem_insert _ _

include hgood in
theorem upPhiS_zero (ω : Ω) : upPhiS κ pL xR ρL ρR G W VL VR B 0 ω =
    upObs κ (upWordXL pL) xR ρL ρR (stripInit (upWordXL pL) xR) := by
  by_cases hω : ω ∈ G
  · simp only [upPhiS, upCoordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
    rw [upCoordAt_zero_eq (hgood ω hω)]
  · simp only [upPhiS, upCoordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte, stripInit]

include hgood in
theorem upChordS_zero (ω : Ω) : upChordS G W VL 0 ω = 0 := by
  by_cases hω : ω ∈ G
  · have h := chordT_zero_up (vL := fun i t => VL i t ω) (w := (W · ω)) (hgood ω hω).1 (upWordXL_zero pL) (hgood ω hω).2.2.2
    simp only [upChordS, hω, ↓reduceIte]
    exact h
  · simp only [upChordS, hω, ↓reduceIte]

include hgood in
theorem upBM_zero (ω : Ω) : upBM κ pL xR ρL ρR G W VL VR B 0 ω = 0 := by
  simp only [upBM, upChordS_zero hgood, upPhiS_zero hgood, sub_self, zero_div]

include hgood in
/-- Eventually in `n`, the localized martingale at `s(t)` is the strip observable at `s(t)`. -/
theorem eventually_upPhiS_min (t : ℝ≥0) (ω : Ω) : ∀ᶠ n : ℕ in atTop,
    upPhiS κ pL xR ρL ρR G W VL VR B (min (upChordS G W VL t ω) (upLoc G W VL VR B ζ n ω)) ω =
      upPhiS κ pL xR ρL ρR G W VL VR B (upChordS G W VL t ω) ω := by
  by_cases hω : ω ∈ G
  · have hg := hgood ω hω
    obtain ⟨n, hn⟩ := exists_le_upLoc hgood (upWordXL_succ_lt pL) hω
      (isStripLife_chordT_up hg.1 (upWordXL_zero pL) hg.2.2.2 t)
    filter_upwards [eventually_ge_atTop n] with m hm
    have : upChordS G W VL t ω ≤ upLoc G W VL VR B ζ m ω := by
      simp only [upChordS, hω, ↓reduceIte]
      exact hn.trans (upLoc_mono hgood ω hm)
    rw [min_eq_left this]
  · refine Eventually.of_forall fun m => ?_
    simp only [upChordS, hω, ↓reduceIte, zero_le, min_eq_left]

end Proc

/-! ### The localized identities -/

section Ident

variable (hgood : ∀ ω ∈ G, IsGoodUp κ (upWordXL pL) xR ρL ρR W VL VR B ζ ω)

include hgood in
/-- `s(t ∧ ρ_n) = s(t) ∧ σ_n`. -/
theorem upChordS_min_upRho (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    upChordS G W VL (min t (upRho pL xR G W VL VR B ζ n ω)) ω =
      min (upChordS G W VL t ω) (upLoc G W VL VR B ζ n ω) := by
  by_cases hω : ω ∈ G
  · have hg := hgood ω hω
    have h := chordT_min_up (vL := fun i t => VL i t ω) (w := (W · ω)) hg.1 (upWordXL_zero pL) hg.2.2.2
      (isStripLife_upLoc hg hω (n := n)) t
    simp only [upChordS, upRho, upCoordS, hω, ↓reduceIte, upCoordAt]
    exact h
  · simp only [upChordS, hω, ↓reduceIte, upLoc_of_not_mem hω n, min_self]

include hgood in
theorem upBM_min_upRho (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    upBM κ pL xR ρL ρR G W VL VR B (min t (upRho pL xR G W VL VR B ζ n ω)) ω =
      (upPhiS κ pL xR ρL ρR G W VL VR B (min (upChordS G W VL t ω) (upLoc G W VL VR B ζ n ω)) ω -
        upObs κ (upWordXL pL) xR ρL ρR (stripInit (upWordXL pL) xR)) / Real.sqrt κ := by
  rw [upBM, upChordS_min_upRho hgood]

include hgood in
/-- The clock coordinate at `s(t) ∧ σ_n` is `t ∧ ρ_n`. -/
theorem upCoordS_clock_min (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    (upCoordS (upWordXL pL) xR G W VL VR (min (upChordS G W VL t ω) (upLoc G W VL VR B ζ n ω)) ω).2.2 =
      ((min t (upRho pL xR G W VL VR B ζ n ω) : ℝ≥0) : ℝ) := by
  by_cases hω : ω ∈ G
  · have hg := hgood ω hω
    rw [← upChordS_min_upRho hgood]
    have h := clk_chordT_up (vL := fun i t => VL i t ω) (w := (W · ω)) hg.1 (upWordXL_zero pL) hg.2.2.2
      (min t (upRho pL xR G W VL VR B ζ n ω))
    simp only [upChordS, upCoordS, hω, ↓reduceIte, upCoordAt]
    exact h
  · simp only [upCoordS, upRho, hω, ↓reduceIte, Real.toNNReal_zero, min_zero, NNReal.coe_zero]

include hgood in
theorem upBM_sq_min_upRho (hκ : 0 < κ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    upBM κ pL xR ρL ρR G W VL VR B (min t (upRho pL xR G W VL VR B ζ n ω)) ω ^ 2 -
        ((min t (upRho pL xR G W VL VR B ζ n ω) : ℝ≥0) : ℝ) =
      (upObs2 κ (upWordXL pL) xR ρL ρR
          (upCoordS (upWordXL pL) xR G W VL VR (min (upChordS G W VL t ω) (upLoc G W VL VR B ζ n ω)) ω,
            Sec2.TwoSeed.brownG G B (min (upChordS G W VL t ω) (upLoc G W VL VR B ζ n ω)) ω) -
        2 * upObs κ (upWordXL pL) xR ρL ρR (stripInit (upWordXL pL) xR) *
          upPhiS κ pL xR ρL ρR G W VL VR B (min (upChordS G W VL t ω) (upLoc G W VL VR B ζ n ω)) ω +
        upObs κ (upWordXL pL) xR ρL ρR (stripInit (upWordXL pL) xR) ^ 2) / κ := by
  rw [upBM_min_upRho hgood, ← upCoordS_clock_min hgood n t ω]
  simp only [upObs2, upPhiS]
  have hs : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have hs0 : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  field_simp
  rw [hs]
  ring

end Ident

/-! ### Martingales in strip time -/

section StripMart

variable (hE : IsIntegratedSLEEvolution κ (upWordXL pL) xR ρL ρR P 𝓕 W VL VR B ζ)
  (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
  (hgood : ∀ ω ∈ G, IsGoodUp κ (upWordXL pL) xR ρL ρR W VL VR B ζ ω)

include hE hGm hGc hgood in
/-- **A frozen bounded continuous martingale read at the inverse strip clock is a martingale of the strip-time
filtration** (affine images included). -/
theorem martingale_comp_upChordS {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M (usualAugmentation 𝓕 P) P)
    (hMc : ∀ ω, Continuous (M · ω)) {C : ℝ} (hMb : ∀ r ω, |M r ω| ≤ C) (N : ℝ≥0)
    (hMN : ∀ r ω, M r ω = M (min r N) ω) (c d : ℝ) :
    Martingale (fun t ω => c * M (upChordS G W VL t ω) ω + d) (upStripFilt hE hGm hGc hgood) P := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hprog : IsStronglyProgressive (usualAugmentation 𝓕 P) M :=
    StronglyAdapted.isStronglyProgressive_of_continuous hM.stronglyAdapted hMc
  have hτ := isStoppingTime_upChordS hE hGm hGc hgood
  have hmeas : ∀ t, Measurable[upStripFilt hE hGm hGc hgood t] fun ω => M (upChordS G W VL t ω) ω := by
    intro t
    have h := measurable_stoppedValue hprog (hτ t)
    have e : stoppedValue M (fun ω => (upChordS G W VL t ω : WithTop ℝ≥0)) =
        fun ω => M (upChordS G W VL t ω) ω := by
      funext ω; simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe]
    rw [e] at h
    exact h
  have hadapt : StronglyAdapted (upStripFilt hE hGm hGc hgood) fun t ω => c * M (upChordS G W VL t ω) ω + d :=
    fun t => (((hmeas t).const_mul c).add_const d).stronglyMeasurable
  have hint : ∀ t, Integrable (fun ω => c * M (upChordS G W VL t ω) ω + d) P := fun t =>
    Integrable.of_bound ((hadapt t).mono ((upStripFilt hE hGm hGc hgood).le t)).aestronglyMeasurable
      (|c| * C + |d|) (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        calc |c * M (upChordS G W VL t ω) ω + d| ≤ |c * M (upChordS G W VL t ω) ω| + |d| := abs_add_le _ _
          _ ≤ |c| * C + |d| := by
            rw [abs_mul]; gcongr; exact hMb _ ω)
  refine ⟨hadapt, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((upStripFilt hE hGm hGc hgood).le s) (hint t)
    (fun A _ _ => (hint s).integrableOn) (fun A hA _ => ?_)
    ((hadapt s).mono le_rfl).aestronglyMeasurable).symm
  have hAm : MeasurableSet A := (upStripFilt hE hGm hGc hgood).le s A hA
  have hMint : ∀ u, Integrable (fun ω => M (upChordS G W VL u ω) ω) P := fun u =>
    Integrable.of_bound ((hmeas u).mono ((upStripFilt hE hGm hGc hgood).le u) le_rfl).aestronglyMeasurable
      C (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hMb _ ω)
  have hOS := setIntegral_comp_eq_of_frozen hM hMc hMb N hMN (hτ s) (hτ t)
    (fun ω => upChordS_mono hgood hst ω) (A := A) hA
  rw [integral_add ((hMint t).const_mul c).integrableOn integrableOn_const,
    integral_add ((hMint s).const_mul c).integrableOn integrableOn_const, integral_const_mul,
    integral_const_mul, hOS]

end StripMart

/-! ### Localization in strip time and Lévy's characterization -/

section Levy

variable (hE : IsIntegratedSLEEvolution κ (upWordXL pL) xR ρL ρR P 𝓕 W VL VR B ζ)
  (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
  (hgood : ∀ ω ∈ G, IsGoodUp κ (upWordXL pL) xR ρL ρR W VL VR B ζ ω)
  (h0 : stripInit (upWordXL pL) xR ∈ upRegion κ (upWordXL pL) xR ρL ρR)

include hgood h0 in
theorem exists_bound_obs_stopped {F : SCoord nL nR × ℝ → ℝ}
    (hF : ContinuousOn F (upRegion κ (upWordXL pL) xR ρL ρR)) (n : ℕ) :
    ∃ C, ∀ s ω, |F (upCoordS (upWordXL pL) xR G W VL VR (min s (upLoc G W VL VR B ζ n ω)) ω,
      Sec2.TwoSeed.brownG G B (min s (upLoc G W VL VR B ζ n ω)) ω)| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_upKc κ (upWordXL pL) xR ρL ρR n).exists_bound_of_continuousOn
    (hF.mono (upKc_subset_region κ (upWordXL pL) xR ρL ρR h0 n))
  exact ⟨C, fun s ω => by
    have := hC _ (mem_upKc_upCoordS hgood n s ω); rwa [Real.norm_eq_abs] at this⟩

include hgood h0 in
theorem continuous_obs_stopped {F : SCoord nL nR × ℝ → ℝ}
    (hF : ContinuousOn F (upRegion κ (upWordXL pL) xR ρL ρR)) (n : ℕ) (ω : Ω) :
    Continuous fun s => F (upCoordS (upWordXL pL) xR G W VL VR (min s (upLoc G W VL VR B ζ n ω)) ω,
      Sec2.TwoSeed.brownG G B (min s (upLoc G W VL VR B ζ n ω)) ω) :=
  hF.comp_continuous ((continuous_upCoordS_stopped hgood n ω).prodMk (continuous_brownG_stopped hgood n ω))
    fun s => upKc_subset_region κ (upWordXL pL) xR ρL ρR h0 n (mem_upKc_upCoordS hgood n s ω)

theorem min_min_upLoc (n : ℕ) (s : ℝ≥0) (ω : Ω) :
    min (min s (n : ℝ≥0)) (upLoc G W VL VR B ζ n ω) = min s (upLoc G W VL VR B ζ n ω) := by
  rw [min_assoc, min_eq_right (upLoc_le n ω)]

include hgood in
theorem continuous_upChordS (ω : Ω) : Continuous fun t => upChordS G W VL t ω := by
  by_cases hω : ω ∈ G
  · simp only [upChordS, hω, ↓reduceIte]
    exact continuous_chordT_up (vL := fun i t => VL i t ω) (w := (W · ω)) (hgood ω hω).1 (upWordXL_zero pL) (hgood ω hω).2.2.2
  · simp only [upChordS, hω, ↓reduceIte]; exact continuous_const

include hE hGm hGc hgood in
/-- **The strip-time localizing sequence** `ρ_n = t(σ_n)`. -/
theorem isLocalizingSequence_upRho :
    IsLocalizingSequence (upStripFilt hE hGm hGc hgood)
      (fun n ω => (upRho pL xR G W VL VR B ζ n ω : WithTop ℝ≥0)) P where
  isStoppingTime n := by
    intro t
    have hτ := isStoppingTime_upChordS hE hGm hGc hgood t
    have hσ := isStoppingTime_upLoc hE hGm hGc hgood n
    have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) 0
    have hGτ : MeasurableSet[hτ.measurableSpace] G := by
      refine (IsStoppingTime.measurableSet hτ G).2 ⟨(le_iSup (usualAugmentation 𝓕 P) 0) G hG0,
        fun i => ((usualAugmentation 𝓕 P).mono (zero_le (a := i)) _ hG0).inter (hτ i)⟩
    have e : {ω | (upRho pL xR G W VL VR B ζ n ω : WithTop ℝ≥0) ≤ t} =
        Gᶜ ∪ (G ∩ {ω | (upLoc G W VL VR B ζ n ω : WithTop ℝ≥0) ≤ (upChordS G W VL t ω : WithTop ℝ≥0)}) := by
      ext ω
      by_cases hω : ω ∈ G
      · have hg := hgood ω hω
        have hlife := isStripLife_upLoc hg hω (n := n)
        simp only [mem_ofPred_eq, WithTop.coe_le_coe, mem_union, mem_compl_iff, hω, not_true_eq_false,
          false_or, mem_inter_iff, true_and]
        simp only [upRho, upChordS, upCoordS, hω, ↓reduceIte, upCoordAt]
        rw [le_chordT_iff_up (vL := fun i t => VL i t ω) (w := (W · ω)) hg.1 (upWordXL_zero pL) hg.2.2.2 hlife,
          Real.toNNReal_le_iff_le_coe]
        rfl
      · simp only [upRho, upCoordS, hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_compl_iff,
          not_false_eq_true, true_or, iff_true, Real.toNNReal_zero, WithTop.coe_zero]
        exact_mod_cast zero_le (a := t)
    show MeasurableSet[hτ.measurableSpace] _
    rw [e]
    exact hGτ.compl.union (hGτ.inter (IsStoppingTime.measurableSet_stopping_time_le hσ hτ))
  mono := ae_of_all _ fun ω m n hmn => by
    by_cases hω : ω ∈ G
    · have hg := hgood ω hω
      simp only [upRho, upCoordS, hω, ↓reduceIte, upCoordAt, WithTop.coe_le_coe]
      refine Real.toNNReal_le_toNNReal ?_
      exact (clk_le_clk_iff_up (vL := fun i t => VL i t ω) (w := (W · ω)) hg.1 (upWordXL_zero pL)
        (isStripLife_upLoc hg hω (n := m)) (isStripLife_upLoc hg hω (n := n))).2
        (upLoc_mono hgood ω hmn)
    · simp only [upRho, upCoordS, hω, ↓reduceIte, le_refl]
  tendsto_top := by
    filter_upwards [show ∀ᵐ ω ∂P, ω ∈ G from by rw [ae_iff]; exact hGc] with ω hω
    have hg := hgood ω hω
    rw [WithTop.tendsto_nhds_top_iff]
    intro x
    obtain ⟨S, hS, hxS⟩ := hg.2.2.2 ((x : ℝ) + 1)
    obtain ⟨n₀, hn₀⟩ := exists_le_upLoc hgood (upWordXL_succ_lt pL) hω hS
    filter_upwards [eventually_ge_atTop n₀] with n hn
    have hle := (clk_le_clk_iff_up (vL := fun i t => VL i t ω) (w := (W · ω)) hg.1 (upWordXL_zero pL) hS
      (isStripLife_upLoc hg hω (n := n))).2 (hn₀.trans (upLoc_mono hgood ω hn))
    simp only [upRho, upCoordS, hω, ↓reduceIte, upCoordAt, WithTop.coe_lt_coe]
    rw [Real.lt_toNNReal_iff_coe_lt]
    have : (x : ℝ) + 1 ≤ clk (W · ω) (VL 0 · ω) (upLoc G W VL VR B ζ n ω) :=
      hxS.trans hle
    simp only [clk] at this
    linarith

end Levy

/-! ### Lévy's characterization -/

section Main

variable (hE : IsIntegratedSLEEvolution κ (upWordXL pL) xR ρL ρR P 𝓕 W VL VR B ζ)
  (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
  (hgood : ∀ ω ∈ G, IsGoodUp κ (upWordXL pL) xR ρL ρR W VL VR B ζ ω)
  (h0 : stripInit (upWordXL pL) xR ∈ upRegion κ (upWordXL pL) xR ρL ρR) (hκ : 0 < κ)

include hgood in
theorem exists_lt_upRho {ω : Ω} (hω : ω ∈ G) (x : ℝ≥0) :
    ∃ n, x < upRho pL xR G W VL VR B ζ n ω := by
  have hg := hgood ω hω
  obtain ⟨S, hS, hxS⟩ := hg.2.2.2 ((x : ℝ) + 1)
  obtain ⟨n, hn⟩ := exists_le_upLoc hgood (upWordXL_succ_lt pL) hω hS
  refine ⟨n, ?_⟩
  have hle := (clk_le_clk_iff_up (vL := fun i t => VL i t ω) (w := (W · ω)) hg.1 (upWordXL_zero pL) hS
    (isStripLife_upLoc hg hω (n := n))).2 hn
  simp only [upRho, upCoordS, hω, ↓reduceIte, upCoordAt]
  rw [Real.lt_toNNReal_iff_coe_lt]
  have : (x : ℝ) + 1 ≤ clk (W · ω) (VL 0 · ω) (upLoc G W VL VR B ζ n ω) := hxS.trans hle
  simp only [clk] at this
  linarith

theorem upRho_of_not_mem {ω : Ω} (hω : ω ∉ G) (n : ℕ) : upRho pL xR G W VL VR B ζ n ω = 0 := by
  simp only [upRho, upCoordS, hω, ↓reduceIte, Real.toNNReal_zero]

include hE hGm hGc hgood h0 hκ in
/-- `B̃` stopped at `ρ_n` is a martingale of the strip-time filtration. -/
theorem martingale_upBM_stopped (n : ℕ) :
    Martingale (stoppedProcess (upBM κ pL xR ρL ρR G W VL VR B)
      (fun ω => (upRho pL xR G W VL VR B ζ n ω : WithTop ℝ≥0))) (upStripFilt hE hGm hGc hgood) P := by
  have hM := martingale_upObs hE hGm hGc hgood hκ.le h0 n
  have hF := (contDiffOn_upObs κ (upWordXL pL) xR ρL ρR (n := 0)).continuousOn
  obtain ⟨C, hC⟩ := exists_bound_obs_stopped hgood h0 hF n
  have hMart := martingale_comp_upChordS hE hGm hGc hgood hM (continuous_obs_stopped hgood h0 hF n) hC n
    (fun r ω => by simp only [min_min_upLoc]) (1 / Real.sqrt κ)
    (-(upObs κ (upWordXL pL) xR ρL ρR (stripInit (upWordXL pL) xR) / Real.sqrt κ))
  convert hMart using 1
  funext t ω
  rw [stoppedProcess_coe_apply, upBM_min_upRho hgood]
  simp only [upPhiS]
  ring

include hE hGm hGc hgood h0 hκ in
/-- `B̃² − t` stopped at `ρ_n` is a martingale of the strip-time filtration. -/
theorem martingale_upBM_sq_stopped (n : ℕ) :
    Martingale (stoppedProcess (fun t ω => upBM κ pL xR ρL ρR G W VL VR B t ω ^ 2 - (t : ℝ))
      (fun ω => (upRho pL xR G W VL VR B ζ n ω : WithTop ℝ≥0))) (upStripFilt hE hGm hGc hgood) P := by
  set Φ₀ := upObs κ (upWordXL pL) xR ρL ρR (stripInit (upWordXL pL) xR)
  have hM := martingale_upObs hE hGm hGc hgood hκ.le h0 n
  have hN := martingale_upObs2 hE hGm hGc hgood hκ.le h0 n
  have hF := (contDiffOn_upObs κ (upWordXL pL) xR ρL ρR (n := 0)).continuousOn
  have hF2 := (contDiffOn_upObs2 κ (upWordXL pL) xR ρL ρR (n := 0)).continuousOn
  obtain ⟨C, hC⟩ := exists_bound_obs_stopped hgood h0 hF n
  obtain ⟨C2, hC2⟩ := exists_bound_obs_stopped hgood h0 hF2 n
  have h1 := martingale_comp_upChordS hE hGm hGc hgood hM (continuous_obs_stopped hgood h0 hF n) hC n
    (fun r ω => by simp only [min_min_upLoc]) (-(2 * Φ₀) / κ) 0
  have h2 := martingale_comp_upChordS hE hGm hGc hgood hN (continuous_obs_stopped hgood h0 hF2 n) hC2 n
    (fun r ω => by simp only [min_min_upLoc]) (1 / κ) (Φ₀ ^ 2 / κ)
  convert h2.add h1 using 1
  funext t ω
  rw [stoppedProcess_coe_apply]
  simp only [Pi.add_apply]
  rw [upBM_sq_min_upRho hgood hκ]
  simp only [upPhiS]
  ring

include hgood in
theorem continuous_upBM_stopped (h0' : stripInit (upWordXL pL) xR ∈
    upRegion κ (upWordXL pL) xR ρL ρR) (n : ℕ) (ω : Ω) :
    Continuous fun t => upBM κ pL xR ρL ρR G W VL VR B (min t (upRho pL xR G W VL VR B ζ n ω)) ω := by
  have hF := (contDiffOn_upObs κ (upWordXL pL) xR ρL ρR (n := 0)).continuousOn
  have hc := (continuous_obs_stopped hgood h0' hF n ω).comp (continuous_upChordS hgood ω)
  simp_rw [upBM_min_upRho hgood]
  exact (hc.sub continuous_const).div_const _

include hgood h0 in
theorem continuous_upBM (ω : Ω) : Continuous fun t => upBM κ pL xR ρL ρR G W VL VR B t ω := by
  by_cases hω : ω ∈ G
  · refine continuous_iff_continuousAt.2 fun t₀ => ?_
    obtain ⟨n, hn⟩ := exists_lt_upRho hgood hω (t₀ + 1)
    have heq : (fun t => upBM κ pL xR ρL ρR G W VL VR B (min t (upRho pL xR G W VL VR B ζ n ω)) ω)
        =ᶠ[𝓝 t₀] fun t => upBM κ pL xR ρL ρR G W VL VR B t ω := by
      filter_upwards [Iio_mem_nhds (lt_add_one t₀)] with t ht
      rw [min_eq_left (le_of_lt ((mem_Iio.1 ht).trans hn))]
    exact ((continuous_upBM_stopped hgood h0 n ω).continuousAt).congr heq
  · have : (fun t => upBM κ pL xR ρL ρR G W VL VR B t ω) = fun _ => 0 := by
      funext t
      have hz : upChordS G W VL t ω = 0 := by simp only [upChordS, hω, ↓reduceIte]
      simp only [upBM, hz, upPhiS_zero hgood, sub_self, zero_div]
    rw [this]; exact continuous_const

include hE hGm hGc hgood h0 hκ in
theorem stronglyAdapted_upBM :
    StronglyAdapted (upStripFilt hE hGm hGc hgood) (upBM κ pL xR ρL ρR G W VL VR B) := by
  intro t
  have hmeas : ∀ n : ℕ, Measurable[upStripFilt hE hGm hGc hgood t] fun ω =>
      upBM κ pL xR ρL ρR G W VL VR B (min t (upRho pL xR G W VL VR B ζ n ω)) ω := fun n => by
    have := ((martingale_upBM_stopped hE hGm hGc hgood h0 hκ n).stronglyAdapted t).measurable
    have e : stoppedProcess (upBM κ pL xR ρL ρR G W VL VR B)
        (fun ω => (upRho pL xR G W VL VR B ζ n ω : WithTop ℝ≥0)) t = fun ω =>
        upBM κ pL xR ρL ρR G W VL VR B (min t (upRho pL xR G W VL VR B ζ n ω)) ω :=
      funext fun ω => stoppedProcess_coe_apply _ _ t ω
    rw [e] at this
    exact this
  refine (@measurable_of_tendsto_metrizable Ω ℝ (upStripFilt hE hGm hGc hgood t) _ _ _ _ _ _ hmeas
    (tendsto_pi_nhds.2 fun ω => ?_)).stronglyMeasurable
  refine tendsto_const_nhds.congr' ?_
  by_cases hω : ω ∈ G
  · obtain ⟨n, hn⟩ := exists_lt_upRho hgood hω t
    have hmono : Monotone fun n => upRho pL xR G W VL VR B ζ n ω := fun m k hmk => by
      have := (isLocalizingSequence_upRho hE hGm hGc hgood).mono
      have hg := hgood ω hω
      simp only [upRho, upCoordS, hω, ↓reduceIte, upCoordAt]
      exact Real.toNNReal_le_toNNReal ((clk_le_clk_iff_up (vL := fun i t => VL i t ω) (w := (W · ω)) hg.1 (upWordXL_zero pL)
        (isStripLife_upLoc hg hω (n := m)) (isStripLife_upLoc hg hω (n := k))).2
        (upLoc_mono hgood ω hmk))
    filter_upwards [eventually_ge_atTop n] with k hk
    rw [min_eq_left (hn.trans_le (hmono hk)).le]
  · refine Eventually.of_forall fun k => ?_
    show upBM κ pL xR ρL ρR G W VL VR B t ω =
      upBM κ pL xR ρL ρR G W VL VR B (min t (upRho pL xR G W VL VR B ζ k ω)) ω
    rw [upRho_of_not_mem hω, min_zero]
    have hz : ∀ u, upChordS G W VL u ω = 0 := fun u => by simp only [upChordS, hω, ↓reduceIte]
    simp only [upBM, hz]

include hE hGm hGc hgood h0 hκ in
/-- **The strip driver's martingale part is `√κ` times a Brownian motion in the strip clock**:
`B̃_t = (Φ_{s(t)} − Φ_0)/√κ` is a Brownian motion of the strip-time filtration `𝓗_t = 𝓖_{s(t)}`. -/
theorem isFilteredBrownianReal_upBM :
    IsFilteredBrownianReal (upStripFilt hE hGm hGc hgood) (upBM κ pL xR ρL ρR G W VL VR B) P := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hB0 : ∀ ω, upBM κ pL xR ρL ρR G W VL VR B 0 ω = 0 := upBM_zero hgood
  have hBc := continuous_upBM hgood h0
  have hBa := stronglyAdapted_upBM hE hGm hGc hgood h0 hκ
  have hloc := isLocalizingSequence_upRho hE hGm hGc hgood
  have hBloc : IsLocalMartingale (upBM κ pL xR ρL ρR G W VL VR B) (upStripFilt hE hGm hGc hgood) P := by
    refine ⟨_, hloc, fun n => ?_⟩
    rw [Sec2.TwoSeed.stoppedProcess_indicator_eq' hB0]
    refine ⟨martingale_upBM_stopped hE hGm hGc hgood h0 hκ n, fun ω => ?_⟩
    have e : (fun t => stoppedProcess (upBM κ pL xR ρL ρR G W VL VR B)
        (fun ω => (upRho pL xR G W VL VR B ζ n ω : WithTop ℝ≥0)) t ω) =
        fun t => upBM κ pL xR ρL ρR G W VL VR B (min t (upRho pL xR G W VL VR B ζ n ω)) ω :=
      funext fun t => stoppedProcess_coe_apply _ _ t ω
    rw [e]
    exact (continuous_upBM_stopped hgood h0 n ω).isCadlag
  have hB2loc : IsLocalMartingale (fun t ω => upBM κ pL xR ρL ρR G W VL VR B t ω ^ 2 - (t : ℝ))
      (upStripFilt hE hGm hGc hgood) P := by
    refine ⟨_, hloc, fun n => ?_⟩
    rw [Sec2.TwoSeed.stoppedProcess_indicator_eq' (X := fun t ω =>
      upBM κ pL xR ρL ρR G W VL VR B t ω ^ 2 - (t : ℝ)) (fun ω => by simp [hB0])]
    refine ⟨martingale_upBM_sq_stopped hE hGm hGc hgood h0 hκ n, fun ω => ?_⟩
    have e : (fun t => stoppedProcess (fun t ω => upBM κ pL xR ρL ρR G W VL VR B t ω ^ 2 - (t : ℝ))
        (fun ω => (upRho pL xR G W VL VR B ζ n ω : WithTop ℝ≥0)) t ω) =
        fun t => upBM κ pL xR ρL ρR G W VL VR B (min t (upRho pL xR G W VL VR B ζ n ω)) ω ^ 2 -
          ((min t (upRho pL xR G W VL VR B ζ n ω) : ℝ≥0) : ℝ) :=
      funext fun t => stoppedProcess_coe_apply _ _ t ω
    rw [e]
    exact (((continuous_upBM_stopped hgood h0 n ω).pow 2).sub
      (NNReal.continuous_coe.comp (continuous_id.min continuous_const))).isCadlag
  have hpre := MathFin.LevyCharacterization.isFilteredPreBrownian_of_localMartingale hBa hBc hB0
    hBloc hB2loc
  have hbm := MathFin.LevyCharacterization.isBrownianReal_of_localMartingale hBa hBc hB0
    hBloc hB2loc
  exact ⟨hbm, hBa.adapted, fun s t hst => hpre.indep s t hst⟩

end Main

end InteractingSLE.ZhanGT4.UpMark
