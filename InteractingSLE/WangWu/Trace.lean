/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Defs
import InteractingSLE.WangWu.TraceGlue
import InteractingSLE.Spec.Dimension.FiniteGirsanov
import InteractingSLE.Spec.Sec4.RepulsionNoncollision
import InteractingSLE.WangWu.ContinuityInputs

/-!
# Wang–Wu Lemma 4.12: the trace of the κ = 4 force-point chain with nonnegative cumulative weights

Packet PROVE-WW-TRACE. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), §4.4,
Lemma 4.12 (text dump L1319–L1381):

> **Lemma 4.12** (Trace construction for nonnegative cumulative weights). Suppose every left and right cumulative
> force weight is nonnegative. Then the force-point chain has a simple continuous trace `γ : [0, ∞) → H`, with
> `γ(0) = 0` and `γ(t) ∈ H` for `t > 0`. This statement does not yet assert transience.

The chain is the frozen integrated evolution at `κ = 4` (`WangWu.IsMarkedChain`, Definition 1.3). The marks are
indexed from the driver outward (`vL 0` is the nearest left mark, `vR 0` the nearest right one), so the cumulative
weights are `ρ̄_{j,q} = ∑_{i ≤ j} ρ_{i,q}` (Definition 1.2).

The proof follows the source's three steps.

1. **Noncollision at positive times; infinite lifetime.** With nonnegative cumulative weights every amalgamated side
   prefix sum is `≥ 0 = κ/2 − 2` (`HasNonnegCumWeights.hasAdmissiblePartialSums`), so Aux. lemma 6 of the
   specification (`Sec4.aux6Statement`, landed: the Bessel comparison of each nearest gap after the Abel summation of
   the same-side drift, which is the source's argument) gives `ζ = ∞` and every force point strictly separated from
   the driver at every positive time.
2. **Local SLE₄ after each positive rational time.** For a rational `s > 0`, a horizon `m` and a gap level `1/(n+1)`,
   the bounded-drift Girsanov comparison after `s` (`Dimension.exists_brownian_localization`, landed) gives a path `X`
   whose law is absolutely continuous with respect to a Brownian law and `W_{s+t} − W_s = 2 X_t` while all gaps stay
   `≥ 1/(n+1)` on `[s, s + t]`, `t ≤ m`. Ordinary SLE₄ driven by `2X` is almost surely a simple radial chain
   (QuantumZipper: radial limits, continuity, simplicity, `K_t = γ((0, t])`), so the mapped-out future after `s` is a
   simple radial chain on `[0, m]` (`IsMarkedChain.ae_shift_isSimpleRadialChainOn`). By step 1 and compactness every
   `[s, s + m]` has a positive minimal gap, so the mapped-out future is a simple radial chain on `[0, ∞)`.
3. **Pullback and gluing** (`TraceGlue.exists_isGeneratingTrace_of_shift`): `γ(t) = g_s⁻¹`-pullback of the future
   trace, continuity at `0` from the shrinking initial hulls, injectivity and `K_t = γ((0, t])`.

## Main results

* `HasNonnegCumWeights`: the hypothesis of Lemma 4.12.
* `IsMarkedChain.ae_simple_trace` (**Lemma 4.12**): almost surely `ζ = ∞`, every force point is strictly separated
  from the driver at every positive time, and there is a generating trace `η` on `[0, ∞]` (frozen `IsGeneratingTrace`:
  `η 0 = 0`, continuous, `K_t` is the filling of `η([0, t])`) which is injective, lies in `ℍ` at positive times, and
  whose hulls are `K_t = η((0, t])`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu

open QuantumZipper QuantumZipper.RS TraceGlue

variable {nL nR : ℕ}

/-! ### The hypothesis: nonnegative cumulative weights -/

/-- **Nonnegative cumulative weights** (hypothesis of Lemma 4.12; Definition 1.2: `ρ̄_{j,q} = ∑_{i ≤ j} ρ_{i,q}`).
The marks are indexed from the driver outward, as in the frozen force word (`xL` antitone, `xR` monotone). -/
def HasNonnegCumWeights (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Prop :=
  (∀ j : Fin nL, 0 ≤ ∑ i ∈ Finset.Iic j, ρL i) ∧ ∀ j : Fin nR, 0 ≤ ∑ i ∈ Finset.Iic j, ρR i

/-- A nonempty set of indices that is closed downward is an initial segment `Iic`. -/
theorem eq_Iic_max'_of_le_mem {n : ℕ} {S : Finset (Fin n)} (hS : S.Nonempty)
    (hdown : ∀ i ∈ S, ∀ j ≤ i, j ∈ S) : S = Finset.Iic (S.max' hS) := by
  ext j
  rw [Finset.mem_Iic]
  exact ⟨fun hj => S.le_max' j hj, fun hj => hdown _ (S.max'_mem hS) j hj⟩

/-- Nonnegative cumulative weights give the admissible partial sums of Aux. lemma 6 at `κ = 4` (`c = κ/2 − 2 = 0`):
every side prefix of an ordered word is an initial segment of indices. -/
theorem HasNonnegCumWeights.hasAdmissiblePartialSums {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR)
    (h : HasNonnegCumWeights ρL ρR) : Sec4.HasAdmissiblePartialSums 4 ρL ρR xL xR := by
  obtain ⟨hxL, -, hxR, -⟩ := hF
  have h42 : (4 : ℝ) / 2 - 2 = 0 := by norm_num
  refine ⟨fun x _ hex => ?_, fun x _ hex => ?_⟩
  · rw [h42]
    have hne : (Finset.univ.filter fun i => x < xL i).Nonempty := by
      obtain ⟨i, hi⟩ := hex
      exact ⟨i, by simpa using hi⟩
    have hS := eq_Iic_max'_of_le_mem hne fun i hi j hji => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact lt_of_lt_of_le hi (hxL hji)
    rw [hS]
    exact h.1 _
  · rw [h42]
    have hne : (Finset.univ.filter fun i => xR i ≤ x).Nonempty := by
      obtain ⟨i, hi⟩ := hex
      exact ⟨i, by simpa using hi⟩
    have hS := eq_Iic_max'_of_le_mem hne fun i hi j hji => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact (hxR hji).trans hi
    rw [hS]
    exact h.2 _

/-- With nonnegative cumulative weights the seed of an ordered word is not a threshold state: the marks at `0` on
each side form an initial segment of indices, whose weight is a cumulative weight `≥ 0 > −2`. -/
theorem HasNonnegCumWeights.not_thresholdCondition_zero {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR)
    (h : HasNonnegCumWeights ρL ρR) : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR := by
  obtain ⟨hxL, hxL0, hxR, hxR0⟩ := hF
  have key : ∀ {n : ℕ} {ρ x : Fin n → ℝ}, (∀ j : Fin n, 0 ≤ ∑ i ∈ Finset.Iic j, ρ i) →
      (∀ i j, j ≤ i → x i = 0 → x j = 0) → 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => x i = 0), ρ i := by
    intro n ρ x hρ hdown
    rcases Finset.eq_empty_or_nonempty (Finset.univ.filter fun i => x i = 0) with he | hne
    · rw [he, Finset.sum_empty]
    · have hS := eq_Iic_max'_of_le_mem hne fun i hi j hji => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact hdown i j hji hi
      rw [hS]
      exact hρ _
  have hL := key h.1 fun i j hji hi => le_antisymm (hxL0 j) (hi ▸ hxL hji)
  have hR := key h.2 fun i j hji hi => le_antisymm (hi ▸ hxR hji) (hxR0 j)
  rintro (h1 | h1) <;> linarith

/-! ### Ordinary SLE₄ is a simple radial chain -/

/-- **Ordinary SLE₄** on the canonical path space is almost surely a simple radial chain (QuantumZipper: radial limits
and continuity `RS.ae_radialGood_drive`, simplicity `RS.ae_sleTrace_simple_of_le_four`, hulls
`RS.ae_fwdHull_eq_sleTrace_image_of_le_four`). -/
theorem ae_isSimpleRadialChain_drive_four {μ : Measure CPath} [IsProbabilityMeasure μ]
    (hμ : IsBrownianReal canonBM μ) :
    ∀ᵐ x ∂μ, Continuous (drive 4 canonBM x) ∧ drive 4 canonBM x 0 = 0 ∧
      IsSimpleRadialChain (drive 4 canonBM x) := by
  filter_upwards [ae_radialGood_drive hμ (κ := 4) four_pos (by norm_num),
    ae_sleTrace_simple_of_le_four hμ (κ := 4) four_pos le_rfl,
    ae_fwdHull_eq_sleTrace_image_of_le_four hμ (κ := 4) four_pos le_rfl] with x hg hs hh
  exact ⟨hg.1, hg.2.1, fun T => ⟨fun u hu => hg.tendsto hu.1, hg.2.2.2.1.mono fun u hu => hu.1,
    fun u hu => hs.2 u hu.1, fun u hu => hh u hu.1⟩⟩

/-! ### Step 2: the mapped-out future after a positive time is locally SLE₄ -/

section Chain

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The real driver of a path with infinite lifetime is continuous. -/
theorem continuous_realDriver_of_eq_top {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} (hT : T = ⊤)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T}) : Continuous fun s : ℝ => w s.toNNReal := by
  have hcw : Continuous w := continuousOn_univ.1 (hw.mono fun t _ => by
    show (t : ℝ≥0∞) < T
    rw [hT]; exact ENNReal.coe_lt_top)
  exact hcw.comp continuous_real_toNNReal

/-- **The localized comparison with SLE₄ after a time `a`** (proof of Lemma 4.12, "Fix a positive rational `s`. Stop
subsequent evolution when a gap becomes smaller than `1/n`, when a coordinate exceeds `n`, or at time `n`. … Girsanov
makes its increment law equivalent to ordinary SLE₄ in the `g_s` image domain"): almost surely, if `ζ = ∞` and all
force gaps are `≥ δ` on `[a, a + m]`, the mapped-out future `shiftDrive W a` is a simple radial chain on `[0, m]`. -/
theorem IsMarkedChain.ae_shift_isSimpleRadialChainOn [IsProbabilityMeasure P]
    (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) (a : ℝ≥0) (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ → (∀ s : ℝ≥0, a ≤ s → s ≤ a + m →
        Dimension.GapsGE δ (W s ω) (fun i => VL i s ω) (fun i => VR i s ω)) →
      IsSimpleRadialChainOn (shiftDrive (fun r : ℝ => W r.toNNReal ω) a) m := by
  obtain ⟨X, hXm, μ, hμP, hμB, hac, hloc⟩ :=
    Dimension.exists_brownian_localization four_pos hE a m hδ
  have hgood := ae_of_ae_map hXm.aemeasurable (hac.ae_le (ae_isSimpleRadialChain_drive_four hμB))
  filter_upwards [hgood, hloc, hE.2.2.2.2] with ω ⟨hVc, hV0, hV⟩ hlocω hp hζ hgap
  have hWc := continuous_realDriver_of_eq_top hζ hp.2.2.2.1
  have hW0 : (fun r : ℝ => W r.toNNReal ω) 0 = 0 := by
    simp only [Real.toNNReal_zero]; exact hp.1
  refine (hV m).congr hVc hV0 (continuous_shiftDrive hWc a) (shiftDrive_zero _ _) fun r hr => ?_
  have ht : r.toNNReal ≤ (m : ℝ≥0) := Real.toNNReal_le_iff_le_coe.2 (by exact_mod_cast hr.2)
  have h1 := hlocω r.toNNReal ht (by rw [hζ]; exact ENNReal.coe_lt_top)
    fun s hs1 hs2 => hgap s hs1 (hs2.trans (add_le_add_right ht a))
  show Real.sqrt 4 * canonBM r.toNNReal (X ω) = W ((a : ℝ) + r).toNNReal ω - W (a : ℝ).toNNReal ω
  rw [Real.toNNReal_coe, Real.toNNReal_add a.coe_nonneg hr.1, Real.toNNReal_coe, h1]
  rfl

/-- A continuous positive function on a compact interval `[a, b]` of `ℝ≥0` has a positive lower bound there. -/
theorem exists_pos_le_of_continuous_Icc {f : ℝ≥0 → ℝ} (hf : Continuous f) {a b : ℝ≥0} (hab : a ≤ b)
    (hpos : ∀ s ∈ Icc a b, 0 < f s) : ∃ ε > 0, ∀ s ∈ Icc a b, ε ≤ f s := by
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab) hf.continuousOn
  exact ⟨f s₀, hpos s₀ hs₀, fun s hs => hmin hs⟩

/-- **Positive minimal gap on compact intervals after a positive time.** If the path has infinite lifetime and every
force point is strictly separated from the driver at positive times, then on every `[a, b]`, `a > 0`, all gaps are
`≥ δ` for some `δ > 0`. -/
theorem exists_gapsGE_Icc {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b0 : ℝ≥0 → ℝ}
    {T : ℝ≥0∞} (hp : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b0 T) (hT : T = ⊤)
    (hsep : ∀ t : ℝ≥0, 0 < t → (∀ i, vL i t < w t) ∧ ∀ i, w t < vR i t) {a b : ℝ≥0} (ha : 0 < a)
    (hab : a ≤ b) : ∃ δ > 0, ∀ s : ℝ≥0, a ≤ s → s ≤ b → Dimension.GapsGE δ (w s) (fun i => vL i s)
      (fun i => vR i s) := by
  have hcont : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < T} → Continuous f := fun hf =>
    continuousOn_univ.1 (hf.mono fun t _ => by
      show (t : ℝ≥0∞) < T
      rw [hT]; exact ENNReal.coe_lt_top)
  have hw := hcont hp.2.2.2.1
  have hL : ∀ i, ∃ ε > 0, ∀ s ∈ Icc a b, ε ≤ |w s - vL i s| := fun i =>
    exists_pos_le_of_continuous_Icc (hw.sub (hcont (hp.2.2.2.2.1 i))).abs hab fun s hs =>
      abs_pos.2 (sub_ne_zero.2 ((hsep s (ha.trans_le hs.1)).1 i).ne')
  have hR : ∀ i, ∃ ε > 0, ∀ s ∈ Icc a b, ε ≤ |w s - vR i s| := fun i =>
    exists_pos_le_of_continuous_Icc (hw.sub (hcont (hp.2.2.2.2.2.1 i))).abs hab fun s hs =>
      abs_pos.2 (sub_ne_zero.2 ((hsep s (ha.trans_le hs.1)).2 i).ne)
  choose εL hεL hεLle using hL
  choose εR hεR hεRle using hR
  obtain ⟨δL, hδL, hδLle⟩ := exists_pos_le_of_pos εL
  obtain ⟨δR, hδR, hδRle⟩ := exists_pos_le_of_pos εR
  refine ⟨min δL δR, lt_min hδL hδR, fun s hs1 hs2 => ⟨fun i => ?_, fun i => ?_⟩⟩
  · exact (min_le_left _ _).trans ((hδLle i (hεL i)).trans (hεLle i s ⟨hs1, hs2⟩))
  · exact (min_le_right _ _).trans ((hδRle i (hεR i)).trans (hεRle i s ⟨hs1, hs2⟩))

/-! ### Lemma 4.12 -/

/-- **Wang–Wu Lemma 4.12** (trace construction for nonnegative cumulative weights). For the κ = 4 force-point chain
(`IsMarkedChain`, the frozen integrated evolution at `κ = 4`) of an ordered force word whose left and right cumulative
weights are all nonnegative, almost surely:

* the lifetime is infinite (no continuation threshold occurs);
* every force point is strictly separated from the driver at every positive time;
* there is a simple continuous trace: `η : ℝ≥0 → ℂ` is a generating trace of the chain on `[0, ∞]` (the frozen
  `IsGeneratingTrace`: `η 0 = 0`, `η` continuous, `K_t` the filling of `η([0, t])`), `η` is injective, `η t ∈ ℍ` for
  `t > 0`, and every hull is the trace initial segment `K_t = η((0, t])`.

Transience is not asserted (Corollary 4.13). -/
theorem IsMarkedChain.ae_simple_trace (hF : IsOrderedForceWord xL xR)
    (hcum : HasNonnegCumWeights ρL ρR) (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t : ℝ≥0, 0 < t → (∀ i, VL i t ω < W t ω) ∧ ∀ i, W t ω < VR i t ω) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧ Function.Injective η ∧
        (∀ t, 0 < t → η t ∈ H) ∧
        ∀ t : ℝ≥0, fwdHull (fun s : ℝ => W s.toNNReal ω) t = η '' Ioc 0 t := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have h6 := Sec4.aux6Statement (k := 4) four_pos xL xR ρL ρR P 𝓕 W VL VR B ζ hF
    (hcum.hasAdmissiblePartialSums hF) hE
  have hloc : ∀ᵐ ω ∂P, ∀ q : ℚ, ∀ m n : ℕ, ζ ω = ⊤ → (∀ s : ℝ≥0, (q : ℝ).toNNReal ≤ s →
      s ≤ (q : ℝ).toNNReal + m →
        Dimension.GapsGE (1 / ((n : ℝ) + 1)) (W s ω) (fun i => VL i s ω) (fun i => VR i s ω)) →
      IsSimpleRadialChainOn (shiftDrive (fun r : ℝ => W r.toNNReal ω) ((q : ℝ).toNNReal : ℝ)) m := by
    rw [ae_all_iff]; intro q
    rw [ae_all_iff]; intro m
    rw [ae_all_iff]; intro n
    exact hE.ae_shift_isSimpleRadialChainOn _ m (by positivity)
  filter_upwards [h6, hloc, hE.2.2.2.2] with ω ⟨hζ, hsep⟩ hlω hp
  refine ⟨hζ, hsep, ?_⟩
  have hWc := continuous_realDriver_of_eq_top hζ hp.2.2.2.1
  refine exists_isGeneratingTrace_of_shift hWc hp.1 (D := range ((↑) : ℚ → ℝ))
    Rat.denseRange_cast ?_
  rintro _ ⟨q, rfl⟩ hq T
  obtain ⟨m, hm⟩ := exists_nat_ge T
  have ha : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq.le
  have ha0 : 0 < (q : ℝ).toNNReal := Real.toNNReal_pos.2 hq
  obtain ⟨δ, hδ, hgapδ⟩ := exists_gapsGE_Icc hp hζ hsep ha0 (le_self_add (b := (m : ℝ≥0)))
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  have h := hlω q m n hζ fun s h1 h2 =>
    ⟨fun i => hn.le.trans ((hgapδ s h1 h2).1 i), fun i => hn.le.trans ((hgapδ s h1 h2).2 i)⟩
  rw [ha] at h
  exact h.mono hm

/-- **Lemma 4.12 in the form of the frozen Theorem 1.3** (without transience): almost surely the seed is not a
threshold state (so the threshold clause of Theorem 1.3 holds vacuously) and the chain has a generating trace on
`[0, ζ]`, `ζ = ∞`. -/
theorem IsMarkedChain.ae_isGeneratingTrace_lifetime (hF : IsOrderedForceWord xL xR)
    (hcum : HasNonnegCumWeights ρL ρR) (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η := by
  filter_upwards [hE.ae_simple_trace hF hcum] with ω ⟨hζ, _, η, hη, _⟩
  exact ⟨fun hth => absurd hth (hcum.not_thresholdCondition_zero hF), η, hζ ▸ hη⟩

end Chain

/-! ### Corollary 4.13 for force points separated from the start -/

section Separated

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

theorem filter_le_eq_Iic {n : ℕ} (k : Fin n) :
    Finset.univ.filter (fun i => i ≤ k) = Finset.Iic k := by
  ext i; simp

/-- **Corollary 4.13 when every force point is strictly separated from the start** (the case in which External input
8.3 applies without a restart): under the hypotheses of Lemma 4.12 and with `xL i < 0 < xR j`, given Zhan's
nonboundary transience (`ZhanNonboundaryTransience`, the named External input 8.3 of PROVE-WW-C), almost surely the
simple trace of Lemma 4.12 also satisfies `γ(t) → ∞`. The general case (marks at `0±`) restarts the chain at a positive
rational time, which needs the restart of the evolution in kernel form (input 8.1); see the handoff. -/
theorem IsMarkedChain.ae_simple_trace_tendsto_of_separated (hZ : ZhanNonboundaryTransience.{u})
    (hF : IsOrderedForceWord xL xR) (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j)
    (hcum : HasNonnegCumWeights ρL ρR) (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t : ℝ≥0, 0 < t → (∀ i, VL i t ω < W t ω) ∧ ∀ i, W t ω < VR i t ω) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧ Function.Injective η ∧
        (∀ t, 0 < t → η t ∈ H) ∧
        (∀ t : ℝ≥0, fwdHull (fun s : ℝ => W s.toNNReal ω) t = η '' Ioc 0 t) ∧
        Tendsto (fun t => ‖η t‖) atTop atTop := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hZω := hZ xL xR ρL ρR hF hxL hxR (fun k => by rw [filter_le_eq_Iic]; exact hcum.1 k)
    (fun k => by rw [filter_le_eq_Iic]; exact hcum.2 k) P 𝓕 W VL VR B ζ hE
  filter_upwards [hE.ae_simple_trace hF hcum, hZω] with ω ⟨hζ, hsep, η, hη, hinj, hH, hhull⟩ hZ'
  refine ⟨hζ, hsep, η, hη, hinj, hH, hhull, hZ' hζ η ?_⟩
  rw [hζ]; exact hη

/-- **The conclusion of the frozen Theorem 1.3 at `κ = 4`** for an ordered word whose force points are all strictly
separated from the start and whose cumulative weights are nonnegative, given Zhan's transience input
(`ZhanNonboundaryTransience`). This is exactly the body of `IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace`
at `a = 4` for these words. -/
theorem IsMarkedChain.ae_theorem13_of_separated (hZ : ZhanNonboundaryTransience.{u})
    (hF : IsOrderedForceWord xL xR) (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j)
    (hcum : HasNonnegCumWeights ρL ρR) (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) := by
  filter_upwards [hE.ae_simple_trace_tendsto_of_separated hZ hF hxL hxR hcum] with ω
    ⟨hζ, _, η, hη, _, _, _, htend⟩
  exact ⟨fun hth => absurd hth (hcum.not_thresholdCondition_zero hF), η, hζ ▸ hη, fun _ => htend⟩

end Separated

end InteractingSLE.WangWu
