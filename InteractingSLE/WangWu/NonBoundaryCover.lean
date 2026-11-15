/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.NonBoundaryReconstruct
import InteractingSLE.WangWu.Trace
import InteractingSLE.Spec.Dimension.Transfer
import InteractingSLE.Spec.Supplement.LPTrace
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Covering numbers of non-boundary-intersecting traces (Wang–Wu Lemma 4.14, first part)

Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), §4.4, proof of Lemma 4.14 (text dump
lines 1399–1421): "For ordinary `SLE₄`, the expected covering-number bound of Rohde–Schramm … Borel–Cantelli and
comparison of disks with squares yield `N_n 2^{-2n} n → 0` almost surely. Local absolute continuity transfers this
property to each non-boundary-intersecting trace on compact subsets. For this transfer, stop first at a positive time
before entering the compact set, and localize the later force-image gaps away from zero. The initial conformal map is
smooth and bi-Lipschitz on a neighborhood of that compact set. … Stopping a trace only decreases its covering numbers.
A finite union preserves the resulting bound."

The ordinary `SLE₄` box-counting bound is Aux. lemma 14 (`Dimension.ae_trace_good_of_absolutelyContinuous`, with
`d₄ = interiorDimBound 4 = 7/4 < 2`). The transfer uses the localized Girsanov comparison
(`Dimension.exists_brownian_localization`) after one positive time `a` before the trace can reach the compact set `K`
(the trace starts at `0 ∉ K`), the tip identity `γ(t) = F_a(γ^a(t − a))` (`TraceGlue.tendsto_trace_of_shift`), and
the fact that a holomorphic map multiplies box counts on a compact set by a constant (`exists_dyadicCount_image_le`).
Since every gap is positive at every positive time (Lemma 4.12), one localization covers a whole compact time
interval `[a, a + m]`; no finite subcover is needed.

## Main results

* `exists_dyadicCount_image_le`: `N_n(F(E)) ≤ C N_n(E)` for large `n`, `F` holomorphic near the compact `E`;
* `IsMarkedChain.ae_localized_dyadicCount`: the localized future is a simple radial chain whose trace has the
  ordinary `SLE₄` box-counting bound;
* **`IsMarkedChain.ae_eventually_dyadicCount_trace_le`**: for nonnegative cumulative weights, almost surely every
  generating trace `η` has, for every `T` and compact `K ⊆ ℍ` and every `d > 7/4`,
  `N_n(η([0, T]) ∩ K) ≤ (2ⁿ)^d` for all large `n`;
* `hasThinCovering_of_eventually_le`: such bounds for finitely many sets give the covering hypothesis (R1.1) of
  `aeDeterminedSigma_offSigma` for their union.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Real

namespace InteractingSLE.WangWu

open Dimension

/-! ### Box counts under holomorphic maps -/

/-- The offsets `[−c, c]²`. -/
def offBox (c : ℕ) : Finset (ℤ × ℤ) := pouIdx c

/-- If two reals are within `D` after scaling, the floor of the second is within `⌈D⌉₊ + 2` of an integer `k`
with `k ≤ x ≤ k + 1`. -/
lemma sub_floor_mem_Icc_of_le {x y D : ℝ} {k : ℤ} (hk1 : (k : ℝ) ≤ x) (hk2 : x ≤ k + 1)
    (hxy : |x - y| ≤ D) : k - ⌊y⌋ ∈ Finset.Icc (-((⌈D⌉₊ + 2 : ℕ) : ℤ)) ((⌈D⌉₊ + 2 : ℕ) : ℤ) := by
  have h1 := Int.floor_le y
  have h2 := Int.lt_floor_add_one y
  have h3 := abs_le.1 hxy
  have hD : D ≤ ⌈D⌉₊ := Nat.le_ceil D
  rw [Finset.mem_Icc]
  push_cast
  constructor
  · have : ((⌊y⌋ : ℤ) : ℝ) - (⌈D⌉₊ + 2) < k := by linarith
    have : (⌊y⌋ : ℤ) - ((⌈D⌉₊ : ℕ) + 2 : ℤ) < k := by exact_mod_cast this
    omega
  · have : (k : ℝ) < ⌊y⌋ + (⌈D⌉₊ + 2) := by linarith
    have : k < (⌊y⌋ : ℤ) + ((⌈D⌉₊ : ℕ) + 2 : ℤ) := by exact_mod_cast this
    omega

/-- **Box counts under a holomorphic map.** If `F` is holomorphic on an open set containing the compact set `E`,
then `N_n(F(E)) ≤ C N_n(E)` for all large `n` ("the initial conformal map is smooth and bi-Lipschitz on a
neighborhood of that compact set"). -/
theorem exists_dyadicCount_image_le {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {E : Set ℂ} (hE : IsCompact E) (hEU : E ⊆ U) :
    ∃ C : ℕ, ∀ᶠ n in atTop, dyadicCount n (F '' E) ≤ C * dyadicCount n E := by
  classical
  obtain ⟨δ, hδ, hδU⟩ := hE.exists_cthickening_subset_open hU hEU
  have hQ : IsCompact (cthickening δ E) := hE.cthickening
  obtain ⟨L₀, hL₀⟩ := hQ.exists_bound_of_continuousOn ((hF.deriv hU).continuousOn.mono hδU)
  set L := max L₀ 0 with hLdef
  have hL : ∀ z ∈ cthickening δ E, ‖deriv F z‖ ≤ L := fun z hz => (hL₀ z hz).trans (le_max_left _ _)
  have hL0 : 0 ≤ L := le_max_right _ _
  set c : ℕ := ⌈2 * L⌉₊ + 2 with hc
  refine ⟨(offBox c).card, ?_⟩
  have hsmall : ∀ᶠ n : ℕ in atTop, (2 : ℝ) / 2 ^ n ≤ δ := by
    have ht : Tendsto (fun n : ℕ => (2 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).const_mul 2
    exact ht.eventually (ge_mem_nhds hδ)
  filter_upwards [hsmall] with n hn
  have h2n : (0 : ℝ) < 2 ^ n := pow_pos two_pos n
  have hEfin : (dyadicHits n E).Finite := dyadicHits_finite hE.isBounded
  have hFEc : IsCompact (F '' E) := hE.image_of_continuousOn (hF.continuousOn.mono hEU)
  have hFfin : (dyadicHits n (F '' E)).Finite := dyadicHits_finite hFEc.isBounded
  -- a chosen point of each hit square and the index of its image
  let pt : ℤ × ℤ → ℂ := fun j => if hj : (dyadicSquare n j ∩ E).Nonempty then hj.some else 0
  have hpt : ∀ j ∈ dyadicHits n E, pt j ∈ dyadicSquare n j ∩ E := fun j hj => by
    have hj' : (dyadicSquare n j ∩ E).Nonempty := hj
    simp only [pt, hj', ↓reduceDIte]
    exact hj'.some_mem
  let κ : ℤ × ℤ → ℤ × ℤ := fun j => (⌊(F (pt j)).re * 2 ^ n⌋, ⌊(F (pt j)).im * 2 ^ n⌋)
  have hsub : dyadicHits n (F '' E) ⊆
      ((hEfin.toFinset ×ˢ offBox c).image fun p => κ p.1 + p.2 : Finset (ℤ × ℤ)) := by
    rintro k ⟨y, hyk, x, hxE, rfl⟩
    set j : ℤ × ℤ := (⌊x.re * 2 ^ n⌋, ⌊x.im * 2 ^ n⌋) with hj
    have hjE : j ∈ dyadicHits n E := ⟨x, mem_dyadicSquare_floor n x, hxE⟩
    obtain ⟨hpS, hpE⟩ := hpt j hjE
    have hdist : dist x (pt j) ≤ 2 / 2 ^ n := dist_le_of_mem_dyadicSquare (mem_dyadicSquare_floor n x) hpS
    have hball : closedBall (pt j) (2 / 2 ^ n) ⊆ cthickening δ E :=
      (closedBall_subset_closedBall hn).trans (closedBall_subset_cthickening hpE δ)
    have hlip : ‖F x - F (pt j)‖ ≤ L * ‖x - pt j‖ :=
      (convex_closedBall (pt j) (2 / 2 ^ n)).norm_image_sub_le_of_norm_deriv_le
        (fun z hz => (hF z (hδU (hball hz))).differentiableAt (hU.mem_nhds (hδU (hball hz))))
        (fun z hz => hL z (hball hz)) (mem_closedBall_self (by positivity))
        (by rw [mem_closedBall]; exact hdist)
    have hF2 : ‖F x - F (pt j)‖ * 2 ^ n ≤ 2 * L := by
      calc ‖F x - F (pt j)‖ * 2 ^ n ≤ L * ‖x - pt j‖ * 2 ^ n :=
            mul_le_mul_of_nonneg_right hlip h2n.le
        _ ≤ L * (2 / 2 ^ n) * 2 ^ n := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hL0) h2n.le
            rw [← dist_eq_norm]; exact hdist
        _ = 2 * L := by field_simp
    have hre : |(F x).re * 2 ^ n - (F (pt j)).re * 2 ^ n| ≤ 2 * L := by
      rw [← sub_mul, abs_mul, abs_of_pos h2n, ← Complex.sub_re]
      exact (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) h2n.le).trans hF2
    have him : |(F x).im * 2 ^ n - (F (pt j)).im * 2 ^ n| ≤ 2 * L := by
      rw [← sub_mul, abs_mul, abs_of_pos h2n, ← Complex.sub_im]
      exact (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm _) h2n.le).trans hF2
    obtain ⟨hk1, hk2, hk3, hk4⟩ := hyk
    rw [div_le_iff₀ h2n] at hk1 hk3
    rw [le_div_iff₀ h2n] at hk2 hk4
    rw [Finset.mem_coe, Finset.mem_image]
    refine ⟨(j, k - κ j), Finset.mem_product.2 ⟨(Set.Finite.mem_toFinset _).2 hjE, ?_⟩, by simp⟩
    exact Finset.mem_product.2 ⟨sub_floor_mem_Icc_of_le hk1 hk2 hre,
      sub_floor_mem_Icc_of_le hk3 hk4 him⟩
  calc dyadicCount n (F '' E) = hFfin.toFinset.card := Set.ncard_eq_toFinset_card _ hFfin
    _ ≤ ((hEfin.toFinset ×ˢ offBox c).image fun p => κ p.1 + p.2).card :=
        Finset.card_le_card (fun k hk => hsub ((Set.Finite.mem_toFinset _).1 hk))
    _ ≤ (hEfin.toFinset ×ˢ offBox c).card := Finset.card_image_le
    _ = (offBox c).card * dyadicCount n E := by
        rw [Finset.card_product, mul_comm, dyadicCount, Set.ncard_eq_toFinset_card _ hEfin]

/-- `C (2ⁿ)^d ≤ (2ⁿ)^{d'}` for all large `n` when `d < d'`. -/
lemma eventually_mul_rpow_le {d d' : ℝ} (h : d < d') (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, C * ((2 : ℝ) ^ n) ^ d ≤ ((2 : ℝ) ^ n) ^ d' := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hq : (1 : ℝ) < 2 ^ (d' - d) := Real.one_lt_rpow (by norm_num) (sub_pos.2 h)
  have ht := tendsto_pow_atTop_atTop_of_one_lt hq
  filter_upwards [ht.eventually_ge_atTop C] with n hn
  have e1 : ((2 : ℝ) ^ n) ^ d' = (2 : ℝ) ^ ((n : ℝ) * d') := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h2]
  have e2 : ((2 : ℝ) ^ n) ^ d = (2 : ℝ) ^ ((n : ℝ) * d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h2]
  have e3 : ((2 : ℝ) ^ (d' - d)) ^ n = (2 : ℝ) ^ ((d' - d) * n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h2]
  have e : ((2 : ℝ) ^ n) ^ d' = ((2 : ℝ) ^ (d' - d)) ^ n * ((2 : ℝ) ^ n) ^ d := by
    rw [e1, e2, e3, ← Real.rpow_add two_pos]
    congr 1; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right hn (by positivity)

/-- **Growth bounds under a holomorphic map.** -/
theorem eventually_dyadicCount_image_le {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {E : Set ℂ} (hE : IsCompact E) (hEU : E ⊆ U) {d d' : ℝ}
    (hdd : d < d') (h : ∀ᶠ n in atTop, (dyadicCount n E : ℝ) ≤ ((2 : ℝ) ^ n) ^ d) :
    ∀ᶠ n in atTop, (dyadicCount n (F '' E) : ℝ) ≤ ((2 : ℝ) ^ n) ^ d' := by
  obtain ⟨C, hC⟩ := exists_dyadicCount_image_le hU hF hE hEU
  filter_upwards [hC, h, eventually_mul_rpow_le hdd C] with n h1 h2 h3
  calc (dyadicCount n (F '' E) : ℝ) ≤ C * dyadicCount n E := by exact_mod_cast h1
    _ ≤ C * ((2 : ℝ) ^ n) ^ d := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg C)
    _ ≤ _ := h3

/-! ### The localized future has the ordinary `SLE₄` box-counting bound -/

section Chain

open QuantumZipper QuantumZipper.RS TraceGlue

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The localized comparison with ordinary `SLE₄`, with box counts** (proof of Lemma 4.14: "Local absolute
continuity transfers this property to each non-boundary-intersecting trace on compact subsets"). Almost surely, if
`ζ = ∞` and all force gaps are `≥ δ` on `[a, a + m]`, the mapped-out future `shiftDrive W a` is a simple radial
chain on `[0, m]` whose trace on `[0, m]` meets, for every compact `K ⊆ ℍ` and all large `n`, at most
`(2ⁿ)^{7/4}` dyadic squares of side `2^{-n}` inside `K`. -/
theorem IsMarkedChain.ae_localized_dyadicCount [IsProbabilityMeasure P]
    (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) (a : ℝ≥0) (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ → (∀ s : ℝ≥0, a ≤ s → s ≤ a + m →
        Dimension.GapsGE δ (W s ω) (fun i => VL i s ω) (fun i => VR i s ω)) →
      IsSimpleRadialChainOn (shiftDrive (fun r : ℝ => W r.toNNReal ω) a) m ∧
      ∀ K : Set ℂ, IsCompact K → K ⊆ H → ∀ᶠ n in atTop,
        (dyadicCount n (trace (shiftDrive (fun r : ℝ => W r.toNNReal ω) a) '' Icc 0 m ∩ K) : ℝ) ≤
          ((2 : ℝ) ^ n) ^ interiorDimBound 4 := by
  obtain ⟨X, hXm, μ, hμP, hμB, hac, hloc⟩ :=
    Dimension.exists_brownian_localization four_pos hE a m hδ
  have hgood := ae_of_ae_map hXm.aemeasurable (hac.ae_le (ae_isSimpleRadialChain_drive_four hμB))
  have hdim := Dimension.ae_trace_good_of_absolutelyContinuous four_pos (by norm_num)
    hXm.aemeasurable hμB hac
  filter_upwards [hgood, hdim, hloc, hE.2.2.2.2] with ω ⟨hVc, hV0, hV⟩ ⟨_, _, hdimω⟩ hlocω hp hζ hgap
  have hWc := continuous_realDriver_of_eq_top hζ hp.2.2.2.1
  have heq : EqOn (drive 4 canonBM (X ω)) (shiftDrive (fun r : ℝ => W r.toNNReal ω) a)
      (Icc 0 (m : ℝ)) := fun r hr => by
    have ht : r.toNNReal ≤ (m : ℝ≥0) := Real.toNNReal_le_iff_le_coe.2 (by exact_mod_cast hr.2)
    have h1 := hlocω r.toNNReal ht (by rw [hζ]; exact ENNReal.coe_lt_top)
      fun s hs1 hs2 => hgap s hs1 (hs2.trans (add_le_add_right ht a))
    show Real.sqrt 4 * canonBM r.toNNReal (X ω) = W ((a : ℝ) + r).toNNReal ω - W (a : ℝ).toNNReal ω
    rw [Real.toNNReal_coe, Real.toNNReal_add a.coe_nonneg hr.1, Real.toNNReal_coe, h1]
    rfl
  have hsc := continuous_shiftDrive hWc a
  have hs0 := shiftDrive_zero (fun r : ℝ => W r.toNNReal ω) a
  refine ⟨(hV m).congr hVc hV0 hsc hs0 heq, fun K hK hKH => ?_⟩
  -- the localized trace on `[0, m]` is part of the ordinary trace
  have hsub : trace (shiftDrive (fun r : ℝ => W r.toNNReal ω) a) '' Icc 0 m ∩ K ⊆
      trace (drive 4 canonBM (X ω)) '' Ici 0 ∩ K := by
    rintro _ ⟨⟨u, hu, rfl⟩, hK'⟩
    refine ⟨⟨u, hu.1, ?_⟩, hK'⟩
    exact trace_congr_drive hVc hV0 hsc hs0 hu.1 (heq.mono (Icc_subset_Icc_right hu.2))
  filter_upwards [hdimω.2 K hK hKH] with n ⟨hfin, hle⟩
  refine le_trans ?_ hle
  exact_mod_cast Set.ncard_le_ncard (dyadicHits_mono hsub) hfin

/-- A compact subset of `ℍ` has a positive lower bound on its imaginary parts. -/
lemma exists_pos_le_im_of_isCompact {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) :
    ∃ y₀ > 0, ∀ z ∈ K, y₀ ≤ z.im := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun z hz => hz.elim⟩
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne continuous_im.continuousOn
  exact ⟨z₀.im, hKH hz₀, fun z hz => hmin hz⟩

/-- **Covering numbers of the κ = 4 non-boundary-intersecting trace** (proof of Lemma 4.14, first part). For an
ordered force word with nonnegative cumulative weights, almost surely every generating trace `η` of the chain
satisfies, for every time `T`, every compact `K ⊆ ℍ` and every `d > 7/4` (`= interiorDimBound 4`):
`N_n(η([0, T]) ∩ K) ≤ (2ⁿ)^d` for all large `n`. -/
theorem IsMarkedChain.ae_eventually_dyadicCount_trace_le (hF : IsOrderedForceWord xL xR)
    (hcum : HasNonnegCumWeights ρL ρR) (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → ∀ T : ℝ≥0,
      ∀ K : Set ℂ, IsCompact K → K ⊆ H → ∀ d : ℝ, interiorDimBound 4 < d →
        ∀ᶠ n in atTop, (dyadicCount n (η '' Icc 0 T ∩ K) : ℝ) ≤ ((2 : ℝ) ^ n) ^ d := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hloc : ∀ᵐ ω ∂P, ∀ q : ℚ, ∀ m j : ℕ, ζ ω = ⊤ → (∀ s : ℝ≥0, (q : ℝ).toNNReal ≤ s →
      s ≤ (q : ℝ).toNNReal + m →
        Dimension.GapsGE (1 / ((j : ℝ) + 1)) (W s ω) (fun i => VL i s ω) (fun i => VR i s ω)) →
      IsSimpleRadialChainOn (shiftDrive (fun r : ℝ => W r.toNNReal ω) ((q : ℝ).toNNReal : ℝ)) m ∧
      ∀ K : Set ℂ, IsCompact K → K ⊆ H → ∀ᶠ n in atTop,
        (dyadicCount n (trace (shiftDrive (fun r : ℝ => W r.toNNReal ω) ((q : ℝ).toNNReal : ℝ)) ''
          Icc 0 m ∩ K) : ℝ) ≤ ((2 : ℝ) ^ n) ^ interiorDimBound 4 := by
    rw [ae_all_iff]; intro q
    rw [ae_all_iff]; intro m
    rw [ae_all_iff]; intro j
    exact hE.ae_localized_dyadicCount _ m (by positivity)
  filter_upwards [hE.ae_simple_trace hF hcum, hloc, hE.2.2.2.2] with ω ⟨hζ, hsep, _⟩ hlω hp
    η hη T K hK hKH d hd
  set W' : ℝ → ℝ := fun r : ℝ => W r.toNNReal ω with hW'
  have hWc : Continuous W' := continuous_realDriver_of_eq_top hζ hp.2.2.2.1
  have hW0 : W' 0 = 0 := by simp only [hW', Real.toNNReal_zero]; exact hp.1
  have hwc : ContinuousOn (fun t => W t ω) {s : ℝ≥0 | (s : ℝ≥0∞) < ⊤} := by
    rw [← hζ]; exact hp.2.2.2.1
  have htr : ∀ t : ℝ≥0, trace W' t = η t := fun t =>
    hη.trace_eq hwc hp.1 ENNReal.coe_lt_top
  -- a positive time before which the trace stays away from `K`
  obtain ⟨y₀, hy₀, hy₀K⟩ := exists_pos_le_im_of_isCompact hK hKH
  have hηc : ContinuousAt η 0 := hη.2.1.continuousAt (by simp)
  obtain ⟨ε, hε, hεη⟩ := Metric.continuousAt_iff.1 hηc y₀ hy₀
  have hfar : ∀ t : ℝ≥0, (t : ℝ) < ε → η t ∉ K := by
    intro t ht hK'
    have h1 := hεη (show dist t 0 < ε by rw [NNReal.dist_eq]; simpa using ht)
    rw [hη.1, dist_zero_right] at h1
    have h2 := hy₀K _ hK'
    linarith [Complex.im_le_norm (η t)]
  -- one localization `[a, a + m]` with `0 < a < ε` and `T ≤ m`
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
  set a : ℝ≥0 := (q : ℝ).toNNReal with ha
  have haq : (a : ℝ) = q := Real.coe_toNNReal _ hq0.le
  have ha0 : 0 < a := Real.toNNReal_pos.2 hq0
  obtain ⟨m, hm⟩ := exists_nat_ge (T : ℝ)
  obtain ⟨δ, hδ, hgapδ⟩ := exists_gapsGE_Icc hp hζ hsep ha0 (le_self_add (b := (m : ℝ≥0)))
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
  obtain ⟨hsh, hbox⟩ := hlω q m j hζ fun s h1 h2 =>
    ⟨fun i => hj.le.trans ((hgapδ s h1 h2).1 i), fun i => hj.le.trans ((hgapδ s h1 h2).2 i)⟩
  set V : ℝ → ℝ := shiftDrive W' (a : ℝ) with hV
  -- the relevant piece of the localized trace
  have hεq : 0 < ε - q := sub_pos.2 hqε
  set E : Set ℂ := trace V '' Icc (ε - q) m with hEdef
  have hEc : IsCompact E :=
    isCompact_Icc.image_of_continuousOn (hsh.2.1.mono (Icc_subset_Icc_left hεq.le))
  have hEH : E ⊆ H := by
    rintro _ ⟨u, hu, rfl⟩
    exact hsh.2.2.1 u ⟨hεq.trans_le hu.1, hu.2⟩
  have hcover : η '' Icc 0 T ∩ K ⊆ fwdMapInv W' a '' E := by
    rintro _ ⟨⟨t, ht, rfl⟩, htK⟩
    have htε : ε ≤ t := not_lt.1 fun h => hfar t h htK
    have hat : (a : ℝ) < t := by rw [haq]; linarith
    have htm : (t : ℝ) - a ≤ m := by
      have : (t : ℝ) ≤ T := ht.2
      linarith [a.coe_nonneg]
    obtain ⟨_, htip, _⟩ := tendsto_trace_of_shift hWc hW0 a.coe_nonneg hat (hsh.mono htm)
    refine ⟨trace V ((t : ℝ) - a), ⟨(t : ℝ) - a, ⟨by rw [haq]; linarith, htm⟩, rfl⟩, ?_⟩
    rw [← htr t, htip]
  have hFd : DifferentiableOn ℂ (fwdMapInv W' a) H :=
    differentiableOn_fwdMapInv hWc hW0 a.coe_nonneg
  have hboxE : ∀ᶠ n in atTop, (dyadicCount n E : ℝ) ≤ ((2 : ℝ) ^ n) ^ interiorDimBound 4 := by
    have hEsub : trace V '' Icc 0 m ∩ E = E :=
      inter_eq_right.2 (image_mono (Icc_subset_Icc_left hεq.le))
    have := hbox E hEc hEH
    rwa [hEsub] at this
  have himg := eventually_dyadicCount_image_le isOpen_H hFd hEc hEH hd hboxE
  filter_upwards [himg] with n hn
  have hFEc : IsCompact (fwdMapInv W' a '' E) := hEc.image_of_continuousOn (hFd.continuousOn.mono hEH)
  refine le_trans ?_ hn
  exact_mod_cast Set.ncard_le_ncard (dyadicHits_mono hcover) (dyadicHits_finite hFEc.isBounded)

lemma interiorDimBound_four : interiorDimBound 4 = 7 / 4 := by
  simp only [interiorDimBound, onePointExponent]
  norm_num

/-- **Covering numbers of a stopped κ = 4 trace** (Lemma 4.14 for stopped traces; `15/8` is any exponent in
`(7/4, 2)`). -/
theorem IsMarkedChain.ae_eventually_dyadicCount_stopped_le (hF : IsOrderedForceWord xL xR)
    (hcum : HasNonnegCumWeights ρL ρR) (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (η ω)) (T : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ K : Set ℂ, IsCompact K → K ⊆ H → ∀ᶠ n in atTop,
      (dyadicCount n (η ω '' Icc 0 (T ω) ∩ K) : ℝ) ≤ ((2 : ℝ) ^ n) ^ (15 / 8 : ℝ) := by
  filter_upwards [hE.ae_eventually_dyadicCount_trace_le hF hcum, hη] with ω h hηω K hK hKH
  exact h (η ω) hηω (T ω) K hK hKH _ (by rw [interiorDimBound_four]; norm_num)

/-- **Covering numbers of a full transient κ = 4 trace** (Lemma 4.14 for the full traces of Corollary 4.13): a
transient trace visits a compact `K ⊆ ℍ` only during a bounded time interval. -/
theorem IsMarkedChain.ae_eventually_dyadicCount_range_le (hF : IsOrderedForceWord xL xR)
    (hcum : HasNonnegCumWeights ρL ρR) (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (η ω) ∧
      Tendsto (fun t => ‖η ω t‖) atTop atTop) :
    ∀ᵐ ω ∂P, ∀ K : Set ℂ, IsCompact K → K ⊆ H → ∀ᶠ n in atTop,
      (dyadicCount n (range (η ω) ∩ K) : ℝ) ≤ ((2 : ℝ) ^ n) ^ (15 / 8 : ℝ) := by
  filter_upwards [hE.ae_eventually_dyadicCount_trace_le hF hcum, hη] with ω h ⟨hηω, htr⟩ K hK hKH
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨T, hT⟩ := (htr.eventually_gt_atTop R).exists_forall_of_atTop
  have hsub : range (η ω) ∩ K ⊆ η ω '' Icc 0 T ∩ K := by
    rintro _ ⟨⟨t, rfl⟩, htK⟩
    refine ⟨⟨t, ⟨zero_le, ?_⟩, rfl⟩, htK⟩
    by_contra hlt
    have h1 := hT t (not_le.1 hlt).le
    have h2 : ‖η ω t‖ ≤ R := by simpa using hR htK
    linarith
  have hfin : ∀ n, (dyadicHits n (η ω '' Icc 0 T ∩ K)).Finite := fun n =>
    dyadicHits_finite (hK.isBounded.subset inter_subset_right)
  filter_upwards [h (η ω) hηω T K hK hKH (15 / 8) (by rw [interiorDimBound_four]; norm_num)]
    with n hn
  refine le_trans ?_ hn
  exact_mod_cast Set.ncard_le_ncard (dyadicHits_mono hsub) (hfin n)

end Chain

/-! ### Finite unions: the covering hypothesis (R1.1), and Lemma 4.14 -/

/-- `C (2ⁿ)^d (n + 1) 4^{-n} → 0` for `d < 2`. -/
lemma tendsto_mul_rpow_mul_succ_div_four_pow {d : ℝ} (hd : d < 2) (C : ℝ) :
    Tendsto (fun n : ℕ => C * ((2 : ℝ) ^ n) ^ d * (n + 1) / 4 ^ n) atTop (𝓝 0) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  set r : ℝ := 2 ^ d / 4 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hr, div_lt_one (by norm_num)]
    calc (2 : ℝ) ^ d < 2 ^ (2 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hd
      _ = 4 := by norm_num
  have he : ∀ n : ℕ, C * ((2 : ℝ) ^ n) ^ d * (n + 1) / 4 ^ n = C * (n * r ^ n + r ^ n) := by
    intro n
    have e1 : ((2 : ℝ) ^ n) ^ d = ((2 : ℝ) ^ d) ^ n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h2, mul_comm, Real.rpow_mul_natCast h2]
    rw [e1, hr, div_pow]
    have : (0 : ℝ) < 4 ^ n := by positivity
    field_simp
  simp_rw [he]
  simpa using ((tendsto_self_mul_const_pow_of_lt_one hr0 hr1).add
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)).const_mul C

section Union

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Finite unions satisfy (R1.1).** If `A ⊆ ⋃ᵢ Aᵢ` (finitely many) and every `Aᵢ` meets, on every compact
`K ⊆ ℍ`, at most `(2ⁿ)^d` dyadic squares of side `2^{-n}` for all large `n`, with `d < 2`, then `A` has the covering
property (R1.1) along all dyadic scales ("A finite union preserves the resulting bound"). -/
theorem hasThinCovering_of_eventually_le {ι : Type*} [Fintype ι] {A : Ω → Set ℂ}
    {Ai : ι → Ω → Set ℂ} {d : ℝ} (hd : d < 2) (hsub : ∀ᵐ ω ∂P, A ω ⊆ ⋃ i, Ai i ω)
    (hcount : ∀ i, ∀ᵐ ω ∂P, ∀ K : Set ℂ, IsCompact K → K ⊆ QuantumZipper.H → ∀ᶠ n in atTop,
      (dyadicCount n (Ai i ω ∩ K) : ℝ) ≤ ((2 : ℝ) ^ n) ^ d) :
    HasThinCovering A P := by
  classical
  intro K hK hKH
  refine ⟨id, tendsto_id, ?_⟩
  have hall : ∀ᵐ ω ∂P, ∀ i, ∀ K : Set ℂ, IsCompact K → K ⊆ QuantumZipper.H → ∀ᶠ n in atTop,
      (dyadicCount n (Ai i ω ∩ K) : ℝ) ≤ ((2 : ℝ) ^ n) ^ d := ae_all_iff.2 hcount
  filter_upwards [hsub, hall] with ω hs hc
  have hev : ∀ᶠ n in atTop, ∀ i, (dyadicCount n (Ai i ω ∩ K) : ℝ) ≤ ((2 : ℝ) ^ n) ^ d :=
    Filter.eventually_all.2 fun i => hc i K hK hKH
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_
    (tendsto_mul_rpow_mul_succ_div_four_pow hd (Fintype.card ι))
  filter_upwards [hev] with n hn
  have hsubh : dyadicHits n (A ω ∩ K) ⊆ ⋃ i ∈ (Finset.univ : Finset ι), dyadicHits n (Ai i ω ∩ K) := by
    rintro k ⟨z, hzk, hzA, hzK⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hs hzA)
    exact mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ i)) ⟨z, hzk, hi, hzK⟩
  have hfin : (⋃ i ∈ (Finset.univ : Finset ι), dyadicHits n (Ai i ω ∩ K)).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun i _ =>
      dyadicHits_finite (hK.isBounded.subset inter_subset_right)
  have h1 : (dyadicCount n (A ω ∩ K) : ℝ) ≤ ∑ i, (dyadicCount n (Ai i ω ∩ K) : ℝ) := by
    have := (Set.ncard_le_ncard hsubh hfin).trans (Finset.set_ncard_biUnion_le _ _)
    exact_mod_cast this
  have h2 : ∑ i, (dyadicCount n (Ai i ω ∩ K) : ℝ) ≤ Fintype.card ι * ((2 : ℝ) ^ n) ^ d := by
    calc ∑ i, (dyadicCount n (Ai i ω ∩ K) : ℝ) ≤ ∑ _i : ι, ((2 : ℝ) ^ n) ^ d :=
          Finset.sum_le_sum fun i _ => hn i
      _ = Fintype.card ι * ((2 : ℝ) ^ n) ^ d := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h4 : (0 : ℝ) < 4 ^ id n := by positivity
  show (dyadicCount (id n) (A ω ∩ K) : ℝ) * ((id n : ℕ) + 1) / 4 ^ id n ≤
    Fintype.card ι * ((2 : ℝ) ^ n) ^ d * (n + 1) / 4 ^ n
  simp only [id]
  gcongr
  exact h1.trans h2

/-- **Wang–Wu Lemma 4.14 (recovering the field off the walls).** Let `h` be a zero-boundary GFF on `ℍ` and
`F = h + m` with `m` bounded on `ℍ`. Let `A` be contained in a finite union of random sets `Aᵢ`, each meeting, on
every compact `K ⊆ ℍ`, at most `(2ⁿ)^d` dyadic squares of side `2^{-n}` for all large `n`, with `d < 2` — e.g. full
or stopped non-boundary-intersecting traces of Lemma 4.12 and Corollary 4.13
(`IsMarkedChain.ae_eventually_dyadicCount_range_le`, `IsMarkedChain.ae_eventually_dyadicCount_stopped_le`, with
`d = 15/8`). Then `F` is almost surely determined by its restriction to `ℍ ∖ A`. -/
theorem aeDeterminedSigma_offSigma_of_eventually_le [IsProbabilityMeasure P]
    {h F : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {m : ℂ → ℝ} {Mm : ℝ}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hm : ∀ z ∈ QuantumZipper.H, |m z| ≤ Mm) (hF : ∀ ω ψ, F ω ψ = h ω ψ + ∫ z, m z * ψ z)
    {ι : Type*} [Fintype ι] {A : Ω → Set ℂ} {Ai : ι → Ω → Set ℂ} {d : ℝ} (hd : d < 2)
    (hsub : ∀ᵐ ω ∂P, A ω ⊆ ⋃ i, Ai i ω)
    (hcount : ∀ i, ∀ᵐ ω ∂P, ∀ K : Set ℂ, IsCompact K → K ⊆ QuantumZipper.H → ∀ᶠ n in atTop,
      (dyadicCount n (Ai i ω ∩ K) : ℝ) ≤ ((2 : ℝ) ^ n) ^ d) :
    LQGMetric.AEDeterminedSigma (MeasurableSpace.comap F inferInstance) (offSigma A F) P :=
  aeDeterminedSigma_offSigma hh hm hF (hasThinCovering_of_eventually_le hd hsub hcount)

end Union

/-- **Lemma 4.14 for one full non-boundary-intersecting trace.** For a κ = 4 chain with an ordered force word and
nonnegative cumulative weights, let `η` be (almost surely) a transient generating trace (Lemma 4.12 and Corollary 4.13;
`IsMarkedChain.ae_simple_transient_trace` supplies one from the named inputs). For a zero-boundary GFF `h` on `ℍ`
on the same space and `F = h + m` with `m` bounded on `ℍ`, `F` is almost surely determined by its restriction to
`ℍ ∖ η([0, ∞))`. No independence or coupling of `h` and the chain is used. -/
theorem IsMarkedChain.aeDeterminedSigma_offSigma_range {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hFw : IsOrderedForceWord xL xR) (hcum : HasNonnegCumWeights ρL ρR)
    (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (η ω) ∧
      Tendsto (fun t => ‖η ω t‖) atTop atTop)
    {h F : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {m : ℂ → ℝ} {Mm : ℝ}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hm : ∀ z ∈ QuantumZipper.H, |m z| ≤ Mm) (hF : ∀ ω ψ, F ω ψ = h ω ψ + ∫ z, m z * ψ z) :
    LQGMetric.AEDeterminedSigma (MeasurableSpace.comap F inferInstance)
      (offSigma (fun ω => range (η ω)) F) P :=
  aeDeterminedSigma_offSigma_of_eventually_le (ι := Unit) (Ai := fun _ ω => range (η ω)) hh hm hF
    (by norm_num : (15 / 8 : ℝ) < 2) (Eventually.of_forall fun ω => subset_iUnion_of_subset () le_rfl)
    fun _ => hE.ae_eventually_dyadicCount_range_le hFw hcum hη

end InteractingSLE.WangWu
