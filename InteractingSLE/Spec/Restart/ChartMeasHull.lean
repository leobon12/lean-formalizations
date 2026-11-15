/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.HullKernel
import InteractingSLE.Foundations.Loewner.ConformalImageLoewner
import InteractingSLE.Foundations.Loewner.CapacityEstimates
import InteractingSLE.Foundations.Topology.PathComplement

/-!
# Dyadic outer approximation of a compact set and of its filled hull

Packet PROVE-RESTART-CPL4 (measurable choice of the first-contact chart). The mapping-out function `g_A` of the hull
`A = fill(K)` of a random compact set `K` is made measurable through approximations from outside that take only
countably many values: `K_n` is the union of the closed dyadic squares of side `2⁻ⁿ` meeting `K`
(`dyadicCover n K`). These decrease to `K`, their fillings decrease to `fill(K)` (`iInter_fillH_dyadicCover`), and the
kernel theorem for decreasing hulls (`tendstoLocallyUniformlyOn_of_antitone_H`, PROVE-GEO-HKERNEL) gives
`g_{fill K_n} → g_{fill K}` locally uniformly on `ℍ \ fill(K)`, with the derivatives.

## Main results

* `dyadicSquare`, `dyadicIdx`, `dyadicCover`; `subset_dyadicCover`, `dyadicCover_antitone`,
  `iInter_dyadicCover`, `dyadicIdx_finite`, `isCompact_dyadicCover`, `isPreconnected_dyadicCover_union`;
* `iInter_fillH_dyadicCover`: for compact `K`, `⋂ₙ fill(Kₙ) = fill(K)`;
* `tendstoLocallyUniformlyOn_mapOut_dyadicCover`, `tendstoLocallyUniformlyOn_deriv_mapOut_dyadicCover`,
  `tendstoLocallyUniformlyOn_invFunOn_mapOut_dyadicCover`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Restart

/-! ### Dyadic squares -/

/-- The closed dyadic square of level `n` and index `k`: `[k₁, k₁ + 1] × [k₂, k₂ + 1]` scaled by `2⁻ⁿ`. -/
def dyadicSquare (n : ℕ) (k : ℤ × ℤ) : Set ℂ :=
  {z | (k.1 : ℝ) ≤ 2 ^ n * z.re ∧ 2 ^ n * z.re ≤ (k.1 : ℝ) + 1 ∧
    (k.2 : ℝ) ≤ 2 ^ n * z.im ∧ 2 ^ n * z.im ≤ (k.2 : ℝ) + 1}

theorem isClosed_dyadicSquare (n : ℕ) (k : ℤ × ℤ) : IsClosed (dyadicSquare n k) := by
  have h1 : Continuous fun z : ℂ => (2 : ℝ) ^ n * z.re := continuous_const.mul continuous_re
  have h2 : Continuous fun z : ℂ => (2 : ℝ) ^ n * z.im := continuous_const.mul continuous_im
  exact (isClosed_le continuous_const h1).inter ((isClosed_le h1 continuous_const).inter
    ((isClosed_le continuous_const h2).inter (isClosed_le h2 continuous_const)))

theorem convex_dyadicSquare (n : ℕ) (k : ℤ × ℤ) : Convex ℝ (dyadicSquare n k) := by
  have hre : IsLinearMap ℝ fun z : ℂ => (2 : ℝ) ^ n * z.re :=
    ⟨fun x y => by simp [mul_add], fun c x => by simp; ring⟩
  have him : IsLinearMap ℝ fun z : ℂ => (2 : ℝ) ^ n * z.im :=
    ⟨fun x y => by simp [mul_add], fun c x => by simp; ring⟩
  exact (convex_halfSpace_ge hre _).inter ((convex_halfSpace_le hre _).inter
    ((convex_halfSpace_ge him _).inter (convex_halfSpace_le him _)))

theorem norm_sub_le_of_mem_dyadicSquare {n : ℕ} {k : ℤ × ℤ} {z w : ℂ} (hz : z ∈ dyadicSquare n k)
    (hw : w ∈ dyadicSquare n k) : ‖z - w‖ ≤ 2 / 2 ^ n := by
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
  obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
  have hre : |z.re - w.re| ≤ 1 / 2 ^ n := by
    rw [abs_le]; constructor
    · rw [neg_le, neg_sub, le_div_iff₀ hp]; nlinarith
    · rw [le_div_iff₀ hp]; nlinarith
  have him : |z.im - w.im| ≤ 1 / 2 ^ n := by
    rw [abs_le]; constructor
    · rw [neg_le, neg_sub, le_div_iff₀ hp]; nlinarith
    · rw [le_div_iff₀ hp]; nlinarith
  calc ‖z - w‖ ≤ |(z - w).re| + |(z - w).im| := Complex.norm_le_abs_re_add_abs_im _
    _ = |z.re - w.re| + |z.im - w.im| := by rw [sub_re, sub_im]
    _ ≤ 1 / 2 ^ n + 1 / 2 ^ n := add_le_add hre him
    _ = 2 / 2 ^ n := by ring

theorem isCompact_dyadicSquare (n : ℕ) (k : ℤ × ℤ) : IsCompact (dyadicSquare n k) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_dyadicSquare n k) ?_
  rw [Metric.isBounded_iff]
  exact ⟨2 / 2 ^ n, fun z hz w hw => by rw [dist_eq_norm]; exact norm_sub_le_of_mem_dyadicSquare hz hw⟩

/-- The level-`n` square containing `z`, indexed by the integer parts of `2ⁿ Re z` and `2ⁿ Im z`. -/
def dyadicIndexOf (n : ℕ) (z : ℂ) : ℤ × ℤ := (⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋)

theorem mem_dyadicSquare_indexOf (n : ℕ) (z : ℂ) : z ∈ dyadicSquare n (dyadicIndexOf n z) :=
  ⟨Int.floor_le _, (Int.lt_floor_add_one _).le, Int.floor_le _, (Int.lt_floor_add_one _).le⟩

/-- Every square of level `n + 1` lies in its parent square of level `n`. -/
theorem dyadicSquare_succ_subset (n : ℕ) (k : ℤ × ℤ) :
    dyadicSquare (n + 1) k ⊆ dyadicSquare n (k.1 / 2, k.2 / 2) := by
  have key : ∀ (m : ℤ) (x : ℝ), (m : ℝ) ≤ 2 * x → 2 * x ≤ m + 1 →
      ((m / 2 : ℤ) : ℝ) ≤ x ∧ x ≤ ((m / 2 : ℤ) : ℝ) + 1 := by
    intro m x h1 h2
    have e : 2 * (m / 2) + m % 2 = m := by omega
    have e' : ((m : ℝ)) = 2 * ((m / 2 : ℤ) : ℝ) + ((m % 2 : ℤ) : ℝ) := by
      rw [← Int.cast_ofNat, ← Int.cast_mul, ← Int.cast_add, e]
    have f0 : (0 : ℝ) ≤ ((m % 2 : ℤ) : ℝ) := by exact_mod_cast (show 0 ≤ m % 2 by omega)
    have f1 : ((m % 2 : ℤ) : ℝ) ≤ 1 := by exact_mod_cast (show m % 2 ≤ 1 by omega)
    constructor <;> linarith
  rintro z ⟨h1, h2, h3, h4⟩
  rw [pow_succ] at h1 h2 h3 h4
  have a := key k.1 (2 ^ n * z.re) (by linarith) (by linarith)
  have b := key k.2 (2 ^ n * z.im) (by linarith) (by linarith)
  exact ⟨a.1, a.2, b.1, b.2⟩

/-! ### The dyadic cover of a set -/

/-- The indices of the level-`n` squares meeting `K`. -/
def dyadicIdx (n : ℕ) (K : Set ℂ) : Set (ℤ × ℤ) := {k | (dyadicSquare n k ∩ K).Nonempty}

/-- The level-`n` dyadic cover of `K`: the union of the closed level-`n` squares meeting `K`. -/
def dyadicCover (n : ℕ) (K : Set ℂ) : Set ℂ := ⋃ k ∈ dyadicIdx n K, dyadicSquare n k

variable {K : Set ℂ}

theorem subset_dyadicCover (n : ℕ) : K ⊆ dyadicCover n K := fun z hz =>
  mem_biUnion (show dyadicIndexOf n z ∈ dyadicIdx n K from ⟨z, mem_dyadicSquare_indexOf n z, hz⟩)
    (mem_dyadicSquare_indexOf n z)

theorem dyadicCover_succ_subset (n : ℕ) : dyadicCover (n + 1) K ⊆ dyadicCover n K := by
  intro z hz
  simp only [dyadicCover, mem_iUnion] at hz ⊢
  obtain ⟨k, ⟨w, hwQ, hwK⟩, hzQ⟩ := hz
  exact ⟨(k.1 / 2, k.2 / 2), ⟨w, dyadicSquare_succ_subset n k hwQ, hwK⟩, dyadicSquare_succ_subset n k hzQ⟩

theorem dyadicCover_antitone : Antitone fun n => dyadicCover n K :=
  antitone_nat_of_succ_le fun n => dyadicCover_succ_subset n

theorem exists_mem_norm_sub_le_of_mem_dyadicCover {n : ℕ} {z : ℂ} (hz : z ∈ dyadicCover n K) :
    ∃ w ∈ K, ‖z - w‖ ≤ 2 / 2 ^ n := by
  simp only [dyadicCover, mem_iUnion] at hz
  obtain ⟨k, ⟨w, hwQ, hwK⟩, hzQ⟩ := hz
  exact ⟨w, hwK, norm_sub_le_of_mem_dyadicSquare hzQ hwQ⟩

theorem exists_lt_two_div_pow {δ : ℝ} (hδ : 0 < δ) : ∃ n : ℕ, 2 / (2 : ℝ) ^ n < δ := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < δ / 2 by positivity) (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨n, ?_⟩
  rw [one_div_pow] at hn
  have : 2 / (2 : ℝ) ^ n = 2 * (1 / 2 ^ n) := by ring
  rw [this]; linarith

theorem iInter_dyadicCover (hK : IsClosed K) : ⋂ n, dyadicCover n K = K := by
  refine Subset.antisymm (fun z hz => ?_) (subset_iInter fun n => subset_dyadicCover n)
  rw [← hK.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_lt_two_div_pow hε
  obtain ⟨w, hwK, hzw⟩ := exists_mem_norm_sub_le_of_mem_dyadicCover (mem_iInter.1 hz n)
  exact ⟨w, hwK, by rw [dist_eq_norm]; linarith⟩

theorem dyadicIdx_finite (hK : Bornology.IsBounded K) (n : ℕ) : (dyadicIdx n K).Finite := by
  obtain ⟨R, hR⟩ := hK.subset_closedBall 0
  set M : ℤ := ⌈(2 : ℝ) ^ n * |R|⌉ + 1 with hM
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have hbd : ∀ x : ℝ, |x| ≤ R → ∀ m : ℤ, (m : ℝ) ≤ 2 ^ n * x → 2 ^ n * x ≤ m + 1 → m ∈ Icc (-M) M := by
    intro x hx m h1 h2
    have hc : (2 : ℝ) ^ n * |R| ≤ ⌈(2 : ℝ) ^ n * |R|⌉ := Int.le_ceil _
    have hx' : (2 : ℝ) ^ n * |x| ≤ 2 ^ n * |R| :=
      mul_le_mul_of_nonneg_left (hx.trans (le_abs_self R)) hp.le
    have habs := abs_le.1 (le_refl |x|)
    have h3 : (2 : ℝ) ^ n * x ≤ 2 ^ n * |x| := mul_le_mul_of_nonneg_left (le_abs_self x) hp.le
    have h4 : -(2 ^ n * |x|) ≤ (2 : ℝ) ^ n * x := by
      rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_abs_le x) hp.le
    constructor
    · have : (-(M : ℝ)) ≤ m := by rw [hM]; push_cast; linarith
      exact_mod_cast this
    · have : (m : ℝ) ≤ M := by rw [hM]; push_cast; linarith
      exact_mod_cast this
  refine ((Set.finite_Icc (-M) M).prod (Set.finite_Icc (-M) M)).subset ?_
  rintro k ⟨w, ⟨h1, h2, h3, h4⟩, hwK⟩
  have hw := mem_closedBall_zero_iff.1 (hR hwK)
  exact ⟨hbd w.re ((abs_re_le_norm w).trans hw) k.1 h1 h2, hbd w.im ((abs_im_le_norm w).trans hw) k.2 h3 h4⟩

theorem isCompact_dyadicCover (hK : Bornology.IsBounded K) (n : ℕ) : IsCompact (dyadicCover n K) :=
  (dyadicIdx_finite hK n).isCompact_biUnion fun k _ => isCompact_dyadicSquare n k

theorem isPreconnected_dyadicCover_union {L : Set ℂ} (hc : IsPreconnected (K ∪ L)) {x : ℂ} (hx : x ∈ L)
    (n : ℕ) : IsPreconnected (dyadicCover n K ∪ L) := by
  set S := K ∪ L with hS
  set c : Set (Set ℂ) := insert S ((fun k => dyadicSquare n k ∪ S) '' dyadicIdx n K) with hcdef
  have hxS : x ∈ S := Or.inr hx
  have heq : dyadicCover n K ∪ L = ⋃₀ c := by
    apply Subset.antisymm
    · rintro z (hz | hz)
      · simp only [dyadicCover, mem_iUnion] at hz
        obtain ⟨k, hk, hzk⟩ := hz
        exact ⟨_, Or.inr ⟨k, hk, rfl⟩, Or.inl hzk⟩
      · exact ⟨S, Or.inl rfl, Or.inr hz⟩
    · rintro z ⟨s, hs, hzs⟩
      rcases hs with rfl | ⟨k, hk, rfl⟩
      · rcases hzs with hz | hz
        · exact Or.inl (subset_dyadicCover n hz)
        · exact Or.inr hz
      · rcases hzs with hz | hz | hz
        · exact Or.inl (mem_biUnion hk hz)
        · exact Or.inl (subset_dyadicCover n hz)
        · exact Or.inr hz
  rw [heq]
  refine isPreconnected_sUnion x c (fun s hs => ?_) (fun s hs => ?_)
  · rcases hs with rfl | ⟨k, -, rfl⟩
    · exact hxS
    · exact Or.inr hxS
  · rcases hs with rfl | ⟨k, ⟨w, hwQ, hwK⟩, rfl⟩
    · exact hc
    · exact IsPreconnected.union w hwQ (Or.inl hwK) (convex_dyadicSquare n k).isPreconnected hc

/-! ### The filled hulls of the dyadic covers -/

/-- The lower closed half-plane `{Im ≤ 0}`. -/
def lowerHalf : Set ℂ := {z | z.im ≤ 0}

theorem zero_mem_lowerHalf : (0 : ℂ) ∈ lowerHalf := show (0 : ℂ).im ≤ 0 by simp

theorem fillH_dyadicCover_antitone : Antitone fun n => fillH (dyadicCover n K) :=
  fun _ _ hmn => fillH_mono (dyadicCover_antitone hmn)

theorem isHPHull_fillH_dyadicCover (hK : Bornology.IsBounded K) (hc : IsPreconnected (K ∪ lowerHalf)) (n : ℕ) :
    IsHPHull (fillH (dyadicCover n K)) :=
  isHPHull_fillH_of_isPreconnected (isCompact_dyadicCover hK n).isBounded
    (isPreconnected_dyadicCover_union hc zero_mem_lowerHalf n)

/-- **The fillings of the dyadic covers decrease to the filling** of a compact set: a point of `ℍ \ fill(K)` is
joined to `(R + 1) i` by a path at positive distance from `K`, which avoids the fine covers. -/
theorem iInter_fillH_dyadicCover (hK : IsCompact K) : ⋂ n, fillH (dyadicCover n K) = fillH K := by
  refine Subset.antisymm (fun z hz => ?_) (subset_iInter fun n => fillH_mono (subset_dyadicCover n))
  have hz0 := mem_iInter.1 hz 0
  by_contra hzK
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · have hidx : dyadicIdx 0 K = ∅ := by
      ext k; simp [dyadicIdx, hKe]
    have : dyadicCover 0 K = ∅ := by simp [dyadicCover, hidx]
    rw [this] at hz0
    exact hzK (by rw [hKe]; exact hz0)
  obtain ⟨R, hR, hKR⟩ := (isCompact_dyadicCover hK.isBounded 0).isBounded.subset_ball_lt 0 0
  have hKR' : K ⊆ ball 0 R := (subset_dyadicCover 0).trans hKR
  have hcl : closure K = K := hK.isClosed.closure_eq
  set w₀ : ℂ := ((R + 1 : ℝ) : ℂ) * I with hw₀
  have hzD : z ∈ H \ fillH K := ⟨hz0.1, hzK⟩
  rw [H_diff_fillH hR (by rw [hcl]; exact hKR'), hcl] at hzD
  have hFo : IsOpen (H \ K) := QuantumZipper.isOpen_H.sdiff hK.isClosed
  have hCo : IsOpen (connectedComponentIn (H \ K) w₀) := hFo.connectedComponentIn
  have hw₀C : w₀ ∈ connectedComponentIn (H \ K) w₀ :=
    mem_connectedComponentIn (connectedComponentIn_nonempty_iff.1 ⟨z, hzD⟩)
  have hCc : IsConnected (connectedComponentIn (H \ K) w₀) :=
    isConnected_connectedComponentIn_iff.2 (connectedComponentIn_subset _ _ hw₀C)
  obtain ⟨p, hp⟩ := (hCo.isConnected_iff_isPathConnected.1 hCc).joinedIn z hzD w₀ hw₀C
  have hpK : ∀ t, p t ∉ K := fun t h => (connectedComponentIn_subset _ _ (hp t)).2 h
  -- the path keeps a positive distance from `K`
  obtain ⟨t₀, -, hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty
    ((continuous_infDist_pt K).comp p.continuous).continuousOn
  have hδ : 0 < infDist (p t₀) K := (hK.isClosed.notMem_iff_infDist_pos hKne).1 (hpK t₀)
  obtain ⟨n, hn⟩ := exists_lt_two_div_pow hδ
  have havoid : ∀ t, p t ∉ dyadicCover n K := fun t ht => by
    obtain ⟨w, hwK, hw⟩ := exists_mem_norm_sub_le_of_mem_dyadicCover ht
    have h1 : infDist (p t₀) K ≤ infDist (p t) K := isMinOn_iff.1 hmin t (mem_univ _)
    have h2 : infDist (p t) K ≤ dist (p t) w := infDist_le_dist_of_mem hwK
    rw [dist_eq_norm] at h2
    linarith
  -- so `z` lies in the unbounded component for the cover
  have hcov : closure (dyadicCover n K) ⊆ ball 0 R := by
    rw [(isCompact_dyadicCover hK.isBounded n).isClosed.closure_eq]
    exact (dyadicCover_antitone (Nat.zero_le n)).trans hKR
  have hmem : z ∈ H \ fillH (dyadicCover n K) := by
    rw [H_diff_fillH hR hcov, (isCompact_dyadicCover hK.isBounded n).isClosed.closure_eq]
    have hsub : range p ⊆ H \ dyadicCover n K := by
      rintro _ ⟨t, rfl⟩
      exact ⟨(connectedComponentIn_subset _ _ (hp t)).1, havoid t⟩
    have hw₀' : w₀ ∈ connectedComponentIn (H \ dyadicCover n K) w₀ :=
      mem_connectedComponentIn (hsub ⟨1, p.target⟩)
    have := (isPreconnected_range p.continuous).subset_connectedComponentIn ⟨1, p.target⟩ hsub
    exact this ⟨0, p.source⟩
  exact hmem.2 (mem_iInter.1 hz n)

/-! ### Convergence of the mapping-out functions -/

variable (hK : IsCompact K) (hc : IsPreconnected (K ∪ lowerHalf))
include hK hc

theorem isHPHull_fillH_of_compact : IsHPHull (fillH K) :=
  isHPHull_fillH_of_isPreconnected hK.isBounded hc

/-- **The mapping-out functions of the dyadic covers converge** locally uniformly on `ℍ \ fill(K)`. -/
theorem tendstoLocallyUniformlyOn_mapOut_dyadicCover :
    TendstoLocallyUniformlyOn (fun n => ConformalImage.mapOut (fillH (dyadicCover n K)))
      (ConformalImage.mapOut (fillH K)) atTop (H \ fillH K) :=
  tendstoLocallyUniformlyOn_of_antitone_H fillH_dyadicCover_antitone
    (isHPHull_fillH_dyadicCover hK.isBounded hc) (isHPHull_fillH_of_compact hK hc)
    (iInter_fillH_dyadicCover hK)
    (fun n => ConformalImage.isMapOut_mapOut (isHPHull_fillH_dyadicCover hK.isBounded hc n))
    (ConformalImage.isMapOut_mapOut (isHPHull_fillH_of_compact hK hc))

theorem exists_subset_ball_dyadicCover : ∃ R, ∀ n, fillH (dyadicCover n K) ⊆ ball 0 R := by
  obtain ⟨R, -, hR⟩ := (isHPHull_fillH_dyadicCover hK.isBounded hc 0).exists_subset_ball
  exact ⟨R, fun n => (fillH_dyadicCover_antitone (Nat.zero_le n)).trans hR⟩

theorem kernelConvergesTo_dyadicCover {w₀ : ℂ} (hw₀ : w₀ ∈ H \ fillH K) :
    QuantumZipper.CA.Kernel.KernelConvergesTo (fun n => H \ fillH (dyadicCover n K)) (H \ fillH K) w₀ :=
  kernelConvergesTo_H_of_antitone fillH_dyadicCover_antitone (isHPHull_fillH_dyadicCover hK.isBounded hc)
    (isHPHull_fillH_of_compact hK hc) (iInter_fillH_dyadicCover hK) hw₀

/-- The derivatives converge as well. -/
theorem tendstoLocallyUniformlyOn_deriv_mapOut_dyadicCover :
    TendstoLocallyUniformlyOn (fun n => deriv (ConformalImage.mapOut (fillH (dyadicCover n K))))
      (deriv (ConformalImage.mapOut (fillH K))) atTop (H \ fillH K) := by
  obtain ⟨R, hR⟩ := exists_subset_ball_dyadicCover hK hc
  obtain ⟨w₀, hw₀⟩ : (H \ fillH K).Nonempty := (isHPHull_fillH_of_compact hK hc).isConnected.nonempty
  exact tendstoLocallyUniformlyOn_deriv_of_kernelConvergesTo_H (isHPHull_fillH_dyadicCover hK.isBounded hc)
    (isHPHull_fillH_of_compact hK hc) hR
    (fun n => ConformalImage.isMapOut_mapOut (isHPHull_fillH_dyadicCover hK.isBounded hc n))
    (ConformalImage.isMapOut_mapOut (isHPHull_fillH_of_compact hK hc)) (kernelConvergesTo_dyadicCover hK hc hw₀)

omit hc in
/-- Every point of `ℍ \ fill(K)` eventually lies outside the fillings of the covers. -/
theorem eventually_mem_H_diff_fillH_dyadicCover {z : ℂ} (hz : z ∈ H \ fillH K) :
    ∀ᶠ n in atTop, z ∈ H \ fillH (dyadicCover n K) := by
  have hz' : z ∉ ⋂ n, fillH (dyadicCover n K) := by rw [iInter_fillH_dyadicCover hK]; exact hz.2
  obtain ⟨m, hm⟩ := not_forall.1 (fun h => hz' (mem_iInter.2 h))
  filter_upwards [eventually_ge_atTop m] with n hn
  exact ⟨hz.1, fun h => hm (fillH_dyadicCover_antitone hn h)⟩

omit hK hc in
theorem fillH_subset_fillH_dyadicCover (n : ℕ) : fillH K ⊆ fillH (dyadicCover n K) :=
  fillH_mono (subset_dyadicCover n)

end Restart

end InteractingSLE
