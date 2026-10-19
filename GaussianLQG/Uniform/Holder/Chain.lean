import GaussianLQG.Uniform.Holder.Geom

/-!
# U12, deterministic part II: the chaining on a covered domain and the pointwise Hölder bound

Phase B, packet PB-U12 (ledger U12, Finding `fd:U12`, changes (iv) and (v)). For a continuous field
`f` and covering data `ChainGeom A Q T P` (`Holder/Geom.lean`):

* `chain_gen`: two points of `T` whose coordinates differ by less than `2^{-K}` (`1 ≤ K ≤ m`) are at
  `S`-internal distance `≤ 2E + 8B' + 24 Σ_{K ≤ k ≤ m} B k` (`S6P28U.chain_restr` in the offset
  square containing both, for the translated field);
* `holderConst_le_chain`: the pathwise bound `H ≤ c · 48P · G` of the `1/2`-Hölder constant over `T`
  of `c · D_S`, where `G = e^{ξM} 2^{-m/2} + Σ_{K ≤ m} 2^{K/2} B'_K + Σ_{k ≤ m} 2^{k/2} B_k`
  (`chainG`) collects the finest link (straight segments, ledger change (v)) and the level bounds
  (ledger change (iv), in place of the Markov/union step of `S6P28U.upper_step1`): pairs at distance
  `t ≤ 2^{-m}` use a straight segment, pairs with `2^{-m} < t ≤ 1/4` the chaining at the scale of
  `t`, farther pairs `P` pieces at scale `1`;
* `holderConst_le_straight`: the straight-segment bound alone (used for `n ≤ 1`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform
namespace Holder

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.Blueprint

/-- **The chaining on a covered domain** (`S6P28U.chain_restr` in the offset square containing
both points, applied to the translated field). -/
theorem chain_gen {ξ : ℝ} (hξ : 0 ≤ ξ) {f : ℂ → ℝ} (hf : Continuous f) {A : Finset ℂ}
    {Q T : Set ℂ} {P : ℕ} (G : ChainGeom A Q T P) {S : Set ℂ} (hQS : Q ⊆ S) {K m : ℕ}
    (hK1 : 1 ≤ K) (hKm : K ≤ m) (B : ℕ → ℝ≥0∞)
    (hB : ∀ k, K ≤ k → k ≤ m → ∀ r ∈ famH A k, S6D.len21 ξ f (k + 1) (jH k r) ≤ B k)
    (B' : ℝ≥0∞) (hB' : ∀ r ∈ famS A K, S6D.len21 ξ f K (jS K r) ≤ B')
    {M : ℝ} (hM : ∀ z ∈ Q, |f z| ≤ M) {x y : ℂ} (hx : x ∈ T) (hy : y ∈ T)
    (hre : |x.re - y.re| < (2 : ℝ)⁻¹ ^ K) (him : |x.im - y.im| < (2 : ℝ)⁻¹ ^ K) :
    lfppDOn ξ f S x y ≤ 2 * ENNReal.ofReal (Real.exp (ξ * M) * (2 * (2 : ℝ)⁻¹ ^ m)) + 8 * B' +
      24 * ∑ t ∈ Finset.range (m - K + 1), B (K + t) := by
  have hK2 : (2 : ℝ)⁻¹ ^ K ≤ 1 / 2 := by
    calc (2 : ℝ)⁻¹ ^ K ≤ (2 : ℝ)⁻¹ ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hK1
      _ = 1 / 2 := by norm_num
  obtain ⟨c, hc, hxc, hyc⟩ := G.cover x hx y hy (hre.trans_le hK2) (him.trans_le hK2)
  have hfc : Continuous fun z => f (z + c) := hf.comp (continuous_id.add continuous_const)
  have key := S6P28U.chain_restr (ξ := ξ) hfc hK1 hKm B
    (fun k hk1 hk2 i hi j hj e => by
      rw [len21_translate]
      exact hB k hk1 hk2 (c, ((i, j), e)) (by
        simp only [famH, S6D.idxSet, Finset.mem_product, Finset.mem_range, Finset.mem_univ,
          and_true]
        exact ⟨hc, hi, hj⟩))
    B' (fun i j hi hj e => by
      rw [len21_translate]
      exact hB' (c, ((i, j), e)) (by
        simp only [famS, S6P28U.idxS, Finset.mem_product, Finset.mem_range, Finset.mem_univ,
          and_true]
        exact ⟨hc, by omega, by omega⟩))
    (E := ENNReal.ofReal (Real.exp (ξ * M) * (2 * (2 : ℝ)⁻¹ ^ m)))
    (fun z hz w hw hzw => (lfppDOn_le_exp hξ LFPP.convex_closedUnitSquare
      (fun v hv => hM _ (G.sq_sub c hc v hv)) hz hw).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hzw (Real.exp_pos _).le)))
    hxc hyc (by rw [Complex.sub_re, Complex.sub_re, sub_sub_sub_cancel_right]; exact hre)
    (by rw [Complex.sub_im, Complex.sub_im, sub_sub_sub_cancel_right]; exact him)
  calc lfppDOn ξ f S x y ≤ lfppDOn ξ f ((· + c) '' closedUnitSquare) x y :=
        lfppDOn_anti (by rintro _ ⟨z, hz, rfl⟩; exact hQS (G.sq_sub c hc z hz)) x y
    _ = lfppDOn ξ (fun z => f (z + c)) closedUnitSquare (x - c) (y - c) := by
        rw [lfppDOn_translate, sub_add_cancel, sub_add_cancel]
    _ ≤ _ := key

/-! ### Far pairs: pieces along the segment -/

/-- the `i`-th of `P` equally spaced points from `x` to `y` -/
def pt (x y : ℂ) (P i : ℕ) : ℂ := x + ((i : ℝ) / P) • (y - x)

lemma pt_zero (x y : ℂ) (P : ℕ) : pt x y P 0 = x := by simp [pt]

lemma pt_self {P : ℕ} (hP : 0 < P) (x y : ℂ) : pt x y P P = y := by
  simp only [pt]
  rw [div_self (by exact_mod_cast hP.ne'), one_smul, add_sub_cancel]

lemma pt_mem {T : Set ℂ} (hT : Convex ℝ T) {x y : ℂ} (hx : x ∈ T) (hy : y ∈ T) {P i : ℕ}
    (hP : 0 < P) (hi : i ≤ P) : pt x y P i ∈ T :=
  hT.add_smul_sub_mem hx hy ⟨by positivity, by
    rw [div_le_one (by exact_mod_cast hP)]; exact_mod_cast hi⟩

lemma pt_sub_re (x y : ℂ) (P i : ℕ) (hP : 0 < P) :
    (pt x y P i).re - (pt x y P (i + 1)).re = (x.re - y.re) / P := by
  have hP' : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  simp only [pt, Complex.add_re, Complex.smul_re, Complex.sub_re, smul_eq_mul]
  push_cast
  field_simp
  ring

lemma pt_sub_im (x y : ℂ) (P i : ℕ) (hP : 0 < P) :
    (pt x y P i).im - (pt x y P (i + 1)).im = (x.im - y.im) / P := by
  have hP' : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  simp only [pt, Complex.add_im, Complex.smul_im, Complex.sub_im, smul_eq_mul]
  push_cast
  field_simp
  ring

/-- **a chain of `P` pieces**: `d(x, y) ≤ P B` if consecutive points are within `B` -/
lemma le_pieces {d : ℂ → ℂ → ℝ≥0∞} (htri : ∀ a b c, d a c ≤ d a b + d b c) (x y : ℂ) {P : ℕ}
    (hP : 0 < P) {B : ℝ≥0∞} (hB : ∀ i < P, d (pt x y P i) (pt x y P (i + 1)) ≤ B) :
    d x y ≤ P * B := by
  have key : ∀ k, 1 ≤ k → k ≤ P → d x (pt x y P k) ≤ k * B := by
    intro k hk1
    induction k, hk1 using Nat.le_induction with
    | base =>
      intro _
      have h := hB 0 hP
      rw [pt_zero] at h
      simpa using h
    | succ k hk ih =>
      intro hkP
      calc d x (pt x y P (k + 1)) ≤ d x (pt x y P k) + d (pt x y P k) (pt x y P (k + 1)) :=
            htri _ _ _
        _ ≤ k * B + B := add_le_add (ih (by omega)) (hB k (by omega))
        _ = ((k + 1 : ℕ) : ℝ≥0∞) * B := by push_cast; ring
  have h := key P hP le_rfl
  rwa [pt_self hP] at h

/-! ### The pointwise Hölder bound -/

/-- the chaining majorant: the finest link and the weighted level bounds -/
def chainG (e : ℝ) (m : ℕ) (BH BS : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (e * √((2 : ℝ)⁻¹ ^ m)) +
    ∑ K ∈ Finset.Icc 1 m, ENNReal.ofReal (√2 ^ K) * BS K +
      ∑ k ∈ Finset.Icc 1 m, ENNReal.ofReal (√2 ^ k) * BH k

/-- `ofReal (D.toReal / s) ≤ G` from `D ≤ ofReal s * G` -/
lemma ofReal_toReal_div_le {D G : ℝ≥0∞} {s : ℝ} (hs : 0 < s) (h : D ≤ ENNReal.ofReal s * G) :
    ENNReal.ofReal (D.toReal / s) ≤ G := by
  rcases eq_or_ne G ⊤ with hG | hG
  · rw [hG]; exact le_top
  have hne : ENNReal.ofReal s * G ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG
  have h1 : D.toReal ≤ s * G.toReal := by
    have := ENNReal.toReal_mono hne h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hs.le] at this
  rw [← ENNReal.ofReal_toReal hG]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ hs, mul_comm]
  exact h1

/-- the Hölder constant from a bound on each pair -/
lemma holderConst_le_of {d : ℂ × ℂ → ℝ} {T : Set ℂ} {G : ℝ≥0∞}
    (h : ∀ z ∈ T, ∀ w ∈ T, z ≠ w → ENNReal.ofReal (d (z, w) / ‖z - w‖ ^ (1 / 2 : ℝ)) ≤ G) :
    holderConst d T ≤ G := by
  unfold holderConst
  exact iSup₂_le fun z hz => iSup₂_le fun w hw => iSup_le fun hzw => h z hz w hw hzw

/-- the Hölder constant of `c · D` from `D(z,w) ≤ |z − w|^{1/2} G` -/
lemma holderConst_mul_le {c : ℝ} (hc : 0 ≤ c) {D : ℂ → ℂ → ℝ≥0∞} {T : Set ℂ} {G : ℝ≥0∞}
    (h : ∀ z ∈ T, ∀ w ∈ T, z ≠ w → D z w ≤ ENNReal.ofReal (√‖z - w‖) * G) :
    holderConst (fun z => c * (D z.1 z.2).toReal) T ≤ ENNReal.ofReal c * G := by
  refine holderConst_le_of fun z hz w hw hzw => ?_
  have ht : 0 < ‖z - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hzw)
  rw [← Real.sqrt_eq_rpow, mul_div_assoc, ENNReal.ofReal_mul hc]
  exact mul_le_mul_right (ofReal_toReal_div_le (Real.sqrt_pos.2 ht) (h z hz w hw hzw)) _

/-- the three groups of terms of the chaining bound against `48 · chainG` -/
lemma chain_terms_le {t : ℝ} {K m : ℕ} (hK1 : 1 ≤ K) (hKm : K ≤ m) {e : ℝ} (he : 0 ≤ e)
    (h1 : 1 ≤ 2 * √t * √2 ^ K) (h2 : (2 : ℝ)⁻¹ ^ m ≤ 2 * √t * √((2 : ℝ)⁻¹ ^ m))
    (BH BS : ℕ → ℝ≥0∞) :
    2 * ENNReal.ofReal (e * (2 * (2 : ℝ)⁻¹ ^ m)) + 8 * BS K +
        24 * ∑ u ∈ Finset.range (m - K + 1), BH (K + u) ≤
      ENNReal.ofReal (√t) * (48 * chainG e m BH BS) := by
  set h := (2 : ℝ)⁻¹ ^ m with hh
  have hst : 0 ≤ √t := Real.sqrt_nonneg _
  have hsh : 0 ≤ √h := Real.sqrt_nonneg _
  have hs2 : ∀ k : ℕ, 0 ≤ √2 ^ k := fun k => pow_nonneg (Real.sqrt_nonneg _) k
  have hs2K : ∀ u : ℕ, √2 ^ K ≤ √2 ^ (K + u) := fun u =>
    pow_le_pow_right₀ (Real.one_le_sqrt.2 (by norm_num)) (by omega)
  -- the finest link
  have hA : 2 * ENNReal.ofReal (e * (2 * h)) ≤
      ENNReal.ofReal (√t) * (8 * ENNReal.ofReal (e * √h)) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul hst]
    refine ENNReal.ofReal_le_ofReal ?_
    have : 2 * (e * (2 * h)) = 4 * e * h := by ring
    rw [this]
    calc 4 * e * h ≤ 4 * e * (2 * √t * √h) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = √t * (8 * (e * √h)) := by ring
  -- the shifted squares of scale `K`
  have hB : 8 * BS K ≤ ENNReal.ofReal (√t) * (16 * (ENNReal.ofReal (√2 ^ K) * BS K)) := by
    rw [← mul_assoc, ← mul_assoc]
    refine mul_le_mul_left ?_ _
    rw [show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by norm_num,
      show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by norm_num, ← ENNReal.ofReal_mul hst,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith
  have hBsum : ENNReal.ofReal (√2 ^ K) * BS K ≤
      ∑ K' ∈ Finset.Icc 1 m, ENNReal.ofReal (√2 ^ K') * BS K' :=
    Finset.single_le_sum (f := fun K' => ENNReal.ofReal (√2 ^ K') * BS K')
      (fun _ _ => zero_le) (Finset.mem_Icc.2 ⟨hK1, hKm⟩)
  -- the halves of the levels `K ≤ k ≤ m`
  have hC : 24 * ∑ u ∈ Finset.range (m - K + 1), BH (K + u) ≤
      ENNReal.ofReal (√t) * (48 * ∑ k ∈ Finset.Icc 1 m, ENNReal.ofReal (√2 ^ k) * BH k) := by
    have hterm : ∀ u : ℕ, 24 * BH (K + u) ≤
        ENNReal.ofReal (√t) * (48 * (ENNReal.ofReal (√2 ^ (K + u)) * BH (K + u))) := by
      intro u
      rw [← mul_assoc, ← mul_assoc]
      refine mul_le_mul_left ?_ _
      rw [show (24 : ℝ≥0∞) = ENNReal.ofReal 24 by norm_num,
        show (48 : ℝ≥0∞) = ENNReal.ofReal 48 by norm_num, ← ENNReal.ofReal_mul hst,
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := hs2K u
      nlinarith
    have hsub : ∑ u ∈ Finset.range (m - K + 1), ENNReal.ofReal (√2 ^ (K + u)) * BH (K + u) ≤
        ∑ k ∈ Finset.Icc 1 m, ENNReal.ofReal (√2 ^ k) * BH k := by
      have e : m - K + 1 = (m + 1) - K := by omega
      rw [e, ← Finset.sum_Ico_eq_sum_range (fun k => ENNReal.ofReal (√2 ^ k) * BH k)]
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun _ _ _ => zero_le)
      rw [Finset.mem_Ico] at hk
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    rw [Finset.mul_sum]
    calc ∑ u ∈ Finset.range (m - K + 1), 24 * BH (K + u)
        ≤ ∑ u ∈ Finset.range (m - K + 1),
            ENNReal.ofReal (√t) * (48 * (ENNReal.ofReal (√2 ^ (K + u)) * BH (K + u))) :=
          Finset.sum_le_sum fun u _ => hterm u
      _ = ENNReal.ofReal (√t) *
            (48 * ∑ u ∈ Finset.range (m - K + 1), ENNReal.ofReal (√2 ^ (K + u)) * BH (K + u)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ _ := by gcongr
  -- assembly
  unfold chainG
  calc 2 * ENNReal.ofReal (e * (2 * h)) + 8 * BS K +
        24 * ∑ u ∈ Finset.range (m - K + 1), BH (K + u)
      ≤ ENNReal.ofReal (√t) * (8 * ENNReal.ofReal (e * √h)) +
          ENNReal.ofReal (√t) * (16 * ∑ K' ∈ Finset.Icc 1 m, ENNReal.ofReal (√2 ^ K') * BS K') +
          ENNReal.ofReal (√t) * (48 * ∑ k ∈ Finset.Icc 1 m, ENNReal.ofReal (√2 ^ k) * BH k) := by
        refine add_le_add (add_le_add hA (hB.trans ?_)) hC
        gcongr
    _ ≤ ENNReal.ofReal (√t) * (48 * ENNReal.ofReal (e * √h)) +
          ENNReal.ofReal (√t) * (48 * ∑ K' ∈ Finset.Icc 1 m, ENNReal.ofReal (√2 ^ K') * BS K') +
          ENNReal.ofReal (√t) * (48 * ∑ k ∈ Finset.Icc 1 m, ENNReal.ofReal (√2 ^ k) * BH k) := by
        gcongr
        · norm_num
        · norm_num
    _ = _ := by ring

/-- **The pointwise Hölder bound by chaining** (ledger U12, changes (iv)–(v)): for `m ≥ 1`, with
`B_k` bounding the crossings of the halves of level `k` and `B'_K` those of the shifted squares of
scale `K` in all offset squares, and `|f| ≤ M` on `Q`,
`H_T(c · D_S) ≤ c · 48P · (e^{ξM} 2^{-m/2} + Σ_{K ≤ m} 2^{K/2} B'_K + Σ_{k ≤ m} 2^{k/2} B_k)`. -/
theorem holderConst_le_chain {ξ : ℝ} (hξ : 0 ≤ ξ) {f : ℂ → ℝ} (hf : Continuous f)
    {A : Finset ℂ} {Q T : Set ℂ} {P : ℕ} (G : ChainGeom A Q T P) {S : Set ℂ} (hQS : Q ⊆ S)
    {m : ℕ} (hm : 1 ≤ m) (BH BS : ℕ → ℝ≥0∞)
    (hBH : ∀ k, 1 ≤ k → k ≤ m → ∀ r ∈ famH A k, S6D.len21 ξ f (k + 1) (jH k r) ≤ BH k)
    (hBS : ∀ K, 1 ≤ K → K ≤ m → ∀ r ∈ famS A K, S6D.len21 ξ f K (jS K r) ≤ BS K)
    {M : ℝ} (hM : ∀ z ∈ Q, |f z| ≤ M) {c : ℝ} (hc : 0 ≤ c) :
    holderConst (fun z => c * (lfppDOn ξ f S z.1 z.2).toReal) T ≤
      ENNReal.ofReal c * (ENNReal.ofReal (48 * P) * chainG (Real.exp (ξ * M)) m BH BS) := by
  refine holderConst_mul_le hc fun z hz w hw hzw => ?_
  set e := Real.exp (ξ * M) with he_def
  have he : 0 ≤ e := (Real.exp_pos _).le
  set h := (2 : ℝ)⁻¹ ^ m with hh
  have hh0 : 0 < h := by positivity
  have hh1 : h ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  set t := ‖z - w‖ with ht_def
  have ht : 0 < t := norm_pos_iff.2 (sub_ne_zero.2 hzw)
  have hst : 0 ≤ √t := Real.sqrt_nonneg _
  have hre : |z.re - w.re| ≤ t := by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
  have him : |z.im - w.im| ≤ t := by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  set g := chainG e m BH BS with hg
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast G.P_pos
  have h48 : (48 : ℝ≥0∞) ≤ ENNReal.ofReal (48 * P) := by
    rw [show (48 : ℝ≥0∞) = ENNReal.ofReal 48 by norm_num]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  have hg48 : 48 * g ≤ ENNReal.ofReal (48 * P) * g := mul_le_mul_left h48 g
  have hzQ := G.T_sub hz
  have hwQ := G.T_sub hw
  -- the chaining at scale `K`
  have hchain : ∀ K, 1 ≤ K → K ≤ m → ∀ a ∈ T, ∀ b ∈ T, |a.re - b.re| < (2 : ℝ)⁻¹ ^ K →
      |a.im - b.im| < (2 : ℝ)⁻¹ ^ K → lfppDOn ξ f S a b ≤
        2 * ENNReal.ofReal (e * (2 * h)) + 8 * BS K +
          24 * ∑ u ∈ Finset.range (m - K + 1), BH (K + u) :=
    fun K hK1 hKm a ha b hb h1 h2 => chain_gen hξ hf G hQS hK1 hKm BH
      (fun k hk1 hk2 r hr => hBH k (hK1.trans hk1) hk2 r hr) (BS K) (hBS K hK1 hKm) hM ha hb h1 h2
  rcases le_or_gt t h with hA | hA
  · -- straight segment
    have hseg : lfppDOn ξ f S z w ≤ ENNReal.ofReal (e * t) := by
      refine (lfppDOn_anti hQS z w).trans ((lfppDOn_le_exp hξ G.convex_Q hM hzQ hwQ).trans ?_)
      rw [norm_sub_rev]
    refine hseg.trans ?_
    have h1 : e * t ≤ √t * (e * √h) := by
      have hts : t = √t * √t := (Real.mul_self_sqrt ht.le).symm
      have : √t ≤ √h := Real.sqrt_le_sqrt hA
      calc e * t = √t * (e * √t) := by
            calc e * t = e * (√t * √t) := by rw [← hts]
              _ = √t * (e * √t) := by ring
        _ ≤ √t * (e * √h) := by gcongr
    calc ENNReal.ofReal (e * t) ≤ ENNReal.ofReal (√t * (e * √h)) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal (√t) * ENNReal.ofReal (e * √h) := ENNReal.ofReal_mul hst
      _ ≤ ENNReal.ofReal (√t) * (ENNReal.ofReal (48 * P) * g) := by
          refine mul_le_mul_right ?_ _
          have hle : ENNReal.ofReal (e * √h) ≤ g := by
            rw [hg, chainG, add_assoc]; exact le_self_add
          refine hle.trans ?_
          calc g = 1 * g := (one_mul g).symm
            _ ≤ ENNReal.ofReal (48 * P) * g := by
                refine mul_le_mul_left ?_ g
                rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by nlinarith)
  rcases le_or_gt t (1 / 4) with hB | hB
  · -- the chaining at the scale of `t`
    obtain ⟨n', hn1, hn2⟩ := exists_nat_pow_near (show (1 : ℝ) ≤ 1 / t by
      rw [le_div_iff₀ ht]; linarith) (show (1 : ℝ) < 2 by norm_num)
    have htn : t ≤ (2 : ℝ)⁻¹ ^ n' := by
      rw [inv_pow, ← one_div, le_div_iff₀ (by positivity)]
      rw [le_div_iff₀ ht] at hn1; linarith
    have htn1 : (2 : ℝ)⁻¹ ^ (n' + 1) < t := by
      rw [inv_pow, ← one_div, div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ ht] at hn2; linarith
    have hn'2 : 2 ≤ n' := by
      by_contra hc
      push Not at hc
      have : (2 : ℝ) ^ (n' + 1) ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) (by omega)
      have h4 : (4 : ℝ) ≤ 1 / t := by rw [le_div_iff₀ ht]; linarith
      norm_num at this; linarith
    have hn'm : n' < m := by
      by_contra hc
      push Not at hc
      have : (2 : ℝ)⁻¹ ^ n' ≤ (2 : ℝ)⁻¹ ^ m := pow_le_pow_of_le_one (by norm_num) (by norm_num) hc
      linarith
    set K := n' - 1 with hK
    have hK2 : (2 : ℝ)⁻¹ ^ K = 2 * (2 : ℝ)⁻¹ ^ n' := by
      rw [show n' = K + 1 by omega, pow_succ]; ring
    have hcoord : ∀ x : ℝ, x ≤ t → x < (2 : ℝ)⁻¹ ^ K := fun x hx => by
      have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n' := by positivity
      rw [hK2]; linarith
    refine (hchain K (by omega) (by omega) z hz w hw (hcoord _ hre) (hcoord _ him)).trans ?_
    refine (chain_terms_le (t := t) (by omega) (by omega) he ?_ ?_ BH BS).trans ?_
    · -- `1 ≤ 2 √t 2^{K/2}` since `t > 2^{-(K+2)}`
      have hsq : (2 * √t * √2 ^ K) ^ 2 = 4 * t * 2 ^ K := by
        rw [mul_pow, mul_pow, Real.sq_sqrt ht.le, ← pow_mul, mul_comm K 2, pow_mul,
          Real.sq_sqrt (by norm_num)]
        ring
      have hlow : 1 < 4 * t * 2 ^ K := by
        have e1 : (2 : ℝ)⁻¹ ^ (n' + 1) * 2 ^ K = 1 / 4 := by
          rw [show n' + 1 = K + 2 by omega, pow_add, mul_comm, ← mul_assoc, ← mul_pow,
            mul_inv_cancel₀ (two_ne_zero), one_pow, one_mul]
          norm_num
        have : (2 : ℝ)⁻¹ ^ (n' + 1) * 2 ^ K < t * 2 ^ K :=
          mul_lt_mul_of_pos_right htn1 (by positivity)
        linarith
      have h0 : 0 ≤ 2 * √t * √2 ^ K := by positivity
      nlinarith
    · -- `2^{-m} ≤ 2 √t 2^{-m/2}` since `2^{-m} < t`
      have hsh : √h ≤ √t := Real.sqrt_le_sqrt hA.le
      have hh' : h = √h * √h := (Real.mul_self_sqrt hh0.le).symm
      have h0 : 0 ≤ √h := Real.sqrt_nonneg _
      calc h = √h * √h := hh'
        _ ≤ √t * √h := by gcongr
        _ ≤ 2 * √t * √h := by nlinarith
    · exact mul_le_mul_right hg48 _
  · -- far pairs: `P` pieces at scale `1`
    have hP := G.P_pos
    have hpieces := le_pieces (d := lfppDOn ξ f S) (fun a b c => lfppDOn_triangle a b c) z w hP
      (B := 2 * ENNReal.ofReal (e * (2 * h)) + 8 * BS 1 +
        24 * ∑ u ∈ Finset.range (m - 1 + 1), BH (1 + u)) (fun i hi => by
        obtain ⟨hp1, hp2⟩ := G.pieces z hz w hw
        have hP' : (0 : ℝ) < P := by exact_mod_cast hP
        refine hchain 1 le_rfl hm _ (pt_mem G.convex_T hz hw hP hi.le) _
          (pt_mem G.convex_T hz hw hP hi) ?_ ?_
        · rw [pt_sub_re z w P i hP, abs_div, abs_of_pos hP', div_lt_iff₀ hP']
          norm_num; linarith
        · rw [pt_sub_im z w P i hP, abs_div, abs_of_pos hP', div_lt_iff₀ hP']
          norm_num; linarith)
    refine hpieces.trans ?_
    have hst2 : 1 / 2 < √t := by
      rw [show (1 / 2 : ℝ) = √(1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) hB
    have hterms := chain_terms_le (t := t) (K := 1) le_rfl hm he (by
        have : (1 : ℝ) ≤ √2 ^ 1 := by rw [pow_one]; exact Real.one_le_sqrt.2 (by norm_num)
        nlinarith) (by
        have h0 : 0 ≤ √h := Real.sqrt_nonneg _
        have hsh1 : √h ≤ 1 := Real.sqrt_le_one.2 hh1
        have hh' : h = √h * √h := (Real.mul_self_sqrt hh0.le).symm
        calc h = √h * √h := hh'
          _ ≤ 1 * √h := by gcongr
          _ ≤ 2 * √t * √h := by nlinarith) BH BS
    calc (P : ℝ≥0∞) * (2 * ENNReal.ofReal (e * (2 * h)) + 8 * BS 1 +
          24 * ∑ u ∈ Finset.range (m - 1 + 1), BH (1 + u))
        ≤ (P : ℝ≥0∞) * (ENNReal.ofReal (√t) * (48 * g)) := mul_le_mul_right hterms _
      _ = ENNReal.ofReal (√t) * (ENNReal.ofReal (48 * P) * g) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast,
            show ENNReal.ofReal 48 = 48 by norm_num]
          ring

/-- **The straight-segment Hölder bound**: `H_T(c · D_S) ≤ c e^{ξM} √Dm` if `|f| ≤ M` on a convex
`Q ⊇ T` and `T` has diameter `≤ Dm` (used for `n ≤ 1`). -/
theorem holderConst_le_straight {ξ : ℝ} (hξ : 0 ≤ ξ) {f : ℂ → ℝ} {Q T S : Set ℂ}
    (hQ : Convex ℝ Q) (hTQ : T ⊆ Q) (hQS : Q ⊆ S) {Dm : ℝ}
    (hDm : ∀ z ∈ T, ∀ w ∈ T, ‖z - w‖ ≤ Dm) {M : ℝ} (hM : ∀ z ∈ Q, |f z| ≤ M) {c : ℝ}
    (hc : 0 ≤ c) :
    holderConst (fun z => c * (lfppDOn ξ f S z.1 z.2).toReal) T ≤
      ENNReal.ofReal c * ENNReal.ofReal (Real.exp (ξ * M) * √Dm) := by
  refine holderConst_mul_le hc fun z hz w hw hzw => ?_
  set e := Real.exp (ξ * M)
  have he : 0 ≤ e := (Real.exp_pos _).le
  set t := ‖z - w‖ with ht_def
  have ht : 0 < t := norm_pos_iff.2 (sub_ne_zero.2 hzw)
  have hseg : lfppDOn ξ f S z w ≤ ENNReal.ofReal (e * t) := by
    refine (lfppDOn_anti hQS z w).trans
      ((lfppDOn_le_exp hξ hQ hM (hTQ hz) (hTQ hw)).trans ?_)
    rw [norm_sub_rev]
  refine hseg.trans ?_
  have hts : t = √t * √t := (Real.mul_self_sqrt ht.le).symm
  have h1 : e * t ≤ √t * (e * √Dm) := by
    have : √t ≤ √Dm := Real.sqrt_le_sqrt (hDm z hz w hw)
    calc e * t = √t * (e * √t) := by
          calc e * t = e * (√t * √t) := by rw [← hts]
            _ = √t * (e * √t) := by ring
      _ ≤ √t * (e * √Dm) := by gcongr
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h1

/-- the coordinate differences of `T` bound its diameter by `P` -/
lemma ChainGeom.norm_sub_le {A : Finset ℂ} {Q T : Set ℂ} {P : ℕ} (G : ChainGeom A Q T P)
    {z w : ℂ} (hz : z ∈ T) (hw : w ∈ T) : ‖z - w‖ ≤ P := by
  obtain ⟨h1, h2⟩ := G.pieces z hz w hw
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.sub_re, Complex.sub_im]
  linarith

end Holder
end Uniform
end GaussianLQG
