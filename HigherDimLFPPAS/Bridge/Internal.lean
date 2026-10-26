import HigherDimLFPPAS.Bridge.Weyl
import HigherDimLFPP.Paths.Polygon
import HigherDimLFPP.Paths.Compare
import HigherDimLQGContinuity.Fatou.Basic

/-!
# The internal LFPP metric is the C¹-path infimum

For an open set, polygonal paths approximate the internal length metric of a continuous LFPP
field. The proof uses small balls along a near-minimizing curve and lets the density oscillation
on those balls tend to zero.
-/

set_option autoImplicit false
-- The finite-partition argument specializes several dependent internal-distance infima.
set_option maxHeartbeats 600000

noncomputable section

open Set Topology
open scoped ENNReal

namespace HigherDimLFPPAS.Bridge

open HigherDimLQGMetric
open HigherDimLFPP (Rd PcwJoined)
open LQGMetric.MetricGeometry

variable {d : ℕ}

private theorem bridgeInternal_euclidean_le_fieldZero (ξ : ℝ) (x y : Rd d) :
    ‖y - x‖ ≤ (fieldLfppMetric ξ (0 : C(Rd d, ℝ))).1 (x, y) := by
  have h := HigherDimLFPP.exp_mul_le_lfppDistOn (ζ := ξ)
    (φ := (0 : C(Rd d, ℝ))) (V := Set.univ) (x := x) (y := y)
    continuous_const (PcwJoined.of_convex convex_univ (Set.mem_univ x) (Set.mem_univ y))
    (r := ‖y - x‖) (m := 0) le_rfl (by simp)
  have heq := fieldLfpp_eq_lfppDistOn (ξ := ξ)
    (φ := (fun _ : Rd d => 0)) continuous_const (x, y)
  change ‖y - x‖ ≤ fieldLfpp ξ (fun _ : Rd d => 0) (x, y)
  rw [heq]
  have hzero : ⇑(0 : C(Rd d, ℝ)) = (fun _ : Rd d => 0) := by funext q; simp
  simpa only [Real.exp_zero, one_mul, hzero] using h

private theorem bridgeInternal_fieldLfppMetric_eq_weylScale
    (ξ : ℝ) (φ : C(Rd d, ℝ)) (x y : Rd d) :
    ENNReal.ofReal ((fieldLfppMetric ξ φ).1 (x,y)) =
      weylScale ξ φ (fieldLfppMetric ξ (0 : C(Rd d, ℝ))) x y := by
  let G := fieldLfppMetric ξ φ
  have h := fieldLfppMetric_internal_eq_weylScaleOn ξ φ
    (0 : C(Rd d, ℝ)) Set.univ isOpen_univ x y
  rw [G.internal_univ_of_isLength (fieldLfppMetric_isLength ξ φ)] at h
  simpa [G, weylScaleOn_univ, sub_zero] using h

private theorem bridgeInternal_edge_bound
    (ξ δ : ℝ) (φ : C(Rd d, ℝ)) {V U : Set (Rd d)} (hUV : U ⊆ V)
    (hU : IsOpen U) {P : ℝ → Rd d} {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) (hPU : MapsTo P (Icc a b) U)
    (hseg : MapsTo (HigherDimLFPP.segPath (P a) (P b)) (Icc (0 : ℝ) 1) U)
    (hvar : ∀ z ∈ U, |ξ * (φ z - φ (P a))| ≤ δ) :
    fieldDistIn ξ φ V (P a) (P b) ≤
      ENNReal.ofReal (Real.exp (2 * δ)) *
        (fieldLfppMetric ξ φ).len P a b := by
  let E := fieldLfppMetric ξ (0 : C(Rd d, ℝ))
  let G := fieldLfppMetric ξ φ
  let c := ξ * φ (P a)
  have hupper (z : Rd d) (hz : z ∈ U) : ξ * φ z ≤ c + δ := by
    have hh := (abs_le.mp (hvar z hz)).2
    dsimp [c]
    nlinarith
  have hlow (z : Rd d) (hz : z ∈ U) : c - δ ≤ ξ * φ z := by
    have hh := (abs_le.mp (hvar z hz)).1
    dsimp [c]
    nlinarith
  have hcost : HigherDimLFPP.lfppLength ξ φ
      (HigherDimLFPP.segPath (P a) (P b)) ≤
        Real.exp (c + δ) * ‖P b - P a‖ := by
    apply HigherDimLFPP.lfppLength_segPath_le φ.continuous
    intro u hu
    have huU := hseg hu
    have huvar := hupper _ huU
    exact Real.exp_le_exp.mpr huvar
  have hfield : fieldDistIn ξ φ V (P a) (P b) ≤
      ENNReal.ofReal (Real.exp (c + δ) * ‖P b - P a‖) := by
    calc
      fieldDistIn ξ φ V (P a) (P b) ≤
          fieldDistIn ξ φ U (P a) (P b) := fieldDistIn_mono hUV
      _ ≤ ENNReal.ofReal
          (HigherDimLFPP.lfppLength ξ φ (HigherDimLFPP.segPath (P a) (P b))) :=
        fieldDistIn_le_ofReal_lfppLength φ.continuous
          (HigherDimLFPP.isPcwC1Path_segPath (P a) (P b)) hseg
      _ ≤ ENNReal.ofReal (Real.exp (c + δ) * ‖P b - P a‖) :=
        ENNReal.ofReal_le_ofReal hcost
  have hspec := fieldLfppMetric_internal_eq_weylScaleOn ξ φ
    (0 : C(Rd d, ℝ)) U hU (P a) (P b)
  have hweyl := le_weylScaleOn_of_le (ξ := ξ) (f := φ) (D := E)
    (U := U) (z := P a) (w := P b) (a := c - δ) hlow
  have hweight : ENNReal.ofReal (Real.exp (c - δ)) * E.internal U (P a) (P b) ≤
      G.internal U (P a) (P b) := by
    have hspec' : G.internal U (P a) (P b) =
        weylScaleOn ξ φ E U (P a) (P b) := by
      simpa [E, G, sub_zero] using hspec
    exact hweyl.trans_eq hspec'.symm
  have hchord : ENNReal.ofReal ‖P b - P a‖ ≤ E.internal U (P a) (P b) := by
    calc
      ENNReal.ofReal ‖P b - P a‖ ≤ ENNReal.ofReal (E.1 (P a, P b)) :=
        ENNReal.ofReal_le_ofReal (bridgeInternal_euclidean_le_fieldZero ξ (P a) (P b))
      _ ≤ E.internal U (P a) (P b) := E.ofReal_le_internal U (P a) (P b)
  have hweight' : ENNReal.ofReal (Real.exp (c - δ) * ‖P b - P a‖) ≤
      G.internal U (P a) (P b) := by
    calc
      ENNReal.ofReal (Real.exp (c - δ) * ‖P b - P a‖) =
          ENNReal.ofReal (Real.exp (c - δ)) * ENNReal.ofReal ‖P b - P a‖ := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (Real.exp (c - δ)) * E.internal U (P a) (P b) :=
        by gcongr
      _ ≤ G.internal U (P a) (P b) := hweight
  have hlen : G.internal U (P a) (P b) ≤ G.len P a b := by
    exact G.internal_le_len hab hP hPU
  have hmain : ENNReal.ofReal (Real.exp (c + δ) * ‖P b - P a‖) ≤
      ENNReal.ofReal (Real.exp (2 * δ)) * G.len P a b := by
    have hexp : Real.exp (c + δ) = Real.exp (2 * δ) * Real.exp (c - δ) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hreal : Real.exp (c + δ) * ‖P b - P a‖ =
        Real.exp (2 * δ) * (Real.exp (c - δ) * ‖P b - P a‖) := by
      rw [hexp]
      ring
    calc
      ENNReal.ofReal (Real.exp (c + δ) * ‖P b - P a‖) =
          ENNReal.ofReal (Real.exp (2 * δ)) *
            ENNReal.ofReal (Real.exp (c - δ) * ‖P b - P a‖) := by
              rw [hreal, ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (Real.exp (2 * δ)) * G.internal U (P a) (P b) :=
        by gcongr
      _ ≤ ENNReal.ofReal (Real.exp (2 * δ)) * G.len P a b :=
        by gcongr
  exact hfield.trans hmain

private theorem bridgeInternal_sum_len
    (G : ContMetric d) {P : ℝ → Rd d} {t : ℕ → ℝ}
    (ht0 : t 0 = 0) (htmono : Monotone t) (n : ℕ) :
    (∑ i ∈ Finset.range n, G.len P (t i) (t (i + 1))) = G.len P 0 (t n) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    rw [ht0]
    change (0 : ℝ≥0∞) = curveLength (G.pt ∘ P) 0 0
    rw [curveLength_self]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h0n : 0 ≤ t n := by rw [← ht0]; exact htmono (Nat.zero_le n)
    exact G.len_add P h0n (htmono (Nat.le_succ n))

private theorem bridgeInternal_path_partition_bound
    (ξ δ : ℝ) (hδ : 0 < δ) (φ : C(Rd d, ℝ)) {V : Set (Rd d)} (hV : IsOpen V)
    {P : ℝ → Rd d} {x y : Rd d}
    (hP : ContinuousOn P (Icc (0 : ℝ) 1)) (h0 : P 0 = x) (h1 : P 1 = y)
    (hPV : MapsTo P (Icc (0 : ℝ) 1) V) :
    fieldDistIn ξ φ V x y ≤
      ENNReal.ofReal (Real.exp (2 * δ)) * (fieldLfppMetric ξ φ).len P 0 1 := by
  let K : Set (Rd d) := P '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hP
  have hKV : K ⊆ V := by
    rintro z ⟨t, ht, rfl⟩
    exact hPV ht
  obtain ⟨rV, hrV, hKVthick⟩ := hK.exists_cthickening_subset_open hV hKV
  let K' : Set (Rd d) := Metric.cthickening rV K
  have hK' : IsCompact K' := hK.cthickening
  have hK'sub : K' ⊆ V := by
    simpa [K'] using hKVthick
  let g : Rd d → ℝ := fun z => ξ * φ z
  have hg : Continuous g := continuous_const.mul φ.continuous
  obtain ⟨ρ, hρ, hgρ⟩ := Metric.uniformContinuousOn_iff.1
    (hK'.uniformContinuousOn_of_continuous hg.continuousOn) δ hδ
  let r : ℝ := min rV (ρ / 2)
  have hr : 0 < r := lt_min hrV (by positivity)
  have hrV' : r ≤ rV := min_le_left _ _
  have hrρ : r < ρ := by dsimp [r]; linarith [min_le_right rV (ρ / 2)]
  obtain ⟨τ, hτ, hPτ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hP) (r / 2) (by positivity)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hτ
  let N : ℕ := n + 1
  have hNpos : (0 : ℝ) < N := by positivity
  have hNinv : 1 / (N : ℝ) < τ := by
    simpa [N] using hn
  let t : ℕ → ℝ := fun i => (i : ℝ) / (N : ℝ)
  have ht0 : t 0 = 0 := by simp [t]
  have htN : t N = 1 := by
    dsimp [t]
    exact div_self hNpos.ne'
  have htmono : Monotone t := by
    intro i j hij
    dsimp [t]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)
  have htstep (i : ℕ) : t (i + 1) - t i = 1 / (N : ℝ) := by
    dsimp [t]
    push_cast
    ring
  have htmem : ∀ i ≤ N, t i ∈ Icc (0 : ℝ) 1 := by
    intro i hi
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hNpos]
    exact_mod_cast hi
  let p : ℕ → Rd d := fun i => P (t i)
  have hp0 : p 0 = x := by simp [p, ht0, h0]
  have hpN : p N = y := by simp [p, htN, h1]
  have hedge : ∀ i < N,
      fieldDistIn ξ φ V (p i) (p (i + 1)) ≤
        ENNReal.ofReal (Real.exp (2 * δ)) *
          (fieldLfppMetric ξ φ).len P (t i) (t (i + 1)) := by
    intro i hiN
    let U : Set (Rd d) := Metric.ball (p i) r
    have hU : IsOpen U := Metric.isOpen_ball
    have hUiV : U ⊆ V := by
      intro z hz
      apply hK'sub
      apply Metric.mem_cthickening_of_dist_le z (p i) rV K
        (mem_image_of_mem P (htmem i (Nat.le_of_lt hiN)))
      exact (Metric.mem_ball.mp (by simpa [U] using hz)).le.trans hrV'
    have htime {s : ℝ} (hs : s ∈ Icc (t i) (t (i + 1))) : dist s (t i) < τ := by
      have hs01 : s ∈ Icc (0 : ℝ) 1 :=
        ⟨(htmem i (Nat.le_of_lt hiN)).1.trans hs.1,
          hs.2.trans (htmem (i + 1) (Nat.succ_le_of_lt hiN)).2⟩
      have hsi : s - t i ≤ t (i + 1) - t i := sub_le_sub_right hs.2 _
      have hsi0 : 0 ≤ s - t i := sub_nonneg.mpr hs.1
      rw [Real.dist_eq, abs_of_nonneg hsi0]
      calc
        s - t i ≤ t (i + 1) - t i := hsi
        _ = 1 / (N : ℝ) := htstep i
        _ < τ := hNinv
    have hchordSmall : dist (p (i + 1)) (p i) < r / 2 := by
      have h := hPτ (t (i + 1)) (htmem (i + 1) (Nat.succ_le_of_lt hiN))
        (t i) (htmem i (Nat.le_of_lt hiN)) ?_
      · simpa [p] using h
      · rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (htmono (Nat.le_succ i)))]
        rw [show t (i + 1) - t i = 1 / (N : ℝ) from htstep i]
        exact hNinv
    have hPball : MapsTo P (Icc (t i) (t (i + 1))) U := by
      intro s hs
      rw [Metric.mem_ball, dist_comm]
      have hs01 : s ∈ Icc (0 : ℝ) 1 :=
        ⟨(htmem i (Nat.le_of_lt hiN)).1.trans hs.1,
          hs.2.trans (htmem (i + 1) (Nat.succ_le_of_lt hiN)).2⟩
      have hs' := hPτ s hs01 (t i) (htmem i (Nat.le_of_lt hiN)) (htime hs)
      have hs'' : dist (p i) (P s) < r / 2 := by simpa [p, dist_comm] using hs'
      exact lt_trans hs'' (by linarith [hr])
    have hsegball : MapsTo (HigherDimLFPP.segPath (p i) (p (i + 1)))
        (Icc (0 : ℝ) 1) U := by
      intro u hu
      rw [Metric.mem_ball, dist_comm]
      have hnorm := HigherDimLFPP.norm_segPath_sub (p i) (p (i + 1)) hu
      have hnorm' : ‖HigherDimLFPP.segPath (p i) (p (i + 1)) u - p i‖ < r := by
        calc
          ‖HigherDimLFPP.segPath (p i) (p (i + 1)) u - p i‖ ≤
              ‖p (i + 1) - p i‖ := hnorm
          _ = dist (p (i + 1)) (p i) := by rw [dist_eq_norm, norm_sub_rev]
          _ < r / 2 := hchordSmall
          _ < r := by linarith
      simpa [U, dist_eq_norm, norm_sub_rev] using hnorm'
    have hvariation : ∀ z ∈ U, |ξ * (φ z - φ (p i))| ≤ δ := by
      intro z hz
      have hz' : z ∈ K' := by
        apply Metric.mem_cthickening_of_dist_le z (p i) rV K
          (mem_image_of_mem P (htmem i (Nat.le_of_lt hiN)))
        exact (Metric.mem_ball.mp (by simpa [U] using hz)).le.trans hrV'
      have hpi' : p i ∈ K' := by
        exact Metric.self_subset_cthickening (δ := rV) K (mem_image_of_mem P
          (htmem i (Nat.le_of_lt hiN)))
      have hdist : dist z (p i) < ρ := by
        have hzdist := Metric.mem_ball.mp (by simpa [U] using hz)
        exact hzdist.trans hrρ
      have hmod := hgρ z hz' (p i) hpi' hdist
      have hreal : g z - g (p i) = ξ * (φ z - φ (p i)) := by
        dsimp [g]
        ring
      have hmod' : |g z - g (p i)| < δ := by simpa [Real.dist_eq] using hmod
      rw [hreal] at hmod'
      exact hmod'.le
    have hPcontseg : ContinuousOn P (Icc (t i) (t (i + 1))) :=
      hP.mono (Icc_subset_Icc (htmem i (Nat.le_of_lt hiN)).1
        (htmem (i + 1) (Nat.succ_le_of_lt hiN)).2)
    have hseg := bridgeInternal_edge_bound (d := d) (ξ := ξ) (δ := δ) (φ := φ)
      (hUV := hUiV) (hU := hU) (P := P) (a := t i) (b := t (i + 1))
      (hab := htmono (Nat.le_succ i)) (hP := hPcontseg) (hPU := hPball)
      (hseg := hsegball) (hvar := hvariation)
    simpa only [p] using hseg
  have hp0V : p 0 ∈ V := hPV (by rw [ht0]; exact ⟨by norm_num, by norm_num⟩)
  have hchain : ∀ k ≤ N,
      fieldDistIn ξ φ V (p 0) (p k) ≤
        ∑ i ∈ Finset.range k,
          ENNReal.ofReal (Real.exp (2 * δ)) *
            (fieldLfppMetric ξ φ).len P (t i) (t (i + 1)) := by
    intro k hk
    induction k with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      rw [fieldDistIn_self (ξ := ξ) (φ := ⇑φ) hp0V]
    | succ k ih =>
      have hkN : k < N := by omega
      calc
        fieldDistIn ξ φ V (p 0) (p (k + 1)) ≤
            fieldDistIn ξ φ V (p 0) (p k) + fieldDistIn ξ φ V (p k) (p (k + 1)) :=
          fieldDistIn_triangle φ.continuous (p 0) (p k) (p (k + 1))
        _ ≤ (∑ i ∈ Finset.range k,
              ENNReal.ofReal (Real.exp (2 * δ)) *
                (fieldLfppMetric ξ φ).len P (t i) (t (i + 1))) +
              ENNReal.ofReal (Real.exp (2 * δ)) *
                (fieldLfppMetric ξ φ).len P (t k) (t (k + 1)) :=
          add_le_add (ih (by omega)) (hedge k hkN)
        _ = ∑ i ∈ Finset.range (k + 1),
              ENNReal.ofReal (Real.exp (2 * δ)) *
                (fieldLfppMetric ξ φ).len P (t i) (t (i + 1)) := by
          rw [Finset.sum_range_succ]
  have hsum := hchain N le_rfl
  rw [hp0, hpN] at hsum
  calc
    fieldDistIn ξ φ V x y ≤
        ∑ i ∈ Finset.range N,
          ENNReal.ofReal (Real.exp (2 * δ)) *
            (fieldLfppMetric ξ φ).len P (t i) (t (i + 1)) := hsum
    _ = ENNReal.ofReal (Real.exp (2 * δ)) *
          (fieldLfppMetric ξ φ).len P 0 1 := by
      rw [← Finset.mul_sum, bridgeInternal_sum_len _ ht0 htmono N, htN]

private theorem bridgeInternal_path_le_len
    (ξ : ℝ) (φ : C(Rd d, ℝ)) {V : Set (Rd d)} (hV : IsOpen V)
    {P : ℝ → Rd d} {x y : Rd d}
    (hP : ContinuousOn P (Icc (0 : ℝ) 1)) (h0 : P 0 = x) (h1 : P 1 = y)
    (hPV : MapsTo P (Icc (0 : ℝ) 1) V) :
    fieldDistIn ξ φ V x y ≤ (fieldLfppMetric ξ φ).len P 0 1 := by
  let G := fieldLfppMetric ξ φ
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hfin => ?_
  let L : ℝ := (G.len P 0 1).toReal
  have hLnonneg : 0 ≤ L := ENNReal.toReal_nonneg
  have hL : ENNReal.ofReal L = G.len P 0 1 := ENNReal.ofReal_toReal (ne_top_of_lt hfin)
  have hεR : 0 < (ε : ℝ) := by exact_mod_cast hε
  let q : ℝ := (ε : ℝ) / (L + 1)
  have hq : 0 < q := by dsimp [q]; positivity
  let δ : ℝ := Real.log (1 + q) / 4
  have hδ : 0 < δ := by
    dsimp [δ]
    apply (div_pos_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).2
    exact Real.log_pos (by linarith)
  have hδexp : Real.exp (2 * δ) ≤ 1 + q := by
    have hlog : 2 * δ ≤ Real.log (1 + q) := by
      dsimp [δ]
      have hlogpos : 0 ≤ Real.log (1 + q) := (Real.log_pos (by linarith)).le
      linarith
    calc
      Real.exp (2 * δ) ≤ Real.exp (Real.log (1 + q)) := Real.exp_le_exp.mpr hlog
      _ = 1 + q := Real.exp_log (by linarith)
  have hpartition := bridgeInternal_path_partition_bound ξ δ hδ φ hV hP h0 h1 hPV
  have hfactor : ENNReal.ofReal (Real.exp (2 * δ)) ≤ ENNReal.ofReal (1 + q) :=
    ENNReal.ofReal_le_ofReal hδexp
  have hprod : ENNReal.ofReal (1 + q) * G.len P 0 1 =
      G.len P 0 1 + ENNReal.ofReal (q * L) := by
    rw [← hL, ← ENNReal.ofReal_mul (by linarith : 0 ≤ 1 + q)]
    have hreal : (1 + q) * L = L + q * L := by ring
    rw [hreal, ENNReal.ofReal_add hLnonneg (mul_nonneg hq.le hLnonneg),
      ENNReal.ofReal_mul hq.le]
  have hratio : L / (L + 1) ≤ 1 := by
    rw [div_le_one (by linarith : 0 < L + 1)]
    linarith
  have hqL : q * L ≤ (ε : ℝ) := by
    have hqeq : q * L = (ε : ℝ) * (L / (L + 1)) := by
      dsimp [q]
      field_simp
    rw [hqeq]
    exact mul_le_of_le_one_right (by positivity) hratio
  have hεcoe : ENNReal.ofReal (ε : ℝ) = ε := ENNReal.ofReal_coe_nnreal
  calc
    fieldDistIn ξ φ V x y ≤ ENNReal.ofReal (Real.exp (2 * δ)) * G.len P 0 1 := hpartition
    _ ≤ ENNReal.ofReal (1 + q) * G.len P 0 1 := by gcongr
    _ = G.len P 0 1 + ENNReal.ofReal (q * L) := hprod
    _ ≤ G.len P 0 1 + ε := by
      exact add_le_add le_rfl
        ((ENNReal.ofReal_le_ofReal hqL).trans_eq hεcoe)

/-- The C¹-path infimum is at most the internal distance of the LFPP metric on an open set. -/
theorem fieldDistIn_le_internal_open
    (ξ : ℝ) (φ : C(Rd d, ℝ)) {V : Set (Rd d)} (hV : IsOpen V) (x y : Rd d) :
    fieldDistIn ξ φ V x y ≤ (fieldLfppMetric ξ φ).internal V x y := by
  let G := fieldLfppMetric ξ φ
  rw [G.internal_eq_iInf_len]
  refine le_iInf fun P => le_iInf fun hP => le_iInf fun h0 => le_iInf fun h1 =>
    le_iInf fun hPV => ?_
  rw [← h0, ← h1]
  exact bridgeInternal_path_le_len ξ φ hV hP rfl rfl hPV

/-- Equality of the two point-to-point internal LFPP distances on open domains. -/
theorem fieldDistIn_eq_internal_open
    (ξ : ℝ) (φ : C(Rd d, ℝ)) {V : Set (Rd d)} (hV : IsOpen V) (x y : Rd d) :
    fieldDistIn ξ φ V x y = (fieldLfppMetric ξ φ).internal V x y := by
  apply le_antisymm
  · exact fieldDistIn_le_internal_open ξ φ hV x y
  · exact HigherDimLQGContinuity.fatou_field_internal_le ξ φ V x y

/-- Equality of the set-to-set internal LFPP distances on open domains. -/
theorem fieldSetDistIn_eq_setDistIn_open
    (ξ : ℝ) (φ : C(Rd d, ℝ)) {V : Set (Rd d)} (hV : IsOpen V)
    (A B : Set (Rd d)) :
    fieldSetDistIn ξ φ V A B = setDistIn (fieldLfppMetric ξ φ) V A B := by
  unfold fieldSetDistIn setDistIn
  refine iInf_congr fun x => ?_
  refine iInf_congr fun hx => ?_
  refine iInf_congr fun y => ?_
  refine iInf_congr fun hy => ?_
  exact fieldDistIn_eq_internal_open ξ φ hV x y

end HigherDimLFPPAS.Bridge
