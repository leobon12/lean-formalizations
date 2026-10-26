import HigherDimLFPPAS.Bridge.Barrier
import HigherDimLFPPAS.Bridge.Weyl
import HigherDimLQGMetric.Proper.Geometry
import HigherDimLQGMetric.Metric.WeylBasic
import HigherDimLFPP.Paths.Compare

/-!
# Geodesics under a deterministic field barrier

Outside a larger ball, modify a continuous field to be nonnegative. The resulting LFPP metric is
proper, and locality transfers its geodesics back through the barrier.
-/

set_option autoImplicit false

noncomputable section

open Set Topology Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Bridge

open HigherDimLQGMetric
open HigherDimLFPP (Rd PcwJoined)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-- A continuous radial cutoff that is zero through radius `R + 1` and one from radius `R + 2`.
-/
private def bridgeBarrierCutoff (R r : ℝ) : ℝ := max 0 (min 1 (r - (R + 1)))

private theorem bridgeBarrierCutoff_continuous (R : ℝ) :
    Continuous (bridgeBarrierCutoff R) := by
  change Continuous (fun r : ℝ => max 0 (min 1 (r - (R + 1))))
  have hmin : Continuous (fun r : ℝ => min 1 (r - (R + 1))) :=
    continuous_min.comp (continuous_const.prodMk (continuous_id.sub continuous_const))
  exact continuous_max.comp (continuous_const.prodMk hmin)

private theorem bridgeBarrierCutoff_nonneg (R r : ℝ) : 0 ≤ bridgeBarrierCutoff R r :=
  le_max_left _ _

private theorem bridgeBarrierCutoff_le_one (R r : ℝ) : bridgeBarrierCutoff R r ≤ 1 := by
  exact (max_le_iff).2 ⟨by norm_num, min_le_left _ _⟩

private theorem bridgeBarrierCutoff_eq_zero {R r : ℝ} (hr : r ≤ R + 1) :
    bridgeBarrierCutoff R r = 0 := by
  have hmin : min 1 (r - (R + 1)) ≤ 0 :=
    (min_le_right _ _).trans (sub_nonpos.mpr hr)
  simp [bridgeBarrierCutoff, max_eq_left hmin]

private theorem bridgeBarrierCutoff_eq_one {R r : ℝ} (hr : R + 2 ≤ r) :
    bridgeBarrierCutoff R r = 1 := by
  have hmin : min 1 (r - (R + 1)) = 1 := by
    apply min_eq_left
    linarith
  simp [bridgeBarrierCutoff, hmin]

/-- The field modified to be nonnegative outside the ball of radius `R + 2`. -/
private def bridgeBarrierField (R : ℝ) (φ : C(Rd d, ℝ)) : C(Rd d, ℝ) :=
  ⟨fun z => φ z + bridgeBarrierCutoff R ‖z‖ * max (-φ z) 0, by
    have hc := bridgeBarrierCutoff_continuous R
    fun_prop⟩

private theorem bridgeBarrierField_eq_on_ball {R : ℝ} {φ : C(Rd d, ℝ)}
    {z : Rd d} (hz : ‖z‖ ≤ R + 1) : bridgeBarrierField R φ z = φ z := by
  simp [bridgeBarrierField, bridgeBarrierCutoff_eq_zero hz]

private theorem bridgeBarrierField_nonneg_outside {R : ℝ} {φ : C(Rd d, ℝ)}
    {z : Rd d} (hz : R + 2 ≤ ‖z‖) : 0 ≤ bridgeBarrierField R φ z := by
  by_cases hφ : φ z ≤ 0
  · simp [bridgeBarrierField, bridgeBarrierCutoff_eq_one hz, max_eq_left (by linarith :
      0 ≤ -φ z)]
  · have hφ' : 0 ≤ φ z := by linarith
    simp [bridgeBarrierField, bridgeBarrierCutoff_eq_one hz,
      max_eq_right (by linarith : -φ z ≤ 0)]
    exact hφ'

private theorem bridgeBarrierField_ge {R : ℝ} {φ : C(Rd d, ℝ)} (z : Rd d) :
    φ z ≤ bridgeBarrierField R φ z := by
  dsimp [bridgeBarrierField]
  exact le_add_of_nonneg_right
    (mul_nonneg (bridgeBarrierCutoff_nonneg R ‖z‖) (le_max_right _ _))

private theorem bridge_exists_last_hit_closed {P : ℝ → Rd d} {a b : ℝ}
    (hP : ContinuousOn P (Icc a b)) {K : Set (Rd d)} (hK : IsClosed K)
    (hne : ∃ t ∈ Icc a b, P t ∈ K) :
    ∃ s ∈ Icc a b, P s ∈ K ∧ ∀ t ∈ Ioc s b, P t ∉ K := by
  let S : Set ℝ := Icc a b ∩ P ⁻¹' K
  have hS : IsClosed S := hP.preimage_isClosed_of_isClosed isClosed_Icc hK
  have hSne : S.Nonempty := by
    obtain ⟨t, ht, htK⟩ := hne
    exact ⟨t, ht, htK⟩
  have hSbound : BddAbove S := ⟨b, fun t ht => ht.1.2⟩
  have hmem := hS.csSup_mem hSne hSbound
  refine ⟨sSup S, hmem.1, hmem.2, ?_⟩
  intro t ht htK
  have hta : a ≤ t := hmem.1.1.trans ht.1.le
  have htS : t ∈ S := ⟨⟨hta, ht.2⟩, htK⟩
  have htle : t ≤ sSup S := le_csSup hSbound htS
  exact (not_lt_of_ge htle) ht.1

private theorem bridgeBarrierField_len_eq {R ξ : ℝ} (φ : C(Rd d, ℝ))
    {P : ℝ → Rd d} {a b : ℝ} (hP : ContinuousOn P (Icc a b))
    (hPU : MapsTo P (Icc a b) (Metric.ball 0 (R + 1))) :
    (fieldLfppMetric ξ (bridgeBarrierField R φ)).len P a b =
      (fieldLfppMetric ξ φ).len P a b := by
  let G' := fieldLfppMetric ξ (bridgeBarrierField R φ)
  let G := fieldLfppMetric ξ φ
  have hU : IsOpen (Metric.ball (0 : Rd d) (R + 1)) := isOpen_ball
  have hlocal : ∀ z ∈ Metric.ball (0 : Rd d) (R + 1), ∀ w ∈ Metric.ball 0 (R + 1),
      G'.internal (Metric.ball 0 (R + 1)) z w = G.internal (Metric.ball 0 (R + 1)) z w := by
    intro z hz w hw
    exact l7a_fieldLfppMetric_internal_congr ξ (bridgeBarrierField R φ) φ hU
      (fun q hq => bridgeBarrierField_eq_on_ball (by
        have hqn : ‖q‖ < R + 1 := by
          simpa only [Metric.mem_ball, dist_zero_right] using hq
        exact hqn.le)) z w
  rw [← G'.curveLengthWith_internal hP hPU, ← G.curveLengthWith_internal hP hPU]
  apply curveLengthWith_congr
  intro s t hs hst ht
  have hsu : s ∈ Icc a b := ⟨hs, hst.trans ht⟩
  have htu : t ∈ Icc a b := ⟨hs.trans hst, ht⟩
  exact hlocal (P s) (hPU hsu) (P t) (hPU htu)

private theorem bridge_euclidean_le_fieldZero (ξ : ℝ) (x y : Rd d) :
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

private theorem bridge_modified_internal_ge_euclidean
    {R ξ : ℝ} (hξ : 0 < ξ) (φ : C(Rd d, ℝ)) (z w : Rd d)
    (hz : R + 2 < ‖z‖) (hw : R + 2 < ‖w‖) :
    ENNReal.ofReal ‖w - z‖ ≤
      (fieldLfppMetric ξ (bridgeBarrierField R φ)).internal
        (Metric.closedBall 0 (R + 2))ᶜ z w := by
  let U : Set (Rd d) := (Metric.closedBall 0 (R + 2))ᶜ
  let E := fieldLfppMetric ξ (0 : C(Rd d, ℝ))
  let G := fieldLfppMetric ξ (bridgeBarrierField R φ)
  have hU : IsOpen U := isOpen_compl_iff.2 Metric.isClosed_closedBall
  have hzU : z ∈ U := by
    change z ∉ Metric.closedBall 0 (R + 2)
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz
  have hwU : w ∈ U := by
    change w ∉ Metric.closedBall 0 (R + 2)
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hw
  have hφ : ∀ q ∈ U, 0 ≤ ξ * bridgeBarrierField R φ q := by
    intro q hq
    have hq' : R + 2 < ‖q‖ := by
      change q ∉ Metric.closedBall 0 (R + 2) at hq
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hq
    exact mul_nonneg hξ.le
      (bridgeBarrierField_nonneg_outside (le_of_lt hq'))
  have hscale := le_weylScaleOn_of_le (ξ := ξ) (f := bridgeBarrierField R φ)
    (D := E) (U := U) (z := z) (w := w) (a := 0) hφ
  have hspec := fieldLfppMetric_internal_eq_weylScaleOn ξ
    (bridgeBarrierField R φ) (0 : C(Rd d, ℝ)) U hU z w
  have hE : ENNReal.ofReal ‖w - z‖ ≤ E.internal U z w := by
    calc
      ENNReal.ofReal ‖w - z‖ ≤ ENNReal.ofReal (E.1 (z, w)) :=
        ENNReal.ofReal_le_ofReal (bridge_euclidean_le_fieldZero ξ z w)
      _ ≤ E.internal U z w := E.ofReal_le_internal U z w
  calc
    ENNReal.ofReal ‖w - z‖ ≤ E.internal U z w := hE
    _ = ENNReal.ofReal (Real.exp 0) * E.internal U z w := by simp
    _ ≤ weylScaleOn ξ (bridgeBarrierField R φ) E U z w := hscale
    _ = G.internal U z w := by simpa [E, G, sub_zero] using hspec.symm

private theorem bridge_modified_sphere_growth
    {R ξ : ℝ} (hR : 0 < R) (hξ : 0 < ξ) (φ : C(Rd d, ℝ)) :
    ∀ M : ℝ, ∃ S : ℝ, 0 < S ∧ ∀ v : Rd d, ‖v‖ = S →
      M < (fieldLfppMetric ξ (bridgeBarrierField R φ)).1 (0, v) := by
  intro M
  let G := fieldLfppMetric ξ (bridgeBarrierField R φ)
  have hG : G.IsLength := fieldLfppMetric_isLength ξ (bridgeBarrierField R φ)
  by_cases hM : M < 0
  · refine ⟨1, by norm_num, fun v hv => ?_⟩
    exact hM.trans_le (G.nonneg 0 v)
  · have hM0 : 0 ≤ M := le_of_not_gt hM
    let S : ℝ := R + M + 4
    have hS : 0 < S := by dsimp [S]; linarith
    refine ⟨S, hS, fun v hv => ?_⟩
    by_contra hdist
    have hdist' : G.1 (0, v) ≤ M := le_of_not_gt hdist
    have hR3 : 0 < R + 3 := by linarith
    obtain ⟨P, hPc, hP0, hP1, hPlen⟩ :=
      (ContMetric.isLength_iff_curves G).1 hG (0 : Rd d) v (1 / 2) (by norm_num)
    have hnorm : ContinuousOn (fun t : ℝ => ‖P t‖) (Icc (0 : ℝ) 1) := hPc.norm
    have hRmem : R + 3 ∈ Icc (‖P 0‖) (‖P 1‖) := by
      rw [hP0, hP1, hv]
      constructor
      · simpa using hR3.le
      · dsimp [S]
        linarith
    obtain ⟨u, hu, huval⟩ := intermediate_value_Icc zero_le_one hnorm hRmem
    let K : Set (Rd d) := {q | ‖q‖ = R + 3}
    have hK : IsClosed K := by
      change IsClosed {q : Rd d | ‖q‖ = R + 3}
      exact isClosed_eq continuous_norm continuous_const
    have hhit : ∃ t ∈ Icc (0 : ℝ) 1, P t ∈ K := by
      exact ⟨u, hu, by simpa [K] using huval⟩
    obtain ⟨s, hs, hsK, hlast⟩ := bridge_exists_last_hit_closed hPc hK hhit
    have hPs : ‖P s‖ = R + 3 := hsK
    have htail : ∀ t ∈ Ioc s 1, R + 3 < ‖P t‖ := by
      intro t ht
      by_contra hnot
      have hle : ‖P t‖ ≤ R + 3 := le_of_not_gt hnot
      have hnorm' : ContinuousOn (fun q : ℝ => ‖P q‖) (Icc t 1) :=
        hnorm.mono (Icc_subset_Icc (by linarith [hs.1, ht.1]) le_rfl)
      have hRmem' : R + 3 ∈ Icc (‖P t‖) (‖P 1‖) := by
        rw [hP1, hv]
        exact ⟨hle, by dsimp [S]; linarith⟩
      obtain ⟨u, hu, huval⟩ := intermediate_value_Icc ht.2 hnorm' hRmem'
      have hu' : u ∈ Ioc s 1 := ⟨lt_of_lt_of_le ht.1 hu.1, hu.2⟩
      exact hlast u hu' (by simpa [K] using huval)
    let U : Set (Rd d) := (Metric.closedBall 0 (R + 2))ᶜ
    have hmap : MapsTo P (Icc s 1) U := by
      intro t ht
      change P t ∉ Metric.closedBall (0 : Rd d) (R + 2)
      rw [Metric.mem_closedBall, dist_zero_right]
      by_cases hts : t = s
      · subst t
        rw [hPs]
        linarith
      · have hst : s < t := lt_of_le_of_ne ht.1 (Ne.symm hts)
        exact not_le_of_gt (lt_trans (by linarith) (htail t ⟨hst, ht.2⟩))
    have htailLen : G.internal U (P s) v ≤ G.len P s 1 := by
      have hcont : ContinuousOn P (Icc s 1) :=
        hPc.mono (Icc_subset_Icc hs.1 le_rfl)
      have h := G.internal_le_len (U := U) (P := P) (a := s) (b := 1) hs.2 hcont hmap
      rw [hP1] at h
      exact h
    have htotal : G.len P 0 1 ≤ ENNReal.ofReal (M + 1 / 2) := by
      calc
        G.len P 0 1 ≤ ENNReal.ofReal (G.1 (0, v)) + ENNReal.ofReal (1 / 2) := hPlen
        _ ≤ ENNReal.ofReal M + ENNReal.ofReal (1 / 2) :=
          by gcongr
        _ = ENNReal.ofReal (M + 1 / 2) := by
          rw [← ENNReal.ofReal_add hM0 (by norm_num)]
    have hlenmono : G.len P s 1 ≤ G.len P 0 1 := by
      change curveLength (G.pt ∘ P) s 1 ≤ curveLength (G.pt ∘ P) 0 1
      exact curveLength_mono (G.pt ∘ P) hs.1 le_rfl
    have hchord : M + 1 ≤ ‖v - P s‖ := by
      have htri := norm_le_norm_add_norm_sub' v (P s)
      rw [hv, hPs] at htri
      dsimp [S] at htri
      linarith
    have hlower : ENNReal.ofReal (M + 1) ≤ G.len P s 1 := by
      calc
        ENNReal.ofReal (M + 1) ≤ ENNReal.ofReal ‖v - P s‖ :=
          ENNReal.ofReal_le_ofReal hchord
        _ ≤ G.internal U (P s) v := by
          simpa [U, G] using bridge_modified_internal_ge_euclidean (R := R) hξ φ
            (P s) v (by rw [hPs]; linarith) (by rw [hv]; dsimp [S]; linarith)
        _ ≤ G.len P s 1 := htailLen
    have hlt : ENNReal.ofReal (M + (1 / 2 : ℝ)) < ENNReal.ofReal (M + 1) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
    exact (not_le_of_gt hlt) (hlower.trans (hlenmono.trans htotal))

/-- A strict path barrier at the sphere forces a unit-speed LFPP geodesic to exist inside the ball.
The barrier is stated for every continuous path segment starting at `x` and ending on the sphere.
-/
theorem fieldLfppMetric_exists_geodesic_of_barrier
    {R κ ξ : ℝ} (hR : 0 < R) (hξ : 0 < ξ) (hκ : 0 < κ)
    (φ : C(Rd d, ℝ)) (x y : Rd d) (hx : ‖x‖ < R) (hy : ‖y‖ < R)
    (hbarrier : ∀ {P : ℝ → Rd d} {a b : ℝ}, a ≤ b →
      ContinuousOn P (Icc a b) → P a = x → ‖P b‖ = R →
        ENNReal.ofReal ((fieldLfppMetric ξ φ).1 (x, y) + κ) <
          (fieldLfppMetric ξ φ).len P a b) :
    ∃ P : ℝ → Rd d,
      P 0 = x ∧ P ((fieldLfppMetric ξ φ).1 (x, y)) = y ∧
      IsGeodesicCurve ((fieldLfppMetric ξ φ).pt ∘ P) 0
        ((fieldLfppMetric ξ φ).1 (x, y)) ∧
      HasUnitSpeedOn ((fieldLfppMetric ξ φ).pt ∘ P)
        (Icc 0 ((fieldLfppMetric ξ φ).1 (x, y))) ∧
      ∀ t ∈ Icc 0 ((fieldLfppMetric ξ φ).1 (x, y)), ‖P t‖ < R := by
  let G := fieldLfppMetric ξ φ
  let φ' := bridgeBarrierField R φ
  let G' := fieldLfppMetric ξ φ'
  have hG : G.IsLength := fieldLfppMetric_isLength ξ φ
  have hG' : G'.IsLength := fieldLfppMetric_isLength ξ φ'
  have hL0 : 0 ≤ G.1 (x, y) := G.nonneg x y
  have hbarrierD : ∀ {P : ℝ → Rd d} {a b : ℝ}, a ≤ b →
      ContinuousOn P (Icc a b) → P a = x → ‖P b‖ = R →
        ENNReal.ofReal (G.1 (x, y) + κ) ≤ G.len P a b := by
    intro P a b hab hP h0 hR'
    exact (le_of_lt (hbarrier hab hP h0 hR')).trans_eq (by simp [G])
  have hglobal := internal_eq_global_of_barrier G hG hx hy
    (by dsimp [G]; linarith) hbarrierD
  have hlocal : ∀ z ∈ Metric.ball (0 : Rd d) R, ∀ w ∈ Metric.ball 0 R,
      G'.internal (Metric.ball 0 R) z w = G.internal (Metric.ball 0 R) z w := by
    intro z hz w hw
    apply l7a_fieldLfppMetric_internal_congr ξ φ' φ isOpen_ball
    intro q hq
    have hqn : ‖q‖ < R := by
      simpa only [Metric.mem_ball, dist_zero_right] using hq
    exact bridgeBarrierField_eq_on_ball (by linarith)
  have hdistENN : ENNReal.ofReal (G'.1 (x, y)) ≤ ENNReal.ofReal (G.1 (x, y)) := by
    calc
      ENNReal.ofReal (G'.1 (x, y)) ≤ G'.internal (Metric.ball 0 R) x y :=
        G'.ofReal_le_internal _ x y
      _ = G.internal (Metric.ball 0 R) x y := hlocal x (by simpa using hx) y (by simpa using hy)
      _ = ENNReal.ofReal (G.1 (x, y)) := hglobal
  have hdist : G'.1 (x, y) ≤ G.1 (x, y) :=
    (ENNReal.ofReal_le_ofReal_iff (G.nonneg x y)).1 hdistENN
  letI : ProperSpace G'.Space :=
    properSpace_of_sphere_growth G' hG' (bridge_modified_sphere_growth hR hξ φ)
  obtain ⟨P, h0, hT, hgeo', hu', hdist'⟩ := G'.exists_geodesic hG' x y
  let T : ℝ := G'.1 (x, y)
  have hTnonneg : 0 ≤ T := G'.nonneg x y
  have hPcont : ContinuousOn P (Icc 0 T) := by
    dsimp [T]
    exact G'.continuous_unpt.comp_continuousOn hgeo'.2.1
  have hPnorm : ContinuousOn (fun t : ℝ => ‖P t‖) (Icc 0 T) := hPcont.norm
  have hstay : ∀ t ∈ Icc (0 : ℝ) T, ‖P t‖ < R := by
    intro t ht
    by_contra hnot
    have hRle : R ≤ ‖P t‖ := le_of_not_gt hnot
    let K : Set (Rd d) := {q | R ≤ ‖q‖}
    have hK : IsClosed K := by
      change IsClosed {q : Rd d | R ≤ ‖q‖}
      exact isClosed_le continuous_const continuous_norm
    have hhit : ∃ u ∈ Icc (0 : ℝ) T, P u ∈ K := ⟨t, ht, by simpa [K] using hRle⟩
    obtain ⟨s, hs, hsK, hbefore⟩ :=
      LQGMetric.MetricGeometry.exists_first_hit hPcont hK hhit
    have hPsge : R ≤ ‖P s‖ := hsK
    have hPsle : ‖P s‖ ≤ R := by
      by_contra hnot'
      have hRlt : R < ‖P s‖ := lt_of_not_ge hnot'
      have hprefixNorm : ContinuousOn (fun u : ℝ => ‖P u‖) (Icc (0 : ℝ) s) :=
        hPnorm.mono (Icc_subset_Icc le_rfl hs.2)
      have hRmem : R ∈ Icc (‖P 0‖) (‖P s‖) := by
        rw [h0]
        exact ⟨by simpa using hx.le, hRlt.le⟩
      obtain ⟨u, hu, huval⟩ := intermediate_value_Icc hs.1 hprefixNorm hRmem
      have hus : u < s := by
        by_contra hus
        have hsu : s ≤ u := le_of_not_gt hus
        have heq : u = s := le_antisymm hu.2 hsu
        subst u
        linarith
      have hU : u ∈ Ico (0 : ℝ) s := ⟨hu.1, hus⟩
      have hnotK := hbefore u hU
      exact hnotK (by simpa [K, huval])
    have hPs : ‖P s‖ = R := le_antisymm hPsle hPsge
    have hprefixMap : MapsTo P (Icc (0 : ℝ) s) (Metric.ball 0 (R + 1)) := by
      intro u hu
      have hbound : ‖P u‖ ≤ R := by
        by_cases hus : u = s
        · subst u
          exact hPs.le
        · have hus' : u < s := lt_of_le_of_ne hu.2 hus
          have hnotK := hbefore u ⟨hu.1, hus'⟩
          exact le_of_lt (lt_of_not_ge (by simpa [K] using hnotK))
      simpa only [Metric.mem_ball, dist_zero_right] using (show ‖P u‖ < R + 1 by linarith)
    have hPprefix : ContinuousOn P (Icc (0 : ℝ) s) :=
      hPcont.mono (Icc_subset_Icc le_rfl hs.2)
    have hbar := hbarrierD (P := P) (a := 0) (b := s) hs.1 hPprefix h0 hPs
    have hlenEq := bridgeBarrierField_len_eq (R := R) (ξ := ξ) φ hPprefix hprefixMap
    have hlenPrefixLe : G'.len P 0 s ≤ G'.len P 0 T := by
      change curveLength (G'.pt ∘ P) 0 s ≤ curveLength (G'.pt ∘ P) 0 T
      exact curveLength_mono (G'.pt ∘ P) le_rfl hs.2
    have hlenTotal : G'.len P 0 T = ENNReal.ofReal T := by
      change curveLength (G'.pt ∘ P) 0 T = ENNReal.ofReal T
      simpa only [sub_zero] using curveLength_of_hasUnitSpeedOn hu'
        ⟨le_rfl, hTnonneg⟩ ⟨hTnonneg, le_rfl⟩
    have hTleL0 : T ≤ G.1 (x, y) := by simpa [T, G] using hdist
    have hbar' : ENNReal.ofReal (G.1 (x, y) + κ) < G'.len P 0 s := by
      calc
        ENNReal.ofReal (G.1 (x, y) + κ) < G.len P 0 s :=
          hbarrier (a := 0) (b := s) hs.1 hPprefix h0 hPs
        _ = G'.len P 0 s := hlenEq.symm
    have hshift : ENNReal.ofReal (G.1 (x, y)) < ENNReal.ofReal (G.1 (x, y) + κ) :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith [G.nonneg x y])).2 (by linarith)
    have hupper : G'.len P 0 s ≤ ENNReal.ofReal (G.1 (x, y)) := by
      calc
        G'.len P 0 s ≤ G'.len P 0 T := hlenPrefixLe
        _ = ENNReal.ofReal T := hlenTotal
        _ ≤ ENNReal.ofReal (G.1 (x, y)) := ENNReal.ofReal_le_ofReal hTleL0
    exact (not_lt_of_ge hshift.le) (hbar'.trans_le hupper)
  have hstayMap : MapsTo P (Icc (0 : ℝ) T) (Metric.ball 0 (R + 1)) := by
    intro t ht
    simpa only [Metric.mem_ball, dist_zero_right] using
      (show ‖P t‖ < R + 1 by linarith [hstay t ht])
  have hlenEq := bridgeBarrierField_len_eq (R := R) (ξ := ξ) φ hPcont hstayMap
  have hlenG : G.len P 0 T = ENNReal.ofReal T := by
    calc
      G.len P 0 T = G'.len P 0 T := hlenEq.symm
      _ = ENNReal.ofReal T := by
        change curveLength (G'.pt ∘ P) 0 T = ENNReal.ofReal T
        simpa only [sub_zero] using curveLength_of_hasUnitSpeedOn hu'
          ⟨le_rfl, hTnonneg⟩ ⟨hTnonneg, le_rfl⟩
  have hL0leT : G.1 (x, y) ≤ T := by
    have hdistLen : ENNReal.ofReal (G.1 (x, y)) ≤ G.len P 0 T := by
      calc
        ENNReal.ofReal (G.1 (x, y)) = edist (G.pt x) (G.pt y) := by rw [G.edist_pt]
        _ = edist (G.pt (P 0)) (G.pt (P T)) := by rw [h0, show P T = y by simpa [T] using hT]
        _ ≤ G.len P 0 T := by
          change edist (G.pt (P 0)) (G.pt (P T)) ≤ curveLength (G.pt ∘ P) 0 T
          exact edist_le_curveLength (G.pt ∘ P) hTnonneg
    exact (ENNReal.ofReal_le_ofReal_iff hTnonneg).1 (hdistLen.trans_eq hlenG)
  have hT_eq : T = G.1 (x, y) := le_antisymm (by simpa [T, G] using hdist) hL0leT
  have hpair_le : ∀ {s t : ℝ}, s ∈ Icc (0 : ℝ) T → t ∈ Icc (0 : ℝ) T → s ≤ t →
      G.1 (P s, P t) = t - s := by
    intro s t hs ht hst
    have hlenSubEq := bridgeBarrierField_len_eq (R := R) (ξ := ξ) φ hPcont hstayMap
    have hlenSub : G.len P s t = ENNReal.ofReal (t - s) := by
      calc
        G.len P s t = G'.len P s t := by
          exact (bridgeBarrierField_len_eq (R := R) (ξ := ξ) φ
            (hPcont.mono (Icc_subset_Icc hs.1 ht.2))
            (fun u hu => hstayMap ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩)).symm
        _ = ENNReal.ofReal (t - s) := curveLength_of_hasUnitSpeedOn hu' hs ht
    have hupper : G.1 (P s, P t) ≤ t - s := by
      have h : edist (G.pt (P s)) (G.pt (P t)) ≤ G.len P s t := by
        change edist (G.pt (P s)) (G.pt (P t)) ≤ curveLength (G.pt ∘ P) s t
        exact edist_le_curveLength (G.pt ∘ P) hst
      rw [G.edist_pt, hlenSub] at h
      exact (ENNReal.ofReal_le_ofReal_iff (by linarith [hst])).1 h
    have hsUpper : G.1 (x, P s) ≤ s := by
      have hlen := bridgeBarrierField_len_eq (R := R) (ξ := ξ) φ
        (hPcont.mono (Icc_subset_Icc le_rfl hs.2))
        (fun u hu => hstayMap ⟨hu.1, hu.2.trans hs.2⟩)
      have hlenG0s : G.len P 0 s = ENNReal.ofReal s := by
        calc
          G.len P 0 s = G'.len P 0 s := hlen.symm
          _ = ENNReal.ofReal (s - 0) := curveLength_of_hasUnitSpeedOn hu'
            ⟨le_rfl, hTnonneg⟩ hs
          _ = ENNReal.ofReal s := by simp
      have h : ENNReal.ofReal (G.1 (x, P s)) ≤ ENNReal.ofReal s := by
        calc
          ENNReal.ofReal (G.1 (x, P s)) = edist (G.pt x) (G.pt (P s)) := by rw [G.edist_pt]
          _ = edist (G.pt (P 0)) (G.pt (P s)) := by rw [h0]
          _ ≤ G.len P 0 s := by
            change edist (G.pt (P 0)) (G.pt (P s)) ≤ curveLength (G.pt ∘ P) 0 s
            exact edist_le_curveLength (G.pt ∘ P) hs.1
          _ = ENNReal.ofReal s := hlenG0s
      exact (ENNReal.ofReal_le_ofReal_iff (by linarith [hs.1])).1 h
    have htUpper : G.1 (P t, y) ≤ T - t := by
      have hlen := bridgeBarrierField_len_eq (R := R) (ξ := ξ) φ
        (hPcont.mono (Icc_subset_Icc ht.1 le_rfl))
        (fun u hu => hstayMap ⟨ht.1.trans hu.1, hu.2⟩)
      have hlenGtT : G.len P t T = ENNReal.ofReal (T - t) := by
        calc
          G.len P t T = G'.len P t T := hlen.symm
          _ = ENNReal.ofReal (T - t) := curveLength_of_hasUnitSpeedOn hu' ht
            ⟨hTnonneg, le_rfl⟩
      have h : ENNReal.ofReal (G.1 (P t, y)) ≤ ENNReal.ofReal (T - t) := by
        calc
          ENNReal.ofReal (G.1 (P t, y)) = edist (G.pt (P t)) (G.pt y) := by rw [G.edist_pt]
          _ = edist (G.pt (P t)) (G.pt (P T)) := by rw [show P T = y by simpa [T] using hT]
          _ ≤ G.len P t T := by
            change edist (G.pt (P t)) (G.pt (P T)) ≤ curveLength (G.pt ∘ P) t T
            exact edist_le_curveLength (G.pt ∘ P) ht.2
          _ = ENNReal.ofReal (T - t) := hlenGtT
      exact (ENNReal.ofReal_le_ofReal_iff (by linarith [ht.2])).1 h
    have htriangle : G.1 (x, y) ≤ G.1 (x, P s) + G.1 (P s, P t) + G.1 (P t, y) := by
      calc
        G.1 (x, y) ≤ G.1 (x, P s) + G.1 (P s, y) := G.apply_triangle x (P s) y
        _ ≤ G.1 (x, P s) + (G.1 (P s, P t) + G.1 (P t, y)) := by
          exact add_le_add_right (G.apply_triangle (P s) (P t) y) _
        _ = G.1 (x, P s) + G.1 (P s, P t) + G.1 (P t, y) := by ring
    apply le_antisymm hupper
    linarith [htriangle, hsUpper, htUpper, hT_eq]
  have hpair : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      G.1 (P s, P t) = |t - s| := by
    intro s hs t ht
    by_cases hst : s ≤ t
    · rw [abs_of_nonneg (sub_nonneg.mpr hst)]
      exact hpair_le hs ht hst
    · have hts : t ≤ s := le_of_not_ge hst
      calc
        G.1 (P s, P t) = G.1 (P t, P s) := G.apply_comm (P s) (P t)
        _ = s - t := hpair_le ht hs hts
        _ = |t - s| := by rw [abs_of_nonpos (sub_nonpos.mpr hts)]; ring
  have hEdist : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      edist (G.pt (P s)) (G.pt (P t)) = edist s t := by
    intro s hs t ht
    calc
      edist (G.pt (P s)) (G.pt (P t)) = ENNReal.ofReal (G.1 (P s, P t)) := G.edist_pt _ _
      _ = ENNReal.ofReal |t - s| := by rw [hpair s hs t ht]
      _ = edist s t := by rw [edist_dist, Real.dist_eq]; simp [abs_sub_comm]
  have hEdist0 : ∀ s ∈ Icc (0 : ℝ) (G.1 (x, y)), ∀ t ∈ Icc (0 : ℝ) (G.1 (x, y)),
      edist (G.pt (P s)) (G.pt (P t)) = edist s t := by
    intro s hs t ht
    apply hEdist s (by simpa [hT_eq] using hs) t
    simpa [hT_eq] using ht
  have hgeoG := LQGMetric.MetricGeometry.isGeodesicCurve_of_edist_eq hL0 hEdist0
  have hstay0 : ∀ t ∈ Icc (0 : ℝ) (G.1 (x, y)), ‖P t‖ < R := by
    intro t ht
    exact hstay t (by simpa [hT_eq] using ht)
  have hPend : P (G.1 (x, y)) = y := by simpa [T, hT_eq, G, G'] using hT
  exact ⟨P, h0, hPend, hgeoG.1, hgeoG.2, hstay0⟩

end HigherDimLFPPAS.Bridge
