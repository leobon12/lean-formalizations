import SupercriticalLQGUniqueness.B2.PfeLocal.L5Minimizer
import SupercriticalLQGUniqueness.B2.PfeLocal.CirclePath

 


















set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open Uniqueness.Toolkit.CompactPathInfimum LQGMetric.LM

 
def l5Circ (q : ℚ × ℚ × ℚ) : Set ℂ := sphere ⟨q.1, q.2.1⟩ (q.2.2 : ℝ)

theorem l5Circ_isRationalCircle (q : ℚ × ℚ × ℚ) (hq : 0 ≤ q.2.2) :
    Iface.IsRationalCircle (l5Circ q) :=
  ⟨q.1, q.2.1, q.2.2, hq, rfl⟩

 
def L5Geo (D : LSCMetric) : Prop :=
  (∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
      ∀ v : ℂ, D.1 (u, v) < ENNReal.ofReal η → dist u v < δ) ∧
    (∀ u v : ℂ, D.1 (u, v) < ∞ → ∃ (γ : ℝ → ℂ) (a b : ℝ),
      D.IsCurve γ a b ∧ γ a = u ∧ γ b = v ∧ D.len γ a b = D.1 (u, v))

 
theorem l5_setDistance_spheres_le_len (D : LSCMetric) (P : ℝ → ℂ) {a b r : ℝ} {c d : ℂ}
    (hP : D.IsCurve P a b) (hcont : ContinuousOn P (Icc a b)) (hr : 0 < r)
    (ha : dist (P a) c < r / 2) (hb : dist (P b) d < r / 2) (hsep : 5 * r < dist (P a) (P b)) :
    Iface.setDistance D.1 (sphere c r) (sphere d r) ≤ D.len P a b := by
  have hr2 : r < 2 * r := by linarith
  have hstart : dist (P a) c < r := by linarith
  have hend : 2 * r < dist (P b) c := by
    have := dist_triangle (P a) c (P b)
    rw [dist_comm c (P b)] at this
    linarith
  obtain ⟨σ, τ, haσ, hστ, hτb, hσc, -, -⟩ := crossing_extract hP.1 hcont hr2 hstart hend
  have hσd : 2 * r < dist (P σ) d := by
    have h1 := dist_triangle (P a) (P σ) (P b)
    have h2 := dist_triangle (P σ) d (P b)
    have h3 := dist_triangle (P a) c (P σ)
    rw [dist_comm c (P σ), hσc] at h3
    rw [dist_comm d (P b)] at h2
    linarith
  have hlast : dist (P b) d < r := by linarith
  have hcont' : ContinuousOn P (Icc σ b) :=
    hcont.mono fun t ht => ⟨haσ.trans ht.1, ht.2⟩
  obtain ⟨σ', τ', hσσ', hσ'τ', hτ'b, -, hτ'd, -⟩ :=
    crossing_extract_reverse (hστ.le.trans hτb) hcont' hr2 hσd hlast
  have hστ' : σ ≤ τ' := hσσ'.trans hσ'τ'.le
  have hlen : D.1 (P σ, P τ') ≤ D.len P a b :=
    calc D.1 (P σ, P τ') ≤ D.len P σ τ' :=
          LQGMetric.MetricGeometry.edist_le_curveLength (D.pt ∘ P) hστ'
      _ ≤ D.len P a b := eVariationOn.mono _ (Icc_subset_Icc haσ hτ'b)
  unfold Iface.setDistance
  exact (iInf_le_of_le (P σ) <| iInf_le_of_le (mem_sphere.mpr hσc) <|
    iInf_le_of_le (P τ') <| iInf_le_of_le (mem_sphere.mpr hτ'd) le_rfl).trans hlen

 
def l5CircApprox (x : ℂ) (n : ℕ) : ℚ × ℚ × ℚ :=
  ((l5ApproxBall x (2 * n + 2)).1, (l5ApproxBall x (2 * n + 2)).2.1, 1 / ((n : ℚ) + 1))

theorem l5CircApprox_radius (x : ℂ) (n : ℕ) :
    (((l5CircApprox x n).2.2 : ℚ) : ℝ) = 1 / ((n : ℝ) + 1) := by
  show ((1 / ((n : ℚ) + 1) : ℚ) : ℝ) = _
  push_cast
  ring

theorem l5CircApprox_center (x : ℂ) (n : ℕ) :
    dist x ⟨((l5CircApprox x n).1 : ℝ), ((l5CircApprox x n).2.1 : ℝ)⟩ <
      (1 / ((n : ℝ) + 1)) / 2 := by
  have h := l5ApproxBall_center_dist x (2 * n + 2)
  have : 1 / (((2 * n + 2 : ℕ) : ℝ) + 1) < (1 / ((n : ℝ) + 1)) / 2 := by
    push_cast
    rw [div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  exact h.trans_lt this

theorem l5Circ_approx_subset (x : ℂ) (n : ℕ) :
    l5Circ (l5CircApprox x n) ⊆ ball x (2 * (1 / ((n : ℝ) + 1))) := by
  intro z hz
  rw [l5Circ, mem_sphere, l5CircApprox_radius] at hz
  rw [mem_ball]
  have := l5CircApprox_center x n
  have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
  calc dist z x ≤ dist z _ + dist _ x := dist_triangle z _ x
    _ < 1 / ((n : ℝ) + 1) + (1 / ((n : ℝ) + 1)) / 2 := by
        rw [hz, dist_comm]; linarith
    _ ≤ 2 * (1 / ((n : ℝ) + 1)) := by linarith

 

theorem l5_edist_le_of_circles (D D' : LSCMetric) (hgeo : L5Geo D) (K : ℝ≥0∞) (hK0 : K ≠ 0)
    (hcmp : ∀ q q' : ℚ × ℚ × ℚ, Iface.setDistance D'.1 (l5Circ q) (l5Circ q') ≤
      K * Iface.setDistance D.1 (l5Circ q) (l5Circ q')) (x y : ℂ) :
    D'.1 (x, y) ≤ K * D.1 (x, y) := by
  by_contra hnot
  have hlt : K * D.1 (x, y) < D'.1 (x, y) := lt_of_not_ge hnot
  have hfin : D.1 (x, y) < ∞ := by
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h, ENNReal.mul_top hK0] at hlt
    exact not_top_lt hlt
  have hxy : x ≠ y := by
    rintro rfl
    rw [D'.isExtMetric.1 x] at hlt
    exact not_lt_zero' hlt
  obtain ⟨P, a, b, hP, hPa, hPb, hPlen⟩ := hgeo.2 x y hfin
  have hcont := continuousOn_euclidean_of_small_metric D hgeo.1 P hP
  have hrn : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hshrink : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      l5Circ (l5CircApprox x n) ⊆ ball x ε ∧ l5Circ (l5CircApprox y n) ⊆ ball y ε := by
    intro ε hε
    filter_upwards [hrn.eventually (gt_mem_nhds (half_pos hε))] with n hn
    exact ⟨(l5Circ_approx_subset x n).trans (ball_subset_ball (by linarith)),
      (l5Circ_approx_subset y n).trans (ball_subset_ball (by linarith))⟩
  have hne : ∀ z : ℂ, ∀ n, (l5Circ (l5CircApprox z n)).Nonempty := fun z n => by
    rw [l5Circ, l5CircApprox_radius]
    exact NormedSpace.sphere_nonempty.2 (by positivity)
  have hlow := eventually_lt_setDistance_of_shrinking D'
    (fun n => l5Circ (l5CircApprox x n)) (fun n => l5Circ (l5CircApprox y n)) x y
    (fun n => isCompact_sphere _ _) (fun n => isCompact_sphere _ _) (hne x) (hne y)
    hshrink hlt
  have hdxy : 0 < dist x y := dist_pos.mpr hxy
  have hsep : ∀ᶠ n : ℕ in atTop, 5 * (1 / ((n : ℝ) + 1)) < dist x y := by
    filter_upwards [hrn.eventually (gt_mem_nhds (show 0 < dist x y / 5 by positivity))] with n hn
    linarith
  obtain ⟨n, hnlow, hnsep⟩ := (hlow.and hsep).exists
  have hupper : Iface.setDistance D.1 (l5Circ (l5CircApprox x n)) (l5Circ (l5CircApprox y n)) ≤
      D.1 (x, y) := by
    rw [← hPlen, l5Circ, l5Circ, l5CircApprox_radius, l5CircApprox_radius]
    refine l5_setDistance_spheres_le_len D P hP hcont (by positivity) ?_ ?_ ?_
    · rw [hPa]; exact l5CircApprox_center x n
    · rw [hPb]; exact l5CircApprox_center y n
    · rw [hPa, hPb]; exact hnsep
  have hKup : K * Iface.setDistance D.1 (l5Circ (l5CircApprox x n)) (l5Circ (l5CircApprox y n)) ≤
      K * D.1 (x, y) := by gcongr
  have := (hcmp (l5CircApprox x n) (l5CircApprox y n)).trans hKup
  exact (not_lt_of_ge this) hnlow

 
def l5CircDist (D : LSCMetric) (q q' : ℚ × ℚ × ℚ) : ℝ≥0∞ :=
  Iface.setDistance D.1 (l5Circ q) (l5Circ q')

 
theorem l5_good_set {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (L : Ω → LSCMetric) (K : ℝ≥0) (hK : 1 ≤ K) (hgeo : ∀ᵐ ω ∂ν, L5Geo (L ω))
    (hpair : ∀ᵐ ω₂ ∂ν, ∀ᵐ ω₁ ∂ν, ∀ q q' : ℚ × ℚ × ℚ,
      l5CircDist (L ω₂) q q' ≤ K * l5CircDist (L ω₁) q q') :
    ∃ G : Set Ω, (∀ᵐ ω ∂ν, ω ∈ G) ∧ ∀ ω₁ ∈ G, ∀ ω₂ ∈ G,
      L5Geo (L ω₁) ∧ ∀ x y, (L ω₂).1 (x, y) ≤ K * (L ω₁).1 (x, y) := by
  have hK0 : (K : ℝ≥0∞) ≠ 0 := by
    have : (0 : ℝ≥0) < K := lt_of_lt_of_le one_pos hK
    exact_mod_cast this.ne'
  have hKt : (K : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  set c : ℚ × ℚ × ℚ → ℚ × ℚ × ℚ → ℝ≥0∞ := fun q q' =>
    essInf (fun ω => l5CircDist (L ω) q q') ν
  have hlow : ∀ᵐ ω ∂ν, ∀ q q' : ℚ × ℚ × ℚ, c q q' ≤ l5CircDist (L ω) q q' := by
    refine ae_all_iff.2 fun q => ae_all_iff.2 fun q' => ?_
    exact ae_essInf_le
  have hup : ∀ᵐ ω ∂ν, ∀ q q' : ℚ × ℚ × ℚ, l5CircDist (L ω) q q' ≤ K * c q q' := by
    filter_upwards [hpair] with ω₂ hω₂
    intro q q'
    have h1 : (fun _ => l5CircDist (L ω₂) q q' / K) ≤ᵐ[ν]
        fun ω => l5CircDist (L ω) q q' := by
      filter_upwards [hω₂] with ω₁ h
      exact ENNReal.div_le_of_le_mul (by rw [mul_comm]; exact h q q')
    have h2 := le_essInf_of_ae_le _ h1
    rw [ENNReal.div_le_iff hK0 hKt, mul_comm] at h2
    exact h2
  refine ⟨{ω | L5Geo (L ω) ∧ ∀ q q' : ℚ × ℚ × ℚ,
      c q q' ≤ l5CircDist (L ω) q q' ∧ l5CircDist (L ω) q q' ≤ K * c q q'}, ?_, ?_⟩
  · filter_upwards [hgeo, hlow, hup] with ω h1 h2 h3
    exact ⟨h1, fun q q' => ⟨h2 q q', h3 q q'⟩⟩
  · rintro ω₁ ⟨hg₁, hs₁⟩ ω₂ ⟨-, hs₂⟩
    refine ⟨hg₁, l5_edist_le_of_circles (L ω₁) (L ω₂) hg₁ K hK0 (fun q q' => ?_)⟩
    have h := (hs₁ q q').1
    calc l5CircDist (L ω₂) q q' ≤ K * c q q' := (hs₂ q q').2
      _ ≤ K * l5CircDist (L ω₁) q q' := by gcongr

 
theorem l5_compactPathInf_le_mul {D D' : LSCMetric} (K : ℝ≥0) (hK : 1 ≤ K)
    (hle : ∀ x y, D'.1 (x, y) ≤ K * D.1 (x, y)) (S E F : Set ℂ) :
    compactPathInf D' S E F ≤ K * compactPathInf D S E F := by
  have hK0 : (K : ℝ≥0∞) ≠ 0 := by
    have : (0 : ℝ≥0) < K := lt_of_lt_of_le one_pos hK
    exact_mod_cast this.ne'
  by_contra hnot
  have hlt : (K : ℝ≥0∞) * compactPathInf D S E F < compactPathInf D' S E F := lt_of_not_ge hnot
  have hlt' : compactPathInf D S E F < compactPathInf D' S E F / K :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl hK0) (Or.inl ENNReal.coe_ne_top)).2 (by
      rw [mul_comm]; exact hlt)
  unfold compactPathInf at hlt'
  obtain ⟨P, a, b, hP, htr, hEa, hFb, hcost⟩ := (by simpa only [iInf_lt_iff] using hlt')
  let ι : D.Space → D'.Space := fun x => x
  have hlip : LipschitzWith K ι := fun x y => by
    change D' (x, y) ≤ (K : ℝ≥0∞) * D (x, y)
    exact hle x y
  have hP' : D'.IsCurve P a b := ⟨hP.1, hlip.continuous.comp_continuousOn hP.2⟩
  have hlen : D'.len P a b ≤ K * D.len P a b :=
    t17_eVariationOn_le_mul fun x _ y _ => hle (P x) (P y)
  have h1 : compactPathInf D' S E F ≤ D'.len P a b :=
    l5_compactPathInf_le D' P a b hP' htr hEa hFb
  have h2 : (K : ℝ≥0∞) * D.len P a b < compactPathInf D' S E F := by
    calc (K : ℝ≥0∞) * D.len P a b < K * (compactPathInf D' S E F / K) :=
          (ENNReal.mul_lt_mul_iff_right hK0 ENNReal.coe_ne_top).2 hcost
      _ ≤ compactPathInf D' S E F := ENNReal.mul_div_le
  exact (not_lt_of_ge (h1.trans hlen)) h2

end SupercriticalLQGUniqueness.B2.PfeLocal
