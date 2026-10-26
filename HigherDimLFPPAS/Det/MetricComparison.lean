import HigherDimLFPPAS.Det.InternalBound
import HigherDimLFPPAS.Det.PathRecovery

/-!
# Multiplicative comparison of internal metrics
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Det

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Local uniform convergence of metrics gives uniform error on any compact endpoint set. -/
theorem eventually_uniform_metric_error_on_compact
    (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
      (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R))
    {F : Set (Rd d)} (hF : IsCompact F) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ F, ∀ y ∈ F,
      |(Dn n).1 (x,y) - D.1 (x,y)| < ε := by
  obtain ⟨R₀, hFball₀⟩ := hF.isBounded.subset_ball (0 : Rd d)
  let R := max R₀ 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hFball : F ⊆ closedBall (0 : Rd d) R := by
    intro x hx
    exact closedBall_subset_closedBall (le_max_left _ _) (ball_subset_closedBall (hFball₀ hx))
  have hev : ∀ᶠ n : ℕ in atTop, ∀ x ∈ closedBall (0 : Rd d) R,
      ∀ y ∈ closedBall (0 : Rd d) R,
        |(Dn n).1 (x,y) - D.1 (x,y)| < ε := by
    have h := (Metric.tendstoUniformlyOn_iff).1 (hconv R hR) ε hε
    filter_upwards [h] with n hn x hx y hy
    have hxy := hn (x,y) ⟨hx,hy⟩
    simpa [Real.dist_eq, abs_sub_comm] using hxy
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  exact ⟨N, fun n hn x hx y hy => hN n hn x (hFball hx) y (hFball hy)⟩

/-- On a compact set, small distance in `D` forces small Euclidean separation. -/
theorem exists_metric_threshold_for_euclidean
    (D : ContMetric d) {F : Set (Rd d)} (hF : IsCompact F)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ α : ℝ, 0 < α ∧ ∀ x ∈ F, ∀ y ∈ F,
      D.1 (x,y) < α → dist x y < δ := by
  let K : Set D.Space := D.pt '' F
  have hK : IsCompact K := hF.image D.continuous_pt
  have hUC : UniformContinuousOn D.unpt K :=
    hK.uniformContinuousOn_of_continuous D.continuous_unpt.continuousOn
  obtain ⟨α, hα, hsmall⟩ := (Metric.uniformContinuousOn_iff.mp hUC) δ hδ
  refine ⟨α, hα, ?_⟩
  intro x hx y hy hxy
  have hxy' : dist (D.pt x) (D.pt y) < α := by simpa [D.dist_pt] using hxy
  have h := hsmall (D.pt x) ⟨x, hx, rfl⟩ (D.pt y) ⟨y, hy, rfl⟩ hxy'
  simpa using h

/-- The deterministic comparison in Lemma 2.1, with both estimates on one eventual tail. -/
theorem eventually_internal_multiplicative_comparison
    (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hDn : ∀ n, (Dn n).IsLength) (hD : D.IsLength)
    (hconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
      (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R))
    {U F : Set (Rd d)} (hU : IsOpen U) (hUc : IsConnected U)
    (hF : IsCompact F) (hFU : F ⊆ U)
    {a η : ℝ} (ha : 0 < a) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ F, ∀ y ∈ F, a ≤ dist x y →
      (Dn n).internal U x y ≤ ENNReal.ofReal (1 + η) * D.internal F x y ∧
      D.internal U x y ≤ ENNReal.ofReal (1 + η) * (Dn n).internal F x y := by
  classical
  obtain ⟨δ₁, hδ₁, N₁, hlocal₁⟩ :=
    eventually_internal_eq_global_on_compact Dn D hDn hconv hU hF hFU
  have hconvConst : ∀ R : ℝ, 0 < R →
      TendstoUniformlyOn (fun _ : ℕ => ⇑D.1) ⇑D.1 atTop
        (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) := by
    intro R hR
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [] with n x hx
    simp only [dist_self]
    exact hε
  obtain ⟨δ₂, hδ₂, N₂, hlocal₂⟩ :=
    eventually_internal_eq_global_on_compact (fun _ : ℕ => D) D (fun _ => hD)
      hconvConst hU hF hFU
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  obtain ⟨α, hα, hEeucl⟩ := exists_metric_threshold_for_euclidean D hF hδ
  obtain ⟨αsep, hαsep, hsep⟩ := exists_metric_threshold_for_euclidean D hF ha
  let m := αsep / 4
  have hm : 0 < m := by dsimp [m]; positivity
  let τ := η * m / 8
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let q := α / 4
  have hq : 0 < q := by dsimp [q]; positivity
  let c := τ / q + 1
  have hc : 0 < c := by dsimp [c]; positivity
  let e := min (q / 2) (min (η * q / 4) (min (m / 4) (η * m / (4 * c))))
  have he : 0 < e := by
    dsimp [e]
    repeat' apply lt_min
    all_goals positivity
  have heq : e ≤ q / 2 := min_le_left _ _
  have heηq : e ≤ η * q / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hem : e ≤ m / 4 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have heηm : e ≤ η * m / (4 * c) := by
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have heα : e < α / 4 := by
    dsimp [q] at heq ⊢
    linarith
  have hemhalf : e < m / 2 := by linarith
  have hcoef : e / q ≤ η / 2 := by
    apply (div_le_iff₀ hq).2
    nlinarith [heηq]
  have hres : τ + c * e ≤ η * m / 2 := by
    have hce : c * e ≤ η * m / 4 := by
      calc c * e ≤ c * (η * m / (4 * c)) := mul_le_mul_of_nonneg_left heηm hc.le
        _ = η * m / 4 := by field_simp [ne_of_gt hc]
    dsimp [τ, c] at hce ⊢
    nlinarith
  obtain ⟨Nerr, herr⟩ := eventually_uniform_metric_error_on_compact Dn D hconv hF he
  let N := max (max N₁ N₂) Nerr
  refine ⟨N, ?_⟩
  intro n hn x hx y hy hxysep
  have hn₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn₂ : N₂ ≤ n :=
    le_trans (le_trans (le_max_right N₁ N₂) (le_max_left (max N₁ N₂) Nerr)) hn
  have hnerr : Nerr ≤ n := le_trans (le_max_right (max N₁ N₂) Nerr) hn
  have herror := herr n hnerr x hx y hy
  have hDsep : m ≤ D.1 (x,y) := by
    have hnot : ¬ D.1 (x,y) < αsep := by
      intro hlt
      have heuc := hsep x hx y hy hlt
      exact (not_lt_of_ge hxysep) heuc
    have hstrong : αsep ≤ D.1 (x,y) := le_of_not_gt hnot
    dsimp [m]
    linarith
  have hDsepStrong : αsep ≤ D.1 (x,y) := by
    have hnot : ¬ D.1 (x,y) < αsep := by
      intro hlt
      have heuc := hsep x hx y hy hlt
      exact (not_lt_of_ge hxysep) heuc
    exact le_of_not_gt hnot
  have hDnlo : m ≤ (Dn n).1 (x,y) := by
    have herr' := abs_lt.mp herror
    dsimp [m] at hDsep hem ⊢
    linarith [hDsepStrong, hem]
  have hDnup : (Dn n).1 (x,y) ≤ D.1 (x,y) + e := by
    have := (abs_lt.mp herror).2
    linarith
  have hDup : D.1 (x,y) ≤ (Dn n).1 (x,y) + e := by
    have := (abs_lt.mp herror).1
    linarith
  have hDnupAll : ∀ z ∈ F, ∀ w ∈ F, (Dn n).1 (z,w) ≤ D.1 (z,w) + e := by
    intro z hz w hw
    have hh := (abs_lt.mp (herr n hnerr z hz w hw)).2
    linarith
  have hDupAll : ∀ z ∈ F, ∀ w ∈ F, D.1 (z,w) ≤ (Dn n).1 (z,w) + e := by
    intro z hz w hw
    have hh := (abs_lt.mp (herr n hnerr z hz w hw)).1
    linarith
  have hlocalDn : ∀ z ∈ F, ∀ w ∈ F, dist z w < δ →
      (Dn n).internal U z w = ENNReal.ofReal ((Dn n).1 (z,w)) := by
    intro z hz w hw hzw
    exact hlocal₁ n (hn₁) z hz w hw (hzw.trans_le (min_le_left _ _))
  have hlocalD : ∀ z ∈ F, ∀ w ∈ F, dist z w < δ →
      D.internal U z w = ENNReal.ofReal (D.1 (z,w)) := by
    intro z hz w hw hzw
    exact hlocal₂ n hn₂ z hz w hw (hzw.trans_le (min_le_right _ _))
  have hrealBound : ∀ v : ℝ, m ≤ v → 0 ≤ v →
      v + τ + ((v + τ) / q + 1) * e ≤ (1 + η) * v := by
    intro v hmv hv
    have hrate : (v / q) * e ≤ (η / 2) * v := by
      calc (v / q) * e = v * (e / q) := by ring
        _ ≤ v * (η / 2) := mul_le_mul_of_nonneg_left hcoef hv
        _ = (η / 2) * v := by ring
    have hsplit : ((v + τ) / q + 1) * e = (v / q) * e + c * e := by
      dsimp [c]
      ring
    rw [hsplit]
    dsimp [q] at hres hrate ⊢
    nlinarith [hres, hrate, hmv, hv]
  constructor
  · by_cases htop : D.internal F x y = ∞
    · have hpos : 0 < ENNReal.ofReal (1 + η) := ENNReal.ofReal_pos.mpr (by linarith)
      calc (Dn n).internal U x y ≤ ⊤ := le_top
        _ = ENNReal.ofReal (1 + η) * D.internal F x y := by
          rw [htop, ENNReal.mul_top hpos.ne']
    · have hfin : D.internal F x y ≠ ∞ := htop
      have hlow : ENNReal.ofReal m ≤ D.internal F x y := by
        calc ENNReal.ofReal m ≤ ENNReal.ofReal (D.1 (x,y)) := ENNReal.ofReal_le_ofReal hDsep
          _ ≤ D.internal F x y := D.ofReal_le_internal F x y
      have hlow' : m ≤ (D.internal F x y).toReal := by
        have hh : ENNReal.ofReal m ≤ ENNReal.ofReal (D.internal F x y).toReal := by
          simpa only [ENNReal.ofReal_toReal hfin] using hlow
        exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hh
      have hrec := recover_internal_upper_bound D (Dn n) D hD hF hFU
        (α := α) (δ := δ) (e := e) (τ := τ) hα hδ he.le heα hτ
        (fun z hz w hw hzw => hEeucl z hz w hw hzw)
        (fun z hz w hw => le_add_of_nonneg_right (le_of_lt he))
        hDnupAll
        hlocalDn hx hy hfin
      have hreal := hrealBound _ hlow' ENNReal.toReal_nonneg
      calc (Dn n).internal U x y ≤ _ := hrec
        _ ≤ ENNReal.ofReal ((1 + η) * (D.internal F x y).toReal) := ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal (1 + η) * ENNReal.ofReal (D.internal F x y).toReal :=
          ENNReal.ofReal_mul (by positivity)
        _ = ENNReal.ofReal (1 + η) * D.internal F x y := by rw [ENNReal.ofReal_toReal hfin]
  · by_cases htop : (Dn n).internal F x y = ∞
    · have hpos : 0 < ENNReal.ofReal (1 + η) := ENNReal.ofReal_pos.mpr (by linarith)
      calc D.internal U x y ≤ ⊤ := le_top
        _ = ENNReal.ofReal (1 + η) * (Dn n).internal F x y := by
          rw [htop, ENNReal.mul_top hpos.ne']
    · have hfin : (Dn n).internal F x y ≠ ∞ := htop
      have hlow : ENNReal.ofReal m ≤ (Dn n).internal F x y := by
        calc ENNReal.ofReal m ≤ ENNReal.ofReal ((Dn n).1 (x,y)) := ENNReal.ofReal_le_ofReal hDnlo
          _ ≤ (Dn n).internal F x y := (Dn n).ofReal_le_internal F x y
      have hlow' : m ≤ ((Dn n).internal F x y).toReal := by
        have hh : ENNReal.ofReal m ≤ ENNReal.ofReal ((Dn n).internal F x y).toReal := by
          simpa only [ENNReal.ofReal_toReal hfin] using hlow
        exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hh
      have hrec := recover_internal_upper_bound (Dn n) D D (hDn n) hF hFU
        (α := α) (δ := δ) (e := e) (τ := τ) hα hδ he.le heα hτ
        (fun z hz w hw hzw => hEeucl z hz w hw hzw)
        hDupAll
        hDupAll
        hlocalD hx hy hfin
      have hreal := hrealBound _ hlow' ENNReal.toReal_nonneg
      calc D.internal U x y ≤ _ := hrec
        _ ≤ ENNReal.ofReal ((1 + η) * ((Dn n).internal F x y).toReal) := ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal (1 + η) * ENNReal.ofReal ((Dn n).internal F x y).toReal :=
          ENNReal.ofReal_mul (by positivity)
        _ = ENNReal.ofReal (1 + η) * (Dn n).internal F x y := by
          rw [ENNReal.ofReal_toReal hfin]

end HigherDimLFPPAS.Det
