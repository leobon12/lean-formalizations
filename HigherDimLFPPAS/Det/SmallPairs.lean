import HigherDimLFPPAS.Det.CompactLocality

/-!
# Shrinking endpoint pairs
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Det

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The internal distances of locally uniformly convergent length metrics vanish uniformly on
endpoint pairs in a compact set whose Euclidean separation tends to zero. -/
theorem internal_small_pair_tendsto
    (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hDn : ∀ n, (Dn n).IsLength)
    (hconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
      (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R))
    {U F : Set (Rd d)} (hU : IsOpen U) (hF : IsCompact F) (hFU : F ⊆ U)
    (ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ F, ∀ y ∈ F,
      dist x y ≤ ρ n → (Dn n).internal U x y ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨δloc, hδloc, Nloc, hloc⟩ := eventually_internal_eq_global_on_compact
    Dn D hDn hconv hU hF hFU
  have hptUC : UniformContinuousOn D.pt F :=
    hF.uniformContinuousOn_of_continuous D.continuous_pt.continuousOn
  obtain ⟨δmet, hδmet, hmet⟩ :=
    (Metric.uniformContinuousOn_iff.mp hptUC) (ε / 2) (by positivity)
  obtain ⟨R₀, hFball₀⟩ := hF.isBounded.subset_ball (0 : Rd d)
  let R := max R₀ 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hFball : F ⊆ closedBall (0 : Rd d) R := by
    intro x hx
    have hx' : x ∈ closedBall (0 : Rd d) R₀ := ball_subset_closedBall (hFball₀ hx)
    exact closedBall_subset_closedBall (le_max_left _ _) hx'
  have hconvε : ∀ᶠ n : ℕ in atTop, ∀ x ∈ closedBall (0 : Rd d) R,
      ∀ y ∈ closedBall (0 : Rd d) R,
        |(Dn n).1 (x,y) - D.1 (x,y)| < ε / 2 := by
    have h := (Metric.tendstoUniformlyOn_iff).1 (hconv R hR) (ε / 2) (by positivity)
    filter_upwards [h] with n hn x hx y hy
    have hxy := hn (x,y) ⟨hx,hy⟩
    simpa [Real.dist_eq, abs_sub_comm] using hxy
  have hρloc : ∀ᶠ n : ℕ in atTop, ρ n < min δloc δmet :=
    hρ.eventually (Iio_mem_nhds (lt_min hδloc hδmet))
  obtain ⟨Nconv, hNconv⟩ := Filter.eventually_atTop.1 hconvε
  obtain ⟨Nρ, hNρ⟩ := Filter.eventually_atTop.1 hρloc
  refine ⟨max (max Nloc Nconv) Nρ, ?_⟩
  intro n hn x hx y hy hxy
  have hnloc : Nloc ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnconv : Nconv ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnρ : Nρ ≤ n := le_trans (le_max_right _ _) hn
  have hρn : ρ n < min δloc δmet := hNρ n hnρ
  have hclosemet : D.1 (x,y) < ε / 2 := by
    have hxy' : dist x y < δmet := hxy.trans_lt (hρn.trans_le (min_le_right _ _))
    have h := hmet x hx y hy hxy'
    simpa [D.dist_pt] using h
  have hcloseDn : |(Dn n).1 (x,y) - D.1 (x,y)| < ε / 2 :=
    hNconv n hnconv x (hFball hx) y (hFball hy)
  have hglobal : (Dn n).1 (x,y) < ε := by
    have h := (abs_lt.mp hcloseDn).2
    linarith
  have hlocxy : dist x y < δloc := hxy.trans_lt (hρn.trans_le (min_le_left _ _))
  rw [hloc n hnloc x hx y hy hlocxy]
  exact ENNReal.ofReal_le_ofReal hglobal.le

end HigherDimLFPPAS.Det

