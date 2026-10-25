import SupercriticalLQGUniqueness.B2.PfeLocal.L1Config
import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaLower
import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaPairs
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteCircleAnnulusLower
import SupercriticalLQGUniqueness.B2.Polylog.P7Bridge

 
















set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open SupercriticalLQGUniqueness.B2.Strong

 
def l1AcrossCost (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) (z : ℂ) (r : ℝ) (i : ℂ) :
    ℝ≥0∞ :=
  ENNReal.ofReal (a : ℝ)⁻¹ *
    crossLenIn ξ φ (closedBall (z + (r : ℂ) * i) (r * l1d))
      (sphere (z + (r : ℂ) * i) (r * l1d / 16))
      (sphere (z + (r : ℂ) * i) (3 * (r * l1d) / 4))

 
def l1AroundCost (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) (z : ℂ) (r : ℝ) (k : Fin 4) :
    ℝ≥0∞ :=
  ENNReal.ofReal ((a : ℝ)⁻¹) *
    crossLenIn ξ φ (l1AroundOpen z r k) {l1Start z r k} {l1End z r k}

 
theorem l1_normalizedCont_eq (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) (p : ℂ × ℂ) :
    ENNReal.ofReal ((DG20Lim.normalizedContLFPP ξ a φ).1 p) =
      PfeWeyl.normalizedLFPPMetric ξ a φ p := by
  have h1 := DG20Lim.normalizedContLFPP_to_rescaledLFPP ξ a φ p
  have h2 := PfeWeyl.normalizedLFPPMetric_toLSCFun ξ a φ p
  rw [LSCMetric.toLSCFun_apply] at h2
  exact EReal.coe_ennreal_injective (h1.trans h2.symm)

 
theorem l1_median_eq_normalized (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) :
    Median.lfppMetric ξ a φ = PfeWeyl.normalizedLFPPMetric ξ a φ := by
  apply Subtype.ext
  funext p
  change ENNReal.ofReal ((a : ℝ)⁻¹) * lfppDistance ξ φ p =
    PfeWeyl.normalizedLFPPMetric ξ a φ p
  rw [PfeWeyl.normalizedLFPPMetric_apply]

 

theorem l1_acrossCost_le (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    (q : Finset ℂ) (hq : ∀ i ∈ q, i ∈ l1Shell)
    (hcov : l1Shell ⊆ ⋃ i ∈ q, ball i (1 / 128))
    (z : ℂ) {r : ℝ} (hr : 0 < r) {u v : ℂ}
    (hu : |‖u - z‖ - r / 2| ≤ r / 256) (hv : r * (1 - 1 / 256) ≤ ‖v - z‖) :
    (⨅ i ∈ q, l1AcrossCost ξ a φ z r i) ≤ PfeWeyl.normalizedLFPPMetric ξ a φ (u, v) := by
  obtain ⟨i, hi, hui, hvi⟩ := l1_net_cover q hq hcov z hr hu hv
  refine (iInf₂_le i hi).trans ?_
  rw [← l1_normalizedCont_eq]
  exact DG20Lim.normalized_annulus_cross_le_point_distance ξ a φ (z + (r : ℂ) * i) u v
    (r * l1d) hui hvi (mul_pos hr (by norm_num [l1d]))

 

theorem l1_across_limsup_le {G : ℕ → LSCMetric} {L : LSCMetric}
    (hG : Tendsto G atTop (𝓝 L)) (ξ : ℝ) (a : ℕ → Set.Ioi (0 : ℝ)) (φ : ℕ → C(ℂ, ℝ))
    (hGdef : ∀ n, G n = PfeWeyl.normalizedLFPPMetric ξ (a n) (φ n))
    (q : Finset ℂ) (hq : ∀ i ∈ q, i ∈ l1Shell)
    (hcov : l1Shell ⊆ ⋃ i ∈ q, ball i (1 / 128))
    (z : ℂ) {r : ℝ} (hr : 0 < r) :
    limsup (fun n => ⨅ i ∈ q, l1AcrossCost ξ (a n) (φ n) z r i) atTop ≤
      acrossDist L (innerAnnulus z r hr) := by
  unfold acrossDist
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
  have hx' : ‖x - z‖ = r / 2 := by
    have : x ∈ sphere z (r / 2) := hx
    rwa [mem_sphere, dist_eq_norm] at this
  have hy' : ‖y - z‖ = r := by
    have : y ∈ sphere z r := hy
    rwa [mem_sphere, dist_eq_norm] at this
  obtain ⟨xs, ys, hxs, hys, hval⟩ :=
    PfeAxioms.recovery_pairs_in_open hG isOpen_univ ⟨x, trivial⟩ ⟨y, trivial⟩
  have hxn : Tendsto (fun n => ‖(xs n : ℂ) - z‖) atTop (𝓝 (r / 2)) := by
    rw [← hx']
    exact ((continuous_subtype_val.tendsto _).comp hxs).sub_const z |>.norm
  have hyn : Tendsto (fun n => ‖(ys n : ℂ) - z‖) atTop (𝓝 r) := by
    rw [← hy']
    exact ((continuous_subtype_val.tendsto _).comp hys).sub_const z |>.norm
  have hev1 : ∀ᶠ n in atTop, |‖(xs n : ℂ) - z‖ - r / 2| ≤ r / 256 := by
    have := (Metric.tendsto_nhds.1 hxn) (r / 256) (by positivity)
    filter_upwards [this] with n hn
    rw [Real.dist_eq] at hn
    exact hn.le
  have hev2 : ∀ᶠ n in atTop, r * (1 - 1 / 256) ≤ ‖(ys n : ℂ) - z‖ := by
    have := (Metric.tendsto_nhds.1 hyn) (r / 256) (by positivity)
    filter_upwards [this] with n hn
    rw [Real.dist_eq] at hn
    have := (abs_lt.1 hn).1
    linarith
  have hle : ∀ᶠ n in atTop, (⨅ i ∈ q, l1AcrossCost ξ (a n) (φ n) z r i) ≤
      G n ((xs n : ℂ), (ys n : ℂ)) := by
    filter_upwards [hev1, hev2] with n h1 h2
    rw [hGdef n]
    exact l1_acrossCost_le ξ (a n) (φ n) q hq hcov z hr h1 h2
  calc limsup (fun n => ⨅ i ∈ q, l1AcrossCost ξ (a n) (φ n) z r i) atTop
      ≤ limsup (fun n => G n ((xs n : ℂ), (ys n : ℂ))) atTop := limsup_le_limsup hle
    _ = L (x, y) := hval.limsup_eq

 
theorem l1_internal_le_aroundCost (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    (z : ℂ) (r : ℝ) (k : Fin 4) :
    (PfeWeyl.normalizedLFPPMetric ξ a φ).internal (l1AroundOpen z r k)
        (⟨l1Start z r k, l1Start_mem_aroundOpen z r k⟩,
          ⟨l1End z r k, l1End_mem_aroundOpen z r k⟩) ≤
      l1AroundCost ξ a φ z r k := by
  rw [← l1_median_eq_normalized]
  exact Polylog.internal_lfppMetric_le_crossLenIn ξ a φ _ _ _

 

theorem l1_around_lt_of_liminf {G : ℕ → LSCMetric} {L : LSCMetric}
    (hG : Tendsto G atTop (𝓝 L)) (ξ : ℝ) (a : ℕ → Set.Ioi (0 : ℝ)) (φ : ℕ → C(ℂ, ℝ))
    (hGdef : ∀ n, G n = PfeWeyl.normalizedLFPPMetric ξ (a n) (φ n))
    (z : ℂ) {r : ℝ} (hr : 0 < r) (M : ℝ≥0∞)
    (hM : ∀ k : Fin 4, liminf (fun n => l1AroundCost ξ (a n) (φ n) z r k) atTop < M) :
    aroundDist L (outerAnnulus z r hr) < M + M + M + M := by
  refine PfeAxioms.aroundDist_lt_four_sector_bound L (outerAnnulus z r hr) M fun k => ?_
  set A := outerAnnulus z r hr
  have hVK := l1AroundOpen_subset_closed z r k
  have hKU := l1AroundClosed_subset_cfgOpens z r hr k
  let x₀ : l1AroundOpen z r k := ⟨l1Start z r k, l1Start_mem_aroundOpen z r k⟩
  let y₀ : l1AroundOpen z r k := ⟨l1End z r k, l1End_mem_aroundOpen z r k⟩
  have hlim := PfeAxioms.buffered_internal_liminf hG hVK (isCompact_l1AroundClosed z r k) hKU
    (fun _ => x₀) (fun _ => y₀) x₀ y₀ tendsto_const_nhds tendsto_const_nhds
  have hset : L.internalSetDist (cfgOpens A k : Set ℂ)
      (Subtype.val ⁻¹' cfgSet₁ A k) (Subtype.val ⁻¹' cfgSet₂ A k) ≤
      L.internal (cfgOpens A k : Set ℂ)
        (⟨x₀, hKU (hVK x₀.property)⟩, ⟨y₀, hKU (hVK y₀.property)⟩) := by
    unfold LSCMetric.internalSetDist
    exact iInf₂_le_of_le ⟨x₀, hKU (hVK x₀.property)⟩ (l1Start_mem_cfgSet₁ z r hr k)
      (iInf₂_le (⟨y₀, hKU (hVK y₀.property)⟩ : (cfgOpens A k : Set ℂ)) (l1End_mem_cfgSet₂ z r hr k))
  refine lt_of_le_of_lt (hset.trans (hlim.trans ?_)) (hM k)
  refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
  rw [hGdef n]
  exact l1_internal_le_aroundCost ξ (a n) (φ n) z r k

end SupercriticalLQGUniqueness.B2.PfeLocal
