import HigherDimLQGMetric.Thm13.LocalLower
import HigherDimLQGMetric.Thm13.TruncLimit

/-! Local lower limits of internal truncated LFPP metrics. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

def l8_localInternal {d : ℕ} {κ : Rd d → ℝ}
    (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (W : Opens (Rd d)) (g : DistRd d) (u v : Rd d) : ℝ≥0∞ :=
  liminf (fun n =>
    (l8_truncScaledMetric hd hκ ξ (hεs n) g).internal W u v) atTop

theorem l8_measurable_localInternal {d : ℕ} {κ : Rd d → ℝ}
    (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (W : Opens (Rd d)) (u v : Rd d) :
    Measurable (fun g : DistRd d =>
      l8_localInternal hd hκ ξ εs hεs W g u v) := by
  have hm (n : ℕ) : Measurable (fun g : DistRd d =>
      (l8_truncScaledMetric hd hκ ξ (hεs n) g).internal W u v) := by
    have hchain : Measurable (fun g : DistRd d =>
        (l8_truncScaledMetric hd hκ ξ (hεs n) g).chainInf W u v) := by
      simpa only [Function.comp_def] using
        (ContMetric.measurable_chainInf (W : Set (Rd d))).comp
          ((l8_measurable_truncScaledMetric hd hκ ξ (hεs n)).prodMk
            (measurable_const.prodMk measurable_const))
    convert hchain using 1
    funext g
    exact ContMetric.internal_eq_chainInf _
      (l8_truncScaledMetric_isLength hd hκ ξ (hεs n) g)
      W.isOpen u v
  exact Measurable.liminf hm

theorem l8_localInternal_congr_of_restrictTo
    {d : ℕ} {κ : Rd d → ℝ}
    (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    (W U : Opens (Rd d))
    (hWc : IsCompact (closure (W : Set (Rd d))))
    (hWU : closure (W : Set (Rd d)) ⊆ U)
    {g g' : DistRd d} (heq : restrictTo U g = restrictTo U g')
    (u v : Rd d) :
    l8_localInternal hd hκ ξ εs hεs W g u v =
      l8_localInternal hd hκ ξ εs hεs W g' u v := by
  obtain ⟨δ, hδ, hδU⟩ :=
    hWc.exists_cthickening_subset_open U.isOpen hWU
  have hs : Tendsto (fun n => Real.sqrt (εs n)) atTop (𝓝 0) := by
    have ht := (Real.continuous_sqrt.tendsto 0).comp hεt
    simpa only [Real.sqrt_zero, Function.comp_def] using ht
  have hsmall : ∀ᶠ n in atTop, Real.sqrt (εs n) < δ :=
    hs.eventually (gt_mem_nhds hδ)
  have hEq : (fun n =>
      (l8_truncScaledMetric hd hκ ξ (hεs n) g).internal W u v) =ᶠ[atTop]
      (fun n =>
        (l8_truncScaledMetric hd hκ ξ (hεs n) g').internal W u v) := by
    filter_upwards [hsmall] with n hn
    have hUV : ∀ z ∈ W,
        closedBall z (Real.sqrt (εs n)) ⊆ U := by
      intro z hz
      exact (closedBall_subset_cthickening (subset_closure hz) _).trans
        ((cthickening_mono hn.le _).trans hδU)
    unfold l8_truncScaledMetric
    rw [ContMetric.internal_smul, ContMetric.internal_smul]
    congr 1
    apply l8_fieldLfppMetric_internal_congr ξ _ _ W.isOpen
    intro x hx
    exact l2c_truncMollify_eq_of_restrictTo hd hκ (hεs n) x U
      (hUV x hx) heq
  unfold l8_localInternal
  exact Filter.liminf_congr hEq

end HigherDimLQGMetric
