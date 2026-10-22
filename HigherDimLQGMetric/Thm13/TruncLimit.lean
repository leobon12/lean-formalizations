import HigherDimLQGMetric.Thm13.LocalLFPP
import HigherDimLQGMetric.LfppTight.MedianPos
import HigherDimLQGMetric.Sharp.ScaledMetric

/-!
# Lower limits of localized truncated LFPP distances

The fixed normalizers `aEps` are positive, so every truncated prelimit is a
continuous length metric on the whole distribution space. For each fixed
center and pair of endpoints, its internal distance has a measurable
lower limit. At distributions where the actual limit exists, the lower
limit agrees with it. These are the local edge weights in the patch.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- The normalized truncated LFPP metric at one cutoff, defined for all distributions. -/
def l8_truncScaledMetric (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) {ε : ℝ} (hε : 0 < ε) (g : DistRd d) : ContMetric d :=
  (fieldLfppMetric ξ (l8_truncFieldC hd hκ hε g)).smul
    (aEps κ ξ ε)⁻¹ (inv_pos.mpr (l6a_aEps_pos hd κ hκ ξ hε))

theorem l8_truncScaledMetric_isLength (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {ε : ℝ} (hε : 0 < ε) (g : DistRd d) :
    (l8_truncScaledMetric hd hκ ξ hε g).IsLength :=
  ContMetric.isLength_smul (inv_pos.mpr (l6a_aEps_pos hd κ hκ ξ hε))
    (l8_truncContMetric_isLength hd hκ ξ hε g)

theorem l8_measurable_truncScaledMetric (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    Measurable (l8_truncScaledMetric hd hκ ξ hε) := by
  apply Measurable.subtype_mk
  exact (continuous_const_smul _).measurable.comp
    (measurable_subtype_coe.comp (l8_measurable_truncContMetric hd hκ ξ hε))

/-- Local edge weight at a center `u`, using the lower limit of internal
metrics of `B₁(u)`. The lower limit preserves ambient lower bounds even
when the internal distances fail to converge. -/
def l8_localEdge (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (g : DistRd d) (u v : Rd d) : ℝ≥0∞ :=
  liminf (fun n =>
    (l8_truncScaledMetric hd hκ ξ (hεs n) g).internal (Metric.ball u 1) u v)
    atTop

theorem l8_measurable_localEdge (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (u v : Rd d) :
    Measurable (fun g : DistRd d => l8_localEdge hd hκ ξ εs hεs g u v) := by
  have hm (n : ℕ) : Measurable (fun g : DistRd d =>
      (l8_truncScaledMetric hd hκ ξ (hεs n) g).internal (Metric.ball u 1) u v) := by
    have hchain : Measurable (fun g : DistRd d =>
        (l8_truncScaledMetric hd hκ ξ (hεs n) g).chainInf (Metric.ball u 1) u v) :=
      (ContMetric.measurable_chainInf (Metric.ball u 1)).comp
        ((l8_measurable_truncScaledMetric hd hκ ξ (hεs n)).prodMk
          (measurable_const.prodMk measurable_const))
    convert hchain using 1
    funext g
    exact ContMetric.internal_eq_chainInf _
      (l8_truncScaledMetric_isLength hd hκ ξ (hεs n) g)
      Metric.isOpen_ball u v
  exact Measurable.liminf hm

/-- Pointwise ambient convergence gives the required lower bound for every
local edge, without convergence of the internal distances. -/
theorem l8_localEdge_ge_ambient (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (g : DistRd d) (D : ContMetric d)
    (hconv : ∀ u v : Rd d,
      Tendsto (fun n => (l8_truncScaledMetric hd hκ ξ (hεs n) g).1 (u, v))
        atTop (𝓝 (D.1 (u, v))))
    (u v : Rd d) :
    ENNReal.ofReal (D.1 (u, v)) ≤ l8_localEdge hd hκ ξ εs hεs g u v := by
  have hlim : Tendsto (fun n => ENNReal.ofReal
      ((l8_truncScaledMetric hd hκ ξ (hεs n) g).1 (u, v)))
      atTop (𝓝 (ENNReal.ofReal (D.1 (u, v)))) :=
    ENNReal.continuous_ofReal.tendsto _ |>.comp (hconv u v)
  calc
    ENNReal.ofReal (D.1 (u, v)) =
        liminf (fun n => ENNReal.ofReal
          ((l8_truncScaledMetric hd hκ ξ (hεs n) g).1 (u, v))) atTop :=
      hlim.liminf_eq.symm
    _ ≤ l8_localEdge hd hκ ξ εs hεs g u v := by
      unfold l8_localEdge
      apply Filter.liminf_le_liminf
      exact Eventually.of_forall fun n =>
        (l8_truncScaledMetric hd hκ ξ (hεs n) g).ofReal_le_internal
          (Metric.ball u 1) u v
      exact Filter.isBounded_ge_of_bot
      exact Filter.isCobounded_ge_of_top

/-- A fixed positive boundary gap makes the local internal distance equal the
ambient distance eventually. Hence the local edge has the ambient limit. -/
theorem l8_localEdge_eq_of_boundary_gap (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (g : DistRd d) (D : ContMetric d) (u v : Rd d) (δ : ℝ)
    (hbar : ∀ᶠ n in atTop, ∀ z ∈ frontier (Metric.ball u 1),
      δ ≤ (l8_truncScaledMetric hd hκ ξ (hεs n) g).1 (u, z))
    (hshort : ∀ᶠ n in atTop,
      (l8_truncScaledMetric hd hκ ξ (hεs n) g).1 (u, v) < δ)
    (hconv : Tendsto
      (fun n => (l8_truncScaledMetric hd hκ ξ (hεs n) g).1 (u, v))
      atTop (𝓝 (D.1 (u, v)))) :
    l8_localEdge hd hκ ξ εs hεs g u v = ENNReal.ofReal (D.1 (u, v)) := by
  have heq : (fun n =>
      (l8_truncScaledMetric hd hκ ξ (hεs n) g).internal (Metric.ball u 1) u v) =ᶠ[atTop]
      (fun n => ENNReal.ofReal
        ((l8_truncScaledMetric hd hκ ξ (hεs n) g).1 (u, v))) := by
    filter_upwards [hbar, hshort] with n hbn hsn
    let Dn := l8_truncScaledMetric hd hκ ξ (hεs n) g
    have hbd : ENNReal.ofReal δ ≤
        Metric.infEDist (Dn.pt u) (Dn.pt '' frontier (Metric.ball u 1)) := by
      apply Metric.le_infEDist.2
      intro y hy
      obtain ⟨z, hz, rfl⟩ := hy
      rw [ContMetric.edist_pt]
      exact ENNReal.ofReal_le_ofReal (hbn z hz)
    have hs : edist (Dn.pt u) (Dn.pt v) < ENNReal.ofReal δ := by
      rw [ContMetric.edist_pt]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Dn.nonneg u v)).2 hsn
    exact Dn.internal_eq_of_lt_infEDist_frontier
      (l8_truncScaledMetric_isLength hd hκ ξ (hεs n) g)
      Metric.isOpen_ball (Metric.mem_ball_self (by norm_num))
      (hs.trans_le hbd) |>.2.trans (ContMetric.edist_pt Dn u v)
  unfold l8_localEdge
  rw [Filter.liminf_congr heq]
  exact (ENNReal.continuous_ofReal.tendsto _ |>.comp hconv).liminf_eq

/-- The local edge limit only uses a continuous perturbation on `B₂(u)`.
The argument applies at every distribution, without a probabilistic event. -/
theorem l8_localEdge_addFun_congr (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0)) (g : DistRd d)
    (f f' : C(Rd d, ℝ)) (u v : Rd d)
    (hff' : EqOn (⇑f) (⇑f') (Metric.ball u 2)) :
    l8_localEdge hd hκ ξ εs hεs (addFun g f) u v =
      l8_localEdge hd hκ ξ εs hεs (addFun g f') u v := by
  have hsmall : ∀ᶠ n in atTop, εs n < 1 :=
    hεt.eventually (gt_mem_nhds one_pos)
  have hEq : (fun n => (l8_truncScaledMetric hd hκ ξ (hεs n)
      (addFun g f)).internal (Metric.ball u 1) u v) =ᶠ[atTop]
    (fun n => (l8_truncScaledMetric hd hκ ξ (hεs n)
      (addFun g f')).internal (Metric.ball u 1) u v) := by
    filter_upwards [hsmall] with n hn
    have hsqrt : Real.sqrt (εs n) < 1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (hεs n).le hn
    have hUV : ∀ z ∈ (⟨Metric.ball u 1, Metric.isOpen_ball⟩ :
        TopologicalSpace.Opens (Rd d)),
        Metric.closedBall z (Real.sqrt (εs n)) ⊆
          (⟨Metric.ball u 2, Metric.isOpen_ball⟩ : TopologicalSpace.Opens (Rd d)) := by
      intro z hz x hx
      change z ∈ Metric.ball u 1 at hz
      change x ∈ Metric.ball u 2
      rw [Metric.mem_ball] at hz ⊢
      rw [Metric.mem_closedBall] at hx
      calc dist x u ≤ dist x z + dist z u := dist_triangle _ _ _
        _ < 2 := by linarith
    unfold l8_truncScaledMetric
    rw [ContMetric.internal_smul, ContMetric.internal_smul]
    exact congrArg (ENNReal.ofReal (aEps κ ξ (εs n))⁻¹ * ·)
      (l8_truncInternal_addFun_congr hd hκ ξ (hεs n) g f f'
        ⟨Metric.ball u 1, Metric.isOpen_ball⟩
        ⟨Metric.ball u 2, Metric.isOpen_ball⟩ hUV hff' u v)
  unfold l8_localEdge
  exact Filter.liminf_congr hEq

end HigherDimLQGMetric
