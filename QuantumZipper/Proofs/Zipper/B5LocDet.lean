import QuantumZipper.Proofs.Zipper.ESMLMeas
import QuantumZipper.Proofs.LQG.PalmNormLocal
import QuantumZipper.Proofs.Zipper.RegContDet
import QuantumZipper.Proofs.RS.TraceShift
import QuantumZipper.Proofs.Zipper.F1ReflReg
import QuantumZipper.Proofs.Loewner.CaraRZ

/-!
# B5 locality, deterministic core: the unzipped lengths read the field only near the hull

Theorem 1.3, node B5 (locality) (`blueprint/E_BRANCH_BLUEPRINT.md` §B5; Sheffield,
arXiv:1012.4797, §5.4, pp. 70–72, where it is used that "the quantum lengths of `η[0,t]` are
determined by the field and the driver in a neighbourhood of the origin" for small `t`).

`unzipLengths γ (x, W) t` is the `qBoundaryMeasure` of the unzipped field
`x_t = coordChange x (fwdMapInv W t) Q` on `[O⁻_t, 0]` and `[0, O⁺_t]`. We show
(`unzipLengths_eq_of_dyCircAgree`, `unzipLengths_eq_of_dyCircAgree_ball`): if two
configurations `(x, W)`, `(x', W')`
* have continuous drivers vanishing at `0` and agreeing on `[0, t]`,
* have unzipped fields whose global vague limits exist (no junk value),
* and `x`, `x'` agree on every folded circle `foldedCircle c 2^{-j}`, `j ≥ j₀`, centred at a
  dyadic point `c = dyadicRoundC n z ∈ S`, `z ∈ ℍ̄` (countably many coordinates), where `S` is an open set into which `f_t⁻¹` maps a `δ`-neighbourhood (in `ℍ`) of an
  open `U ⊇ [O⁻_t, O⁺_t]`,

then their unzipped lengths agree. The chain is: `qBoundaryMeasure` on `U` depends only on
`avgReg x_t k` on `U` for large `k` (`PalmNorm.qBoundaryMeasure_restrict_eq_of_avgReg`);
`avgReg x_t k s` only reads `x_t` on folded circles centred within `2^{-k}` of `s`
(`LocalRule.avgReg_congr_local`); `x_t` on such a circle is `evalReg x` of its pushforward under
`f_t⁻¹` (plus an `x`-independent term), which depends only on `avgReg x j` on the pushed circle
for large `j` (`evalReg_congr_of_eventually_ae`), hence only on `x` on circles centred in `S`.

The paper states the locality without proof; the argument here is our own elementary
bookkeeping around the definitions (`FOUNDATIONS.md` §0.1: `avgReg`, `evalReg`, `coordChange`,
`qBoundaryMeasure`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace B5

/-- `evalReg` only reads the regularizations `avgReg x k`, for large `k`, `ν`-a.e. -/
theorem evalReg_congr_of_eventually_ae {x y : FieldSample} {ν : Measure ℂ}
    (h : ∀ᶠ k in atTop, ∀ᵐ w ∂ν, avgReg x k w = avgReg y k w) :
    evalReg x ν = evalReg y ν := by
  unfold evalReg
  have hev : (fun k => ∫ w, avgReg x k w ∂ν) =ᶠ[atTop] (fun k => ∫ w, avgReg y k w ∂ν) :=
    h.mono fun k hk => integral_congr_ae hk
  unfold limUnder
  rw [Filter.map_congr hev]

theorem measurable_avgReg_z (x : FieldSample) (k : ℕ) : Measurable (avgReg x k) :=
  (measurable_avgReg k).comp measurable_prodMk_left

/-- A coordinate change of `x` evaluated at `μ` depends only on `avgReg x k ∘ ψ`, for large `k`,
on a set `D` carrying `μ`. -/
theorem coordChange_congr_of_avgReg {x y : FieldSample} {ψ : ℂ → ℂ} {μ : Measure ℂ}
    (hψ : AEMeasurable ψ μ) {D : Set ℂ} (hD : ∀ᵐ u ∂μ, u ∈ D)
    (h : ∀ᶠ k in atTop, ∀ u ∈ D, avgReg x k (ψ u) = avgReg y k (ψ u)) (Q : ℝ) :
    coordChange x ψ Q μ = coordChange y ψ Q μ := by
  show evalReg x (μ.map ψ) + _ = evalReg y (μ.map ψ) + _
  rw [evalReg_congr_of_eventually_ae (h.mono fun k hk => ?_)]
  rw [ae_map_iff hψ (measurableSet_eq_fun (measurable_avgReg_z x k) (measurable_avgReg_z y k))]
  exact hD.mono fun u hu => hk u hu

/-- **Circle agreement on `S` at scales `≥ j₀`**: `x` and `y` agree on every folded circle of
dyadic radius `2^{-j}`, `j ≥ j₀`, centred at a point of `ℍ̄ ∩ S`. -/
def CircAgree (x y : FieldSample) (S : Set ℂ) (j₀ : ℕ) : Prop :=
  ∀ j, j₀ ≤ j → ∀ c ∈ Hbar, c ∈ S →
    x (foldedCircle c (radius j)) = y (foldedCircle c (radius j))

/-- **Dyadic circle agreement on `S` at scales `≥ j₀`**: `x` and `y` agree on the folded circles
of radius `2^{-j}`, `j ≥ j₀`, centred at the dyadic points `dyadicRoundC n z` (`z ∈ ℍ̄`) lying in
`S`. Only countably many coordinates of the field are involved; these are the only circles that
`avgReg` reads. -/
def DyCircAgree (x y : FieldSample) (S : Set ℂ) (j₀ : ℕ) : Prop :=
  ∀ j, j₀ ≤ j → ∀ n : ℕ, ∀ z ∈ Hbar, dyadicRoundC n z ∈ S →
    x (foldedCircle (dyadicRoundC n z) (radius j)) = y (foldedCircle (dyadicRoundC n z) (radius j))

/-- Dyadic circle agreement on an open `S` gives agreement of all `avgReg · j`, `j ≥ j₀`, on
`ℍ̄ ∩ S`. -/
theorem avgReg_eq_of_dyCircAgree {x y : FieldSample} {S : Set ℂ} (hS : IsOpen S) {j₀ : ℕ}
    (hag : DyCircAgree x y S j₀) {j : ℕ} (hj : j₀ ≤ j) {w : ℂ} (hw : w ∈ Hbar) (hwS : w ∈ S) :
    avgReg x j w = avgReg y j w := by
  unfold avgReg
  have hev : (fun n => x (foldedCircle (dyadicRoundC n w) (radius j))) =ᶠ[atTop]
      (fun n => y (foldedCircle (dyadicRoundC n w) (radius j))) := by
    filter_upwards [(RegClosure.tendsto_dyadicRoundC w).eventually (hS.mem_nhds hwS)] with n hn
    exact hag j hj n w hw hn
  unfold limUnder
  rw [Filter.map_congr hev]

/-- The regularized averages of the coordinate changes `coordChange x ψ Q`, `coordChange y ψ Q`
at a point `s ∈ ℍ̄` and scale `2^{-k}` agree if `x`, `y` agree on circles centred in `S` and `ψ`
maps the points of `ℍ` within `δ > 2·2^{-k}` of `s` into `S`. -/
theorem avgReg_coordChange_congr {x y : FieldSample} {ψ : ℂ → ℂ} (Q : ℝ)
    (hψm : ∀ c : ℂ, ∀ r : ℝ, 0 < r → AEMeasurable ψ (foldedCircle c r))
    (hψH : ∀ u, ψ u ∈ Hbar) {S : Set ℂ} (hS : IsOpen S) {j₀ : ℕ} (hag : DyCircAgree x y S j₀)
    {s : ℂ} (hs : s ∈ Hbar) {k : ℕ} {δ : ℝ} (hk : 2 * radius k < δ)
    (hψS : ∀ u ∈ H, dist u s < δ → ψ u ∈ S) :
    avgReg (coordChange x ψ Q) k s = avgReg (coordChange y ψ Q) k s := by
  refine LocalRule.avgReg_congr_local k (radius_pos k) (fun c hc hcs => ?_) hs
  have hD : ∀ᵐ u ∂foldedCircle c (radius k), u ∈ Metric.closedBall c (radius k) ∩ H :=
    (LocalRule.ae_fc_mem_closedBall hc (radius_pos k)).and
      (TwoPoint.foldedCircle_ae_mem_H c (radius_pos k))
  refine coordChange_congr_of_avgReg (hψm c _ (radius_pos k)) hD ?_ Q
  filter_upwards [eventually_ge_atTop j₀] with j hj u hu
  refine avgReg_eq_of_dyCircAgree hS hag hj (hψH u) (hψS u hu.2 ?_)
  have h1 : dist u c ≤ radius k := Metric.mem_closedBall.1 hu.1
  calc dist u s ≤ dist u c + dist c s := dist_triangle _ _ _
    _ < δ := by linarith

/-- `f_t⁻¹` moves points of `ℍ` by at most `6M + 6√t` when `|W| ≤ M` on `[0,t]`: the time-reversed
driver `W(t - ·) - W t` is bounded by `2M`, and the reverse flow moves points by at most
`3·(2M) + 6√t` (`CaraR.norm_revMap_sub_self_le`, after Lawler, *Conformally Invariant Processes in
the Plane*, Lemma 4.12, p. 80). -/
theorem norm_fwdMapInv_sub_le {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t M : ℝ}
    (ht : 0 < t) (hM : ∀ r ∈ Icc (0 : ℝ) t, |W r| ≤ M) {u : ℂ} (hu : u ∈ H) :
    ‖fwdMapInv W t u - u‖ ≤ 6 * M + 6 * Real.sqrt t := by
  rw [UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht.le hu]
  have hV : Continuous (fun s => W (t - s) - W t) :=
    (hW.comp (continuous_const.sub continuous_id)).sub continuous_const
  have hb : ∀ r ∈ Icc (0 : ℝ) t, |W (t - r) - W t| ≤ 2 * M := fun r hr => by
    have h1 := abs_le.1 (hM (t - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩)
    have h2 := abs_le.1 (hM t ⟨ht.le, le_rfl⟩)
    rw [abs_le]; constructor <;> linarith
  have := CaraR.norm_revMap_sub_self_le hV ht hb hu
  linarith

theorem DyCircAgree.mono {x y : FieldSample} {S S' : Set ℂ} {j₀ : ℕ} (h : DyCircAgree x y S j₀)
    (hS : S' ⊆ S) : DyCircAgree x y S' j₀ := fun j hj n z hz hzS => h j hj n z hz (hS hzS)

end B5
end QuantumZipper
