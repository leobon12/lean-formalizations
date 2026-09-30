import QuantumZipper.Proofs.Zipper.XAreaPCEnergy
import QuantumZipper.Proofs.Zipper.SWCoreDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-VA (i): the pushed-circle variance bound, uniformly over an area map class

Task SWC-VA (`handoff/SW-CORE.md` §5). For a rational area class
`Λ = SWCore.AreaClass a b c d ρ M m` (`c, ρ, m > 0`) there are `C ≥ 0`, `r₀ > 0`, depending only on
the class data, such that for every `ψ ∈ Λ`, every `z ∈ K = [a,b] × [c,d]` and `0 < r ≤ r₀`,

  `|kernelCov2 neumannH (ψ_* fc(z, r) − fc(ψ z, r‖ψ'(z)‖))| ≤ C r`

(`swcVA_kernelCov2_push_le`): the variance of `X(ψ_* fc(z,r)) − X(fc(ψ z, r‖ψ'(z)‖))` for the free
boundary field (Neumann kernel) is `O(r)`, uniformly over the class and `z ∈ K`. This is the area,
circle-average form of Sheffield–Wang arXiv:1605.06171 Lemma 3.4 (3.17)–(3.19) with the variance
estimate (3.20) (p. 15–16), with de Branges' coefficient bounds replaced by Cauchy estimates on the
class (SW-A3 adaptation, `SWCoreDefs.lean`).

Proof: the per-map energy bound `E6.XAreaPC.abs_kernelCov2_push_circle_le` (proved; exact circle
means) needs `ψ` to be `η`-close to its linearization on `B̄(z,r)` with `η = C r`. On the class, the
Cauchy estimate (mathlib `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`) applied twice gives
`‖ψ'‖ ≤ 4M/ρ` on the `ρ/2`-thickening and `‖ψ''‖ ≤ 16M/ρ²` on the `ρ/8`-thickening of `K`;
then the argument of `E6.XAreaPC.exists_pushCircHyp_uniform` runs with these explicit constants.
Own elementary argument (Cauchy estimates), following the repository's per-map proof.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace SWCore

open E6.XAreaPC

/-- A point within `s` of a point of the `t'`-thickening lies in the `t`-thickening if
`s + t' < t`. -/
theorem swcVA_mem_thickening {E : Set ℂ} {u v : ℂ} {s t t' : ℝ} (hu : u ∈ thickening t' E)
    (hv : dist v u ≤ s) (hs : s + t' < t) : v ∈ thickening t E := by
  have h := thickening_thickening_subset (t - t') t' E
    (mem_thickening_iff.2 ⟨u, hu, by linarith⟩)
  rwa [sub_add_cancel] at h

/-- **Cauchy estimate for `ψ'`** on the `ρ/2`-thickening. -/
theorem swcVA_norm_deriv_le {ψ : ℂ → ℂ} {K : Set ℂ} {ρ M : ℝ} (hρ : 0 < ρ)
    (hψ : DifferentiableOn ℂ ψ (thickening ρ K)) (hM : ∀ z ∈ thickening ρ K, ‖ψ z‖ ≤ M)
    {u : ℂ} (hu : u ∈ thickening (ρ / 2) K) : ‖deriv ψ u‖ ≤ M / (ρ / 4) := by
  have hR : 0 < ρ / 4 := by positivity
  have hsub : closedBall u (ρ / 4) ⊆ thickening ρ K := fun v hv =>
    swcVA_mem_thickening hu (mem_closedBall.1 hv) (by linarith)
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR ?_ fun v hv =>
    hM v (hsub (sphere_subset_closedBall hv))
  exact (hψ.mono ((closure_ball u hR.ne').symm ▸ hsub)).diffContOnCl

/-- **Cauchy estimate for `ψ''`** on the `ρ/8`-thickening. -/
theorem swcVA_norm_deriv2_le {ψ : ℂ → ℂ} {K : Set ℂ} {ρ M : ℝ} (hρ : 0 < ρ)
    (hψ : DifferentiableOn ℂ ψ (thickening ρ K)) (hM : ∀ z ∈ thickening ρ K, ‖ψ z‖ ≤ M)
    {u : ℂ} (hu : u ∈ thickening (ρ / 8) K) :
    ‖deriv (deriv ψ) u‖ ≤ M / (ρ / 4) / (ρ / 4) := by
  have hR : 0 < ρ / 4 := by positivity
  have hA : AnalyticOnNhd ℂ ψ (thickening ρ K) := hψ.analyticOnNhd isOpen_thickening
  have hsub : closedBall u (ρ / 4) ⊆ thickening (ρ / 2) K := fun v hv =>
    swcVA_mem_thickening hu (mem_closedBall.1 hv) (by linarith)
  have hsub' : thickening (ρ / 2) K ⊆ thickening ρ K := thickening_mono (by linarith) K
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR ?_ fun v hv =>
    swcVA_norm_deriv_le hρ hψ hM (hsub (sphere_subset_closedBall hv))
  exact (hA.deriv.differentiableOn.mono
    (((closure_ball u hR.ne').symm ▸ hsub).trans hsub')).diffContOnCl

open Classical in
/-- **Uniform affine approximation over the class**: `PushCircHyp ψ̃ z ψ'(z) r (C r)` with `C, r₀`
depending only on the class data, `ψ̃` the measurable version of `ψ` (equal to `ψ` on the
`ρ`-thickening). -/
theorem swcVA_pushCircHyp {a b c d ρ M m : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hm : 0 < m) :
    ∃ C r₀ : ℝ, 0 ≤ C ∧ 0 < r₀ ∧ ∀ ψ ∈ AreaClass a b c d ρ M m, ∀ z ∈ rectC a b c d,
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        PushCircHyp ((thickening ρ (rectC a b c d)).piecewise ψ 0) z (deriv ψ z) r (C * r) := by
  classical
  set K := rectC a b c d with hK
  set U := thickening ρ K with hU
  set M₁' := |M| / (ρ / 4) + 1 with hM₁'
  have hM₁'0 : 0 < M₁' := by positivity
  set M₂' := |M| / (ρ / 4) / (ρ / 4) with hM₂'
  have hM₂'0 : 0 ≤ M₂' := by positivity
  set C := M₂' / m with hC
  have hC0 : 0 ≤ C := div_nonneg hM₂'0 hm.le
  set r₀ := min (min (ρ / 16) c) (min (ρ / M₁') (1 / (2 * C + 1))) with hr₀
  have hr₀0 : 0 < r₀ := lt_min (lt_min (by positivity) hc) (lt_min (by positivity) (by positivity))
  refine ⟨C, r₀, hC0, hr₀0, fun ψ hψ z hz r hr hrr => ?_⟩
  obtain ⟨hψd, -, hψb, hψm⟩ := hψ
  have hrρ : r ≤ ρ / 16 := hrr.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrc : r ≤ c := hrr.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrM : r ≤ ρ / M₁' := hrr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrC : r ≤ 1 / (2 * C + 1) := hrr.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hM : ∀ u ∈ U, ‖ψ u‖ ≤ |M| := fun u hu => (hψb u hu).1.trans (le_abs_self M)
  have hzt : ∀ {ε : ℝ}, 0 < ε → z ∈ thickening ε K := fun hε => self_subset_thickening hε K hz
  have hBL : closedBall z r ⊆ thickening (ρ / 8) K := fun u hu =>
    swcVA_mem_thickening (hzt (show (0 : ℝ) < ρ / 32 by positivity)) (mem_closedBall.1 hu)
      (by linarith)
  have hBU : closedBall z r ⊆ U := hBL.trans (thickening_mono (by linarith) K)
  have hzU : z ∈ U := hBU (mem_closedBall_self hr.le)
  have hA : AnalyticOnNhd ℂ ψ U := hψd.analyticOnNhd isOpen_thickening
  have hd1 : DifferentiableOn ℂ (deriv ψ) U := hA.deriv.differentiableOn
  have hmd : m ≤ ‖deriv ψ z‖ := hψm z hz
  have hdz : ‖deriv ψ z‖ ≤ M₁' :=
    (swcVA_norm_deriv_le hρ hψd hM (hzt (by positivity))).trans (by rw [hM₁']; linarith)
  have hmi : c ≤ z.im := hz.2.1
  have hmψ : ρ ≤ (ψ z).im := (hψb z hzU).2
  have hconv : Convex ℝ (closedBall z r) := convex_closedBall z r
  have hzB : z ∈ closedBall z r := mem_closedBall_self hr.le
  have hdiff1 : ∀ s ∈ closedBall z r, DifferentiableAt ℂ (deriv ψ) s := fun s hs =>
    hd1.differentiableAt (isOpen_thickening.mem_nhds (hBU hs))
  have hb1 : ∀ s ∈ closedBall z r, ‖deriv (deriv ψ) s‖ ≤ M₂' := fun s hs =>
    swcVA_norm_deriv2_le hρ hψd hM (hBL hs)
  have hder : ∀ s ∈ closedBall z r, ‖deriv ψ s - deriv ψ z‖ ≤ M₂' * r := fun s hs => by
    have := hconv.norm_image_sub_le_of_norm_deriv_le hdiff1 hb1 hzB hs
    exact this.trans (mul_le_mul_of_nonneg_left
      (by rw [← dist_eq_norm]; exact mem_closedBall.1 hs) hM₂'0)
  set g : ℂ → ℂ := fun s => ψ s - deriv ψ z * s with hg
  have hgd : ∀ s ∈ closedBall z r, HasDerivAt g (deriv ψ s - deriv ψ z) s := fun s hs => by
    have h1 : HasDerivAt ψ (deriv ψ s) s :=
      (hψd.differentiableAt (isOpen_thickening.mem_nhds (hBU hs))).hasDerivAt
    have h2 := h1.sub ((hasDerivAt_id' s).const_mul (deriv ψ z))
    rw [mul_one] at h2
    exact h2
  have hlin0 : ∀ u ∈ closedBall z r, ∀ w ∈ closedBall z r,
      ‖ψ u - ψ w - deriv ψ z * (u - w)‖ ≤ M₂' * r * ‖u - w‖ := fun u hu w hw => by
    have := hconv.norm_image_sub_le_of_norm_deriv_le (f := g)
      (fun s hs => (hgd s hs).differentiableAt)
      (fun s hs => by rw [(hgd s hs).deriv]; exact hder s hs) hw hu
    have e : g u - g w = ψ u - ψ w - deriv ψ z * (u - w) := by simp only [hg]; ring
    rwa [e] at this
  have hψc : ContinuousOn ψ U := hψd.continuousOn
  have hψ'm : Measurable (U.piecewise ψ 0) :=
    hψc.measurable_piecewise continuousOn_const isOpen_thickening.measurableSet
  have hψ'eq : EqOn (U.piecewise ψ 0) ψ U := fun x hx => piecewise_eq_of_mem _ _ _ hx
  refine
    { r_pos := hr
      r_le_im := hrc.trans hmi
      meas := hψ'm
      analytic := fun u hu => (hA u (hBU hu)).congr
        (Filter.eventually_of_mem (isOpen_thickening.mem_nhds (hBU hu))
          fun v hv => (hψ'eq hv).symm)
      im_pos := fun u hu => by
        rw [hψ'eq (hBU hu)]; exact lt_of_lt_of_le hρ (hψb u (hBU hu)).2
      a_ne := norm_pos_iff.1 (lt_of_lt_of_le hm hmd)
      eta_nonneg := mul_nonneg hC0 hr.le
      eta_le := ?_
      lin := fun u hu w hw => ?_
      rho_le := ?_ }
  · have h1 : C * r ≤ C * (1 / (2 * C + 1)) := mul_le_mul_of_nonneg_left hrC hC0
    have h2 : C * (1 / (2 * C + 1)) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) two_pos]
      linarith
    linarith
  · rw [hψ'eq (hBU hu), hψ'eq (hBU hw)]
    refine (hlin0 u hu w hw).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have : M₂' * r = C * r * m := by
      rw [hC]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hmd (mul_nonneg hC0 hr.le)
  · rw [hψ'eq hzU]
    have : r * ‖deriv ψ z‖ ≤ ρ / M₁' * M₁' :=
      mul_le_mul hrM hdz (norm_nonneg _) (div_nonneg hρ.le hM₁'0.le)
    rw [div_mul_cancel₀ _ hM₁'0.ne'] at this
    linarith

open Classical in
/-- **SWC-VA (i): pushed-circle minus image-circle Neumann energy is `O(r)`, uniformly over an area
map class and `z ∈ K`.** -/
theorem swcVA_kernelCov2_push_le {a b c d ρ M m : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hm : 0 < m) :
    ∃ C r₀ : ℝ, 0 ≤ C ∧ 0 < r₀ ∧ ∀ ψ ∈ AreaClass a b c d ρ M m, ∀ z ∈ rectC a b c d,
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        |kernelCov2 neumannH ((foldedCircle z r).map ψ, foldedCircle (ψ z) (r * ‖deriv ψ z‖))
          ((foldedCircle z r).map ψ, foldedCircle (ψ z) (r * ‖deriv ψ z‖))| ≤ C * r := by
  obtain ⟨C, r₀, hC, hr₀, h⟩ := swcVA_pushCircHyp (a := a) (b := b) (d := d) (M := M) hc hρ hm
  refine ⟨4 * C, min r₀ (ρ / 16), by positivity, lt_min hr₀ (by positivity),
    fun ψ hψ z hz r hr hrr => ?_⟩
  have hh := h ψ hψ z hz r hr (hrr.trans (min_le_left _ _))
  have hr16 : r ≤ ρ / 16 := hrr.trans (min_le_right _ _)
  set U := thickening ρ (rectC a b c d) with hU
  have hBU : closedBall z r ⊆ U := fun u hu =>
    swcVA_mem_thickening (self_subset_thickening (show (0 : ℝ) < ρ / 2 by positivity) _ hz)
      (mem_closedBall.1 hu) (by linarith)
  have hmap : (foldedCircle z r).map ψ = (foldedCircle z r).map (U.piecewise ψ 0) := by
    rw [hh.fc_eq]
    refine Measure.map_congr ?_
    filter_upwards [hh.ae_sphere] with u hu
    exact (piecewise_eq_of_mem _ _ _ (hBU hu.1)).symm
  have hz' : U.piecewise ψ 0 z = ψ z := piecewise_eq_of_mem _ _ _ (hBU (mem_closedBall_self hr.le))
  have := abs_kernelCov2_push_circle_le hh
  rw [hmap, ← hz']
  linarith

end SWCore
end QuantumZipper
