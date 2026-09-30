import QuantumZipper.Proofs.GFF.K3.HalfDiscMarkov
import QuantumZipper.Proofs.GFF.Admissible
import Mathlib.Analysis.Complex.RemovableSingularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3-CURVE, piece 1a: the Neumann kernel pulled back by a local conformal map

Let `Φ` be holomorphic and injective on a disc `B(b, r₀)` centred on the real line, with
non-vanishing derivative and the Schwarz symmetry `Φ(z̄) = conj Φ(z)` (i.e. `Φ` is real on the
real segment). The pulled-back Neumann kernel `neumannH (Φ z) (Φ w)` differs from `neumannH z w`
by `kPull Φ z w`, which, off the two points `w = z, z̄`, is the harmonic function
`hk Φ z w = −log|(Φw − Φz)/(w − z)| − log|(Φw − Φz̄)/(w − z̄)|` (Neumann-even across `ℝ`).
Consequently the half-disc balayage `bal b ρ` (`ρ < r₀`) reproduces `kPull Φ z ·`, and the
pulled-back kernel has the same half-disc Markov pairing as `neumannH` itself
(`kernelCov2_pull_eq`): this is the covariance form of the domain Markov property of `X ∘ Φ` for
a free field `X` (the analogue of M7-a for the pulled-back free field).

Source: Sheffield, *Gaussian free fields for mathematicians*, PTRF 139 (2007), §2.2 (conformal
invariance of the Dirichlet inner product) and Thm. 2.17 (Markov property), used in Sheffield
arXiv:1012.4797 pp. 70–71 implicitly; the kernel form here (Green function of `Φ⁻¹(ℍ)` near
the boundary point = `neumannH` + a function harmonic in each variable) is the standard
conformal covariance of Green's functions. The Lean route (log of the difference quotient
`dslope`, half-disc Poisson reproduction `integral_halfDiscPoisson_of_harmonic`) is own.
-/

noncomputable section

open MeasureTheory Metric Filter InnerProductSpace Set
open scoped ComplexConjugate ENNReal Topology

namespace QuantumZipper
namespace G3Cv

open K3

/-- A local conformal map at the real point `b`: holomorphic and injective on `B(b, r₀)`,
non-vanishing derivative, Schwarz symmetric, globally measurable. -/
structure LocConf (Φ : ℂ → ℂ) (b r₀ : ℝ) : Prop where
  pos : 0 < r₀
  diff : DifferentiableOn ℂ Φ (ball (b : ℂ) r₀)
  inj : InjOn Φ (ball (b : ℂ) r₀)
  deriv_ne : ∀ z ∈ ball (b : ℂ) r₀, deriv Φ z ≠ 0
  symm : ∀ z ∈ ball (b : ℂ) r₀, Φ (conj z) = conj (Φ z)
  meas : Measurable Φ

/-- The correction kernel `neumannH (Φ z) (Φ w) − neumannH z w`. -/
def kPull (Φ : ℂ → ℂ) (z w : ℂ) : ℝ := neumannH (Φ z) (Φ w) - neumannH z w

/-- Its harmonic version in `w`. -/
def hk (Φ : ℂ → ℂ) (z w : ℂ) : ℝ :=
  -Real.log ‖dslope Φ z w‖ - Real.log ‖dslope Φ (conj z) w‖

variable {Φ : ℂ → ℂ} {b r₀ : ℝ}

theorem conj_mem_ball_g3cv {r : ℝ} {z : ℂ} (hz : z ∈ ball (b : ℂ) r) :
    conj z ∈ ball (b : ℂ) r := by
  rw [mem_ball_iff_norm] at hz ⊢; rwa [norm_conj_sub_ofReal_k3]

theorem conj_mem_closedBall_g3cv {r : ℝ} {z : ℂ} (hz : z ∈ closedBall (b : ℂ) r) :
    conj z ∈ closedBall (b : ℂ) r := by
  rw [mem_closedBall_iff_norm] at hz ⊢; rwa [norm_conj_sub_ofReal_k3]

theorem log_norm_dslope_g3cv {a w : ℂ} (hw : w ≠ a) (hΦ : Φ w ≠ Φ a) :
    Real.log ‖dslope Φ a w‖ = Real.log ‖Φ w - Φ a‖ - Real.log ‖w - a‖ := by
  rw [dslope_of_ne _ hw, slope_def_field, norm_div,
    Real.log_div (norm_ne_zero_iff.2 (sub_ne_zero.2 hΦ)) (norm_ne_zero_iff.2 (sub_ne_zero.2 hw))]

theorem kPull_eq_hk (hΦ : LocConf Φ b r₀) {z w : ℂ} (hz : z ∈ ball (b : ℂ) r₀)
    (hw : w ∈ ball (b : ℂ) r₀) (h1 : w ≠ z) (h2 : w ≠ conj z) : kPull Φ z w = hk Φ z w := by
  have hzc := conj_mem_ball_g3cv hz
  have e1 := log_norm_dslope_g3cv (Φ := Φ) h1 (fun h => h1 (hΦ.inj hw hz h))
  have e2 := log_norm_dslope_g3cv (Φ := Φ) h2 (fun h => h2 (hΦ.inj hw hzc h))
  rw [hΦ.symm z hz] at e2
  have n1 : ‖Φ w - conj (Φ z)‖ = ‖Φ z - conj (Φ w)‖ := norm_sub_conj_comm _ _
  have n2 : ‖w - conj z‖ = ‖z - conj w‖ := norm_sub_conj_comm _ _
  have n3 : ‖Φ w - Φ z‖ = ‖Φ z - Φ w‖ := norm_sub_rev _ _
  have n4 : ‖w - z‖ = ‖z - w‖ := norm_sub_rev _ _
  simp only [kPull, hk, neumannH, e1, e2, n1, n2, n3, n4]
  ring

theorem analyticAt_dslope_g3cv (hΦ : LocConf Φ b r₀) {a w : ℂ} (ha : a ∈ ball (b : ℂ) r₀)
    (hw : w ∈ ball (b : ℂ) r₀) : AnalyticAt ℂ (dslope Φ a) w :=
  ((Complex.differentiableOn_dslope (isOpen_ball.mem_nhds ha)).2 hΦ.diff).analyticAt
    (isOpen_ball.mem_nhds hw)

theorem dslope_ne_zero_g3cv (hΦ : LocConf Φ b r₀) {a w : ℂ} (ha : a ∈ ball (b : ℂ) r₀)
    (hw : w ∈ ball (b : ℂ) r₀) : dslope Φ a w ≠ 0 := by
  by_cases h : w = a
  · subst h; rw [dslope_same]; exact hΦ.deriv_ne w hw
  · rw [dslope_of_ne _ h, slope_def_field]
    exact div_ne_zero (sub_ne_zero.2 fun e => h (hΦ.inj hw ha e)) (sub_ne_zero.2 h)

theorem harmonicAt_hk (hΦ : LocConf Φ b r₀) {z w : ℂ} (hz : z ∈ ball (b : ℂ) r₀)
    (hw : w ∈ ball (b : ℂ) r₀) : HarmonicAt (hk Φ z) w := by
  have hzc := conj_mem_ball_g3cv hz
  have h1 := (analyticAt_dslope_g3cv hΦ hz hw).harmonicAt_log_norm (dslope_ne_zero_g3cv hΦ hz hw)
  have h2 := (analyticAt_dslope_g3cv hΦ hzc hw).harmonicAt_log_norm
    (dslope_ne_zero_g3cv hΦ hzc hw)
  convert h1.neg.add h2.neg using 1
  funext u
  simp only [hk, Pi.add_apply, Pi.neg_apply]
  ring

theorem neumannH_conj_right_g3cv (x y : ℂ) : neumannH x (conj y) = neumannH x y := by
  unfold neumannH; rw [Complex.conj_conj]; ring

theorem kPull_conj_right (hΦ : LocConf Φ b r₀) (z : ℂ) {w : ℂ} (hw : w ∈ ball (b : ℂ) r₀) :
    kPull Φ z (conj w) = kPull Φ z w := by
  simp only [kPull, hΦ.symm w hw, neumannH_conj_right_g3cv]

/-- `hk Φ z` is even across `ℝ` (by continuity at the two exceptional points). -/
theorem hk_conj (hΦ : LocConf Φ b r₀) {z w : ℂ} (hz : z ∈ ball (b : ℂ) r₀)
    (hw : w ∈ ball (b : ℂ) r₀) : hk Φ z (conj w) = hk Φ z w := by
  set S : Set ℂ := {z} ∪ {conj z}
  set f : ℂ → ℝ := fun u => hk Φ z (conj u) - hk Φ z u
  have hwc := conj_mem_ball_g3cv hw
  have hfc : ContinuousAt f w :=
    ((harmonicAt_hk hΦ hz hwc).1.continuousAt.comp
      (Complex.continuous_conj.continuousAt)).sub (harmonicAt_hk hΦ hz hw).1.continuousAt
  have hfin : (S \ {w}).Finite := ((finite_singleton z).union (finite_singleton _)).sdiff
  have hev : ∀ᶠ u in 𝓝[≠] w, f u = 0 := by
    have h1 : ∀ᶠ u in 𝓝[≠] w, u ∈ ball (b : ℂ) r₀ :=
      nhdsWithin_le_nhds (isOpen_ball.mem_nhds hw)
    have h2 : ∀ᶠ u in 𝓝[≠] w, u ∉ S \ {w} :=
      nhdsWithin_le_nhds (hfin.isClosed.isOpen_compl.mem_nhds fun h => h.2 rfl)
    have h3 : ∀ᶠ u in 𝓝[≠] w, u ≠ w := self_mem_nhdsWithin
    filter_upwards [h1, h2, h3] with u hu1 hu2 hu3
    have hS : u ∉ S := fun h => hu2 ⟨h, hu3⟩
    have hu4 : u ≠ z := fun h => hS (Or.inl h)
    have hu5 : u ≠ conj z := fun h => hS (Or.inr h)
    have huc := conj_mem_ball_g3cv hu1
    have hc1 : conj u ≠ z := fun h => hu5 (by rw [← h, Complex.conj_conj])
    have hc2 : conj u ≠ conj z := fun h => hu4 (by rw [← Complex.conj_conj u, h, Complex.conj_conj])
    simp only [f]
    rw [← kPull_eq_hk hΦ hz huc hc1 hc2, ← kPull_eq_hk hΦ hz hu1 hu4 hu5,
      kPull_conj_right hΦ z hu1, sub_self]
  have hlim : Tendsto f (𝓝[≠] w) (𝓝 (f w)) := hfc.tendsto.mono_left nhdsWithin_le_nhds
  have hlim0 : Tendsto f (𝓝[≠] w) (𝓝 0) := tendsto_const_nhds.congr' (hev.mono fun u h => h.symm)
  have := tendsto_nhds_unique hlim hlim0
  simp only [f] at this
  linarith

/-- Half-disc Poisson measures have no atoms. -/
theorem halfDiscPoisson_ae_ne {t r : ℝ} (hr : 0 < r) (z p : ℂ) :
    ∀ᵐ w ∂halfDiscPoisson t r z, w ≠ p := by
  have hc : ∀ q : ℂ, circleUnif (t : ℂ) r {q} = 0 := fun q => by
    rw [circleUnif_eq_circMeas_k3]; exact LQGDimension.Coupling.circMeas_singleton hr.ne' q
  rw [ae_iff]
  simp only [ne_eq, not_not, ofPred_eq_eq_singleton]
  unfold halfDiscPoisson
  rw [Measure.map_apply measurable_foldH (measurableSet_singleton p)]
  refine withDensity_absolutelyContinuous _ _ ?_
  refine measure_mono_null (t := {p} ∪ {conj p}) ?_ (measure_union_null (hc p) (hc (conj p)))
  intro w hw
  simp only [mem_preimage, mem_singleton_iff, foldH] at hw
  split_ifs at hw with h
  · exact Or.inl hw
  · exact Or.inr (by rw [mem_singleton_iff, ← hw, Complex.conj_conj])

/-- **Reproduction of the correction kernel** by the half-disc Poisson measure. -/
theorem integral_kPull_poisson (hΦ : LocConf Φ b r₀) {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r₀)
    {z w' : ℂ} (hz : z ∈ closedBall (b : ℂ) ρ) (hw' : w' ∈ ball (b : ℂ) ρ) (h1 : w' ≠ z)
    (h2 : w' ≠ conj z) :
    ∫ w, kPull Φ z w ∂(halfDiscPoisson b ρ w') = kPull Φ z w' := by
  have hsub : closedBall (b : ℂ) ρ ⊆ ball (b : ℂ) r₀ := closedBall_subset_ball hρr
  have hzB : z ∈ ball (b : ℂ) r₀ := hsub hz
  have hrep := integral_halfDiscPoisson_of_harmonic hρ hw' (f := hk Φ z)
    (fun x hx => harmonicAt_hk hΦ hzB (hsub hx))
    (fun x hx => hk_conj hΦ hzB (hsub (sphere_subset_closedBall hx)))
  rw [kPull_eq_hk hΦ hzB (ball_subset_ball hρr.le hw') h1 h2, ← hrep]
  refine integral_congr_ae ?_
  filter_upwards [halfDiscPoisson_ae_ne hρ w' z, halfDiscPoisson_ae_ne hρ w' (conj z),
    ae_halfDiscPoisson_mem hρ w'] with w hw1 hw2 hw3
  exact kPull_eq_hk hΦ hzB (hsub (sphere_subset_closedBall hw3.1)) hw1 hw2

end G3Cv
end QuantumZipper
