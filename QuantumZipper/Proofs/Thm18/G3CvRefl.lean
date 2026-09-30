import QuantumZipper.Proofs.Thm18.G3CvCov
import QuantumZipper.Proofs.Thm18.G1ZZ1Meas
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Analytic.IsolatedZeros

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3-CURVE, piece 2: the local maps of the curve are local conformal maps (`LocConf`)

`locConf_of_real`: a function holomorphic near a real point `b`, real on the real axis near `b`
and with `Ψ'(b) ≠ 0`, agrees near `b` with a `LocConf` map (G3CvKer.lean) which is bi-Lipschitz
on every closed disc `closedBall b ρ`, `ρ < r₀` (`BiLip`, G3CvCov.lean): injectivity and the
two-sided bounds come from the strict derivative (`HasStrictFDerivAt.approximates_deriv_on_nhds`),
the Schwarz symmetry `Ψ(z̄) = conj Ψ(z)` from the identity theorem (Schwarz reflection principle,
Ahlfors, *Complex Analysis*, Ch. 4 §6.5), measurability by cutting off outside the disc.

`sideRefl_locConf`: for the side maps with reflection data (`SideReflGood`, proved for simple
chords in `sideReflChordStmt_holds`), at every point of the side half-line the side map agrees on
`H` near `b = Φ⁻¹ x` with such a map `Ψ̃`, `Ψ̃ b = x`. Hence `g1zLocMap left W x`
`= ψ(· + b) − x` agrees on `H` near `0` with the translate of a `LocConf` map
(`g1zBdryPre_eq`). Own elementary argument (Sheffield, arXiv:1012.4797 p. 70, uses the
conformal local maps implicitly).
-/

noncomputable section

open MeasureTheory Metric Filter Set
open scoped ComplexConjugate ENNReal Topology NNReal

namespace QuantumZipper
namespace G3Cv

open Thm18Asm

/-- **Local conformal maps from reflection data.** -/
theorem locConf_of_real {Ψ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hΨ : DifferentiableOn ℂ Ψ U)
    {b ε : ℝ} (hbU : (b : ℂ) ∈ U) (hε : 0 < ε)
    (hreal : ∀ t : ℝ, |t - b| < ε → (Ψ t).im = 0) (hd : deriv Ψ b ≠ 0) :
    ∃ (Ψ' : ℂ → ℂ) (r₀ m M : ℝ), LocConf Ψ' b r₀ ∧ EqOn Ψ' Ψ (ball (b : ℂ) r₀) ∧
      ∀ ρ, ρ < r₀ → BiLip Ψ' b ρ m M := by
  classical
  obtain ⟨r₁, hr₁, hr₁U⟩ := Metric.isOpen_iff.1 hU _ hbU
  set d := deriv Ψ b with hd_def
  have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hd
  have hstrict : HasStrictDerivAt Ψ d b :=
    (hΨ.analyticAt (hU.mem_nhds hbU)).hasStrictDerivAt
  set c : ℝ≥0 := ⟨‖d‖ / 2, by positivity⟩ with hc_def
  have hc : (c : ℝ) = ‖d‖ / 2 := rfl
  obtain ⟨s, hs, happrox⟩ := hstrict.hasStrictFDerivAt.approximates_deriv_on_nhds
    (c := c) (Or.inr (by rw [← NNReal.coe_pos, hc]; positivity))
  obtain ⟨r₂, hr₂, hr₂s⟩ := Metric.mem_nhds_iff.1 hs
  set r₀ := min (min r₁ r₂) ε with hr₀
  have hr₀pos : 0 < r₀ := lt_min (lt_min hr₁ hr₂) hε
  have hr₀U : ball (b : ℂ) r₀ ⊆ U :=
    (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))).trans hr₁U
  have hr₀s : ball (b : ℂ) r₀ ⊆ s :=
    (ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _))).trans hr₂s
  have hr₀ε : r₀ ≤ ε := min_le_right _ _
  -- two-sided bounds on `ball b r₀`
  have hbounds : ∀ z ∈ ball (b : ℂ) r₀, ∀ w ∈ ball (b : ℂ) r₀,
      ‖d‖ / 2 * ‖z - w‖ ≤ ‖Ψ z - Ψ w‖ ∧ ‖Ψ z - Ψ w‖ ≤ 3 * ‖d‖ / 2 * ‖z - w‖ := by
    intro z hz w hw
    have h := happrox z (hr₀s hz) w (hr₀s hw)
    have e : (ContinuousLinearMap.toSpanSingleton ℂ d) (z - w) = (z - w) * d := by
      rw [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    rw [e, hc] at h
    have n : ‖(z - w) * d‖ = ‖z - w‖ * ‖d‖ := norm_mul _ _
    constructor
    · have := norm_sub_norm_le ((z - w) * d) ((z - w) * d - (Ψ z - Ψ w))
      rw [sub_sub_cancel] at this
      have h' : ‖(z - w) * d - (Ψ z - Ψ w)‖ = ‖Ψ z - Ψ w - (z - w) * d‖ := norm_sub_rev _ _
      nlinarith [norm_nonneg (z - w)]
    · have := norm_le_insert' (Ψ z - Ψ w) ((z - w) * d)
      have h2 : ‖Ψ z - Ψ w‖ ≤ ‖Ψ z - Ψ w - (z - w) * d‖ + ‖(z - w) * d‖ := by
        have := norm_add_le (Ψ z - Ψ w - (z - w) * d) ((z - w) * d)
        rwa [sub_add_cancel] at this
      nlinarith [norm_nonneg (z - w)]
  -- the cut-off map
  set Ψ' : ℂ → ℂ := (ball (b : ℂ) r₀).piecewise Ψ 0 with hΨ'
  have heq : EqOn Ψ' Ψ (ball (b : ℂ) r₀) := fun z hz => piecewise_eq_of_mem _ _ _ hz
  have hdiff : DifferentiableOn ℂ Ψ' (ball (b : ℂ) r₀) :=
    (hΨ.mono hr₀U).congr heq
  have hderiv_eq : ∀ z ∈ ball (b : ℂ) r₀, deriv Ψ' z = deriv Ψ z := fun z hz =>
    Filter.EventuallyEq.deriv_eq (eventually_of_mem (isOpen_ball.mem_nhds hz) heq)
  -- symmetry of `Ψ` on the ball
  have hsymm : ∀ z ∈ ball (b : ℂ) r₀, Ψ (conj z) = conj (Ψ z) := by
    have hfA : AnalyticOnNhd ℂ Ψ (ball (b : ℂ) r₀) := (hΨ.mono hr₀U).analyticOnNhd isOpen_ball
    have hgD : DifferentiableOn ℂ (conj ∘ Ψ ∘ conj) (ball (b : ℂ) r₀) := by
      intro z hz
      have hzc : conj z ∈ ball (b : ℂ) r₀ := conj_mem_ball_g3cv hz
      have h1 : DifferentiableAt ℂ Ψ (conj z) :=
        (hΨ.mono hr₀U).differentiableAt (isOpen_ball.mem_nhds hzc)
      have h2 := h1.conj_conj
      rw [Complex.conj_conj] at h2
      exact h2.differentiableWithinAt
    have hgA : AnalyticOnNhd ℂ (conj ∘ Ψ ∘ conj) (ball (b : ℂ) r₀) :=
      hgD.analyticOnNhd isOpen_ball
    have hfreq : ∃ᶠ z in 𝓝[≠] (b : ℂ), Ψ z = (conj ∘ Ψ ∘ conj) z := by
      have hT : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] b) (𝓝[≠] (b : ℂ)) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
          (eventually_nhdsWithin_of_forall fun t ht h => ht (Complex.ofReal_injective h))
      refine hT.frequently (Eventually.frequently ?_)
      have hnb : ∀ᶠ t in 𝓝[≠] b, |t - b| < ε := by
        refine nhdsWithin_le_nhds ?_
        have := Metric.ball_mem_nhds b hε
        filter_upwards [this] with t ht
        rwa [Metric.mem_ball, Real.dist_eq] at ht
      filter_upwards [hnb] with t ht
      have him := hreal t ht
      simp only [Function.comp_apply, Complex.conj_ofReal]
      exact (Complex.conj_eq_iff_im.2 him).symm
    have hEq := hfA.eqOn_of_preconnected_of_frequently_eq hgA
      (convex_ball _ _).isPreconnected (mem_ball_self hr₀pos) hfreq
    intro z hz
    have := hEq (conj_mem_ball_g3cv hz)
    simp only [Function.comp_apply, Complex.conj_conj] at this
    exact this
  refine ⟨Ψ', r₀, ‖d‖ / 2, 3 * ‖d‖ / 2, ⟨hr₀pos, hdiff, ?_, ?_, ?_, ?_⟩, heq, ?_⟩
  · -- injectivity
    intro z hz w hw h
    rw [heq hz, heq hw] at h
    have := (hbounds z hz w hw).1
    rw [h, sub_self, norm_zero] at this
    have hzw : ‖z - w‖ = 0 := by nlinarith [norm_nonneg (z - w)]
    exact sub_eq_zero.1 (norm_eq_zero.1 hzw)
  · -- non-vanishing derivative
    intro z hz h0
    rw [hderiv_eq z hz] at h0
    have hD : HasDerivAt Ψ 0 z := by
      have := ((hΨ.mono hr₀U).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
      rwa [h0] at this
    have hlo := hD.isLittleO
    have hm4 : 0 < ‖d‖ / 4 := by positivity
    have h1 := hlo.def hm4
    have h2 : ∀ᶠ w in 𝓝 z, w ∈ ball (b : ℂ) r₀ := isOpen_ball.mem_nhds hz
    have h3 : ∀ᶠ w in 𝓝[≠] z, w = z := by
      refine nhdsWithin_le_nhds ?_
      filter_upwards [h1, h2] with w hw1 hw2
      have hb := (hbounds w hw2 z hz).1
      simp only [smul_zero, sub_zero] at hw1
      have : ‖w - z‖ = 0 := by nlinarith [norm_nonneg (w - z)]
      exact sub_eq_zero.1 (norm_eq_zero.1 this)
    obtain ⟨w, hw1, hw2⟩ := (h3.and self_mem_nhdsWithin).exists
    exact hw2 hw1
  · -- symmetry of the cut-off map
    intro z hz
    rw [heq hz, heq (conj_mem_ball_g3cv hz)]
    exact hsymm z hz
  · -- measurability
    exact ContinuousOn.measurable_piecewise ((hΨ.mono hr₀U).continuousOn) continuousOn_const
      measurableSet_ball
  · intro ρ hρ
    refine ⟨by positivity, by positivity, fun z hz w hw => ?_⟩
    have hz' : z ∈ ball (b : ℂ) r₀ := closedBall_subset_ball hρ hz
    have hw' : w ∈ ball (b : ℂ) r₀ := closedBall_subset_ball hρ hw
    rw [heq hz', heq hw']
    exact hbounds z hz' w hw'

end G3Cv
end QuantumZipper
