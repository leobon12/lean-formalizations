import LQGMetric.Papers.DFGPS.L2_1PolarSwap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.1: the polar formula at a fixed `(ε, z)`

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:715–722: "The functions
`w ↦ ψ_ε(z−w)` and `w ↦ p_{ε²/2}(z,w)` are each radially symmetric about `z` … Using the circle
average process we may therefore write in polar coordinates
`g*_ε(z) = (2/ε²) ∫_0^∞ r g_r(z) e^{−r²/ε²} dr`, `ĝ*_ε(z) = (2/ε²) ∫_0^{ε^{1/2}} r g_r(z) ψ_ε(r) e^{−r²/ε²} dr`."

* `Lem2_1RadialPairing` (open node): for a test function `φ` radial about `z`, a.s.
  `⟨g, φ⟩ = ∫_0^∞ 2π r φ(z + r) g_r(z) dr` (polar coordinates with the circle averages).
* `lem2_1PolarPoint_of : Lem2_1RadialPairing → Lem2_1PolarPoint`: apply it to the radial test
  functions `p_s(z,·)ρ_n(· − z) − ψ_ε(z − ·)p_s(z,·)`, swap the cutoffs
  (`ae_tendsto_heatTrunc_sub_radTrunc`) and let `n → ∞` by dominated convergence (Lemma 2.2 bound).
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace LQGMetric.DFGPS

open LFPP

/-- **Pairing with a radial test function** (DFGPS T:715–717): for a whole-plane GFF `g`, a jointly
continuous version `H` of its circle-average process, and a test function `φ` radial about `z`,
a.s. `⟨g, φ⟩ = ∫_0^∞ 2π r φ(z + r) H(r, z) dr`. Open node. -/
def Lem2_1RadialPairing.{u} : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (g : Ω → DistC) (H : ℝ → ℂ → Ω → ℝ),
    IsWholePlaneGFF g P → IsCircleAvgVersion g P H →
    ∀ (z : ℂ) (φ : TestC), (∀ w : ℂ, φ w = φ (z + ((‖w - z‖ : ℝ) : ℂ))) →
    ∀ᵐ ω ∂P, g ω φ = ∫ r in Ioi (0 : ℝ), 2 * Real.pi * r * φ (z + (r : ℂ)) * H r z ω

lemma heatKernel_radial (s : ℝ) (z w : ℂ) :
    heatKernel s z w = heatKernel s z (z + ((‖w - z‖ : ℝ) : ℂ)) := by
  unfold heatKernel
  rw [show z - (z + ((‖w - z‖ : ℝ) : ℂ)) = -((‖w - z‖ : ℝ) : ℂ) by ring, norm_neg,
    Complex.norm_real, norm_norm, norm_sub_rev]

lemma heatKernel_add_real (s : ℝ) (z : ℂ) (r : ℝ) :
    heatKernel s z (z + r) = (2 * Real.pi * s)⁻¹ * Real.exp (-r ^ 2 / (2 * s)) := by
  unfold heatKernel
  rw [show z - (z + (r : ℂ)) = -(r : ℂ) by ring, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]

lemma locBump_neg_real {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    locBump ε hε (-(r : ℂ)) = locBump ε hε (r : ℂ) := by
  rw [locBump_radial ε hε (-(r : ℂ)), locBump_radial ε hε (r : ℂ), norm_neg]

/-- the radial test function `p_s(z,·)ρ_n(· − z) − ψ_ε(z − ·)p_s(z,·)` -/
def polarTest (ε : ℝ) (hε : 0 < ε) (z : ℂ) (n : ℕ) : TestC :=
  radTrunc (ε ^ 2 / 2) z n - locTest ε hε z

lemma polarTest_apply (ε : ℝ) (hε : 0 < ε) (z : ℂ) (n : ℕ) (w : ℂ) :
    polarTest ε hε z n w = heatKernel (ε ^ 2 / 2) z w * radCut n (w - z) -
      locBump ε hε (z - w) * heatKernel (ε ^ 2 / 2) z w := rfl

lemma polarTest_radial (ε : ℝ) (hε : 0 < ε) (z : ℂ) (n : ℕ) (w : ℂ) :
    polarTest ε hε z n w = polarTest ε hε z n (z + ((‖w - z‖ : ℝ) : ℂ)) := by
  rw [polarTest_apply, polarTest_apply, ← heatKernel_radial, add_sub_cancel_left,
    show z - (z + ((‖w - z‖ : ℝ) : ℂ)) = -((‖w - z‖ : ℝ) : ℂ) by ring, locBump_neg_real,
    radCut_radial n (w - z), locBump_radial ε hε (z - w), norm_sub_rev]

lemma polarTest_add_real (ε : ℝ) (hε : 0 < ε) (z : ℂ) (n : ℕ) (r : ℝ) :
    2 * Real.pi * r * polarTest ε hε z n (z + r) =
      2 / ε ^ 2 * (r * (radCut n (r : ℂ) - locBump ε hε (r : ℂ)) *
        Real.exp (-r ^ 2 / ε ^ 2)) := by
  rw [polarTest_apply, add_sub_cancel_left, show z - (z + (r : ℂ)) = -(r : ℂ) by ring,
    locBump_neg_real, heatKernel_add_real]
  have hε0 : ε ≠ 0 := by
    intro h0; simp [h0] at hε
  have hpi := Real.pi_pos.ne'
  rw [show 2 * (ε ^ 2 / 2) = ε ^ 2 by ring]
  field_simp

/-- **The polar formula at a fixed `(ε, z)`** from the radial pairing formula. -/
theorem lem2_1PolarPoint_of.{u} (HR : Lem2_1RadialPairing.{u}) : Lem2_1PolarPoint.{u} := by
  intro Ω _ P g H hg hH ε hε z
  set s := ε ^ 2 / 2
  have hs : 0 < s := by positivity
  obtain ⟨A, hA, hAb⟩ := lem2_2 hg hH (‖z‖ + 1)
  have hz : z ∈ ball (0 : ℂ) (‖z‖ + 1) := by rw [mem_ball_zero_iff]; linarith
  have hPt : ∀ᵐ ω ∂P, ∀ n : ℕ, g ω (polarTest ε hε z n) =
      ∫ r in Ioi (0 : ℝ), 2 * Real.pi * r * polarTest ε hε z n (z + (r : ℂ)) * H r z ω :=
    ae_all_iff.2 fun n => HR P g H hg hH z _ (polarTest_radial ε hε z n)
  filter_upwards [hg.ae_tendsto_heatMollify ε hε.ne' z, ae_tendsto_heatTrunc_sub_radTrunc hg hs z,
    hPt, hAb (1 / 2) (by norm_num)] with ω h1 h2 h3 h4
  obtain ⟨C, hC⟩ := h4
  set f : ℝ → ℝ := fun r => 2 / ε ^ 2 * (r * H r z ω * (1 - locBump ε hε (r : ℂ)) *
    Real.exp (-r ^ 2 / ε ^ 2))
  -- dominated convergence for the polar integrals
  have hDCT : Tendsto (fun n : ℕ => g ω (polarTest ε hε z n)) atTop
      (𝓝 (∫ r in Ioi 0, f r)) := by
    simp only [h3]
    have hHc : ContinuousOn (fun r => H r z ω) (Ioi 0) :=
      (hH.cont ω).comp (continuous_id.prodMk continuous_const).continuousOn
        fun r hr => ⟨hr, mem_univ _⟩
    refine tendsto_integral_of_dominated_convergence (fun r => 2 / ε ^ 2 * (|C| *
      ((A + r ^ 2 + r) * Real.exp (-(1 / ε ^ 2) * r ^ 2)))) (fun n => ?_)
      (((integrableOn_gaussW A (by positivity)).const_mul _).const_mul _) (fun n => ?_) ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      exact ((continuousOn_const.mul continuousOn_id).mul
        ((polarTest ε hε z n).continuous.comp (continuous_const.add
          Complex.continuous_ofReal)).continuousOn).mul hHc
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
      have hr : 0 < r := hr
      rw [polarTest_add_real]
      have hI := radCut_mem_Icc n (r : ℂ)
      have hd : |radCut n (r : ℂ) - locBump ε hε (r : ℂ)| ≤ 1 := by
        have := locBump_nonneg ε hε (r : ℂ); have := locBump_le_one ε hε (r : ℂ)
        rw [abs_le]; constructor <;> linarith [hI.1, hI.2]
      have hFb : |H r z ω| ≤ |C| * (A / r + r + 1) := by
        have hm := max_log_le hA.le hr
        have hm1 : (1 : ℝ) ≤ max (max (A * Real.log (1 / r))
            (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1 := le_max_right _ _
        calc |H r z ω| ≤ C * max (max (A * Real.log (1 / r))
              (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1 := hC r hr z hz
          _ ≤ |C| * max (max (A * Real.log (1 / r))
              (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1 :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
          _ ≤ |C| * (A / r + r + 1) := mul_le_mul_of_nonneg_left hm (abs_nonneg C)
      have he : Real.exp (-r ^ 2 / ε ^ 2) = Real.exp (-(1 / ε ^ 2) * r ^ 2) := by
        congr 1; ring
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 2 / ε ^ 2), abs_of_pos hr,
        abs_of_pos (Real.exp_pos _), he]
      set E := Real.exp (-(1 / ε ^ 2) * r ^ 2)
      calc 2 / ε ^ 2 * (r * |radCut n (r : ℂ) - locBump ε hε (r : ℂ)| * E) * |H r z ω|
          = 2 / ε ^ 2 * (r * |radCut n (r : ℂ) - locBump ε hε (r : ℂ)| * E * |H r z ω|) := by
            ring
        _ ≤ 2 / ε ^ 2 * (r * 1 * E * (|C| * (A / r + r + 1))) := by gcongr
        _ = 2 / ε ^ 2 * (|C| * ((A + r ^ 2 + r) * E)) := by
            field_simp
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈r⌉₊] with n hn
      have hrn : r ≤ (n : ℝ) + 1 := by
        have := (Nat.le_ceil r).trans (Nat.cast_le.2 hn); linarith
      have hr0 : (0 : ℝ) < r := hr
      rw [polarTest_add_real, radCut_eq_one n (by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]; exact hrn)]
      simp only [f]; ring
  -- assemble
  have hsum : Tendsto (fun n : ℕ => (g ω (heatTrunc s z n) - g ω (radTrunc s z n)) +
      g ω (polarTest ε hε z n)) atTop (𝓝 (0 + ∫ r in Ioi 0, f r)) := h2.add hDCT
  have hlim : Tendsto (fun n : ℕ => g ω (heatTrunc s z n) - locMollify ε hε (g ω) z) atTop
      (𝓝 (heatMollify ε (g ω) z - locMollify ε hε (g ω) z)) := h1.sub_const _
  have e : (fun n : ℕ => (g ω (heatTrunc s z n) - g ω (radTrunc s z n)) +
      g ω (polarTest ε hε z n)) = fun n : ℕ => g ω (heatTrunc s z n) -
        locMollify ε hε (g ω) z := by
    funext n
    simp only [polarTest, map_sub, locMollify]
    ring
  rw [e, zero_add] at hsum
  rw [tendsto_nhds_unique hlim hsum, integral_const_mul]

end LQGMetric.DFGPS
