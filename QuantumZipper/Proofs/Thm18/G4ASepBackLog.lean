import QuantumZipper.Proofs.Thm18.G4ASepDefs
import QuantumZipper.Proofs.Zipper.Cor15RezipRegDist
import QuantumZipper.Proofs.Loewner.TwoPoint
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G4 Core A-sep: the deterministic log-derivative node `BackLogSepStmt`

The integrand `w ↦ log ‖R'(R⁻¹ w)‖` (`R = revMap V T`) is bounded on a set of full
folded-circle measure. Points of the (compact) part of the closed upper half-plane that lie in
`closedBall 0 M` and outside the `δ`-thickening of the hull are either in `R(ℍ)` (then
`R⁻¹` is continuous there, `Im R⁻¹` is bounded above and below nearby, and
`TwoPoint.abs_log_norm_deriv_revMap_le` bounds the integrand), or real points at distance
`≥ δ` from the hull (local boundedness by Schwarz reflection, Lawler, *Conformally Invariant
Processes in the Plane*, §4.1). A finite subcover gives a uniform bound.
Own elementary compactness argument (task G4C-ASEP-LOG).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G4Core

/-- Local boundedness of `log ‖R'(R⁻¹ ·)‖` on `ℍ` near an interior point `x ∈ R(ℍ)`. -/
theorem backLog_locBound_of_mem_image {V : ℝ → ℝ} (hV : Continuous V) {T : ℝ} (hT : 0 ≤ T)
    {x : ℂ} (hx : x ∈ revMap V T '' H) :
    ∃ ρ > 0, ∃ C : ℝ, ∀ w ∈ H, w ∈ Metric.ball x ρ →
      |Real.log ‖deriv (revMap V T) (revMapInv V T w)‖| ≤ C := by
  obtain ⟨u0, hu0, rfl⟩ := hx
  have hu0' : 0 < u0.im := hu0
  have hc : ContinuousAt (fun w => (revMapInv V T w).im) (revMap V T u0) :=
    Complex.continuous_im.continuousAt.comp
      (Cor15Group.hasStrictDerivAt_revMapInv hV hT hu0).hasDerivAt.continuousAt
  have hval : (revMapInv V T (revMap V T u0)).im = u0.im := by
    rw [Cor15Group.revMapInv_revMap hV hT hu0]
  have hev : ∀ᶠ w in 𝓝 (revMap V T u0),
      (revMapInv V T w).im ∈ Ioo (u0.im / 2) (u0.im + 1) := by
    apply hc.eventually (isOpen_Ioo.mem_nhds _)
    show (revMapInv V T (revMap V T u0)).im ∈ _
    rw [hval]; constructor <;> linarith
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨ρ, hρ, |Real.log (Real.sqrt ((u0.im + 1) ^ 2 + 4 * T))| +
    (|Real.log (u0.im / 2)| + |Real.log (u0.im + 1)|), fun w _ hw => ?_⟩
  obtain ⟨h1, h2⟩ := hball w hw
  have hpos : 0 < (revMapInv V T w).im := by linarith
  refine (TwoPoint.abs_log_norm_deriv_revMap_le hV hT (u := revMapInv V T w) hpos
    h2.le).trans ?_
  gcongr
  rw [abs_le]
  constructor
  · have := Real.log_le_log (by positivity) h1.le
    linarith [neg_abs_le (Real.log (u0.im / 2)), abs_nonneg (Real.log (u0.im + 1))]
  · have := Real.log_le_log hpos h2.le
    linarith [le_abs_self (Real.log (u0.im + 1)), abs_nonneg (Real.log (u0.im / 2))]

/-- `BackLogSepStmt` from local boundedness at real points separated from the hull. -/
theorem backLogSepStmt_of_real
    (hreal : ∀ V : ℝ → ℝ, Continuous V → V 0 = 0 → ∀ T : ℝ, 0 ≤ T → ∀ (x : ℝ) (δ : ℝ),
      0 < δ → Disjoint (Metric.ball (x : ℂ) δ) (revHull V T) →
      ∃ ρ > 0, ∃ C : ℝ, ∀ w ∈ H, w ∈ Metric.ball (x : ℂ) ρ →
        |Real.log ‖deriv (revMap V T) (revMapInv V T w)‖| ≤ C) :
    BackLogSepStmt := by
  intro V hV hV0 T hT d r hr _ ⟨δ, hδ, hnull⟩
  set f : ℂ → ℝ := fun w => Real.log ‖deriv (revMap V T) (revMapInv V T w)‖ with hf
  set S : Set ℂ := (Metric.closedBall (0 : ℂ) (‖d‖ + r) ∩ {x | 0 ≤ x.im}) \
    Metric.thickening δ (revHull V T) with hS
  have hScpt : IsCompact S :=
    ((isCompact_closedBall _ _).inter_right
      (isClosed_le continuous_const Complex.continuous_im)).diff Metric.isOpen_thickening
  have hloc : ∀ x ∈ S, ∃ ρ > 0, ∃ C : ℝ, ∀ w ∈ H, w ∈ Metric.ball x ρ → |f w| ≤ C := by
    intro x hx
    obtain ⟨⟨_, hxim⟩, hxth⟩ := hx
    rcases (show (0 : ℝ) ≤ x.im from hxim).lt_or_eq with hpos | hzero
    · apply backLog_locBound_of_mem_image hV hT
      by_contra hn
      exact hxth (Metric.self_subset_thickening hδ _ ⟨hpos, hn⟩)
    · have hxr : x = ((x.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← hzero])
      rw [hxr]
      refine hreal V hV hV0 T hT x.re δ hδ ?_
      rw [Set.disjoint_left]
      intro z hz hzK
      apply hxth
      rw [Metric.mem_thickening_iff]
      refine ⟨z, hzK, ?_⟩
      rw [← hxr] at hz
      rw [dist_comm]; exact hz
  choose! ρ hρ C hC using hloc
  obtain ⟨t, htS, hcov⟩ := hScpt.elim_nhds_subcover (fun x => Metric.ball x (ρ x))
    (fun x hx => Metric.ball_mem_nhds x (hρ x hx))
  have hmeas : Measurable f :=
    Real.measurable_log.comp ((measurable_deriv (revMap V T)).norm.comp
      (Cor15Group.measurable_revMapInv hV hT))
  refine Integrable.of_bound hmeas.aestronglyMeasurable (∑ x ∈ t, |C x|) ?_
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hr, TwoPoint.foldedCircle_ae_norm_le d hr.le,
    measure_eq_zero_iff_ae_notMem.1 hnull] with w hwH hwn hwth
  have hwS : w ∈ S := ⟨⟨by simpa using hwn, show (0 : ℝ) ≤ w.im from le_of_lt hwH⟩, hwth⟩
  obtain ⟨x, hx, hwx⟩ := mem_iUnion₂.1 (hcov hwS)
  rw [Real.norm_eq_abs]
  exact (hC x (htS x hx) w hwH hwx).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun x => |C x|) (fun _ _ => abs_nonneg _) hx))

theorem im_sin_ofReal_add_mul_I_g4 (p q : ℝ) :
    (Complex.sin ((p : ℂ) + (q : ℂ) * Complex.I)).im = Real.cos p * Real.sinh q := by
  rw [Complex.sin_add_mul_I]
  simp [Complex.cos_ofReal_re, Complex.sinh_ofReal_re, Complex.sin_ofReal_im,
    Complex.cosh_ofReal_im]

/-- **Local bound at a real point separated from the hull.** `h = Im R⁻¹` is positive harmonic
on the half-disc `ℍ ∩ B(x, δ)` (which lies in `R(ℍ)`), so by the minimum principle on a
rectangle, compared with the harmonic function `Im sin(k(z - x))` (a Hopf-type lower bound),
`Im R⁻¹ w ≥ c Im w` near `x`; then `|log ‖R'(R⁻¹ w)‖| ≤ log (Im w / Im R⁻¹ w) ≤ -log c`.
Own elementary argument (a quantitative form of the Schwarz-reflection fact, Lawler §4.1). -/
theorem backLog_locBound_real {V : ℝ → ℝ} (hV : Continuous V) {T : ℝ} (hT : 0 ≤ T) (x δ : ℝ)
    (hδ : 0 < δ) (hdisj : Disjoint (Metric.ball (x : ℂ) δ) (revHull V T)) :
    ∃ ρ > 0, ∃ C : ℝ, ∀ w ∈ H, w ∈ Metric.ball (x : ℂ) ρ →
      |Real.log ‖deriv (revMap V T) (revMapInv V T w)‖| ≤ C := by
  set D : Set ℂ := {z | 0 < z.im ∧ dist z x < δ} with hD
  have hmem : ∀ z ∈ D, z ∈ revMap V T '' H := by
    intro z hz
    by_contra hn
    exact Set.disjoint_left.1 hdisj (Metric.mem_ball.2 hz.2) ⟨hz.1, hn⟩
  have hgA : ∀ z ∈ D, DifferentiableAt ℂ (revMapInv V T) z := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := hmem z hz
    exact (Cor15Group.hasStrictDerivAt_revMapInv hV hT hu).hasDerivAt.differentiableAt
  have hhpos : ∀ z ∈ D, 0 < (revMapInv V T z).im := fun z hz =>
    (Cor15Group.revMapInv_mem_H hV hT (hmem z hz)).1
  set a : ℝ := δ / 4 with ha
  have ha0 : 0 < a := by positivity
  set k : ℝ := Real.pi / (2 * a) with hk
  have hk0 : 0 < k := by positivity
  have hka : k * a = Real.pi / 2 := by rw [hk]; field_simp
  have hinD : ∀ z : ℂ, 0 < z.im → |z.re - x| ≤ a → z.im ≤ a → z ∈ D := by
    intro z h1 h2 h3
    refine ⟨h1, ?_⟩
    rw [Complex.dist_eq]
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    rw [abs_of_pos h1]; linarith
  have hseg_re : ∀ t : ℝ, ((t : ℂ) + (a : ℂ) * Complex.I).re = t := by intro t; simp
  have hseg_im : ∀ t : ℝ, ((t : ℂ) + (a : ℂ) * Complex.I).im = a := by intro t; simp
  set φ : ℝ → ℝ := fun t => (revMapInv V T ((t : ℂ) + (a : ℂ) * Complex.I)).im with hφ
  have hsegD : ∀ t ∈ Icc (x - a) (x + a), ((t : ℂ) + (a : ℂ) * Complex.I) ∈ D := by
    intro t ht
    refine hinD _ (by rw [hseg_im]; exact ha0) ?_ (by rw [hseg_im])
    rw [hseg_re, abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hφc : ContinuousOn φ (Icc (x - a) (x + a)) := by
    intro t ht
    have hl : Continuous fun t : ℝ => (t : ℂ) + (a : ℂ) * Complex.I := by fun_prop
    have h1 : ContinuousAt (fun t : ℝ => revMapInv V T ((t : ℂ) + (a : ℂ) * Complex.I)) t :=
      ContinuousAt.comp (g := revMapInv V T) (hgA _ (hsegD t ht)).continuousAt hl.continuousAt
    exact (Complex.continuous_im.continuousAt.comp h1).continuousWithinAt
  obtain ⟨t0, ht0, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.2 (by linarith)) hφc
  have hm0 : 0 < φ t0 := hhpos _ (hsegD t0 ht0)
  have hsa : 0 < Real.sinh (k * a) := Real.sinh_pos_iff.2 (by positivity)
  set m : ℝ := φ t0 / Real.sinh (k * a) with hmdef
  have hm : 0 < m := div_pos hm0 hsa
  have hmsa : m * Real.sinh (k * a) = φ t0 := by rw [hmdef]; field_simp
  have hkey : ∀ w : ℂ, 0 < w.im → w.im < a → |w.re - x| ≤ a / 4 →
      m * k * w.im / 4 ≤ (revMapInv V T w).im := by
    intro w hy hya hwre
    set ε : ℝ := w.im / 2 with hε
    have hε0 : 0 < ε := by positivity
    set U : Set ℂ := Ioo (x - a) (x + a) ×ℂ Ioo ε a with hU
    set F : ℂ → ℂ := fun z => revMapInv V T z - (m : ℂ) * Complex.sin ((k : ℂ) * (z - x))
      with hF
    have hFim : ∀ z : ℂ, (F z).im =
        (revMapInv V T z).im - m * (Real.cos (k * (z.re - x)) * Real.sinh (k * z.im)) := by
      intro z
      have e : (k : ℂ) * (z - x) = ((k * (z.re - x) : ℝ) : ℂ) + ((k * z.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      show (revMapInv V T z - (m : ℂ) * Complex.sin ((k : ℂ) * (z - x))).im = _
      rw [e, Complex.sub_im, Complex.im_ofReal_mul, im_sin_ofReal_add_mul_I_g4]
    have hre : ∀ z : ℂ, (Complex.I * F z).re = -(F z).im := by intro z; simp
    have hUopen : IsOpen U := isOpen_Ioo.reProdIm isOpen_Ioo
    have hclU : closure U = Icc (x - a) (x + a) ×ℂ Icc ε a := by
      rw [hU, Complex.closure_reProdIm, closure_Ioo (by linarith), closure_Ioo (by linarith)]
    have hclD : ∀ z ∈ closure U, z ∈ D := by
      intro z hz
      rw [hclU, Complex.mem_reProdIm] at hz
      exact hinD z (by linarith [hz.2.1]) (abs_le.2 ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩)
        hz.2.2
    have hdiffF : DifferentiableOn ℂ (fun z => Complex.exp (Complex.I * F z)) (closure U) := by
      intro z hz
      have h1 := hgA z (hclD z hz)
      have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (Complex.I *
          (revMapInv V T z - (m : ℂ) * Complex.sin ((k : ℂ) * (z - x))))) z := by fun_prop
      exact h2.differentiableWithinAt
    have hbd : Bornology.IsBounded U :=
      (Metric.isBounded_ball (x := (x : ℂ)) (r := δ)).subset
        (fun z hz => (hclD z (subset_closure hz)).2)
    have hfr : ∀ z ∈ frontier U,
        ‖Complex.exp (Complex.I * F z)‖ ≤ Real.exp (m * Real.sinh (k * ε)) := by
      intro z hz
      rw [hUopen.frontier_eq] at hz
      obtain ⟨hzc, hzU⟩ := hz
      have hzD := hclD z hzc
      rw [hclU, Complex.mem_reProdIm] at hzc
      rw [Complex.norm_exp, Real.exp_le_exp, hre, hFim]
      have hpos := hhpos z hzD
      have hsε : 0 ≤ Real.sinh (k * ε) := (Real.sinh_pos_iff.2 (by positivity)).le
      have hmsε : 0 ≤ m * Real.sinh (k * ε) := mul_nonneg hm.le hsε
      by_cases htop : z.im = a
      · have hz' : (z.re : ℂ) + (a : ℂ) * Complex.I = z :=
          Complex.ext (by simp) (by simp [htop])
        have h1 : φ t0 ≤ φ z.re := hmin hzc.1
        have h2 : φ z.re = (revMapInv V T z).im := by simp only [hφ, hz']
        have h3 : Real.cos (k * (z.re - x)) * Real.sinh (k * z.im) ≤ Real.sinh (k * a) := by
          rw [htop]; exact mul_le_of_le_one_left hsa.le (Real.cos_le_one _)
        have h4 := mul_le_mul_of_nonneg_left h3 hm.le
        linarith
      · by_cases hlat : z.re = x - a ∨ z.re = x + a
        · have hc0 : Real.cos (k * (z.re - x)) = 0 := by
            rcases hlat with h | h
            · rw [h, show k * (x - a - x) = -(k * a) by ring, hka, Real.cos_neg,
                Real.cos_pi_div_two]
            · rw [h, show k * (x + a - x) = k * a by ring, hka, Real.cos_pi_div_two]
          rw [hc0]; simp only [zero_mul, mul_zero, sub_zero]; linarith
        · have hzε : z.im = ε := by
            by_contra hne
            apply hzU
            rw [hU, Complex.mem_reProdIm]
            push Not at hlat
            exact ⟨⟨lt_of_le_of_ne hzc.1.1 (Ne.symm hlat.1), lt_of_le_of_ne hzc.1.2 hlat.2⟩,
              ⟨lt_of_le_of_ne hzc.2.1 (Ne.symm hne), lt_of_le_of_ne hzc.2.2 htop⟩⟩
          have h3 : Real.cos (k * (z.re - x)) * Real.sinh (k * z.im) ≤ Real.sinh (k * ε) := by
            rw [hzε]; exact mul_le_of_le_one_left hsε (Real.cos_le_one _)
          have h4 := mul_le_mul_of_nonneg_left h3 hm.le
          linarith
    have hwU : w ∈ U := by
      rw [hU, Complex.mem_reProdIm]
      rw [abs_le] at hwre
      exact ⟨⟨by linarith [hwre.1], by linarith [hwre.2]⟩, ⟨by linarith, hya⟩⟩
    have hw := Complex.norm_le_of_forall_mem_frontier_norm_le hbd hdiffF.diffContOnCl hfr
      (subset_closure hwU)
    rw [Complex.norm_exp, Real.exp_le_exp, hre, hFim] at hw
    set p : ℝ := k * (w.re - x) with hp
    have hpabs : |p| ≤ 1 / 2 := by
      rw [hp, abs_mul, abs_of_pos hk0]
      calc k * |w.re - x| ≤ k * (a / 4) := mul_le_mul_of_nonneg_left hwre hk0.le
        _ = Real.pi / 8 := by rw [show k * (a / 4) = k * a / 4 by ring, hka]; ring
        _ ≤ 1 / 2 := by linarith [Real.pi_le_four]
    have hp2 : p ^ 2 ≤ 1 / 4 := by
      rw [← sq_abs]; nlinarith [abs_nonneg p]
    have hcos : 7 / 8 ≤ Real.cos p := by
      have := Real.one_sub_sq_div_two_le_cos (x := p); linarith
    set S : ℝ := Real.sinh (k * w.im) with hS
    set S2 : ℝ := Real.sinh (k * ε) with hS2
    have hS2nn : 0 ≤ S2 := (Real.sinh_pos_iff.2 (by positivity)).le
    have hSS2 : 2 * S2 ≤ S := by
      have e : k * w.im = 2 * (k * ε) := by rw [hε]; ring
      rw [hS, e, Real.sinh_two_mul]
      nlinarith [Real.one_le_cosh (k * ε)]
    have hSy : k * w.im ≤ S := Real.self_le_sinh_iff.2 (by positivity)
    have hSnn : 0 ≤ S := by linarith
    have e1 : m * (7 / 8 * S) ≤ m * (Real.cos p * S) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcos hSnn) hm.le
    have e2 : m * (2 * S2) ≤ m * S := mul_le_mul_of_nonneg_left hSS2 hm.le
    have e3 : m * (k * w.im) ≤ m * S := mul_le_mul_of_nonneg_left hSy hm.le
    nlinarith
  refine ⟨a / 4, by positivity, |Real.log (m * k / 4)|, fun w hw hwb => ?_⟩
  have hy : 0 < w.im := hw
  rw [Metric.mem_ball, Complex.dist_eq] at hwb
  have hre1 : |w.re - x| ≤ a / 4 := by
    have := Complex.abs_re_le_norm (w - x); simp at this; linarith
  have him1 : w.im < a := by
    have := Complex.abs_im_le_norm (w - x); simp at this
    linarith [le_abs_self w.im]
  have hwD : w ∈ D := hinD w hy (by linarith) him1.le
  obtain ⟨huH, hRu⟩ := Cor15Group.revMapInv_mem_H hV hT (hmem w hwD)
  rw [QuantumZipper.log_norm_deriv_revMap V hV hT huH]
  refine (TwoPoint.abs_re_integral_sq_le hV huH hT).trans ?_
  have hL := TwoPoint.log_im_revMap hV huH hT
  rw [hRu] at hL
  have hlow := hkey w hy him1 hre1
  have hl2 : Real.log (m * k * w.im / 4) ≤ Real.log (revMapInv V T w).im :=
    Real.log_le_log (by positivity) hlow
  rw [show m * k * w.im / 4 = (m * k / 4) * w.im by ring,
    Real.log_mul (by positivity) hy.ne'] at hl2
  linarith [neg_abs_le (Real.log (m * k / 4))]

/-- **`BackLogSepStmt` holds.** -/
theorem backLogSepStmt_holds : BackLogSepStmt :=
  backLogSepStmt_of_real fun _ hV _ _ hT x δ hδ hdisj => backLog_locBound_real hV hT x δ hδ hdisj

end G4Core
end Thm18Asm
end QuantumZipper
