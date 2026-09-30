import QuantumZipper.Proofs.Zipper.FieldLawler2Semi

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Field–Lawler (2.3)–(2.4) at the outer circle: a pointwise majorant (task FL2-FLUX24)

Source: L. S. Field, G. F. Lawler, *Escape probability and transience for SLE*, EJP 20 (2015),
p. 6, (2.3)–(2.4) (`literature/1407.3314.pdf`), used in the proof of Prop 3.4 as
`E_H(C_R, C_ε) ≤ c ε / R`. FL state it from "the Poisson kernel in `ℍ \ D_r`" without details.

`fl2_outer_majorant`: a harmonic `w` with `0 ≤ w ≤ 1` on an open `U ⊆ ℍ ∩ {ε < |z| < R}`,
tending to `0` at every frontier point off `D̄_ε`, satisfies near the outer circle
`w z ≤ 32π ε Im z (1/|z|² - 1/R²)`.

Proof (own elementary comparison argument, standard; recorded as own argument): with `a = 3ε/2`,
step 1 is the semicircle comparison `w ≤ arg((z-a)/(z+a))` of `FieldLawler2Semi`; step 2 compares
`w` on `U ∩ {|z| > R/2}` with the harmonic majorant
`M z = 32π ε (Im(-1/z) - Im z / R²)`, which is `≥ 0` inside `D_R ∩ ℍ` and dominates
`24π ε Im z / |z|²` on `|z| = R/2`. Both steps use the weak maximum principle
`lwExc_harm_le_zero`.
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open QuantumZipper.Thm18Asm.LWFar

lemma fl2Flux_maj_im (K R : ℝ) (y : ℂ) :
    ((K : ℂ) * (-(y⁻¹) - y / ((R ^ 2 : ℝ) : ℂ))).im = K * y.im * (1 / ‖y‖ ^ 2 - 1 / R ^ 2) := by
  rw [Complex.im_ofReal_mul, sub_im, neg_im, Complex.inv_im, Complex.div_ofReal_im,
    Complex.normSq_eq_norm_sq]
  ring

lemma fl2Flux_maj_harm (K R : ℝ) {z : ℂ} (hz : z ≠ 0) :
    InnerProductSpace.HarmonicAt (fun y : ℂ => K * y.im * (1 / ‖y‖ ^ 2 - 1 / R ^ 2)) z := by
  have hF : AnalyticAt ℂ (fun y : ℂ => (K : ℂ) * (-(y⁻¹) - y / ((R ^ 2 : ℝ) : ℂ))) z :=
    analyticAt_const.mul ((analyticAt_inv hz).neg.sub (analyticAt_id.div_const))
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).1 hF.harmonicAt_im
  exact Eventually.of_forall fun y => fl2Flux_maj_im K R y

/-- **Field–Lawler (2.3)–(2.4) at the outer circle** (EJP 20 (2015), p. 6), pointwise-majorant
form: near `C_R`, the function `w` (e.g. the harmonic measure of `C_ε` in a subdomain of
`ℍ ∩ {ε < |z| < R}`) is at most `32π ε Im z (1/|z|² - 1/R²)`. -/
theorem fl2_outer_majorant : ∀ (ε R : ℝ) (U : Set ℂ) (w : ℂ → ℝ), 0 < ε → 4 * ε ≤ R →
    IsOpen U → U ⊆ {z | 0 < z.im ∧ ε < ‖z‖ ∧ ‖z‖ < R} → InnerProductSpace.HarmonicOnNhd w U →
    (∀ z ∈ U, 0 ≤ w z ∧ w z ≤ 1) →
    (∀ x₀ ∈ frontier U, ε < ‖x₀‖ → ∀ δ > 0, ∃ ρ > 0, ∀ y ∈ U, dist y x₀ < ρ → w y ≤ δ) →
    ∀ z ∈ U, R / 2 ≤ ‖z‖ → w z ≤ 32 * π * ε * z.im * (1 / ‖z‖ ^ 2 - 1 / R ^ 2) := by
  intro ε R U w hε hR hUo hUsub hw h01 hfr
  have ha : 0 < 3 * ε / 2 := by positivity
  have hRpos : 0 < R := by linarith
  have hne0 : ∀ y ∈ U, y ≠ 0 := fun y hy h0 => by
    have := (hUsub hy).2.1; rw [h0, norm_zero] at this; linarith
  obtain ⟨M, hM⟩ : ∃ M : ℂ → ℝ, M = fun y => 32 * π * ε * y.im * (1 / ‖y‖ ^ 2 - 1 / R ^ 2) :=
    ⟨_, rfl⟩
  have hMy : ∀ y, M y = 32 * π * ε * y.im * (1 / ‖y‖ ^ 2 - 1 / R ^ 2) := fun y => by rw [hM]
  have hMharm : ∀ y ∈ U, InnerProductSpace.HarmonicAt M y := fun y hy => by
    rw [hM]; exact fl2Flux_maj_harm _ R (hne0 y hy)
  have hMnn : ∀ y ∈ U, 0 ≤ M y := by
    intro y hy
    obtain ⟨him, hε', hR'⟩ := hUsub hy
    have hy0 : 0 < ‖y‖ := by linarith
    have h1 : 1 / R ^ 2 ≤ 1 / ‖y‖ ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    rw [hMy]
    exact mul_nonneg (by positivity) (by linarith)
  -- step 1: comparison with the angle subtended by `[-a, a]`, `a = 3ε/2`
  have step1 : ∀ y ∈ U, w y ≤ fl2SemiAng (3 * ε / 2) y := by
    have hmax := lwExc_harm_le_zero (f := fun y => w y - fl2SemiAng (3 * ε / 2) y) hUo
      (fun y hy => (hw y hy).sub (fl2Semi_harm ha (hUsub hy).1))
      (by
        intro x₀ hx₀ δ hδ
        by_cases hx : ‖x₀‖ < 3 * ε / 2
        · refine ⟨3 * ε / 2 - ‖x₀‖, by linarith, fun y hy hyd => ?_⟩
          have hya : ‖y‖ < 3 * ε / 2 := by
            have : ‖y‖ ≤ ‖x₀‖ + dist y x₀ := by
              rw [dist_eq_norm]; exact norm_le_norm_add_norm_sub' y x₀
            linarith
          have h1 := fl2Semi_ge_one ha (hUsub hy).1 hya
          have h2 := (h01 y hy).2
          show w y - fl2SemiAng (3 * ε / 2) y ≤ δ
          linarith
        · push Not at hx
          obtain ⟨ρ, hρ, hρU⟩ := hfr x₀ hx₀ (by linarith) δ hδ
          refine ⟨ρ, hρ, fun y hy hyd => ?_⟩
          have h1 := hρU y hy hyd
          have h2 := fl2Semi_nonneg (3 * ε / 2) y (hUsub hy).1.le ha.le
          show w y - fl2SemiAng (3 * ε / 2) y ≤ δ
          linarith)
      (fun δ hδ => ⟨R, fun y hy hyR => absurd hyR (not_le.2 (hUsub hy).2.2)⟩)
    intro y hy
    have := hmax y hy
    linarith
  -- on the circle `|z| = R/2`
  have hcirc : ∀ y ∈ U, ‖y‖ = R / 2 → w y ≤ M y := by
    intro y hy hyn
    have h1 := step1 y hy
    have h2 := fl2Semi_le hε (hUsub hy).1 (by rw [hyn]; linarith)
    have h3 : 24 * π * ε * y.im / ‖y‖ ^ 2 = M y := by
      rw [hMy, hyn]; field_simp; ring
    linarith
  -- step 2: comparison with `M` on `U ∩ {|z| > R/2}`
  have hVo : IsOpen (U ∩ {y | R / 2 < ‖y‖}) := hUo.inter (isOpen_lt continuous_const continuous_norm)
  have hmax2 := lwExc_harm_le_zero (f := fun y => w y - M y) hVo
    (fun y hy => (hw y hy.1).sub (hMharm y hy.1))
    (by
      intro x₀ hx₀ δ hδ
      have hx₀cl : x₀ ∈ closure (U ∩ {y | R / 2 < ‖y‖}) := hx₀.1
      have hx₀V : x₀ ∉ U ∩ {y | R / 2 < ‖y‖} := by
        intro h; exact hx₀.2 (by rw [hVo.interior_eq]; exact h)
      have hnorm : R / 2 ≤ ‖x₀‖ := by
        have : closure (U ∩ {y | R / 2 < ‖y‖}) ⊆ {y | R / 2 ≤ ‖y‖} :=
          closure_minimal (fun y hy => show R / 2 ≤ ‖y‖ from le_of_lt hy.2) (isClosed_le continuous_const continuous_norm)
        exact this hx₀cl
      by_cases hxU : x₀ ∈ U
      · have hxn : ‖x₀‖ = R / 2 := by
          by_contra hne
          exact hx₀V ⟨hxU, lt_of_le_of_ne hnorm (Ne.symm hne)⟩
        have hc : ContinuousAt (fun y => w y - M y) x₀ :=
          ((hw x₀ hxU).sub (hMharm x₀ hxU)).1.continuousAt
        have hval : w x₀ - M x₀ < δ := by linarith [hcirc x₀ hxU hxn]
        have hev := hc.eventually (gt_mem_nhds hval)
        obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 hev
        exact ⟨ρ, hρ, fun y _ hyd => (hball hyd).le⟩
      · have hxfr : x₀ ∈ frontier U :=
          ⟨closure_mono inter_subset_left hx₀cl, by rw [hUo.interior_eq]; exact hxU⟩
        obtain ⟨ρ, hρ, hρU⟩ := hfr x₀ hxfr (by linarith) δ hδ
        refine ⟨ρ, hρ, fun y hy hyd => ?_⟩
        have h1 := hρU y hy.1 hyd
        have h2 := hMnn y hy.1
        show w y - M y ≤ δ
        linarith)
    (fun δ hδ => ⟨R, fun y hy hyR => absurd hyR (not_le.2 (hUsub hy.1).2.2)⟩)
  intro z hz hzR
  rw [← hMy]
  rcases eq_or_lt_of_le hzR with h | h
  · exact hcirc z hz h.symm
  · have := hmax2 z ⟨hz, h⟩
    linarith

end FieldLawler
end QuantumZipper
