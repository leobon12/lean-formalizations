import QuantumZipper.Proofs.Section5.Prop16ActRegBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, node B′ input: the free-arc regularity `Prop16ActRegStmt` (proved)

`prop16ActReg_holds : Prop16ActRegStmt`. For `x ∈ (a,b)` and `r = 2^{-n}` with
`2r < gap(x)`, almost surely `avgReg (h0 + X) n x = (h0 + X)(fc(x, r))`.

Proof (own argument, following the domain-Markov route of the paper's proof of Prop. 1.6,
Sheffield arXiv:1012.4797 p. 25, with Sheffield, *Gaussian free fields for mathematicians*,
PTRF 139 (2007), Thm 2.17, in the half-disc form M7 `K3.mixedFreeCouplingHalfDisc_holds`):

1. The countable family of circles `fc(x, r)`, `fc(d_j, r)` (`d_j = dyadicRoundC (j + j₀) x`,
   eventually `δ`-close to `x`) lies in `D ∪ (a,b)` and is admissible for the mixed space.
2. On the M7 coupling space, for each such circle `μ`, a.s. `Y μ = X_f μ − X_f ρ₀ + ∫ g dμ`,
   with `g ∘ foldH` harmonic near `x`. The free field's dyadic circle averages converge to its
   value on `fc(x,r)` (`BdryExist.ae_avgReg_spec`), and `∫ g d fc(d_j, r) = g(d_j) → g(x)`
   (mean value property). Hence `Y(fc(d_j, r)) → Y(fc(x, r))` a.s.
3. This is a measurable property of the law of the family, which the mixed GFF pins
   (`ae_family_of_isMixedGFF`), so it holds for `X`; adding the (continuous) `h0` part gives the
   claim.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal Real

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area.G

/-- An admissible probability measure giving no mass to `ball x R` (own elementary lemma). -/
theorem exists_rho0_far (x : ℝ) {R : ℝ} (hR : 0 < R) :
    ∃ ρ₀ : Measure ℂ, IsAdmissibleH ρ₀ ∧ ρ₀ Set.univ = 1 ∧ ρ₀ (ball (x : ℂ) R) = 0 := by
  set c : ℂ := (x : ℂ) + ((3 * R : ℝ) : ℂ) * Complex.I with hc
  have hcim : c.im = 3 * R := by simp [hc]
  have hcH : c ∈ Hbar := show (0 : ℝ) ≤ c.im by rw [hcim]; linarith
  refine ⟨foldedCircle c R, isAdmissibleH_foldedCircle hcH hR, measure_univ, ?_⟩
  refine measure_mono_null (show ball (x : ℂ) R ⊆ (closedBall c R ∩ Hbar)ᶜ from
    fun u hu hK => ?_) (K3.foldedCircle_compl_eq_zero hcH hR.le)
  have h1 : dist u (x : ℂ) < R := hu
  have h2 : dist u c ≤ R := hK.1
  have e1 : |(u - (x : ℂ)).im| ≤ ‖u - (x : ℂ)‖ := Complex.abs_im_le_norm _
  have e2 : |(u - c).im| ≤ ‖u - c‖ := Complex.abs_im_le_norm _
  rw [← dist_eq_norm] at e1 e2
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, hcim] at e1 e2
  have := abs_le.1 (e2.trans h2)
  have := (le_abs_self u.im).trans e1
  linarith

/-- **Free-arc regularity of the actual field (node `Prop16ActRegStmt`).** -/
theorem prop16ActReg_holds : Prop16ActRegStmt := by
  intro γ D c d a b h0 Ω _ P X hH x hx n hn
  obtain ⟨⟨-, -, hgeom, -, hca, hbd, hh0, hP, hX, -, -⟩, -, -⟩ := hH
  have := hP
  set r := radius n with hrdef
  set G := palmGap D a b x with hGdef
  have hr : 0 < r := radius_pos n
  set δ := (G - r) / 4 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set r' := r + 2 * δ with hr'def
  have hr'G : r' < G := by rw [hr'def, hδdef]; linarith
  have hxH : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((x : ℂ)).im by simp
  obtain ⟨j0, hj0⟩ : ∃ j0, ∀ j ≥ j0, dist (dyadicRoundC j (x : ℂ)) (x : ℂ) < δ :=
    Metric.tendsto_atTop.1 (RegClosure.tendsto_dyadicRoundC (x : ℂ)) δ hδ
  set dj : ℕ → ℂ := fun i => dyadicRoundC (i + j0) (x : ℂ) with hdj
  have hdjlim : Tendsto dj atTop (𝓝 (x : ℂ)) :=
    (tendsto_add_atTop_iff_nat j0).2 (RegClosure.tendsto_dyadicRoundC (x : ℂ))
  set ctr : ℕ → ℂ := fun i => if i = 0 then (x : ℂ) else dj (i - 1) with hctr
  have hctr0 : ctr 0 = x := by simp [hctr]
  have hctrS : ∀ i, ctr (i + 1) = dj i := fun i => by simp [hctr]
  have hctrH : ∀ i, ctr i ∈ Hbar := fun i => by
    rcases i with _ | i
    · rw [hctr0]; exact hxH
    · rw [hctrS]; exact dyadicRoundC_ofReal_mem_Hbar _ x
  have hctrd : ∀ i, dist (ctr i) (x : ℂ) < δ := fun i => by
    rcases i with _ | i
    · rw [hctr0, dist_self]; exact hδ
    · rw [hctrS]; exact hj0 _ (Nat.le_add_left _ _)
  have hball : ∀ i, closedBall (ctr i) r ∩ Hbar ⊆ closedBall (x : ℂ) r' := fun i u hu => by
    have h1 : dist u (ctr i) ≤ r := hu.1
    rw [mem_closedBall]
    linarith [dist_triangle u (ctr i) (x : ℂ), hctrd i]
  -- admissibility of the family for the mixed space
  obtain ⟨W, hWo, hWV⟩ := locGood_exists_open hgeom hca hbd
  have hm : ∀ i, IsAdmissibleDual D (mixedSpace D (realSet (Icc c d)))
      (foldedCircle (ctr i) r) := fun i =>
    locGood_isAdmissible_circle hgeom hca hbd hWo hWV (hctrH i) hr
      (closedBall_subset_of_gap hWV (by linarith [hctrd i]))
  -- the event
  set T : Set (ℕ → ℝ) := {y | Tendsto (fun i => y (i + 1)) atTop (𝓝 (y 0))} with hTdef
  have hT : MeasurableSet T :=
    measurableSet_tendsto_seq (u := fun y i => y (i + 1)) (L := fun y => y 0)
      (Measurable.of_eval fun i => measurable_pi_apply _) (measurable_pi_apply 0)
  -- the M7 coupling at `x`
  have hxcd : x ∈ Ioo c d := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hG0 : 0 < G := by linarith
  obtain ⟨ρ₀, hρadm, hρ1, hρB⟩ := exists_rho0_far x hG0
  obtain ⟨Ω₀, _, P₀, Y, Xf, g, E', _, Ξ, hP₀, hY, hXf, -, -, hgh, -, hrep⟩ :=
    K3.mixedFreeCouplingHalfDisc_holds D c d x G r' ρ₀ hgeom hxcd (by positivity) hr'G
      (ball_inter_H_subset_D le_rfl) hρadm hρ1 hρB
  have := hP₀
  have hYae : ∀ᵐ ω ∂P₀, (fun i => Y ω (foldedCircle (ctr i) r)) ∈ T := by
    have hrep' : ∀ᵐ ω ∂P₀, ∀ i, Y ω (foldedCircle (ctr i) r) =
        Xf ω (foldedCircle (ctr i) r) - ((foldedCircle (ctr i) r) Set.univ).toReal * Xf ω ρ₀ +
          ∫ z, g ω z ∂(foldedCircle (ctr i) r) :=
      ae_all_iff.2 fun i => hrep _ (isAdmissibleH_foldedCircle (hctrH i) hr)
        (measure_mono_null (compl_subset_compl.2 (hball i))
          (K3.foldedCircle_compl_eq_zero (hctrH i) hr.le))
    obtain ⟨hA, hB⟩ := BdryExist.ae_avgReg_spec hXf n
    filter_upwards [hrep', hA, hB (x : ℂ) hxH] with ω hω hAω hBω
    show Tendsto (fun i => Y ω (foldedCircle (ctr (i + 1)) r)) atTop
      (𝓝 (Y ω (foldedCircle (ctr 0) r)))
    simp only [hω, measure_univ, ENNReal.toReal_one, one_mul]
    have hMV : ∀ i, ∫ z, g ω z ∂(foldedCircle (ctr i) r) = g ω (ctr i) := fun i =>
      integral_foldedCircle_of_harm_center ((hgh ω).mono ball_subset_closedBall) (hctrH i) hr
        (by rw [← dist_eq_norm]; linarith [hctrd i])
    simp only [hMV]
    simp only [hctrS, hctr0]
    refine Tendsto.add (Tendsto.sub ?_ tendsto_const_nhds) ?_
    · have h1 := (tendsto_add_atTop_iff_nat j0).2 (hAω (x : ℂ) hxH)
      rw [hBω] at h1
      exact h1
    · have hcont := K3.continuousOn_of_harmonic_foldH (hgh ω)
      have hxK : (x : ℂ) ∈ closedBall (x : ℂ) r' ∩ Hbar :=
        ⟨mem_closedBall_self (by linarith), hxH⟩
      refine (hcont (x : ℂ) hxK).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hdjlim, ?_⟩)
      refine Eventually.of_forall fun i => ?_
      have := hball (i + 1) ⟨mem_closedBall_self hr.le, hctrH (i + 1)⟩
      rw [hctrS] at this
      exact ⟨this, by rw [← hctrS]; exact hctrH (i + 1)⟩
  have hXae := ae_family_of_isMixedGFF hX hY hm hT hYae
  -- the `h0` part
  have hKV : closedBall (x : ℂ) r' ∩ Hbar ⊆ D ∪ realSet (Ioo a b) := fun u hu =>
    mem_union_of_dist_lt_palmGap hu.2 (lt_of_le_of_lt hu.1 hr'G)
  obtain ⟨mc, hmc, hmcEq⟩ := exists_continuous_eqOn (isClosed_closedBall.inter isClosed_Hbar)
    (hh0.mono hKV)
  have hEqInt : ∀ i, ∫ u, h0 u ∂foldedCircle (ctr i) r = ∫ u, mc u ∂foldedCircle (ctr i) r :=
    fun i => integral_congr_ae ((ae_fc_mem_ball_inter (hctrH i) hr).mono fun u hu =>
      (hmcEq ⟨hball i hu, hu.2⟩).symm)
  have hh0lim : Tendsto (fun i => ∫ u, h0 u ∂foldedCircle (ctr (i + 1)) r) atTop
      (𝓝 (∫ u, h0 u ∂foldedCircle (ctr 0) r)) := by
    simp only [hEqInt]
    have h1 := (TwoPoint.continuous_integral_foldedCircle hmc).tendsto ((ctr 0), r)
    have h2 : Tendsto (fun i : ℕ => (ctr (i + 1), r)) atTop (𝓝 (ctr 0, r)) := by
      simp only [hctrS, hctr0]
      exact hdjlim.prodMk_nhds tendsto_const_nhds
    simpa only [Function.comp_def] using h1.comp h2
  filter_upwards [hXae] with ω hω
  have htail : Tendsto (fun i => (ofFun h0 + X ω) (foldedCircle (ctr (i + 1)) r)) atTop
      (𝓝 ((ofFun h0 + X ω) (foldedCircle (ctr 0) r))) := hh0lim.add hω
  simp only [hctrS, hctr0, hdj] at htail
  have htot : Tendsto (fun j => (ofFun h0 + X ω) (foldedCircle (dyadicRoundC j (x : ℂ)) r))
      atTop (𝓝 ((ofFun h0 + X ω) (foldedCircle (x : ℂ) r))) :=
    (tendsto_add_atTop_iff_nat j0).1 htail
  exact htot.limUnder_eq

end Prop16Asm

end QuantumZipper
