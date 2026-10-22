import HigherDimLQGMetric.LGF.BoxField

/-!
# Deterministic identities for the antiderivative field (packet F2, target 1, part 6)

With `D = ∂₁⋯∂_d` (`boxDeriv d`), `θ = ψ_{0,0}` and the box densities
`boxDens q = 1_{[0,q]} − (∏ qᵢ) θ`:

* `integral_boxDeriv_mul_prod`: `∫ Dφ(x) ∏ᵢ xᵢ dx = (−1)^d ∫ φ` (FTC + Fubini);
* `integral_boxDeriv_mul_boxDens`: `∫ Dφ(x) boxDens x u dx = (−1)^d (φ(u) − (∫ φ) θ(u))`;
* `integral_boxDeriv_mul_logCovF` (the deterministic half of the stochastic Fubini step):
  `∫ Dφ(x) logCovF (boxDens x) f dx = (−1)^d logCovF (φ − (∫ φ) θ) f` for bounded boundedly
  supported `f` (Fubini on `ℝ^d × ℝ^d × ℝ^d`);
* `exists_norm_gramVec_boxDens_sq_le`: `‖gramVec (boxDens x)‖²` is bounded on balls.

Port of LQGMetric's `Field/ExistKerId.lean`, `ExistSFub.lean` (deterministic halves) with the log
kernel in place of the heat-kernel vectors (the identities are proved at the level of `logCovF`, so
no `L²(ℝ × ℝ^d)`-valued integrals are needed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem abs_apply_le_norm (x : Rd d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  rw [← Real.norm_eq_abs]
  exact PiLp.norm_apply_le x i

theorem measurable_boxIndF_rd₂ :
    Measurable fun p : Rd d × Rd d => boxIndF p.1.ofLp p.2.ofLp := by
  have h : Measurable fun p : Rd d × Rd d => (p.1.ofLp, p.2.ofLp) :=
    ((PiLp.continuous_ofLp 2 _).measurable.comp measurable_fst).prodMk
      ((PiLp.continuous_ofLp 2 _).measurable.comp measurable_snd)
  have h2 := (measurable_boxIndF₂ (n := d)).comp h
  exact h2

theorem continuous_prod_coord : Continuous fun x : Rd d => ∏ i, x i :=
  continuous_finsetProd _ fun i _ => (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)

theorem measurable_boxDens₂ : Measurable fun p : Rd d × Rd d => boxDens p.1.ofLp p.2 := by
  have h1 : Measurable fun p : Rd d × Rd d => ∏ i, p.1 i :=
    continuous_prod_coord.measurable.comp measurable_fst
  have h2 : Measurable fun p : Rd d × Rd d => theta d p.2 :=
    (theta d).continuous.measurable.comp measurable_snd
  have h3 := (measurable_boxIndF_rd₂ (d := d)).sub (h1.mul h2)
  exact h3

/-- `|Dφ(x) 1_{[0,x]}(u)| ≤ |Dφ(x)| 1_{B̄(0, dR+1)}(u)` when `Dφ` vanishes outside `B̄(0, R)`. -/
theorem abs_mul_boxIndF_le {g : Rd d → ℝ} {R : ℝ} (hR : 0 ≤ R) (hg : ∀ x, R < ‖x‖ → g x = 0)
    (x u : Rd d) :
    |g x * boxIndF x.ofLp u.ofLp| ≤ |g x| * (closedBall (0 : Rd d) (d * R + 1)).indicator 1 u := by
  by_cases hx : R < ‖x‖
  · rw [hg x hx]; simp
  · have hx' : ∀ i, |x.ofLp i| ≤ R := fun i => (abs_apply_le_norm x i).trans (not_lt.1 hx)
    have hb := isBddSupp_boxIndF hR hx'
    rw [abs_mul]
    by_cases hu : u ∈ closedBall (0 : Rd d) (d * R + 1)
    · rw [indicator_of_mem hu, Pi.one_apply, mul_one]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_boxIndF_le_one _ _)
    · rw [indicator_of_notMem hu, hb.eq_zero_of_notMem hu]
      simp

theorem integrable_indicator_closedBall (R : ℝ) :
    Integrable ((closedBall (0 : Rd d) R).indicator (1 : Rd d → ℝ)) :=
  (integrable_indicator_iff measurableSet_closedBall).2
    (integrableOn_const measure_closedBall_lt_top.ne)

/-- `∫ Dφ(x) ∏ᵢ xᵢ dx = (−1)^d ∫ φ`. -/
theorem integral_boxDeriv_mul_prod (φ : TestRd d) :
    ∫ x, boxDeriv d φ x * ∏ i, x i = (-1) ^ d * ∫ x, φ x := by
  obtain ⟨M, R₀, hD⟩ := exists_isBddSupp_testOn (boxDeriv d φ)
  set R := max R₀ 0 with hRdef
  have hR : 0 ≤ R := le_max_right _ _
  have hDz : ∀ x, R < ‖x‖ → boxDeriv d φ x = 0 :=
    fun x hx => hD.eq_zero x ((le_max_left _ _).trans_lt hx)
  set F : Rd d × Rd d → ℝ := fun p => boxDeriv d φ p.1 * boxIndF p.1.ofLp p.2.ofLp with hF
  have hFm : Measurable F :=
    ((boxDeriv d φ).continuous.measurable.comp measurable_fst).mul measurable_boxIndF_rd₂
  have hFi : Integrable F (volume.prod volume) := by
    refine Integrable.mono' ((integrable_testOn (boxDeriv d φ)).abs.mul_prod
      (integrable_indicator_closedBall (d := d) (d * R + 1))) hFm.aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs]
    exact abs_mul_boxIndF_le hR hDz p.1 p.2
  have e1 : ∀ x : Rd d, boxDeriv d φ x * ∏ i, x i = ∫ u, F (x, u) := fun x => by
    simp only [hF]
    rw [integral_const_mul, ← integral_boxIndF_rd]
  simp_rw [e1]
  rw [integral_integral_swap (f := fun x u => F (x, u)) hFi]
  simp only [hF]
  simp_rw [integral_boxDeriv_mul_boxIndF]
  rw [integral_const_mul]

/-- `∫ Dφ(x) boxDens x u dx = (−1)^d (φ(u) − (∫ φ) θ(u))`. -/
theorem integral_boxDeriv_mul_boxDens (φ : TestRd d) (u : Rd d) :
    ∫ x, boxDeriv d φ x * boxDens x.ofLp u = (-1) ^ d * (φ u - (∫ y, φ y) * theta d u) := by
  obtain ⟨M, R₀, hD⟩ := exists_isBddSupp_testOn (boxDeriv d φ)
  set R := max R₀ 0 with hRdef
  have hR : 0 ≤ R := le_max_right _ _
  have hDz : ∀ x, R < ‖x‖ → boxDeriv d φ x = 0 :=
    fun x hx => hD.eq_zero x ((le_max_left _ _).trans_lt hx)
  have hi1 : Integrable fun x : Rd d => boxDeriv d φ x * boxIndF x.ofLp u.ofLp := by
    refine Integrable.mono' ((integrable_testOn (boxDeriv d φ)).abs) ?_ (ae_of_all _ fun x => ?_)
    · have hm0 : Measurable fun x : Rd d => (x, u) := measurable_id.prodMk measurable_const
      have hm1 := (measurable_boxIndF_rd₂ (d := d)).comp hm0
      have hm : Measurable fun x : Rd d => boxIndF x.ofLp u.ofLp := hm1
      exact ((boxDeriv d φ).continuous.measurable.mul hm).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_boxIndF_le_one _ _)
  have hi2 : Integrable fun x : Rd d => boxDeriv d φ x * ∏ i, x i :=
    ((boxDeriv d φ).continuous.mul continuous_prod_coord).integrable_of_hasCompactSupport
      (boxDeriv d φ).hasCompactSupport.mul_right
  have e : ∀ x : Rd d, boxDeriv d φ x * boxDens x.ofLp u =
      boxDeriv d φ x * boxIndF x.ofLp u.ofLp - theta d u * (boxDeriv d φ x * ∏ i, x i) := by
    intro x
    simp only [boxDens]
    ring_nf
  simp_rw [e]
  rw [integral_sub hi1 (hi2.const_mul _), integral_const_mul, integral_boxDeriv_mul_boxIndF,
    integral_boxDeriv_mul_prod]
  ring

theorem isBddSupp_indicator_closedBall (D : ℝ) :
    IsBddSupp ((closedBall (0 : Rd d) D).indicator (1 : Rd d → ℝ)) 1 D := by
  refine ⟨measurable_one.indicator measurableSet_closedBall, fun z => ?_, fun z hz => ?_⟩
  · by_cases hz : z ∈ closedBall (0 : Rd d) D
    · rw [indicator_of_mem hz]; simp
    · rw [indicator_of_notMem hz]; simp
  · refine indicator_of_notMem ?_ _
    rw [mem_closedBall, dist_zero_right, not_le]
    exact hz

/-- **The deterministic half of the stochastic Fubini step** (`d ≥ 1`): for bounded boundedly
supported `f`, `∫ Dφ(x) logCovF (boxDens x) f dx = (−1)^d logCovF (φ − (∫ φ) θ) f`. -/
theorem integral_boxDeriv_mul_logCovF [NeZero d] (φ : TestRd d) {f : Rd d → ℝ} {M D : ℝ}
    (hf : IsBddSupp f M D) :
    ∫ x, boxDeriv d φ x * logCovF (boxDens x.ofLp) f =
      (-1) ^ d * logCovF (fun u => φ u - (∫ y, φ y) * theta d u) f := by
  obtain ⟨M₁, R₀, hD⟩ := exists_isBddSupp_testOn (boxDeriv d φ)
  set R := max R₀ 0 with hRdef
  have hR : 0 ≤ R := le_max_right _ _
  have hDz : ∀ x, R < ‖x‖ → boxDeriv d φ x = 0 :=
    fun x hx => hD.eq_zero x ((le_max_left _ _).trans_lt hx)
  obtain ⟨Mb, hMb⟩ := exists_isBddSupp_boxDens (d := d) hR
  set Db : ℝ := d * R + 1 with hDb
  have hMb0 : 0 ≤ Mb := (hMb 0 fun i => by simpa using hR).nonneg
  set b : Rd d → ℝ := fun u => Mb * (closedBall (0 : Rd d) Db).indicator 1 u with hb
  have hbS : IsBddSupp b (|Mb| * 1) Db := (isBddSupp_indicator_closedBall Db).const_mul Mb
  have hb0 : ∀ u, 0 ≤ b u := fun u => by
    simp only [hb]
    by_cases hu : u ∈ closedBall (0 : Rd d) Db
    · rw [indicator_of_mem hu]; simpa using hMb0
    · rw [indicator_of_notMem hu, mul_zero]
  have hbox : ∀ x : Rd d, ‖x‖ ≤ R → ∀ u, |boxDens x.ofLp u| ≤ b u := by
    intro x hx u
    have hq : ∀ i, |x.ofLp i| ≤ R := fun i => (abs_apply_le_norm x i).trans hx
    have h1 := hMb x.ofLp hq
    by_cases hu : u ∈ closedBall (0 : Rd d) Db
    · simp only [hb, indicator_of_mem hu, Pi.one_apply, mul_one]
      exact h1.abs_le u
    · rw [h1.eq_zero_of_notMem hu, abs_zero]
      exact hb0 u
  set Φ : Rd d × (Rd d × Rd d) → ℝ := fun z => boxDeriv d φ z.1 *
    (boxDens z.1.ofLp z.2.1 * f z.2.2 * (-Real.log ‖z.2.1 - z.2.2‖)) with hΦ
  have hΦm : Measurable Φ := by
    refine ((boxDeriv d φ).continuous.measurable.comp measurable_fst).mul ?_
    have hb0 : Measurable fun z : Rd d × (Rd d × Rd d) => (z.1, z.2.1) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have hb1 := (measurable_boxDens₂ (d := d)).comp hb0
    have hb2 : Measurable fun z : Rd d × (Rd d × Rd d) => boxDens z.1.ofLp z.2.1 := hb1
    refine (hb2.mul
      (hf.measurable.comp (measurable_snd.comp measurable_snd))).mul ?_
    exact ((measurable_fst.comp measurable_snd).sub
      (measurable_snd.comp measurable_snd)).norm.log.neg
  have hΦi : Integrable Φ (volume.prod volume) := by
    refine Integrable.mono' ((integrable_testOn (boxDeriv d φ)).abs.mul_prod
      (integrable_logKer hbS hf).abs) hΦm.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs]
    simp only [hΦ]
    by_cases hx : R < ‖z.1‖
    · rw [hDz z.1 hx]; simp
    · have h1 : |boxDens z.1.ofLp z.2.1| ≤ |b z.2.1| :=
        (hbox z.1 (not_lt.1 hx) z.2.1).trans (le_abs_self _)
      have e1 : |boxDeriv d φ z.1 * (boxDens z.1.ofLp z.2.1 * f z.2.2 *
          -Real.log ‖z.2.1 - z.2.2‖)| = |boxDeriv d φ z.1| * (|boxDens z.1.ofLp z.2.1| *
          |f z.2.2 * -Real.log ‖z.2.1 - z.2.2‖|) := by
        rw [abs_mul, mul_assoc (boxDens _ _), abs_mul]
      have e2 : |b z.2.1 * f z.2.2 * -Real.log ‖z.2.1 - z.2.2‖| =
          |b z.2.1| * |f z.2.2 * -Real.log ‖z.2.1 - z.2.2‖| := by
        rw [mul_assoc, abs_mul]
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
        (abs_nonneg _)
  have e1 : ∀ x : Rd d, boxDeriv d φ x * logCovF (boxDens x.ofLp) f =
      ∫ p : Rd d × Rd d, Φ (x, p) := fun x => by
    simp only [hΦ, logCovF]
    rw [integral_const_mul]
  simp_rw [e1]
  rw [integral_integral_swap (f := fun x p => Φ (x, p)) hΦi]
  have e2 : ∀ p : Rd d × Rd d, ∫ x, Φ (x, p) =
      (-1) ^ d * ((φ p.1 - (∫ y, φ y) * theta d p.1) * f p.2 * (-Real.log ‖p.1 - p.2‖)) := by
    intro p
    have e : (fun x => Φ (x, p)) = fun x => (boxDeriv d φ x * boxDens x.ofLp p.1) *
        (f p.2 * (-Real.log ‖p.1 - p.2‖)) := by
      funext x
      simp only [hΦ]
      ring
    rw [e, integral_mul_const, integral_boxDeriv_mul_boxDens]
    ring
  simp_rw [e2]
  rw [integral_const_mul]
  rfl

/-- The white-noise vectors of the box densities are bounded on balls (`d ≥ 1`). -/
theorem exists_norm_gramVec_boxDens_sq_le [NeZero d] (R : ℝ) :
    ∃ C : ℝ, ∀ x : Rd d, ‖x‖ ≤ R → ‖gramVec (boxDens x.ofLp)‖ ^ 2 ≤ C := by
  set R' := max R 0 with hR'
  obtain ⟨M, hM⟩ := exists_isBddSupp_boxDens (d := d) (le_max_right R 0)
  set D : ℝ := d * R' + 1 with hD
  set N₁ : ℝ := M * (volume (closedBall (0 : Rd d) D)).toReal with hN₁
  set L : ℝ := max 0 (Real.log (2 * D)) with hL
  refine ⟨N₁ * (M * volBall d + N₁ * (1 + L)), fun x hx => ?_⟩
  have hq : ∀ i, |x.ofLp i| ≤ R' :=
    fun i => (abs_apply_le_norm x i).trans (hx.trans (le_max_left _ _))
  have hf := hM _ hq
  have hM0 := hf.nonneg
  have hL0 : 0 ≤ L := le_max_left _ _
  have hV0 := volBall_nonneg (d := d)
  have hN0 : 0 ≤ ∫ z, |boxDens x.ofLp z| := integral_nonneg fun z => abs_nonneg _
  have hN : ∫ z, |boxDens x.ofLp z| ≤ N₁ := hf.integral_abs_le
  rw [← real_inner_self_eq_norm_sq, inner_gramVec hf (integral_boxDens _) hf (integral_boxDens _)]
  calc logCovF (boxDens x.ofLp) (boxDens x.ofLp)
      ≤ |logCovF (boxDens x.ofLp) (boxDens x.ofLp)| := le_abs_self _
    _ ≤ (∫ z, |boxDens x.ofLp z|) * (M * volBall d + (∫ z, |boxDens x.ofLp z|) * (1 + L)) :=
        abs_logCovF_self_le hf
    _ ≤ N₁ * (M * volBall d + N₁ * (1 + L)) := by
        have hN₁0 : 0 ≤ N₁ := hN0.trans hN
        gcongr

end HigherDimLQGMetric
