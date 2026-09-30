import QuantumZipper.Proofs.Zipper.LocHitScaleLen
import QuantumZipper.Proofs.Thm18.G3FidProxy

/-!
# LOC-HITSCALE (3): the local scale of the unzipped field

Theorem 1.3, node E6 under D25. Continuation of `LocHitScaleLen.lean`. The scale `scaleParam γ y`
(the radius at which `B_a(0) ∩ ℍ` first has unit quantum area) of the unzipped field at time
`t` is read from the rich local data along the rationals of `(0, N]` (junk `N`), with the
measurable area reader `Thm18Asm.areaProxy` (sup over the bumps `openBump (B_q(0) ∩ ℍ) n` of the
`liminf` of the approximate integrals), applied to the unzipped *localized* field
`yLoc … t d = ufJ ((pathX κ T d.2, locField R' d.1), t)`:

* `areaProxy_congr_on`: `areaProxy γ y q` only sees the regularized averages on `B_q(0)`;
* `aLoc`: the scale read at the local hitting time `tauLoc`; measurable (`measurable_aLoc`);
* `aLocAt_eq_scale`: at the local data `locRich R' (x, W)`, at a time `t ∈ (0, T]` at which the
  unzipped field has an area limit on `ℍ`, the reader returns the true scale as soon as either
  the scale lies in `(0, N]` or the reader is below the junk value `N` (`N ≤ M`, `|W| ≤ M` on
  `[0,T]`, `9M + 9√T + 7 ≤ R'`).

Own elementary bookkeeping (the paper, Sheffield arXiv:1012.4797 §5.4, pp. 70–72, asserts the
locality without proof).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper.E6

open D3Plus MeasUnzip CharFun

theorem measurableSet_H_loc : MeasurableSet H :=
  (isOpen_lt continuous_const Complex.continuous_im).measurableSet

/-- `areaFun γ f` only sees the regularized averages on a set outside of which `f` vanishes. -/
theorem areaFun_congr_on {γ : ℝ} {y y' : FieldSample} {U : Set ℂ} (hU : MeasurableSet U)
    {f : ℂ → ℝ} (hf : ∀ z, z ∉ U → f z = 0)
    (h : ∀ k, ∀ z ∈ U, avgReg y k z = avgReg y' k z) :
    LQGMeas.areaFun γ f y = LQGMeas.areaFun γ f y' := by
  unfold LQGMeas.areaFun
  congr 1
  funext k
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := areaApprox γ y k) hf,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := areaApprox γ y' k) hf]
  congr 1
  unfold areaApprox
  rw [restrict_withDensity hU, restrict_withDensity hU]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem hU] with z hz
  rw [h k z hz]

/-- `areaProxy γ y a` only sees the regularized averages on `B_a(0)`. -/
theorem areaProxy_congr_on {γ : ℝ} {y y' : FieldSample} {a : ℝ}
    (h : ∀ k, ∀ z ∈ ball (0 : ℂ) a, avgReg y k z = avgReg y' k z) :
    Thm18Asm.areaProxy γ y a = Thm18Asm.areaProxy γ y' a := by
  unfold Thm18Asm.areaProxy
  congr 1
  funext n
  congr 1
  refine areaFun_congr_on (U := ball (0 : ℂ) a ∩ H) (measurableSet_ball.inter measurableSet_H_loc)
    (fun z hz => image_eq_zero_of_notMem_tsupport fun h' =>
      hz (LQGMeas.tsupport_openBump_subset _ n h')) fun k z hz => h k z hz.1

theorem areaProxy_congr_avg {γ : ℝ} {y y' : FieldSample} (h : avgReg y = avgReg y') (a : ℝ) :
    Thm18Asm.areaProxy γ y a = Thm18Asm.areaProxy γ y' a := by
  unfold Thm18Asm.areaProxy LQGMeas.areaFun
  rw [Factorization.areaApprox_congr h]

/-! ## The local scale -/

/-- The unzipped localized field at time `t`. -/
def yLoc (γ κ : ℝ) (T R' : ℕ) (t : ℝ) (d : FullData) : FieldSample :=
  ufJ (natCast_nonneg' T) γ κ ((pathX κ T d.2, locField R' d.1), t)

/-- The scale of the unzipped localized field at time `t`, along the rationals of `(0, N]`. -/
def aLocAt (γ κ : ℝ) (T R' N : ℕ) (t : ℝ) (d : FullData) : ℝ :=
  ratInf N fun q => 1 ≤ Thm18Asm.areaProxy γ (yLoc γ κ T R' t d) q

/-- The local scale at the local hitting time. -/
def aLoc (γ κ ℓ : ℝ) (T R' N : ℕ) (d : FullData) : ℝ :=
  aLocAt γ κ T R' N (tauLoc γ κ ℓ T R' d) d

theorem measurable_yLoc_tau (γ κ ℓ : ℝ) (T R' : ℕ) :
    Measurable fun d : FullData => yLoc γ κ T R' (tauLoc γ κ ℓ T R' d) d := by
  have h1 : Measurable fun d : FullData =>
      ((pathX κ T d.2, locField R' d.1), tauLoc γ κ ℓ T R' d) :=
    ((measurable_pathX_snd κ T).prodMk ((measurable_locField R').comp measurable_fst)).prodMk
      (measurable_tauLoc γ κ ℓ T R')
  have h2 := (measurable_ufJ (natCast_nonneg' T) γ κ).comp h1
  have e : (fun d : FullData => yLoc γ κ T R' (tauLoc γ κ ℓ T R' d) d) =
      ufJ (natCast_nonneg' T) γ κ ∘ fun d : FullData =>
        ((pathX κ T d.2, locField R' d.1), tauLoc γ κ ℓ T R' d) := by
    funext d; rfl
  rw [e]
  exact h2

theorem measurable_aLoc (γ κ ℓ : ℝ) (T R' N : ℕ) : Measurable (aLoc γ κ ℓ T R' N) := by
  have hy := measurable_yLoc_tau γ κ ℓ T R'
  have e : aLoc γ κ ℓ T R' N = fun d => ratInf N fun q =>
      1 ≤ Thm18Asm.areaProxy γ (yLoc γ κ T R' (tauLoc γ κ ℓ T R' d) d) q := by
    funext d; rfl
  rw [e]
  exact measurable_ratInf N fun q =>
    measurableSet_le measurable_const ((Thm18Asm.measurable_areaProxy γ q).comp hy)

/-- **The local area reader is the true area** of `B_q(0) ∩ ℍ` for rational `q ∈ (0, N]`. -/
theorem areaProxy_yLoc_locRich {γ κ : ℝ} (hκ : 0 < κ) {T R' N : ℕ} (hTR : T ≤ R') {M : ℝ}
    (hNM : (N : ℝ) ≤ M) (x : FieldSample) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hM : ∀ r ∈ Icc (0 : ℝ) T, |W r| ≤ M) (hR' : 9 * M + 9 * Real.sqrt T + 7 ≤ R')
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (ht0 : 0 < t)
    {μ : Measure ℂ} (hA : IsVagueLimitOn H (areaApprox γ (unzippedField γ (x, W) t)) μ)
    {q : ℝ} (hqN : q ≤ N) :
    Thm18Asm.areaProxy γ (yLoc γ κ T R' t (locRich R' (x, W))) q =
      qAreaMeasure γ (unzippedField γ (x, W) t) (ball 0 q ∩ H) := by
  have hT := natCast_nonneg' T
  set f := pathX κ T (locRich R' (x, W)).2 with hfdef
  have hWf : ∀ r ∈ Icc (0 : ℝ) T, Wof κ T hT f r = W r := Wof_pathX_locRich hκ hTR x hW
  set W₁ := Wof κ T hT f with hW₁def
  have hW₁c : Continuous W₁ := continuous_Wof κ T hT f
  have hW₁0 : W₁ 0 = 0 := by rw [hWf 0 ⟨le_rfl, hT⟩, hW0]
  have hfPZ : f ∈ PZ hT κ := hW₁0
  have hWt : ∀ r ∈ Icc (0 : ℝ) t, W r = W₁ r := fun r hr =>
    (hWf r ⟨hr.1, hr.2.trans ht.2⟩).symm
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  have hsq : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt ht.2
  have hflow : ∀ u ∈ H, ‖u‖ ≤ M + 3 → ‖fwdMapInv W₁ t u‖ + 3 ≤ R' := by
    intro u hu hub
    have h1 := B5.norm_fwdMapInv_sub_le hW₁c hW₁0 ht0
      (fun r hr => by rw [← hWt r hr]; exact hM r ⟨hr.1, hr.2.trans ht.2⟩) hu
    have h2 := norm_sub_norm_le (fwdMapInv W₁ t u) u
    have h3 := Real.sqrt_nonneg (T : ℝ)
    linarith
  have havg : avgReg (ufJ hT γ κ ((f, x), t)) = avgReg (unzippedField γ (x, W) t) := by
    rw [avgReg_ufJ hT γ κ hfPZ ht x]
    exact funext fun k => funext fun z => B5.avgReg_coordChange_eqOn x
      (ESM.fwdMapInv_eqOn_of_drive_eqOn hW₁c hW hW₁0 hW0 ht.1 fun r hr => (hWt r hr).symm)
      (Qc γ) k z
  have e1 : Thm18Asm.areaProxy γ (yLoc γ κ T R' t (locRich R' (x, W))) q =
      Thm18Asm.areaProxy γ (ufJ hT γ κ ((f, x), t)) q := by
    refine areaProxy_congr_on fun k z hz => ?_
    refine avgReg_ufJ_locField hT hfPZ ht x hflow k ?_
    have := mem_ball_zero_iff.1 hz
    linarith
  rw [e1, areaProxy_congr_avg havg, Thm18Asm.areaProxy_eq_qAreaMeasure hA]

/-- **The local scale is the true scale** (at the local data of `(x, W)`, a time `t ∈ (0, T]`
with an area limit), if the true scale lies in `(0, N]` or the reader is below `N`. -/
theorem aLocAt_eq_scale {γ κ : ℝ} (hκ : 0 < κ) {T R' N : ℕ} (hTR : T ≤ R') {M : ℝ}
    (hNM : (N : ℝ) ≤ M) (x : FieldSample) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hM : ∀ r ∈ Icc (0 : ℝ) T, |W r| ≤ M) (hR' : 9 * M + 9 * Real.sqrt T + 7 ≤ R')
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (ht0 : 0 < t)
    (hA : ∃ μ, IsVagueLimitOn H (areaApprox γ (unzippedField γ (x, W) t)) μ)
    (hcase : (0 < scaleParam γ (unzippedField γ (x, W) t) ∧
        scaleParam γ (unzippedField γ (x, W) t) ≤ N) ∨
      aLocAt γ κ T R' N t (locRich R' (x, W)) < N) :
    aLocAt γ κ T R' N t (locRich R' (x, W)) = scaleParam γ (unzippedField γ (x, W) t) := by
  obtain ⟨μ, hμ⟩ := hA
  set E : Set ℝ := {a : ℝ | 0 < a ∧ 1 ≤ qAreaMeasure γ (unzippedField γ (x, W) t) (ball 0 a ∩ H)}
    with hEdef
  have hsc : scaleParam γ (unzippedField γ (x, W) t) = sInf E := rfl
  have hP : ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) ≤ N →
      ((1 ≤ Thm18Asm.areaProxy γ (yLoc γ κ T R' t (locRich R' (x, W))) q) ↔ (q : ℝ) ∈ E) := by
    intro q hq0 hqN
    rw [areaProxy_yLoc_locRich hκ hTR hNM x hW hW0 hM hR' ht ht0 hμ hqN]
    exact ⟨fun h => ⟨hq0, h⟩, fun h => h.2⟩
  have h0 : ∀ s ∈ E, 0 ≤ s := fun s hs => hs.1.le
  have hup : ∀ s ∈ E, ∀ q : ℝ, s < q → q ≤ N → q ∈ E := fun s hs q hsq _ =>
    ⟨hs.1.trans hsq, hs.2.trans (measure_mono (inter_subset_inter_left _
      (ball_subset_ball hsq.le)))⟩
  have hb : BddBelow E := ⟨0, h0⟩
  rw [hsc]
  rcases hcase with ⟨hpos, hle⟩ | hlt
  · have hne : E.Nonempty := by
      by_contra hc
      rw [not_nonempty_iff_eq_empty] at hc
      rw [hsc, hc, Real.sInf_empty] at hpos
      exact lt_irrefl _ hpos
    exact iInf_rat_eq hP h0 hup hne (hsc ▸ hle)
  · obtain ⟨q, hq0, hqN, hPq⟩ := exists_of_ratInf_lt hlt
    have hqE := (hP q hq0 hqN.le).1 hPq
    exact iInf_rat_eq hP h0 hup ⟨q, hqE⟩ ((csInf_le hb hqE).trans hqN.le)

end QuantumZipper.E6
