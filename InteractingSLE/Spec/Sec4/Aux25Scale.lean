/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Ito.Observable

/-!
# Aux. lemma 25: the scale function of the ratio of a force gap to a passive gap

Packet PROVE-AUX25. The endpoint step of Aux. lemma 25 (Specification p. 127: "the first endpoint is strictly
beyond the marked point if a finite swallow occurs") is proved through one martingale. For a single force
group of total weight `ρ` at gap `û = V − W` and a real point to its right at gap `X = Y − W` (`X > û > 0`),
driven by `dW = √κ dB + ρ/(W − V) dt`, the ratio `u = û/X ∈ (0, 1)` has, after the time change `dt/X²`, the
generator `(κ/2)(1 − u)² ∂² + N(u) ∂` with `N(u) = (2 + ρ)/u − ρ − κ + (κ − 2)u`, whose scale density is

  `g(u) = u^{−α} (1 − u)^{β}`,  `α = 2(2 + ρ)/κ`,  `β = 2(4 + ρ − κ)/κ`.

It is integrable at `u = 1` exactly when `ρ > κ/2 − 4`. With `F(u) = ∫_{1/2}^u g`, the observable
`Φ = F(û/X)` of the state `(A, V, V^L, Y)` and the Brownian coordinate `b` (`W = A + √κ b`) has zero Itô
drift along the one-force dynamics (`itoGen_scaleObs_eq_zero`). The computation is by hand above: with
`u_b = −√κ(1 − u)/X`, `∂²_b Φ = −(κ/X²)(1 − u)(2g − (1 − u)g')`, and `g'/g = −α/u − β/(1 − u)`.

## Main results

* `scaleDens`, `scaleFn`, `scaleTop` (`= ∫_{1/2}^1 g`, finite for `β > −1`);
* `contDiffOn_scaleFn`, `tendsto_scaleTop_sub_scaleFn` (`∫_c^1 g → 0` as `c → 1`);
* `scaleObs`, `scaleRegion`, `itoGen_scaleObs_eq_zero`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Aux25

/-! ### The scale density and the scale function -/

section Scalar

variable {α β : ℝ}

/-- The scale density `g(u) = u^{−α} (1 − u)^{β}`. -/
def scaleDens (α β u : ℝ) : ℝ := u ^ (-α) * (1 - u) ^ β

/-- The scale function `F(u) = ∫_{1/2}^u g`. -/
def scaleFn (α β u : ℝ) : ℝ := ∫ v in (1 / 2 : ℝ)..u, scaleDens α β v

/-- The value `∫_{1/2}^1 g` (finite for `β > −1`). -/
def scaleTop (α β : ℝ) : ℝ := ∫ v in (1 / 2 : ℝ)..1, scaleDens α β v

theorem scaleDens_pos {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : 0 < scaleDens α β u :=
  mul_pos (Real.rpow_pos_of_pos hu.1 _) (Real.rpow_pos_of_pos (by linarith [hu.2]) _)

theorem scaleDens_nonneg {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : 0 ≤ scaleDens α β u :=
  mul_nonneg (Real.rpow_nonneg hu.1 _) (Real.rpow_nonneg (by linarith [hu.2]) _)

theorem continuousAt_scaleDens {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : ContinuousAt (scaleDens α β) u :=
  (Real.continuousAt_rpow_const _ _ (Or.inl hu.1.ne')).mul
    ((Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hu.2]))).comp
      (continuous_const.sub continuous_id).continuousAt)

theorem continuousOn_scaleDens : ContinuousOn (scaleDens α β) (Ioo 0 1) :=
  fun _ hu => (continuousAt_scaleDens hu).continuousWithinAt

/-- `g' = g · (−α/u − β/(1 − u))` on `(0, 1)`. -/
theorem hasDerivAt_scaleDens {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (scaleDens α β) (scaleDens α β u * (-α / u - β / (1 - u))) u := by
  have h1u : 0 < 1 - u := by linarith [hu.2]
  have h1 : HasDerivAt (fun v : ℝ => v ^ (-α)) (-α * u ^ (-α - 1)) u :=
    Real.hasDerivAt_rpow_const (Or.inl hu.1.ne')
  have h2 : HasDerivAt (fun v : ℝ => (1 - v) ^ β) (β * (1 - u) ^ (β - 1) * (-1)) u := by
    have h := (Real.hasDerivAt_rpow_const (x := 1 - u) (p := β) (Or.inl h1u.ne')).comp u
      ((hasDerivAt_id u).const_sub 1)
    simpa [Function.comp_def] using h
  refine (h1.mul h2).congr_deriv ?_
  rw [Real.rpow_sub_one hu.1.ne', Real.rpow_sub_one h1u.ne', scaleDens]
  field_simp
  ring

theorem contDiffOn_scaleDens : ContDiffOn ℝ 2 (scaleDens α β) (Ioo 0 1) := by
  refine ContDiffOn.mul ?_ ?_
  · exact contDiffOn_id.rpow_const_of_ne fun v hv => hv.1.ne'
  · exact (contDiffOn_const.sub contDiffOn_id).rpow_const_of_ne fun v hv => by
      have := hv.2; simp only [id]; linarith

theorem intervalIntegrable_scaleDens {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (scaleDens α β) volume a b :=
  (continuousOn_scaleDens.mono fun v hv => by
    rw [uIcc] at hv
    exact ⟨lt_of_lt_of_le (lt_min ha.1 hb.1) hv.1, lt_of_le_of_lt hv.2 (max_lt ha.2 hb.2)⟩
    ).intervalIntegrable

theorem hasDerivAt_scaleFn {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (scaleFn α β) (scaleDens α β u) u :=
  intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_scaleDens ⟨by norm_num, by norm_num⟩ hu)
    (continuousOn_scaleDens.stronglyMeasurableAtFilter isOpen_Ioo u hu) (continuousAt_scaleDens hu)

theorem contDiffOn_scaleFn : ContDiffOn ℝ 3 (scaleFn α β) (Ioo 0 1) := by
  rw [show (3 : WithTop ℕ∞) = 2 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun u hu => (hasDerivAt_scaleFn hu).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  exact contDiffOn_scaleDens.congr fun u hu => (hasDerivAt_scaleFn hu).deriv

/-- The density is integrable at `1` when `β > −1`. -/
theorem intervalIntegrable_scaleDens_one (hβ : -1 < β) :
    IntervalIntegrable (scaleDens α β) volume (1 / 2) 1 := by
  have h1 : IntervalIntegrable (fun v : ℝ => (1 - v) ^ β) volume (1 / 2) 1 := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 1 / 2) (b := 0) hβ).comp_sub_left 1
    convert this using 2 <;> norm_num
  have h2 : ContinuousOn (fun v : ℝ => v ^ (-α)) (uIcc (1 / 2) 1) := fun v hv => by
    rw [uIcc_of_le (by norm_num)] at hv
    exact (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hv.1]))).continuousWithinAt
  refine (h1.continuousOn_mul h2).congr fun v _ => ?_
  simp only [scaleDens]

theorem intervalIntegrable_scaleDens_of_le (hβ : -1 < β) {c : ℝ} (hc : c ∈ Icc (1 / 2 : ℝ) 1) :
    IntervalIntegrable (scaleDens α β) volume c 1 :=
  (intervalIntegrable_scaleDens_one hβ).mono_set (by
    rw [uIcc_of_le hc.2, uIcc_of_le (by norm_num)]; exact Icc_subset_Icc_left hc.1)

/-- `∫_{1/2}^1 g − F(c) = ∫_c^1 g`. -/
theorem scaleTop_sub_scaleFn (hβ : -1 < β) {c : ℝ} (hc : c ∈ Icc (1 / 2 : ℝ) 1) :
    scaleTop α β - scaleFn α β c = ∫ v in c..1, scaleDens α β v := by
  have h1 := intervalIntegrable_scaleDens_one (α := α) hβ
  have h2 : IntervalIntegrable (scaleDens α β) volume (1 / 2) c :=
    h1.mono_set (by
      rw [uIcc_of_le hc.1, uIcc_of_le (by norm_num)]; exact Icc_subset_Icc_right hc.2)
  rw [scaleTop, scaleFn, ← intervalIntegral.integral_interval_sub_left h1 h2]

theorem scaleFn_le_scaleTop (hβ : -1 < β) {c : ℝ} (hc : c ∈ Icc (1 / 2 : ℝ) 1) :
    scaleFn α β c ≤ scaleTop α β := by
  have h := scaleTop_sub_scaleFn (α := α) hβ hc
  have h0 : 0 ≤ ∫ v in c..1, scaleDens α β v :=
    intervalIntegral.integral_nonneg hc.2 fun v hv =>
      scaleDens_nonneg ⟨by linarith [hc.1, hv.1], hv.2⟩
  linarith

theorem scaleFn_half : scaleFn α β (1 / 2) = 0 := intervalIntegral.integral_same

theorem scaleFn_nonneg {c : ℝ} (hc : c ∈ Icc (1 / 2 : ℝ) 1) : 0 ≤ scaleFn α β c :=
  intervalIntegral.integral_nonneg hc.1 fun v hv => scaleDens_nonneg ⟨by linarith [hv.1], hv.2.trans hc.2⟩

theorem scaleFn_le_scaleFn {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hab : a ≤ b) :
    scaleFn α β a ≤ scaleFn α β b := by
  have h := intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_scaleDens (α := α) (β := β) (a := 1 / 2) ⟨by norm_num, by norm_num⟩ hb)
    (intervalIntegrable_scaleDens (α := α) (β := β) (a := 1 / 2) ⟨by norm_num, by norm_num⟩ ha)
  have h0 : 0 ≤ ∫ v in a..b, scaleDens α β v :=
    intervalIntegral.integral_nonneg hab fun v hv => scaleDens_nonneg
      ⟨ha.1.le.trans hv.1, hv.2.trans hb.2.le⟩
  simp only [scaleFn] at h ⊢
  linarith

theorem scaleTop_pos (hβ : -1 < β) : 0 < scaleTop α β :=
  intervalIntegral.intervalIntegral_pos_of_pos_on (intervalIntegrable_scaleDens_one hβ)
    (fun v hv => scaleDens_pos ⟨by linarith [hv.1], hv.2⟩) (by norm_num)

/-- `∫_c^1 g → 0` as `c → 1⁻`. -/
theorem tendsto_scaleTop_sub_scaleFn (hβ : -1 < β) :
    Tendsto (fun c => scaleTop α β - scaleFn α β c) (𝓝[<] 1) (𝓝 0) := by
  have hc := intervalIntegral.continuousOn_primitive_interval' (intervalIntegrable_scaleDens_one
    (α := α) hβ) (a := 1 / 2) (by rw [uIcc_of_le (by norm_num)]; exact ⟨le_rfl, by norm_num⟩)
  rw [uIcc_of_le (by norm_num)] at hc
  have h1 := (hc 1 ⟨by norm_num, le_rfl⟩).mono (Ioo_subset_Icc_self (a := (1 / 2 : ℝ)) (b := 1))
  rw [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] at h1
  have h2 : Tendsto (fun c => scaleTop α β - scaleFn α β c) (𝓝[<] 1)
      (𝓝 (scaleTop α β - scaleTop α β)) := tendsto_const_nhds.sub h1
  simpa only [sub_self] using h2

end Scalar

/-! ### The observable -/

section Obs

variable {nL nR : ℕ}

/-- The state `(A, V^R, V^L, Y)`: the drift integral `A = W − √κ B`, the right and left force points, and a
real point `Y` (all uncentred). -/
abbrev StateE (nL nR : ℕ) := ℝ × (Fin nR → ℝ) × (Fin nL → ℝ) × ℝ

/-- The driver `W = A + √κ b` of a state. -/
def stW (sk : ℝ) (p : StateE nL nR × ℝ) : ℝ := p.1.1 + sk * p.2

/-- The force gap `û = V_k − W`. -/
def gapU (sk : ℝ) (k : Fin nR) (p : StateE nL nR × ℝ) : ℝ := p.1.2.1 k - stW sk p

/-- The passive gap `X = Y − W`. -/
def gapX (sk : ℝ) (p : StateE nL nR × ℝ) : ℝ := p.1.2.2.2 - stW sk p

/-- The observable `Φ = F(û/X)`. -/
def scaleObs (α β sk : ℝ) (k : Fin nR) (p : StateE nL nR × ℝ) : ℝ :=
  scaleFn α β (gapU sk k p / gapX sk p)

/-- The region `0 < û < X`. -/
def scaleRegion (sk : ℝ) (k : Fin nR) : Set (StateE nL nR × ℝ) :=
  {p | 0 < gapU sk k p ∧ gapU sk k p < gapX sk p}

theorem continuous_stW (sk : ℝ) : Continuous (stW (nL := nL) (nR := nR) sk) := by
  unfold stW; fun_prop

theorem continuous_gapU (sk : ℝ) (k : Fin nR) : Continuous (gapU (nL := nL) sk k) := by
  unfold gapU stW; fun_prop

theorem continuous_gapX (sk : ℝ) : Continuous (gapX (nL := nL) (nR := nR) sk) := by
  unfold gapX stW; fun_prop

theorem isOpen_scaleRegion (sk : ℝ) (k : Fin nR) : IsOpen (scaleRegion (nL := nL) sk k) :=
  (isOpen_lt continuous_const (continuous_gapU sk k)).inter
    (isOpen_lt (continuous_gapU sk k) (continuous_gapX sk))

theorem gapX_pos {sk : ℝ} {k : Fin nR} {p : StateE nL nR × ℝ} (hp : p ∈ scaleRegion sk k) :
    0 < gapX sk p := hp.1.trans hp.2

theorem ratio_mem {sk : ℝ} {k : Fin nR} {p : StateE nL nR × ℝ} (hp : p ∈ scaleRegion sk k) :
    gapU sk k p / gapX sk p ∈ Ioo (0 : ℝ) 1 :=
  ⟨div_pos hp.1 (gapX_pos hp), (div_lt_one (gapX_pos hp)).2 hp.2⟩

theorem contDiffOn_scaleObs (α β sk : ℝ) (k : Fin nR) :
    ContDiffOn ℝ 3 (scaleObs (nL := nL) α β sk k) (scaleRegion sk k) := by
  have hr : ContDiffOn ℝ 3 (fun p : StateE nL nR × ℝ => gapU sk k p / gapX sk p)
      (scaleRegion sk k) := by
    refine ContDiffOn.div ?_ ?_ fun p hp => (gapX_pos hp).ne'
    · unfold gapU stW; fun_prop
    · unfold gapX stW; fun_prop
  exact contDiffOn_scaleFn.comp hr fun p hp => ratio_mem hp

variable {α β sk : ℝ} {k : Fin nR}

theorem partialFst_scaleObs {p : StateE nL nR × ℝ} (hp : p ∈ scaleRegion sk k) (v : StateE nL nR) :
    Ito.partialFst (scaleObs α β sk k) p v =
      scaleDens α β (gapU sk k p / gapX sk p) *
        (((v.2.1 k - v.1) * gapX sk p - gapU sk k p * (v.2.2.2 - v.1)) / gapX sk p ^ 2) := by
  have hX := gapX_pos hp
  have hdiff : DifferentiableAt ℝ (scaleObs α β sk k) p :=
    ((contDiffOn_scaleObs α β sk k).contDiffAt ((isOpen_scaleRegion sk k).mem_nhds hp)).differentiableAt
      (by norm_num)
  refine Ito.partialFst_eq_of_hasDerivAt hdiff ?_
  have hnum : HasDerivAt (fun t : ℝ => gapU sk k p + t * (v.2.1 k - v.1)) (v.2.1 k - v.1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v.2.1 k - v.1)).const_add (gapU sk k p)
  have hden : HasDerivAt (fun t : ℝ => gapX sk p + t * (v.2.2.2 - v.1)) (v.2.2.2 - v.1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v.2.2.2 - v.1)).const_add (gapX sk p)
  have hq : HasDerivAt (fun t : ℝ => (gapU sk k p + t * (v.2.1 k - v.1)) /
      (gapX sk p + t * (v.2.2.2 - v.1)))
      (((v.2.1 k - v.1) * gapX sk p - gapU sk k p * (v.2.2.2 - v.1)) / gapX sk p ^ 2) 0 := by
    have h := hnum.div hden (by simpa using hX.ne')
    simp only [zero_mul, add_zero] at h
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun t => rfl)
  have hF : HasDerivAt (scaleFn α β) (scaleDens α β (gapU sk k p / gapX sk p))
      ((fun t : ℝ => (gapU sk k p + t * (v.2.1 k - v.1)) / (gapX sk p + t * (v.2.2.2 - v.1))) 0) := by
    simp only [zero_mul, add_zero]
    exact hasDerivAt_scaleFn (ratio_mem hp)
  have hc := hF.comp 0 hq
  refine hc.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply, scaleObs, gapU, gapX, stW, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  ring_nf

theorem partialSnd_scaleObs {p : StateE nL nR × ℝ} (hp : p ∈ scaleRegion sk k) :
    Ito.partialSnd (scaleObs α β sk k) p =
      scaleDens α β (gapU sk k p / gapX sk p) * (sk * (p.1.2.1 k - p.1.2.2.2) / gapX sk p ^ 2) := by
  have hX := gapX_pos hp
  have hdiff : DifferentiableAt ℝ (scaleObs α β sk k) p :=
    ((contDiffOn_scaleObs α β sk k).contDiffAt ((isOpen_scaleRegion sk k).mem_nhds hp)).differentiableAt
      (by norm_num)
  refine Ito.partialSnd_eq_of_hasDerivAt hdiff ?_
  have hlin : ∀ c : ℝ, HasDerivAt (fun y : ℝ => c - p.1.1 - sk * y) (-sk) p.2 := fun c => by
    simpa using ((hasDerivAt_id p.2).const_mul sk).const_sub (c - p.1.1)
  have hq := (hlin (p.1.2.1 k)).div (hlin p.1.2.2.2) (by
    show p.1.2.2.2 - p.1.1 - sk * p.2 ≠ 0
    have : gapX sk p = p.1.2.2.2 - p.1.1 - sk * p.2 := by simp only [gapX, stW]; ring
    rw [← this]; exact hX.ne')
  have hu : (p.1.2.1 k - p.1.1 - sk * p.2) / (p.1.2.2.2 - p.1.1 - sk * p.2) ∈ Ioo (0 : ℝ) 1 := by
    have h1 : gapU sk k p = p.1.2.1 k - p.1.1 - sk * p.2 := by simp only [gapU, stW]; ring
    have h2 : gapX sk p = p.1.2.2.2 - p.1.1 - sk * p.2 := by simp only [gapX, stW]; ring
    rw [← h1, ← h2]; exact ratio_mem hp
  have hc := (hasDerivAt_scaleFn (α := α) (β := β) hu).comp p.2 hq
  refine (hc.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [Function.comp_apply, Pi.div_apply, scaleObs, gapU, gapX, stW]
    congr 1
    ring_nf
  · have h1 : gapU sk k p = p.1.2.1 k - p.1.1 - sk * p.2 := by simp only [gapU, stW]; ring
    have h2 : gapX sk p = p.1.2.2.2 - p.1.1 - sk * p.2 := by simp only [gapX, stW]; ring
    rw [h1, h2]
    congr 1
    field_simp
    ring

theorem partialSndSnd_scaleObs {p : StateE nL nR × ℝ} (hp : p ∈ scaleRegion sk k) :
    Ito.partialSndSnd (scaleObs α β sk k) p =
      scaleDens α β (gapU sk k p / gapX sk p) *
        ((-α / (gapU sk k p / gapX sk p) - β / (1 - gapU sk k p / gapX sk p)) * sk ^ 2 *
            (p.1.2.1 k - p.1.2.2.2) ^ 2 / gapX sk p ^ 4 +
          2 * sk ^ 2 * (p.1.2.1 k - p.1.2.2.2) / gapX sk p ^ 3) := by
  have hcd : ContDiffAt ℝ 2 (scaleObs α β sk k) p :=
    ((contDiffOn_scaleObs α β sk k).contDiffAt ((isOpen_scaleRegion sk k).mem_nhds hp)).of_le
      (by norm_num)
  set V := p.1.2.1 k with hV
  set Y := p.1.2.2.2 with hY
  set A := p.1.1 with hA
  set uf : ℝ → ℝ := fun y => (V - A - sk * y) / (Y - A - sk * y) with huf
  set Xf : ℝ → ℝ := fun y => Y - A - sk * y with hXf
  set g : ℝ → ℝ := fun y => scaleDens α β (uf y) * (sk * (V - Y) / Xf y ^ 2) with hg
  have hline : ContinuousAt (fun y : ℝ => ((p.1, y) : StateE nL nR × ℝ)) p.2 :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hev : ∀ᶠ y in 𝓝 p.2, ((p.1, y) : StateE nL nR × ℝ) ∈ scaleRegion sk k :=
    hline.eventually ((isOpen_scaleRegion sk k).mem_nhds (by simpa using hp))
  have hU : gapU sk k p = V - A - sk * p.2 := by simp only [gapU, stW, hV, hA]; ring
  have hXp : gapX sk p = Y - A - sk * p.2 := by simp only [gapX, stW, hY, hA]; ring
  refine Ito.partialSndSnd_eq_of_hasDerivAt hcd (g := g) (hev.mono fun y hy => ?_) ?_
  · rw [partialSnd_scaleObs hy]
    simp only [hg, huf, hXf, gapU, gapX, stW, hV, hY, hA]
    congr 2 <;> ring
  · have hX := gapX_pos hp
    have hu := ratio_mem hp
    rw [hU, hXp] at hu
    rw [hXp] at hX
    have hlin : ∀ c : ℝ, HasDerivAt (fun y : ℝ => c - A - sk * y) (-sk) p.2 := fun c => by
      simpa using ((hasDerivAt_id p.2).const_mul sk).const_sub (c - A)
    have hq : HasDerivAt uf ((-sk * (Y - A - sk * p.2) - (V - A - sk * p.2) * -sk) /
        (Y - A - sk * p.2) ^ 2) p.2 := by
      have h := (hlin V).div (hlin Y) hX.ne'
      exact h.congr_of_eventuallyEq (Eventually.of_forall fun t => rfl)
    have hG1 := (hasDerivAt_scaleDens (α := α) (β := β) hu).comp p.2 hq
    have hG2 : HasDerivAt (fun y => sk * (V - Y) / Xf y ^ 2)
        (-(sk * (V - Y)) * (2 * Xf p.2 * -sk) / (Xf p.2 ^ 2) ^ 2) p.2 := by
      have h := ((hlin Y).pow 2).inv (pow_ne_zero 2 hX.ne')
      have h2 := h.const_mul (sk * (V - Y))
      refine (h2.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).congr_deriv ?_
      · simp only [hXf, div_eq_mul_inv, Pi.inv_apply, Pi.pow_apply]
      · simp only [hXf, Pi.pow_apply]
        norm_num
        field_simp
    have hprod := hG1.mul hG2
    refine (hprod.congr_of_eventuallyEq (Eventually.of_forall fun t => rfl)).congr_deriv ?_
    simp only [Function.comp_apply, hXf, huf, hU, hXp]
    have hXne : Y - A - sk * p.2 ≠ 0 := hX.ne'
    field_simp
    ring

/-- **The observable has zero Itô drift** along the one-group dynamics
`V' − A' = (2 + ρ)/û`, `Y' − A' = 2/X + ρ/û`, when `α = 2(2 + ρ)/κ`, `β = 2(4 + ρ − κ)/κ`, `sk² = κ`. -/
theorem itoGen_scaleObs_eq_zero {κ ρ : ℝ} (hκ : 0 < κ) (hsk : sk ^ 2 = κ)
    (hα : α = 2 * (2 + ρ) / κ) (hβ : β = 2 * (4 + ρ - κ) / κ) {p : StateE nL nR × ℝ}
    (hp : p ∈ scaleRegion sk k) {v : StateE nL nR}
    (h1 : v.2.1 k - v.1 = (2 + ρ) / gapU sk k p) (h2 : v.2.2.2 - v.1 = 2 / gapX sk p + ρ / gapU sk k p) :
    Ito.itoGen (scaleObs α β sk k) p v = 0 := by
  rw [Ito.itoGen, partialFst_scaleObs hp, partialSndSnd_scaleObs hp, h1, h2]
  have hU := hp.1
  have hX := gapX_pos hp
  have hVY : p.1.2.1 k - p.1.2.2.2 = gapU sk k p - gapX sk p := by
    simp only [gapU, gapX]; ring
  rw [hVY, hsk, hα, hβ]
  set u := gapU sk k p with hudef
  set X := gapX sk p with hXdef
  have hXu : X - u ≠ 0 := (sub_pos.2 hp.2).ne'
  have h1u : 1 - u / X ≠ 0 := by
    rw [one_sub_div hX.ne']; exact div_ne_zero hXu hX.ne'
  have hu0 : u / X ≠ 0 := div_ne_zero hU.ne' hX.ne'
  field_simp
  ring

end Obs

end Aux25

end InteractingSLE
