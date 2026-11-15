/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12LowLyap
import InteractingSLE.Spec.Supplement.G12Obs

/-!
# Lemma G12 when the weight before the mark is `≤ −2`: the Lyapunov observable and its generator

Packet PROVE-G12C. In the coordinates of PROVE-G12's localized Itô formula (`G12Obs.lean`: `Λ = (V^L, V^R, T)`, the
Brownian coordinate `b`, the driver `W = √κ b + ℓ(V)`), for right marks `k` (inner) and `j₀` (target), the observable

  `lowObs = h(log o − log e)`,  `o = V^k − W`,  `e = V^{j₀} − V^k`,

with the Lyapunov function `h` of `G12LowLyap.lean`, is smooth on `{o > 0, e > 0}` (`contDiffOn_lowObs`). Along the
density `(2/(V^L − W), 2/(V^R − W), u⁻²)` of an evolution, with the marks of the group of `j₀` at `V^{j₀}`, its Itô
generator is

  `(L h)(Y)/o² − h'(Y) D/o`  (`itoGen_lowObs_dens`),

where `L h` is the generator of the two-mark reference (weight `S` at `k`, the group weight `ρ_Y` at `j₀`:
`b₋ = S + 2 − κ/2`, `b₊ = S + ρ_Y + 4 − κ/2`) and `D = Σᵢ ρ_{i,L}/(W − V^{i,L}) + Σⱼ (ρ_{j,R} − ρ'ⱼ)/(W − V^{j,R})` is
the drift difference between the actual word and the reference weights `ρ'` (`lowRefW`). With the Lyapunov bounds this
gives the pathwise inequality used by the expectation argument (`budget_le_itoGen_lowObs`):

  `β/(2c₃) − D²/κ ≤ itoGen(lowObs)`,  `β = 4e/(u²o) + 4e/u³` the two-mark budget of `G12Det`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Finset Real
open scoped NNReal

namespace InteractingSLE

namespace Supp7

namespace G12Low

open G12 (GCoord gDriftLin gDriftLin₀ g12Dens offY onY rhoY)

variable {nL nR : ℕ}

/-! ### Parameters of the reference -/

/-- The reference weights: `S` at the inner mark `k`, the actual weights on the group of `j₀`, `0` elsewhere. -/
def lowRefW (xR : Fin nR → ℝ) (ρR : Fin nR → ℝ) (k j₀ : Fin nR) (S : ℝ) (j : Fin nR) : ℝ :=
  (if j = k then S else 0) + (if xR j = xR j₀ then ρR j else 0)

/-- `b₋ = S + 2 − κ/2`. -/
def lowBm (κ S : ℝ) : ℝ := S + 2 - κ / 2

/-- `b₊ = S + ρ_Y + 4 − κ/2`. -/
def lowBp (κ S ρY : ℝ) : ℝ := S + ρY + 4 - κ / 2

/-- `α = min(1/2, min(b₊, −b₋)/κ)`. -/
def lowAlpha (κ bm bp : ℝ) : ℝ := min (1 / 2) (min bp (-bm) / κ)

/-- `c₃ = 8 cosh(Y₀/2)/(κα²)`. -/
def lowC3 (κ bm bp : ℝ) : ℝ := 8 * cosh (lowY0 bm bp / 2) / (κ * lowAlpha κ bm bp ^ 2)

theorem lowAlpha_pos {κ bm bp : ℝ} (hκ : 0 < κ) (hbm : bm < 0) (hbp : 0 < bp) : 0 < lowAlpha κ bm bp :=
  lt_min (by norm_num) (div_pos (lt_min hbp (neg_pos.2 hbm)) hκ)

theorem lowAlpha_le {κ bm bp : ℝ} : lowAlpha κ bm bp ≤ 1 / 2 := min_le_left _ _

theorem mul_lowAlpha_le {κ bm bp : ℝ} (hκ : 0 < κ) : κ * lowAlpha κ bm bp ≤ min bp (-bm) := by
  have h : lowAlpha κ bm bp ≤ min bp (-bm) / κ := min_le_right _ _
  rw [le_div_iff₀ hκ] at h
  linarith

theorem lowC3_pos {κ bm bp : ℝ} (hκ : 0 < κ) (hbm : bm < 0) (hbp : 0 < bp) : 0 < lowC3 κ bm bp := by
  unfold lowC3
  have := lowAlpha_pos hκ hbm hbp
  have := cosh_pos (lowY0 bm bp / 2)
  positivity

/-! ### The observable -/

/-- `o = V^k − W` with `W = √κ b + ℓ(V)`. -/
def lowO (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (k : Fin nR)
    (p : GCoord nL nR × ℝ) : ℝ :=
  p.1.2.1 k - (Real.sqrt κ * p.2 + gDriftLin xL xR ρL ρR p.1)

/-- `e = V^{j₀} − V^k`. -/
def lowE (k j₀ : Fin nR) (p : GCoord nL nR × ℝ) : ℝ := p.1.2.1 j₀ - p.1.2.1 k

/-- **The Lyapunov observable** `h(log o − log e)`. -/
def lowObs (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (k j₀ : Fin nR)
    (α Y₀ : ℝ) (p : GCoord nL nR × ℝ) : ℝ :=
  lowH α Y₀ (log (lowO κ xL xR ρL ρR k p) - log (lowE k j₀ p))

/-- Its region of smoothness `{o > 0, e > 0}`. -/
def lowRegion (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (k j₀ : Fin nR) : Set (GCoord nL nR × ℝ) :=
  {p | 0 < lowO κ xL xR ρL ρR k p ∧ 0 < lowE k j₀ p}

variable (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (k j₀ : Fin nR)
  (α Y₀ : ℝ)

theorem contDiff_lowO {n : WithTop ℕ∞} : ContDiff ℝ n (lowO κ xL xR ρL ρR k) := by
  unfold lowO gDriftLin
  fun_prop

theorem contDiff_lowE {n : WithTop ℕ∞} : ContDiff ℝ n (lowE (nL := nL) k j₀) := by
  unfold lowE
  fun_prop

theorem isOpen_lowRegion : IsOpen (lowRegion κ xL xR ρL ρR k j₀) :=
  (isOpen_lt continuous_const (contDiff_lowO κ xL xR ρL ρR k (n := 0)).continuous).inter
    (isOpen_lt continuous_const (contDiff_lowE (nL := nL) k j₀ (n := 0)).continuous)

theorem contDiffOn_lowObs {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (lowObs κ xL xR ρL ρR k j₀ α Y₀) (lowRegion κ xL xR ρL ρR k j₀) := by
  have h1 : ContDiffOn ℝ n (fun p => log (lowO κ xL xR ρL ρR k p) - log (lowE k j₀ p))
      (lowRegion κ xL xR ρL ρR k j₀) :=
    ((contDiff_lowO κ xL xR ρL ρR k).contDiffOn.log fun p hp => hp.1.ne').sub
      ((contDiff_lowE k j₀).contDiffOn.log fun p hp => hp.2.ne')
  exact (contDiff_lowH α Y₀).comp_contDiffOn h1

theorem contDiffAt_lowObs {n : WithTop ℕ∞} {p : GCoord nL nR × ℝ} (hp : p ∈ lowRegion κ xL xR ρL ρR k j₀) :
    ContDiffAt ℝ n (lowObs κ xL xR ρL ρR k j₀ α Y₀) p :=
  (contDiffOn_lowObs κ xL xR ρL ρR k j₀ α Y₀).contDiffAt ((isOpen_lowRegion κ xL xR ρL ρR k j₀).mem_nhds hp)

omit κ k j₀ α Y₀ in
theorem gDriftLin_add_smul (q v : GCoord nL nR) (t : ℝ) :
    gDriftLin xL xR ρL ρR (q + t • v) = gDriftLin xL xR ρL ρR q + t * gDriftLin₀ ρL ρR v := by
  simp only [gDriftLin, gDriftLin₀, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  have e1 : ∑ i, ρL i * (q.1 i + t * v.1 i - xL i) = ∑ i, ρL i * (q.1 i - xL i) + t * ∑ i, ρL i * v.1 i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ j, ρR j * (q.2.1 j + t * v.2.1 j - xR j) =
      ∑ j, ρR j * (q.2.1 j - xR j) + t * ∑ j, ρR j * v.2.1 j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2]
  ring

/-- `∂_Λ` of the observable: `h'(Y) (o_v/o − e_v/e)`. -/
theorem partialFst_lowObs {p : GCoord nL nR × ℝ} (hp : p ∈ lowRegion κ xL xR ρL ρR k j₀) (v : GCoord nL nR) :
    Ito.partialFst (lowObs κ xL xR ρL ρR k j₀ α Y₀) p v =
      lowH1 α Y₀ (log (lowO κ xL xR ρL ρR k p) - log (lowE k j₀ p)) *
        ((v.2.1 k - gDriftLin₀ ρL ρR v) / lowO κ xL xR ρL ρR k p - (v.2.1 j₀ - v.2.1 k) / lowE k j₀ p) := by
  have hd : DifferentiableAt ℝ (lowObs κ xL xR ρL ρR k j₀ α Y₀) p :=
    (contDiffAt_lowObs κ xL xR ρL ρR k j₀ α Y₀ (n := 1) hp).differentiableAt (by norm_num)
  refine Ito.partialFst_eq_of_hasDerivAt hd ?_
  set o := lowO κ xL xR ρL ρR k p
  set e := lowE k j₀ p
  have hline : (fun t : ℝ => lowObs κ xL xR ρL ρR k j₀ α Y₀ (p.1 + t • v, p.2)) = fun t =>
      lowH α Y₀ (log (o + t * (v.2.1 k - gDriftLin₀ ρL ρR v)) - log (e + t * (v.2.1 j₀ - v.2.1 k))) := by
    funext t
    simp only [lowObs, lowO, lowE, o, e, gDriftLin_add_smul, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    congr 2
    · congr 1; ring
    · congr 1; ring
  rw [hline]
  set d := v.2.1 k - gDriftLin₀ ρL ρR v
  set d' := v.2.1 j₀ - v.2.1 k
  have hin : HasDerivAt (fun t : ℝ => log (o + t * d) - log (e + t * d')) (d / o - d' / e) 0 :=
    (G12.hasDerivAt_log_add_mul hp.1.ne').sub (G12.hasDerivAt_log_add_mul hp.2.ne')
  have h := (hasDerivAt_lowH α Y₀ (log (o + 0 * d) - log (e + 0 * d'))).comp 0 hin
  simp only [zero_mul, add_zero] at h
  exact h

/-- The Brownian-slot derivative: `∂_b (lowObs) = h'(Y) (−√κ/o)`. -/
theorem hasDerivAt_lowObs_snd {p : GCoord nL nR × ℝ} (hp : p ∈ lowRegion κ xL xR ρL ρR k j₀) :
    HasDerivAt (fun y : ℝ => lowObs κ xL xR ρL ρR k j₀ α Y₀ (p.1, y))
      (lowH1 α Y₀ (log (lowO κ xL xR ρL ρR k p) - log (lowE k j₀ p)) *
        (-Real.sqrt κ / lowO κ xL xR ρL ρR k p)) p.2 := by
  have h1 : HasDerivAt (fun y : ℝ => lowO κ xL xR ρL ρR k (p.1, y)) (-(Real.sqrt κ * 1)) p.2 := by
    exact (((hasDerivAt_id' p.2).const_mul (Real.sqrt κ)).add_const (gDriftLin xL xR ρL ρR p.1)).const_sub
      (p.1.2.1 k)
  have h2 : HasDerivAt (fun y : ℝ => log (lowO κ xL xR ρL ρR k (p.1, y)) - log (lowE k j₀ (p.1, y)))
      (-(Real.sqrt κ * 1) / lowO κ xL xR ρL ρR k p) p.2 := by
    have := (h1.log (by simpa using hp.1.ne')).sub_const (log (lowE k j₀ p))
    simpa only [lowE] using this
  have h := (hasDerivAt_lowH α Y₀ _).comp p.2 h2
  refine h.congr_deriv ?_
  simp only [mul_one, neg_div]

theorem partialSnd_lowObs {p : GCoord nL nR × ℝ} (hp : p ∈ lowRegion κ xL xR ρL ρR k j₀) :
    Ito.partialSnd (lowObs κ xL xR ρL ρR k j₀ α Y₀) p =
      lowH1 α Y₀ (log (lowO κ xL xR ρL ρR k p) - log (lowE k j₀ p)) *
        (-Real.sqrt κ / lowO κ xL xR ρL ρR k p) :=
  Ito.partialSnd_eq_of_hasDerivAt ((contDiffAt_lowObs κ xL xR ρL ρR k j₀ α Y₀ (n := 1) hp).differentiableAt
    (by norm_num)) (hasDerivAt_lowObs_snd κ xL xR ρL ρR k j₀ α Y₀ hp)

/-- `∂²_b (lowObs) = κ (h''(Y) − h'(Y))/o²`. -/
theorem partialSndSnd_lowObs (hκ : 0 ≤ κ) {p : GCoord nL nR × ℝ} (hp : p ∈ lowRegion κ xL xR ρL ρR k j₀) :
    Ito.partialSndSnd (lowObs κ xL xR ρL ρR k j₀ α Y₀) p =
      κ * (lowH2 α Y₀ (log (lowO κ xL xR ρL ρR k p) - log (lowE k j₀ p)) -
        lowH1 α Y₀ (log (lowO κ xL xR ρL ρR k p) - log (lowE k j₀ p))) / lowO κ xL xR ρL ρR k p ^ 2 := by
  set c := p.1.2.1 k - gDriftLin xL xR ρL ρR p.1 with hc
  set e := lowE k j₀ p with he
  have hline : ContinuousAt (fun y : ℝ => ((p.1, y) : GCoord nL nR × ℝ)) p.2 :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hev : ∀ᶠ y in 𝓝 p.2, ((p.1, y) : GCoord nL nR × ℝ) ∈ lowRegion κ xL xR ρL ρR k j₀ :=
    hline.eventually ((isOpen_lowRegion κ xL xR ρL ρR k j₀).mem_nhds (by simpa using hp))
  have ho : ∀ y : ℝ, lowO κ xL xR ρL ρR k (p.1, y) = c - Real.sqrt κ * y := fun y => by
    simp only [lowO, hc]; ring
  have heq : ∀ y : ℝ, lowE k j₀ (p.1, y) = e := fun y => rfl
  set g : ℝ → ℝ := fun y => lowH1 α Y₀ (log (c - Real.sqrt κ * y) - log e) *
    (-Real.sqrt κ / (c - Real.sqrt κ * y)) with hg
  have hop : lowO κ xL xR ρL ρR k p = c - Real.sqrt κ * p.2 := by rw [← ho]
  have hne : c - Real.sqrt κ * p.2 ≠ 0 := by rw [← hop]; exact hp.1.ne'
  refine Ito.partialSndSnd_eq_of_hasDerivAt (contDiffAt_lowObs κ xL xR ρL ρR k j₀ α Y₀ hp) (g := g)
    (hev.mono fun y hy => ?_) ?_
  · rw [partialSnd_lowObs κ xL xR ρL ρR k j₀ α Y₀ hy, ho, heq]
  · have h1 : HasDerivAt (fun y : ℝ => c - Real.sqrt κ * y) (-(Real.sqrt κ * 1)) p.2 :=
      ((hasDerivAt_id p.2).const_mul (Real.sqrt κ)).const_sub c
    have hY : HasDerivAt (fun y : ℝ => log (c - Real.sqrt κ * y) - log e)
        (-(Real.sqrt κ * 1) / (c - Real.sqrt κ * p.2)) p.2 := (h1.log hne).sub_const _
    have hA := (hasDerivAt_lowH1 α Y₀ _).comp p.2 hY
    have hB : HasDerivAt (fun y : ℝ => -Real.sqrt κ / (c - Real.sqrt κ * y))
        (-(-(-(Real.sqrt κ * 1)) / (c - Real.sqrt κ * p.2) ^ 2) * Real.sqrt κ) p.2 := by
      have := (h1.inv hne).const_mul (-Real.sqrt κ)
      refine this.congr_deriv ?_
      ring
    have h := hA.mul hB
    refine h.congr_deriv ?_
    rw [hop]
    have hs : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ
    simp only [Function.comp_apply]
    field_simp
    rw [hs]
    ring

/-- **The Itô generator of the observable.** -/
theorem itoGen_lowObs (hκ : 0 ≤ κ) {p : GCoord nL nR × ℝ} (hp : p ∈ lowRegion κ xL xR ρL ρR k j₀)
    (v : GCoord nL nR) :
    Ito.itoGen (lowObs κ xL xR ρL ρR k j₀ α Y₀) p v =
      lowH1 α Y₀ (log (lowO κ xL xR ρL ρR k p) - log (lowE k j₀ p)) *
        ((v.2.1 k - gDriftLin₀ ρL ρR v) / lowO κ xL xR ρL ρR k p - (v.2.1 j₀ - v.2.1 k) / lowE k j₀ p) +
      1 / 2 * (κ * (lowH2 α Y₀ (log (lowO κ xL xR ρL ρR k p) - log (lowE k j₀ p)) -
        lowH1 α Y₀ (log (lowO κ xL xR ρL ρR k p) - log (lowE k j₀ p))) / lowO κ xL xR ρL ρR k p ^ 2) := by
  rw [Ito.itoGen, partialFst_lowObs κ xL xR ρL ρR k j₀ α Y₀ hp,
    partialSndSnd_lowObs κ xL xR ρL ρR k j₀ α Y₀ hκ hp]

/-! ### Along the density of an evolution -/

omit κ k j₀ α Y₀ in
/-- `ℓ₀` of the density is the drift `Σ ρ/(W − V)` of the driver. -/
theorem gDriftLin₀_g12Dens (w : ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) (j₀ : Fin nR) :
    gDriftLin₀ ρL ρR (g12Dens j₀ w vL vR) = (∑ i, ρL i / (w - vL i)) + ∑ j, ρR j / (w - vR j) := by
  simp only [gDriftLin₀, g12Dens]
  have hL : -(1 / 2) * ∑ i, ρL i * (2 / (vL i - w)) = ∑ i, ρL i / (w - vL i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← neg_sub (vL i) w, div_neg]
    ring
  have hR : -(1 / 2 * ∑ j, ρR j * (2 / (vR j - w))) = ∑ j, ρR j / (w - vR j) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← neg_sub (vR j) w, div_neg]
    ring
  rw [sub_eq_add_neg, hL, hR]

omit κ xL ρL α Y₀ in
/-- The reference drift: `Σⱼ ρ'ⱼ/(W − V^j) = S/(W − V^k) + ρ_Y/(W − V^{j₀})` with the group of `j₀` at `V^{j₀}`. -/
theorem sum_lowRefW_div {w : ℝ} {vR : Fin nR → ℝ} (S : ℝ) (hgrp : ∀ j, xR j = xR j₀ → vR j = vR j₀) :
    ∑ j, lowRefW xR ρR k j₀ S j / (w - vR j) = S / (w - vR k) + rhoY xR ρR j₀ / (w - vR j₀) := by
  simp only [lowRefW, add_div, Finset.sum_add_distrib]
  congr 1
  · simp only [ite_div, zero_div, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  · rw [rhoY, Finset.sum_div, G12.onY, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : xR j = xR j₀
    · simp only [hj, ↓reduceIte, hgrp j hj]
    · simp only [hj, ↓reduceIte, zero_div]

/-- **The generator along the density**: `(L h)(Y)/o² − h'(Y) D/o`, where `L h` is the reference generator (weight
`S` at `k`, `ρ_Y` at `j₀`) and `D` the drift difference to the reference. -/
theorem itoGen_lowObs_dens (hκ : 0 ≤ κ) (S : ℝ) {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} {T b w : ℝ}
    (hw : w = Real.sqrt κ * b + gDriftLin xL xR ρL ρR (vL, vR, T)) (ho : 0 < vR k - w)
    (he : 0 < vR j₀ - vR k) (hgrp : ∀ j, xR j = xR j₀ → vR j = vR j₀) :
    Ito.itoGen (lowObs κ xL xR ρL ρR k j₀ α Y₀) ((vL, vR, T), b) (g12Dens j₀ w vL vR) =
      lowGen κ (lowBm κ S) (lowBp κ S (rhoY xR ρR j₀)) α Y₀ (log (vR k - w) - log (vR j₀ - vR k)) /
          (vR k - w) ^ 2 -
        lowH1 α Y₀ (log (vR k - w) - log (vR j₀ - vR k)) *
          ((∑ i, ρL i / (w - vL i)) + ∑ j, (ρR j - lowRefW xR ρR k j₀ S j) / (w - vR j)) / (vR k - w) := by
  have hO : lowO κ xL xR ρL ρR k ((vL, vR, T), b) = vR k - w := by simp only [lowO, hw]
  have hE : lowE k j₀ (((vL, vR, T), b) : GCoord nL nR × ℝ) = vR j₀ - vR k := rfl
  have hp : (((vL, vR, T), b) : GCoord nL nR × ℝ) ∈ lowRegion κ xL xR ρL ρR k j₀ := by
    refine ⟨?_, ?_⟩
    · rw [hO]; exact ho
    · rw [hE]; exact he
  rw [itoGen_lowObs κ xL xR ρL ρR k j₀ α Y₀ hκ hp, hO, hE, gDriftLin₀_g12Dens]
  have hsub : ∑ j, (ρR j - lowRefW xR ρR k j₀ S j) / (w - vR j) =
      (∑ j, ρR j / (w - vR j)) - (S / (w - vR k) + rhoY xR ρR j₀ / (w - vR j₀)) := by
    rw [← sum_lowRefW_div xR ρR k j₀ S hgrp, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => sub_div _ _ _
  rw [hsub]
  simp only [g12Dens]
  have ho' : vR k - w ≠ 0 := ho.ne'
  have he' : vR j₀ - vR k ≠ 0 := he.ne'
  have hu' : vR j₀ - w ≠ 0 := by linarith
  have hwk : w - vR k ≠ 0 := by linarith
  have hwj : w - vR j₀ ≠ 0 := by linarith
  have hexp : exp (-(log (vR k - w) - log (vR j₀ - vR k))) = (vR j₀ - vR k) / (vR k - w) := by
    rw [neg_sub, exp_sub, exp_log he, exp_log ho]
  unfold lowGen lowDrift lowBm lowBp
  rw [hexp]
  have hd : 1 + (vR j₀ - vR k) / (vR k - w) ≠ 0 := by
    have : 0 < (vR j₀ - vR k) / (vR k - w) := div_pos he ho
    linarith
  field_simp
  ring

/-- **The pathwise inequality of the expectation argument**: for `S ≤ −2` and `b₊ > 0`,
`β/(2c₃) − D²/κ ≤ itoGen(lowObs)` along the density, `β = 4e/(u²o) + 4e/u³` the two-mark budget. -/
theorem budget_le_itoGen_lowObs (hκ : 0 < κ) {S : ℝ} (hS : S ≤ -2) (hbp : 0 < lowBp κ S (rhoY xR ρR j₀))
    {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} {T b w : ℝ}
    (hw : w = Real.sqrt κ * b + gDriftLin xL xR ρL ρR (vL, vR, T)) (ho : 0 < vR k - w)
    (he : 0 < vR j₀ - vR k) (hgrp : ∀ j, xR j = xR j₀ → vR j = vR j₀) :
    (4 * (vR j₀ - vR k) / ((vR j₀ - w) ^ 2 * (vR k - w)) + 4 * (vR j₀ - vR k) / (vR j₀ - w) ^ 3) /
          (2 * lowC3 κ (lowBm κ S) (lowBp κ S (rhoY xR ρR j₀))) -
        ((∑ i, ρL i / (w - vL i)) + ∑ j, (ρR j - lowRefW xR ρR k j₀ S j) / (w - vR j)) ^ 2 / κ ≤
      Ito.itoGen (lowObs κ xL xR ρL ρR k j₀ (lowAlpha κ (lowBm κ S) (lowBp κ S (rhoY xR ρR j₀)))
        (lowY0 (lowBm κ S) (lowBp κ S (rhoY xR ρR j₀)))) ((vL, vR, T), b) (g12Dens j₀ w vL vR) := by
  set bm := lowBm κ S with hbmdef
  set bp := lowBp κ S (rhoY xR ρR j₀) with hbpdef
  have hbm : bm < 0 := by rw [hbmdef, lowBm]; linarith
  set α := lowAlpha κ bm bp
  have hα0 : 0 < α := lowAlpha_pos hκ hbm hbp
  have hα : α ≤ 1 / 2 := lowAlpha_le
  have hαp : κ * α ≤ bp := (mul_lowAlpha_le hκ).trans (min_le_left _ _)
  have hαm : κ * α ≤ -bm := (mul_lowAlpha_le hκ).trans (min_le_right _ _)
  rw [itoGen_lowObs_dens κ xL xR ρL ρR k j₀ α (lowY0 bm bp) hκ.le S hw ho he hgrp]
  set o := vR k - w with hodef
  set e := vR j₀ - vR k with hedef
  have hu : vR j₀ - w = o + e := by rw [hodef, hedef]; ring
  rw [hu]
  set D := (∑ i, ρL i / (w - vL i)) + ∑ j, (ρR j - lowRefW xR ρR k j₀ S j) / (w - vR j)
  have h1 := lowGen_sub_ge hbm hbp hα0 hα hκ hαp hαm (log o - log e) ho D
  have h2 := budget_le_lowGen hbm hbp hα0 hα hκ hαp hαm ho he
  have hc3 : 0 < lowC3 κ bm bp := lowC3_pos hκ hbm hbp
  set G := lowGen κ bm bp α (lowY0 bm bp) (log o - log e)
  have h3 : (4 * e / ((o + e) ^ 2 * o) + 4 * e / (o + e) ^ 3) / (2 * lowC3 κ bm bp) ≤ G / (2 * o ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h2' : 4 * e / ((o + e) ^ 2 * o) + 4 * e / (o + e) ^ 3 ≤ lowC3 κ bm bp * (G / o ^ 2) := h2
    have : lowC3 κ bm bp * (G / o ^ 2) * (2 * o ^ 2) = G * (2 * lowC3 κ bm bp) := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_right h2' (show (0 : ℝ) ≤ 2 * o ^ 2 by positivity)]
  linarith

end G12Low

end Supp7

end InteractingSLE
