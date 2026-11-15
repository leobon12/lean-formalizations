/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A5ClearanceJacobi
import InteractingSLE.Spec.Zhan.StripNoncollisionGen
import InteractingSLE.Spec.Ito.TwoPointGen

/-!
# Protected-ray clearance, II: the Lyapunov observable and its Itô generator

Packet PROVE-ZHAN-CLEAR. The state of the separated two-force law is `Λ = (V^R, V^L, D, s) ∈ ℝ⁴` together with the
Brownian slot `x = B`, where `D = W − √κ B` is the drift part of the driver and `s = ∫₀ᵗ Z⁻²` the capacity clock of
the right mark. In these coordinates

  `Z = V^R − D − √κ x`,  `Y = D + √κ x − V^L`,  `Y + Z = V^R − V^L`,  `v = Y/(Y + Z)`,

and the state solves `Λ' = (2/Z, −2/Y, ρ_L/Y − ρ_R/Z, Z⁻²)` (`clrField`). The observable is
`Φ = exp(−λ(log Z + s/3 + q(v)))` (`lyapObs`) with `λ, q` from `exists_lyapunov`.

## Main results

* `itoGen_lyapV`: the Itô generator of `log Z + s/3 + q(v)` along `clrField` is `lyapDrift` (the computation of
  `A5ClearanceJacobi`'s docstring), and its `x`-derivative is `√κ (q'(v)/(Y + Z) − 1/Z)`;
* **`itoGen_lyapObs_nonpos`**: the generator of `Φ` is `≤ 0` on the region `{Z > 0, Y > 0}`;
* `contDiffOn_lyapObs`, `isOpen_clrRegion`, `continuousOn_clrField`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace InteractingSLE.ZhanGT4.A5Clear

/-- The state space `(V^R, V^L, D, s)`. -/
abbrev CE := ℝ × ℝ × ℝ × ℝ

section Coord

variable (κ : ℝ)

/-- `Z = V^R − D − √κ x`. -/
def zC (p : CE × ℝ) : ℝ := p.1.1 - p.1.2.2.1 - Real.sqrt κ * p.2

/-- `Y = D + √κ x − V^L`. -/
def yC (p : CE × ℝ) : ℝ := p.1.2.2.1 + Real.sqrt κ * p.2 - p.1.2.1

/-- `Y + Z = V^R − V^L`. -/
def dC (p : CE × ℝ) : ℝ := p.1.1 - p.1.2.1

/-- The clock `s`. -/
def sC (p : CE × ℝ) : ℝ := p.1.2.2.2

/-- The angle `v = Y/(Y + Z)`. -/
def vC (p : CE × ℝ) : ℝ := yC κ p / dC p

theorem yC_add_zC (p : CE × ℝ) : yC κ p + zC κ p = dC p := by
  simp only [yC, zC, dC]; ring

/-- `log Z + s/3 + q(v)`. -/
def lyapV (q : ℝ → ℝ) (p : CE × ℝ) : ℝ := Real.log (zC κ p) + sC p / 3 + q (vC κ p)

/-- The observable `Φ = exp(−λ(log Z + s/3 + q(v)))`. -/
def lyapObs (lam : ℝ) (q : ℝ → ℝ) (p : CE × ℝ) : ℝ := Real.exp (-(lam * lyapV κ q p))

/-- The region `{Z > 0, Y > 0}`. -/
def clrRegion : Set (CE × ℝ) := {p | 0 < zC κ p ∧ 0 < yC κ p}

/-- The state velocity `(2/Z, −2/Y, ρ_L/Y − ρ_R/Z, Z⁻²)`. -/
def clrField (ρL ρR : ℝ) (p : CE × ℝ) : CE :=
  (2 / zC κ p, -2 / yC κ p, ρL / yC κ p - ρR / zC κ p, 1 / zC κ p ^ 2)

theorem contDiff_zC {n : WithTop ℕ∞} : ContDiff ℝ n (zC κ) :=
  ((contDiff_fst.fst).sub contDiff_fst.snd.snd.fst).sub (contDiff_const.mul contDiff_snd)

theorem contDiff_yC {n : WithTop ℕ∞} : ContDiff ℝ n (yC κ) :=
  (contDiff_fst.snd.snd.fst.add (contDiff_const.mul contDiff_snd)).sub contDiff_fst.snd.fst

theorem contDiff_dC {n : WithTop ℕ∞} : ContDiff ℝ n dC :=
  contDiff_fst.fst.sub contDiff_fst.snd.fst

theorem contDiff_sC {n : WithTop ℕ∞} : ContDiff ℝ n sC :=
  contDiff_fst.snd.snd.snd

theorem continuous_zC : Continuous (zC κ) := (contDiff_zC κ (n := 0)).continuous

theorem continuous_yC : Continuous (yC κ) := (contDiff_yC κ (n := 0)).continuous

theorem isOpen_clrRegion : IsOpen (clrRegion κ) :=
  (isOpen_lt continuous_const (continuous_zC κ)).inter (isOpen_lt continuous_const (continuous_yC κ))

theorem dC_pos {p : CE × ℝ} (hp : p ∈ clrRegion κ) : 0 < dC p := by
  rw [← yC_add_zC]; exact add_pos hp.2 hp.1

theorem continuousOn_clrField (ρL ρR : ℝ) : ContinuousOn (clrField κ ρL ρR) (clrRegion κ) := by
  have hz : ContinuousOn (zC κ) (clrRegion κ) := (continuous_zC κ).continuousOn
  have hy : ContinuousOn (yC κ) (clrRegion κ) := (continuous_yC κ).continuousOn
  have hz0 : ∀ p ∈ clrRegion κ, zC κ p ≠ 0 := fun p hp => hp.1.ne'
  have hy0 : ∀ p ∈ clrRegion κ, yC κ p ≠ 0 := fun p hp => hp.2.ne'
  refine (continuousOn_const.div hz hz0).prodMk ((continuousOn_const.div hy hy0).prodMk
    (((continuousOn_const.div hy hy0).sub (continuousOn_const.div hz hz0)).prodMk
      (continuousOn_const.div (hz.pow 2) fun p hp => pow_ne_zero 2 (hz0 p hp))))

end Coord

/-! ### Generators of the coordinates -/

section Affine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The generator and the `x`-derivative of a function whose `x`-derivative is a constant `σ` along the line through
`p` (so that its second `x`-derivative vanishes). -/
theorem itoGen_affine {F : E × ℝ → ℝ} {p : E × ℝ} (hF : ContDiffAt ℝ 2 F p) {σ : ℝ}
    (hσ : ∀ y, HasDerivAt (fun y' : ℝ => F (p.1, y')) σ y) (hd : ∀ y, DifferentiableAt ℝ F (p.1, y))
    {w : E} {L : ℝ} (hL : HasDerivAt (fun t : ℝ => F (p.1 + t • w, p.2)) L 0) :
    Ito.itoGen F p w = L ∧ Ito.partialSnd F p = σ := by
  have hsnd : ∀ y, Ito.partialSnd F (p.1, y) = σ := fun y =>
    Ito.partialSnd_eq_of_hasDerivAt (hd y) (by simpa using hσ y)
  have hss : Ito.partialSndSnd F p = 0 :=
    Ito.partialSndSnd_eq_of_hasDerivAt hF (g := fun _ => σ) (Eventually.of_forall hsnd) (hasDerivAt_const _ _)
  have hfst : Ito.partialFst F p w = L := Ito.partialFst_eq_of_hasDerivAt (hF.differentiableAt (by norm_num)) hL
  refine ⟨?_, by simpa using hsnd p.2⟩
  rw [Ito.itoGen, hfst, hss]; ring

theorem hasDerivAt_affine_line (c L t₀ : ℝ) : HasDerivAt (fun t : ℝ => c + t * L) L t₀ := by
  simpa using ((hasDerivAt_id t₀).mul_const L).const_add c

end Affine

section CoordGen

variable (κ : ℝ)

theorem itoGen_zC (p : CE × ℝ) (w : CE) :
    Ito.itoGen (zC κ) p w = w.1 - w.2.2.1 ∧ Ito.partialSnd (zC κ) p = -Real.sqrt κ := by
  refine itoGen_affine (contDiff_zC κ).contDiffAt (fun y => ?_)
    (fun y => (contDiff_zC κ (n := 1)).differentiable (by norm_num) _) ?_
  · have e : (fun y' : ℝ => zC κ (p.1, y')) = fun y' => (p.1.1 - p.1.2.2.1) + y' * (-Real.sqrt κ) := by
      funext y'; simp only [zC]; ring
    rw [e]; exact hasDerivAt_affine_line _ _ _
  · have e : (fun t : ℝ => zC κ (p.1 + t • w, p.2)) = fun t => zC κ p + t * (w.1 - w.2.2.1) := by
      funext t; simp only [zC, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [e]; exact hasDerivAt_affine_line _ _ _

theorem itoGen_yC (p : CE × ℝ) (w : CE) :
    Ito.itoGen (yC κ) p w = w.2.2.1 - w.2.1 ∧ Ito.partialSnd (yC κ) p = Real.sqrt κ := by
  refine itoGen_affine (contDiff_yC κ).contDiffAt (fun y => ?_)
    (fun y => (contDiff_yC κ (n := 1)).differentiable (by norm_num) _) ?_
  · have e : (fun y' : ℝ => yC κ (p.1, y')) = fun y' => (p.1.2.2.1 - p.1.2.1) + y' * Real.sqrt κ := by
      funext y'; simp only [yC]; ring
    rw [e]; exact hasDerivAt_affine_line _ _ _
  · have e : (fun t : ℝ => yC κ (p.1 + t • w, p.2)) = fun t => yC κ p + t * (w.2.2.1 - w.2.1) := by
      funext t; simp only [yC, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [e]; exact hasDerivAt_affine_line _ _ _

theorem itoGen_sC (p : CE × ℝ) (w : CE) :
    Ito.itoGen (fun q => sC q / 3) p w = w.2.2.2 / 3 ∧ Ito.partialSnd (fun q => sC q / 3) p = 0 := by
  have hc : ContDiff ℝ 2 (fun q : CE × ℝ => sC q / 3) := (contDiff_sC (n := 2)).div_const 3
  refine itoGen_affine hc.contDiffAt (fun y => ?_) (fun y => (hc.differentiable (by norm_num)) _) ?_
  · simpa [sC] using hasDerivAt_const y (p.1.2.2.2 / 3)
  · have e : (fun t : ℝ => sC (p.1 + t • w, p.2) / 3) = fun t => sC p / 3 + t * (w.2.2.2 / 3) := by
      funext t; simp only [sC, Prod.snd_add, Prod.smul_snd, smul_eq_mul]; ring
    rw [e]; exact hasDerivAt_affine_line _ _ _

theorem contDiffAt_vC {n : WithTop ℕ∞} {p : CE × ℝ} (hD : dC p ≠ 0) : ContDiffAt ℝ n (vC κ) p :=
  (contDiff_yC κ).contDiffAt.div (contDiff_dC).contDiffAt hD

theorem itoGen_vC {p : CE × ℝ} (hD : dC p ≠ 0) (w : CE) :
    Ito.itoGen (vC κ) p w = ((w.2.2.1 - w.2.1) * dC p - yC κ p * (w.1 - w.2.1)) / dC p ^ 2 ∧
      Ito.partialSnd (vC κ) p = Real.sqrt κ / dC p := by
  have hDy : ∀ y : ℝ, dC (p.1, y) = dC p := fun y => rfl
  refine itoGen_affine (contDiffAt_vC κ hD) (fun y => ?_)
    (fun y => (contDiffAt_vC κ (n := 1) (by rw [hDy]; exact hD)).differentiableAt (by norm_num)) ?_
  · have e : (fun y' : ℝ => vC κ (p.1, y')) =
        fun y' => (p.1.2.2.1 - p.1.2.1) / dC p + y' * (Real.sqrt κ / dC p) := by
      funext y'; simp only [vC, yC, hDy]; field_simp; ring
    rw [e]; exact hasDerivAt_affine_line _ _ _
  · have e : (fun t : ℝ => vC κ (p.1 + t • w, p.2)) =
        fun t => (yC κ p + t * (w.2.2.1 - w.2.1)) / (dC p + t * (w.1 - w.2.1)) := by
      funext t
      simp only [vC, yC, dC, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      congr 1 <;> ring
    rw [e]
    have h := (hasDerivAt_affine_line (yC κ p) (w.2.2.1 - w.2.1) 0).div
      (hasDerivAt_affine_line (dC p) (w.1 - w.2.1) 0) (by simpa using hD)
    have hv : ((w.2.2.1 - w.2.1) * (dC p + 0 * (w.1 - w.2.1)) - (yC κ p + 0 * (w.2.2.1 - w.2.1)) *
        (w.1 - w.2.1)) / (dC p + 0 * (w.1 - w.2.1)) ^ 2 =
        ((w.2.2.1 - w.2.1) * dC p - yC κ p * (w.1 - w.2.1)) / dC p ^ 2 := by simp
    rw [hv] at h
    exact h

end CoordGen

/-! ### The Lyapunov observable -/

section Lyap

variable (κ : ℝ) {q q1 q2 : ℝ → ℝ}

theorem contDiffAt_lyapV {n : ℕ} (hq : ContDiff ℝ n q) {p : CE × ℝ} (hp : p ∈ clrRegion κ) :
    ContDiffAt ℝ n (lyapV κ q) p := by
  have hz := (contDiff_zC κ (n := n)).contDiffAt (x := p)
  have h1 : ContDiffAt ℝ n (fun r => Real.log (zC κ r)) p := hz.log hp.1.ne'
  have h2 : ContDiffAt ℝ n (fun r => sC r / 3) p := ((contDiff_sC (n := n)).div_const 3).contDiffAt
  have h3 : ContDiffAt ℝ n (fun r => q (vC κ r)) p :=
    hq.contDiffAt.comp p (contDiffAt_vC κ (dC_pos κ hp).ne')
  exact (h1.add h2).add h3

theorem contDiffAt_lyapObs {n : ℕ} (hq : ContDiff ℝ n q) (lam : ℝ) {p : CE × ℝ} (hp : p ∈ clrRegion κ) :
    ContDiffAt ℝ n (lyapObs κ lam q) p :=
  Real.contDiff_exp.contDiffAt.comp p ((contDiffAt_const.mul (contDiffAt_lyapV κ hq hp)).neg)

theorem contDiffOn_lyapObs (hq : ContDiff ℝ 3 q) (lam : ℝ) : ContDiffOn ℝ 3 (lyapObs κ lam q) (clrRegion κ) :=
  fun _ hp => (contDiffAt_lyapObs κ hq lam hp).contDiffWithinAt

theorem lyapObs_pos (lam : ℝ) (p : CE × ℝ) : 0 < lyapObs κ lam q p := Real.exp_pos _

/-- **The generator of `log Z + s/3 + q(v)`** and its `x`-derivative. -/
theorem itoGen_lyapV (hκ : 0 ≤ κ) (hq : ContDiff ℝ 2 q) (hq1 : ∀ v, HasDerivAt q (q1 v) v)
    (hq2 : ∀ v, HasDerivAt q1 (q2 v) v) {p : CE × ℝ} (hp : p ∈ clrRegion κ) (w : CE) :
    Ito.itoGen (lyapV κ q) p w =
        (w.1 - w.2.2.1) / zC κ p - κ / (2 * zC κ p ^ 2) + w.2.2.2 / 3 +
          q1 (vC κ p) * (((w.2.2.1 - w.2.1) * dC p - yC κ p * (w.1 - w.2.1)) / dC p ^ 2) +
            1 / 2 * q2 (vC κ p) * (Real.sqrt κ / dC p) ^ 2 ∧
      Ito.partialSnd (lyapV κ q) p = -Real.sqrt κ / zC κ p + q1 (vC κ p) * (Real.sqrt κ / dC p) := by
  have hz := (contDiff_zC κ (n := 2)).contDiffAt (x := p)
  have hzpos : 0 < zC κ p := hp.1
  have hD : dC p ≠ 0 := (dC_pos κ hp).ne'
  have h1 : ContDiffAt ℝ 2 (fun r => Real.log (zC κ r)) p := hz.log hzpos.ne'
  have h2 : ContDiffAt ℝ 2 (fun r => sC r / 3) p := ((contDiff_sC (n := 2)).div_const 3).contDiffAt
  have hv := contDiffAt_vC κ (n := 2) hD
  have h3 : ContDiffAt ℝ 2 (fun r => q (vC κ r)) p := hq.contDiffAt.comp p hv
  have e : lyapV κ q = fun r => (Real.log (zC κ r) + sC r / 3) + q (vC κ r) := rfl
  obtain ⟨gz, sz⟩ := itoGen_zC κ p w
  obtain ⟨gs, ss⟩ := itoGen_sC p w
  obtain ⟨gv, sv⟩ := itoGen_vC κ hD w
  have hlog := Zhan.itoGen_log hz hzpos w
  have hcomp := Zhan.itoGen_comp_of_hasDerivAt (φ := q) (φ' := q1) (d2 := q2 (vC κ p)) hq.contDiffAt hv
    (Eventually.of_forall hq1) (hq2 _) w
  have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ
  have hd1 := h1.differentiableAt (by norm_num)
  have hd2 := h2.differentiableAt (by norm_num)
  have hd3 := h3.differentiableAt (by norm_num)
  constructor
  · rw [e, Ito.itoGen_add (h1.add h2) h3, Ito.itoGen_add h1 h2, hlog, hcomp, gz, sz, gs, gv, sv]
    rw [neg_sq, hsq]
    field_simp
    ring
  · have hd12 : DifferentiableAt ℝ (fun r => Real.log (zC κ r) + sC r / 3) p := hd1.add hd2
    rw [e, Zhan.partialSnd_add hd12 hd3, Zhan.partialSnd_add hd1 hd2,
      Zhan.partialSnd_log (hz.differentiableAt (by norm_num)) hzpos,
      Zhan.partialSnd_comp_of_hasDerivAt (hv.differentiableAt (by norm_num)) (hq1 _), sz, ss, sv]
    field_simp
    ring

/-- The generator of `Φ = exp(−λ V)`: `Φ (−λ itoGen V + (λ²/2) (∂_x V)²)`. -/
theorem itoGen_lyapObs_eq (hq : ContDiff ℝ 2 q) (lam : ℝ) {p : CE × ℝ} (hp : p ∈ clrRegion κ) (w : CE) :
    Ito.itoGen (lyapObs κ lam q) p w = lyapObs κ lam q p *
      (-lam * Ito.itoGen (lyapV κ q) p w + lam ^ 2 / 2 * Ito.partialSnd (lyapV κ q) p ^ 2) := by
  have hV := contDiffAt_lyapV κ hq hp
  have hφ : ContDiff ℝ 2 (fun x : ℝ => Real.exp (-(lam * x))) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id).neg
  have h1 : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Real.exp (-(lam * x))) (-lam * Real.exp (-(lam * x))) x := by
    intro x
    have := (((hasDerivAt_id x).const_mul lam).neg).exp
    simpa [mul_comm] using this
  have h2 : HasDerivAt (fun x : ℝ => -lam * Real.exp (-(lam * x))) (lam ^ 2 * Real.exp (-(lam * lyapV κ q p)))
      (lyapV κ q p) := by
    have := (h1 (lyapV κ q p)).const_mul (-lam)
    rw [show lam ^ 2 * Real.exp (-(lam * lyapV κ q p)) = -lam * (-lam * Real.exp (-(lam * lyapV κ q p))) by
      ring]
    exact this
  have h := Zhan.itoGen_comp_of_hasDerivAt (φ := fun x : ℝ => Real.exp (-(lam * x)))
    (φ' := fun x => -lam * Real.exp (-(lam * x))) (d2 := lam ^ 2 * Real.exp (-(lam * lyapV κ q p)))
    hφ.contDiffAt hV (Eventually.of_forall h1) h2 w
  have e : lyapObs κ lam q = fun r => Real.exp (-(lam * lyapV κ q r)) := rfl
  rw [e, h]
  ring

/-- Along the state velocity the generator of `log Z + s/3 + q(v)` is `lyapDrift`. -/
theorem itoGen_lyapV_field (hκ : 0 ≤ κ) {ρL ρR : ℝ} (hq : ContDiff ℝ 2 q) (hq1 : ∀ v, HasDerivAt q (q1 v) v)
    (hq2 : ∀ v, HasDerivAt q1 (q2 v) v) {p : CE × ℝ} (hp : p ∈ clrRegion κ) :
    Ito.itoGen (lyapV κ q) p (clrField κ ρL ρR p) = lyapDrift κ ρL ρR q1 q2 (zC κ p) (yC κ p) ∧
      Ito.partialSnd (lyapV κ q) p ^ 2 = κ * (q1 (vC κ p) / dC p - 1 / zC κ p) ^ 2 := by
  obtain ⟨hg, hs⟩ := itoGen_lyapV κ hκ hq hq1 hq2 hp (clrField κ ρL ρR p)
  have hZ : 0 < zC κ p := hp.1
  have hY : 0 < yC κ p := hp.2
  have hDe : dC p = yC κ p + zC κ p := (yC_add_zC κ p).symm
  have hvC : yC κ p / (yC κ p + zC κ p) = vC κ p := by rw [vC, hDe]
  have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ
  constructor
  · rw [hg, lyapDrift, ← hvC]
    simp only [clrField]
    rw [hDe, div_pow, hsq]
    generalize q1 (yC κ p / (yC κ p + zC κ p)) = A1
    generalize q2 (yC κ p / (yC κ p + zC κ p)) = A2
    field_simp
    ring
  · rw [hs]
    have : (-Real.sqrt κ / zC κ p + q1 (vC κ p) * (Real.sqrt κ / dC p)) =
        Real.sqrt κ * (q1 (vC κ p) / dC p - 1 / zC κ p) := by ring
    rw [this, mul_pow, hsq]

/-- **The drift of the Lyapunov observable is nonpositive** on `{Z > 0, Y > 0}` along the state velocity, given the
inequality of `exists_lyapunov`. -/
theorem itoGen_lyapObs_nonpos (hκ : 0 ≤ κ) {ρL ρR lam : ℝ} (hlam : 0 ≤ lam) (hq : ContDiff ℝ 2 q)
    (hq1 : ∀ v, HasDerivAt q (q1 v) v) (hq2 : ∀ v, HasDerivAt q1 (q2 v) v)
    (hineq : ∀ Z Y : ℝ, 0 < Z → 0 < Y →
      lam * (κ / 2) * (q1 (Y / (Y + Z)) / (Y + Z) - 1 / Z) ^ 2 ≤ lyapDrift κ ρL ρR q1 q2 Z Y)
    {p : CE × ℝ} (hp : p ∈ clrRegion κ) :
    Ito.itoGen (lyapObs κ lam q) p (clrField κ ρL ρR p) ≤ 0 := by
  obtain ⟨hg, hs⟩ := itoGen_lyapV_field κ hκ (ρL := ρL) (ρR := ρR) hq hq1 hq2 hp
  rw [itoGen_lyapObs_eq κ hq lam hp, hg, hs]
  have hDe : dC p = yC κ p + zC κ p := (yC_add_zC κ p).symm
  have hvC : yC κ p / (yC κ p + zC κ p) = vC κ p := by rw [vC, hDe]
  have hI := hineq (zC κ p) (yC κ p) hp.1 hp.2
  rw [hvC, ← hDe] at hI
  have hpos := lyapObs_pos κ lam p (q := q)
  refine mul_nonpos_of_nonneg_of_nonpos hpos.le ?_
  have e : lam ^ 2 / 2 * (κ * (q1 (vC κ p) / dC p - 1 / zC κ p) ^ 2) =
      lam * (lam * (κ / 2) * (q1 (vC κ p) / dC p - 1 / zC κ p) ^ 2) := by ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hI hlam]

end Lyap

end InteractingSLE.ZhanGT4.A5Clear
