/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S8Abel
import InteractingSLE.Spec.Ito.Observable

/-!
# Lemma GB5: the Lyapunov observable and its generator bound

Packet PROVE-T14-GB. Specification supplement §8.5, **Lemma GB5** (general protected-tail estimate,
`source/spec/p481-528.md` L874–L922, pp. 516–518). For a right force word with `0 ≤ V₁(0) ≤ ⋯ ≤ V_N(0)`,
`S_i = Σ_{ℓ ≤ i} ρ_ℓ`, `S_i > −2` for `i < j` and `S_i ≥ c = k/2 − 2` for `i ≥ j`, `V₁(0) < V_j(0)`, the gap
`X_j = V_j − W` never vanishes. The source's proof runs in the random clock `du = dt/X_j²` and splits into a finite
and an infinite clock. Here a single **Lyapunov function** of `x = X_j` and `d = V_j − V₁` replaces both cases:

  `F(x, d) = −log x + α Z + λ Z^p`,   `Z = d/x = 1 − U₁`,

with `α = 4/ε` (`ε ≤ min_{i<j} (S_i + 2)`), `p = 1/(1 + k/2)` and `λ = (4 + α|c|)/(p (2 − pk/2))`. In the source's
notation (`A`, `E`, `H` of `S8Abel.lean`) its drift in the new clock is

  `−(E + A) + α Z (c − A − H) + p λ Z^p (pk/2 − 2 − A − H)`

(the drifts of `−log X_j`, of `−αU₁` and of `λZ^p`, from the source's identities for `d log X_j`, `dU₁`,
`d log Z`), and it is `≤ 0` by `H ≥ ε(1/U₁ − 1)`, `A ≥ 0` and `Z^p ≥ Z` (`lyapDrift_nonpos`). Since `F → +∞`
as `x → 0` while `Z`, `Z^p` stay in `[0, 1]`, optional stopping excludes every finite vanishing of `X_j` (files
`GB5Loc.lean`, `GB5.lean`); no time change, strong law or limsup argument is needed.

The coordinates of the Itô formula are `Λ = (X_j + √k B, d)` with Brownian coordinate `b = B`, so `x = Λ₁ − √k b`
(`lyapObs`). This file proves the smoothness of `lyapObs` on `lyapRegion = {x > 0, d > 0}`, its Itô generator
(`itoGen_lyapObs`), and the pathwise generator bound with an extra opposite-side drift `β` in `X_j`:
`itoGen ≤ (1 + α + pλ) |β| / x` (`itoGen_lyapObs_le`).

## Main results

* `lyapDrift_nonpos`: the drift inequality in the new clock;
* `contDiffOn_lyapObs`, `itoGen_lyapObs`: smoothness and generator of the observable;
* `itoGen_lyapObs_le`: the generator bound along a path, in terms of `E`, `A`, `H`;
* `log_le_lyapF`, `lyapF_le`: `−log x ≤ F ≤ −log x + α + λ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace InteractingSLE

namespace Supp8

namespace GB5

/-! ### Constants -/

/-- `α = 4/ε`. -/
def alphaC (ε : ℝ) : ℝ := 4 / ε

/-- The exponent `p = 1/(1 + k/2)`: `0 < p < 1` and `p k/2 < 1`. -/
def expoC (k : ℝ) : ℝ := 1 / (1 + k / 2)

/-- `μ = 4 + α|c|`, `c = k/2 − 2`. -/
def muC (k ε : ℝ) : ℝ := 4 + alphaC ε * |k / 2 - 2|

/-- `λ = μ / (p (2 − p k/2))`, so that `p λ (2 − p k/2) = μ`. -/
def lamC (k ε : ℝ) : ℝ := muC k ε / (expoC k * (2 - expoC k * k / 2))

variable {k ε : ℝ}

theorem expoC_pos (hk : 0 < k) : 0 < expoC k := by unfold expoC; positivity

theorem expoC_le_one (hk : 0 < k) : expoC k ≤ 1 := by
  unfold expoC
  rw [div_le_one (by positivity)]
  linarith

theorem expoC_mul_lt (hk : 0 < k) : expoC k * k / 2 < 1 := by
  unfold expoC
  rw [div_mul_eq_mul_div, one_mul, div_div, div_lt_one (by positivity)]
  linarith

theorem alphaC_pos (hε : 0 < ε) : 0 < alphaC ε := by unfold alphaC; positivity

theorem muC_pos (hε : 0 < ε) : 0 < muC k ε := by
  unfold muC
  have := alphaC_pos hε
  positivity

theorem lamC_pos (hk : 0 < k) (hε : 0 < ε) : 0 < lamC k ε := by
  unfold lamC
  have h1 := expoC_pos hk
  have h2 := expoC_mul_lt hk
  have h3 := muC_pos (k := k) hε
  exact div_pos h3 (mul_pos h1 (by linarith))

theorem expoC_mul_lamC (hk : 0 < k) :
    expoC k * lamC k ε * (2 - expoC k * k / 2) = muC k ε := by
  unfold lamC
  have h1 := expoC_pos hk
  have h2 := expoC_mul_lt hk
  have h3 : expoC k * (2 - expoC k * k / 2) ≠ 0 := (mul_pos h1 (by linarith)).ne'
  rw [show expoC k * (muC k ε / (expoC k * (2 - expoC k * k / 2))) * (2 - expoC k * k / 2) =
      muC k ε / (expoC k * (2 - expoC k * k / 2)) * (expoC k * (2 - expoC k * k / 2)) by ring,
    div_mul_cancel₀ _ h3]

/-! ### The drift inequality in the new clock -/

/-- **The drift of `F` in the new clock is nonpositive.** With `0 < Z < 1`, `W = Z/(1 − Z) = 1/U₁ − 1`,
`H = E + 2W ≥ ε W` (`gb5_H_ge`), `A ≥ 0` (`gb5_A_bounds`) and `Z ≤ Y ≤ 1` (`Y = Z^p`):
`−(E + A) + αZ(c − A − H) + pλY(pk/2 − 2 − A − H) ≤ 0`. -/
theorem lyapDrift_nonpos (hk : 0 < k) (hε : 0 < ε) {Z W Y E A : ℝ} (hZ0 : 0 < Z) (hZ1 : Z < 1)
    (hW : W * (1 - Z) = Z) (hY : Z ≤ Y) (hA : 0 ≤ A) (hH : ε * W ≤ E + 2 * W) :
    -(E + A) + alphaC ε * Z * (k / 2 - 2 - A - (E + 2 * W)) +
      expoC k * lamC k ε * Y * (expoC k * k / 2 - 2 - A - (E + 2 * W)) ≤ 0 := by
  set α := alphaC ε with hα
  set pl := expoC k * lamC k ε with hpl
  have hpl0 : 0 ≤ pl := (mul_pos (expoC_pos hk) (lamC_pos hk hε)).le
  have hα0 : 0 < α := alphaC_pos hε
  have hεα : ε * α = 4 := by rw [hα]; unfold alphaC; field_simp
  have hmu : pl * (2 - expoC k * k / 2) = 4 + α * |k / 2 - 2| := by
    rw [hpl, expoC_mul_lamC hk]; rfl
  have hW0 : 0 ≤ W := by
    have h1 : 0 < 1 - Z := by linarith
    nlinarith
  set H := E + 2 * W with hHdef
  have hH0 : 0 ≤ H := le_trans (mul_nonneg hε.le hW0) hH
  have hY0 : 0 ≤ Y := hZ0.le.trans hY
  -- the `λ Z^p` term: `pλY(pk/2 − 2 − A − H) ≤ −μ Y ≤ −μ Z`
  have h1 : pl * Y * (expoC k * k / 2 - 2 - A - H) ≤ -((4 + α * |k / 2 - 2|) * Z) := by
    have e : pl * Y * (expoC k * k / 2 - 2 - A - H) =
        -(pl * (2 - expoC k * k / 2)) * Y - pl * Y * (A + H) := by ring
    rw [e, hmu]
    have : 0 ≤ pl * Y * (A + H) := mul_nonneg (mul_nonneg hpl0 hY0) (add_nonneg hA hH0)
    have hμ : 0 ≤ 4 + α * |k / 2 - 2| := by positivity
    nlinarith
  -- the `α Z` term
  have h2 : α * Z * (k / 2 - 2 - A - H) ≤ α * Z * |k / 2 - 2| - α * Z * H := by
    have : α * Z * A ≥ 0 := mul_nonneg (mul_nonneg hα0.le hZ0.le) hA
    have hc : k / 2 - 2 ≤ |k / 2 - 2| := le_abs_self _
    nlinarith [mul_le_mul_of_nonneg_left hc (mul_nonneg hα0.le hZ0.le)]
  -- `−(E + A) ≤ −H + 2W`
  have h3 : -(E + A) ≤ -H + 2 * W := by rw [hHdef]; linarith
  -- combine: `≤ −(1 + αZ) H + 2W − 4Z ≤ W(2 − ε − 4Z) − 4Z`
  have h4 : -(1 + α * Z) * H ≤ -(1 + α * Z) * (ε * W) :=
    by nlinarith [mul_le_mul_of_nonneg_left hH (by positivity : (0 : ℝ) ≤ 1 + α * Z)]
  have h5 : -(1 + α * Z) * (ε * W) = -(ε * W) - 4 * Z * W := by
    have : α * Z * (ε * W) = (ε * α) * Z * W := by ring
    rw [neg_mul, add_mul, one_mul, this, hεα]; ring
  have hsum : -(E + A) + α * Z * (k / 2 - 2 - A - H) + pl * Y * (expoC k * k / 2 - 2 - A - H) ≤
      W * (2 - ε - 4 * Z) - 4 * Z := by nlinarith
  rcases le_or_gt (1 / 2) Z with hZh | hZh
  · have : W * (2 - ε - 4 * Z) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hW0 (by linarith)
    linarith
  · have hW2 : W ≤ 2 * Z := by nlinarith
    have : W * (2 - ε - 4 * Z) ≤ 2 * W := by nlinarith
    linarith

/-! ### The Lyapunov function of `(x, d)` -/

/-- `Z^p = exp(p (log d − log x))` for `Z = d/x`. -/
def powZ (k x d : ℝ) : ℝ := Real.exp (expoC k * (Real.log d - Real.log x))

/-- The Lyapunov function `F(x, d) = −log x + α (d/x) + λ Z^p`. -/
def lyapF (k ε x d : ℝ) : ℝ := -Real.log x + alphaC ε * (d / x) + lamC k ε * powZ k x d

/-- `∂_x F`. -/
def lyapFx (k ε x d : ℝ) : ℝ :=
  -(1 / x) - alphaC ε * (d / x ^ 2) - expoC k * lamC k ε * powZ k x d / x

/-- `∂_d F`. -/
def lyapFd (k ε x d : ℝ) : ℝ := alphaC ε / x + expoC k * lamC k ε * powZ k x d / d

/-- `∂²_x F`. -/
def lyapFxx (k ε x d : ℝ) : ℝ :=
  1 / x ^ 2 + 2 * alphaC ε * d / x ^ 3 + expoC k * (expoC k + 1) * lamC k ε * powZ k x d / x ^ 2

theorem hasDerivAt_powZ {X D : ℝ → ℝ} {X' D' t : ℝ} (hX : HasDerivAt X X' t) (hD : HasDerivAt D D' t)
    (hX0 : 0 < X t) (hD0 : 0 < D t) :
    HasDerivAt (fun s => powZ k (X s) (D s))
      (powZ k (X t) (D t) * (expoC k * (D' / D t - X' / X t))) t := by
  unfold powZ
  exact (((hD.log hD0.ne').sub (hX.log hX0.ne')).const_mul (expoC k)).exp

theorem hasDerivAt_lyapF {X D : ℝ → ℝ} {X' D' t : ℝ} (hX : HasDerivAt X X' t)
    (hD : HasDerivAt D D' t) (hX0 : 0 < X t) (hD0 : 0 < D t) :
    HasDerivAt (fun s => lyapF k ε (X s) (D s))
      (lyapFx k ε (X t) (D t) * X' + lyapFd k ε (X t) (D t) * D') t := by
  have h1 := (hX.log hX0.ne').neg
  have h2 := (hD.div hX hX0.ne').const_mul (alphaC ε)
  have h3 := (hasDerivAt_powZ (k := k) hX hD hX0 hD0).const_mul (lamC k ε)
  refine ((h1.add h2).add h3).congr_deriv ?_
  unfold lyapFx lyapFd
  field_simp
  ring

theorem hasDerivAt_lyapFx {x d : ℝ} (hx : 0 < x) (hd : 0 < d) :
    HasDerivAt (fun y => lyapFx k ε y d) (lyapFxx k ε x d) x := by
  have hP := hasDerivAt_powZ (k := k) (hasDerivAt_id x) (hasDerivAt_const x d) hx hd
  simp only [id] at hP
  have h1 := ((hasDerivAt_id x).inv hx.ne')
  have h2 := ((hasDerivAt_id x).pow 2).inv (pow_ne_zero 2 hx.ne')
  have h3 := (hP.div (hasDerivAt_id x) hx.ne').const_mul (expoC k * lamC k ε)
  have e : (fun y => lyapFx k ε y d) = fun y => -(id y)⁻¹ - alphaC ε * d * ((id y) ^ 2)⁻¹ -
      expoC k * lamC k ε * (powZ k y d / id y) := by
    funext y; unfold lyapFx; simp only [id]; ring
  rw [e]
  refine ((h1.neg.sub (h2.const_mul (alphaC ε * d))).sub h3).congr_deriv ?_
  unfold lyapFxx
  simp only [Pi.pow_apply, id]
  field_simp
  ring

/-! ### The observable on the Itô coordinates -/

/-- `x = Λ₁ − √k b` on the coordinates `((Λ₁, d), b)`. -/
def lyapX (k : ℝ) (q : (ℝ × ℝ) × ℝ) : ℝ := q.1.1 - Real.sqrt k * q.2

/-- The Lyapunov observable `F(Λ₁ − √k b, d)`. -/
def lyapObs (k ε : ℝ) (q : (ℝ × ℝ) × ℝ) : ℝ := lyapF k ε (lyapX k q) q.1.2

/-- Its region of smoothness `{x > 0, d > 0}`. -/
def lyapRegion (k : ℝ) : Set ((ℝ × ℝ) × ℝ) := {q | 0 < lyapX k q ∧ 0 < q.1.2}

theorem continuous_lyapX : Continuous (lyapX k) := by unfold lyapX; fun_prop

theorem isOpen_lyapRegion : IsOpen (lyapRegion k) :=
  (isOpen_lt continuous_const continuous_lyapX).inter
    (isOpen_lt continuous_const (continuous_snd.comp continuous_fst))

theorem contDiffOn_lyapObs : ContDiffOn ℝ 3 (lyapObs k ε) (lyapRegion k) := by
  have hX : ContDiff ℝ 3 (lyapX k) := by unfold lyapX; fun_prop
  have hd : ContDiff ℝ 3 (fun q : (ℝ × ℝ) × ℝ => q.1.2) := by fun_prop
  have hlx : ContDiffOn ℝ 3 (fun q => Real.log (lyapX k q)) (lyapRegion k) :=
    hX.contDiffOn.log fun q hq => hq.1.ne'
  have hld : ContDiffOn ℝ 3 (fun q : (ℝ × ℝ) × ℝ => Real.log q.1.2) (lyapRegion k) :=
    hd.contDiffOn.log fun q hq => hq.2.ne'
  have hdiv : ContDiffOn ℝ 3 (fun q => q.1.2 / lyapX k q) (lyapRegion k) :=
    hd.contDiffOn.div hX.contDiffOn fun q hq => hq.1.ne'
  have hpow : ContDiffOn ℝ 3 (fun q => powZ k (lyapX k q) q.1.2) (lyapRegion k) :=
    Real.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul (hld.sub hlx))
  exact (hlx.neg.add (contDiffOn_const.mul hdiv)).add (contDiffOn_const.mul hpow)

theorem contDiffAt_lyapObs {q : (ℝ × ℝ) × ℝ} (hq : q ∈ lyapRegion k) :
    ContDiffAt ℝ 3 (lyapObs k ε) q :=
  contDiffOn_lyapObs.contDiffAt (isOpen_lyapRegion.mem_nhds hq)

/-- **The Itô generator of the observable**:
`itoGen F (q) (v₁, v₂) = ∂_x F v₁ + ∂_d F v₂ + ½ k ∂²_x F` at `x = Λ₁ − √k b`. -/
theorem itoGen_lyapObs (hk : 0 ≤ k) {q : (ℝ × ℝ) × ℝ} (hq : q ∈ lyapRegion k) (v : ℝ × ℝ) :
    Ito.itoGen (lyapObs k ε) q v = lyapFx k ε (lyapX k q) q.1.2 * v.1 +
      lyapFd k ε (lyapX k q) q.1.2 * v.2 + 1 / 2 * (k * lyapFxx k ε (lyapX k q) q.1.2) := by
  have hdiff : ∀ q' ∈ lyapRegion k, DifferentiableAt ℝ (lyapObs k ε) q' := fun q' hq' =>
    (contDiffAt_lyapObs hq').differentiableAt (by norm_num)
  -- the first partial, along the line `t ↦ (q.1 + t v, q.2)`
  have hfst : Ito.partialFst (lyapObs k ε) q v =
      lyapFx k ε (lyapX k q) q.1.2 * v.1 + lyapFd k ε (lyapX k q) q.1.2 * v.2 := by
    refine Ito.partialFst_eq_of_hasDerivAt (hdiff q hq) ?_
    have hX : HasDerivAt (fun t : ℝ => lyapX k q + t * v.1) v.1 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v.1).const_add (lyapX k q)
    have hD : HasDerivAt (fun t : ℝ => q.1.2 + t * v.2) v.2 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v.2).const_add q.1.2
    have h := hasDerivAt_lyapF (k := k) (ε := ε) hX hD (by simpa using hq.1) (by simpa using hq.2)
    simp only [zero_mul, add_zero] at h
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp only [lyapObs, lyapX, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring_nf
  -- the second partial near `q.2`
  have hev : ∀ᶠ y in 𝓝 q.2, (q.1, y) ∈ lyapRegion k :=
    ((continuous_const.prodMk continuous_id).continuousAt (x := q.2)).preimage_mem_nhds
      (by simpa using isOpen_lyapRegion.mem_nhds hq)
  have hsnd : ∀ y, (q.1, y) ∈ lyapRegion k → Ito.partialSnd (lyapObs k ε) (q.1, y) =
      lyapFx k ε (q.1.1 - Real.sqrt k * y) q.1.2 * (-Real.sqrt k) := by
    intro y hy
    refine Ito.partialSnd_eq_of_hasDerivAt (hdiff _ hy) ?_
    have hX : HasDerivAt (fun y' : ℝ => q.1.1 - Real.sqrt k * y') (-Real.sqrt k) y := by
      simpa using ((hasDerivAt_id y).const_mul (Real.sqrt k)).const_sub q.1.1
    have h := hasDerivAt_lyapF (k := k) (ε := ε) hX (hasDerivAt_const y q.1.2) hy.1 hy.2
    simp only [mul_zero, add_zero] at h
    exact h
  have hsndsnd : Ito.partialSndSnd (lyapObs k ε) q = k * lyapFxx k ε (lyapX k q) q.1.2 := by
    refine Ito.partialSndSnd_eq_of_hasDerivAt ((contDiffAt_lyapObs hq).of_le (by norm_num))
      (hev.mono fun y hy => hsnd y hy) ?_
    have hX : HasDerivAt (fun y' : ℝ => q.1.1 - Real.sqrt k * y') (-Real.sqrt k) q.2 := by
      simpa using ((hasDerivAt_id q.2).const_mul (Real.sqrt k)).const_sub q.1.1
    have h := ((hasDerivAt_lyapFx (k := k) (ε := ε) hq.1 hq.2).comp q.2 hX).mul_const (-Real.sqrt k)
    refine h.congr_deriv ?_
    rw [mul_assoc, neg_mul_neg, Real.mul_self_sqrt hk, mul_comm]
  unfold Ito.itoGen
  rw [hfst, hsndsnd]

/-! ### The generator bound along a path -/

theorem powZ_ge {x d : ℝ} (hk : 0 < k) (hx : 0 < x) (hd : 0 < d) (hdx : d ≤ x) :
    d / x ≤ powZ k x d ∧ powZ k x d ≤ 1 := by
  have hZ : 0 < d / x := div_pos hd hx
  have hl : Real.log d - Real.log x = Real.log (d / x) := (Real.log_div hd.ne' hx.ne').symm
  have hlog : Real.log (d / x) ≤ 0 := Real.log_nonpos hZ.le ((div_le_one hx).2 hdx)
  have hp := expoC_le_one hk
  have hp0 := expoC_pos hk
  unfold powZ
  rw [hl]
  constructor
  · calc d / x = Real.exp (Real.log (d / x)) := (Real.exp_log hZ).symm
      _ ≤ Real.exp (expoC k * Real.log (d / x)) := Real.exp_le_exp.2 (by nlinarith)
  · exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos hp0.le hlog)

/-- **The generator bound.** At a point of the region with `d < x`, for the density
`v = ((2 + Q)/x + β, 2/x − 2/(x − d))` of the coordinates (`Q = x Σ_i ρ_i/X_i` the right force sum, `β` the drift of
`X_j` from the opposite side, `x − d = X₁`), if `2 + Q − k/2 = E + A` (`gb5_drift_logX`), `A ≥ 0`
(`gb5_A_bounds`) and `H = E + 2(1/U₁ − 1) ≥ ε(1/U₁ − 1)` (`gb5_H_ge`, `1/U₁ = x/(x − d)`), then
`itoGen F ≤ (1 + α + pλ) |β| / x`. -/
theorem itoGen_lyapObs_le (hk : 0 < k) (hε : 0 < ε) {q : (ℝ × ℝ) × ℝ} (hq : q ∈ lyapRegion k)
    (hdx : q.1.2 < lyapX k q) {Q β E A : ℝ} (hQ : 2 + Q - k / 2 = E + A) (hA : 0 ≤ A)
    (hH : ε * (lyapX k q / (lyapX k q - q.1.2) - 1) ≤
      E + 2 * (lyapX k q / (lyapX k q - q.1.2) - 1)) :
    Ito.itoGen (lyapObs k ε) q ((2 + Q) / lyapX k q + β, 2 / lyapX k q - 2 / (lyapX k q - q.1.2)) ≤
      (1 + alphaC ε + expoC k * lamC k ε) * |β| / lyapX k q := by
  rw [itoGen_lyapObs hk.le hq]
  have hx : 0 < lyapX k q := hq.1
  have hd : 0 < q.1.2 := hq.2
  set x := lyapX k q with hxdef
  set d := q.1.2 with hddef
  have hxd : 0 < x - d := by linarith
  obtain ⟨hYZ, hY1⟩ := powZ_ge (k := k) hk hx hd hdx.le
  set Y := powZ k x d with hYdef
  have hZ0 : 0 < d / x := div_pos hd hx
  have hZ1 : d / x < 1 := (div_lt_one hx).2 hdx
  have hWZ : (x / (x - d) - 1) * (1 - d / x) = d / x := by field_simp; ring
  have hdrift := lyapDrift_nonpos (k := k) hk hε hZ0 hZ1 hWZ hYZ hA hH
  set α := alphaC ε with hα
  set pl := expoC k * lamC k ε with hpl
  have hE : E = 2 + Q - k / 2 - A := by linarith
  have key : lyapFx k ε x d * ((2 + Q) / x + β) + lyapFd k ε x d * (2 / x - 2 / (x - d)) +
      1 / 2 * (k * lyapFxx k ε x d) =
      (-(E + A) + α * (d / x) * (k / 2 - 2 - A - (E + 2 * (x / (x - d) - 1))) +
        pl * Y * (expoC k * k / 2 - 2 - A - (E + 2 * (x / (x - d) - 1)))) / x ^ 2 -
      β * (1 + α * (d / x) + pl * Y) / x := by
    rw [hE]
    unfold lyapFx lyapFd lyapFxx
    rw [← hα, ← hYdef]
    have e : expoC k * (expoC k + 1) * lamC k ε = pl * (expoC k + 1) := by rw [hpl]; ring
    rw [e]
    field_simp
    ring
  rw [key]
  have h1 : (-(E + A) + α * (d / x) * (k / 2 - 2 - A - (E + 2 * (x / (x - d) - 1))) +
      pl * Y * (expoC k * k / 2 - 2 - A - (E + 2 * (x / (x - d) - 1)))) / x ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hdrift (sq_nonneg x)
  have hα0 : 0 < α := alphaC_pos hε
  have hpl0 : 0 ≤ pl := (mul_pos (expoC_pos hk) (lamC_pos hk hε)).le
  have h2 : -(β * (1 + α * (d / x) + pl * Y)) ≤ (1 + α + pl) * |β| := by
    have hb : 0 ≤ 1 + α * (d / x) + pl * Y := by
      have : 0 ≤ Y := hZ0.le.trans hYZ
      positivity
    have hle : 1 + α * (d / x) + pl * Y ≤ 1 + α + pl := by
      have h1' : α * (d / x) ≤ α := by nlinarith
      have h2' : pl * Y ≤ pl := by nlinarith
      linarith
    calc -(β * (1 + α * (d / x) + pl * Y)) ≤ |β| * (1 + α * (d / x) + pl * Y) := by
          rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_le_abs β) hb
      _ ≤ |β| * (1 + α + pl) := mul_le_mul_of_nonneg_left hle (abs_nonneg β)
      _ = (1 + α + pl) * |β| := mul_comm _ _
  have h3 : -(β * (1 + α * (d / x) + pl * Y)) / x ≤ (1 + α + pl) * |β| / x :=
    div_le_div_of_nonneg_right h2 hx.le
  rw [neg_div] at h3
  linarith

/-! ### Bounds on the observable -/

theorem lyapF_ge {x d : ℝ} (hk : 0 < k) (hε : 0 < ε) (hx : 0 < x) (hd : 0 < d) :
    -Real.log x ≤ lyapF k ε x d := by
  unfold lyapF
  have h1 : 0 ≤ alphaC ε * (d / x) := mul_nonneg (alphaC_pos hε).le (div_pos hd hx).le
  have h2 : 0 ≤ lamC k ε * powZ k x d := mul_nonneg (lamC_pos hk hε).le (Real.exp_pos _).le
  linarith

theorem lyapF_le {x d : ℝ} (hk : 0 < k) (hε : 0 < ε) (hx : 0 < x) (hd : 0 < d) (hdx : d ≤ x) :
    lyapF k ε x d ≤ -Real.log x + alphaC ε + lamC k ε := by
  unfold lyapF
  have h1 : alphaC ε * (d / x) ≤ alphaC ε :=
    mul_le_of_le_one_right (alphaC_pos hε).le ((div_le_one hx).2 hdx)
  have h2 : lamC k ε * powZ k x d ≤ lamC k ε :=
    mul_le_of_le_one_right (lamC_pos hk hε).le (powZ_ge hk hx hd hdx).2
  linarith

end GB5

end Supp8

end InteractingSLE
