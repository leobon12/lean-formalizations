/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtASetup
import InteractingSLE.Spec.Ito.Mean
import QuantumZipper.Proofs.GFF.K3.GreenH

/-!
# The local comparison of Aux. lemma 55: the distant-force function `q`, the cutoff `f = ζq` and its source `v`

Packet PROVE-LOCEXT-A, step 2 (`planning/handoffs/PROVE-AUX52-55.md`, item 2). Source: Aux. lemma 55, proof
(`source/spec/p241-288.md` L132–L160, pp. 247–248):

"Let `m` be the actual initial mean, let `m_0` be the mean with only the seed weights, and put `q = m − m_0`. The
finite boundary data imply that `q` is bounded and harmonic in `ℍ`, has continuous zero values on `(−8r, 8r)`, and
extends oddly and harmonically across that interval. Choose a real smooth cutoff `ζ` equal to one on a neighborhood
of `B̄(0, 2r)`, supported in `B(0, 4r)`, and set `f = ζ q ∈ H¹₀(ℍ)` (HL1). […] the source `v = −(2π)⁻¹ Δ f` (HL2) is
supported outside a fixed neighborhood of every `K_{t∧S}`. […] Dirichlet Green inversion gives `G_ℍ v = f`."

Here the cutoff is radial, equal to one on `B̄(0, 6r)` and supported in `B̄(0, 7r)` (a larger buffer than the source's
`2r`/`4r`; Aux. 55 only needs `f = q` on the buffered neighbourhood `U = B(0, 2r)` and a source away from the hulls).

## Main definitions

* `seedWtL`, `seedWtR`, `distSetL`, `distSetR`: the seed weights and the distant marks `J`;
* `distantHarm κ xL xR ρL ρR aL aR w`: **(HL5)**, `κ^{-1/2}(π ∑_{J,right} ρ_j − ∑_J ρ_j arg(w − a_j))`;
  `meanHarmonic_eq_add_distantHarm`: the canonical mean of (2.5) is the seed mean plus `distantHarm`;
* `qExt`: the odd harmonic extension of `q = distantHarm (x)` across `(−8r, 8r)`,
  `−κ^{-1/2}(∑_{J,left} ρ_j arg(z − x_j) + ∑_{J,right} ρ_j arg(x_j − z))`;
* `cutoffFn R₁ R₂`: a radial smooth cutoff, `1` on `B̄(0, R₁)`, `0` off `B(0, R₂)`;
* `fCut`: **(HL1)** `f = ζ q`; `vSrc`: **(HL2)** `v = −(2π)⁻¹ Δ f` restricted to `ℍ`.

## Main results

* `qExt_eq_distantHarm`: `qExt = q` on `ℍ`; `harmonicAt_qExt`, `qExt_conj`: harmonic and odd on `B(0, 8r)`;
* `fCut` is smooth with compact support, odd, `= q` on `B̄(0, 6r)`; `vSrc` is continuous with compact support in
  `{6r ≤ |z| ≤ 7r} ∩ ℍ̄`;
* `integral_greenH_mul_vSrc`: **Green inversion** `∫ G_ℍ(w, z) v(z) dz = f(w)` for `w ∈ ℍ̄`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate Laplacian

namespace InteractingSLE

namespace LocalExt

/-! ### Seed weights and distant marks -/

section Weights

variable {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)

/-- The seed weights on the left: `ρ` on the left marks started at `0`, `0` on the distant ones. -/
def seedWtL : Fin nL → ℝ := fun i => if xL i = 0 then ρL i else 0

/-- The seed weights on the right. -/
def seedWtR : Fin nR → ℝ := fun i => if xR i = 0 then ρR i else 0

/-- The distant left marks `J ∩ left`. -/
def distSetL : Finset (Fin nL) := Finset.univ.filter fun i => xL i ≠ 0

/-- The distant right marks `J ∩ right`. -/
def distSetR : Finset (Fin nR) := Finset.univ.filter fun i => xR i ≠ 0

variable {xL xR}

theorem sum_mul_eq_seed_add_dist_L (X : Fin nL → ℝ) :
    ∑ i, ρL i * X i = ∑ i, seedWtL xL ρL i * X i + ∑ i ∈ distSetL xL, ρL i * X i := by
  classical
  rw [distSetL, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : xL i = 0 <;> simp [seedWtL, h]

theorem sum_mul_eq_seed_add_dist_R (X : Fin nR → ℝ) :
    ∑ i, ρR i * X i = ∑ i, seedWtR xR ρR i * X i + ∑ i ∈ distSetR xR, ρR i * X i := by
  classical
  rw [distSetR, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : xR i = 0 <;> simp [seedWtR, h]

theorem sum_eq_seed_add_dist_R : ∑ i, ρR i = ∑ i, seedWtR xR ρR i + ∑ i ∈ distSetR xR, ρR i := by
  simpa using sum_mul_eq_seed_add_dist_R ρR (fun _ => 1)

end Weights

/-! ### (HL5): the distant-force harmonic function -/

section Distant

variable {nL nR : ℕ} (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)

/-- **(HL5)**, the difference of the canonical means with and without the distant marks, in the centred half-plane
coordinate `w` with centred positions `aL`, `aR`:
`κ^{-1/2}(π ∑_{J,right} ρ_j − ∑_{J,left} ρ_j arg(w − aL_j) − ∑_{J,right} ρ_j arg(w − aR_j))`. -/
def distantHarm (aL : Fin nL → ℝ) (aR : Fin nR → ℝ) (w : ℂ) : ℝ :=
  1 / Real.sqrt κ * (Real.pi * ∑ i ∈ distSetR xR, ρR i - ∑ i ∈ distSetL xL, ρL i * Complex.arg (w - aL i)
    - ∑ i ∈ distSetR xR, ρR i * Complex.arg (w - aR i))

/-- **The canonical mean splits into the seed mean and (HL5)**: `meanHarmonic` (the imaginary part of (2.5)) with
all weights is the one with the seed weights plus `distantHarm`. -/
theorem meanHarmonic_eq_add_distantHarm (aL : Fin nL → ℝ) (aR : Fin nR → ℝ) (w : ℂ) :
    Ito.meanHarmonic κ ρL ρR aL aR w =
      Ito.meanHarmonic κ (seedWtL xL ρL) (seedWtR xR ρR) aL aR w + distantHarm κ xL xR ρL ρR aL aR w := by
  simp only [Ito.meanHarmonic, distantHarm]
  rw [sum_mul_eq_seed_add_dist_L ρL (fun i => Complex.arg (w - aL i)),
    sum_mul_eq_seed_add_dist_R ρR (fun i => Complex.arg (w - aR i)), sum_eq_seed_add_dist_R ρR]
  ring

/-- **The odd harmonic extension of `q` across `(−8r, 8r)`**:
`−κ^{-1/2}(∑_{J,left} ρ_j arg(z − x_j) + ∑_{J,right} ρ_j arg(x_j − z))`. -/
def qExt (z : ℂ) : ℝ :=
  -(1 / Real.sqrt κ) * (∑ i ∈ distSetL xL, ρL i * Complex.arg (z - xL i)
    + ∑ i ∈ distSetR xR, ρR i * Complex.arg ((xR i : ℂ) - z))

/-- The holomorphic function whose imaginary part is `qExt`. -/
def qHolo (z : ℂ) : ℂ :=
  -((1 / Real.sqrt κ : ℝ) : ℂ) * (∑ i ∈ distSetL xL, (ρL i : ℂ) * Complex.log (z - xL i)
    + ∑ i ∈ distSetR xR, (ρR i : ℂ) * Complex.log ((xR i : ℂ) - z))

variable {κ xL xR ρL ρR}

/-- **`qExt = q` on `ℍ`**: for `z ∈ ℍ`, `qExt z = distantHarm (x) z` (for a right mark `x > 0`,
`π − arg(z − x) = −arg(x − z)`). -/
theorem qExt_eq_distantHarm {z : ℂ} (hz : 0 < z.im) :
    qExt κ xL xR ρL ρR z = distantHarm κ xL xR ρL ρR xL xR z := by
  have hR : ∀ i ∈ distSetR xR, Complex.arg (z - xR i) = Complex.arg ((xR i : ℂ) - z) + Real.pi := by
    intro i _
    have him : ((xR i : ℂ) - z).im < 0 := by simp [hz]
    rw [← Complex.arg_neg_eq_arg_add_pi_of_im_neg him, neg_sub]
  have hsum : ∑ i ∈ distSetR xR, ρR i * Complex.arg (z - xR i) =
      ∑ i ∈ distSetR xR, ρR i * Complex.arg ((xR i : ℂ) - z) + Real.pi * ∑ i ∈ distSetR xR, ρR i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i hi => by rw [hR i hi]; ring
  simp only [qExt, distantHarm]
  rw [hsum]
  ring

theorem qExt_eq_im_qHolo (z : ℂ) : qExt κ xL xR ρL ρR z = (qHolo κ xL xR ρL ρR z).im := by
  simp only [qExt, qHolo, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_im, Complex.add_re, Complex.im_sum, Complex.re_sum, Complex.log_im,
    Complex.log_re, zero_mul, add_zero, neg_zero]

/-- Near the seed (`|z| < 8r`), the distant marks see `z` in the slit plane. -/
theorem sub_mem_slitPlane_L (hF : IsOrderedForceWord xL xR) {r : ℝ} (hr : IsSeedRadius xL xR r) {z : ℂ}
    (hz : ‖z‖ < 8 * r) {i : Fin nL} (hi : i ∈ distSetL xL) : z - xL i ∈ Complex.slitPlane := by
  have hi' : xL i ≠ 0 := (Finset.mem_filter.1 hi).2
  have h1 := hr.2.1 i hi'
  rw [abs_of_nonpos (hF.2.1 i)] at h1
  have h2 : -‖z‖ ≤ z.re := by have := Complex.abs_re_le_norm z; linarith [neg_abs_le z.re]
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  simp only [Complex.sub_re, Complex.ofReal_re]
  linarith

theorem sub_mem_slitPlane_R (hF : IsOrderedForceWord xL xR) {r : ℝ} (hr : IsSeedRadius xL xR r) {z : ℂ}
    (hz : ‖z‖ < 8 * r) {i : Fin nR} (hi : i ∈ distSetR xR) : (xR i : ℂ) - z ∈ Complex.slitPlane := by
  have hi' : xR i ≠ 0 := (Finset.mem_filter.1 hi).2
  have h1 := hr.2.2 i hi'
  rw [abs_of_nonneg (hF.2.2.2 i)] at h1
  have h2 : z.re ≤ ‖z‖ := (le_abs_self _).trans (Complex.abs_re_le_norm z)
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  simp only [Complex.sub_re, Complex.ofReal_re]
  linarith

theorem analyticAt_qHolo (hF : IsOrderedForceWord xL xR) {r : ℝ} (hr : IsSeedRadius xL xR r) {z : ℂ}
    (hz : ‖z‖ < 8 * r) : AnalyticAt ℂ (qHolo κ xL xR ρL ρR) z := by
  refine analyticAt_const.mul ((Finset.analyticAt_fun_sum _ fun i hi => ?_).add
    (Finset.analyticAt_fun_sum _ fun i hi => ?_))
  · exact analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).clog (sub_mem_slitPlane_L hF hr hz hi))
  · exact analyticAt_const.mul ((analyticAt_const.sub analyticAt_id).clog (sub_mem_slitPlane_R hF hr hz hi))

/-- **`q` extends harmonically across `(−8r, 8r)`** (p. 247). -/
theorem harmonicAt_qExt (hF : IsOrderedForceWord xL xR) {r : ℝ} (hr : IsSeedRadius xL xR r) {z : ℂ}
    (hz : ‖z‖ < 8 * r) : InnerProductSpace.HarmonicAt (qExt κ xL xR ρL ρR) z := by
  have h := (analyticAt_qHolo (κ := κ) (ρL := ρL) (ρR := ρR) hF hr hz).harmonicAt_im
  have he : (fun z => (qHolo κ xL xR ρL ρR z).im) = qExt κ xL xR ρL ρR :=
    funext fun z => (qExt_eq_im_qHolo z).symm
  rwa [he] at h

/-- **`q` extends oddly across `(−8r, 8r)`** (p. 247). -/
theorem qExt_conj (hF : IsOrderedForceWord xL xR) {r : ℝ} (hr : IsSeedRadius xL xR r) {z : ℂ}
    (hz : ‖z‖ < 8 * r) : qExt κ xL xR ρL ρR (conj z) = -qExt κ xL xR ρL ρR z := by
  have hz' : ‖conj z‖ < 8 * r := by rwa [Complex.norm_conj]
  have hargc : ∀ u : ℂ, u ∈ Complex.slitPlane → Complex.arg (conj u) = -Complex.arg u := fun u hu => by
    rw [Complex.arg_conj, ite_eq_right_iff.2 fun h => absurd h (Complex.mem_slitPlane_iff_arg.1 hu).1]
  have hL : ∀ i ∈ distSetL xL, Complex.arg (conj z - xL i) = -Complex.arg (z - xL i) := fun i hi => by
    rw [← hargc _ (sub_mem_slitPlane_L hF hr hz hi), map_sub, Complex.conj_ofReal]
  have hR : ∀ i ∈ distSetR xR, Complex.arg ((xR i : ℂ) - conj z) = -Complex.arg ((xR i : ℂ) - z) :=
    fun i hi => by rw [← hargc _ (sub_mem_slitPlane_R hF hr hz hi), map_sub, Complex.conj_ofReal]
  have hsL : ∑ i ∈ distSetL xL, ρL i * Complex.arg (conj z - xL i) =
      -∑ i ∈ distSetL xL, ρL i * Complex.arg (z - xL i) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i hi => by rw [hL i hi, mul_neg]
  have hsR : ∑ i ∈ distSetR xR, ρR i * Complex.arg ((xR i : ℂ) - conj z) =
      -∑ i ∈ distSetR xR, ρR i * Complex.arg ((xR i : ℂ) - z) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i hi => by rw [hR i hi, mul_neg]
  simp only [qExt]
  rw [hsL, hsR]
  ring

end Distant

/-! ### The radial cutoff -/

section Cutoff

/-- **A radial smooth cutoff**: `1` on `B̄(0, R₁)`, `0` off `B(0, R₂)`. -/
def cutoffFn (R₁ R₂ : ℝ) (z : ℂ) : ℝ := Real.smoothTransition ((R₂ ^ 2 - ‖z‖ ^ 2) / (R₂ ^ 2 - R₁ ^ 2))

variable {R₁ R₂ : ℝ}

theorem contDiff_cutoffFn {n : ℕ∞} : ContDiff ℝ n (cutoffFn R₁ R₂) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub (contDiff_norm_sq ℝ)).div_const _)

theorem cutoffFn_eq_one (h0 : 0 ≤ R₁) (h : R₁ < R₂) {z : ℂ} (hz : ‖z‖ ≤ R₁) : cutoffFn R₁ R₂ z = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  have hd : 0 < R₂ ^ 2 - R₁ ^ 2 := by nlinarith
  rw [le_div_iff₀ hd]
  have : ‖z‖ ^ 2 ≤ R₁ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
  linarith

theorem cutoffFn_eq_zero (h0 : 0 ≤ R₁) (h : R₁ < R₂) {z : ℂ} (hz : R₂ ≤ ‖z‖) : cutoffFn R₁ R₂ z = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  have hd : 0 < R₂ ^ 2 - R₁ ^ 2 := by nlinarith
  refine div_nonpos_of_nonpos_of_nonneg ?_ hd.le
  have : R₂ ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (by linarith) hz 2
  linarith

theorem cutoffFn_conj (z : ℂ) : cutoffFn R₁ R₂ (conj z) = cutoffFn R₁ R₂ z := by
  simp only [cutoffFn, Complex.norm_conj]

end Cutoff

/-! ### The Laplacian commutes with complex conjugation -/

section Conj

theorem laplacian_comp_conj {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (z : ℂ) :
    Δ (fun y => f (conj y)) z = Δ f (conj z) := by
  have hL : (fun y => f (conj y)) = f ∘ (Complex.conjCLE : ℂ →L[ℝ] ℂ) := rfl
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane, hL]
  simp only
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ hf z le_rfl]
  have hc : ∀ u, (Complex.conjCLE : ℂ →L[ℝ] ℂ) u = conj u := fun u => rfl
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hc]
  have h1 : (fun i : Fin 2 => conj (![(1 : ℂ), 1] i)) = ![1, 1] := by
    funext i; fin_cases i <;> simp
  have h2 : (fun i : Fin 2 => conj (![Complex.I, Complex.I] i)) =
      fun i : Fin 2 => (-1 : ℝ) • ![Complex.I, Complex.I] i := by
    funext i; fin_cases i <;> simp
  rw [h1, h2, ContinuousMultilinearMap.map_smul_univ]
  simp

theorem laplacian_neg_apply {f : ℂ → ℝ} (z : ℂ) : Δ (fun y => -f y) z = -Δ f z := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only
  rw [show (fun y => -f y) = -f from rfl, iteratedFDeriv_neg_apply]
  simp only [neg_apply]
  ring

end Conj

/-! ### (HL1)–(HL2): the cutoff field and its source -/

section Field

variable {nL nR : ℕ} (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ)

/-- **(HL1)** `f = ζ q`, `ζ` the radial cutoff equal to `1` on `B̄(0, 6r)` and `0` off `B(0, 7r)`. -/
def fCut (z : ℂ) : ℝ := cutoffFn (6 * r) (7 * r) z * qExt κ xL xR ρL ρR z

/-- `−(2π)⁻¹ Δ f` on the whole plane. -/
def vDens : ℂ → ℝ := QuantumZipper.K3.greenDensity (fCut κ xL xR ρL ρR r)

/-- **(HL2)** the source `v = −(2π)⁻¹ Δ f`, restricted to `ℍ`. -/
def vSrc : ℂ → ℝ := Set.indicator QuantumZipper.H (vDens κ xL xR ρL ρR r)

variable {κ xL xR ρL ρR r}

theorem fCut_eq_zero (hr0 : 0 < r) {z : ℂ} (hz : 7 * r ≤ ‖z‖) : fCut κ xL xR ρL ρR r z = 0 := by
  rw [fCut, cutoffFn_eq_zero (by linarith) (by linarith) hz, zero_mul]

theorem fCut_eq_qExt (hr0 : 0 < r) {z : ℂ} (hz : ‖z‖ ≤ 6 * r) :
    fCut κ xL xR ρL ρR r z = qExt κ xL xR ρL ρR z := by
  rw [fCut, cutoffFn_eq_one (by linarith) (by linarith) hz, one_mul]

theorem contDiffAt_qExt (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) {z : ℂ}
    (hz : ‖z‖ < 8 * r) {n : ℕ∞} : ContDiffAt ℝ n (qExt κ xL xR ρL ρR) z := by
  have he : qExt κ xL xR ρL ρR = fun z => Complex.imCLM (qHolo κ xL xR ρL ρR z) :=
    funext fun z => qExt_eq_im_qHolo z
  rw [he]
  exact Complex.imCLM.contDiff.contDiffAt.comp z
    ((analyticAt_qHolo hF hr hz).contDiffAt.restrict_scalars ℝ)

theorem contDiff_fCut (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) {n : ℕ∞} :
    ContDiff ℝ n (fCut κ xL xR ρL ρR r) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  rcases lt_or_ge ‖z‖ (8 * r) with hz | hz
  · exact contDiff_cutoffFn.contDiffAt.mul (contDiffAt_qExt hF hr hz)
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    have hopen : IsOpen {y : ℂ | 7 * r < ‖y‖} := isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds (show 7 * r < ‖z‖ by linarith [hr.1])] with y hy
    exact fCut_eq_zero hr.1 hy.le

theorem tsupport_fCut_subset (hr0 : 0 < r) : tsupport (fCut κ xL xR ρL ρR r) ⊆ closedBall 0 (7 * r) := by
  refine closure_minimal (fun z hz => ?_) isClosed_closedBall
  by_contra h
  rw [mem_closedBall, dist_zero_right, not_le] at h
  exact hz (fCut_eq_zero hr0 h.le)

theorem hasCompactSupport_fCut (hr0 : 0 < r) : HasCompactSupport (fCut κ xL xR ρL ρR r) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (7 * r)) fun z hz => by
    rw [mem_closedBall, dist_zero_right, not_le] at hz
    exact fCut_eq_zero hr0 hz.le

/-- `f` is odd under reflection in `ℝ`. -/
theorem fCut_conj (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (z : ℂ) :
    fCut κ xL xR ρL ρR r (conj z) = -fCut κ xL xR ρL ρR r z := by
  rcases lt_or_ge ‖z‖ (8 * r) with hz | hz
  · rw [fCut, fCut, cutoffFn_conj, qExt_conj hF hr hz, mul_neg]
  · rw [fCut_eq_zero hr.1 (by rw [Complex.norm_conj]; linarith [hr.1]), fCut_eq_zero hr.1 (by linarith [hr.1]),
      neg_zero]

theorem continuous_vDens (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) :
    Continuous (vDens κ xL xR ρL ρR r) :=
  QuantumZipper.K3.continuous_greenDensity (contDiff_fCut hF hr)

theorem hasCompactSupport_vDens (hr0 : 0 < r) : HasCompactSupport (vDens κ xL xR ρL ρR r) :=
  QuantumZipper.K3.hasCompactSupport_greenDensity (hasCompactSupport_fCut hr0)

theorem tsupport_vDens_subset (hr0 : 0 < r) : tsupport (vDens κ xL xR ρL ρR r) ⊆ closedBall 0 (7 * r) :=
  (QuantumZipper.K3.tsupport_greenDensity_subset _).trans (tsupport_fCut_subset hr0)

/-- `v` is odd under reflection in `ℝ`. -/
theorem vDens_conj (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (z : ℂ) :
    vDens κ xL xR ρL ρR r (conj z) = -vDens κ xL xR ρL ρR r z := by
  have hodd : (fun y => fCut κ xL xR ρL ρR r (conj y)) = fun y => -fCut κ xL xR ρL ρR r y :=
    funext fun y => fCut_conj hF hr y
  have h := laplacian_comp_conj (contDiff_fCut (κ := κ) (ρL := ρL) (ρR := ρR) hF hr (n := 2)) z
  rw [hodd, laplacian_neg_apply] at h
  simp only [vDens, QuantumZipper.K3.greenDensity]
  rw [← h]
  ring

/-- `v` vanishes on `ℝ`. -/
theorem vDens_eq_zero_of_im_eq_zero (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) {z : ℂ}
    (hz : z.im = 0) : vDens κ xL xR ρL ρR r z = 0 := by
  have hc : conj z = z := Complex.conj_eq_iff_im.2 hz
  have h := vDens_conj (κ := κ) (ρL := ρL) (ρR := ρR) hF hr z
  rw [hc] at h
  linarith

/-- `v` vanishes on `B(0, 6r)`, where `f = q` is harmonic. -/
theorem vDens_eq_zero_of_norm_lt (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) {z : ℂ}
    (hz : ‖z‖ < 6 * r) : vDens κ xL xR ρL ρR r z = 0 := by
  have hopen : IsOpen {y : ℂ | ‖y‖ < 6 * r} := isOpen_lt continuous_norm continuous_const
  have heq : fCut κ xL xR ρL ρR r =ᶠ[𝓝 z] qExt κ xL xR ρL ρR := by
    filter_upwards [hopen.mem_nhds hz] with y hy
    exact fCut_eq_qExt hr.1 hy.le
  have hH := harmonicAt_qExt (κ := κ) (ρL := ρL) (ρR := ρR) hF hr (show ‖z‖ < 8 * r by linarith [hr.1])
  simp only [vDens, QuantumZipper.K3.greenDensity]
  rw [(InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds, hH.2.eq_of_nhds, Pi.zero_apply, mul_zero]

/-- The source vanishes off `{6r ≤ |z| ≤ 7r} ∩ ℍ`. -/
theorem vSrc_eq_zero_of_not (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) {z : ℂ}
    (hz : ¬ (0 < z.im ∧ 6 * r ≤ ‖z‖ ∧ ‖z‖ ≤ 7 * r)) : vSrc κ xL xR ρL ρR r z = 0 := by
  by_cases hH : 0 < z.im
  · rw [vSrc, Set.indicator_of_mem (show z ∈ QuantumZipper.H from hH)]
    rcases lt_or_ge ‖z‖ (6 * r) with h4 | h4
    · exact vDens_eq_zero_of_norm_lt hF hr h4
    · have h6 : 7 * r < ‖z‖ := by
        by_contra h6; exact hz ⟨hH, h4, not_lt.1 h6⟩
      exact image_eq_zero_of_notMem_tsupport fun hm => by
        have := tsupport_vDens_subset hr.1 hm
        rw [mem_closedBall, dist_zero_right] at this
        linarith
  · exact Set.indicator_of_notMem (show z ∉ QuantumZipper.H from hH) _

theorem measurable_vSrc (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) :
    Measurable (vSrc κ xL xR ρL ρR r) :=
  (continuous_vDens hF hr).measurable.indicator (isOpen_lt continuous_const Complex.continuous_im).measurableSet

end Field

/-! ### Green inversion: `G_ℍ v = f` -/

section Green

open QuantumZipper (greenH)

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}

theorem greenH_conj_right (w z : ℂ) : greenH w (conj z) = -greenH w z := by
  simp only [greenH, Complex.conj_conj]
  ring

theorem integrable_greenH_mul_vDens (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (w : ℂ) :
    Integrable fun z => greenH w z * vDens κ xL xR ρL ρR r z := by
  have hΔc := continuous_vDens (κ := κ) (ρL := ρL) (ρR := ρR) hF hr
  have hs := hasCompactSupport_vDens (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR) hr.1
  have i1 := QuantumZipper.K3.integrable_log_norm_sub_mul_K3 hΔc hs (conj w)
  have i2 := QuantumZipper.K3.integrable_log_norm_sub_mul_K3 hΔc hs w
  refine (i1.sub i2).congr (ae_of_all _ fun z => ?_)
  simp only [Pi.sub_apply, greenH, QuantumZipper.norm_sub_conj_comm w z, norm_sub_rev w z]
  ring

/-- The whole-plane Green integral of `v`: `∫ G_ℍ(w, z) v(z) dz = f(w) − f(w̄)`. -/
theorem integral_greenH_mul_vDens (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (w : ℂ) :
    ∫ z, greenH w z * vDens κ xL xR ρL ρR r z =
      fCut κ xL xR ρL ρR r w - fCut κ xL xR ρL ρR r (conj w) := by
  have h2 : ContDiff ℝ 2 (fCut κ xL xR ρL ρR r) := contDiff_fCut hF hr
  have hc := hasCompactSupport_fCut (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR) hr.1
  have hΔc := QuantumZipper.K3.continuous_laplacian_K3 h2
  have hΔs := QuantumZipper.K3.hasCompactSupport_laplacian_K3 hc
  have i1 := QuantumZipper.K3.integrable_log_norm_sub_mul_K3 hΔc hΔs (conj w)
  have i2 := QuantumZipper.K3.integrable_log_norm_sub_mul_K3 hΔc hΔs w
  have e : ∀ z, greenH w z * vDens κ xL xR ρL ρR r z =
      -(2 * Real.pi)⁻¹ * (Real.log ‖z - conj w‖ * Δ (fCut κ xL xR ρL ρR r) z
        - Real.log ‖z - w‖ * Δ (fCut κ xL xR ρL ρR r) z) := by
    intro z
    simp only [greenH, vDens, QuantumZipper.K3.greenDensity, QuantumZipper.norm_sub_conj_comm w z,
      norm_sub_rev w z]
    ring
  simp_rw [e]
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  rw [integral_const_mul, integral_sub i1 i2, QuantumZipper.K3.integral_log_norm_sub_mul_laplacian h2 hc,
    QuantumZipper.K3.integral_log_norm_sub_mul_laplacian h2 hc]
  field_simp
  ring

/-- **Dirichlet Green inversion `G_ℍ v = f`** (p. 248): `∫ G_ℍ(w, z) v(z) dz = f(w)` for the source `v`
restricted to `ℍ` (by the reflection symmetry of `f`, `v` and `G_ℍ`, the whole-plane integral is twice the
half-plane one). -/
theorem integral_greenH_mul_vSrc (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (w : ℂ) :
    ∫ z, greenH w z * vSrc κ xL xR ρL ρR r z = fCut κ xL xR ρL ρR r w := by
  set v := vDens κ xL xR ρL ρR r with hv
  set vLow : ℂ → ℝ := Set.indicator {z : ℂ | z.im < 0} v with hvLow
  have hHm : MeasurableSet QuantumZipper.H := (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hLm : MeasurableSet {z : ℂ | z.im < 0} := (isOpen_lt Complex.continuous_im continuous_const).measurableSet
  have hint := integrable_greenH_mul_vDens (κ := κ) (ρL := ρL) (ρR := ρR) hF hr w
  have hup : (fun z => greenH w z * vSrc κ xL xR ρL ρR r z) =
      Set.indicator QuantumZipper.H (fun z => greenH w z * v z) := by
    funext z
    rw [vSrc, Set.indicator_mul_right]
  have hlow : (fun z => greenH w z * vLow z) = Set.indicator {z : ℂ | z.im < 0} (fun z => greenH w z * v z) := by
    funext z
    rw [hvLow, Set.indicator_mul_right]
  have hsplit : (fun z => greenH w z * v z) =
      fun z => greenH w z * vSrc κ xL xR ρL ρR r z + greenH w z * vLow z := by
    funext z
    rw [← mul_add]
    congr 1
    rcases lt_trichotomy z.im 0 with h | h | h
    · rw [vSrc, Set.indicator_of_notMem (show z ∉ QuantumZipper.H from fun h' => by
        change 0 < z.im at h'; linarith), hvLow, Set.indicator_of_mem (show z ∈ {z : ℂ | z.im < 0} from h),
        zero_add]
    · rw [hv, vDens_eq_zero_of_im_eq_zero hF hr h, vSrc, Set.indicator_of_notMem
        (show z ∉ QuantumZipper.H from fun h' => by change 0 < z.im at h'; linarith), hvLow,
        Set.indicator_of_notMem (show z ∉ {z : ℂ | z.im < 0} from fun h' => by
          change z.im < 0 at h'; linarith), add_zero]
    · rw [vSrc, Set.indicator_of_mem (show z ∈ QuantumZipper.H from h), hvLow, Set.indicator_of_notMem
        (show z ∉ {z : ℂ | z.im < 0} from fun h' => by change z.im < 0 at h'; linarith), add_zero]
  have hrefl : ∫ z, greenH w z * vLow z = ∫ z, greenH w z * vSrc κ xL xR ρL ρR r z := by
    rw [← (Complex.conjLIE.measurePreserving).integral_comp
      Complex.conjLIE.toHomeomorph.measurableEmbedding]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [Complex.conjLIE_apply]
    rw [greenH_conj_right]
    by_cases hz : 0 < z.im
    · rw [hvLow, Set.indicator_of_mem (show conj z ∈ {z : ℂ | z.im < 0} by
        change (conj z).im < 0; rw [Complex.conj_im]; linarith), hv, vDens_conj hF hr, vSrc,
        Set.indicator_of_mem (show z ∈ QuantumZipper.H from hz)]
      ring
    · rw [hvLow, Set.indicator_of_notMem (show conj z ∉ {z : ℂ | z.im < 0} by
        change ¬ (conj z).im < 0; rw [Complex.conj_im]; linarith), vSrc,
        Set.indicator_of_notMem (show z ∉ QuantumZipper.H from hz)]
      ring
  have htot := integral_greenH_mul_vDens (κ := κ) (ρL := ρL) (ρR := ρR) hF hr w
  rw [← hv, hsplit, integral_add (hup ▸ hint.indicator hHm) (hlow ▸ hint.indicator hLm), hrefl,
    fCut_conj hF hr] at htot
  linarith

end Green

end LocalExt

end InteractingSLE
