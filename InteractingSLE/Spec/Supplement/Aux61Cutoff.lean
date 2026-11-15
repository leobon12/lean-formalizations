/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux61Ident

/-!
# Aux. lemma 62, the cutoff: two real cores (the seed and the target interval)

Packet PROVE-GB7A2. Source: proofs of Aux. lemmas 62 and 64 (`source/spec/p241-288.md`, pp. 262–265): "The
reflected boundary cutoff construction at 3.2 provides `f ∈ H¹₀(ℍ)`, with `f = v` on `U` and on a neighborhood of
its closure"; the buffered set `U₀` of Aux. 64 meets the real line only in the canonical seed neighbourhood and in
the interval `I₁`, where the actual and the reference means agree.

In the half-plane chart of the restart, the difference of the two means is an arg sum `D = c₀ + ∑ cⱼ arg(z − pⱼ)`
whose boundary value vanishes on two real *cores*, the seed core `(−a₀, a₀)` and the target core `(a₁, b₁)`. This file
builds

* `cutChi P`: a smooth cutoff, even in `Im z`, equal to `1` on the open set `cutN P` (the buffer: the disc of radius
  `R`, above height `2μ` or over the shrunk cores), vanishing near the real points off the cores;
* `oddExt p c c₀`: the odd extension of `D` across `ℝ`, analytic across each core (`oddExt_eq_im_coreHol`);
* `cutF = cutChi · oddExt`: odd, compactly supported and smooth (`contDiff_cutF`), equal to `D` on `cutN P`;
* `fillH_subset_cutN`: a compact set in the inner buffer `cutU P` meeting `ℝ` only at `0` has its filling, and
  the closure of the filling, inside `cutN P` (every point near the real line off the cores, or far out, is joined to
  `∞` outside the set).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate Interval

namespace InteractingSLE

namespace GB7a

open QuantumZipper (H Hbar fwdMap fwdHull IsForwardSol greenH fwdMapInv)

/-! ### Parameters and the one-dimensional bumps -/

/-- The parameters of the cutoff: the seed core `(−a₀, a₀)`, the target core `(a₁, b₁)`, the margin `μ` and the
radius `R`. -/
structure CutParams where
  a₀ : ℝ
  a₁ : ℝ
  b₁ : ℝ
  μ : ℝ
  R : ℝ

/-- The admissibility of the parameters. -/
structure CutParams.Valid (P : CutParams) : Prop where
  μ_pos : 0 < P.μ
  a₀_gt : 3 * P.μ < P.a₀
  a₀_lt : P.a₀ + P.μ < P.a₁ - P.μ
  core1 : P.a₁ + 3 * P.μ < P.b₁ - 3 * P.μ
  R_pos : 0 < P.R

/-- The seed bump: `1` for `|x| ≤ a₀ − μ`, `0` for `|x| ≥ a₀`. -/
def bump0 (P : CutParams) (x : ℝ) : ℝ :=
  Real.smoothTransition ((P.a₀ ^ 2 - x ^ 2) / (P.a₀ ^ 2 - (P.a₀ - P.μ) ^ 2))

/-- The target bump: `1` on `[a₁ + μ, b₁ − μ]`, `0` off `(a₁, b₁)`. -/
def bump1 (P : CutParams) (x : ℝ) : ℝ :=
  Real.smoothTransition ((x - P.a₁) / P.μ) * Real.smoothTransition ((P.b₁ - x) / P.μ)

/-- The core bump `A = bump0 + bump1`. -/
def coreBump (P : CutParams) (x : ℝ) : ℝ := bump0 P x + bump1 P x

/-- The height bump: `0` for `|y| ≤ μ`, `1` for `|y| ≥ 2μ`. -/
def heightBump (P : CutParams) (y : ℝ) : ℝ := Real.smoothTransition ((y ^ 2 - P.μ ^ 2) / (3 * P.μ ^ 2))

/-- **The cutoff** `χ(z) = D(|z|) (A(Re z) + C(Im z) − A(Re z) C(Im z))`. -/
def cutChi (P : CutParams) (z : ℂ) : ℝ :=
  LocalExt.cutoffFn P.R (P.R + 1) z *
    (coreBump P z.re + heightBump P z.im - coreBump P z.re * heightBump P z.im)

variable {P : CutParams}

theorem contDiff_bump0 {n : ℕ∞} : ContDiff ℝ n (bump0 P) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub (contDiff_id.pow 2)).div_const _)

theorem contDiff_bump1 {n : ℕ∞} : ContDiff ℝ n (bump1 P) :=
  (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _))

theorem contDiff_heightBump {n : ℕ∞} : ContDiff ℝ n (heightBump P) :=
  Real.smoothTransition.contDiff.comp (((contDiff_id.pow 2).sub contDiff_const).div_const _)

theorem contDiff_cutChi {n : ℕ∞} : ContDiff ℝ n (cutChi P) := by
  have hre : ContDiff ℝ n fun z : ℂ => coreBump P z.re :=
    (contDiff_bump0.add contDiff_bump1).comp Complex.reCLM.contDiff
  have him : ContDiff ℝ n fun z : ℂ => heightBump P z.im := contDiff_heightBump.comp Complex.imCLM.contDiff
  exact LocalExt.contDiff_cutoffFn.mul ((hre.add him).sub (hre.mul him))

theorem bump0_eq_zero (hP : P.Valid) {x : ℝ} (hx : P.a₀ ≤ |x|) : bump0 P x = 0 := by
  refine Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ?_ ?_)
  · have : P.a₀ ^ 2 ≤ x ^ 2 := by
      rw [← sq_abs x]; exact pow_le_pow_left₀ (by linarith [hP.μ_pos, hP.a₀_gt]) hx 2
    linarith
  · have h1 : 0 ≤ P.a₀ - P.μ := by linarith [hP.μ_pos, hP.a₀_gt]
    nlinarith [hP.μ_pos]

theorem bump0_eq_one (hP : P.Valid) {x : ℝ} (hx : |x| ≤ P.a₀ - P.μ) : bump0 P x = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  have h1 : 0 ≤ P.a₀ - P.μ := by linarith [hP.μ_pos, hP.a₀_gt]
  have hd : 0 < P.a₀ ^ 2 - (P.a₀ - P.μ) ^ 2 := by nlinarith [hP.μ_pos]
  rw [le_div_iff₀ hd, one_mul]
  have : x ^ 2 ≤ (P.a₀ - P.μ) ^ 2 := by rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  linarith

theorem bump1_eq_zero (hP : P.Valid) {x : ℝ} (hx : x ≤ P.a₁ ∨ P.b₁ ≤ x) : bump1 P x = 0 := by
  rcases hx with hx | hx
  · rw [bump1, Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      hP.μ_pos.le), zero_mul]
  · have h : (P.b₁ - x) / P.μ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hP.μ_pos.le
    rw [bump1, Real.smoothTransition.zero_of_nonpos h, mul_zero]

theorem bump1_eq_one (hP : P.Valid) {x : ℝ} (hx : x ∈ Icc (P.a₁ + P.μ) (P.b₁ - P.μ)) : bump1 P x = 1 := by
  have h1 : 1 ≤ (x - P.a₁) / P.μ := by rw [le_div_iff₀ hP.μ_pos]; linarith [hx.1]
  have h2 : 1 ≤ (P.b₁ - x) / P.μ := by rw [le_div_iff₀ hP.μ_pos]; linarith [hx.2]
  rw [bump1, Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, one_mul]

theorem heightBump_eq_zero {y : ℝ} (hy : |y| ≤ P.μ) : heightBump P y = 0 := by
  refine Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ?_ (by positivity))
  have : y ^ 2 ≤ P.μ ^ 2 := by rw [← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  linarith

theorem heightBump_eq_one (hP : P.Valid) {y : ℝ} (hy : 2 * P.μ ≤ |y|) : heightBump P y = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  have hμ := hP.μ_pos
  rw [le_div_iff₀ (by positivity), one_mul]
  have : (2 * P.μ) ^ 2 ≤ y ^ 2 := by rw [← sq_abs y]; exact pow_le_pow_left₀ (by positivity) hy 2
  nlinarith

theorem heightBump_neg (y : ℝ) : heightBump P (-y) = heightBump P y := by simp [heightBump]

theorem cutChi_conj (z : ℂ) : cutChi P (conj z) = cutChi P z := by
  simp only [cutChi, LocalExt.cutoffFn_conj, Complex.conj_re, Complex.conj_im, heightBump_neg]

/-! ### The buffer `N` where `χ = 1` -/

/-- **The buffer** `N`: the disc of radius `R`, above height `2μ` (in absolute value) or over the shrunk cores. -/
def cutN (P : CutParams) : Set ℂ :=
  {z | ‖z‖ < P.R ∧ (2 * P.μ < |z.im| ∨ |z.re| < P.a₀ - P.μ ∨ z.re ∈ Ioo (P.a₁ + P.μ) (P.b₁ - P.μ))}

theorem isOpen_cutN : IsOpen (cutN P) := by
  refine (isOpen_lt continuous_norm continuous_const).inter (((isOpen_lt continuous_const
    Complex.continuous_im.abs)).union ((isOpen_lt Complex.continuous_re.abs continuous_const).union
      (isOpen_Ioo.preimage Complex.continuous_re)))

theorem cutChi_eq_one (hP : P.Valid) {z : ℂ} (hz : z ∈ cutN P) : cutChi P z = 1 := by
  obtain ⟨hR, h⟩ := hz
  have hD : LocalExt.cutoffFn P.R (P.R + 1) z = 1 :=
    LocalExt.cutoffFn_eq_one hP.R_pos.le (by linarith) hR.le
  rw [cutChi, hD, one_mul]
  rcases h with h | h | h
  · rw [heightBump_eq_one hP h.le]; ring
  · have h1 : bump1 P z.re = 0 := bump1_eq_zero hP (Or.inl (by
      have := (abs_lt.1 h).2; linarith [hP.a₀_lt, hP.μ_pos]))
    rw [coreBump, bump0_eq_one hP h.le, h1]; ring
  · have h0 : bump0 P z.re = 0 := bump0_eq_zero hP (by
      rw [abs_of_pos (by linarith [h.1, hP.a₀_lt, hP.a₀_gt, hP.μ_pos])]; linarith [h.1, hP.a₀_lt, hP.μ_pos])
    rw [coreBump, h0, bump1_eq_one hP ⟨h.1.le, h.2.le⟩]; ring

theorem zero_mem_cutN (hP : P.Valid) : (0 : ℂ) ∈ cutN P :=
  ⟨by simpa using hP.R_pos, Or.inr (Or.inl (by simp; linarith [hP.a₀_gt, hP.μ_pos]))⟩

/-- Near a real point off the closed cores, `χ` vanishes. -/
theorem cutChi_eq_zero_near (hP : P.Valid) {x : ℝ} (hx : P.a₀ < |x|) (hx1 : x < P.a₁ ∨ P.b₁ < x) :
    ∀ᶠ z in 𝓝 (x : ℂ), cutChi P z = 0 := by
  have h1 : ∀ᶠ z in 𝓝 (x : ℂ), P.a₀ < |z.re| :=
    (Complex.continuous_re.abs.tendsto _).eventually (lt_mem_nhds (by simpa using hx))
  have h2 : ∀ᶠ z in 𝓝 (x : ℂ), z.re < P.a₁ ∨ P.b₁ < z.re := by
    rcases hx1 with h | h
    · exact ((Complex.continuous_re.tendsto _).eventually (gt_mem_nhds (by simpa using h))).mono
        fun z hz => Or.inl hz
    · exact ((Complex.continuous_re.tendsto _).eventually (lt_mem_nhds (by simpa using h))).mono
        fun z hz => Or.inr hz
  have h3 : ∀ᶠ z in 𝓝 (x : ℂ), |z.im| < P.μ :=
    (Complex.continuous_im.abs.tendsto _).eventually (gt_mem_nhds (by simpa using hP.μ_pos))
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
  rw [cutChi, coreBump, bump0_eq_zero hP hz1.le,
    bump1_eq_zero hP (hz2.imp le_of_lt le_of_lt), heightBump_eq_zero hz3.le]
  ring

/-! ### The odd extension of an arg sum -/

section OddExt

variable {ι : Type*} [Fintype ι] (p c : ι → ℝ) (c₀ : ℝ)

/-- The arg sum `c₀ + ∑ cⱼ arg(z − pⱼ)` in the original coordinate (time `0`). -/
def argSum0 (z : ℂ) : ℝ := c₀ + ∑ j, c j * Complex.arg (z - p j)

/-- **The odd extension** of `argSum0` across `ℝ`: `argSum0` on `ℍ`, `−argSum0(z̄)` below, `0` on `ℝ`. -/
def oddExt (z : ℂ) : ℝ :=
  if 0 < z.im then argSum0 p c c₀ z else if z.im < 0 then -argSum0 p c c₀ (conj z) else 0

/-- The core expression over the strip `l < Re z < r`: `∑_{pⱼ ≤ l} cⱼ arg(z − pⱼ) + ∑_{pⱼ ≥ r} cⱼ arg(pⱼ − z)`. -/
def argCore (l r : ℝ) (z : ℂ) : ℝ :=
  (∑ j ∈ Finset.univ.filter (fun j => p j ≤ l), c j * Complex.arg (z - p j)) +
    ∑ j ∈ Finset.univ.filter (fun j => r ≤ p j), c j * Complex.arg ((p j : ℂ) - z)

/-- The holomorphic function with imaginary part `argCore` on the strip. -/
def holCore (l r : ℝ) (z : ℂ) : ℂ :=
  (∑ j ∈ Finset.univ.filter (fun j => p j ≤ l), (c j : ℂ) * Complex.log (z - p j)) +
    ∑ j ∈ Finset.univ.filter (fun j => r ≤ p j), (c j : ℂ) * Complex.log ((p j : ℂ) - z)

variable {p c c₀}

theorem argCore_eq_im_holCore (l r : ℝ) (z : ℂ) : argCore p c l r z = (holCore p c l r z).im := by
  simp only [argCore, holCore, Complex.add_im, Complex.im_sum, Complex.im_ofReal_mul, Complex.log_im]

theorem slit_left {l : ℝ} {z : ℂ} (hz : l < z.re) {x : ℝ} (hx : x ≤ l) : z - x ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inl (by simp; linarith))

theorem slit_right {r : ℝ} {z : ℂ} (hz : z.re < r) {x : ℝ} (hx : r ≤ x) : (x : ℂ) - z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inl (by simp; linarith))

theorem contDiffAt_argCore {l r : ℝ} {z : ℂ} (hl : l < z.re) (hr : z.re < r) {n : ℕ∞} :
    ContDiffAt ℝ n (argCore p c l r) z := by
  have he : argCore p c l r = fun z => Complex.imCLM (holCore p c l r z) :=
    funext fun z => argCore_eq_im_holCore l r z
  rw [he]
  have hh : AnalyticAt ℂ (holCore p c l r) z := by
    refine (Finset.analyticAt_fun_sum _ fun j hj => ?_).add (Finset.analyticAt_fun_sum _ fun j hj => ?_)
    · have hx : p j ≤ l := (Finset.mem_filter.1 hj).2
      exact analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).clog (slit_left hl hx))
    · have hx : r ≤ p j := (Finset.mem_filter.1 hj).2
      exact analyticAt_const.mul ((analyticAt_const.sub analyticAt_id).clog (slit_right hr hx))
  exact Complex.imCLM.contDiff.contDiffAt.comp z (hh.contDiffAt.restrict_scalars ℝ)

/-- **The odd extension is the core expression on the strip** (when no mark lies in `(l, r)` and the boundary
value `c₀ + π ∑_{pⱼ ≥ r} cⱼ` of the arg sum vanishes there). -/
theorem oddExt_eq_argCore {l r : ℝ} (havoid : ∀ j, p j ≤ l ∨ r ≤ p j)
    (hdata : c₀ + Real.pi * ∑ j ∈ Finset.univ.filter (fun j => r ≤ p j), c j = 0) {z : ℂ} (hl : l < z.re)
    (hr : z.re < r) : oddExt p c c₀ z = argCore p c l r z := by
  classical
  have hlr : l < r := hl.trans hr
  have hsplit : ∀ g : ι → ℝ, ∑ j, g j = (∑ j ∈ Finset.univ.filter (fun j => p j ≤ l), g j) +
      ∑ j ∈ Finset.univ.filter (fun j => r ≤ p j), g j := by
    intro g
    rw [← Finset.sum_union]
    · congr 1; ext j; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
      exact havoid j
    · exact Finset.disjoint_filter.2 fun j _ h1 h2 => by linarith
  have hR : ∀ w : ℂ, (∑ j ∈ Finset.univ.filter (fun j => r ≤ p j), c j * Real.pi) =
      Real.pi * ∑ j ∈ Finset.univ.filter (fun j => r ≤ p j), c j := fun _ => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rcases lt_trichotomy 0 z.im with hpos | hzero | hneg
  · simp only [oddExt, hpos, ↓reduceIte]
    rw [argSum0, hsplit, argCore]
    have hRr : ∀ j ∈ Finset.univ.filter (fun j => r ≤ p j), c j * Complex.arg (z - p j) =
        c j * Complex.arg ((p j : ℂ) - z) + c j * Real.pi := by
      intro j _
      have him : ((p j : ℂ) - z).im < 0 := by simp; linarith
      rw [show z - p j = -((p j : ℂ) - z) by ring, Complex.arg_neg_eq_arg_add_pi_of_im_neg him]
      ring
    rw [Finset.sum_congr rfl hRr, Finset.sum_add_distrib, hR z]
    linear_combination hdata
  · have h0 : ¬ 0 < z.im := by rw [← hzero]; exact lt_irrefl 0
    have h1 : ¬ z.im < 0 := by rw [← hzero]; exact lt_irrefl 0
    simp only [oddExt, h0, h1, ↓reduceIte]
    rw [argCore]
    have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [← hzero])
    have hL : ∀ j ∈ Finset.univ.filter (fun j => p j ≤ l), c j * Complex.arg (z - p j) = 0 := by
      intro j hj
      have hx : p j ≤ l := (Finset.mem_filter.1 hj).2
      rw [hzr, ← Complex.ofReal_sub, Complex.arg_ofReal_of_nonneg (by linarith), mul_zero]
    have hRr : ∀ j ∈ Finset.univ.filter (fun j => r ≤ p j), c j * Complex.arg ((p j : ℂ) - z) = 0 := by
      intro j hj
      have hx : r ≤ p j := (Finset.mem_filter.1 hj).2
      rw [hzr, ← Complex.ofReal_sub, Complex.arg_ofReal_of_nonneg (by linarith), mul_zero]
    rw [Finset.sum_eq_zero hL, Finset.sum_eq_zero hRr, add_zero]
  · have h0 : ¬ 0 < z.im := not_lt.2 hneg.le
    simp only [oddExt, h0, hneg, ↓reduceIte]
    rw [argSum0, hsplit, argCore]
    have hL : ∀ j ∈ Finset.univ.filter (fun j => p j ≤ l), c j * Complex.arg (conj z - p j) =
        -(c j * Complex.arg (z - p j)) := by
      intro j hj
      have hx : p j ≤ l := (Finset.mem_filter.1 hj).2
      have hs := slit_left hl hx
      rw [show conj z - (p j : ℂ) = conj (z - p j) by simp, Complex.arg_conj]
      simp only [(Complex.mem_slitPlane_iff_arg.1 hs).1, ↓reduceIte]
      ring
    have hRr : ∀ j ∈ Finset.univ.filter (fun j => r ≤ p j), c j * Complex.arg (conj z - p j) =
        -(c j * Complex.arg ((p j : ℂ) - z)) + c j * Real.pi := by
      intro j hj
      have hx : r ≤ p j := (Finset.mem_filter.1 hj).2
      have hs := slit_right hr hx
      have him : ((p j : ℂ) - conj z).im < 0 := by simp; linarith
      rw [show conj z - (p j : ℂ) = -((p j : ℂ) - conj z) by ring, Complex.arg_neg_eq_arg_add_pi_of_im_neg him,
        show (p j : ℂ) - conj z = conj ((p j : ℂ) - z) by simp, Complex.arg_conj]
      simp only [(Complex.mem_slitPlane_iff_arg.1 hs).1, ↓reduceIte]
      ring
    rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hRr, Finset.sum_add_distrib, hR z,
      Finset.sum_neg_distrib, Finset.sum_neg_distrib]
    linear_combination -hdata

/-- On `ℍ` the odd extension is the arg sum. -/
theorem oddExt_of_pos {z : ℂ} (hz : 0 < z.im) : oddExt p c c₀ z = argSum0 p c c₀ z := by
  simp only [oddExt, hz, ↓reduceIte]

theorem oddExt_conj (z : ℂ) : oddExt p c c₀ (conj z) = -oddExt p c c₀ z := by
  rcases lt_trichotomy 0 z.im with hpos | hzero | hneg
  · have h1 : ¬ 0 < (conj z).im := by simp; linarith
    have h2 : (conj z).im < 0 := by simp; linarith
    simp only [oddExt, h1, h2, ↓reduceIte, Complex.conj_conj, hpos]
  · have h0 : (conj z).im = 0 := by simp [← hzero]
    simp only [oddExt, h0, ← hzero, lt_irrefl, ↓reduceIte, neg_zero]
  · have h1 : 0 < (conj z).im := by simp; linarith
    have h2 : ¬ 0 < z.im := not_lt.2 hneg.le
    rw [oddExt_of_pos h1]
    simp only [oddExt, h2, hneg, ↓reduceIte, neg_neg]

/-- The arg sum is smooth off the real line. -/
theorem contDiffAt_argSum0 {z : ℂ} (hz : z.im ≠ 0) {n : ℕ∞} : ContDiffAt ℝ n (argSum0 p c c₀) z := by
  have he : argSum0 p c c₀ = fun z => c₀ + Complex.imCLM (∑ j, (c j : ℂ) * Complex.log (z - p j)) := by
    funext w
    simp only [argSum0, Complex.imCLM_apply, Complex.im_sum, Complex.im_ofReal_mul, Complex.log_im]
  rw [he]
  have hh : AnalyticAt ℂ (fun z : ℂ => ∑ j, (c j : ℂ) * Complex.log (z - p j)) z :=
    Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).clog
      (Complex.mem_slitPlane_iff.2 (Or.inr (by simpa using hz))))
  exact contDiffAt_const.add (Complex.imCLM.contDiff.contDiffAt.comp z (hh.contDiffAt.restrict_scalars ℝ))

end OddExt

/-! ### The cutoff field `f = χ · oddExt` -/

section CutF

variable {ι : Type*} [Fintype ι] {p c : ι → ℝ} {c₀ : ℝ}

/-- The configuration hypotheses: the marks avoid the closed `μ`-neighbourhoods of both cores, and the boundary
value of the arg sum vanishes on both cores. -/
structure CutConfig (P : CutParams) (p c : ι → ℝ) (c₀ : ℝ) : Prop where
  avoid0 : ∀ j, P.a₀ + P.μ < |p j|
  avoid1 : ∀ j, p j < P.a₁ - P.μ ∨ P.b₁ + P.μ < p j
  seed : c₀ + Real.pi * ∑ j ∈ Finset.univ.filter (fun j => 0 < p j), c j = 0
  core : c₀ + Real.pi * ∑ j ∈ Finset.univ.filter (fun j => P.b₁ + P.μ ≤ p j), c j = 0

/-- **The cutoff field** `f = χ · oddExt`. -/
def cutF (P : CutParams) (p c : ι → ℝ) (c₀ : ℝ) (z : ℂ) : ℝ := cutChi P z * oddExt p c c₀ z

/-- The holomorphic function with imaginary part `oddExt` off the real line. -/
def holOff (p c : ι → ℝ) (c₀ : ℝ) (σ : ℝ) (w : ℂ) : ℂ :=
  ((σ * c₀ : ℝ) : ℂ) * Complex.I + ∑ j, (c j : ℂ) * Complex.log (w - p j)

theorem oddExt_eq_im_holOff {w : ℂ} (hw : w.im ≠ 0) :
    oddExt p c c₀ w = (holOff p c c₀ (if 0 < w.im then 1 else -1) w).im := by
  have him : ∀ σ : ℝ, (holOff p c c₀ σ w).im = σ * c₀ + ∑ j, c j * Complex.arg (w - p j) := fun σ => by
    simp only [holOff, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_one, mul_zero, zero_mul, add_zero, Complex.im_sum, Complex.log_im]
  rcases lt_or_gt_of_ne hw with hneg | hpos
  · have h0 : ¬ 0 < w.im := not_lt.2 hneg.le
    simp only [oddExt, h0, hneg, ↓reduceIte, him, argSum0]
    have hc : ∀ j, Complex.arg (conj w - p j) = -Complex.arg (w - p j) := fun j => by
      have hs : w - p j ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.2 (Or.inr (by simp; linarith))
      rw [show conj w - (p j : ℂ) = conj (w - p j) by simp, Complex.arg_conj]
      simp [(Complex.mem_slitPlane_iff_arg.1 hs).1]
    simp only [hc, mul_neg, Finset.sum_neg_distrib]
    ring
  · simp only [oddExt_of_pos hpos, hpos, ↓reduceIte, him, argSum0, one_mul]

theorem analyticAt_holOff (σ : ℝ) {w : ℂ} (hw : w.im ≠ 0) : AnalyticAt ℂ (holOff p c c₀ σ) w :=
  analyticAt_const.add (Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul
    ((analyticAt_id.sub analyticAt_const).clog (Complex.mem_slitPlane_iff.2 (Or.inr (by simpa using hw)))))

/-- Off the real line `oddExt` is locally the imaginary part of a holomorphic function. -/
theorem oddExt_eventuallyEq_off {w : ℂ} (hw : w.im ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧ oddExt p c c₀ =ᶠ[𝓝 w] fun u => (g u).im := by
  refine ⟨holOff p c c₀ (if 0 < w.im then 1 else -1), analyticAt_holOff _ hw, ?_⟩
  rcases lt_or_gt_of_ne hw with hneg | hpos
  · have hev : ∀ᶠ u in 𝓝 w, u.im < 0 := (Complex.continuous_im.tendsto w).eventually (gt_mem_nhds hneg)
    filter_upwards [hev] with u hu
    rw [oddExt_eq_im_holOff hu.ne]
    simp [not_lt.2 hu.le, not_lt.2 hneg.le]
  · have hev : ∀ᶠ u in 𝓝 w, 0 < u.im := (Complex.continuous_im.tendsto w).eventually (lt_mem_nhds hpos)
    filter_upwards [hev] with u hu
    rw [oddExt_eq_im_holOff hu.ne']
    simp [hu, hpos]

/-- Across a core strip `oddExt` is locally the imaginary part of a holomorphic function. -/
theorem oddExt_eventuallyEq_core {l r : ℝ} (havoid : ∀ j, p j ≤ l ∨ r ≤ p j)
    (hdata : c₀ + Real.pi * ∑ j ∈ Finset.univ.filter (fun j => r ≤ p j), c j = 0) {w : ℂ} (hl : l < w.re)
    (hr : w.re < r) : AnalyticAt ℂ (holCore p c l r) w ∧
      oddExt p c c₀ =ᶠ[𝓝 w] fun u => (holCore p c l r u).im := by
  refine ⟨(Finset.analyticAt_fun_sum _ fun j hj => ?_).add (Finset.analyticAt_fun_sum _ fun j hj => ?_), ?_⟩
  · exact analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).clog
      (slit_left hl (Finset.mem_filter.1 hj).2))
  · exact analyticAt_const.mul ((analyticAt_const.sub analyticAt_id).clog
      (slit_right hr (Finset.mem_filter.1 hj).2))
  · have hev : ∀ᶠ u in 𝓝 w, l < u.re ∧ u.re < r :=
      ((Complex.continuous_re.tendsto w).eventually (lt_mem_nhds hl)).and
        ((Complex.continuous_re.tendsto w).eventually (gt_mem_nhds hr))
    filter_upwards [hev] with u hu
    rw [oddExt_eq_argCore havoid hdata hu.1 hu.2, argCore_eq_im_holCore]

/-- The two core strips of a configuration. -/
theorem CutConfig.local_hol (hP : P.Valid) (hC : CutConfig P p c c₀) {w : ℂ}
    (hw : |w.re| < P.a₀ + P.μ ∨ w.re ∈ Ioo (P.a₁ - P.μ) (P.b₁ + P.μ)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧ oddExt p c c₀ =ᶠ[𝓝 w] fun u => (g u).im := by
  classical
  rcases hw with h | h
  · have havoid : ∀ j, p j ≤ -(P.a₀ + P.μ) ∨ P.a₀ + P.μ ≤ p j := fun j => by
      rcases lt_abs.1 (hC.avoid0 j) with h' | h'
      · exact Or.inr h'.le
      · exact Or.inl (by linarith)
    have hfilt : Finset.univ.filter (fun j => P.a₀ + P.μ ≤ p j) = Finset.univ.filter (fun j => 0 < p j) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hj; linarith [hP.a₀_gt, hP.μ_pos]
      · intro hj
        rcases havoid j with h' | h'
        · linarith [hP.a₀_gt, hP.μ_pos]
        · exact h'
    have hdata : c₀ + Real.pi * ∑ j ∈ Finset.univ.filter (fun j => P.a₀ + P.μ ≤ p j), c j = 0 := by
      rw [hfilt]; exact hC.seed
    obtain ⟨ha, he⟩ := oddExt_eventuallyEq_core havoid hdata (by linarith [(abs_lt.1 h).1])
      (abs_lt.1 h).2
    exact ⟨_, ha, he⟩
  · have havoid : ∀ j, p j ≤ P.a₁ - P.μ ∨ P.b₁ + P.μ ≤ p j := fun j =>
      (hC.avoid1 j).imp le_of_lt le_of_lt
    obtain ⟨ha, he⟩ := oddExt_eventuallyEq_core havoid hC.core h.1 h.2
    exact ⟨_, ha, he⟩

/-- **The cutoff field is smooth.** -/
theorem contDiff_cutF (hP : P.Valid) (hC : CutConfig P p c c₀) {n : ℕ∞} : ContDiff ℝ n (cutF P p c c₀) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  have hol : ∀ {g : ℂ → ℂ}, AnalyticAt ℂ g z → oddExt p c c₀ =ᶠ[𝓝 z] (fun u => (g u).im) →
      ContDiffAt ℝ n (cutF P p c c₀) z := fun {g} hg he => by
    have hgd : ContDiffAt ℝ n (fun u => (g u).im) z :=
      Complex.imCLM.contDiff.contDiffAt.comp z (hg.contDiffAt.restrict_scalars ℝ)
    exact ((contDiff_cutChi (P := P)).contDiffAt.mul hgd).congr_of_eventuallyEq
      (he.mono fun u hu => by simp only [cutF, hu])
  by_cases hz : z.im ≠ 0
  · obtain ⟨g, hg, he⟩ := oddExt_eventuallyEq_off (p := p) (c := c) (c₀ := c₀) hz
    exact hol hg he
  · push Not at hz
    by_cases hcore : |z.re| < P.a₀ + P.μ ∨ z.re ∈ Ioo (P.a₁ - P.μ) (P.b₁ + P.μ)
    · obtain ⟨g, hg, he⟩ := hC.local_hol hP hcore
      exact hol hg he
    · push Not at hcore
      obtain ⟨h1, h2⟩ := hcore
      have hx : P.a₀ < |z.re| := by linarith [hP.μ_pos]
      have hx1 : z.re < P.a₁ ∨ P.b₁ < z.re := by
        by_contra h'
        push Not at h'
        exact h2 ⟨by linarith [hP.μ_pos, h'.1], by linarith [hP.μ_pos, h'.2]⟩
      have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz])
      have hev := cutChi_eq_zero_near hP hx hx1
      rw [← hzr] at hev
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hev] with u hu
      simp only [cutF, hu, zero_mul]

theorem hasCompactSupport_cutF (hP : P.Valid) : HasCompactSupport (cutF P p c c₀) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (P.R + 1)) fun z hz => by
    rw [mem_closedBall, dist_zero_right, not_le] at hz
    simp only [cutF, cutChi, LocalExt.cutoffFn_eq_zero hP.R_pos.le (by linarith) hz.le, zero_mul]

theorem cutF_conj (z : ℂ) : cutF P p c c₀ (conj z) = -cutF P p c c₀ z := by
  simp only [cutF, cutChi_conj, oddExt_conj, mul_neg]

/-- On the buffer the cutoff field is the odd extension, and on `ℍ ∩ N` it is the arg sum. -/
theorem cutF_eq_of_mem_cutN (hP : P.Valid) {z : ℂ} (hz : z ∈ cutN P) : cutF P p c c₀ z = oddExt p c c₀ z := by
  rw [cutF, cutChi_eq_one hP hz, one_mul]

/-- **The source vanishes on the buffer**: `Δ f = 0` on `N`. -/
theorem laplacian_cutF_eq_zero (hP : P.Valid) (hC : CutConfig P p c c₀) {z : ℂ} (hz : z ∈ cutN P) :
    Laplacian.laplacian (cutF P p c c₀) z = 0 := by
  have heq : cutF P p c c₀ =ᶠ[𝓝 z] oddExt p c c₀ := by
    filter_upwards [isOpen_cutN.mem_nhds hz] with w hw using cutF_eq_of_mem_cutN hP hw
  have harm : ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ oddExt p c c₀ =ᶠ[𝓝 z] fun u => (g u).im := by
    by_cases him : z.im ≠ 0
    · exact oddExt_eventuallyEq_off him
    · push Not at him
      refine hC.local_hol hP ?_
      obtain ⟨-, h⟩ := hz
      rcases h with h | h | h
      · rw [him, abs_zero] at h; linarith [hP.μ_pos]
      · left; linarith [hP.μ_pos]
      · right; exact ⟨by linarith [h.1, hP.μ_pos], by linarith [h.2, hP.μ_pos]⟩
  obtain ⟨g, hg, he⟩ := harm
  have hH := hg.harmonicAt_im
  rw [(InnerProductSpace.laplacian_congr_nhds (heq.trans he)).eq_of_nhds, hH.2.eq_of_nhds, Pi.zero_apply]

end CutF

/-! ### The inner buffer and the fillings of curves in it -/

/-- **The inner buffer** `U`: the disc of radius `R − μ`, above height `3μ` or over the cores shrunk by `2μ`. -/
def cutU (P : CutParams) : Set ℂ :=
  {z | ‖z‖ < P.R - P.μ ∧ (3 * P.μ < z.im ∨ |z.re| < P.a₀ - 2 * P.μ ∨ z.re ∈ Ioo (P.a₁ + 2 * P.μ) (P.b₁ - 2 * P.μ))}

theorem isOpen_cutU : IsOpen (cutU P) :=
  (isOpen_lt continuous_norm continuous_const).inter ((isOpen_lt continuous_const Complex.continuous_im).union
    ((isOpen_lt Complex.continuous_re.abs continuous_const).union (isOpen_Ioo.preimage Complex.continuous_re)))

/-- The closure of the inner buffer, intersected with `ℍ̄`, lies in the buffer. -/
theorem closure_cutU_inter_subset (hP : P.Valid) : closure (cutU P) ∩ Hbar ⊆ cutN P := by
  have hcl : closure (cutU P) ⊆ {z | ‖z‖ ≤ P.R - P.μ ∧ (3 * P.μ ≤ z.im ∨ |z.re| ≤ P.a₀ - 2 * P.μ ∨
      z.re ∈ Icc (P.a₁ + 2 * P.μ) (P.b₁ - 2 * P.μ))} := by
    refine closure_minimal (fun z hz => ⟨hz.1.le, ?_⟩) ?_
    · rcases hz.2 with h | h | h
      · exact Or.inl h.le
      · exact Or.inr (Or.inl h.le)
      · exact Or.inr (Or.inr ⟨h.1.le, h.2.le⟩)
    · exact (isClosed_le continuous_norm continuous_const).inter ((isClosed_le continuous_const
        Complex.continuous_im).union ((isClosed_le Complex.continuous_re.abs continuous_const).union
          (isClosed_Icc.preimage Complex.continuous_re)))
  rintro z ⟨hz, hzH⟩
  obtain ⟨h1, h2⟩ := hcl hz
  have hμ := hP.μ_pos
  have him : 0 ≤ z.im := hzH
  refine ⟨by linarith, ?_⟩
  rcases h2 with h | h | h
  · exact Or.inl (by rw [abs_of_nonneg him]; linarith)
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr ⟨by linarith [h.1], by linarith [h.2]⟩)

/-- **A compact set in the inner buffer meeting `ℝ` only at `0` has its filling in the inner buffer.** -/
theorem fillH_subset_cutU (hP : P.Valid) {C : Set ℂ} (hCc : IsCompact C) (hCU : C ⊆ cutU P) (hCH : C ⊆ Hbar)
    (hCR : ∀ z ∈ C, z.im = 0 → z = 0) : fillH C ⊆ cutU P := by
  have hμ := hP.μ_pos
  intro z hz
  have hzH : 0 < z.im := hz.1
  by_contra hzU
  have hCcl : closure C = C := hCc.isClosed.closure_eq
  -- an unbounded preconnected set through `z` avoiding `C`
  suffices ∃ S : Set ℂ, z ∈ S ∧ IsPreconnected S ∧ S ⊆ H \ C ∧ ¬ Bornology.IsBounded S by
    obtain ⟨S, hzS, hS, hSsub, hSb⟩ := this
    rw [← hCcl] at hSsub
    exact (subset_H_diff_fillH_of_isPreconnected hCc.isBounded hS hSsub hSb hzS).2 hz
  by_cases hfar : P.R - P.μ ≤ ‖z‖
  · -- the radial ray
    refine ⟨(fun t : ℝ => (t : ℂ) * z) '' Ici 1, ⟨1, mem_Ici.2 le_rfl, by simp⟩,
      (isPreconnected_Ici.image _ (by fun_prop)), ?_, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      have ht1 : (1 : ℝ) ≤ t := ht
      refine ⟨show 0 < ((t : ℂ) * z).im by simp; positivity, fun hC => ?_⟩
      have hn := (hCU hC).1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at hn
      nlinarith [norm_nonneg z]
    · intro hb
      obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hb
      have hz0 : 0 < ‖z‖ := norm_pos_iff.2 fun h => by rw [h, Complex.zero_im] at hzH; exact lt_irrefl 0 hzH
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ ⟨1, mem_Ici.2 le_rfl, rfl⟩)
      have h1 : (1 : ℝ) ≤ M / ‖z‖ + 1 := by
        have : 0 ≤ M / ‖z‖ := by positivity
        linarith
      have := hM _ ⟨M / ‖z‖ + 1, h1, rfl⟩
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), add_mul,
        div_mul_cancel₀ _ hz0.ne'] at this
      linarith
  · -- near the real line off the cores
    push Not at hfar
    have hlow3 : z.re ∉ Ioo (P.a₁ + 2 * P.μ) (P.b₁ - 2 * P.μ) := fun h => hzU ⟨hfar, Or.inr (Or.inr h)⟩
    have hlow2 : P.a₀ - 2 * P.μ ≤ |z.re| := by
      by_contra h; exact hzU ⟨hfar, Or.inr (Or.inl (not_le.1 h))⟩
    have hlow1 : z.im ≤ 3 * P.μ := by
      by_contra h; exact hzU ⟨hfar, Or.inl (not_le.1 h)⟩
    have hx0 : z.re ≠ 0 := fun h => by rw [h, abs_zero] at hlow2; linarith [hP.a₀_gt]
    -- every point above `Re z`, at height at most `Im z`, avoids `C`
    have hvert : ∀ y : ℝ, 0 < y → y ≤ z.im → ((z.re : ℂ) + y * Complex.I) ∉ C := by
      intro y hy hyz hC
      have hU := (hCU hC).2
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.I_re, mul_one, mul_zero, zero_add, Complex.add_re, Complex.mul_re, sub_zero, add_zero] at hU
      rcases hU with h | h | h
      · linarith
      · linarith
      · exact hlow3 h
    -- the side of `C` beyond `Re z` stays above a positive height `h₀`
    have hside : ∃ h₀ > 0, ∀ w ∈ C, (if 0 < z.re then z.re ≤ w.re else w.re ≤ z.re) → h₀ ≤ w.im := by
      set D : Set ℂ := C ∩ {w | if 0 < z.re then z.re ≤ w.re else w.re ≤ z.re} with hD
      have hDc : IsCompact D := by
        refine hCc.inter_right ?_
        split_ifs
        · exact isClosed_le continuous_const Complex.continuous_re
        · exact isClosed_le Complex.continuous_re continuous_const
      have hDpos : ∀ w ∈ D, 0 < w.im := by
        intro w hw
        have hwH : 0 ≤ w.im := hCH hw.1
        rcases hwH.lt_or_eq with h | h
        · exact h
        · have hw0 := hCR w hw.1 h.symm
          have hw2 := hw.2
          rw [hw0] at hw2
          simp only [Set.mem_ofPred_eq, Complex.zero_re] at hw2
          split_ifs at hw2 with hpos
          · linarith
          · exact (hx0 (le_antisymm (not_lt.1 hpos) hw2)).elim
      rcases D.eq_empty_or_nonempty with hDe | hDn
      · refine ⟨1, one_pos, fun w hw hw' => ?_⟩
        exact absurd (show w ∈ D from ⟨hw, hw'⟩) (by rw [hDe]; exact Set.notMem_empty w)
      · obtain ⟨w₀, hw₀, hmin⟩ := hDc.exists_isMinOn hDn Complex.continuous_im.continuousOn
        exact ⟨w₀.im, hDpos w₀ hw₀, fun w hw hw' => hmin ⟨hw, hw'⟩⟩
    obtain ⟨h₀, hh₀, hh₀C⟩ := hside
    set h : ℝ := min (h₀ / 2) z.im with hh
    have hhpos : 0 < h := lt_min (by positivity) hzH
    have hhz : h ≤ z.im := min_le_right _ _
    have hhh₀ : h < h₀ := (min_le_left _ _).trans_lt (by linarith)
    set σ : ℝ := if 0 < z.re then 1 else -1 with hσ
    set vert : Set ℂ := (fun y : ℝ => (z.re : ℂ) + y * Complex.I) '' Icc h z.im
    set horiz : Set ℂ := (fun t : ℝ => ((z.re + σ * t : ℝ) : ℂ) + h * Complex.I) '' Ici 0
    have hjoin : ((z.re : ℂ) + h * Complex.I) ∈ vert ∩ horiz :=
      ⟨⟨h, ⟨le_rfl, hhz⟩, rfl⟩, ⟨0, mem_Ici.2 le_rfl, by simp⟩⟩
    refine ⟨vert ∪ horiz, Or.inl ⟨z.im, ⟨hhz, le_rfl⟩, Complex.ext (by simp) (by simp)⟩,
      (isPreconnected_Icc.image _ (by fun_prop)).union _ hjoin.1 hjoin.2
        (isPreconnected_Ici.image _ (by fun_prop)), ?_, ?_⟩
    · rintro w (⟨y, hy, rfl⟩ | ⟨t, ht, rfl⟩)
      · refine ⟨show 0 < ((z.re : ℂ) + y * Complex.I).im by simp; linarith [hy.1], ?_⟩
        exact hvert y (hhpos.trans_le hy.1) hy.2
      · refine ⟨show 0 < (((z.re + σ * t : ℝ) : ℂ) + h * Complex.I).im by simp; exact hhpos, fun hC => ?_⟩
        have hside := hh₀C _ hC (by
          have ht0 : (0 : ℝ) ≤ t := ht
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
            Complex.I_im, mul_zero]
          split_ifs with hpos
          · simp only [hσ, hpos, ↓reduceIte, one_mul]; linarith
          · simp only [hσ, hpos, ↓reduceIte]; linarith)
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
          Complex.I_re, mul_one, mul_zero, zero_add] at hside
        linarith
    · intro hb
      obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hb
      have hσ1 : |σ| = 1 := by simp only [hσ]; split_ifs <;> simp
      have hM0' : 0 ≤ M := (norm_nonneg _).trans (hM _ (Or.inr ⟨0, mem_Ici.2 le_rfl, rfl⟩))
      have hpos' : (0 : ℝ) ≤ M + |z.re| + 1 := by positivity
      have ht := hM _ (Or.inr ⟨M + |z.re| + 1, mem_Ici.2 hpos', rfl⟩)
      have hre := (Complex.abs_re_le_norm _).trans ht
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
        Complex.I_im, mul_zero, add_zero, mul_one, sub_self] at hre
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ (Or.inr ⟨0, mem_Ici.2 le_rfl, rfl⟩))
      have : M + 1 ≤ |z.re + σ * (M + |z.re| + 1)| := by
        have h1 : |σ * (M + |z.re| + 1)| = M + |z.re| + 1 := by
          rw [abs_mul, hσ1, one_mul, abs_of_nonneg (by positivity)]
        have key := abs_add_le (z.re + σ * (M + |z.re| + 1)) (-z.re)
        rw [show z.re + σ * (M + |z.re| + 1) + -z.re = σ * (M + |z.re| + 1) by ring, h1, abs_neg] at key
        linarith
      linarith

/-! ### Uniform separation of an alive compact set from the driver -/

/-- `(u, z) ↦ f_u(z)` is continuous on `[0, t] × A` for the set `A` of points alive through `[0, t]`. -/
theorem continuousOn_fwdMap_alive {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (fun q : ℝ × ℂ => fwdMap W q.1 q.2) (Icc 0 t ×ˢ {z | ∃ u, IsForwardSol W z t u}) := by
  rintro ⟨r₀, z₀⟩ ⟨hr₀, u, hu⟩
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol ht hu
  set E := Real.exp (2 / δ ^ 2 * t) with hE
  have hE0 : 0 < E := Real.exp_pos _
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨η, hη, hη'⟩ := Metric.continuousWithinAt_iff.1 (hu.1 r₀ hr₀) (ε / 2) (by linarith)
  refine ⟨min η (min δ (ε / 2) / (2 * E)), by positivity, ?_⟩
  rintro ⟨r, z⟩ ⟨hr, v, hv⟩ hd
  rw [Prod.dist_eq] at hd
  have hdr : dist r r₀ < η := (le_max_left _ _).trans_lt (hd.trans_le (min_le_left _ _))
  have hdz : dist z z₀ < min δ (ε / 2) / (2 * E) :=
    (le_max_right _ _).trans_lt (hd.trans_le (min_le_right _ _))
  have hzz : ‖z - z₀‖ * E < min δ (ε / 2) / 2 := by
    rw [← dist_eq_norm]
    calc dist z z₀ * E < min δ (ε / 2) / (2 * E) * E := mul_lt_mul_of_pos_right hdz hE0
      _ = min δ (ε / 2) / 2 := by field_simp
  have hst := norm_sub_le_of_isForwardSol hW hu hv hδ ht le_rfl hlow
    (by linarith [min_le_left δ (ε / 2), hzz]) r hr
  have hexp : ‖z - z₀‖ * Real.exp (2 / δ ^ 2 * r) ≤ ‖z - z₀‖ * E :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hr.2 (by positivity)))
      (norm_nonneg _)
  simp only
  rw [dist_eq_norm, fwdMap_eq_of_isForwardSol hW hv hr, fwdMap_eq_of_isForwardSol hW hu hr₀]
  have h2 : ‖u r - u r₀‖ < ε / 2 := by rw [← dist_eq_norm]; exact hη' hr hdr
  calc ‖v r - u r₀‖ ≤ ‖v r - u r‖ + ‖u r - u r₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := by linarith [min_le_right δ (ε / 2)]
    _ = ε := by ring

/-- **A compact set of points alive through `[0, t]` stays at a positive distance from the driver.** -/
theorem exists_far {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) {K : Set ℂ} (hK : IsCompact K)
    (halive : ∀ z ∈ K, ∃ u, IsForwardSol W z t u) :
    ∃ m > 0, ∀ z ∈ K, ∀ u ∈ Icc (0 : ℝ) t, m ≤ ‖fwdMap W u z‖ := by
  rcases K.eq_empty_or_nonempty with hKe | hKn
  · exact ⟨1, one_pos, fun z hz => by rw [hKe] at hz; exact absurd hz (Set.notMem_empty z)⟩
  have hc : ContinuousOn (fun q : ℝ × ℂ => ‖fwdMap W q.1 q.2‖) (Icc 0 t ×ˢ K) :=
    continuous_norm.comp_continuousOn ((continuousOn_fwdMap_alive hW ht).mono
      (prod_mono le_rfl fun z hz => halive z hz))
  obtain ⟨q, hq, hmin⟩ := (isCompact_Icc.prod hK).exists_isMinOn
    ((nonempty_Icc.2 ht).prod hKn) hc
  obtain ⟨u, hu⟩ := halive q.2 hq.2
  refine ⟨‖fwdMap W q.1 q.2‖, ?_, fun z hz r hr => hmin (show (r, z) ∈ Icc 0 t ×ˢ K from ⟨hr, hz⟩)⟩
  rw [fwdMap_eq_of_isForwardSol hW hu hq.1]
  exact norm_pos_iff.2 (hu.2 q.1 hq.1).1

/-- `f_0(z) = z` for `z ≠ 0` (`W 0 = 0`). -/
theorem fwdMap_zero_time {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {z : ℂ} (hz : z ≠ 0) :
    fwdMap W 0 z = z := by
  have hsol : IsForwardSol W z 0 (fun _ => z) := by
    refine ⟨continuousOn_const, fun r hr => ⟨hz, ?_⟩⟩
    have : r = 0 := le_antisymm hr.2 hr.1
    subst this
    simp [hW0]
  exact fwdMap_eq_of_isForwardSol hW hsol ⟨le_rfl, le_rfl⟩

/-! ### The energy bound for the two-core cutoff -/

/-- **The energy bound of the comparison** (Aux. lemmas 61–62 in the field-free form): for a configuration of
marks admissible for the cutoff parameters there is a constant `C` such that, for every driver whose trace up to
time `t` stays in the inner buffer and meets `ℝ` only at `0`, and whose marks are alive through `[0, t]`,
`∫₀ˢ markDrift² ≤ C` for `s ≤ t`. -/
theorem exists_markDrift_energy_le {ι : Type*} [Fintype ι] {P : CutParams} (hP : P.Valid) {p c : ι → ℝ}
    {c₀ : ℝ} (hC : CutConfig P p c c₀) :
    ∃ C : ℝ, ∀ (W : ℝ → ℝ) (t : ℝ) (η : ℝ → ℂ), Continuous W → W 0 = 0 → 0 < t →
      ContinuousOn η (Icc 0 t) → (∀ s ∈ Ioc (0 : ℝ) t, fwdHull W s = fillH (η '' Icc 0 s)) →
      η '' Icc 0 t ⊆ cutU P → (∀ s ∈ Icc (0 : ℝ) t, η s ∈ Hbar ∧ ((η s).im = 0 → η s = 0)) →
      MarksAlive W p t → ∀ s ∈ Icc (0 : ℝ) t, ∫ u in (0 : ℝ)..s, markDrift W p c u ^ 2 ≤ C := by
  classical
  set f := cutF P p c c₀ with hf
  set v : ℂ → ℝ := H.indicator (QuantumZipper.K3.greenDensity f) with hv
  have hf2 : ContDiff ℝ 2 f := contDiff_cutF hP hC
  have hfc : HasCompactSupport f := hasCompactSupport_cutF hP
  have hvc : Continuous (QuantumZipper.K3.greenDensity f) := continuous_greenDensity hf2
  have hvs : HasCompactSupport (QuantumZipper.K3.greenDensity f) := hasCompactSupport_greenDensity hfc
  obtain ⟨Cv₀, hCv₀⟩ := hvs.exists_bound_of_continuous hvc
  set Cv := max Cv₀ 0 with hCv
  have hHm : MeasurableSet H := (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hvb : ∀ z, |v z| ≤ Cv := fun z => by
    by_cases hz : z ∈ H
    · rw [hv, Set.indicator_of_mem hz, ← Real.norm_eq_abs]; exact (hCv₀ z).trans (le_max_left _ _)
    · rw [hv, Set.indicator_of_notMem hz, abs_zero]; exact le_max_right _ _
  have hΔN : ∀ z ∈ cutN P, QuantumZipper.K3.greenDensity f z = 0 := fun z hz => by
    rw [QuantumZipper.K3.greenDensity, laplacian_cutF_eq_zero hP hC hz, mul_zero]
  have hvN : ∀ z, v z ≠ 0 → z ∉ cutN P := fun z hz hzN => by
    apply hz
    by_cases hzH : z ∈ H
    · rw [hv, Set.indicator_of_mem hzH, hΔN z hzN]
    · rw [hv, Set.indicator_of_notMem hzH]
  have htsupN : Disjoint (tsupport (QuantumZipper.K3.greenDensity f)) (cutN P) := by
    rw [Set.disjoint_right]
    intro z hzN hzt
    have hev : QuantumZipper.K3.greenDensity f =ᶠ[𝓝 z] 0 := by
      filter_upwards [isOpen_cutN.mem_nhds hzN] with w hw
      rw [hΔN w hw, Pi.zero_apply]
    exact (notMem_tsupport_iff_eventuallyEq.2 hev) hzt
  have hvH : ∀ z, v z ≠ 0 → z ∈ H := fun z hz => by
    by_contra hzH; exact hz (by rw [hv, Set.indicator_of_notMem hzH])
  have hvt : ∀ z, v z ≠ 0 → z ∈ tsupport (QuantumZipper.K3.greenDensity f) ∩ Hbar := fun z hz =>
    ⟨subset_tsupport _ fun h0 => hz (by rw [hv, Set.indicator_of_mem (hvH z hz), h0]),
      show (0 : ℝ) ≤ z.im from le_of_lt (hvH z hz)⟩
  have hsupR : ∀ z, v z ≠ 0 → ‖z‖ ≤ P.R + 1 := fun z hz => by
    have h1 := QuantumZipper.K3.tsupport_greenDensity_subset f (hvt z hz).1
    have hsub : tsupport f ⊆ closedBall 0 (P.R + 1) :=
      closure_minimal (fun w hw => by
        by_contra hwb
        rw [mem_closedBall, dist_zero_right, not_le] at hwb
        exact hw (by simp only [hf, cutF, cutChi, LocalExt.cutoffFn_eq_zero hP.R_pos.le (by linarith) hwb.le,
          zero_mul])) isClosed_closedBall
    have := hsub h1
    rwa [mem_closedBall, dist_zero_right] at this
  have hInt : Integrable v := (hvc.integrable_of_hasCompactSupport hvs).indicator hHm
  refine ⟨2 * IsSrc.greenBound Cv (P.R + 1) * ∫ z, |v z|, ?_⟩
  intro W t η hW hW0 ht hηc hfill hηU hηH hp s hs
  -- the hull stays in the buffer
  have hKt : fwdHull W t = fillH (η '' Icc 0 t) := hfill t ⟨ht, le_rfl⟩
  have hcpt : IsCompact (η '' Icc 0 t) := isCompact_Icc.image_of_continuousOn hηc
  have hKU : fwdHull W t ⊆ cutU P := by
    rw [hKt]
    refine fillH_subset_cutU hP hcpt hηU ?_ ?_
    · rintro _ ⟨r, hr, rfl⟩; exact (hηH r hr).1
    · rintro _ ⟨r, hr, rfl⟩ h0; exact (hηH r hr).2 h0
  have hKN : closure (fwdHull W t) ⊆ cutN P := by
    intro z hz
    refine closure_cutU_inter_subset hP ⟨closure_mono hKU hz, ?_⟩
    have : closure (fwdHull W t) ⊆ Hbar := by
      rw [← closure_H]; exact closure_mono (QuantumZipper.fwdHull_mono.2 t)
    exact this hz
  -- the source is admissible
  have halive : ∀ z ∈ tsupport (QuantumZipper.K3.greenDensity f) ∩ Hbar, ∃ u, IsForwardSol W z t u := by
    rintro z ⟨hzt, hzH⟩
    have hzN : z ∉ cutN P := Set.disjoint_left.1 htsupN hzt
    rcases (show (0 : ℝ) ≤ z.im from hzH).lt_or_eq with hpos | hzero
    · exact Ito.exists_isForwardSol_of_mem ht.le ⟨hpos, fun hK => hzN (hKN (subset_closure hK))⟩
    · have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [← hzero])
      have hz0 : z.re ≠ 0 := fun h => hzN (by rw [hzr, h, Complex.ofReal_zero]; exact zero_mem_cutN hP)
      have hzcl : z ∉ closure (fwdHull W t) := fun h => hzN (hKN h)
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hzcl
      have hd : Disjoint (ball ((z.re : ℝ) : ℂ) r) (fwdHull W t) := by
        rw [← hzr]
        exact Set.disjoint_left.2 fun w hw hwK => hball hw (subset_closure hwK)
      obtain ⟨u, hu⟩ := ZhanGT4.exists_isForwardSol_of_disjoint_ball hW hW0 hz0 ht.le hr hd
      exact ⟨u, by rw [hzr]; exact hu⟩
  obtain ⟨m, hm, hmfar⟩ := exists_far hW ht.le ((hvs.isCompact).inter_right
    (isClosed_le continuous_const Complex.continuous_im)) halive
  have hsrc : IsSrc W v t Cv (P.R + 1) m :=
    { meas := hvc.measurable.indicator hHm
      bound := hvb
      m_pos := hm
      alive := fun z hz => ⟨hvH z hz, fun hK => hvN z hz (hKN (subset_closure hK))⟩
      norm_le := hsupR
      far := fun z hz u hu => hmfar z (hvt z hz) u hu }
  have hp0 : ∀ j, (p j : ℂ) ≠ 0 := fun j => by
    obtain ⟨u, hu⟩ := hp j
    exact ne_zero_of_isForwardSol hW0 ht.le hu
  have hI : IdentHyp W t η p c c₀ v Cv (P.R + 1) m f (cutN P) :=
    { cont := hW
      zero := hW0
      t_pos := ht
      trace_cont := hηc
      fill := hfill
      marks := hp
      seed := hC.seed
      src := hsrc
      open_N := isOpen_cutN
      hull_N := hKN
      zero_N := zero_mem_cutN hP
      src_N := hvN
      green := fun y _ => integral_greenH_mul_indicator_greenDensity hf2 hfc (fun z => cutF_conj z) y
      f_eq := fun y ⟨hyN, hyH⟩ => by
        have hy0 : y ≠ 0 := fun h => by
          have : (0 : ℝ) < y.im := hyH
          rw [h, Complex.zero_im] at this; exact lt_irrefl 0 this
        rw [hf, cutF_eq_of_mem_cutN hP hyN, oddExt_of_pos hyH, argSum0, argSum, fwdMap_zero_time hW hW0 hy0]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [fwdMap_zero_time hW hW0 (hp0 j)] }
  have heq : ∫ u in (0 : ℝ)..s, markDrift W p c u ^ 2 = ∫ u in (0 : ℝ)..s, srcDrift W v u ^ 2 := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hs.1] at hu
    rw [srcDrift_eq_markDrift hI ⟨hu.1, hu.2.trans hs.2⟩]
  rw [heq]
  exact integral_srcDrift_sq_le hW hsrc hs

end GB7a

end InteractingSLE
