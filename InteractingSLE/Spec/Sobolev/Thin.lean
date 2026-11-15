import InteractingSLE.Spec.Sobolev.Cutoff
import Mathlib.Analysis.Distribution.Support

/-!
# Aux. lemma 12: a small-dimensional set supports no `H^{-ε}_loc` distribution

Source: `source/spec/p049-096.md`, Aux. lemma 12 (`#aux-12`, p. 84) and its proof (pp. 84–85):
let `0 < ε < 1`, let `E` be a relatively closed subset of an open set `U ⊆ ℝ²` with
`dim_H(E ∩ K) < 2 - 2ε` for every compact `K ⋐ U` (SR3); if `T ∈ H^{-ε}_loc(U)` is supported on
`E`, then `T = 0`.

Formalization: `U : Opens ℂ`; `E` relatively closed in `U` is `closure E ∩ U ⊆ E`; (SR3) uses
Mathlib's `dimH`; `T ∈ H^{-ε}_loc(U)` is `IsLocNegSobolev ε T` (the Fourier definition,
`InteractingSLE.Sobolev.negSobolevSq`); "`T` supported on `E`" is: `T φ = 0` for every test
function whose support is disjoint from `E` (equivalently `Distribution.IsVanishingOn T Eᶜ`).

Proof (the source's cutoff argument): fix `φ ∈ 𝓓(U)` and `E₀ = E ∩ tsupport φ` (compact, of zero
`(2-2ε)`-dimensional Hausdorff measure). For every `δ > 0` a smooth `v_δ` with `0 ≤ v_δ ≤ 1`,
`v_δ = 1` near `E₀` and `‖v_δ‖²₂ + [v_δ]²_ε ≤ Cδ` exists (`exists_small_cutoff`); then
`T φ = T(φ v_δ)` because `φ(1 - v_δ)` vanishes near `E`, and with a cutoff `ζ = 1` on `tsupport φ`,
`T(φ v_δ)² ≤ 4 ‖ζT‖²_{H^{-ε}} ‖φ v_δ‖²_{H^ε} ≤ C' δ` (duality, (SR4), and multiplication by `φ`).

## Main results

* `eq_zero_of_isLocNegSobolev_of_dimH_lt` : Aux. lemma 12;
* `eq_zero_of_isVanishingOn` : the same with Mathlib's `Distribution.IsVanishingOn`;
* `eq_of_isLocNegSobolev_of_eq_off` : two `H^{-ε}_loc` distributions that agree off `E` agree.
-/

noncomputable section

open MeasureTheory Set Filter Topology Function Real Metric
open scoped Distributions ContDiff ENNReal NNReal

namespace InteractingSLE.Sobolev

open LQGMetric TopologicalSpace

theorem exists_lipschitz_of_contDiff {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∃ L : ℝ, ∀ x y, |f x - f y| ≤ L * ‖x - y‖ := by
  have hc : Continuous (fun x => fderiv ℝ f x) := hf.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support (hfc.fderiv (𝕜 := ℝ))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hL : LipschitzWith ⟨C, hC0⟩ f :=
    lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by simp)) fun x => hC x
  refine ⟨C, fun x y => ?_⟩
  have := hL.dist_le_mul x y
  rwa [Real.dist_eq, dist_eq_norm] at this

theorem eq_zero_of_le_mul_ofReal {X K : ℝ≥0∞} (hK : K ≠ ⊤)
    (h : ∀ δ : ℝ, 0 < δ → X ≤ K * ENNReal.ofReal δ) : X = 0 := by
  have h1 : Tendsto ENNReal.ofReal (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  have h2 : Tendsto (fun δ : ℝ => K * ENNReal.ofReal δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul h1 (Or.inr hK)
    simpa using this
  exact le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds h2
    (eventually_nhdsWithin_of_forall fun δ hδ => h δ hδ)) bot_le

/-- The constant in `‖φ v‖²_{H^ε} ≤ B (‖v‖²₂ + [v]²_ε)`. -/
theorem sobolevSq_mul_le {φ v : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hv : ContDiff ℝ ∞ v) {M L : ℝ} (hM : ∀ x, |φ x| ≤ M) (hL : ∀ x y, |φ x - φ y| ≤ L * ‖x - y‖)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    sobolevSq ε (fun x => φ x * v x) ≤
      (ENNReal.ofReal (M ^ 2) + (ENNReal.ofReal (gagConst ε))⁻¹ * (ENNReal.ofReal (2 * M ^ 2) +
        ENNReal.ofReal (2 * max 1 (4 * M ^ 2)) * gagJ ε L)) * (l2Sq v + gagSq ε v) := by
  have hψ : ContDiff ℝ ∞ (fun x => φ x * v x) := hφ.mul hv
  refine (sobolevSq_le_l2Sq_add_gagSq hψ hφc.mul_right hε0 hε1).trans ?_
  have h1 := l2Sq_mul_le (v := v) hM
  have h2 := gagSq_mul_le hv.continuous hM hL ε
  set c := (ENNReal.ofReal (gagConst ε))⁻¹
  set a := ENNReal.ofReal (M ^ 2)
  set b := ENNReal.ofReal (2 * M ^ 2)
  set e := ENNReal.ofReal (2 * max 1 (4 * M ^ 2)) * gagJ ε L
  calc l2Sq (fun x => φ x * v x) + c * gagSq ε (fun x => φ x * v x)
      ≤ a * l2Sq v + c * (b * gagSq ε v + e * l2Sq v) := by gcongr
    _ ≤ (a + c * (b + e)) * (l2Sq v + gagSq ε v) := by
        have : a * l2Sq v + c * (b * gagSq ε v + e * l2Sq v) =
            a * l2Sq v + c * b * gagSq ε v + c * e * l2Sq v := by ring
        rw [this]
        have h3 : (a + c * (b + e)) * (l2Sq v + gagSq ε v) =
            a * l2Sq v + a * gagSq ε v + c * b * l2Sq v + c * b * gagSq ε v +
              c * e * l2Sq v + c * e * gagSq ε v := by ring
        rw [h3]
        calc a * l2Sq v + c * b * gagSq ε v + c * e * l2Sq v
            ≤ a * l2Sq v + c * b * gagSq ε v + c * e * l2Sq v +
                (a * gagSq ε v + c * b * l2Sq v + c * e * gagSq ε v) := le_self_add
          _ = _ := by ring

variable {U : Opens ℂ}

/-- Aux. lemma 12 from the local `H^{-ε}` bound of `T` through *some* cutoff equal to `1` on the
support of each test function (the form in which conditional means are a.s. regular: for a
countable family of cutoffs). -/
theorem eq_zero_of_cutoff_bound_of_dimH_lt {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {E : Set ℂ} (hE : closure E ∩ U ⊆ E)
    (hdim : ∀ K, IsCompact K → K ⊆ U → dimH (E ∩ K) < ENNReal.ofReal (2 - 2 * ε))
    {T : DistOn U}
    (hT : ∀ φ : TestOn U, ∃ ζ : TestOn U, EqOn ζ 1 (tsupport φ) ∧ negSobolevSq ε T ζ < ⊤)
    (hsupp : ∀ φ : TestOn U, Disjoint (tsupport φ) E → T φ = 0) : T = 0 := by
  refine ContinuousLinearMap.ext fun φ => ?_
  change T φ = 0
  set K₀ := tsupport φ
  have hK₀ : IsCompact K₀ := φ.hasCompactSupport
  have hK₀U : K₀ ⊆ U := φ.tsupport_subset
  set E₀ := E ∩ K₀
  have hE₀eq : E₀ = closure E ∩ K₀ := by
    refine Subset.antisymm (inter_subset_inter_left _ subset_closure) fun x hx => ⟨?_, hx.2⟩
    exact hE ⟨hx.1, hK₀U hx.2⟩
  have hE₀ : IsCompact E₀ := by rw [hE₀eq]; exact hK₀.inter_left isClosed_closure
  have hH : μH[2 - 2 * ε] E₀ = 0 := by
    have h := hausdorffMeasure_of_dimH_lt (s := E₀) (d := (2 - 2 * ε).toNNReal)
      (hdim K₀ hK₀ hK₀U)
    rwa [Real.coe_toNNReal _ (by linarith)] at h
  obtain ⟨C, hC, hcut⟩ := exists_small_cutoff hε0 hε1 hE₀ hH
  obtain ⟨ζ, hζ1, hN⟩ := hT φ
  obtain ⟨M, hM⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  obtain ⟨L, hL⟩ := exists_lipschitz_of_contDiff φ.contDiff φ.hasCompactSupport
  have hM' : ∀ x, |φ x| ≤ M := fun x => by rw [← Real.norm_eq_abs]; exact hM x
  set B := ENNReal.ofReal (M ^ 2) + (ENNReal.ofReal (gagConst ε))⁻¹ * (ENNReal.ofReal (2 * M ^ 2) +
    ENNReal.ofReal (2 * max 1 (4 * M ^ 2)) * gagJ ε L)
  have hB : B ≠ ⊤ := by
    have hc : ENNReal.ofReal (gagConst ε) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact gagConst_pos ε
    exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.2 hc) (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (gagJ_lt_top hε0 hε1 L).ne⟩)⟩
  have key : ∀ δ : ℝ, 0 < δ → ENNReal.ofReal (T φ ^ 2) ≤
      (4 * negSobolevSq ε T ζ * B * C) * ENNReal.ofReal δ := by
    intro δ hδ
    obtain ⟨v, hv, -, ⟨O, hO, hE₀O, hvO⟩, hvC⟩ := hcut δ hδ
    have hψ : ContDiff ℝ ∞ (fun x => φ x * v x) := φ.contDiff.mul hv
    set χ₁ := mulTest ζ hψ
    have hχ₁ : ∀ x, χ₁ x = φ x * v x := by
      intro x
      rw [mulTest_apply]
      by_cases hx : x ∈ K₀
      · rw [hζ1 hx, Pi.one_apply, one_mul]
      · rw [image_eq_zero_of_notMem_tsupport hx]; ring
    have hχ₂ : T (φ - χ₁) = 0 := by
      refine hsupp _ (Set.disjoint_left.2 fun x hx hxE => ?_)
      have hsub : support (⇑(φ - χ₁)) ⊆ K₀ := fun y hy => by
        by_contra h
        apply hy
        change φ y - χ₁ y = 0
        rw [hχ₁, image_eq_zero_of_notMem_tsupport h]; ring
      have hxK : x ∈ K₀ := closure_minimal hsub (isClosed_tsupport _) hx
      have hxO : x ∈ O := hE₀O ⟨hxE, hxK⟩
      have hzero : ⇑(φ - χ₁) =ᶠ[𝓝 x] 0 := by
        filter_upwards [hO.mem_nhds hxO] with y hy
        change φ y - χ₁ y = 0
        rw [hχ₁, hvO hy, Pi.one_apply]; ring
      exact (notMem_tsupport_iff_eventuallyEq.2 hzero) hx
    have hTφ : T φ = T χ₁ := by
      have : φ = χ₁ + (φ - χ₁) := (add_sub_cancel χ₁ φ).symm
      conv_lhs => rw [this, map_add, hχ₂, add_zero]
    rw [hTφ]
    calc ENNReal.ofReal (T χ₁ ^ 2)
        ≤ 4 * negSobolevSq ε T ζ * sobolevSq ε (fun x => φ x * v x) :=
          sq_apply_mulTest_le T ζ hψ φ.hasCompactSupport.mul_right ε
      _ ≤ 4 * negSobolevSq ε T ζ * (B * (l2Sq v + gagSq ε v)) := by
          gcongr
          exact sobolevSq_mul_le φ.contDiff φ.hasCompactSupport hv hM' hL hε0 hε1.le
      _ ≤ 4 * negSobolevSq ε T ζ * (B * (C * ENNReal.ofReal δ)) := by gcongr
      _ = 4 * negSobolevSq ε T ζ * B * C * ENNReal.ofReal δ := by ring
  have hK : 4 * negSobolevSq ε T ζ * B * C ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hN.ne) hB) hC
  have h0 := eq_zero_of_le_mul_ofReal hK key
  rw [ENNReal.ofReal_eq_zero] at h0
  nlinarith [sq_nonneg (T φ)]

/-- **Aux. lemma 12** (a small-dimensional set supports no such distribution). Let `0 < ε < 1`,
let `E` be relatively closed in `U` with `dim_H(E ∩ K) < 2 - 2ε` for every compact `K ⊆ U`
(SR3). A distribution `T ∈ H^{-ε}_loc(U)` supported on `E` vanishes. -/
theorem eq_zero_of_isLocNegSobolev_of_dimH_lt {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {E : Set ℂ} (hE : closure E ∩ U ⊆ E)
    (hdim : ∀ K, IsCompact K → K ⊆ U → dimH (E ∩ K) < ENNReal.ofReal (2 - 2 * ε))
    {T : DistOn U} (hT : IsLocNegSobolev ε T)
    (hsupp : ∀ φ : TestOn U, Disjoint (tsupport φ) E → T φ = 0) : T = 0 :=
  eq_zero_of_cutoff_bound_of_dimH_lt hε0 hε1 hE hdim (fun φ => by
    obtain ⟨ζ, -, hζ1⟩ := exists_cutoff_testOn φ.hasCompactSupport φ.tsupport_subset
    exact ⟨ζ, hζ1, hT ζ⟩) hsupp

/-- Aux. lemma 12 with "`T` supported on `E`" in Mathlib's form `Distribution.IsVanishingOn T Eᶜ`. -/
theorem eq_zero_of_isVanishingOn {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {E : Set ℂ} (hE : closure E ∩ U ⊆ E)
    (hdim : ∀ K, IsCompact K → K ⊆ U → dimH (E ∩ K) < ENNReal.ofReal (2 - 2 * ε))
    {T : DistOn U} (hT : IsLocNegSobolev ε T) (hsupp : Distribution.IsVanishingOn (⇑T) Eᶜ) :
    T = 0 :=
  eq_zero_of_isLocNegSobolev_of_dimH_lt hε0 hε1 hE hdim hT fun φ hφ =>
    hsupp φ (subset_compl_iff_disjoint_right.2 hφ)

theorem fourierSq_neg (T : DistOn U) (ζ : TestOn U) (ξ : ℂ) : fourierSq (-T) ζ ξ = fourierSq T ζ ξ := by
  simp [fourierSq]

theorem IsLocNegSobolev.neg {ε : ℝ} {T : DistOn U} (hT : IsLocNegSobolev ε T) :
    IsLocNegSobolev ε (-T) := fun ζ => by
  have : negSobolevSq ε (-T) ζ = negSobolevSq ε T ζ := by simp only [negSobolevSq, fourierSq_neg]
  rw [this]; exact hT ζ

theorem IsLocNegSobolev.sub {ε : ℝ} {T S : DistOn U} (hT : IsLocNegSobolev ε T)
    (hS : IsLocNegSobolev ε S) : IsLocNegSobolev ε (T - S) := by
  rw [sub_eq_add_neg]; exact hT.add hS.neg

/-- Two distributions of `H^{-ε}_loc(U)` that agree off a set `E` as in Aux. lemma 12 agree (the
injectivity of the restriction off a thin set, as used after Aux. lemma 12 in the specification). -/
theorem eq_of_isLocNegSobolev_of_eq_off {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {E : Set ℂ} (hE : closure E ∩ U ⊆ E)
    (hdim : ∀ K, IsCompact K → K ⊆ U → dimH (E ∩ K) < ENNReal.ofReal (2 - 2 * ε))
    {T S : DistOn U} (hT : IsLocNegSobolev ε T) (hS : IsLocNegSobolev ε S)
    (h : ∀ φ : TestOn U, Disjoint (tsupport φ) E → T φ = S φ) : T = S := by
  have := eq_zero_of_isLocNegSobolev_of_dimH_lt hε0 hε1 hE hdim (hT.sub hS) fun φ hφ => by
    rw [sub_apply, h φ hφ, sub_self]
  exact sub_eq_zero.1 this

end InteractingSLE.Sobolev
