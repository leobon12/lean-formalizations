/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Prop61
import InteractingSLE.WangWu.UnboundedComponent

/-!
# Proposition 6.1: every component, bounded or not (Aux. 27 at `∞` + Aux. 28)

Packet PROVE-SEC6-D, item (R1) of `planning/handoffs/PROVE-SEC6-C.md` (specification §6.1,
`source/spec/p145-192.md`, `#prop-6.1-proof` pp. 166–169).

The proof of Proposition 6.1 identifies the conditional mean on the **remaining** component of
`ℍ ∖ A(τ)` (to the right of `η_{θ₂}`; it contains the future tail, so in `ℍ` it is unbounded). The
source handles `∞` by working in the strip and mapping to the disk: "To include the remaining
component of the strip in the growth argument, choose a deterministic conformal map `ψ : 𝒮 → 𝔻` …
All complementary components in these coordinates are bounded … Apply **Aux.** lemma 27 and then
**Aux.** lemma 28 to each component" (pp. 168–169). PROVE-SEC6-C proved the identification for
bounded components only (Aux. 27 is a bound on bounded windows).

Here the transport to a bounded picture is done once and for all by Wang–Wu's Lemma 4.6 on all of
`ℍ` (`WangWu.ae_abs_le_log_global_of_condMean`, landed: the window bound for the field and for its
transport by the `ℍ`-automorphism `z ↦ −1/z`), which gives for the local-set mean the global bound
`|𝒞_A(z)| ≤ K (1 + log(1 + |z|) + log(1 + 1/dist(z, A ∪ ℝ)))`. The Riemann map of a component
grows at most polynomially in `1/(1 − |ζ|)` (Koebe), so this bound is logarithmic in the disk, as is
the `arg φ'` term of the candidate; Wang–Wu's Lemma 4.7 (`WangWu.eqOn_zero_of_log_growth`) then
replaces the disk step of Aux. 28.

* `aux28_eqOn_of_tendsto_disk_of_log_growth` : Aux. lemma 28 (simply connected form, prime ends
  read in the disk) with the growth hypothesis `|H(z)| ≤ K (1 + log(1 + |z|) + log(1 + 1/dist(z, ∂C)))`
  — no boundedness of `C`.
* `ae_abs_le_log_global_of_isLocalSetMean` : the global bound for the project's local-set mean.
* `ae_eqOn_component_of_tendsto_global` : PROVE-SEC6-C's `ae_eqOn_component_of_tendsto` for every
  component, bounded or not (the deterministic mean `F` bounded on `ℍ`).
* `ae_eqOn_component_union_of_tendsto_global`, `ae_eqOn_component_of_subset_of_tendsto_global` : the
  full-union and stopped-inside-full assemblies of `Prop61.lean` for every component.
* `ae_condExp_exp_eq_of_component_of_tendsto_global` : the Gaussian law on any component.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal Real

namespace InteractingSLE.Sec6

open QuantumZipper (H)
open LQGMetric (DistOn TestOn CondIndepEv)
open SupercriticalConformalCovariance (IsConformalBijection)
open LocalSets QuantumZipper.CA.Koebe

/-! ### Deterministic: Aux. 28 with logarithmic growth at `∞` -/

section Deterministic

/-- **Disk growth of a function with logarithmic growth on `C`.** If `f : 𝔻 → C` is a Riemann map
and `|H(z)| ≤ K (1 + log(1 + |z|) + log(1 + 1/dist(z, ∂C)))` on `C`, then `|H(f(ζ))|` is at most a
constant times `1 + log(1/(1 − |ζ|))`: Koebe's distance estimate `dist(f(ζ), ∂C) ≥ κ (1 − |ζ|)^p`
and growth theorem `|f(ζ)| ≤ |f(0)| + |f'(0)| (1 − |ζ|)^{−p₀}`. (The step inside Wang–Wu's
`eqOn_of_log_norm_growth_of_tendsto`, isolated.) -/
theorem exists_abs_comp_le_log_of_log_norm_growth {C : Set ℂ} (hCo : IsOpen C) {f : ℂ → ℂ}
    (hf : IsConformalBijection f (ball 0 1) C) {Hh : ℂ → ℝ} {K : ℝ}
    (hgrowth : ∀ z ∈ C, |Hh z| ≤
      K * (1 + Real.log (1 + ‖z‖) + Real.log (1 + (infDist z (frontier C))⁻¹))) :
    ∃ K' : ℝ, ∀ ζ ∈ ball (0 : ℂ) 1, |Hh (f ζ)| ≤ K' * (1 + Real.log (1 / (1 - ‖ζ‖))) := by
  obtain ⟨hfd, hfb⟩ := hf
  have hfinj := hfb.injOn
  have hfim : f '' ball 0 1 = C := hfb.image_eq
  have hball0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hCne : C.Nonempty := ⟨f 0, hfb.mapsTo hball0⟩
  have hCuniv : C ≠ univ := hfim ▸ QuantumZipper.CA.Koebe.image_ball_ne_univ one_pos hfd hfinj
  set κ := koebeCovConst * ‖deriv f 0‖
  have hκ : 0 < κ := mul_pos koebeCovConst_pos
    (norm_pos_iff.2 (QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn isOpen_ball hfd hfinj hball0))
  set p : ℝ := 1 + koebeDistExp
  have hp0 : 0 < koebeDistExp := koebeDistExp_pos
  have hp : 0 < p := by simp only [p]; linarith
  have hdist : ∀ ζ ∈ ball (0 : ℂ) 1, κ * (1 - ‖ζ‖) ^ p ≤ infDist (f ζ) (frontier C) := by
    intro ζ hζ
    have := koebe_mul_pow_le_infDist hfd hfinj hζ
    rw [hfim] at this
    exact this.trans (infDist_compl_le_infDist_frontier hCo hCne hCuniv _)
  set A₀ : ℝ := 1 + ‖f 0‖ + ‖deriv f 0‖
  have hA₀ : 1 ≤ A₀ := by simp only [A₀]; linarith [norm_nonneg (f 0), norm_nonneg (deriv f 0)]
  have hgrow : ∀ ζ ∈ ball (0 : ℂ) 1,
      Real.log (1 + ‖f ζ‖) ≤ Real.log A₀ + koebeDistExp * Real.log (1 / (1 - ‖ζ‖)) := by
    intro ζ hζ
    have hz1 : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
    have hr : 0 < 1 - ‖ζ‖ := by linarith
    have hr1 : 1 - ‖ζ‖ ≤ 1 := by linarith [norm_nonneg ζ]
    have hy : 0 < (1 - ‖ζ‖) ^ koebeDistExp := Real.rpow_pos_of_pos hr _
    have hy1 : (1 - ‖ζ‖) ^ koebeDistExp ≤ 1 := Real.rpow_le_one hr.le hr1 hp0.le
    have h := QuantumZipper.CA.Koebe.norm_sub_le_growth_global hfd hfinj hζ
    rw [dist_zero_right, div_one, Real.rpow_neg hr.le] at h
    have hfz : 1 + ‖f ζ‖ ≤ A₀ * ((1 - ‖ζ‖) ^ koebeDistExp)⁻¹ := by
      have hX : 1 ≤ ((1 - ‖ζ‖) ^ koebeDistExp)⁻¹ := one_le_inv₀ hy |>.2 hy1
      have h1 : ‖f ζ‖ ≤ ‖f 0‖ + ‖f ζ - f 0‖ := by
        have := norm_add_le (f 0) (f ζ - f 0)
        rwa [add_sub_cancel] at this
      have h2 : ‖ζ‖ * (‖deriv f 0‖ * ((1 - ‖ζ‖) ^ koebeDistExp)⁻¹) ≤
          ‖deriv f 0‖ * ((1 - ‖ζ‖) ^ koebeDistExp)⁻¹ :=
        mul_le_of_le_one_left (by positivity) hz1.le
      simp only [A₀]
      nlinarith [norm_nonneg (f 0), norm_nonneg (deriv f 0)]
    calc Real.log (1 + ‖f ζ‖) ≤ Real.log (A₀ * ((1 - ‖ζ‖) ^ koebeDistExp)⁻¹) :=
          Real.log_le_log (by positivity) hfz
      _ = Real.log A₀ + koebeDistExp * Real.log (1 / (1 - ‖ζ‖)) := by
          rw [Real.log_mul (by linarith) (inv_pos.2 hy).ne', Real.log_inv, Real.log_rpow hr, one_div,
            Real.log_inv]
          ring
  refine ⟨|K| * (1 + Real.log A₀ + koebeDistExp + Real.log (1 + κ⁻¹) + p), fun ζ hζ => ?_⟩
  have hz1 : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
  have hr : 0 < 1 - ‖ζ‖ := by linarith
  have hr1 : 1 - ‖ζ‖ ≤ 1 := by linarith [norm_nonneg ζ]
  have hL0 := WangWu.log_one_div_nonneg hr hr1
  have hy : 0 < (1 - ‖ζ‖) ^ p := Real.rpow_pos_of_pos hr p
  have hy1 : (1 - ‖ζ‖) ^ p ≤ 1 := Real.rpow_le_one hr.le hr1 hp.le
  have hd := hdist ζ hζ
  have hd0 : 0 < κ * (1 - ‖ζ‖) ^ p := mul_pos hκ hy
  have h1 : 1 + (infDist (f ζ) (frontier C))⁻¹ ≤ (1 + κ⁻¹) * ((1 - ‖ζ‖) ^ p)⁻¹ := by
    have hinv : (infDist (f ζ) (frontier C))⁻¹ ≤ κ⁻¹ * ((1 - ‖ζ‖) ^ p)⁻¹ := by
      rw [← mul_inv]
      exact inv_anti₀ hd0 hd
    have hge : 1 ≤ ((1 - ‖ζ‖) ^ p)⁻¹ := one_le_inv₀ hy |>.2 hy1
    nlinarith [inv_pos.2 hκ]
  have hpos1 : 0 < 1 + (infDist (f ζ) (frontier C))⁻¹ := by
    have := inv_nonneg.2 (infDist_nonneg (x := f ζ) (s := frontier C)); linarith
  have hκ1 : 0 < 1 + κ⁻¹ := by have := inv_pos.2 hκ; linarith
  have h2 : Real.log (1 + (infDist (f ζ) (frontier C))⁻¹) ≤
      Real.log (1 + κ⁻¹) + p * Real.log (1 / (1 - ‖ζ‖)) := by
    calc Real.log (1 + (infDist (f ζ) (frontier C))⁻¹)
        ≤ Real.log ((1 + κ⁻¹) * ((1 - ‖ζ‖) ^ p)⁻¹) := Real.log_le_log hpos1 h1
      _ = Real.log (1 + κ⁻¹) + p * Real.log (1 / (1 - ‖ζ‖)) := by
        rw [Real.log_mul hκ1.ne' (inv_pos.2 hy).ne', Real.log_inv, Real.log_rpow hr, one_div,
          Real.log_inv]
        ring
  have h3 := hgrow ζ hζ
  have hlogA : 0 ≤ Real.log A₀ := Real.log_nonneg hA₀
  have hκlog : 0 ≤ Real.log (1 + κ⁻¹) := Real.log_nonneg (by have := inv_pos.2 hκ; linarith)
  have hlog0 : 0 ≤ Real.log (1 + (infDist (f ζ) (frontier C))⁻¹) := Real.log_nonneg (by
    have := inv_nonneg.2 (infDist_nonneg (x := f ζ) (s := frontier C)); linarith)
  have hlogn : 0 ≤ Real.log (1 + ‖f ζ‖) := Real.log_nonneg (by linarith [norm_nonneg (f ζ)])
  set L := Real.log (1 / (1 - ‖ζ‖))
  calc |Hh (f ζ)| ≤ K * (1 + Real.log (1 + ‖f ζ‖) +
        Real.log (1 + (infDist (f ζ) (frontier C))⁻¹)) := hgrowth _ (hfb.mapsTo hζ)
    _ ≤ |K| * (1 + Real.log (1 + ‖f ζ‖) +
        Real.log (1 + (infDist (f ζ) (frontier C))⁻¹)) :=
        mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
    _ ≤ |K| * (1 + (Real.log A₀ + koebeDistExp * L) + (Real.log (1 + κ⁻¹) + p * L)) := by
        gcongr
    _ ≤ |K| * (1 + Real.log A₀ + koebeDistExp + Real.log (1 + κ⁻¹) + p) * (1 + L) := by
        rw [mul_assoc]
        gcongr
        nlinarith

/-- A continuous branch `A` of `arg φ'` on an open `C` is harmonic there: it is the imaginary part of
the holomorphic logarithm `log |φ'| + i A` of `φ'` (`isDerivLog_of_arg_branch`). -/
theorem harmonicOnNhd_of_arg_branch {C : Set ℂ} (hCo : IsOpen C) {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ C {w : ℂ | 0 < w.im}) {A : ℂ → ℝ} (hAc : ContinuousOn A C)
    (hA : ∀ z ∈ C, deriv φ z = ‖deriv φ z‖ * exp (A z * I)) :
    InnerProductSpace.HarmonicOnNhd A C := by
  have hL := isDerivLog_of_arg_branch hCo hφ hAc hA
  intro z hz
  have han : AnalyticAt ℂ (fun z => (Real.log ‖deriv φ z‖ : ℂ) + (A z : ℂ) * I) z :=
    hL.1.analyticAt (hCo.mem_nhds hz)
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).1 han.harmonicAt_im
  filter_upwards [hCo.mem_nhds hz] with w _
  simp

/-- **Disk growth of the `arg φ'` term.** For a Riemann map `f : 𝔻 → C` and a continuous branch `A`
of `arg φ'` (`φ : C → ℍ` conformal), `|A(f(ζ))|` is at most a constant times
`1 + log(1/(1 − |ζ|))`: `A ∘ f = Im (L_{φ∘f} − log f')` and both logarithms of derivatives of univalent
maps of the disk grow logarithmically (`norm_derivLog_sub_le`). -/
theorem exists_abs_arg_comp_le_log {C : Set ℂ} (hCo : IsOpen C) {f φ : ℂ → ℂ}
    (hf : IsConformalBijection f (ball 0 1) C) (hφ : IsConformalBijection φ C {w : ℂ | 0 < w.im})
    {A : ℂ → ℝ} (hAc : ContinuousOn A C)
    (hA : ∀ z ∈ C, deriv φ z = ‖deriv φ z‖ * exp (A z * I)) :
    ∃ K' : ℝ, ∀ ζ ∈ ball (0 : ℂ) 1, |A (f ζ)| ≤ K' * (1 + Real.log (1 / (1 - ‖ζ‖))) := by
  obtain ⟨hfd, hfb⟩ := hf
  have hfinj := hfb.injOn
  have hL := isDerivLog_of_arg_branch hCo hφ hAc hA
  set L := fun z => (Real.log ‖deriv φ z‖ : ℂ) + (A z : ℂ) * I
  obtain ⟨ℓf, hℓf⟩ := exists_isDerivLog isOpen_ball isSimplyConnected_unitBall hfd
    (fun ζ hζ => QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn isOpen_ball hfd hfinj hζ)
  have hLm := IsDerivLog.comp isOpen_ball hCo hφ.1 hfd hfb.mapsTo hL hℓf
  have hmd : DifferentiableOn ℂ (φ ∘ f) (ball 0 1) := hφ.1.comp hfd hfb.mapsTo
  have hminj : InjOn (φ ∘ f) (ball 0 1) := hφ.2.injOn.comp hfinj hfb.mapsTo
  set K₀ := ‖(L (f 0) + ℓf 0) - ℓf 0‖
  refine ⟨K₀ + 2 * koebeDistExp, fun ζ hζ => ?_⟩
  have hr : 0 < 1 - ‖ζ‖ := by have := mem_ball_zero_iff.1 hζ; linarith
  have hr1 : 1 - ‖ζ‖ ≤ 1 := by linarith [norm_nonneg ζ]
  have hL0 := WangWu.log_one_div_nonneg hr hr1
  have hlog : -Real.log (1 - ‖ζ‖) = Real.log (1 / (1 - ‖ζ‖)) := by
    rw [one_div, Real.log_inv]
  have h1 := norm_derivLog_sub_le hmd hminj hLm hζ
  have h2 := norm_derivLog_sub_le hfd hfinj hℓf hζ
  have hAf : A (f ζ) = (L (f ζ) + ℓf ζ - ℓf ζ).im := by simp [L]
  have hK₀ : 0 ≤ K₀ := norm_nonneg _
  have hC2 := koebeDistExp_pos
  rw [hAf]
  refine (Complex.abs_im_le_norm _).trans ?_
  calc ‖L (f ζ) + ℓf ζ - ℓf ζ‖
      = ‖((L (f ζ) + ℓf ζ) - (L (f 0) + ℓf 0)) - (ℓf ζ - ℓf 0) +
          ((L (f 0) + ℓf 0) - ℓf 0)‖ := by ring_nf
    _ ≤ ‖(L (f ζ) + ℓf ζ) - (L (f 0) + ℓf 0)‖ + ‖ℓf ζ - ℓf 0‖ + K₀ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ koebeDistExp * Real.log (1 / (1 - ‖ζ‖)) + koebeDistExp * Real.log (1 / (1 - ‖ζ‖)) + K₀ := by
        rw [← hlog]; simp only [L] at h1 ⊢; linarith
    _ ≤ (K₀ + 2 * koebeDistExp) * (1 + Real.log (1 / (1 - ‖ζ‖))) := by nlinarith

/-- **Aux. lemma 28 with logarithmic growth at `∞`** (simply connected form; prime ends read in the
disk through `f`). Let `C` be open (bounded or not), `f : 𝔻 → C` conformal, `H` harmonic in `C`
with `|H(z)| ≤ K (1 + log(1 + |z|) + log(1 + 1/dist(z, ∂C)))`, `φ : C → ℍ` conformal, `g` bounded
harmonic in `ℍ`, `χ` real and `A` a continuous branch of `arg φ'`. If `H − (g ∘ φ − χ A)` tends to
zero at every point of the unit circle outside a finite set, then `H = g ∘ φ − χ A` on `C`. -/
theorem aux28_eqOn_of_tendsto_disk_of_log_growth {C : Set ℂ} (hCo : IsOpen C) {f : ℂ → ℂ}
    (hf : IsConformalBijection f (ball 0 1) C) {Hh : ℂ → ℝ}
    (hH : InnerProductSpace.HarmonicOnNhd Hh C) {K : ℝ}
    (hgrowth : ∀ z ∈ C, |Hh z| ≤
      K * (1 + Real.log (1 + ‖z‖) + Real.log (1 + (infDist z (frontier C))⁻¹)))
    {φ : ℂ → ℂ} (hφ : IsConformalBijection φ C {w : ℂ | 0 < w.im})
    {g : ℂ → ℝ} (hg : InnerProductSpace.HarmonicOnNhd g {w : ℂ | 0 < w.im})
    (hgb : ∃ M, ∀ w : ℂ, 0 < w.im → |g w| ≤ M) (χ : ℝ) {A : ℂ → ℝ} (hAc : ContinuousOn A C)
    (hA : ∀ z ∈ C, deriv φ z = ‖deriv φ z‖ * exp (A z * I)) {E : Set ℂ} (hEfin : E.Finite)
    (hbd : ∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
      Tendsto (fun ζ => Hh (f ζ) - (g (φ (f ζ)) - χ * A (f ζ))) (𝓝[ball 0 1] q) (𝓝 0)) :
    ∀ z ∈ C, Hh z = g (φ z) - χ * A z := by
  obtain ⟨K₁, hK₁⟩ := exists_abs_comp_le_log_of_log_norm_growth hCo hf hgrowth
  obtain ⟨K₂, hK₂⟩ := exists_abs_arg_comp_le_log hCo hf hφ hAc hA
  obtain ⟨M, hM⟩ := hgb
  have hAh := harmonicOnNhd_of_arg_branch hCo hφ hAc hA
  have hcand : InnerProductSpace.HarmonicOnNhd (fun z => g (φ z) - χ * A z) C := by
    intro z hz
    have hφa : AnalyticAt ℂ φ z := hφ.1.analyticAt (hCo.mem_nhds hz)
    have h2 : InnerProductSpace.HarmonicAt (g ∘ φ) z :=
      QuantumZipper.FieldLawler.fl_harmonicAt_comp hφa (hg _ (hφ.2.mapsTo hz))
    have h3 : InnerProductSpace.HarmonicAt (fun z => χ * A z) z := by
      have h := (hAh z hz).const_smul (c := χ)
      refine (InnerProductSpace.harmonicAt_congr_nhds ?_).1 h
      filter_upwards with w
      simp only [Pi.smul_apply, smul_eq_mul]
    exact h2.sub h3
  have hu := WangWu.harmonicOnNhd_comp_sub hf hH hcand
  have hgrowth' : ∀ ζ ∈ ball (0 : ℂ) 1, 0 < ‖ζ‖ →
      |Hh (f ζ) - (g (φ (f ζ)) - χ * A (f ζ))| ≤
        (|K₁| + |M| + |χ| * |K₂|) * (1 + Real.log (1 / (1 - ‖ζ‖))) := by
    intro ζ hζ _
    have hr : 0 < 1 - ‖ζ‖ := by have := mem_ball_zero_iff.1 hζ; linarith
    have hr1 : 1 - ‖ζ‖ ≤ 1 := by linarith [norm_nonneg ζ]
    have hL0 := WangWu.log_one_div_nonneg hr hr1
    set L := Real.log (1 / (1 - ‖ζ‖))
    have h1 : |Hh (f ζ)| ≤ |K₁| * (1 + L) :=
      (hK₁ ζ hζ).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
    have h2 : |g (φ (f ζ))| ≤ |M| * (1 + L) :=
      ((hM _ (hφ.2.mapsTo (hf.2.mapsTo hζ))).trans (le_abs_self M)).trans
        (le_mul_of_one_le_right (abs_nonneg _) (by linarith))
    have h3 : |A (f ζ)| ≤ |K₂| * (1 + L) :=
      (hK₂ ζ hζ).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
    calc |Hh (f ζ) - (g (φ (f ζ)) - χ * A (f ζ))|
        ≤ |Hh (f ζ)| + (|g (φ (f ζ))| + |χ| * |A (f ζ)|) := by
          rw [← abs_mul]
          exact (abs_sub _ _).trans (add_le_add le_rfl (abs_sub _ _))
      _ ≤ |K₁| * (1 + L) + (|M| * (1 + L) + |χ| * (|K₂| * (1 + L))) := by
          gcongr
      _ = (|K₁| + |M| + |χ| * |K₂|) * (1 + L) := by ring
  have h0 := WangWu.eqOn_zero_of_log_growth hu hEfin hgrowth' hbd
  intro z hz
  obtain ⟨ζ, hζ, rfl⟩ := hf.2.surjOn hz
  have := h0 ζ hζ
  linarith

end Deterministic

/-! ### Lemma 4.6 on all of `ℍ` for the project's local-set mean -/

section Global

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {A : Ω → Set ℂ} {g : Ω → DistOn upperHalfPlaneOpens}

/-- **The global growth bound of the local-set mean** (Wang–Wu Lemma 4.6 on all of `ℍ`, landed as
`WangWu.ae_abs_le_log_global_of_condMean`, transferred to `IsLocalSetMean`): almost surely there is
a finite `K` such that every harmonic representative `v` of `𝒞_A` on `ℍ ∖ A` satisfies
`|v(z)| ≤ K (1 + log(1 + |z|) + log(1 + 1/dist(z, (ℍ ∖ A)ᶜ)))` on `ℍ ∖ A`. -/
theorem ae_abs_le_log_global_of_isLocalSetMean
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A h P)
    (hg : IsLocalSetMean A h P g) :
    ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ = ∫ x, v x * φ x) →
      ∀ z ∈ H \ A ω,
        |v z| ≤ K * (1 + Real.log (1 + ‖z‖) + Real.log (1 + 1 / infDist z (H \ A ω)ᶜ)) := by
  have hhm := hh.measurable
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := hloc.2.1
  have hav : IsAvoidanceLocal A h P := ((isLocalSet_tfae hh hA hAc).out 4 1).1 hloc
  obtain ⟨M, h₁, hM, hMlim, hh₁m, hh₁⟩ := exists_germVersion hh hA hav hAc
  have hharm := ae_isHarmonicDistOn_germVersion hh hA hav hAc hM hMlim hh₁
  have hg₁ : IsLocalSetMean A h P h₁ :=
    ⟨hh₁m, hharm, isCondZeroBoundaryGFF_germVersion hh hA hAc hM hh₁m hh₁⟩
  have hmean : ∀ φ : TestOn upperHalfPlaneOpens,
      (fun ω => h₁ ω φ) =ᵐ[P] P[fun ω => h ω φ | germSigma A h] :=
    fun φ => (hh₁ φ).trans (hM φ).2.1
  have hagree : ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
      g ω φ = h₁ ω φ :=
    ae_forall_apply_eq_of_bump (hAc.mono fun ω hω => ⟨hω.2, sdiff_subset⟩) hg.2.1 hharm
      fun x δ hδ hB => (IsLocalSetMean.ae_apply_eq hA hhm hg hg₁ _).mono fun ω hω _ => hω
  filter_upwards [WangWu.ae_abs_le_log_global_of_condMean hh hmean (hAc.mono fun _ h => h.2),
    hagree] with ω ⟨K, hK⟩ hag
  exact ⟨K, fun v hv hrep z hz => hK v hv (fun φ hφ => (hag φ hφ).symm.trans (hrep φ hφ)) z hz⟩

/-- **Proposition 6.1, identification step, on every component** (bounded or not; p. 169: "Apply
**Aux.** lemma 27 and then **Aux.** lemma 28 to each component", after mapping to the disk). Let `A`
be a local set of the zero-boundary GFF `h` on `ℍ`, `g` a version of `𝒞_A`, and `F` a harmonic
function bounded on `ℍ` (the deterministic mean; the field is `h + F`). Almost surely, for every
component `C` of `ℍ ∖ A`, every harmonic representative `v` of `g` on `ℍ ∖ A`, and every chart
`(f, φ, G, L)` of Aux. lemma 28: if `(v + F) − (G ∘ φ − χ L)` tends to zero at every prime end of
`C` (point of the unit circle, read through `f`) outside a finite set `E`, then
`v + F = G ∘ φ − χ L` on `C`. -/
theorem ae_eqOn_component_of_tendsto_global
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A h P)
    (hg : IsLocalSetMean A h P g) {F : ℂ → ℝ} (hF : InnerProductSpace.HarmonicOnNhd F H)
    (hFb : ∃ M : ℝ, ∀ z ∈ H, |F z| ≤ M) (χ : ℝ) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ A ω,
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ = ∫ x, v x * φ x) →
      ∀ (f φc : ℂ → ℂ) (G L : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ A ω) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ A ω) z₀) {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn L (connectedComponentIn (H \ A ω) z₀) →
      (∀ z ∈ connectedComponentIn (H \ A ω) z₀, deriv φc z = ‖deriv φc z‖ * exp (L z * I)) →
      E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
        Tendsto (fun ζ => (v (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * L (f ζ)))
          (𝓝[ball 0 1] q) (𝓝 0)) →
      ∀ z ∈ connectedComponentIn (H \ A ω) z₀, v z + F z = G (φc z) - χ * L z := by
  obtain ⟨MF, hMF⟩ := hFb
  filter_upwards [ae_abs_le_log_global_of_isLocalSetMean hh hA hloc hg, hloc.2.1]
    with ω ⟨K, hK⟩ ⟨_, hAo⟩ z₀ _ v hv hrep f φc G L E hf hφc hG hGb hLc hL hE hbd
  set C := connectedComponentIn (H \ A ω) z₀ with hCdef
  have hCo : IsOpen C := hAo.connectedComponentIn
  have hCV : C ⊆ H \ A ω := connectedComponentIn_subset _ _
  have hH : InnerProductSpace.HarmonicOnNhd (fun z => v z + F z) C := fun z hz =>
    (hv z (hCV hz)).add (hF z (hCV hz).1)
  have hvg := WangWu.growth_of_global hAo sdiff_subset hCo hCV (hK v hv hrep)
  refine aux28_eqOn_of_tendsto_disk_of_log_growth (Hh := fun z => v z + F z) (K := |K| + |MF|)
    hCo hf hH (fun z hz => ?_) hφc hG hGb χ hLc hL hE hbd
  set B := 1 + Real.log (1 + ‖z‖) + Real.log (1 + (infDist z (frontier C))⁻¹)
  have hB : 1 ≤ B := by
    have h1 : 0 ≤ Real.log (1 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
    have h2 : 0 ≤ Real.log (1 + (infDist z (frontier C))⁻¹) := Real.log_nonneg (by
      have := inv_nonneg.2 (infDist_nonneg (x := z) (s := frontier C)); linarith)
    simp only [B]; linarith
  have hFz : |F z| ≤ |MF| * B :=
    ((hMF z (hCV hz).1).trans (le_abs_self MF)).trans (le_mul_of_one_le_right (abs_nonneg _) hB)
  calc |v z + F z| ≤ |v z| + |F z| := abs_add_le _ _
    _ ≤ |K| * B + |MF| * B := add_le_add (hvg z hz) hFz
    _ = (|K| + |MF|) * B := by ring

/-- **The Gaussian law of Proposition 6.1 on any component** (bounded or not): with the hypotheses of
`ae_eqOn_component_of_tendsto_global` and a test function `φ` supported in the component `C`, given
the germ σ-algebra the field `h + F` paired with `φ` has the conditional characteristic function of
`(𝔥_C, φ) + GFF_C(φ)`, `𝔥_C = G ∘ φ_C − χ L`. -/
theorem ae_condExp_exp_eq_of_component_of_tendsto_global
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A h P)
    (hg : IsLocalSetMean A h P g) {F : ℂ → ℝ} (hF : InnerProductSpace.HarmonicOnNhd F H)
    (hFb : ∃ M : ℝ, ∀ z ∈ H, |F z| ≤ M) (χ : ℝ) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ A ω, tsupport φ ⊆ connectedComponentIn (H \ A ω) z₀ →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ A ω → g ω ψ = ∫ x, v x * ψ x) →
      ∀ (f φc : ℂ → ℂ) (G L : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ A ω) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ A ω) z₀) {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn L (connectedComponentIn (H \ A ω) z₀) →
      (∀ z ∈ connectedComponentIn (H \ A ω) z₀, deriv φc z = ‖deriv φc z‖ * exp (L z * I)) →
      E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
        Tendsto (fun ζ => (v (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * L (f ζ)))
          (𝓝[ball 0 1] q) (𝓝 0)) →
      P[fun ω' => cexp (I * ((h ω' φ + ∫ x, F x * φ x : ℝ) : ℂ)) | germSigma A h] ω =
        cexp (I * ((∫ x, (G (φc x) - χ * L x) * φ x : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) *
            QuantumZipper.zeroGFFTestCov (connectedComponentIn (H \ A ω) z₀) φ φ) : ℝ) : ℂ) := by
  have hFc : ContinuousOn F H := fun z hz => (hF z hz).1.continuousAt.continuousWithinAt
  filter_upwards [ae_condExp_exp_eq_of_eqOn_component hA hh.measurable
      (hloc.2.1.mono fun _ h => h.2) hg hFc φ,
    ae_eqOn_component_of_tendsto_global hh hA hloc hg hF hFb χ]
    with ω hlaw hid z₀ hz₀ hφC v hv hvrep f φc G L E hf hφc hG hGb hLc hL hE hbd
  exact hlaw z₀ hz₀ hφC v hv hvrep _ (hid z₀ hz₀ v hv hvrep f φc G L E hf hφc hG hGb hLc hL hE hbd)

end Global

/-! ### The two-set assemblies on every component -/

section Assembly

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Proposition 6.1 for the full union `A₁ ∪ A₂`, every component** (the case `τ = ∞`, p. 167, and
the exterior components): `ae_eqOn_component_union_of_tendsto` of `Prop61.lean` without the
boundedness of the component, for a deterministic mean `F` bounded on `ℍ`. -/
theorem ae_eqOn_component_union_of_tendsto_global {A₁ A₂ : Ω → Set ℂ}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap A₁ hittingSigma) (MeasurableSpace.comap A₂ hittingSigma) P)
    (h₁ : IsLocalSet A₁ h P) (h₂ : IsLocalSet A₂ h P)
    (hunb₁ : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₁ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₁ ω)) z))
    (hunb₂ : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ ω)) z))
    {g g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) h P g) (hg₁ : IsLocalSetMean A₁ h P g₁)
    (hg₂ : IsLocalSetMean A₂ h P g₂) {F : ℂ → ℝ} (hF : InnerProductSpace.HarmonicOnNhd F H)
    (hFb : ∃ M : ℝ, ∀ z ∈ H, |F z| ≤ M) (χ : ℝ) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ (A₁ ω ∪ A₂ ω),
      ∀ v v₁ v₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (A₁ ω ∪ A₂ ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A₁ ω ∪ A₂ ω) →
        g ω φ = ∫ x, v x * φ x) →
      InnerProductSpace.HarmonicOnNhd v₁ (H \ A₁ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ x, v₁ x * φ x) →
      InnerProductSpace.HarmonicOnNhd v₂ (H \ A₂ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ ω → g₂ ω φ = ∫ x, v₂ x * φ x) →
      ∀ (f φc : ℂ → ℂ) (G L : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ (A₁ ω ∪ A₂ ω)) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ (A₁ ω ∪ A₂ ω)) z₀) {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn L (connectedComponentIn (H \ (A₁ ω ∪ A₂ ω)) z₀) →
      (∀ z ∈ connectedComponentIn (H \ (A₁ ω ∪ A₂ ω)) z₀,
        deriv φc z = ‖deriv φc z‖ * exp (L z * I)) →
      E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E → ∃ p : ℂ, Tendsto f (𝓝[ball 0 1] q) (𝓝 p) ∧
        ((p ∈ A₂ ω ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, A₁ ω ∩ ball p r ⊆ A₂ ω) ∧
            Tendsto (fun ζ => (v₂ (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * L (f ζ)))
              (𝓝[ball 0 1] q) (𝓝 0)) ∨
          (p ∈ A₁ ω ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, A₂ ω ∩ ball p r ⊆ A₁ ω) ∧
            Tendsto (fun ζ => (v₁ (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * L (f ζ)))
              (𝓝[ball 0 1] q) (𝓝 0)))) →
      ∀ z ∈ connectedComponentIn (H \ (A₁ ω ∪ A₂ ω)) z₀,
        v z + F z = G (φc z) - χ * L z := by
  have hAU : Measurable[mΩ, hittingSigma] fun ω => A₁ ω ∪ A₂ ω := measurable_union_hitting hA₁ hA₂
  have hlocU : IsLocalSet (fun ω => A₁ ω ∪ A₂ ω) h P :=
    IsLocalSet.isLocalSet_union hh hA₁ hA₂ hci h₁ h₂
  filter_upwards [ae_eqOn_component_of_tendsto_global (A := fun ω => A₁ ω ∪ A₂ ω) hh hAU hlocU hg
      hF hFb χ, ae_tendsto_comp_sub_of_union hh hA₁ hA₂ hci h₁ h₂ hunb₂ hg hg₂,
    ae_tendsto_comp_sub_of_union_symm hh hA₁ hA₂ hci h₁ h₂ hunb₁ hg hg₁] with ω hid hc₂ hc₁
    z₀ hz₀ v v₁ v₂ hv hvrep hv₁ hv₁rep hv₂ hv₂rep f φc G L E hf hφc hG hGb hLc hL hE hbd
  refine hid z₀ hz₀ v hv hvrep f φc G L E hf hφc hG hGb hLc hL hE fun q hq hqE => ?_
  have hfC : MapsTo f (ball 0 1) (H \ (A₁ ω ∪ A₂ ω)) :=
    hf.2.mapsTo.mono_right (connectedComponentIn_subset _ _)
  obtain ⟨p, hfq, ⟨hp, hr, hlim⟩ | ⟨hp, hr, hlim⟩⟩ := hbd q hq hqE
  · have hf₂ : MapsTo f (ball 0 1) (H \ A₂ ω) :=
      hfC.mono_right (sdiff_subset_sdiff_right subset_union_right)
    have hd := hc₂ v v₂ hv hvrep hv₂ hv₂rep f q p hf₂ hfq hp hr
    refine tendsto_sub_zero_trans (b := fun ζ => v₂ (f ζ) + F (f ζ)) ?_ hlim
    refine hd.congr fun ζ => ?_
    ring
  · have hf₁ : MapsTo f (ball 0 1) (H \ A₁ ω) :=
      hfC.mono_right (sdiff_subset_sdiff_right subset_union_left)
    have hd := hc₁ v v₁ hv hvrep hv₁ hv₁rep f q p hf₁ hfq hp hr
    refine tendsto_sub_zero_trans (b := fun ζ => v₁ (f ζ) + F (f ζ)) ?_ hlim
    refine hd.congr fun ζ => ?_
    ring

/-- **Proposition 6.1 for a stopped set inside a full one, every component** (p. 168, the remaining
component: "Applying Proposition 3.8 to `A(τ) ⊆ A(∞)` therefore compares the conditional means on
each of these local sides"; in `ℍ` this component contains the future tail and is unbounded):
`ae_eqOn_component_of_subset_of_tendsto` of `Prop61.lean` without the boundedness of the component,
for a deterministic mean `F` bounded on `ℍ`. The boundary values at a prime end come either from
the mean of the full set `L` (impression `p ∈ S ∪ ℝ` with `L ⊆ S` near `p`: the stopped prefix and
the active slit) or from the mean of a further local set `T ⊆ S` (impression `p ∈ T ∪ ℝ` with
`S ⊆ T` near `p`: the suffix of `η_{θ₂}` after the last contact, which the compact stopped prefix
avoids). -/
theorem ae_eqOn_component_of_subset_of_tendsto_global {S L T : Ω → Set ℂ}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hS : Measurable[mΩ, hittingSigma] S) (hL : Measurable[mΩ, hittingSigma] L)
    (hT : Measurable[mΩ, hittingSigma] T)
    (hSL : ∀ ω, S ω ⊆ L ω) (hTS : ∀ ω, T ω ⊆ S ω)
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap L hittingSigma) (MeasurableSpace.comap S hittingSigma) P)
    (hciT : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap S hittingSigma) (MeasurableSpace.comap T hittingSigma) P)
    (hlS : IsLocalSet S h P) (hlL : IsLocalSet L h P) (hlT : IsLocalSet T h P)
    (hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (S ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (S ω)) z))
    (hunbT : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (T ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (T ω)) z))
    {gS gL gT : Ω → DistOn upperHalfPlaneOpens} (hgS : IsLocalSetMean S h P gS)
    (hgL : IsLocalSetMean L h P gL) (hgT : IsLocalSetMean T h P gT) {F : ℂ → ℝ}
    (hF : InnerProductSpace.HarmonicOnNhd F H) (hFb : ∃ M : ℝ, ∀ z ∈ H, |F z| ≤ M) (χ : ℝ) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ S ω,
      ∀ v vL vT : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ S ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ S ω → gS ω φ = ∫ x, v x * φ x) →
      InnerProductSpace.HarmonicOnNhd vL (H \ L ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ L ω → gL ω φ = ∫ x, vL x * φ x) →
      InnerProductSpace.HarmonicOnNhd vT (H \ T ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ T ω → gT ω φ = ∫ x, vT x * φ x) →
      ∀ (f φc : ℂ → ℂ) (G Lc : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ S ω) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ S ω) z₀) {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn Lc (connectedComponentIn (H \ S ω) z₀) →
      (∀ z ∈ connectedComponentIn (H \ S ω) z₀, deriv φc z = ‖deriv φc z‖ * exp (Lc z * I)) →
      E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E → ∃ p : ℂ, Tendsto f (𝓝[ball 0 1] q) (𝓝 p) ∧
        ((p ∈ S ω ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, L ω ∩ ball p r ⊆ S ω) ∧
            Tendsto (fun ζ => (vL (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * Lc (f ζ)))
              (𝓝[ball 0 1] q) (𝓝 0)) ∨
          (p ∈ T ω ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, S ω ∩ ball p r ⊆ T ω) ∧
            Tendsto (fun ζ => (vT (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * Lc (f ζ)))
              (𝓝[ball 0 1] q) (𝓝 0)))) →
      ∀ z ∈ connectedComponentIn (H \ S ω) z₀, v z + F z = G (φc z) - χ * Lc z := by
  have hLS : (fun ω => L ω ∪ S ω) = L := funext fun ω => union_eq_left.2 (hSL ω)
  have hgLS : IsLocalSetMean (fun ω => L ω ∪ S ω) h P gL := by rw [hLS]; exact hgL
  have hST : (fun ω => S ω ∪ T ω) = S := funext fun ω => union_eq_left.2 (hTS ω)
  have hgST : IsLocalSetMean (fun ω => S ω ∪ T ω) h P gS := by rw [hST]; exact hgS
  filter_upwards [ae_eqOn_component_of_tendsto_global hh hS hlS hgS hF hFb χ,
    ae_tendsto_comp_sub_of_union hh hL hS hci hlL hlS hunb hgLS hgS,
    ae_tendsto_comp_sub_of_union hh hS hT hciT hlS hlT hunbT hgST hgT] with ω hid hc hcT
    z₀ hz₀ v vL vT hv hvrep hvL hvLrep hvT hvTrep f φc G Lc E hf hφc hG hGb hLc hLd hE hbd
  refine hid z₀ hz₀ v hv hvrep f φc G Lc E hf hφc hG hGb hLc hLd hE fun q hq hqE => ?_
  have hfS : MapsTo f (ball 0 1) (H \ S ω) :=
    hf.2.mapsTo.mono_right (connectedComponentIn_subset _ _)
  obtain ⟨p, hfq, ⟨hp, hr, hlim⟩ | ⟨hp, hr, hlim⟩⟩ := hbd q hq hqE
  · have hu : L ω ∪ S ω = L ω := union_eq_left.2 (hSL ω)
    have hd := hc vL v (by rw [hu]; exact hvL) (by rw [hu]; exact hvLrep) hv hvrep f q p hfS hfq
      hp hr
    refine tendsto_sub_zero_trans (b := fun ζ => vL (f ζ) + F (f ζ)) ?_ hlim
    have := hd.neg
    rw [neg_zero] at this
    refine this.congr fun ζ => ?_
    ring
  · have hu : S ω ∪ T ω = S ω := union_eq_left.2 (hTS ω)
    have hfT : MapsTo f (ball 0 1) (H \ T ω) :=
      hfS.mono_right (sdiff_subset_sdiff_right (hTS ω))
    have hd := hcT v vT (by rw [hu]; exact hv) (by rw [hu]; exact hvrep) hvT hvTrep f q p hfT hfq
      hp hr
    refine tendsto_sub_zero_trans (b := fun ζ => vT (f ζ) + F (f ζ)) ?_ hlim
    refine hd.congr fun ζ => ?_
    ring

end Assembly

end InteractingSLE.Sec6
