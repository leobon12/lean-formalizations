/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopChart
import InteractingSLE.Spec.Sec7.Lemma72BChart
import InteractingSLE.Spec.Jordan.ChartExists

/-!
# The pocket chart: a conformal chart of the pocket with a measurably selected derivative logarithm

Packet PROVE-STRIPSYS35 (PROVE-STRIPSYS33 §5.3). Specification §7.4, Aux. lemma 119 (`source/spec/p385-432.md` L52,
p. 387: "There is a measurably selected derivative-logarithm lift for a conformal chart `φ : C → ℍ`"; "Analytic
derivative logarithms are determined by their value at one interior point").

`PocketStopChart.PocketStopField` asks for a pocket chart `c` (`PocketCoupling.IsPocketChartOn`: conformal, domain the
pocket `C`, forward map the Jordan coordinate `ψ`, continuous lift, lift measurable for the walls' σ-algebra at every
fixed point) together with a derivative logarithm `ℓ` of `ψ` whose imaginary part is the lift. No landed result
produced one. Here:

* `canonLogH g`: for `g` holomorphic on `ℍ` with `g′ ≠ 0`, the analytic logarithm of `g′` on `ℍ` with value
  `Log g′(i)` at `i` (`isDerivLog_canonLogH`; `ℍ` is simply connected);
* **`tendsto_sum_log_ratio`** (deterministic): along the segment `[a, b]`, a continuous logarithm `M` of `f` satisfies
  `M b − M a = lim_n ∑_{k ≤ n} Log (f(p_{k+1}) / f(p_k))` (`p_k = a + k(b − a)/(n + 1)`; the sum is eventually exactly
  `M b − M a`, by uniform continuity of `M` on the segment). Hence the canonical logarithm is an explicit limit of
  finitely many values of `g′` (**`canonLogH_eq_lim`**);
* **`measurable_canonLogH_apply`**, **`measurable_uncurry_canonLogH`**: for a random family of such `g` whose
  derivatives are measurable at fixed points, the canonical logarithm is measurable at fixed points, and jointly
  measurable on `ℍ × Ω` (Carathéodory);
* **`exists_isPocketChartOn`**: every random conformal bijection `ψ ω : C ω → ℍ` (on a measurable event `A`, open
  `C ω ⊆ ℍ`) whose membership events and values at fixed points are measurable has a pocket chart with a derivative
  logarithm: `c ω = (ψ ω, ψ ω⁻¹, −Im canonLogH (ψ ω⁻¹) ∘ ψ ω)`;
* **`IsPocketChartOn.shift`**: the branch can be shifted by any measurable integer, `lift − 2πn`, `ℓ − 2πin`.

Ruling R48: nothing here uses Theorem 1.2/1.3 or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex Function
open scoped Real NNReal

namespace InteractingSLE.Sec7.PocketStopField

open QuantumZipper (H isOpen_H)
open SupercriticalConformalCovariance (IsConformalBijection)

/-! ### The canonical logarithm of `g′` on `ℍ` -/

section Canon

open Classical in
/-- **The canonical derivative logarithm on `ℍ`**: an analytic logarithm `M` of `g′` on `ℍ` with `M i = Log g′(i)`
(chosen; `0` if there is none). -/
def canonLogH (g : ℂ → ℂ) : ℂ → ℂ :=
  if h : ∃ M : ℂ → ℂ, IsDerivLog g M H ∧ M I = log (deriv g I) then h.choose else 0

theorem I_mem_H : I ∈ H := by
  change 0 < I.im
  rw [I_im]
  exact one_pos

/-- The canonical logarithm is a logarithm of `g′` on `ℍ` with the principal value at `i`. -/
theorem isDerivLog_canonLogH {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g H) (hne : ∀ w ∈ H, deriv g w ≠ 0) :
    IsDerivLog g (canonLogH g) H ∧ canonLogH g I = log (deriv g I) := by
  have hex : ∃ M : ℂ → ℂ, IsDerivLog g M H ∧ M I = log (deriv g I) := by
    obtain ⟨M₀, hM₀⟩ := exists_isDerivLog isOpen_H isSimplyConnected_H hg hne
    have he : exp (M₀ I) = exp (log (deriv g I)) := by
      rw [hM₀.2 I I_mem_H, exp_log (hne I I_mem_H)]
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 he
    refine ⟨fun w => M₀ w - n * (2 * π * I), ⟨hM₀.1.sub_const _, fun w hw => ?_⟩, ?_⟩
    · rw [exp_sub, exp_int_mul_two_pi_mul_I, div_one]
      exact hM₀.2 w hw
    · simp only [hn, add_sub_cancel_right]
  rw [canonLogH, dite_eq_left_of_eq_true (eq_true hex)]
  exact hex.choose_spec

end Canon

/-! ### The telescoping formula along a segment -/

section Telescope

/-- The `k`-th of the `n + 2` equally spaced points of the segment `[a, b]`. -/
def segPt (a b : ℂ) (n k : ℕ) : ℂ := a + (((k : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) * (b - a)

/-- The telescoping sum of principal logarithms of the ratios of `f` at consecutive points. -/
def logRatioSum (f : ℂ → ℂ) (a b : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), log (f (segPt a b n (k + 1)) / f (segPt a b n k))

theorem segPt_mem_segment (a b : ℂ) {n k : ℕ} (hk : k ≤ n + 1) : segPt a b n k ∈ segment ℝ a b := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine ⟨1 - (k : ℝ) / ((n : ℝ) + 1), (k : ℝ) / ((n : ℝ) + 1), ?_, by positivity, by ring, ?_⟩
  · rw [sub_nonneg, div_le_one hn]
    exact_mod_cast hk
  · simp only [segPt, real_smul]
    push_cast
    ring

/-- **The telescoping formula** (deterministic): if `M` is continuous on the segment `[a, b]` and `exp ∘ M = f` there,
then `∑_{k ≤ n} Log (f(p_{k+1}) / f(p_k)) → M b − M a` (it is eventually equal: once the mesh is below the uniform
continuity scale of `M` for `π`, every increment of `M` has imaginary part in `(−π, π)`). -/
theorem tendsto_logRatioSum {M f : ℂ → ℂ} {a b : ℂ} (hM : ContinuousOn M (segment ℝ a b))
    (hexp : ∀ z ∈ segment ℝ a b, exp (M z) = f z) :
    Tendsto (logRatioSum f a b) atTop (𝓝 (M b - M a)) := by
  set F : ℝ → ℂ := fun t => M (a + (t : ℂ) * (b - a)) with hF
  have hmaps : MapsTo (fun t : ℝ => a + (t : ℂ) * (b - a)) (Icc 0 1) (segment ℝ a b) := by
    intro t ht
    refine ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, ?_⟩
    simp only [real_smul]
    push_cast
    ring
  have hFc : ContinuousOn F (Icc 0 1) :=
    hM.comp (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn hmaps
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hFc
  obtain ⟨δ, hδ, hδF⟩ := Metric.uniformContinuousOn_iff.1 huc π Real.pi_pos
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpt : ∀ k : ℕ, segPt a b n k = a + ((((k : ℝ) / ((n : ℝ) + 1)) : ℝ) : ℂ) * (b - a) := fun k => rfl
  have hmem : ∀ k : ℕ, k ≤ n + 1 → (k : ℝ) / ((n : ℝ) + 1) ∈ Icc (0 : ℝ) 1 := fun k hk =>
    ⟨by positivity, by rw [div_le_one hn1]; exact_mod_cast hk⟩
  have hstep : ∀ k ∈ Finset.range (n + 1),
      log (f (segPt a b n (k + 1)) / f (segPt a b n k)) = F (((k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) -
        F ((k : ℝ) / ((n : ℝ) + 1)) := by
    intro k hk
    have hk' : k < n + 1 := Finset.mem_range.1 hk
    have h1 := hmem (k + 1) hk'
    have h0 := hmem k hk'.le
    have hd : dist (((k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ((k : ℝ) / ((n : ℝ) + 1)) < δ := by
      rw [Real.dist_eq, ← sub_div, Nat.cast_add, Nat.cast_one, add_sub_cancel_left,
        abs_of_pos (by positivity)]
      refine lt_of_le_of_lt ?_ hN
      have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have hlt := hδF _ h1 _ h0 hd
    rw [dist_eq_norm] at hlt
    set d := F (((k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) - F ((k : ℝ) / ((n : ℝ) + 1)) with hd_def
    have him : |d.im| < π := lt_of_le_of_lt (abs_im_le_norm d) hlt
    have hexpd : exp d = f (segPt a b n (k + 1)) / f (segPt a b n k) := by
      rw [hd_def, exp_sub, hF]
      simp only
      rw [hexp _ (hmaps h1), hexp _ (hmaps h0)]
      rfl
    rw [← hexpd, log_exp (by linarith [neg_abs_le d.im]) (le_of_lt (lt_of_le_of_lt (le_abs_self _) him))]
  rw [logRatioSum, Finset.sum_congr rfl hstep, Finset.sum_range_sub (fun k : ℕ => F ((k : ℝ) / ((n : ℝ) + 1)))]
  have e1 : ((n + 1 : ℕ) : ℝ) / ((n : ℝ) + 1) = 1 := by rw [Nat.cast_add, Nat.cast_one, div_self hn1.ne']
  rw [e1, Nat.cast_zero, zero_div, hF]
  simp only [ofReal_one, one_mul, add_sub_cancel, ofReal_zero, zero_mul, add_zero]

/-- **The canonical logarithm as an explicit limit**: `canonLogH g w = Log g′(i) + lim_n ∑_{k ≤ n} Log (g′(p_{k+1}) /
g′(p_k))` along the segment `[i, w] ⊆ ℍ`. -/
theorem tendsto_canonLogH {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g H) (hne : ∀ w ∈ H, deriv g w ≠ 0) {w : ℂ}
    (hw : w ∈ H) :
    Tendsto (fun n => log (deriv g I) + logRatioSum (deriv g) I w n) atTop (𝓝 (canonLogH g w)) := by
  obtain ⟨hM, hMI⟩ := isDerivLog_canonLogH hg hne
  have hseg : segment ℝ I w ⊆ H := (convex_halfSpace_gt Complex.imLm.isLinear 0).segment_subset I_mem_H hw
  have h := tendsto_logRatioSum (hM.1.continuousOn.mono hseg) fun z hz => hM.2 z (hseg hz)
  have h2 := h.const_add (log (deriv g I))
  rw [hMI, add_sub_cancel] at h2
  exact h2

end Telescope

/-! ### Measurability of the canonical logarithm -/

section Meas

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The canonical logarithm is measurable at fixed points** for a random family of conformal maps of `ℍ` whose
derivatives are measurable at fixed points (a limit of finite sums of principal logarithms of ratios). -/
theorem measurable_canonLogH_apply {g : Ω → ℂ → ℂ} (hg : ∀ ω, DifferentiableOn ℂ (g ω) H)
    (hne : ∀ ω, ∀ w ∈ H, deriv (g ω) w ≠ 0) (hd : ∀ w ∈ H, Measurable fun ω => deriv (g ω) w) {w : ℂ}
    (hw : w ∈ H) : Measurable fun ω => canonLogH (g ω) w := by
  have hseg : ∀ n k : ℕ, k ≤ n + 1 → segPt I w n k ∈ H := fun n k hk =>
    (convex_halfSpace_gt Complex.imLm.isLinear 0).segment_subset I_mem_H hw (segPt_mem_segment I w hk)
  refine measurable_of_tendsto_metrizable
    (f := fun n ω => log (deriv (g ω) I) + logRatioSum (deriv (g ω)) I w n) (fun n => ?_)
    (tendsto_pi_nhds.2 fun ω => tendsto_canonLogH (hg ω) (hne ω) hw)
  refine (Complex.measurable_log.comp (hd I I_mem_H)).add ?_
  refine Finset.measurable_sum _ fun k hk => ?_
  have hk' : k < n + 1 := Finset.mem_range.1 hk
  exact Complex.measurable_log.comp ((hd _ (hseg n (k + 1) hk')).div (hd _ (hseg n k hk'.le)))

/-- **The canonical logarithm is jointly measurable** on `ℍ × Ω` (Carathéodory: continuous in the point, measurable
in the sample). -/
theorem measurable_uncurry_canonLogH {g : Ω → ℂ → ℂ} (hg : ∀ ω, DifferentiableOn ℂ (g ω) H)
    (hne : ∀ ω, ∀ w ∈ H, deriv (g ω) w ≠ 0) (hd : ∀ w ∈ H, Measurable fun ω => deriv (g ω) w) :
    Measurable fun p : H × Ω => canonLogH (g p.2) p.1 := by
  refine measurable_uncurry_of_continuous_of_measurable (u := fun (x : H) ω => canonLogH (g ω) x) (fun ω => ?_)
    fun x => measurable_canonLogH_apply hg hne hd x.2
  exact continuousOn_iff_continuous_domRestrict.1 (isDerivLog_canonLogH (hg ω) (hne ω)).1.1.continuousOn

end Meas

/-! ### The inverse of a conformal bijection onto `ℍ` -/

section Inverse

/-- The inverse of a conformal bijection `ψ : D → ℍ` of an open `D ⊆ ℍ`: holomorphic on `ℍ` with nonvanishing
derivative, a bijection of `ℍ` onto `D` inverting `ψ` on both sides. -/
theorem invFunOn_props {D : Set ℂ} {ψ : ℂ → ℂ} (hDo : IsOpen D) (hψ : IsConformalBijection ψ D H) :
    DifferentiableOn ℂ (invFunOn ψ D) H ∧ (∀ w ∈ H, invFunOn ψ D w ∈ D) ∧
      (∀ w ∈ H, ψ (invFunOn ψ D w) = w) ∧ (∀ z ∈ D, invFunOn ψ D (ψ z) = z) ∧ InjOn (invFunOn ψ D) H ∧
      invFunOn ψ D '' H = D ∧ ∀ w ∈ H, deriv (invFunOn ψ D) w ≠ 0 := by
  have hinv_mem : ∀ w ∈ H, invFunOn ψ D w ∈ D := fun w hw => (invFunOn_pos (hψ.2.surjOn hw)).1
  have hψinv : ∀ w ∈ H, ψ (invFunOn ψ D w) = w := fun w hw => (invFunOn_pos (hψ.2.surjOn hw)).2
  have hinvψ : ∀ z ∈ D, invFunOn ψ D (ψ z) = z := fun z hz => hψ.2.injOn.leftInvOn_invFunOn hz
  have hdiff : DifferentiableOn ℂ (invFunOn ψ D) H := by
    have h := SmallGammaGeodesics.CC.differentiableOn_leftInv hDo hψ.1 hψ.2.injOn hinvψ
    rwa [hψ.2.image_eq] at h
  have hinj : InjOn (invFunOn ψ D) H := fun w₁ hw₁ w₂ hw₂ he => by
    rw [← hψinv w₁ hw₁, he, hψinv w₂ hw₂]
  have himg : invFunOn ψ D '' H = D :=
    Subset.antisymm (fun _ ⟨w, hw, he⟩ => he ▸ hinv_mem w hw) fun z hz => ⟨ψ z, hψ.2.mapsTo hz, hinvψ z hz⟩
  exact ⟨hdiff, hinv_mem, hψinv, hinvψ, hinj, himg,
    fun w hw => QuantumZipper.CA.deriv_ne_zero_of_injOn isOpen_H hdiff hinj hw⟩

end Inverse

/-! ### The random pocket chart -/

section Chart

variable {Ω : Type*}

open Classical in
/-- The forward map of the pocket chart: `ψ ω` on `A`, the identity off `A`. -/
def pFwd (A : Set Ω) (ψ : Ω → ℂ → ℂ) (ω : Ω) : ℂ → ℂ := if ω ∈ A then ψ ω else id

open Classical in
/-- The inverse map of the pocket chart: `(ψ ω)⁻¹` on `A`, the identity off `A`. -/
def pInv (A : Set Ω) (C : Ω → Set ℂ) (ψ : Ω → ℂ → ℂ) (ω : Ω) : ℂ → ℂ :=
  if ω ∈ A then invFunOn (ψ ω) (C ω) else id

/-- The derivative logarithm of the pocket chart's forward map: `−canonLogH ((ψ ω)⁻¹) ∘ ψ ω`. -/
def pLog (A : Set Ω) (C : Ω → Set ℂ) (ψ : Ω → ℂ → ℂ) (ω : Ω) (z : ℂ) : ℂ :=
  -canonLogH (pInv A C ψ ω) (pFwd A ψ ω z)

/-- **The pocket chart**: `(ψ, ψ⁻¹, Im ℓ)` with `ℓ = −canonLogH (ψ⁻¹) ∘ ψ`. -/
def pChart (A : Set Ω) (C : Ω → Set ℂ) (ψ : Ω → ℂ → ℂ) (ω : Ω) : Chart :=
  (pFwd A ψ ω, pInv A C ψ ω, fun z => (pLog A C ψ ω z).im)

variable {A : Set Ω} {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ}

theorem pFwd_of_mem {ω : Ω} (hω : ω ∈ A) : pFwd A ψ ω = ψ ω := by simp only [pFwd, hω, ↓reduceIte]

theorem pFwd_of_notMem {ω : Ω} (hω : ω ∉ A) : pFwd A ψ ω = id := by simp only [pFwd, hω, ↓reduceIte]

theorem pInv_of_mem {ω : Ω} (hω : ω ∈ A) : pInv A C ψ ω = invFunOn (ψ ω) (C ω) := by
  simp only [pInv, hω, ↓reduceIte]

theorem pInv_of_notMem {ω : Ω} (hω : ω ∉ A) : pInv A C ψ ω = id := by simp only [pInv, hω, ↓reduceIte]

/-- The inverse map of the pocket chart is a conformal map of `ℍ` with nonvanishing derivative, and the chart is
conformal; on `A` its domain is the pocket. -/
theorem pChart_props (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (ω : Ω) :
    DifferentiableOn ℂ (pInv A C ψ ω) H ∧ (∀ w ∈ H, deriv (pInv A C ψ ω) w ≠ 0) ∧
      (pChart A C ψ ω).IsConformal ∧
      ((pChart A C ψ ω).dom : Set ℂ) = {z | (ω ∈ A ∧ z ∈ C ω) ∨ (ω ∉ A ∧ z ∈ H)} := by
  by_cases hω : ω ∈ A
  · obtain ⟨hd, hmem, hψinv, -, -, himg, hne⟩ := invFunOn_props (hCo ω hω) (hψ ω hω)
    have hconf : (pChart A C ψ ω).IsConformal := by
      refine ⟨?_, fun w hw => ?_, fun w hw => ?_⟩
      · change DifferentiableOn ℂ (pInv A C ψ ω) H
        rw [pInv_of_mem hω]; exact hd
      · change pInv A C ψ ω w ∈ H
        rw [pInv_of_mem hω]; exact hCH ω hω (hmem w hw)
      · change pFwd A ψ ω (pInv A C ψ ω w) = w
        rw [pInv_of_mem hω, pFwd_of_mem hω]; exact hψinv w hw
    refine ⟨by rw [pInv_of_mem hω]; exact hd, by rw [pInv_of_mem hω]; exact hne, hconf, ?_⟩
    rw [hconf.coe_dom]
    change pInv A C ψ ω '' H = _
    rw [pInv_of_mem hω, himg]
    ext z
    simp only [mem_ofPred_eq, hω, true_and, not_true_eq_false, false_and, or_false]
  · have hconf : (pChart A C ψ ω).IsConformal := by
      refine ⟨?_, fun w hw => ?_, fun w _ => ?_⟩
      · change DifferentiableOn ℂ (pInv A C ψ ω) H
        rw [pInv_of_notMem hω]; exact differentiableOn_id
      · change pInv A C ψ ω w ∈ H
        rw [pInv_of_notMem hω]; exact hw
      · change pFwd A ψ ω (pInv A C ψ ω w) = w
        rw [pInv_of_notMem hω, pFwd_of_notMem hω]; rfl
    refine ⟨by rw [pInv_of_notMem hω]; exact differentiableOn_id, fun w _ => ?_, hconf, ?_⟩
    · rw [pInv_of_notMem hω, deriv_id]; exact one_ne_zero
    · rw [hconf.coe_dom]
      change pInv A C ψ ω '' H = _
      rw [pInv_of_notMem hω, image_id]
      ext z
      simp only [mem_ofPred_eq, hω, false_and, not_false_eq_true, true_and, false_or]

/-- **The derivative logarithm of the pocket chart** on `A`: `ℓ = −canonLogH (ψ⁻¹) ∘ ψ` is an analytic logarithm of
`ψ′` on the pocket, and the lift is its imaginary part. -/
theorem isDerivLog_pLog (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H)
    {ω : Ω} (hω : ω ∈ A) : IsDerivLog (pChart A C ψ ω).1 (pLog A C ψ ω) (C ω) := by
  obtain ⟨hd, -, -, -, hinj, himg, hne⟩ := invFunOn_props (hCo ω hω) (hψ ω hω)
  set g := invFunOn (ψ ω) (C ω) with hg
  have hM := (isDerivLog_canonLogH hd hne).1
  have hinvbij : IsConformalBijection g H (C ω) := ⟨hd, himg ▸ hinj.bijOn_image⟩
  have hL := hM.invFunOn isOpen_H hinvbij
  have heq : EqOn (invFunOn g H) (ψ ω) (C ω) := fun z hz => by
    obtain ⟨w, hw, rfl⟩ := himg.symm ▸ hz
    rw [hinj.leftInvOn_invFunOn hw, (invFunOn_pos ((hψ ω hω).2.surjOn hw)).2]
  have hLψ := hL.congr_of_eqOn (hCo ω hω) heq
  have hlog : EqOn (fun z => -canonLogH g (invFunOn g H z)) (pLog A C ψ ω) (C ω) := fun z hz => by
    change -canonLogH g (invFunOn g H z) = -canonLogH (pInv A C ψ ω) (pFwd A ψ ω z)
    rw [heq hz, pInv_of_mem hω, pFwd_of_mem hω]
  refine ⟨hLψ.1.congr fun z hz => (hlog hz).symm, fun z hz => ?_⟩
  change exp (pLog A C ψ ω z) = deriv (pFwd A ψ ω) z
  rw [← hlog hz, hLψ.2 z hz, pFwd_of_mem hω]

end Chart

/-! ### The pocket chart is measurable -/

section ChartMeas

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {A : Set Ω} {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ}

omit mΩ in
theorem mem_dom_pChart_iff (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (ω : Ω) (z : ℂ) :
    z ∈ (pChart A C ψ ω).dom ↔ (ω ∈ A ∧ z ∈ C ω) ∨ (ω ∉ A ∧ z ∈ H) := by
  rw [← SetLike.mem_coe, (pChart_props hCo hCH hψ ω).2.2.2]
  rfl

/-- The domain events of the pocket chart are measurable. -/
theorem measurableSet_mem_dom_pChart (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (hA : MeasurableSet A)
    (hCm : ∀ z, MeasurableSet {ω | ω ∈ A ∧ z ∈ C ω}) (z : ℂ) :
    MeasurableSet {ω | z ∈ (pChart A C ψ ω).dom} := by
  have e : {ω | z ∈ (pChart A C ψ ω).dom} = {ω | ω ∈ A ∧ z ∈ C ω} ∪ (Aᶜ ∩ {_ω | z ∈ H}) := by
    ext ω
    rw [mem_ofPred_eq, mem_dom_pChart_iff hCo hCH hψ]
    rfl
  rw [e]
  exact (hCm z).union (hA.compl.inter (MeasurableSet.const _))

/-- The forward values of the pocket chart at fixed points are measurable on the domain events. -/
theorem measurable_fwd_pChart (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (hA : MeasurableSet A)
    (hψm : ∀ z, Measurable ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z)) (z : ℂ) :
    Measurable ({ω | z ∈ (pChart A C ψ ω).dom}.indicator fun ω => (pChart A C ψ ω).1 z) := by
  have e : {ω | z ∈ (pChart A C ψ ω).dom}.indicator (fun ω => (pChart A C ψ ω).1 z) =
      {ω | ω ∈ A ∧ z ∈ C ω}.indicator (fun ω => ψ ω z) + (Aᶜ ∩ {_ω | z ∈ H}).indicator fun _ => z := by
    funext ω
    have hD := mem_dom_pChart_iff hCo hCH hψ ω z
    by_cases hω : ω ∈ A
    · have hf : (pChart A C ψ ω).1 z = ψ ω z := congrFun (pFwd_of_mem hω) z
      have h3 : ω ∉ Aᶜ ∩ {_ω | z ∈ H} := fun h => h.1 hω
      by_cases hz : z ∈ C ω
      · rw [Pi.add_apply, indicator_of_mem (show ω ∈ {ω | z ∈ (pChart A C ψ ω).dom} from hD.2 (Or.inl ⟨hω, hz⟩)),
          indicator_of_mem (show ω ∈ {ω | ω ∈ A ∧ z ∈ C ω} from ⟨hω, hz⟩), indicator_of_notMem h3, add_zero, hf]
      · have h1 : ω ∉ {ω | z ∈ (pChart A C ψ ω).dom} := fun h => by
          rcases hD.1 h with h' | h'
          · exact hz h'.2
          · exact h'.1 hω
        rw [Pi.add_apply, indicator_of_notMem h1,
          indicator_of_notMem (show ω ∉ {ω | ω ∈ A ∧ z ∈ C ω} from fun h => hz h.2), indicator_of_notMem h3,
          add_zero]
    · have hf : (pChart A C ψ ω).1 z = z := congrFun (pFwd_of_notMem hω) z
      have h2 : ω ∉ {ω | ω ∈ A ∧ z ∈ C ω} := fun h => hω h.1
      by_cases hz : z ∈ H
      · rw [Pi.add_apply, indicator_of_mem (show ω ∈ {ω | z ∈ (pChart A C ψ ω).dom} from hD.2 (Or.inr ⟨hω, hz⟩)),
          indicator_of_notMem h2, indicator_of_mem (show ω ∈ Aᶜ ∩ {_ω | z ∈ H} from ⟨hω, hz⟩), zero_add, hf]
      · have h1 : ω ∉ {ω | z ∈ (pChart A C ψ ω).dom} := fun h => by
          rcases hD.1 h with h' | h'
          · exact hω h'.1
          · exact hz h'.2
        rw [Pi.add_apply, indicator_of_notMem h1, indicator_of_notMem h2,
          indicator_of_notMem (show ω ∉ Aᶜ ∩ {_ω | z ∈ H} from fun h => hz h.2), add_zero]
  rw [e]
  exact (hψm z).add (measurable_const.indicator (hA.compl.inter (MeasurableSet.const _)))

/-- **The pocket chart of a random conformal bijection** (Aux. lemma 119's measurably selected derivative-logarithm
lift): on a measurable event `A`, if `ψ ω` is a conformal bijection of the open `C ω ⊆ ℍ` onto `ℍ`, and the membership
events `{z ∈ C}` and the values `ψ(z)` at fixed points are measurable, then `pChart A C ψ` is a pocket chart on `A`
(`IsPocketChartOn`) whose forward map has the analytic logarithm `pLog A C ψ` with imaginary part the lift. -/
theorem isPocketChartOn_pChart (hA : MeasurableSet A) (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (hCm : ∀ z, MeasurableSet {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z)) :
    PocketCoupling.IsPocketChartOn mΩ A C ψ (pChart A C ψ) ∧
      ∀ ω ∈ A, IsDerivLog (pChart A C ψ ω).1 (pLog A C ψ ω) (pChart A C ψ ω).dom ∧
        ∀ z ∈ (pChart A C ψ ω).dom, (pChart A C ψ ω).2.2 z = (pLog A C ψ ω z).im := by
  have hprops := pChart_props hCo hCH hψ
  have hdomA : ∀ ω ∈ A, ((pChart A C ψ ω).dom : Set ℂ) = C ω := fun ω hω => by
    rw [(hprops ω).2.2.2]
    ext z
    simp only [mem_ofPred_eq, hω, true_and, not_true_eq_false, false_and, or_false]
  have hlogA : ∀ ω ∈ A, IsDerivLog (pChart A C ψ ω).1 (pLog A C ψ ω) (pChart A C ψ ω).dom := fun ω hω => by
    rw [hdomA ω hω]
    exact isDerivLog_pLog hCo hψ hω
  refine ⟨⟨fun ω hω => ⟨(hprops ω).2.2.1, hdomA ω hω, fun z _ => congrFun (pFwd_of_mem hω) z, ?_⟩, fun z => ?_⟩,
    fun ω hω => ⟨hlogA ω hω, fun _ _ => rfl⟩⟩
  · exact Complex.continuous_im.comp_continuousOn (hlogA ω hω).1.continuousOn
  · -- the lift at a fixed point, through the jointly measurable canonical logarithm
    set S := {ω | ω ∈ A ∧ z ∈ C ω} with hS
    have hd : ∀ w ∈ H, Measurable fun ω => deriv (pInv A C ψ ω) w := fun w hw =>
      Lemma72B.measurable_deriv_inv_apply (c := pChart A C ψ) (fun ω => (hprops ω).2.2.1)
        (measurableSet_mem_dom_pChart hCo hCH hψ hA hCm) (measurable_fwd_pChart hCo hCH hψ hA hψm) hw
    have hJ := measurable_uncurry_canonLogH (g := pInv A C ψ) (fun ω => (hprops ω).1) (fun ω => (hprops ω).2.1) hd
    have hqH : ∀ ω, S.indicator (fun ω => ψ ω z) ω + Sᶜ.indicator (fun _ => I) ω ∈ H := by
      intro ω
      by_cases hω : ω ∈ S
      · rw [indicator_of_mem hω, indicator_of_notMem (show ω ∉ Sᶜ from fun h => h hω), add_zero]
        exact (hψ ω hω.1).2.mapsTo hω.2
      · rw [indicator_of_notMem hω, indicator_of_mem (show ω ∈ Sᶜ from hω), zero_add]
        exact I_mem_H
    set q : Ω → H := fun ω => ⟨_, hqH ω⟩ with hq
    have hqm : Measurable q :=
      ((hψm z).add (measurable_const.indicator (hCm z).compl)).subtype_mk
    have hF : Measurable fun ω => -(canonLogH (pInv A C ψ ω) (q ω)).im :=
      (Complex.measurable_im.comp (hJ.comp (hqm.prodMk measurable_id))).neg
    have e : S.indicator (fun ω => (pChart A C ψ ω).2.2 z) =
        S.indicator fun ω => -(canonLogH (pInv A C ψ ω) (q ω)).im := by
      funext ω
      by_cases hω : ω ∈ S
      · rw [indicator_of_mem hω, indicator_of_mem hω]
        have hqω : (q ω : ℂ) = pFwd A ψ ω z := by
          rw [hq]
          change S.indicator (fun ω => ψ ω z) ω + Sᶜ.indicator (fun _ => I) ω = pFwd A ψ ω z
          rw [indicator_of_mem hω, indicator_of_notMem (show ω ∉ Sᶜ from fun h => h hω), add_zero,
            pFwd_of_mem hω.1]
        change (pLog A C ψ ω z).im = _
        rw [pLog, hqω, neg_im]
      · rw [indicator_of_notMem hω, indicator_of_notMem hω]
    rw [e]
    exact hF.indicator (hCm z)

end ChartMeas

/-! ### Shifting the branch by a measurable integer -/

section Shift

variable {Ω : Type*}

/-- The chart with its lift shifted by `−2πn`. -/
def shiftChart (c : Chart) (n : ℤ) : Chart := (c.1, c.2.1, fun z => c.2.2 z - 2 * π * n)

/-- A derivative logarithm shifted by `−2πin` is a derivative logarithm. -/
theorem isDerivLog_sub_int {f L : ℂ → ℂ} {D : Set ℂ} (h : IsDerivLog f L D) (n : ℤ) :
    IsDerivLog f (fun z => L z - n * (2 * π * I)) D :=
  ⟨h.1.sub_const _, fun z hz => by rw [exp_sub, exp_int_mul_two_pi_mul_I, div_one]; exact h.2 z hz⟩

theorem im_sub_int_mul (w : ℂ) (n : ℤ) : (w - n * (2 * π * I)).im = w.im - 2 * π * n := by
  simp only [sub_im, mul_im, intCast_re, intCast_im, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, I_re,
    I_im, zero_mul, sub_zero, mul_one, mul_zero, add_zero]
  ring

/-- **The branch of a pocket chart can be shifted by any measurable integer** (`lift − 2πn`), when the pocket
membership events at fixed points are measurable. -/
theorem isPocketChartOn_shift {𝓦 : MeasurableSpace Ω} {A : Set Ω} {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ}
    {c : Ω → Chart} (hc : PocketCoupling.IsPocketChartOn 𝓦 A C ψ c)
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω}) {n : Ω → ℤ} (hn : Measurable[𝓦] n) :
    PocketCoupling.IsPocketChartOn 𝓦 A C ψ fun ω => shiftChart (c ω) (n ω) := by
  refine ⟨fun ω hω => ?_, fun z => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hc.1 ω hω
    exact ⟨h1, h2, h3, h4.sub continuousOn_const⟩
  · have e : {ω | ω ∈ A ∧ z ∈ C ω}.indicator (fun ω => (shiftChart (c ω) (n ω)).2.2 z) =
        fun ω => {ω | ω ∈ A ∧ z ∈ C ω}.indicator (fun ω => (c ω).2.2 z) ω -
          {ω | ω ∈ A ∧ z ∈ C ω}.indicator (fun ω => 2 * π * (n ω : ℝ)) ω := by
      funext ω
      by_cases hω : ω ∈ {ω | ω ∈ A ∧ z ∈ C ω}
      · rw [indicator_of_mem hω, indicator_of_mem hω, indicator_of_mem hω]
        rfl
      · rw [indicator_of_notMem hω, indicator_of_notMem hω, indicator_of_notMem hω, sub_zero]
    rw [e]
    have hnm : Measurable[𝓦] fun ω => 2 * π * (n ω : ℝ) :=
      measurable_const.mul ((measurable_from_top (f := fun k : ℤ => (k : ℝ))).comp hn)
    exact (hc.2 z).sub (hnm.indicator (hCm z))

end Shift

/-! ### The change pocket of the strip system -/

section Pocket

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω}

open WangWu (negInv)
open PocketCoord PocketJordan PocketWordAssembly PocketSeedOpen PocketCoupling

/-- **The pocket chart of the bounded change pocket**: on a walls-measurable event `A ⊆ G` of change configurations, a
walls-point-measurable Jordan coordinate `ψ` is the forward map of the pocket chart `pChart`, measurable for the
walls' σ-algebra, with the derivative logarithm `pLog`. -/
theorem isPocketChartOn_cfPocket {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ) :
    IsPocketChartOn 𝓦 A (fun ω => cfPocket (R ω) (L ω) r) ψ (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ) ∧
      ∀ ω ∈ A, IsDerivLog (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω).1
          (pLog A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω).dom ∧
        ∀ z ∈ (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω).dom,
          (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω).2.2 z =
            (pLog A (fun ω => cfPocket (R ω) (L ω) r) ψ ω z).im := by
  have hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    PocketUnionPt.measurableSet_mem_cfPocket_of_subset hRm hLm hGm hG hA hAG z
  refine isPocketChartOn_pChart (mΩ := 𝓦) hA (fun ω hω => ?_) (fun ω hω => ?_) (fun ω hω => (hψ ω hω).2.2.2.1)
    hCm fun z => ?_
  · exact isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  · exact image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  · exact hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω =>
      ⟨subset_closure hω.2, fun h => (hG ω (hAG hω.1)).cfPt_openPt_notMem (h ▸ hω.2)⟩

/-- **The pocket chart of the change pocket opening at the flow seed** (Jordan coordinates at infinity). -/
theorem isPocketChartOn_cfPocketInf {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ) :
    IsPocketChartOn 𝓦 A (fun ω => cfPocket (R ω) (L ω) r) ψ (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ) ∧
      ∀ ω ∈ A, IsDerivLog (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω).1
          (pLog A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω).dom ∧
        ∀ z ∈ (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω).dom,
          (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω).2.2 z =
            (pLog A (fun ω => cfPocket (R ω) (L ω) r) ψ ω z).im := by
  have hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    PocketUnionPt.measurableSet_mem_cfPocket_of_subset hRm hLm hGm hG hA hAG z
  refine isPocketChartOn_pChart (mΩ := 𝓦) hA (fun ω hω => ?_) (fun ω hω => ?_) (fun ω hω => (hψ ω hω).2.2.2.1)
    hCm fun z => ?_
  · exact isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  · exact image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  · exact hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω => subset_closure hω.2

end Pocket

end InteractingSLE.Sec7.PocketStopField
