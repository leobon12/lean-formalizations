/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.FanTipFiberLaw
import InteractingSLE.Spec.Sec7.FanOptional
import QuantumZipper.Proofs.RS.TraceMeas
import QuantumZipper.Proofs.Zipper.JointModDet

/-!
# Aux. lemma 136: simultaneous singleton active tip fibres

Packet PROVE-SEC7-E (specification §7.5, `source/spec/p433-480.md` L153–L201, pp. 441–442).

**Aux. lemma 136.** Suppose the continuous Loewner trace and the local absolute-continuity hypotheses
of Aux. lemma 135 hold through an increasing sequence of original-filtration stopping horizons
`H_n < T_*` which exhaust the available lifetime. Then, on one probability-one event, at every
`0 < t < T_*` with `η'(t) ∈ ℍ`, `f_t⁻¹({η'(t)}) = {W_t}` (SF1).

## Formal statement

`ae_forall_isSingletonTipFiber`: for a filtration `𝓕` satisfying the usual conditions, an adapted driver
`W` with continuous paths, `W_0 = 0`, generating the continuous Loewner trace `η` (for every sample), and
`𝓕`-stopping times `H_n` such that the hypothesis of Aux. 135 holds for every finite stopping time
`T ≤ H_n`, almost surely, for every `t > 0` with `t < H_n` for some `n` and `η(t) ∈ ℍ`,
`IsSingletonTipFiber W t`. The available lifetime is `T_* = sup_n H_n`; monotonicity of the `H_n` and
`H_n < T_*` are not needed. The trace is assumed for every sample (the specification's "continuous
Loewner trace"; a version modified on a null set of `𝓕₀` has this form). Inputs: Aux. 135
(`FanTipFiberLaw.lean`, with its named input `ZhanStoppingTipFiberStatement`) and the optional section
theorem `OptionalSectionStatement` (`FanOptional.lean`).

## Proof (the specification's)

* **Optionality, verified** (p. 441): for `z ∈ ℍ`, `t ↦ F_t(z)` is continuous
  (`continuous_fwdMapInv_time`, from the joint continuity of QuantumZipper) and adapted
  (`measurable_fwdMapInv_realPath`, from QuantumZipper's measurability of `F_t(z)` in the driver, applied
  to the stopped driver), hence optional (`measurable_optionalSigma_of_continuous`); the vertical limits
  `F̄_t(v) = lim_k F_t(v + i/k)` are optional (`measurable_optionalSigma_extendFrom`).
* **The exceptional sets** (SF2)–(SF3): `tipFiberBadSet W H m` (with `m + 1` in place of the source's
  `m`) is the set of `(t, ω)` with `t ∈ [1/(m+1), m+1]`, `t < H`, `Im η(t) ≥ 1/(m+1)` and
  `inf_{q ∈ ℚ, 1/(m+1) < |q| < m+1} |F̄_t(q) − η(t)| = 0`; it is optional
  (`measurableSet_tipFiberBadSet`). Its points have a second real preimage `v` with
  `1/(m+1) ≤ |v| ≤ m+1` (compactness, `exists_ne_of_mem_tipFiberBadSet`), and every failure of (SF1)
  lies in one of them (`exists_mem_tipFiberBadSet`).
* **Sections**: if the projection of a bad set had positive probability, the optional section theorem
  would give a stopping time `S` with graph in it; Aux. 135 at the bounded stop `S ∧ H_n ∧ (m+1)` shows
  `P(S < ∞) = 0`. The countable union of the null projections contains every failure of (SF1).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal

open QuantumZipper (H Hbar drive fwdMapInv)

namespace InteractingSLE

namespace Sec7

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-! ### Continuity and adaptedness of `t ↦ F_t(z)` -/

/-- For `z ∈ ℍ`, `t ↦ F_t(z)` is continuous on `ℝ≥0` ("the inverse Loewner maps depend continuously on
time locally in the open half-plane"). -/
theorem continuous_fwdMapInv_time {V : ℝ → ℝ} (hV : Continuous V) (hV0 : V 0 = 0) {z : ℂ}
    (hz : z ∈ H) : Continuous fun t : ℝ≥0 => fwdMapInv V t z := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hT : (0 : ℝ) ≤ (t₀ : ℝ) + 1 := by positivity
  have hcont := QuantumZipper.RegUnif.continuousOn_fwdMapInv_joint hV hV0 ((t₀ : ℝ) + 1)
  have h1 : Continuous fun t : ℝ≥0 => fwdMapInv V (min (t : ℝ) ((t₀ : ℝ) + 1)) z := by
    have hf : Continuous fun t : ℝ≥0 => ((min (t : ℝ) ((t₀ : ℝ) + 1)), z) :=
      (NNReal.continuous_coe.min continuous_const).prodMk continuous_const
    exact hcont.comp_continuous hf fun t =>
      ⟨⟨le_min t.coe_nonneg hT, min_le_right _ _⟩, hz⟩
  refine h1.continuousAt.congr ?_
  have hev : ∀ᶠ t : ℝ≥0 in 𝓝 t₀, (t : ℝ) < (t₀ : ℝ) + 1 :=
    (NNReal.continuous_coe.tendsto t₀).eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hev] with t ht
  rw [min_eq_left ht.le]

/-- For an adapted driver with continuous paths and `W_0 = 0`, `ω ↦ F_t(z)` is `𝓕_t`-measurable. -/
theorem measurable_fwdMapInv_realPath {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    (hWa : Adapted 𝓕 W) (hWc : ∀ ω, Continuous fun t : ℝ≥0 => W t ω) (hW0 : ∀ ω, W 0 ω = 0)
    (t : ℝ≥0) {z : ℂ} (hz : 0 < z.im) :
    Measurable[𝓕 t] fun ω => fwdMapInv (realPath W ω) t z := by
  set Ws : ℝ≥0 → Ω → ℝ := fun r ω => W (min r t) ω with hWs
  have hWsm : ∀ r, Measurable[𝓕 t] (Ws r) := fun r =>
    (hWa (min r t)).mono (𝓕.mono (min_le_right r t)) le_rfl
  have hWsc : ∀ ω, Continuous fun r => Ws r ω := fun ω =>
    (hWc ω).comp (continuous_id.min continuous_const)
  have hWs0 : ∀ ω, Ws 0 ω = 0 := fun ω => by simp [hWs, hW0]
  have heq : (fun ω => fwdMapInv (realPath W ω) t z) = fun ω => fwdMapInv (drive 1 Ws ω) t z := by
    funext ω
    have hd : drive 1 Ws ω = realPath Ws ω := by funext s; simp [drive, realPath]
    rw [hd]
    refine fwdMapInv_eqOn_of_eqOn (continuous_realPath (hWc ω)) (realPath_zero (hW0 ω))
      (continuous_realPath (hWsc ω)) (realPath_zero (hWs0 ω)) t.coe_nonneg (fun r hr => ?_)
      (show z ∈ H from hz)
    have hrt : r.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hr.2
    simp only [realPath, hWs, min_eq_left hrt]
  rw [heq]
  exact @QuantumZipper.RS.measurable_fwdMapInv_drive Ω (𝓕 t) Ws hWsm hWsc hWs0 1 t t.coe_nonneg z hz

/-! ### Optionality of the boundary values `F̄_t(v)` -/

theorem im_add_inv_mul_I_pos (v : ℝ) (k : ℕ) :
    0 < ((v : ℂ) + ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * I).im := by
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, zero_add]
  positivity

/-- The points `v + i/(k+1)` approach `v` from inside `ℍ`. -/
theorem tendsto_add_inv_mul_I (v : ℝ) :
    Tendsto (fun k : ℕ => (v : ℂ) + ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * I) atTop (𝓝[H] (v : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => im_add_inv_mul_I_pos v k⟩
  have h : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 := ((Complex.continuous_ofReal.tendsto 0).comp h).mul_const I
  simpa using (tendsto_const_nhds (x := (v : ℂ))).add h2

/-- **The boundary values are optional** (p. 441: "For every realized continuous trace, the active
inverse maps extend continuously to the boundary at every time. Taking the vertical limit `k → ∞`
proves that `t ↦ f_t(W_t + v)` is optional … Pointwise limits of optional measurable functions are
optional."). -/
theorem measurable_optionalSigma_extendFrom {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {η : Ω → ℝ → ℂ} (hWa : Adapted 𝓕 W) (hWc : ∀ ω, Continuous fun t : ℝ≥0 => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hη : ∀ ω, IsLoewnerTrace (realPath W ω) (η ω)) (v : ℝ) :
    Measurable[optionalSigma 𝓕]
      fun p : ℝ≥0 × Ω => extendFrom H (fwdMapInv (realPath W p.2) p.1) (v : ℂ) := by
  let _ : MeasurableSpace (ℝ≥0 × Ω) := optionalSigma 𝓕
  have hk : ∀ k : ℕ, Measurable fun p : ℝ≥0 × Ω =>
      fwdMapInv (realPath W p.2) p.1 ((v : ℂ) + ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * I) := fun k =>
    measurable_optionalSigma_of_continuous
      (X := fun t ω => fwdMapInv (realPath W ω) t ((v : ℂ) + ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * I))
      (fun t => measurable_fwdMapInv_realPath hWa hWc hW0 t (im_add_inv_mul_I_pos v k))
      (fun ω => continuous_fwdMapInv_time (continuous_realPath (hWc ω)) (realPath_zero (hW0 ω))
        (im_add_inv_mul_I_pos v k))
  refine measurable_of_tendsto_metrizable hk (tendsto_pi_nhds.2 fun p => ?_)
  have hb := ((hη p.2).hasBdryLimits (continuous_realPath (hWc p.2)) (realPath_zero (hW0 p.2))
    p.1.coe_nonneg).tendsto (mem_Hbar_of_im_eq_zero (by simp) : (v : ℂ) ∈ Hbar)
  exact hb.comp (tendsto_add_inv_mul_I v)

/-! ### The exceptional sets (SF2)–(SF3) -/

/-- **The exceptional set `E_{n,m}` of (SF3)** for the horizon `Hor = H_n`, with `m + 1` in place of
the source's `m`: the `(t, ω)` with `t ∈ [1/(m+1), m+1]`, `t < H_n`, `Im η(t) ≥ 1/(m+1)` and
`X^{n,m}_t = inf_{q ∈ ℚ, 1/(m+1) < |q| < m+1} |F̄_t(q) − η(t)| = 0` (the tip is `F̄_t(0)`). -/
def tipFiberBadSet (W : ℝ≥0 → Ω → ℝ) (Hor : Ω → WithTop ℝ≥0) (m : ℕ) : Set (ℝ≥0 × Ω) :=
  {p | 1 / ((m : ℝ) + 1) ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ (m : ℝ) + 1 ∧ (p.1 : WithTop ℝ≥0) < Hor p.2 ∧
    1 / ((m : ℝ) + 1) ≤ (loewnerTip (realPath W p.2) p.1).im ∧
    ∀ j : ℕ, ∃ q : ℚ, (1 / ((m : ℝ) + 1) < |(q : ℝ)| ∧ |(q : ℝ)| < (m : ℝ) + 1) ∧
      dist (extendFrom H (fwdMapInv (realPath W p.2) p.1) ((q : ℝ) : ℂ))
        (loewnerTip (realPath W p.2) p.1) < 1 / ((j : ℝ) + 1)}

/-- **The exceptional set is optional** (p. 442: "The set `E_{n,m}` … is optional"). -/
theorem measurableSet_tipFiberBadSet {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {η : Ω → ℝ → ℂ} (hWa : Adapted 𝓕 W) (hWc : ∀ ω, Continuous fun t : ℝ≥0 => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hη : ∀ ω, IsLoewnerTrace (realPath W ω) (η ω))
    {Hor : Ω → WithTop ℝ≥0} (hH : IsStoppingTime 𝓕 Hor) (m : ℕ) :
    MeasurableSet[optionalSigma 𝓕] (tipFiberBadSet W Hor m) := by
  let _ : MeasurableSpace (ℝ≥0 × Ω) := optionalSigma 𝓕
  have htime : Measurable fun p : ℝ≥0 × Ω => (p.1 : ℝ) :=
    measurable_optionalSigma_of_continuous (X := fun t (_ : Ω) => (t : ℝ))
      (fun _ => measurable_const) (fun _ => NNReal.continuous_coe)
  have htip : Measurable fun p : ℝ≥0 × Ω => loewnerTip (realPath W p.2) p.1 := by
    have h := measurable_optionalSigma_extendFrom hWa hWc hW0 hη 0
    simpa [loewnerTip] using h
  have hZ : ∀ q : ℚ, Measurable fun p : ℝ≥0 × Ω =>
      extendFrom H (fwdMapInv (realPath W p.2) p.1) ((q : ℝ) : ℂ) := fun q =>
    measurable_optionalSigma_extendFrom hWa hWc hW0 hη q
  have hHor : MeasurableSet {p : ℝ≥0 × Ω | (p.1 : WithTop ℝ≥0) < Hor p.2} := by
    have h := (measurableSet_optionalSigma_stochInterval hH).compl
    convert h using 1
    ext p
    exact (lt_iff_not_ge : (p.1 : WithTop ℝ≥0) < Hor p.2 ↔ _)
  have hlast : MeasurableSet {p : ℝ≥0 × Ω | ∀ j : ℕ, ∃ q : ℚ,
      (1 / ((m : ℝ) + 1) < |(q : ℝ)| ∧ |(q : ℝ)| < (m : ℝ) + 1) ∧
      dist (extendFrom H (fwdMapInv (realPath W p.2) p.1) ((q : ℝ) : ℂ))
        (loewnerTip (realPath W p.2) p.1) < 1 / ((j : ℝ) + 1)} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists, Set.ofPred_and]
    exact MeasurableSet.iInter fun j => MeasurableSet.iUnion fun q =>
      ((MeasurableSet.const _).inter (MeasurableSet.const _)).inter
        (measurableSet_lt ((hZ q).dist htip) measurable_const)
  exact (measurableSet_le measurable_const htime).inter ((measurableSet_le htime measurable_const).inter
    (hHor.inter ((measurableSet_le measurable_const (Complex.measurable_im.comp htip)).inter hlast)))

/-- Along a continuous Loewner trace, `x ↦ F̄_t(x)` is continuous on `ℝ`. -/
theorem continuous_extendFrom_ofReal {V : ℝ → ℝ} {γ : ℝ → ℂ} (hγ : IsLoewnerTrace V γ)
    (hV : Continuous V) (hV0 : V 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    Continuous fun x : ℝ => extendFrom H (fwdMapInv V t) (x : ℂ) :=
  (hγ.hasBdryLimits hV hV0 ht).continuousOn.comp_continuous Complex.continuous_ofReal
    fun x => mem_Hbar_of_im_eq_zero (by simp)

/-- **A point of the exceptional set has a second real preimage** (p. 442: "For each fixed time the
inverse map is continuous on the compact real set in (SF2). Thus `X^{n,m}_t = 0` is equivalent to the
existence of an actual `v ∈ I_m` with `f_t(W_t + v) = η'(t)`"). -/
theorem exists_ne_of_mem_tipFiberBadSet {W : ℝ≥0 → Ω → ℝ} {η : Ω → ℝ → ℂ}
    (hWc : ∀ ω, Continuous fun t : ℝ≥0 => W t ω) (hW0 : ∀ ω, W 0 ω = 0)
    (hη : ∀ ω, IsLoewnerTrace (realPath W ω) (η ω)) {Hor : Ω → WithTop ℝ≥0} {m : ℕ}
    {p : ℝ≥0 × Ω} (hp : p ∈ tipFiberBadSet W Hor m) :
    ∃ v : ℝ, 1 / ((m : ℝ) + 1) ≤ |v| ∧
      extendFrom H (fwdMapInv (realPath W p.2) p.1) (v : ℂ) = loewnerTip (realPath W p.2) p.1 := by
  obtain ⟨-, -, -, -, hq⟩ := hp
  choose q hqI hqd using hq
  have hcF := continuous_extendFrom_ofReal (hη p.2) (continuous_realPath (hWc p.2))
    (realPath_zero (hW0 p.2)) p.1.coe_nonneg
  have hmem : ∀ j, ((q j : ℚ) : ℝ) ∈ Icc (-((m : ℝ) + 1)) ((m : ℝ) + 1) := fun j =>
    abs_le.1 (hqI j).2.le
  obtain ⟨v, -, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
  refine ⟨v, ?_, ?_⟩
  · exact ge_of_tendsto' ((continuous_abs.tendsto v).comp hlim) fun j => (hqI (φ j)).1.le
  · have h1 := ((hcF.tendsto v).comp hlim).dist
      (tendsto_const_nhds (x := loewnerTip (realPath W p.2) p.1))
    have h0 : Tendsto (fun j => 1 / ((φ j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    exact dist_le_zero.1 (le_of_tendsto_of_tendsto' h1 h0 fun j => (hqd (φ j)).le)

/-- **Every failure of (SF1) lies in an exceptional set** (p. 442: "Every positive available time with
an interior tip and a second finite real preimage belongs to some `E_{n,m}`"). -/
theorem exists_mem_tipFiberBadSet {W : ℝ≥0 → Ω → ℝ} {η : Ω → ℝ → ℂ}
    (hWc : ∀ ω, Continuous fun t : ℝ≥0 => W t ω) (hW0 : ∀ ω, W 0 ω = 0)
    (hη : ∀ ω, IsLoewnerTrace (realPath W ω) (η ω)) {Hor : Ω → WithTop ℝ≥0} {ω : Ω}
    {t : ℝ≥0} (htH : (t : WithTop ℝ≥0) < Hor ω) (ht : 0 < t) (hpH : η ω t ∈ H)
    (hns : ¬ IsSingletonTipFiber (realPath W ω) t) : ∃ m : ℕ, (t, ω) ∈ tipFiberBadSet W Hor m := by
  have hV := continuous_realPath (hWc ω)
  have hV0 := realPath_zero (hW0 ω)
  have htip : loewnerTip (realPath W ω) t = η ω t := (hη ω).loewnerTip_eq hV hV0 t.coe_nonneg
  unfold IsSingletonTipFiber at hns
  push Not at hns
  obtain ⟨v, hv, hv0⟩ := hns
  have ha : 0 < |v| := abs_pos.2 hv0
  have hb : (0 : ℝ) < t := by exact_mod_cast ht
  have hc : 0 < (loewnerTip (realPath W ω) t).im := by rw [htip]; exact hpH
  obtain ⟨m, hm⟩ := exists_nat_gt (max (max (1 / |v|) |v|)
    (max (max (1 / (t : ℝ)) t) (1 / (loewnerTip (realPath W ω) t).im)))
  have hm1 : (m : ℝ) < (m : ℝ) + 1 := lt_add_one _
  have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have key : ∀ x : ℝ, 0 < x → 1 / x ≤ (m : ℝ) → 1 / ((m : ℝ) + 1) < x := fun x hx h =>
    (one_div_lt hm0 hx).2 (h.trans_lt hm1)
  have h1 : 1 / |v| ≤ (m : ℝ) := ((le_max_left _ _).trans (le_max_left _ _)).trans hm.le
  have h2 : |v| ≤ (m : ℝ) := ((le_max_right _ _).trans (le_max_left _ _)).trans hm.le
  have h3 : 1 / (t : ℝ) ≤ (m : ℝ) :=
    (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hm.le
  have h4 : (t : ℝ) ≤ (m : ℝ) :=
    (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hm.le
  have h5 : 1 / (loewnerTip (realPath W ω) t).im ≤ (m : ℝ) :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hm.le
  refine ⟨m, (key _ hb h3).le, h4.trans hm1.le, htH, (key _ hc h5).le, fun j => ?_⟩
  have hcF := continuous_extendFrom_ofReal (hη ω) hV hV0 t.coe_nonneg
  have hU : IsOpen {x : ℝ | 1 / ((m : ℝ) + 1) < |x| ∧ |x| < (m : ℝ) + 1} :=
    (isOpen_lt continuous_const continuous_abs).inter (isOpen_lt continuous_abs continuous_const)
  obtain ⟨δ', hδ', hball⟩ := Metric.isOpen_iff.1 hU v ⟨key _ ha h1, h2.trans_lt hm1⟩
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.1 hcF v (1 / ((j : ℝ) + 1)) (by positivity)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show v - min δ δ' < v + min δ δ' by
    linarith [lt_min hδ hδ'])
  have hqv : dist (q : ℝ) v < min δ δ' := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  refine ⟨q, hball (hqv.trans_le (min_le_right _ _)), ?_⟩
  have h := hcont (q : ℝ) (hqv.trans_le (min_le_left _ _))
  rwa [hv] at h

/-! ### Aux. lemma 136 -/

/-- **The projection of an exceptional set is null** (p. 442: "If its projection had positive
probability, the optional section theorem would supply a stopping time `S` whose finite graph lies in
`E_{n,m}` … Put `Ŝ = S ∧ H_n ∧ m` … Thus `{S < ∞}` … has probability zero"). -/
theorem measure_snd_image_tipFiberBadSet {κ' : ℝ} (hZ : ZhanStoppingTipFiberStatement.{u} κ')
    (hOS : OptionalSectionStatement.{u}) {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (h𝓕 : IsUsualFiltration 𝓕 P) {W : ℝ≥0 → Ω → ℝ} {η : Ω → ℝ → ℂ}
    (hWa : Adapted 𝓕 W) (hWc : ∀ ω, Continuous fun t : ℝ≥0 => W t ω) (hW0 : ∀ ω, W 0 ω = 0)
    (hη : ∀ ω, IsLoewnerTrace (realPath W ω) (η ω)) {Hor : Ω → WithTop ℝ≥0}
    (hH : IsStoppingTime 𝓕 Hor)
    (hloc : ∀ T : Ω → ℝ≥0, IsStoppingTime 𝓕 (fun ω => (T ω : WithTop ℝ≥0)) →
      (∀ ω, (T ω : WithTop ℝ≥0) ≤ Hor ω) →
      ∀ a : ℚ, 0 < a → IsLocallyBrownianAfter κ' 𝓕 P W (a : ℝ).toNNReal T) (m : ℕ) :
    P (Prod.snd '' tipFiberBadSet W Hor m) = 0 := by
  by_contra hpos
  obtain ⟨S, hS, hSpos, hSgraph⟩ := hOS P 𝓕 h𝓕 _
    (measurableSet_tipFiberBadSet hWa hWc hW0 hη hH m) hpos
  set c : WithTop ℝ≥0 := (((m : ℝ≥0) + 1 : ℝ≥0) : WithTop ℝ≥0) with hc
  have hne : ∀ ω, min (min (S ω) (Hor ω)) c ≠ ⊤ := fun ω =>
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
  set T : Ω → ℝ≥0 := fun ω => (min (min (S ω) (Hor ω)) c).untop (hne ω) with hTdef
  have hTc : (fun ω => (T ω : WithTop ℝ≥0)) = fun ω => min (min (S ω) (Hor ω)) c := by
    funext ω; exact WithTop.coe_untop _ _
  have hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0) := by
    rw [hTc]; exact (hS.min hH).min (isStoppingTime_const 𝓕 _)
  have hTle : ∀ ω, (T ω : WithTop ℝ≥0) ≤ Hor ω := fun ω => by
    rw [congrFun hTc ω]; exact (min_le_left _ _).trans (min_le_right _ _)
  have h135 := ae_isSingletonTipFiber_of_isLocallyBrownianAfter hZ (ae_of_all P hWc)
    (ae_of_all P hW0) (ae_of_all P hη) hT (hloc T hT hTle)
  apply hSpos
  have hae : ∀ᵐ ω ∂P, S ω = ⊤ := by
    filter_upwards [h135] with ω hω
    by_contra hne'
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hne'
    have hb := hSgraph ω t ht.symm
    obtain ⟨hb1, hb2, hb3, hb4, -⟩ := hb
    have hm0 : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have htm : t ≤ (m : ℝ≥0) + 1 := by
      rw [← NNReal.coe_le_coe]; push_cast; exact hb2
    have hTt : T ω = t := by
      have h1 : min (min (S ω) (Hor ω)) c = (t : WithTop ℝ≥0) := by
        rw [← ht, min_eq_left hb3.le, min_eq_left (WithTop.coe_le_coe.2 htm)]
      exact WithTop.coe_injective ((congrFun hTc ω).trans h1)
    have htpos : 0 < t := by
      rw [← NNReal.coe_pos]; exact hm0.trans_le hb1
    have hpH : η ω t ∈ H := by
      rw [← (hη ω).loewnerTip_eq (continuous_realPath (hWc ω)) (realPath_zero (hW0 ω))
        t.coe_nonneg]
      exact hm0.trans_le hb4
    rw [hTt] at hω
    have hsing := hω htpos hpH
    obtain ⟨v, hv, hFv⟩ := exists_ne_of_mem_tipFiberBadSet hWc hW0 hη (hSgraph ω t ht.symm)
    rw [hsing v hFv, abs_zero] at hv
    exact absurd hv (not_le.2 hm0)
  exact ae_iff.1 hae

/-- **Aux. lemma 136** (simultaneous singleton active tip fibres). Let `𝓕` satisfy the usual
conditions, `W` be an `𝓕`-adapted driver with continuous paths and `W_0 = 0` whose chain has the
continuous Loewner trace `η` (for every sample), and `H_n` be `𝓕`-stopping times such that the
hypotheses of Aux. 135 hold for every finite stopping time `T ≤ H_n`. Then, given the named inputs
[Zha10, Theorem 6.1 (iii)–(iv)] and the optional section theorem, on one probability-one event, at
every `t > 0` before some `H_n` with `η(t) ∈ ℍ`, `f_t⁻¹({η(t)}) = {W_t}` (SF1). Consequently (SF1) holds
at any random time in the available lifetime, including times selected using additional flow lines;
no Brownian or SDE property in an enlarged filtration is asserted. -/
theorem ae_forall_isSingletonTipFiber {κ' : ℝ} (hZ : ZhanStoppingTipFiberStatement.{u} κ')
    (hOS : OptionalSectionStatement.{u}) {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (h𝓕 : IsUsualFiltration 𝓕 P) {W : ℝ≥0 → Ω → ℝ} {η : Ω → ℝ → ℂ}
    (hWa : Adapted 𝓕 W) (hWc : ∀ ω, Continuous fun t : ℝ≥0 => W t ω) (hW0 : ∀ ω, W 0 ω = 0)
    (hη : ∀ ω, IsLoewnerTrace (realPath W ω) (η ω)) {Hn : ℕ → Ω → WithTop ℝ≥0}
    (hH : ∀ n, IsStoppingTime 𝓕 (Hn n))
    (hloc : ∀ n, ∀ T : Ω → ℝ≥0, IsStoppingTime 𝓕 (fun ω => (T ω : WithTop ℝ≥0)) →
      (∀ ω, (T ω : WithTop ℝ≥0) ≤ Hn n ω) →
      ∀ a : ℚ, 0 < a → IsLocallyBrownianAfter κ' 𝓕 P W (a : ℝ).toNNReal T) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (∃ n, (t : WithTop ℝ≥0) < Hn n ω) → 0 < t → η ω t ∈ H →
      IsSingletonTipFiber (realPath W ω) t := by
  have hnull : ∀ n m, ∀ᵐ ω ∂P, ω ∉ Prod.snd '' tipFiberBadSet W (Hn n) m := fun n m =>
    measure_eq_zero_iff_ae_notMem.1
      (measure_snd_image_tipFiberBadSet hZ hOS h𝓕 hWa hWc hW0 hη (hH n) (hloc n) m)
  filter_upwards [ae_all_iff.2 fun n => ae_all_iff.2 (hnull n)] with ω hω t ⟨n, htn⟩ ht hpH
  by_contra hns
  obtain ⟨m, hm⟩ := exists_mem_tipFiberBadSet hWc hW0 hη htn ht hpH hns
  exact hω n m ⟨(t, ω), hm, rfl⟩

end Sec7

end InteractingSLE
