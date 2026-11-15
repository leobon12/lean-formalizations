/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TransienceTrace
import InteractingSLE.SLE8.TraceBridge
import InteractingSLE.Foundations.SLE.All
import QuantumZipper.Proofs.Zipper.B5LocDet
import QuantumZipper.Proofs.RS.TraceMain
import QuantumZipper.Proofs.RS.GenerationCor
import QuantumZipper.Proofs.RS.TraceShift

/-!
# The shrinking-prefix trace lemma (Part B.1), and the trace with marks at the seed for every `κ`

Packet PROVE-ZHAN-GT4-B. Source: Astra, *Follow-up proofs and dependency audit*, §B.1 "Shrinking-prefix trace
lemma" (`source/external/AstraIG1/ig1_followup_proofs.txt` L1028–L1086, ruling R38): "Let a continuous chordal
driver start from zero. Suppose that, for every positive rational `q`, its chain mapped out at time `q` has a
continuous trace on every compact subsequent time interval. Then the original chain has a continuous trace,
including time zero." and L1088–L1094: "For a noncolliding force word, fix rational `q > 0` and localize the future
on a finite elapsed time, bounded coordinates, and gaps bounded below. The additional driving drift is bounded.
Conditional Girsanov and ordinary SLE continuity give the hypothesis of the lemma … This proves finite-prefix
continuity even for nonsimple seed laws."

## The deterministic lemma, in uniform radial form

We work with the uniform radial Cauchy property `HasUnifRadial W T` of the centred inverse maps
`F_t = fwdMapInv W t` on `[0, T]` (the radial limits `F_t(iy)`, `y ↓ 0`, are uniformly Cauchy in `t ∈ [0, T]`);
this is how ordinary `SLE_κ` is known to have its trace for every `κ > 0` (QuantumZipper's TR4 bound for `κ < 8`,
the sealed SLE₈ anchor, GEO-RS8 for `κ > 8`), so it is the form in which the hypothesis of the lemma is available.

The source's collapse maps `C_r` are not needed in this form: the hydrodynamic displacement bound
`‖F_q(u) − u‖ ≤ 6 sup_{[0,q]} |W| + 6 √q` (QuantumZipper `B5.norm_fwdMapInv_sub_le`, Lawler Lemma 4.12) gives, through
the composition identity `F_t = F_q ∘ G_{t−q}` (`G` the inverse maps of the mapped-out chain `shiftDrive W q`,
QuantumZipper `RS.fwdMapInv_add_shift`),

  `‖F_t(iy) − F_t(iy')‖ ≤ ‖G_{t−q}(iy) − G_{t−q}(iy')‖ + 2 (6 sup_{[0,q]} |W| + 6 √q)`   (`t ≥ q`),

and `‖F_t(iy) − F_t(iy')‖ ≤ |y − y'| + 2 (6 sup_{[0,q]} |W| + 6 √q)` for `t ≤ q`. The error term is the source's
`r_n + r_m` (the shrinking initial hulls), and it tends to `0` as `q ↓ 0` by continuity of the driver at `0`.
The SLE₈ note's deterministic bridge (`SLE8.exists_continuous_trace_of_norm_sub_le`, [RS05, Theorem 4.1] in
QuantumZipper's uniform form) turns the uniform radial Cauchy property on every `[0, T]` into a continuous
generating trace (the filled-range identity of the source).

## Main results

* `HasUnifRadial W T`, `hasUnifRadial_of_shift` (**the shrinking-prefix lemma**), and
  `exists_isGeneratingTrace_of_hasUnifRadial` (the bridge to the frozen `IsGeneratingTrace`).
* `ae_hasUnifRadial_drive`: ordinary `SLE_κ`, every `κ > 0`.
* `IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible`: for every `κ > 0` and every ordered
  force word with admissible side partial sums (marks at `0⁻`, `0⁺` allowed): almost surely `ζ = ∞`, the marks are
  separated from the driver at positive times, and there is a continuous generating trace on `[0, ∞)` (the trace
  part of Aux. lemma 7, PDF p. 34, for nonsimple seed laws).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open QuantumZipper QuantumZipper.RS

/-! ### The uniform radial Cauchy property -/

/-- **Uniform radial Cauchy property on `[0, T]`**: the radial values `F_t(iy) = g_t⁻¹(W_t + iy)` of the centred
inverse Loewner maps are Cauchy as `y ↓ 0`, uniformly in `t ∈ [0, T]`. -/
def HasUnifRadial (W : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ e > (0 : ℝ), ∃ y₁ > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Ioc (0 : ℝ) y₁, ∀ y' ∈ Ioc (0 : ℝ) y₁,
    ‖fwdMapInv W t (y * I) - fwdMapInv W t (y' * I)‖ ≤ e

section Deterministic

variable {W W' : ℝ → ℝ}

theorem HasUnifRadial.mono {T T' : ℝ} (h : HasUnifRadial W T) (hT : T' ≤ T) : HasUnifRadial W T' := by
  intro e he
  obtain ⟨y₁, hy₁, hb⟩ := h e he
  exact ⟨y₁, hy₁, fun t ht => hb t ⟨ht.1, ht.2.trans hT⟩⟩

/-- The property only depends on the driver on `[0, T₂]`, `T < T₂`. -/
theorem HasUnifRadial.congr {T T₂ : ℝ} (h : HasUnifRadial W T) (hTT₂ : T < T₂)
    (hWW' : ∀ r ∈ Icc (0 : ℝ) T₂, W r = W' r) : HasUnifRadial W' T := by
  intro e he
  obtain ⟨y₁, hy₁, hb⟩ := h e he
  refine ⟨y₁, hy₁, fun t ht y hy y' hy' => ?_⟩
  rw [← fwdMapInv_eq_of_eqOn ht.1 (lt_of_le_of_lt ht.2 hTT₂) hWW']
  exact hb t ht y hy y' hy'

/-- Uniform radial convergence on `[0, T]` gives the uniform radial Cauchy property. -/
theorem hasUnifRadial_of_tendstoUniformlyOn {T : ℝ} {g : ℝ → ℂ}
    (h : TendstoUniformlyOn (fun (y : ℝ) (s : ℝ) => fwdMapInv W s (y * I)) g (𝓝[>] 0) (Icc 0 T)) :
    HasUnifRadial W T := by
  intro e he
  rw [Metric.tendstoUniformlyOn_iff] at h
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (h (e / 2) (half_pos he))
  have hu' : (0 : ℝ) < u := hu
  refine ⟨u / 2, half_pos hu', fun t ht y hy y' hy' => ?_⟩
  have h1 := hsub ⟨hy.1, lt_of_le_of_lt hy.2 (half_lt_self hu')⟩ t ht
  have h2 := hsub ⟨hy'.1, lt_of_le_of_lt hy'.2 (half_lt_self hu')⟩ t ht
  rw [dist_eq_norm] at h1 h2
  calc ‖fwdMapInv W t (y * I) - fwdMapInv W t (y' * I)‖
      = ‖(g t - fwdMapInv W t (y' * I)) - (g t - fwdMapInv W t (y * I))‖ := by
        congr 1; ring
    _ ≤ ‖g t - fwdMapInv W t (y' * I)‖ + ‖g t - fwdMapInv W t (y * I)‖ := norm_sub_le _ _
    _ ≤ e := by linarith

/-- A radial bound `‖F_t(iy) − trace W t‖ ≤ C y^δ` on every `[0, N] × (0, 1]` (the shape of QuantumZipper's TR4)
gives the uniform radial Cauchy property on every `[0, T]`. -/
theorem hasUnifRadial_of_rpow_bound {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ N : ℕ, ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) N, ∀ y ∈ Ioc (0 : ℝ) 1,
      ‖fwdMapInv W t (y * I) - trace W t‖ ≤ C * y ^ δ) (T : ℝ) : HasUnifRadial W T := by
  obtain ⟨C, hC⟩ := h ⌈T⌉₊
  have hU := tendstoUniformlyOn_fwdMapInv_mul_I_of_bound (W := W) (t := (⌈T⌉₊ : ℝ)) hδ hC
  exact (hasUnifRadial_of_tendstoUniformlyOn hU).mono (Nat.le_ceil T)

/-! ### The shrinking-prefix lemma -/

/-- The hydrodynamic displacement bound at every time `t ∈ [0, q]`, including `t = 0`. -/
theorem norm_fwdMapInv_sub_le_of_le (hW : Continuous W) (hW0 : W 0 = 0) {t M : ℝ} (ht : 0 ≤ t)
    (hM : ∀ r ∈ Icc (0 : ℝ) t, |W r| ≤ M) {u : ℂ} (hu : u ∈ H) :
    ‖fwdMapInv W t u - u‖ ≤ 6 * M + 6 * Real.sqrt t := by
  rcases ht.lt_or_eq with ht | rfl
  · exact B5.norm_fwdMapInv_sub_le hW hW0 ht hM hu
  · rw [InteractingSLE.fwdMapInv_zero_time hW hW0 hu, sub_self, norm_zero]
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, le_rfl⟩)
    positivity

/-- **The shrinking-prefix lemma** (Part B.1, L1028–L1086, uniform radial form). Let `W` be a continuous driver
with `W 0 = 0`. Suppose that there are arbitrarily small `q > 0` whose mapped-out chain `shiftDrive W q` has the
uniform radial Cauchy property on every compact time interval. Then the chain of `W` has it on every `[0, T]`. -/
theorem hasUnifRadial_of_shift (hW : Continuous W) (hW0 : W 0 = 0)
    (h : ∀ e > (0 : ℝ), ∃ q ∈ Ioo (0 : ℝ) e, ∀ U : ℝ, HasUnifRadial (shiftDrive W q) U) (T : ℝ) :
    HasUnifRadial W T := by
  intro e he
  set c : ℝ := e / 36 with hc
  have hc0 : 0 < c := by positivity
  -- smallness of the driver near `0`
  obtain ⟨δ, hδ, hWδ⟩ := Metric.continuousAt_iff.1 hW.continuousAt c hc0
  obtain ⟨q, ⟨hq0, hqe⟩, hqU⟩ := h (min δ (c ^ 2)) (lt_min hδ (by positivity))
  have hWq : ∀ r ∈ Icc (0 : ℝ) q, |W r| ≤ c := fun r hr => by
    have hr' : dist r 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hr.1]
      exact lt_of_le_of_lt hr.2 (lt_of_lt_of_le hqe (min_le_left _ _))
    have := hWδ hr'
    rw [Real.dist_eq, hW0, sub_zero] at this
    exact this.le
  have hsq : Real.sqrt q ≤ c := by
    rw [Real.sqrt_le_left hc0.le]
    exact (lt_of_lt_of_le hqe (min_le_right _ _)).le
  -- the displacement of `F_t`, `t ≤ q`, is at most `e/3`
  have hdisp : ∀ t ∈ Icc (0 : ℝ) q, ∀ u ∈ H, ‖fwdMapInv W t u - u‖ ≤ e / 3 := by
    intro t ht u hu
    have h1 := norm_fwdMapInv_sub_le_of_le hW hW0 ht.1 (fun r hr => hWq r ⟨hr.1, hr.2.trans ht.2⟩) hu
    have h2 : Real.sqrt t ≤ Real.sqrt q := Real.sqrt_le_sqrt ht.2
    linarith
  obtain ⟨y₁, hy₁, hG⟩ := hqU T (e / 3) (by positivity)
  refine ⟨min y₁ (e / 3), lt_min hy₁ (by positivity), fun t ht y hy y' hy' => ?_⟩
  have hyH : (y : ℂ) * I ∈ H := SLE8.ofReal_mul_I_mem_H hy.1
  have hy'H : (y' : ℂ) * I ∈ H := SLE8.ofReal_mul_I_mem_H hy'.1
  -- the triangle inequality around the displacement
  have htri : ∀ s ∈ Icc (0 : ℝ) q, ∀ u ∈ H, ∀ u' ∈ H,
      ‖fwdMapInv W s u - fwdMapInv W s u'‖ ≤ ‖u - u'‖ + 2 * (e / 3) := by
    intro s hs u hu u' hu'
    have h1 := hdisp s hs u hu
    have h2 := hdisp s hs u' hu'
    calc ‖fwdMapInv W s u - fwdMapInv W s u'‖
        = ‖(fwdMapInv W s u - u) + (u - u') - (fwdMapInv W s u' - u')‖ := by congr 1; ring
      _ ≤ ‖(fwdMapInv W s u - u) + (u - u')‖ + ‖fwdMapInv W s u' - u'‖ := norm_sub_le _ _
      _ ≤ ‖fwdMapInv W s u - u‖ + ‖u - u'‖ + ‖fwdMapInv W s u' - u'‖ := by
        gcongr; exact norm_add_le _ _
      _ ≤ ‖u - u'‖ + 2 * (e / 3) := by linarith
  rcases le_or_gt t q with htq | htq
  · -- `t ≤ q`: both radial points move by at most `e/3`
    have h1 := htri t ⟨ht.1, htq⟩ _ hyH _ hy'H
    have h2 : ‖(y : ℂ) * I - (y' : ℂ) * I‖ ≤ e / 3 := by
      rw [← sub_mul, norm_mul, Complex.norm_I, mul_one, ← ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hy.1, hy'.1, hy.2.trans (min_le_right _ _),
        hy'.2.trans (min_le_right _ _)]
    linarith
  · -- `t > q`: compose with the mapped-out chain
    have hWs := continuous_shiftDrive hW q
    have hcomp : ∀ w ∈ H, fwdMapInv W t w = fwdMapInv W q (fwdMapInv (shiftDrive W q) (t - q) w) := by
      intro w hw
      have := fwdMapInv_add_shift hW hW0 hq0.le (sub_nonneg.2 htq.le) hw
      rwa [add_sub_cancel] at this
    rw [hcomp _ hyH, hcomp _ hy'H]
    have hGH : ∀ w ∈ H, fwdMapInv (shiftDrive W q) (t - q) w ∈ H := fun w hw =>
      fwdMapInv_mem_H hWs (shiftDrive_zero W q) (sub_nonneg.2 htq.le) hw
    have h1 := htri q ⟨hq0.le, le_rfl⟩ _ (hGH _ hyH) _ (hGH _ hy'H)
    have h2 := hG (t - q) ⟨sub_nonneg.2 htq.le, by linarith [ht.2]⟩ y
      ⟨hy.1, hy.2.trans (min_le_left _ _)⟩ y' ⟨hy'.1, hy'.2.trans (min_le_left _ _)⟩
    linarith

/-- **A rate function** from the uniform radial Cauchy property: the form of the SLE₈ note's deterministic bridge
(`SLE8.exists_continuous_trace_of_norm_sub_le`). -/
theorem HasUnifRadial.exists_rate {T : ℝ} (h : HasUnifRadial W T) :
    ∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧ ∃ y₀ > (0 : ℝ), ∀ t ∈ Icc 0 T, ∀ y ∈ Ioc 0 y₀,
      ∀ y' ∈ Ioc 0 y, ‖fwdMapInv W t (y * I) - fwdMapInv W t (y' * I)‖ ≤ ε y := by
  set S : ℝ → Set ℝ := fun y => {r | ∃ t ∈ Icc (0 : ℝ) T, ∃ a ∈ Ioc (0 : ℝ) y, ∃ b ∈ Ioc (0 : ℝ) y,
      r = ‖fwdMapInv W t (a * I) - fwdMapInv W t (b * I)‖} with hS
  obtain ⟨y₀, hy₀, hb₀⟩ := h 1 one_pos
  refine ⟨fun y => sSup (S y), ?_, y₀, hy₀, fun t ht y hy y' hy' => ?_⟩
  · rw [Metric.tendsto_nhds]
    intro e he
    obtain ⟨y₁, hy₁, hb₁⟩ := h (e / 2) (half_pos he)
    filter_upwards [Ioc_mem_nhdsGT_zero hy₁] with y hy
    have hup : sSup (S y) ≤ e / 2 := by
      refine Real.sSup_le ?_ (by positivity)
      rintro r ⟨s, hs, a, ha, b, hb, rfl⟩
      exact hb₁ s hs a ⟨ha.1, ha.2.trans hy.2⟩ b ⟨hb.1, hb.2.trans hy.2⟩
    have hlow : 0 ≤ sSup (S y) := by
      refine Real.sSup_nonneg ?_
      rintro r ⟨_, _, _, _, _, _, rfl⟩
      exact norm_nonneg _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hlow]
    linarith
  · refine le_csSup ⟨1, ?_⟩ ⟨t, ht, y, ⟨hy.1, le_rfl⟩, y', hy', rfl⟩
    rintro r ⟨s, hs, a, ha, b, hb, rfl⟩
    exact hb₀ s hs a ⟨ha.1, ha.2.trans hy.2⟩ b ⟨hb.1, hb.2.trans hy.2⟩

/-- **The bridge to the frozen generating trace** (the filled-range identity of B.1). If the chain of a continuous
driver `w` with `w 0 = 0` has the uniform radial Cauchy property on every `[0, T]`, then `w` has a continuous
generating trace on `[0, ∞)`: the radial limit `η(t) = lim_{y ↓ 0} F_t(iy)` ([RS05, Theorem 4.1] in QuantumZipper's
uniform form, through the SLE₈ note's bridge). -/
theorem exists_isGeneratingTrace_of_hasUnifRadial {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    (h : ∀ T : ℝ, HasUnifRadial (fun s : ℝ => w s.toNNReal) T) :
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ⊤ η := by
  have hW : Continuous (fun s : ℝ => w s.toNNReal) := hw.comp continuous_real_toNNReal
  have hW0 : (fun s : ℝ => w s.toNNReal) 0 = 0 := by simp [hw0]
  obtain ⟨γ, -, hγc, -, hγ0, hfill⟩ :=
    SLE8.exists_continuous_trace_of_norm_sub_le hW hW0 fun T _ => (h T).exists_rate
  exact ⟨γ, hγ0, hγc.continuousOn, fun t _ => hfill t⟩

/-- **The shrinking-prefix trace lemma** (Part B.1, L1028–L1031), in the form used below: if there are arbitrarily
small `q > 0` whose mapped-out chain has the uniform radial Cauchy property on every compact time interval, then the
original chain has a continuous generating trace on `[0, ∞)`, including time zero. -/
theorem exists_isGeneratingTrace_of_shift {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    (h : ∀ e > (0 : ℝ), ∃ q ∈ Ioo (0 : ℝ) e,
      ∀ U : ℝ, HasUnifRadial (shiftDrive (fun s : ℝ => w s.toNNReal) q) U) :
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ⊤ η := by
  have hW : Continuous (fun s : ℝ => w s.toNNReal) := hw.comp continuous_real_toNNReal
  have hW0 : (fun s : ℝ => w s.toNNReal) 0 = 0 := by simp [hw0]
  exact exists_isGeneratingTrace_of_hasUnifRadial hw hw0 (hasUnifRadial_of_shift hW hW0 h)

end Deterministic

/-! ### Ordinary `SLE_κ`, every `κ > 0` -/

/-- **Ordinary `SLE_κ` has the uniform radial Cauchy property** on every `[0, T]`, for every `κ > 0`, almost surely:
QuantumZipper's TR4 radial bound (`κ < 8`), the sealed SLE₈ anchor (`κ = 8`, locally uniform radial convergence),
GEO-RS8's radial bound (`κ > 8`). -/
theorem ae_hasUnifRadial_drive {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ, HasUnifRadial (drive κ B ω) T := by
  have : IsProbabilityMeasure P := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  rcases lt_trichotomy κ 8 with h8 | rfl | h8
  · obtain ⟨δ, hδ, hg⟩ := ae_sleTrace_good hB hκ h8
    filter_upwards [hg] with ω ⟨_, _, hb⟩
    exact hasUnifRadial_of_rpow_bound hδ hb
  · filter_upwards [SLE8.ae_exists_continuous_trace hB] with ω ⟨γ, hU, _⟩ T
    have hK := (tendstoLocallyUniformly_iff_forall_isCompact.1 hU) (Icc 0 T.toNNReal) isCompact_Icc
    refine hasUnifRadial_of_tendstoUniformlyOn (g := fun s => γ s.toNNReal) ?_
    rw [Metric.tendstoUniformlyOn_iff] at hK ⊢
    intro e he
    filter_upwards [hK e he] with y hy s hs
    have hs' : s.toNNReal ∈ Icc (0 : ℝ≥0) T.toNNReal :=
      ⟨zero_le, Real.toNNReal_le_toNNReal hs.2⟩
    have := hy _ hs'
    rwa [Real.coe_toNNReal _ hs.1] at this
  · obtain ⟨δ, hδ, hg⟩ := InteractingSLE.ae_sleTrace_good_of_eight_lt hB h8
    filter_upwards [hg] with ω ⟨_, _, hb⟩
    exact hasUnifRadial_of_rpow_bound hδ hb

/-! ### Force words: the trace with marks at the seed, every `κ > 0` -/

section Evolution

variable {κ : ℝ} {nL nR : ℕ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **The localized comparison after a time `a`** (any `κ > 0`): almost surely, if `ζ = ∞` and all force gaps are
`≥ δ` on `[a, a + m + 1]`, the mapped-out future `shiftDrive W a` has the uniform radial Cauchy property on
`[0, m]` (bounded-drift Girsanov, `Dimension.exists_brownian_localization`, and `ae_hasUnifRadial_drive`). -/
theorem IsIntegratedSLEEvolution.ae_shift_hasUnifRadial [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (a : ℝ≥0) (m : ℕ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ → (∀ s : ℝ≥0, a ≤ s → s ≤ a + ((m : ℝ≥0) + 1) →
        Dimension.GapsGE δ (W s ω) (fun i => VL i s ω) (fun i => VR i s ω)) →
      HasUnifRadial (shiftDrive (fun r : ℝ => W r.toNNReal ω) a) m := by
  obtain ⟨X, hXm, μ, hμP, hμB, hac, hloc⟩ :=
    Dimension.exists_brownian_localization hκ hE a ((m : ℝ≥0) + 1) hδ
  have hgood := ae_of_ae_map hXm.aemeasurable (hac.ae_le (ae_hasUnifRadial_drive hμB hκ))
  filter_upwards [hgood, hloc] with ω hV hlocω hζ hgap
  refine (hV m).congr (T₂ := (m : ℝ) + 1) (by linarith) fun r hr => ?_
  have ht : r.toNNReal ≤ (m : ℝ≥0) + 1 :=
    Real.toNNReal_le_iff_le_coe.2 (by push_cast; exact hr.2)
  have h1 := hlocω r.toNNReal ht (by rw [hζ]; exact ENNReal.coe_lt_top)
    fun s hs1 hs2 => hgap s hs1 (hs2.trans (add_le_add_right ht a))
  show Real.sqrt κ * canonBM r.toNNReal (X ω) = W ((a : ℝ) + r).toNNReal ω - W (a : ℝ).toNNReal ω
  rw [Real.toNNReal_coe, Real.toNNReal_add a.coe_nonneg hr.1, Real.toNNReal_coe, h1]
  rfl

/-- **The trace with marks at the seed, for every `κ > 0`** (Part B.1, L1088–L1094: "finite-prefix continuity even
for nonsimple seed laws"; the trace part of Aux. lemma 7). For an integrated `SLE_κ(ρ)` evolution of an ordered force
word with admissible side partial sums (marks at `0⁻`, `0⁺` allowed), almost surely: the lifetime is infinite, every
force point is strictly separated from the driver at every positive time (Aux. lemma 6), and the driver has a
continuous generating trace on `[0, ∞)`. -/
theorem IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible (hκ : 0 < κ)
    (hF : IsOrderedForceWord xL xR) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t : ℝ≥0, 0 < t → (∀ i, VL i t ω < W t ω) ∧ ∀ i, W t ω < VR i t ω) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have h6 := Sec4.aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hE
  have hloc : ∀ᵐ ω ∂P, ∀ q : ℚ, ∀ m n : ℕ, ζ ω = ⊤ → (∀ s : ℝ≥0, (q : ℝ).toNNReal ≤ s →
      s ≤ (q : ℝ).toNNReal + ((m : ℝ≥0) + 1) →
        Dimension.GapsGE (1 / ((n : ℝ) + 1)) (W s ω) (fun i => VL i s ω) (fun i => VR i s ω)) →
      HasUnifRadial (shiftDrive (fun r : ℝ => W r.toNNReal ω) ((q : ℝ).toNNReal : ℝ)) m := by
    rw [ae_all_iff]; intro q
    rw [ae_all_iff]; intro m
    rw [ae_all_iff]; intro n
    exact IsIntegratedSLEEvolution.ae_shift_hasUnifRadial hκ hE _ m (by positivity)
  filter_upwards [h6, hloc, hE.2.2.2.2] with ω ⟨hζ, hsep⟩ hlω hp
  refine ⟨hζ, hsep, ?_⟩
  have hwc : Continuous (fun t => W t ω) :=
    continuousOn_univ.1 (hp.2.2.2.1.mono fun t _ => by
      show (t : ℝ≥0∞) < ζ ω
      rw [hζ]; exact ENNReal.coe_lt_top)
  refine exists_isGeneratingTrace_of_shift hwc hp.1 fun e he => ?_
  obtain ⟨q, hq0, hqe⟩ := exists_rat_btwn he
  refine ⟨q, ⟨hq0, hqe⟩, fun U => ?_⟩
  obtain ⟨m, hm⟩ := exists_nat_ge U
  have ha : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0.le
  have ha0 : 0 < (q : ℝ).toNNReal := Real.toNNReal_pos.2 hq0
  obtain ⟨δ, hδ, hgapδ⟩ :=
    Zhan.exists_gapsGE_Icc_of_sep hp hζ hsep ha0 (le_self_add (b := (m : ℝ≥0) + 1))
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  have h := hlω q m n hζ fun s h1 h2 =>
    ⟨fun i => hn.le.trans ((hgapδ s h1 h2).1 i), fun i => hn.le.trans ((hgapδ s h1 h2).2 i)⟩
  rw [ha] at h
  exact h.mono hm

end Evolution

end InteractingSLE.ZhanGT4
