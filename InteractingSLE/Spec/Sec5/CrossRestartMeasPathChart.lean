/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartMeasPath
import InteractingSLE.WangWu.CouplingVersion
import InteractingSLE.Foundations.Loewner.FiniteEndpoint

/-!
# A measurable surrogate of the restart chart path

Packet PROVE-SEC5-I. The restart chart path `restartPath q U σ x₁ γ′` evaluates the Loewner map `g_σ` of the segment
driver at the random points `m₁(γ′ t)` and uses the boundary value `x₁ = Re g_σ(−1 − q)`, a `limUnder` along `𝓝[ℍ]`.
Neither is measurable in general (the Loewner map is a junk value off the alive set and the `limUnder` is a choice).
This file builds a **surrogate** from countable, jointly measurable data and proves that it is the chart path at every
time that the measurable-form restart objects read (time `0` and the times before `lawExit`):

* `fwdMap_eq_zero_of_mem_fwdHull`: the forward map is the junk value `0` on the hull;
* **`tendsto_gmap_bdryVal_of_notMem`**: if the hull at time `σ` is the filling of a compact set `F` and `y ∉ F`, then
  `g_σ` tends to its boundary value at `y` along `𝓝[ℍ] y` (either a ball around `y` misses the hull, or its upper half
  lies in the hull, where `g_σ` is the constant `U_σ`); hence along the vertical sequence `bdrySeq y`;
* `aliveFwd` (Wang–Wu's jointly measurable alive forward map of a path in `C([0, σ])`) and `aliveFwd_eq`: it is the
  forward map at every point of `ℍ`;
* `surrStart`, `surrPath`: the surrogate boundary value and chart path; **`surrPath_eq_restartPath`**: equality at
  time `0` and before `lawExit`, whenever the trace data are good once `lawExit > 0`;
* `measurable_surrPath`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H fwdHull fwdMap extIccPath)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE

namespace Sec5

namespace CrossRestart

open ConformalImage ConformalImageFull Restart

/-! ### The Loewner map on the hull and at the boundary -/

section Loewner

variable {V : ℝ → ℝ} {σ : ℝ}

/-- **The forward map is the junk value `0` on the hull** (a swallowed point has no forward solution on `[0, σ]`). -/
theorem fwdMap_eq_zero_of_mem_fwdHull (hV : Continuous V) (hσ : 0 ≤ σ) {z : ℂ} (hz : z ∈ fwdHull V σ) :
    fwdMap V σ z = 0 :=
  Ito.fwdMap_eq_zero_of_not fun ⟨_, hu⟩ => Ito.notMem_fwdHull_of_isForwardSol hV hz.1 hσ hu hz

/-- **The boundary value at a point off the filled set.** If the hull at time `σ` is the filling of a compact set `F`
and `y ∉ F`, then `g_σ` tends to `bdryVal V y σ` along `𝓝[ℍ] y`. -/
theorem tendsto_gmap_bdryVal_of_notMem (hV : Continuous V) (hV0 : V 0 = 0) (hσ : 0 ≤ σ) {F : Set ℂ}
    (hF : IsCompact F) (hK : fwdHull V σ = fillH F) {y : ℝ} (hy : (y : ℂ) ∉ F) :
    Tendsto (gmap V σ) (𝓝[H] (y : ℂ)) (𝓝 (bdryVal V y σ)) := by
  obtain ⟨δ, hδ, hδF⟩ := Metric.mem_nhds_iff.1 (hF.isClosed.isOpen_compl.mem_nhds hy)
  set B : Set ℂ := H ∩ ball (y : ℂ) δ with hBdef
  have hBp : IsPreconnected B :=
    ((convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).inter (convex_ball _ _)).isPreconnected
  have hBne : B.Nonempty := by
    refine ⟨(y : ℂ) + ((δ / 2 : ℝ) : ℂ) * I, ?_, ?_⟩
    · show (0 : ℝ) < ((y : ℂ) + ((δ / 2 : ℝ) : ℂ) * I).im
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero, zero_add, mul_one]
      linarith
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
  have hBA : B ⊆ H \ closure F := by
    rw [hF.isClosed.closure_eq]
    exact fun z hz => ⟨hz.1, hδF hz.2⟩
  have hBmem : B ∈ 𝓝[H] (y : ℂ) := inter_mem_nhdsWithin H (ball_mem_nhds _ hδ)
  rcases subset_fillH_or_disjoint_restart hBp hBne hBA with hsub | hdisj
  · -- the upper half-ball lies in the hull, where `g_σ` is constant
    have hc : Tendsto (gmap V σ) (𝓝[H] (y : ℂ)) (𝓝 (V σ : ℂ)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hBmem] with z hz
      have hzK : z ∈ fwdHull V σ := by rw [hK]; exact hsub hz
      rw [gmap, fwdMap_eq_zero_of_mem_fwdHull hV hσ hzK, zero_add]
    have : (𝓝[H] (y : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
    rw [bdryVal, hc.limUnder_eq]
    exact hc
  · have hball : Disjoint (ball (y : ℂ) δ) (fwdHull V σ) := by
      rw [Set.disjoint_left]
      intro z hz hzK
      have hzK' : z ∈ fillH F := by rw [← hK]; exact hzK
      exact Set.disjoint_left.1 hdisj ⟨hzK.1, hz⟩ hzK'
    exact (bdryVal_spec hV hV0 hσ hδ hball).2

/-- The vertical sequence `y + i/(n + 1)` approaching the real point `y` from `ℍ`. -/
def bdrySeq (y : ℝ) (n : ℕ) : ℂ := (y : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I

theorem bdrySeq_mem_H (y : ℝ) (n : ℕ) : bdrySeq y n ∈ H := by
  show (0 : ℝ) < (bdrySeq y n).im
  simp only [bdrySeq, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero, zero_add, mul_one]
  positivity

theorem tendsto_bdrySeq (y : ℝ) : Tendsto (bdrySeq y) atTop (𝓝[H] (y : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall (bdrySeq_mem_H y)⟩
  have h := ((Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat).mul_const I
  have h' := h.const_add (y : ℂ)
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at h'
  exact h'

end Loewner

/-! ### The alive forward map of a path -/

section Alive

variable {σ : ℝ≥0}

/-- The endpoint `σ` of `[0, σ]`. -/
def topPt (σ : ℝ≥0) : Icc (0 : ℝ) σ := ⟨σ, right_mem_Icc.2 σ.coe_nonneg⟩

/-- The forward map of the path `g` at time `σ` on its alive set, `0` elsewhere (Wang–Wu's jointly measurable
`measurable_fwdMap_alivePath`). -/
def aliveFwd (σ : ℝ≥0) (g : C(Icc (0 : ℝ) σ, ℝ)) (z : ℂ) : ℂ :=
  (WangWu.alivePath σ.coe_nonneg).indicator (fun p => fwdMap (extIccPath σ.coe_nonneg p.2) σ p.1) (z, g)

/-- **The alive forward map is the forward map at every point of `ℍ`**, for any continuous driver that reads the path
on `[0, σ]`. -/
theorem aliveFwd_eq {g : C(Icc (0 : ℝ) σ, ℝ)} {V : ℝ → ℝ} (hV : Continuous V)
    (hVg : ∀ r ∈ Icc (0 : ℝ) σ, V r = extIccPath σ.coe_nonneg g r) {z : ℂ} (hz : z ∈ H) :
    aliveFwd σ g z = fwdMap V σ z := by
  have hc := QuantumZipper.continuous_extIccPath σ.coe_nonneg g
  have hK : fwdHull (extIccPath σ.coe_nonneg g) σ = fwdHull V σ :=
    QuantumZipper.Thm14FromThm13.fwdHull_eq_of_eqOn hc hV σ.coe_nonneg fun r hr => (hVg r hr).symm
  have hf : fwdMap (extIccPath σ.coe_nonneg g) σ z = fwdMap V σ z :=
    QuantumZipper.fwdMap_congr_drive hc hV hz σ.coe_nonneg fun r hr => (hVg r hr).symm
  by_cases hzK : z ∈ fwdHull V σ
  · rw [aliveFwd, indicator_of_notMem, fwdMap_eq_zero_of_mem_fwdHull hV σ.coe_nonneg hzK]
    rintro ⟨-, h⟩
    exact h (hK ▸ hzK)
  · rw [aliveFwd, indicator_of_mem (show (z, g) ∈ WangWu.alivePath σ.coe_nonneg from ⟨hz, hK ▸ hzK⟩)]
    exact hf

/-- **The surrogate boundary value**: the real part of the limit of `g_σ` along `bdrySeq (−1 − q)`, with the forward
map read from the path `g`. -/
def surrStart (q : ℝ) (σ : ℝ≥0) (g : C(Icc (0 : ℝ) σ, ℝ)) : ℝ :=
  (limOr0 fun n => aliveFwd σ g (bdrySeq (-1 - q) n) + (g (topPt σ) : ℂ)).re

/-- **The surrogate chart path**: `restartPath` with the forward map read from the path `g` on its alive set and the
surrogate boundary value. -/
def surrPath (q : ℝ) (σ : ℝ≥0) (g : C(Icc (0 : ℝ) σ, ℝ)) (γ : ℝ≥0 → ℂ) (t : ℝ≥0) : ℂ :=
  open scoped Classical in
  if t = 0 then 0 else
    realMobius (-1) 0 1 (-(g (topPt σ) - surrStart q σ g))
      (aliveFwd σ g (realMobius 0 (-(1 + q)) 1 1 (γ t)) + (g (topPt σ) : ℂ) - (surrStart q σ g : ℂ))

theorem surrPath_zero (q : ℝ) (σ : ℝ≥0) (g : C(Icc (0 : ℝ) σ, ℝ)) (γ : ℝ≥0 → ℂ) : surrPath q σ g γ 0 = 0 := by
  simp [surrPath]

/-- **The surrogate is the restart chart path at time `0` and before the exit.** Hypothesis: whenever `lawExit > 0`,
`σ` is before the flow-line lifetime, the flow-line driver `w` is continuous before it with `w 0 = 0`, the flow-line
trace `η₀` is continuous on `[0, σ]` and generates the hull at `σ`, the counterflow trace `γ₀` is continuous on its
closed available interval, and the path `g` is `w` on `[0, σ]`. -/
theorem surrPath_eq_restartPath {q : ℝ} (hq : 0 < q) {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η₀ : ℝ≥0 → ℂ} {ζ' : ℝ≥0∞}
    {γ₀ : ℝ≥0 → ℂ} {g : C(Icc (0 : ℝ) σ, ℝ)}
    (hgood : 0 < lawExit q η₀ σ ζ' γ₀ → (σ : ℝ≥0∞) < ζ ∧ ContinuousOn w {t | (t : ℝ≥0∞) < ζ} ∧ w 0 = 0 ∧
      ContinuousOn η₀ (Icc 0 σ) ∧ IsFilling (fwdHull (fun s : ℝ => w s.toNNReal) σ) (η₀ '' Icc 0 σ) ∧
      ContinuousOn γ₀ {t | (t : ℝ≥0∞) ≤ ζ'} ∧ ∀ r ∈ Icc (0 : ℝ) σ, extIccPath σ.coe_nonneg g r = w r.toNNReal)
    (t : ℝ≥0) (ht : t = 0 ∨ (t : ℝ≥0∞) < lawExit q η₀ σ ζ' γ₀) :
    surrPath q σ g γ₀ t = restartPath q (segDrive w ζ σ) σ (segStart q w ζ σ) γ₀ t := by
  rcases eq_or_ne t 0 with rfl | ht0
  · rw [surrPath_zero, restartPath_zero]
  have hE : (t : ℝ≥0∞) < lawExit q η₀ σ ζ' γ₀ := ht.resolve_left ht0
  have hpos : 0 < lawExit q η₀ σ ζ' γ₀ := lt_of_le_of_lt bot_le hE
  obtain ⟨hσζ, hwc, hw0, hηc, hfill, hγc, hg⟩ := hgood hpos
  set U := segDrive w ζ σ with hUdef
  have hσ₂ := lt_midTime hσζ
  have hUc : Continuous U := continuous_frozenDrive_of_lt hwc (ofReal_midTime_lt hσζ)
  have hU0 : U 0 = 0 := by
    rw [hUdef, segDrive, frozenDrive_zero ((NNReal.coe_nonneg σ).trans hσ₂.le), hw0]
  have hK₁ : fwdHull U σ = fillH (η₀ '' Icc 0 σ) := by
    rw [hUdef, segDrive, fwdHull_eq_of_eqOn (NNReal.coe_nonneg σ) hσ₂ fun r hr => frozenDrive_eq hr]
    exact fwdHull_eq_fillH_of_isFilling (isCompact_Icc.image_of_continuousOn hηc) hfill
  have hUg : ∀ r ∈ Icc (0 : ℝ) σ, U r = extIccPath σ.coe_nonneg g r := fun r hr => by
    rw [hUdef, segDrive, frozenDrive_eq ⟨hr.1, hr.2.trans hσ₂.le⟩, hg r hr]
  have hgσ : g (topPt σ) = U σ := by
    rw [hUg σ (right_mem_Icc.2 σ.coe_nonneg), QuantumZipper.extIccPath_of_mem σ.coe_nonneg g
      (right_mem_Icc.2 σ.coe_nonneg)]
    rfl
  have hgm : ∀ z ∈ H, aliveFwd σ g z + (g (topPt σ) : ℂ) = gmap U σ z := fun z hz => by
    rw [aliveFwd_eq hUc hUg hz, hgσ, gmap]
  -- the start of the counterflow is off the flow-line segment
  have htg0 := isTraceGood_of_lt_lawExit hγc hηc (t := 0) (by simpa using hpos)
  have hy : ((-1 - q : ℝ) : ℂ) ∉ η₀ '' Icc 0 σ := fun hmem => by
    refine Set.disjoint_left.1 htg0.2.2 hmem ⟨γ₀ 0, ⟨0, ⟨le_rfl, le_rfl⟩, rfl⟩, ?_⟩
    rw [htg0.2.1.zero, mob_zero (q := q)]
  have hlim := (tendsto_gmap_bdryVal_of_notMem hUc hU0 σ.coe_nonneg
    (isCompact_Icc.image_of_continuousOn hηc) hK₁ hy).comp (tendsto_bdrySeq (-1 - q))
  have hstart : surrStart q σ g = segStart q w ζ σ := by
    rw [surrStart, segStart, ← hUdef]
    congr 1
    refine limOr0_eq (hlim.congr fun n => ?_)
    simp only [Function.comp_apply]
    rw [hgm _ (bdrySeq_mem_H _ n)]
  -- the counterflow point is in `ℍ`, so is its `E`-image
  have htg := isTraceGood_of_lt_lawExit hγc hηc hE
  have hγH : γ₀ t ∈ H := htg.2.1.mem t (pos_iff_ne_zero.2 ht0) le_rfl
  have hmH : realMobius 0 (-(1 + q)) 1 1 (γ₀ t) ∈ H :=
    QuantumZipper.CA.realMobius_mem_H (by linarith) hγH
  simp only [surrPath, ht0, ↓reduceIte]
  rw [restartPath_of_ne_zero ht0, restartMap, hstart, hgm _ hmH, hgσ]

/-! ### Measurability -/

section Meas

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace C(Icc (0 : ℝ) σ, ℝ)] [BorelSpace C(Icc (0 : ℝ) σ, ℝ)]
  {g : Ω → C(Icc (0 : ℝ) σ, ℝ)}

theorem measurable_aliveFwd (hg : Measurable g) {Z : Ω → ℂ} (hZ : Measurable Z) :
    Measurable fun ω => aliveFwd σ (g ω) (Z ω) :=
  (WangWu.measurable_fwdMap_alivePath σ.coe_nonneg).comp (hZ.prodMk hg)

theorem measurable_topPt (hg : Measurable g) : Measurable fun ω => g ω (topPt σ) :=
  (continuous_eval_const (topPt σ)).measurable.comp hg

theorem measurable_surrStart (q : ℝ) (hg : Measurable g) : Measurable fun ω => surrStart q σ (g ω) :=
  Complex.measurable_re.comp (measurable_limOr0 fun _ =>
    (measurable_aliveFwd hg measurable_const).add (Complex.measurable_ofReal.comp (measurable_topPt hg)))

theorem measurable_realMobius_param {a : Ω → ℝ} {Z : Ω → ℂ} (ha : Measurable a) (hZ : Measurable Z) :
    Measurable fun ω => realMobius (-1) 0 1 (a ω) (Z ω) := by
  unfold realMobius
  exact ((measurable_const.mul hZ).add measurable_const).div
    ((measurable_const.mul hZ).add (Complex.measurable_ofReal.comp ha))

theorem measurable_surrPath (q : ℝ) (hg : Measurable g) {γ : Ω → ℝ≥0 → ℂ} (hγ : ∀ t, Measurable fun ω => γ ω t)
    (t : ℝ≥0) : Measurable fun ω => surrPath q σ (g ω) (γ ω) t := by
  by_cases ht : t = 0
  · simp only [ht, surrPath_zero]
    exact measurable_const
  · simp only [surrPath, ht, ↓reduceIte]
    have hs := measurable_surrStart q hg
    have hσm := measurable_topPt hg
    refine measurable_realMobius_param (hσm.sub hs).neg ?_
    exact ((measurable_aliveFwd hg ((measurable_mob q).comp (hγ t))).add
      (Complex.measurable_ofReal.comp hσm)).sub (Complex.measurable_ofReal.comp hs)

end Meas

end Alive

end CrossRestart

end Sec5

end InteractingSLE
