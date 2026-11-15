/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideHeight

/-!
# A flow line's side heights at every approached point of its trace, real points included

Packet PROVE-SIDEHEIGHT2 (specification Lemma 7.8, p. 294: "An original real contact in the interior of one arc
creates no further exceptional datum: the countable ordinary-stop comparison above identifies its germ with that of the
whole corresponding single-path prefix"). PROVE-SIDEHEIGHT's `SinglePathSideHeightStatement` gives the side heights of
a flow line's range mean at interior trace points. Here the same conclusion is proved at **every** point `p` approached
from the unbounded domain of the stopped range along which the chart `f_q(· − x)` has a real limit `y`, provided the
point is not on the wrong side of the real line: for `y > 0` it suffices that `p − x` is not a real point `≥ 0`, for
`y < 0` that it is not a real point `≤ 0` (`singlePathSideHeight_gen`).

The only new ingredient is the slit bound for such points (`lt_rightImg_sub_of_extendFrom`,
`neg_rightImg_sub_lt_of_extendFrom`): real points `≥ R_t − W_t` are limits of images of alive right points, which the
boundary extension `F̄_t` returns to positive reals, so `F̄_t(x)` is then a real number `≥ 0`. The proof of
`singlePathSideHeight_gen` is PROVE-SIDEHEIGHT's proof of `singlePathSideHeightStatement_of_inputs` with this bound in
place of the interior-point bound.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace SideHeightBox

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open LQGMetric (DistOn TestOn)
open LocalSets Sec6 MartChar.RealFlow SideHeight

/-! ### The slit bound at boundary points -/

section Slit

variable {W : ℝ → ℝ} {t : ℝ}

/-- **Right real points mapped off the closed right half-line lie left of the image of `0⁺`**: if `F̄_t(x)` is not a
real number `≥ 0`, then `x < R_t − W_t`. -/
theorem lt_rightImg_sub_of_extendFrom (hB : HasBdryLimits (fwdMapInv W t)) (hW : Continuous W) (hW0 : W 0 = 0)
    (ht : 0 ≤ t) {x : ℝ}
    (hFx : ¬ ((extendFrom H (fwdMapInv W t) x).im = 0 ∧ 0 ≤ (extendFrom H (fwdMapInv W t) x).re)) :
    x < rightImg W 0 t - W t := by
  by_contra hle
  push Not at hle
  have hM : rightImg W 0 t ≤ x + W t := by linarith
  have hseq : ∀ n : ℕ, ∃ y, 0 < y ∧ Alive W y t ∧ x + W t < gImg W y t ∧
      gImg W y t < x + W t + 1 / ((n : ℝ) + 1) :=
    fun n => exists_alive_gImg_mem hW ht (by positivity) hM
  choose y hy0 hya hyM hyM' using hseq
  set xn : ℕ → ℝ := fun n => gImg W (y n) t - W t with hxn
  have hval : ∀ n, extendFrom H (fwdMapInv W t) (xn n) = (y n : ℂ) := fun n => by
    have h := extendFrom_eq_of_isForwardSol' hB hW hW0 ht
      (show (0 : ℝ) ≤ ((y n : ℂ)).im by simp) (WangWu.isForwardSol_of_alive hW (hya n))
    have e : (cflow W (y n) t : ℂ) = ((xn n : ℝ) : ℂ) := by
      rw [hxn]
      simp only [gImg]
      push_cast
      ring
    rwa [e] at h
  have hlim : Tendsto xn atTop (𝓝 x) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => x)
      (h := fun n : ℕ => x + 1 / ((n : ℝ) + 1)) tendsto_const_nhds ?_ (fun n => ?_) (fun n => ?_)
    · simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · have := hyM n
      simp only [hxn]
      linarith
    · have := hyM' n
      simp only [hxn]
      linarith
  have hxH : ((x : ℂ)) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hF : Tendsto (extendFrom H (fwdMapInv W t)) (𝓝[Hbar] (x : ℂ))
      (𝓝 (extendFrom H (fwdMapInv W t) x)) := hB.continuousOn _ hxH
  have hc : Tendsto (fun n => ((xn n : ℝ) : ℂ)) atTop (𝓝[Hbar] (x : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨(Complex.continuous_ofReal.tendsto x).comp hlim,
      Eventually.of_forall fun n => show (0 : ℝ) ≤ ((xn n : ℝ) : ℂ).im by simp⟩
  have hFn := hF.comp hc
  have him : (extendFrom H (fwdMapInv W t) x).im = 0 := by
    refine tendsto_nhds_unique ((continuous_im.tendsto _).comp hFn) ?_
    refine (tendsto_const_nhds (x := (0 : ℝ))).congr fun n => ?_
    simp only [Function.comp_apply, hval n, ofReal_im]
  have hre : 0 ≤ (extendFrom H (fwdMapInv W t) x).re :=
    ge_of_tendsto ((continuous_re.tendsto _).comp hFn) (Eventually.of_forall fun n => by
      simp only [Function.comp_apply, hval n, ofReal_re]; exact (hy0 n).le)
  exact hFx ⟨him, hre⟩

/-- **Left real points mapped off the closed left half-line lie right of the image of `0⁻`**. -/
theorem neg_rightImg_sub_lt_of_extendFrom (hB : HasBdryLimits (fwdMapInv W t)) (hW : Continuous W)
    (hW0 : W 0 = 0) (ht : 0 ≤ t) {x : ℝ}
    (hFx : ¬ ((extendFrom H (fwdMapInv W t) x).im = 0 ∧ (extendFrom H (fwdMapInv W t) x).re ≤ 0)) :
    -rightImg (fun s => -W s) 0 t - W t < x := by
  by_contra hle
  push Not at hle
  have hM : rightImg (fun s => -W s) 0 t ≤ -x - W t := by linarith
  have hseq : ∀ n : ℕ, ∃ y, 0 < y ∧ Alive (fun s => -W s) y t ∧ -x - W t < gImg (fun s => -W s) y t ∧
      gImg (fun s => -W s) y t < -x - W t + 1 / ((n : ℝ) + 1) :=
    fun n => exists_alive_gImg_mem hW.neg ht (by positivity) hM
  choose y hy0 hya hyM hyM' using hseq
  set xn : ℕ → ℝ := fun n => -(gImg (fun s => -W s) (y n) t + W t) with hxn
  have hcf : ∀ n, cflow (fun s => -W s) (y n) t = gImg (fun s => -W s) (y n) t + W t := fun n => by
    simp only [gImg]
    ring
  have hval : ∀ n, extendFrom H (fwdMapInv W t) (xn n) = ((-y n : ℝ) : ℂ) := fun n => by
    have h := extendFrom_eq_of_isForwardSol' hB hW hW0 ht
      (show (0 : ℝ) ≤ (-(y n : ℂ)).im by simp) (WangWu.isForwardSol_neg_of_alive hW (hya n))
    have e : -(cflow (fun s => -W s) (y n) t : ℂ) = ((xn n : ℝ) : ℂ) := by
      rw [hcf n, hxn]
      push_cast
      ring
    rw [e] at h
    rw [h]
    push_cast
    ring
  have hlim : Tendsto xn atTop (𝓝 x) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n : ℕ => x - 1 / ((n : ℝ) + 1))
      (h := fun _ => x) ?_ tendsto_const_nhds (fun n => ?_) (fun n => ?_)
    · simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · have := hyM' n
      simp only [hxn]
      linarith
    · have := hyM n
      simp only [hxn]
      linarith
  have hxH : ((x : ℂ)) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hF : Tendsto (extendFrom H (fwdMapInv W t)) (𝓝[Hbar] (x : ℂ))
      (𝓝 (extendFrom H (fwdMapInv W t) x)) := hB.continuousOn _ hxH
  have hc : Tendsto (fun n => ((xn n : ℝ) : ℂ)) atTop (𝓝[Hbar] (x : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨(Complex.continuous_ofReal.tendsto x).comp hlim,
      Eventually.of_forall fun n => show (0 : ℝ) ≤ ((xn n : ℝ) : ℂ).im by simp⟩
  have hFn := hF.comp hc
  have him : (extendFrom H (fwdMapInv W t) x).im = 0 := by
    refine tendsto_nhds_unique ((continuous_im.tendsto _).comp hFn) ?_
    refine (tendsto_const_nhds (x := (0 : ℝ))).congr fun n => ?_
    simp only [Function.comp_apply, hval n, ofReal_im]
  have hre : (extendFrom H (fwdMapInv W t) x).re ≤ 0 :=
    le_of_tendsto ((continuous_re.tendsto _).comp hFn) (Eventually.of_forall fun n => by
      simp only [Function.comp_apply, hval n, ofReal_re]; linarith [hy0 n])
  exact hFx ⟨him, hre⟩

end Slit

/-! ### The side values of the coupling mean at boundary points -/

section Side

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {γ : ℝ≥0 → ℂ}

/-- **The slit interval at a boundary point** (`mem_slit_of_tendsto_fwdMap` without `p ∈ ℍ`): if `F ≤ 𝓝[ℍ \ K_q] p`
and `f_q → y` along `F`, then `y < V̂^{i,R}_q` when `p` is not a real point `≥ 0`, and `V̂^{i,L}_q < y` when `p` is
not a real point `≤ 0`. -/
theorem mem_slit_of_tendsto_fwdMap' (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hγ : IsGeneratingTrace w ζ γ) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < ζ) {p : ℂ} {F : Filter ℂ} [F.NeBot]
    (hF : F ≤ 𝓝[H \ fwdHull (fun s : ℝ => w s.toNNReal) q] p) {y : ℝ}
    (hy : Tendsto (fwdMap (fun s : ℝ => w s.toNNReal) q) F (𝓝 (y : ℂ))) :
    (¬ (p.im = 0 ∧ p.re ≤ 0) → ∀ i, vL i q - w q < y) ∧ (¬ (p.im = 0 ∧ 0 ≤ p.re) → ∀ i, y < vR i q - w q) := by
  obtain ⟨t₂, hqt₂, ht₂⟩ := exists_real_btwn_of_lt hq
  have ht₂0 : 0 ≤ t₂ := (NNReal.coe_nonneg q).trans hqt₂.le
  have hwc := hp.2.2.2.1
  have hw0 := hp.1
  have hW : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hwc ht₂
  have hW0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂0, hw0]
  have hB := (hγ.isLoewnerTraceLT ht₂).hasBdryLimits hW hW0 q.coe_nonneg hqt₂
  have hFy : extendFrom H (fwdMapInv (frozenDrive w t₂) q) y = p :=
    extendFrom_eq_of_tendsto_fwdMap hγ hwc hw0 hqt₂ ht₂ hF hy
  have hWq : frozenDrive w t₂ q = w q := by
    rw [frozenDrive_eq ⟨q.coe_nonneg, hqt₂.le⟩, Real.toNNReal_coe]
  have hζ0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt (by simp) hq
  refine ⟨fun hpL i => ?_, fun hpR i => ?_⟩
  · have hk := neg_rightImg_sub_lt_of_extendFrom hB hW hW0 q.coe_nonneg (by rwa [hFy])
    have hxL : 0 ≤ -xL i := by
      have := hp.2.2.2.2.2.2.2.1 0 hζ0 i
      rw [hp.1, hp.2.1 i] at this
      linarith
    have hmono : rightImg (fun s => -frozenDrive w t₂ s) 0 q ≤ rightImg (fun s => -frozenDrive w t₂ s) (-xL i) q :=
      rightImg_mono_index hW.neg q.coe_nonneg hxL
    rw [vL_eq_neg_rightImg_frozenDrive hp ht₂ hqt₂.le i]
    rw [hWq] at hk
    linarith
  · have hk := lt_rightImg_sub_of_extendFrom hB hW hW0 q.coe_nonneg (by rwa [hFy])
    have hxR : 0 ≤ xR i := by
      have := hp.2.2.2.2.2.2.2.2.1 0 hζ0 i
      rwa [hp.1, hp.2.2.1 i] at this
    have hmono := rightImg_mono_index hW q.coe_nonneg hxR
    rw [vR_eq_rightImg_frozenDrive hp ht₂ hqt₂.le i]
    rw [hWq] at hk
    linarith

/-- **Right-side height `λ` at a boundary point** (`tendsto_comp_fwdMap_of_pos` for a point `p` that is not a real
point `≥ 0`). -/
theorem tendsto_comp_fwdMap_of_pos' (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hγ : IsGeneratingTrace w ζ γ) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < ζ) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR (fun i => vL i q - w q) (fun i => vR i q - w q))
      (forceJumpSet (fun i => vL i q - w q) (fun i => vR i q - w q)) u)
    {p : ℂ} (hpR : ¬ (p.im = 0 ∧ 0 ≤ p.re)) {F : Filter ℂ} [F.NeBot]
    (hF : F ≤ 𝓝[H \ fwdHull (fun s : ℝ => w s.toNNReal) q] p)
    {y : ℝ} (hy : Tendsto (fwdMap (fun s : ℝ => w s.toNNReal) q) F (𝓝 (y : ℂ))) (hy0 : 0 < y) :
    Tendsto (fun z => u (fwdMap (fun s : ℝ => w s.toNNReal) q z)) F (𝓝 (sleLambda κ)) := by
  have hR := (mem_slit_of_tendsto_fwdMap' hp hγ hq hF hy).2 hpR
  have hζ : ∀ i, vL i q - w q ≤ 0 := fun i => sub_nonpos.2 (hp.2.2.2.2.2.2.2.1 q hq i)
  have hyS : y ∉ forceJumpSet (fun i => vL i q - w q) (fun i => vR i q - w q) := by
    intro hmem
    simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range] at hmem
    rcases hmem with h0 | ⟨i, hi⟩ | ⟨i, hi⟩
    · exact hy0.ne' h0
    · linarith [hζ i]
    · exact (hR i).ne' hi
  have hdata : forceBoundaryData κ ρL ρR (fun i => vL i q - w q) (fun i => vR i q - w q) y = sleLambda κ := by
    simp only [forceBoundaryData, show ¬ y < 0 from not_lt.2 hy0.le, ↓reduceIte]
    rw [Finset.filter_false_of_mem fun i _ => not_le.2 (hR i), Finset.sum_empty, add_zero, mul_one, sleLambda]
  have hbd := hu.2.2 y hyS
  rw [hdata] at hbd
  have hev : ∀ᶠ z in F, z ∈ H \ fwdHull (fun s : ℝ => w s.toNNReal) q := hF self_mem_nhdsWithin
  obtain ⟨t₂, hqt₂, ht₂⟩ := exists_real_btwn_of_lt hq
  have hM : fwdMap (fun s : ℝ => w s.toNNReal) q = fwdMap (frozenDrive w t₂) q :=
    funext fun z => fwdMap_eq_of_eqOn q.coe_nonneg fun r hr => (frozenDrive_eq ⟨hr.1, hr.2.trans hqt₂.le⟩).symm
  have hK : fwdHull (fun s : ℝ => w s.toNNReal) q = fwdHull (frozenDrive w t₂) q :=
    fwdHull_eq_of_eqOn q.coe_nonneg hqt₂ fun r hr => (frozenDrive_eq hr).symm
  have hW : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hp.2.2.2.1 ht₂
  have hmaps : ∀ᶠ z in F, fwdMap (fun s : ℝ => w s.toNNReal) q z ∈ H := hev.mono fun z hz => by
    rw [hM]
    rw [hK] at hz
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hW q.coe_nonneg hz
  exact hbd.comp (tendsto_nhdsWithin_iff.2 ⟨hy, hmaps⟩)

/-- **Left-side height `−λ` at a boundary point** (`tendsto_comp_fwdMap_of_neg` for a point `p` that is not a real
point `≤ 0`). -/
theorem tendsto_comp_fwdMap_of_neg' (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hγ : IsGeneratingTrace w ζ γ) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < ζ) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR (fun i => vL i q - w q) (fun i => vR i q - w q))
      (forceJumpSet (fun i => vL i q - w q) (fun i => vR i q - w q)) u)
    {p : ℂ} (hpL : ¬ (p.im = 0 ∧ p.re ≤ 0)) {F : Filter ℂ} [F.NeBot]
    (hF : F ≤ 𝓝[H \ fwdHull (fun s : ℝ => w s.toNNReal) q] p)
    {y : ℝ} (hy : Tendsto (fwdMap (fun s : ℝ => w s.toNNReal) q) F (𝓝 (y : ℂ))) (hy0 : y < 0) :
    Tendsto (fun z => u (fwdMap (fun s : ℝ => w s.toNNReal) q z)) F (𝓝 (-sleLambda κ)) := by
  have hL := (mem_slit_of_tendsto_fwdMap' hp hγ hq hF hy).1 hpL
  have hζ : ∀ i, 0 ≤ vR i q - w q := fun i => sub_nonneg.2 (hp.2.2.2.2.2.2.2.2.1 q hq i)
  have hyS : y ∉ forceJumpSet (fun i => vL i q - w q) (fun i => vR i q - w q) := by
    intro hmem
    simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range] at hmem
    rcases hmem with h0 | ⟨i, hi⟩ | ⟨i, hi⟩
    · exact hy0.ne h0
    · exact (hL i).ne' hi.symm
    · linarith [hζ i]
  have hdata : forceBoundaryData κ ρL ρR (fun i => vL i q - w q) (fun i => vR i q - w q) y = -sleLambda κ := by
    simp only [forceBoundaryData, hy0, ↓reduceIte]
    rw [Finset.filter_false_of_mem fun i _ => not_lt.2 (hL i).le, Finset.sum_empty, add_zero, mul_one, sleLambda]
  have hbd := hu.2.2 y hyS
  rw [hdata] at hbd
  have hev : ∀ᶠ z in F, z ∈ H \ fwdHull (fun s : ℝ => w s.toNNReal) q := hF self_mem_nhdsWithin
  obtain ⟨t₂, hqt₂, ht₂⟩ := exists_real_btwn_of_lt hq
  have hM : fwdMap (fun s : ℝ => w s.toNNReal) q = fwdMap (frozenDrive w t₂) q :=
    funext fun z => fwdMap_eq_of_eqOn q.coe_nonneg fun r hr => (frozenDrive_eq ⟨hr.1, hr.2.trans hqt₂.le⟩).symm
  have hK : fwdHull (fun s : ℝ => w s.toNNReal) q = fwdHull (frozenDrive w t₂) q :=
    fwdHull_eq_of_eqOn q.coe_nonneg hqt₂ fun r hr => (frozenDrive_eq hr).symm
  have hW : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hp.2.2.2.1 ht₂
  have hmaps : ∀ᶠ z in F, fwdMap (fun s : ℝ => w s.toNNReal) q z ∈ H := hev.mono fun z hz => by
    rw [hM]
    rw [hK] at hz
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hW q.coe_nonneg hz
  exact hbd.comp (tendsto_nhdsWithin_iff.2 ⟨hy, hmaps⟩)

end Side

/-! ### A flow line's side heights at every approached point -/

section Flow

/-- **A flow line's side heights at every approached point of its stopped range** (PROVE-SIDEHEIGHT's
`singlePathSideHeightStatement_of_inputs` for an arbitrary approached point `p`, real points of the trace included):
almost surely on `{q < ζ}`, for every harmonic representative `v` of the range mean and every nontrivial approach `F`
to `p` inside the unbounded component of `ℍ \ η([0, q])` along which `f_q(· − x)` tends to a real `y`: if `y > 0` and
`p − x` is not a real point `≥ 0`, then `v + 𝔥₀ + χ arg f_q′(· − x) → λ − θχ`; if `y < 0` and `p − x` is not a real
point `≤ 0`, it tends to `−λ − θχ`. The named inputs are those of `SinglePathSideHeightStatement`'s proof. -/
theorem singlePathSideHeight_gen (hL75 : Theorem15.Lemma75Statement.{u})
    (hA56 : Restart.RetainedRangeEntranceStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ}
    {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {x θ : ℝ} {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hη : IsFlowLine κ b jumps x θ P h η ζ) {W : ℝ≥0 → Ω → ℝ}
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η ω t - x)) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {m q : ℝ≥0} (hqm : q ≤ m) {ηc : Ω → ℝ≥0 → ℂ}
    (hηcc : ∀ ω, Continuous (ηc ω)) (hηcm : ∀ t, Measurable fun ω => ηc ω t)
    (hηce : ∀ᵐ ω ∂P, ∀ t, ηc ω t = η ω (Restart.capTime m (ζ ω) t)) {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => ηc ω '' {t | (t : ℝ≥0∞) ≤ q} ∩ H) (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ ω → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (ηc ω '' {t | (t : ℝ≥0∞) ≤ q} ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (ηc ω '' {t | (t : ℝ≥0∞) ≤ q} ∩ H) →
        g ω φ = ∫ z, v z * φ z) →
      ∀ (p : ℂ) (F : Filter ℂ), F.NeBot → F ≤ 𝓝[H \ fillH (η ω '' Icc 0 q)] p → ∀ y : ℝ,
        Tendsto (fun z => fwdMap (fun s : ℝ => W s.toNNReal ω) q (z - x)) F (𝓝 (y : ℂ)) →
          (0 < y → ¬ ((p - x).im = 0 ∧ 0 ≤ (p - x).re) → Tendsto (fun z => v z + u₀ z + QuantumZipper.chiC κ *
              (QuantumZipper.logDerivFwd (fun s : ℝ => W s.toNNReal ω) q (z - x)).im) F
            (𝓝 (sleLambda κ - θ * QuantumZipper.chiC κ))) ∧
          (y < 0 → ¬ ((p - x).im = 0 ∧ (p - x).re ≤ 0) → Tendsto (fun z => v z + u₀ z + QuantumZipper.chiC κ *
              (QuantumZipper.logDerivFwd (fun s : ℝ => W s.toNNReal ω) q (z - x)).im) F
            (𝓝 (-sleLambda κ - θ * QuantumZipper.chiC κ))) := by
  classical
  obtain ⟨h', 𝓕, W', VL, VR, B, htrans, hC, htr'⟩ := id hη
  obtain ⟨u₀', hu₀'⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ (flowLineRhoL κ b jumps x θ)
    (flowLineRhoR κ b jumps x θ) (flowLineXL b jumps x) (flowLineXR b jumps x)
  have hrel := Exist.eqOn_flowLine_harmonicExtension hκ hb x θ hu₀ hu₀'
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨hX, -⟩ := hC.2.2.2
  -- good versions of the capped flow line (Lemma 6.2 inputs), from the pair construction with the line twice
  obtain ⟨ηs, hc, h0, hηm, hdet, hloc, hfr, -, hs₁, -⟩ :=
    exists_twoHist_versions hL75 hA56 hκ hκ4 hb hh hη hη hu₀ m
  set s₂ : Fin 2 → ℝ≥0∞ := ![(q : ℝ≥0∞), 0] with hs₂
  have hA₁'loc := isLocalSet_explored_const hh0 hc h0 hηm hdet hloc hfr s₂
  have hA₁'det := comap_explored_const_le_aeSigma hc hdet s₂
  have hA₁'eq : ∀ ω, explored ηs (fun i _ => s₂ i) ω = ηs 0 ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H := fun ω =>
    explored_pair_left ηs q (by rw [h0 1 ω]; simp)
  -- the range of the given version
  set A₁ : Ω → Set ℂ := fun ω => ηc ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H with hA₁_def
  have hA₁A₁' : A₁ =ᵐ[P] explored ηs fun i _ => s₂ i := by
    filter_upwards [hηce, hs₁] with ω h1 h2
    rw [hA₁'eq]
    have : ηc ω = ηs 0 ω := funext fun t => (h1 t).trans (h2 t).symm
    show ηc ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H = _
    rw [this]
  have hA₁loc := Coupling.IsLocalSet.congr_set hA₁'loc hA₁A₁'
  have hA₁det := comap_le_aeSigma_of_ae_eq hA₁A₁' hA₁'det
  have hA₁m : Measurable[_, hittingSigma] A₁ := by
    have h1 := measurable_explored_const (η := fun _ : Fin 1 => ηc) (fun _ => hηcc) (fun _ => hηcm)
      (fun _ => (q : ℝ≥0∞))
    have e : (explored (fun _ : Fin 1 => ηc) fun _ _ => (q : ℝ≥0∞)) = A₁ := by
      funext ω
      simp only [explored, iUnion_const, hA₁_def]
    rwa [e] at h1
  have hA₁b : ∀ ω, Bornology.IsBounded (A₁ ω) := fun ω =>
    (((isCompact_Icc (a := (0 : ℝ≥0)) (b := q)).image (hηcc ω)).isBounded).subset (inter_subset_left.trans (by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := hz
      exact ⟨t, ⟨zero_le, show t ≤ q from by exact_mod_cast ht⟩, rfl⟩))
  -- the range is the stopped range of the flow line on `{q < ζ}`
  have hA₁q : ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ ω → A₁ ω = η ω '' Icc 0 q ∩ H := by
    filter_upwards [hηce] with ω hce hq
    show ηc ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} ∩ H = η ω '' Icc 0 q ∩ H
    congr 1
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      have htq : t ≤ q := by exact_mod_cast ht
      refine ⟨t, ⟨zero_le, htq⟩, ?_⟩
      rw [hce t, Restart.capTime_of_le m (ζ ω) (le_min (ht.trans hq.le) (ENNReal.coe_le_coe.2 (htq.trans hqm)))]
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t, by exact_mod_cast ht.2, ?_⟩
      rw [hce t, Restart.capTime_of_le m (ζ ω)
        (le_min ((ENNReal.coe_le_coe.2 ht.2).trans hq.le) (ENNReal.coe_le_coe.2 (ht.2.trans hqm)))]
  -- every earlier hull lies in the filling of the range
  have hA₁fill : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ q → (t : ℝ≥0∞) < ζ ω →
      (fun z : ℂ => z + x) '' fwdHull (fun s : ℝ => W' s.toNNReal ω) t ⊆ fillH (A₁ ω) := by
    filter_upwards [htr', hηce] with ω htrω hce t htq htζ
    rw [fwdHull_eq_fillH_of_isGeneratingTrace htrω htζ, ← Restart.fillH_image_add_real,
      Restart.image_add_real_eq, hA₁_def, fillH_inter_H]
    refine fillH_mono ?_
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨s, show (s : ℝ≥0∞) ≤ q from ENNReal.coe_le_coe.2 (hs.2.trans htq), ?_⟩
    rw [hce s, Restart.capTime_of_le m (ζ ω)
      (le_min ((ENNReal.coe_le_coe.2 hs.2).trans htζ.le) (ENNReal.coe_le_coe.2 ((hs.2.trans htq).trans hqm)))]
  -- the force data at `q`
  choose u hu using fun ω => Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ (flowLineRhoL κ b jumps x θ)
    (flowLineRhoR κ b jumps x θ) (fun i => VL i q ω - W' q ω) (fun i => VR i q ω - W' q ω)
  have hmain := ae_apply_eq_flowMean_of_range hC hκ htrans hh0 hu₀.1 hu₀' hrel hX htr' hA₁m
    (fun ω => inter_subset_right) hA₁b hA₁loc hA₁det hA₁q hA₁fill hg hu
  filter_upwards [hmain, htr, htr', hC.1.2.2.2.2, hA₁q, hA₁fill] with ω hmω htrω htr'ω hp h1 hfill hq v hv hrep
    p F hFne hFle y hy
  have := hFne
  set χ := QuantumZipper.chiC κ with hχ
  -- the unbounded part and the identification of `v`
  set U := H \ fillH (A₁ ω) with hU
  have hUo : IsOpen U := isOpen_H_diff_fillH (hA₁b ω)
  have hUA : U ⊆ H \ A₁ ω := fun z hz => ⟨hz.1, fun h => hz.2 (subset_fillH inter_subset_right h)⟩
  set M : ℂ → ℝ := fun z => couplingMean κ (fun s : ℝ => W' s.toNNReal ω) q (u ω) (z - x) - θ * χ - u₀ z with hM
  have hKU : U ⊆ H \ (fun z : ℂ => z + x) '' fwdHull (fun s : ℝ => W' s.toNNReal ω) q := fun z hz =>
    ⟨hz.1, fun h => hz.2 (hfill q le_rfl hq h)⟩
  have hMh : InnerProductSpace.HarmonicOnNhd M U :=
    (harmonicOnNhd_flowMean hp.2.2.2.1 hq (hu ω).1 x (θ * χ) hu₀.1).mono hKU
  have hvM : EqOn v M U := eqOn_of_integral_mul_eq hUo (hUA.trans sdiff_subset) (hv.mono hUA) hMh
    fun φ hφ => by rw [← hrep φ (hφ.trans hUA), hmω hq φ hφ]
  have hfillη : fillH (η ω '' Icc 0 q) = fillH (A₁ ω) := by rw [h1 hq, fillH_inter_H]
  have hev : ∀ᶠ z in F, z ∈ U := by
    have := hFle self_mem_nhdsWithin
    rwa [hfillη] at this
  -- the coupling's driver generates the same trace
  have hf := fwdMap_eq_of_isGeneratingTrace htrω htr'ω hq
  have hL := logDerivFwd_eq_of_isGeneratingTrace htrω htr'ω hq
  -- the approach in the centred chart
  set F' : Filter ℂ := Filter.map (fun z => z - x) F with hF'
  have hF'le : F' ≤ 𝓝[H \ fwdHull (fun s : ℝ => W' s.toNNReal ω) q] (p - x) := by
    refine tendsto_nhdsWithin_iff.2 ⟨((continuous_sub_right (x : ℂ)).tendsto _).comp
      (hFle.trans nhdsWithin_le_nhds), hev.mono fun z hz => ?_⟩
    have hz' := hKU hz
    refine ⟨show 0 < (z - x).im by simpa using (show 0 < z.im from hz'.1), fun hK => hz'.2 ⟨z - x, hK, by ring⟩⟩
  have hy' : Tendsto (fwdMap (fun s : ℝ => W' s.toNNReal ω) q) F' (𝓝 (y : ℂ)) := by
    rw [← hf]
    exact tendsto_map'_iff.2 hy
  -- the function along `F`
  have hcongr : (fun z => v z + u₀ z + χ * (QuantumZipper.logDerivFwd (fun s : ℝ => W s.toNNReal ω) q (z - x)).im)
      =ᶠ[F] fun z => u ω (fwdMap (fun s : ℝ => W' s.toNNReal ω) q (z - x)) - θ * χ := by
    filter_upwards [hev] with z hz
    rw [hvM hz, hM, hL]
    simp only [couplingMean]
    ring
  refine ⟨fun hy0 hpR => ?_, fun hy0 hpL => ?_⟩
  · have hlim := tendsto_comp_fwdMap_of_pos' hp htr'ω hq (hu ω) hpR hF'le hy' hy0
    have hlim' : Tendsto (fun z => u ω (fwdMap (fun s : ℝ => W' s.toNNReal ω) q (z - x))) F (𝓝 (sleLambda κ)) :=
      tendsto_map'_iff.1 hlim
    exact (hlim'.sub_const (θ * χ)).congr' hcongr.symm
  · have hlim := tendsto_comp_fwdMap_of_neg' hp htr'ω hq (hu ω) hpL hF'le hy' hy0
    have hlim' : Tendsto (fun z => u ω (fwdMap (fun s : ℝ => W' s.toNNReal ω) q (z - x))) F
        (𝓝 (-sleLambda κ)) :=
      tendsto_map'_iff.1 hlim
    exact (hlim'.sub_const (θ * χ)).congr' hcongr.symm

end Flow

end SideHeightBox

end Sec7

end InteractingSLE
