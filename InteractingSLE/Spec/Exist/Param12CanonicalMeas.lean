/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.Param12Sampled
import InteractingSLE.Spec.Exist.Param12Conv

/-!
# The protected characteristic function on the code space, measurable in the word (S4)

Packet PROVE-PARAM12C. On pairs (word data, code) `p = (w, x)`:

* `cwP`, `stWord`, `uP`: the decoded driver, the word of the state at time `t` (marks relative to the driver and the
  weights of `w`) and the explicit bounded harmonic extension of the state (`Param12Conv.wordExt`);
* `aliveSet K q`: the codes in `Good` at which `K` is alive at time `q < ζ` (measurable, `measurableSet_aliveSet`);
* `measurable_cfAt_indicator`: the protected characteristic function `cfAt` at the fixed time `q`, restricted to the
  codes at which a compact `K ⊇ supp ψ` is alive, is jointly measurable in the word and the code. On the codes safe
  with margin `δ` for `supp ψ` it is `exp(i M − E/2)` with the measurable tested mean and energy of
  `Coupling.Assembly11Meas`; the alive set is the increasing union over the margins.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Exist

namespace Param12

open Sec2.Assembly Coupling Ito Staged

variable {nL nR : ℕ}

/-! ### Processes on (word data, code) -/

/-- The decoded driver on pairs (word data, code). -/
def cwP (t : ℝ≥0) (p : WordData nL nR × XCode nL nR) : ℝ := cw p.2 t

/-- The word of the state at time `t`: marks relative to the driver, and the weights of the word. -/
def stWord (p : WordData nL nR × XCode nL nR) (t : ℝ≥0) : WordData nL nR :=
  (((fun i => cvL p.2 i t - cw p.2 t), (fun j => cvR p.2 j t - cw p.2 t)), p.1.2)

/-- The explicit bounded harmonic extension of the state at time `t`. -/
def uP (κ : ℝ) (p : WordData nL nR × XCode nL nR) (t : ℝ≥0) : ℂ → ℝ := wordExt κ (stWord p t)

theorem isBoundedHarmonicExtension_uP (κ : ℝ) (p : WordData nL nR × XCode nL nR) (t : ℝ≥0) :
    IsBoundedHarmonicExtension
      (forceBoundaryData κ p.1.2.1 p.1.2.2 (fun i => cvL p.2 i t - cw p.2 t) (fun j => cvR p.2 j t - cw p.2 t))
      (forceJumpSet (fun i => cvL p.2 i t - cw p.2 t) (fun j => cvR p.2 j t - cw p.2 t)) (uP κ p t) :=
  isBoundedHarmonicExtension_wordExt κ _ _ _ _

theorem measurable_stWord (t : ℝ≥0) : Measurable fun p : WordData nL nR × XCode nL nR => stWord p t :=
  ((measurable_pi_iff.2 fun i => ((measurable_cvL_at i t).comp measurable_snd).sub
      ((measurable_cw_at t).comp measurable_snd)).prodMk
    (measurable_pi_iff.2 fun j => ((measurable_cvR_at j t).comp measurable_snd).sub
      ((measurable_cw_at t).comp measurable_snd))).prodMk measurable_fst.snd

/-- The constant filtration of the full σ-algebra. -/
def fullFilt (Ω : Type*) [MeasurableSpace Ω] : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) :=
  Filtration.const ℝ≥0 inferInstance le_rfl

theorem fullFilt_apply (Ω : Type*) [MeasurableSpace Ω] (t : ℝ≥0) :
    (fullFilt Ω : ℝ≥0 → MeasurableSpace Ω) t = (inferInstance : MeasurableSpace Ω) := rfl

theorem adaptedBefore_cwP :
    AdaptedBefore (fullFilt (WordData nL nR × XCode nL nR)) (fun p => cζ p.2) cwP := by
  intro t A hA
  have h := adaptedBefore_cw (nL := nL) (nR := nR) t A hA
  have h' : MeasurableSet {x : XCode nL nR | (t : ℝ≥0∞) < cζ x ∧ cw x t ∈ A} :=
    (codeFilt (nL := nL) (nR := nR)).le t _ h
  rw [fullFilt_apply]
  exact measurable_snd h'

theorem measurableSet_goodP :
    MeasurableSet[(fullFilt (WordData nL nR × XCode nL nR)) 0] {p : WordData nL nR × XCode nL nR | Good p.2} := by
  rw [fullFilt_apply]
  exact measurable_snd (measurableSet_good (nL := nL) (nR := nR))

theorem continuousOn_cwP {p : WordData nL nR × XCode nL nR} (hp : p ∈ {p : WordData nL nR × XCode nL nR | Good p.2}) :
    ContinuousOn (fun t => cwP t p) {t | (t : ℝ≥0∞) < cζ p.2} :=
  Good.continuousOn_w hp

/-! ### The alive event on the code space -/

/-- The good codes at which `K` is alive at time `q < ζ`. -/
def codeAlive (K : Set ℂ) (q : ℝ≥0) : Set (XCode nL nR) :=
  {x | Good x ∧ (q : ℝ≥0∞) < cζ x ∧ ∀ z ∈ K, ∃ v, IsForwardSol (rpath (cw x)) z q v}

theorem adaptedBefore_cw_full :
    AdaptedBefore (fullFilt (XCode nL nR)) cζ fun t x => cw x t := by
  intro t A hA
  rw [fullFilt_apply]
  exact (codeFilt (nL := nL) (nR := nR)).le t _ (adaptedBefore_cw t A hA)

/-- On good codes, aliveness of a compact set is safety with some rational margin. -/
theorem codeAlive_eq_iUnion {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) (q : ℝ≥0) :
    codeAlive (nL := nL) (nR := nR) K q =
      ⋃ j : ℕ, {x | Good x ∧ IsSafeAt K (1 / ((j : ℝ) + 1)) q q (cζ x) (cw x) q} := by
  ext x
  simp only [codeAlive, mem_ofPred_eq, mem_iUnion]
  constructor
  · rintro ⟨hg, hq, hal⟩
    obtain ⟨δ, hδ, hsafe⟩ := exists_isSafeAt_of_alive hg.continuousOn_w hK hKH hq hal
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
    exact ⟨j, hg, hsafe.mono hj.le le_rfl le_rfl⟩
  · rintro ⟨j, hg, hsafe⟩
    exact ⟨hg, hsafe.1, fun z hz => (hsafe.2.2.2 z hz).1⟩

theorem measurableSet_codeAlive {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) (q : ℝ≥0) :
    MeasurableSet (codeAlive (nL := nL) (nR := nR) K q) := by
  rw [codeAlive_eq_iUnion hK hKH q]
  refine MeasurableSet.iUnion fun j => ?_
  obtain ⟨D, hDK, hDc, hKD⟩ := (TopologicalSpace.IsSeparable.of_separableSpace K).exists_countable_dense_subset
  have hδ : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  have h := measurableSet_isSafeAt (𝓖 := fullFilt (XCode nL nR)) (G := {x : XCode nL nR | Good x})
    adaptedBefore_cw_full (fun x hx => Good.continuousOn_w hx)
    (by rw [fullFilt_apply]; exact measurableSet_good) hDc (hDK.trans hKH) (σ₀ := fun _ => q)
    (isStoppingTime_const _ q) (1 / ((j : ℝ) + 1)) q q
  rw [fullFilt_apply] at h
  convert h using 1
  ext x
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨hg, hs⟩; exact ⟨hg, hs.subset hDK⟩
  · rintro ⟨hg, hs⟩; exact ⟨hg, hs.of_dense hg.continuousOn_w hKH hKD hDK hδ⟩

/-! ### The protected characteristic function, measurable in (word, code) -/

section CfMeas

variable (κ : ℝ)

/-- The lifetime on pairs. -/
def cζP (p : WordData nL nR × XCode nL nR) : ℝ≥0∞ := cζ p.2

/-- The good pairs. -/
def goodP : Set (WordData nL nR × XCode nL nR) := {p | Good p.2}

theorem measurableSet_goodP' : MeasurableSet (goodP (nL := nL) (nR := nR)) :=
  measurable_snd (measurableSet_good (nL := nL) (nR := nR))

/-- The tested mean at time `q` on the codes safe with margin `δ` for `supp ψ`. -/
def meanP (ψ : LQGMetric.TestOn upperHalfPlaneOpens) (δ : ℝ) (q : ℝ≥0) (p : WordData nL nR × XCode nL nR) : ℝ :=
  ∫ z, (if p ∈ safeSet cwP cζP goodP ψ δ q then
    (wordExt κ (stWord p q) (fwdSafe cwP cζP goodP ψ δ q z p) -
      chiC κ * (logSafe cwP cζP goodP ψ δ q z p).im) * ψ z else 0)

theorem measurableSet_safeSetP (ψ : LQGMetric.TestOn upperHalfPlaneOpens) {δ : ℝ} (hδ : 0 < δ) (q : ℝ≥0) :
    MeasurableSet (safeSet (cwP (nL := nL) (nR := nR)) cζP goodP ψ δ q) := by
  have h := measurableSet_safeSet (𝓖 := fullFilt (WordData nL nR × XCode nL nR)) (G := goodP)
    adaptedBefore_cwP (fun p hp => Good.continuousOn_w hp) measurableSet_goodP (tsupport_subset_H ψ) hδ q
  rw [fullFilt_apply] at h
  exact h

theorem measurable_fwdSafeP (ψ : LQGMetric.TestOn upperHalfPlaneOpens) {δ : ℝ} (hδ : 0 < δ) (q : ℝ≥0) :
    Measurable fun r : ℂ × (WordData nL nR × XCode nL nR) => fwdSafe cwP cζP goodP ψ δ q r.1 r.2 := by
  have h := measurable_fwdSafe (𝓖 := fullFilt (WordData nL nR × XCode nL nR)) (G := goodP)
    adaptedBefore_cwP (fun p hp => Good.continuousOn_w hp) measurableSet_goodP (tsupport_subset_H ψ) hδ q
  rw [fullFilt_apply, ← BorelSpace.measurable_eq] at h
  exact h

theorem measurable_logSafeP (ψ : LQGMetric.TestOn upperHalfPlaneOpens) {δ : ℝ} (hδ : 0 < δ) (q : ℝ≥0) :
    Measurable fun r : ℂ × (WordData nL nR × XCode nL nR) => logSafe cwP cζP goodP ψ δ q r.1 r.2 := by
  have h := measurable_logSafe (𝓖 := fullFilt (WordData nL nR × XCode nL nR)) (G := goodP)
    adaptedBefore_cwP (fun p hp => Good.continuousOn_w hp) measurableSet_goodP (tsupport_subset_H ψ) hδ q
  rw [fullFilt_apply, ← BorelSpace.measurable_eq] at h
  exact h

theorem measurable_meanP_integrand (ψ : LQGMetric.TestOn upperHalfPlaneOpens) (q : ℝ≥0)
    {S : Set (WordData nL nR × XCode nL nR)} (hS : MeasurableSet S)
    {f l : ℂ → WordData nL nR × XCode nL nR → ℂ}
    (hf : Measurable fun r : ℂ × (WordData nL nR × XCode nL nR) => f r.1 r.2)
    (hl : Measurable fun r : ℂ × (WordData nL nR × XCode nL nR) => l r.1 r.2) :
    Measurable fun r : ℂ × (WordData nL nR × XCode nL nR) =>
      (if r.2 ∈ S then (wordExt κ (stWord r.2 q) (f r.1 r.2) - chiC κ * (l r.1 r.2).im) * ψ r.1 else 0) := by
  have hst : Measurable fun r : ℂ × (WordData nL nR × XCode nL nR) => stWord r.2 q :=
    (measurable_stWord q).comp measurable_snd
  -- `wordExt` is kept opaque: unfolding it in unification is very slow
  obtain ⟨E, hE⟩ : ∃ E : WordData nL nR → ℂ → ℝ, E = wordExt κ := ⟨_, rfl⟩
  have hEm : Measurable fun p : WordData nL nR × ℂ => E p.1 p.2 := by rw [hE]; exact measurable_wordExt κ
  rw [← hE]
  have hw : Measurable fun r : ℂ × (WordData nL nR × XCode nL nR) => E (stWord r.2 q) (f r.1 r.2) :=
    hEm.comp (hst.prodMk hf)
  exact Measurable.ite (measurable_snd hS)
    ((hw.sub (measurable_const.mul (Complex.measurable_im.comp hl))).mul
      (ψ.continuous.measurable.comp measurable_fst)) measurable_const

theorem measurable_meanP (ψ : LQGMetric.TestOn upperHalfPlaneOpens) {δ : ℝ} (hδ : 0 < δ) (q : ℝ≥0) :
    Measurable (meanP (nL := nL) (nR := nR) κ ψ δ q) :=
  measurable_integral_param (measurable_meanP_integrand κ ψ q (measurableSet_safeSetP ψ hδ q)
    (measurable_fwdSafeP ψ hδ q) (measurable_logSafeP ψ hδ q))

theorem cfAt_eq_of_mem_safeSet (ψ : LQGMetric.TestOn upperHalfPlaneOpens) {δ : ℝ} (q : ℝ≥0)
    {p : WordData nL nR × XCode nL nR} (hp : p ∈ safeSet cwP cζP goodP ψ δ q) :
    cfAt κ cwP (uP κ) ψ 1 (fun _ => q) p =
      Complex.exp (Complex.I * ((1 : ℝ) : ℂ) * ((meanP κ ψ δ q p : ℝ) : ℂ) -
        ((1 : ℝ) : ℂ) ^ 2 * ((energyK cwP cζP goodP ψ δ q p : ℝ) : ℂ) / 2) := by
  have hm : (∫ z, couplingMean κ (fun s : ℝ => cwP s.toNNReal p) q (uP κ p q) z * ψ z) = meanP κ ψ δ q p := by
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    by_cases hz : z ∈ tsupport (ψ : ℂ → ℝ)
    · simp only [hp, ↓reduceIte, fwdSafe, logSafe, hz, and_self, couplingMean, uP]
      rfl
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have he : loewnerGreenEnergy (fun s : ℝ => cwP s.toNNReal p) q ψ = energyK cwP cζP goodP ψ δ q p := by
    simp only [energyK, hp, ↓reduceIte]
    rfl
  simp only [cfAt, hm, he]

/-- **The protected characteristic function at a fixed time, restricted to the alive codes, is jointly measurable in
the word and the code.** -/
theorem measurable_cfAt_indicator {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H)
    (ψ : LQGMetric.TestOn upperHalfPlaneOpens) (hψK : tsupport (ψ : ℂ → ℝ) ⊆ K) (q : ℝ≥0) :
    Measurable fun p : WordData nL nR × XCode nL nR =>
      if p.2 ∈ codeAlive K q then cfAt κ cwP (uP κ) ψ 1 (fun _ => q) p else 0 := by
  have hψH : tsupport (ψ : ℂ → ℝ) ⊆ H := tsupport_subset_H ψ
  set δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with hδdef
  have hδ : ∀ j, 0 < δ j := fun j => by positivity
  set T : ℕ → WordData nL nR × XCode nL nR → ℂ := fun j p =>
    if p.2 ∈ codeAlive K q ∧ p ∈ safeSet cwP cζP goodP ψ (δ j) q then
      Complex.exp (Complex.I * ((1 : ℝ) : ℂ) * ((meanP κ ψ (δ j) q p : ℝ) : ℂ) -
        ((1 : ℝ) : ℂ) ^ 2 * ((energyK cwP cζP goodP ψ (δ j) q p : ℝ) : ℂ) / 2) else 0 with hT
  have hTm : ∀ j, Measurable (T j) := fun j => by
    have hS := measurableSet_safeSet (𝓖 := fullFilt (WordData nL nR × XCode nL nR)) (G := goodP)
      adaptedBefore_cwP (fun p hp => Good.continuousOn_w hp) measurableSet_goodP hψH (hδ j) q
    have hE := measurable_energyK (𝓖 := fullFilt (WordData nL nR × XCode nL nR)) (G := goodP)
      adaptedBefore_cwP (fun p hp => Good.continuousOn_w hp) measurableSet_goodP hψH (hδ j)
      ψ.continuous.measurable q
    rw [fullFilt_apply] at hS hE
    refine Measurable.ite ((measurable_snd (measurableSet_codeAlive hK hKH q)).inter hS) ?_ measurable_const
    have hM := measurable_meanP (nL := nL) (nR := nR) κ ψ (hδ j) q
    fun_prop
  refine measurable_of_tendsto_metrizable hTm (tendsto_pi_nhds.2 fun p => ?_)
  by_cases hp : p.2 ∈ codeAlive K q
  · obtain ⟨hg, hq, hal⟩ := hp
    obtain ⟨δ₀, hδ₀, hsafe⟩ := exists_isSafeAt_of_alive hg.continuousOn_w hK hKH hq hal
    obtain ⟨j₀, hj₀⟩ := exists_nat_one_div_lt hδ₀
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop j₀] with j hj
    have hδj : δ j ≤ δ₀ := by
      refine le_trans ?_ hj₀.le
      simp only [hδdef]
      gcongr
    have hmem : p ∈ safeSet cwP cζP goodP ψ (δ j) q :=
      ⟨hg, (hsafe.subset hψK).mono hδj le_rfl le_rfl⟩
    simp only [hT, show p.2 ∈ codeAlive K q from ⟨hg, hq, hal⟩, hmem, and_self, ↓reduceIte,
      cfAt_eq_of_mem_safeSet κ ψ q hmem]
  · refine tendsto_const_nhds.congr' (Eventually.of_forall fun j => ?_)
    simp only [hT, hp, false_and, ↓reduceIte]

end CfMeas

end Param12

end Exist

end InteractingSLE
