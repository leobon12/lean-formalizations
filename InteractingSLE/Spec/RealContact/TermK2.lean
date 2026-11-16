/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermOrder
import InteractingSLE.Spec.Restart.FCKerDReflChart
import InteractingSLE.Spec.Supplement.CounterflowNoReturnBack
import InteractingSLE.Spec.Supplement.SB2VoCol

/-!
# The chart path of the first path in the original orientation (reflection of the builder frame)

Packet PROVE-RC-TERM, second run (ruling R124). The builder frame (`TermEntryChart` … `TermPathClock`) has the
retained path on the right of the explorer. The flow lines of the path statement have the completed second path on the
**left** of the first one. This module reflects the builder-frame objects by `R(z) = −z̄`:

* `kStop ρ₂ T d ρ₁ ζ`, `kPath U ρ₂ T d ρ₁ ζ`, `kInv U T d`: the physical stop, the chart path (seed-centred, K2's
  orientation) and the boundary inverse of the chart, for the second path `ρ₂` (centred at its seed, driver `U`,
  lifetime `T`), the first path `ρ₁` (centred at its seed, which is at `d ≥ 0` in the coordinates of `ρ₂`);
* `IsKSample U T ρ₂ q d w ζ ρ₁`: the pathwise hypotheses (`IsPathSample` of the reflected data);
* `isAGood_reflect`, **`IsKSample.isAGood`**: the chart path with the physical stop is a good sample of the abstract
  A-stopped processes;
* `IsKSample.kInv_kPath`: `kInv (kPath s) = ρ₁ (s ∧ stop)`;
* **`IsKSample.tendsto_fwdMapInv`**, `IsKSample.extendFrom_eq`: the boundary values of the Loewner inverse of `U`
  are `kInv`, so `kInv U T d v + x₁ = Term.termInv x₂ r (v + τ)` for a record `r` with driver `U`, time `T` and seed
  position `τ = markPos U T d` (`termInv_eq_kInv`);
* `IsFreshRealTip.reflect`.

Deterministic; R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.RealContact

namespace Term

open LP (reflectC)
open Restart Supp7 RLC.AStopProc
open Exist.StagedLaw (markPos markPosL)

/-! ### Reflection of good samples and of fresh real tips -/

/-- **Good samples are reflection invariant.** -/
theorem isAGood_reflect {Ω : Type*} {Γ : Ω → ℝ≥0 → ℂ} {L : Ω → ℝ≥0∞} {ω : Ω} (hg : IsAGood Γ L ω) :
    IsAGood (fun ω s => reflectC (Γ ω s)) L ω := by
  have hclk : chartClock (fun s => reflectC (Γ ω s)) = chartClock (Γ ω) :=
    funext (FCPlumb.FCKerD.chartClock_reflect (Γ ω))
  obtain ⟨hpos, hc, h0, hck, hm, hcc, hconst, W, hWc, hW0, hWg⟩ := hg
  refine ⟨hpos, LP.continuous_reflectC.comp hc, ?_, ?_, ?_, ?_, fun s hs => ?_, -W, hWc.neg, ?_, ?_⟩
  · show reflectC (Γ ω 0) = 0
    rw [h0]
    simp [reflectC]
  · show IsClockOn (chartClock fun s => reflectC (Γ ω s)) (L ω)
    rw [hclk]
    exact hck
  · show Monotone (chartClock fun s => reflectC (Γ ω s))
    rw [hclk]
    exact hm
  · show Continuous (chartClock fun s => reflectC (Γ ω s))
    rw [hclk]
    exact hcc
  · show reflectC (Γ ω s) = reflectC (Γ ω (L ω).toNNReal)
    rw [hconst s hs]
  · show (-W) 0 = 0
    simp [hW0]
  · have hl : aLife (fun ω s => reflectC (Γ ω s)) L ω = aLife Γ L ω := by
      show capLife (chartClock fun s => reflectC (Γ ω s)) (L ω) = capLife (chartClock (Γ ω)) (L ω)
      rw [hclk]
    have hp : aPath (fun ω s => reflectC (Γ ω s)) L ω = fun q => reflectC (aPath Γ L ω q) := by
      funext q
      show reflectC (Γ ω (invClock (chartClock fun s => reflectC (Γ ω s)) (L ω) q)) =
        reflectC (Γ ω (invClock (chartClock (Γ ω)) (L ω) q))
      rw [hclk]
    rw [hl, hp]
    exact LP.isGeneratingTrace_reflect hWg

theorem reflectC_ofReal' (x : ℝ) : reflectC (x : ℂ) = ((-x : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [reflectC]

theorem reflectC_add_ofReal (z : ℂ) (x : ℝ) : reflectC (z + (x : ℂ)) = reflectC z - (x : ℂ) := by
  apply Complex.ext
  · simp only [reflectC, neg_re, conj_re, add_re, ofReal_re, sub_re]
    ring
  · simp only [reflectC, neg_im, conj_im, add_im, ofReal_im, sub_im, add_zero, sub_zero]

theorem reflectC_sub_ofReal (z : ℂ) (x : ℝ) : reflectC (z - (x : ℂ)) = reflectC z + (x : ℂ) := by
  apply Complex.ext
  · simp only [reflectC, neg_re, conj_re, add_re, ofReal_re, sub_re]
    ring
  · simp only [reflectC, neg_im, conj_im, add_im, ofReal_im, sub_im, add_zero, sub_zero]

theorem closure_image_reflectC' (S : Set ℂ) : closure (reflectC '' S) = reflectC '' closure S :=
  (LP.reflectHomeo.image_closure S).symm

/-- **A fresh real tip reflects to a fresh real tip.** -/
theorem IsFreshRealTip.reflect {U : ℝ → ℝ} {T : ℝ} {γ : ℝ → ℂ} {q : ℝ} (h : IsFreshRealTip U T γ q) :
    IsFreshRealTip (-U) T (fun s => reflectC (γ s)) (-q) where
  cont := h.cont.neg
  zero := by simp [h.zero]
  pos := h.pos
  trace := Theorem14.SB.Vo.isLoewnerTraceLT_reflect h.trace
  traceCont := LP.continuous_reflectC.comp_continuousOn h.traceCont
  tip := by rw [h.tip, reflectC_ofReal']
  ne := neg_ne_zero.2 h.ne
  fresh := fun t ht htT hmem => by
    rw [LP.fwdHull_neg, closure_image_reflectC', ← reflectC_ofReal'] at hmem
    obtain ⟨z, hz, hze⟩ := hmem
    have : z = (q : ℂ) := by
      have := congrArg reflectC hze
      rwa [LP.reflectC_reflectC, LP.reflectC_reflectC] at this
    exact h.fresh t ht htT (this ▸ hz)

/-! ### The objects in the original orientation -/

/-- The physical stop: the first positive time at which the first path meets the completed second path. -/
def kStop (ρ₂ : ℝ → ℂ) (T : ℝ≥0) (d : ℝ) (ρ₁ : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) : ℝ≥0∞ :=
  physStop (fun s => reflectC (ρ₂ s)) T d (fun s => reflectC (ρ₁ s)) ζ

/-- The chart path of the first path, stopped at the physical stop (seed-centred chart of the completed second
path). -/
def kPath (U : ℝ → ℝ) (ρ₂ : ℝ → ℂ) (T : ℝ≥0) (d : ℝ) (ρ₁ : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (s : ℝ≥0) : ℂ :=
  reflectC (chartPath (-U) (fun s => reflectC (ρ₂ s)) T d (fun s => reflectC (ρ₁ s)) ζ s)

/-- The physical time `min s stop`. -/
def kTime (ρ₂ : ℝ → ℂ) (T : ℝ≥0) (d : ℝ) (ρ₁ : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (s : ℝ≥0) : ℝ≥0 :=
  stopT (fun s => reflectC (ρ₂ s)) T d (fun s => reflectC (ρ₁ s)) ζ s

/-- The boundary inverse of the seed-centred chart, in the coordinates centred at the first seed. -/
def kInv (U : ℝ → ℝ) (T d : ℝ) (v : ℂ) : ℂ := reflectC (entryInv (-U) T d (reflectC v))

/-- **The pathwise hypotheses in the original orientation**: `Term.IsPathSample` of the reflected data. -/
def IsKSample (U : ℝ → ℝ) (T : ℝ≥0) (ρ₂ : ℝ → ℂ) (q d : ℝ) (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (ρ₁ : ℝ≥0 → ℂ) : Prop :=
  IsPathSample (-U) T (fun s => reflectC (ρ₂ s)) (-q) d (-w) ζ (fun s => reflectC (ρ₁ s))

namespace IsKSample

variable {U : ℝ → ℝ} {T : ℝ≥0} {ρ₂ : ℝ → ℂ} {q d : ℝ} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {ρ₁ : ℝ≥0 → ℂ}
  (h : IsKSample U T ρ₂ q d w ζ ρ₁)
include h

/-- **The chart path with the physical stop is a good sample.** -/
theorem isAGood {Ω : Type*} (ω : Ω) :
    IsAGood (fun _ : Ω => kPath U ρ₂ T d ρ₁ ζ) (fun _ : Ω => kStop ρ₂ T d ρ₁ ζ) ω :=
  isAGood_reflect (IsPathSample.isAGood h ω)

theorem stopPos : 0 < kStop ρ₂ T d ρ₁ ζ := IsPathSample.stopPos h

theorem kPath_zero : kPath U ρ₂ T d ρ₁ ζ 0 = 0 := by
  unfold kPath
  rw [IsPathSample.chartPath_zero h]
  simp [reflectC]

theorem kPath_mem_Hbar (s : ℝ≥0) : 0 ≤ (kPath U ρ₂ T d ρ₁ ζ s).im := by
  unfold kPath
  rw [LP.im_reflectC]
  exact IsPathSample.chartPath_mem_Hbar h s

theorem continuous_kPath : Continuous (kPath U ρ₂ T d ρ₁ ζ) :=
  LP.continuous_reflectC.comp (IsPathSample.continuous_chartPath h)

/-- The boundary inverse of the chart path is the first path at the stopped time. -/
theorem kInv_kPath (s : ℝ≥0) : kInv U (T : ℝ) d (kPath U ρ₂ T d ρ₁ ζ s) = ρ₁ (kTime ρ₂ T d ρ₁ ζ s) := by
  unfold kInv kPath kTime
  rw [LP.reflectC_reflectC, IsPathSample.entryInv_chartPath h, LP.reflectC_reflectC]

theorem injOn_kPath : InjOn (kPath U ρ₂ T d ρ₁ ζ) {r : ℝ≥0 | (r : ℝ≥0∞) ≤ kStop ρ₂ T d ρ₁ ζ} := by
  intro a ha b hb hab
  have hab' := congrArg reflectC hab
  unfold kPath at hab'
  rw [LP.reflectC_reflectC, LP.reflectC_reflectC] at hab'
  exact IsPathSample.injOn_chartPath h ha hb hab'

theorem continuousOn_kInv : ContinuousOn (kInv U (T : ℝ) d) Hbar := by
  have h1 := IsPathSample.entry h
  have h2 : ContinuousOn (entryInv (-U) (T : ℝ) d) {w | 0 ≤ w.im} := h1.continuousOn_entryInv
  refine LP.continuous_reflectC.comp_continuousOn (h2.comp LP.continuous_reflectC.continuousOn fun v hv => ?_)
  show 0 ≤ (reflectC v).im
  rw [LP.im_reflectC]
  exact hv

/-- **The boundary values of the Loewner inverse of the second path.** -/
theorem tendsto_fwdMapInv {v : ℂ} (hv : 0 ≤ v.im) :
    Tendsto (fwdMapInv U (T : ℝ)) (𝓝[H] (v + (markPos U (T : ℝ) d : ℂ)))
      (𝓝 (kInv U (T : ℝ) d v + (d : ℂ))) := by
  have hE := IsPathSample.entry h
  have hU : Continuous U := by
    have := hE.tip.cont.neg
    simpa using this
  have hU0 : U 0 = 0 := by
    have := hE.tip.zero
    simpa using this
  have hT : (0 : ℝ) ≤ T := T.coe_nonneg
  have hmL : markPosL (-U) (T : ℝ) (-d) = -markPos U (T : ℝ) d := by
    unfold markPosL
    have e : (fun s => -(-U) s) = U := funext fun s => by simp
    rw [e, neg_neg]
  have hv' : 0 ≤ (reflectC v).im := by rw [LP.im_reflectC]; exact hv
  have hlim := hE.tendsto_inv hv'
  -- the change of variable `w ↦ reflectC w + τ`
  have hmap : Tendsto (fun w : ℂ => reflectC w + (markPos U (T : ℝ) d : ℂ))
      (𝓝[H] (v + (markPos U (T : ℝ) d : ℂ))) (𝓝[H] (reflectC v)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun w hw => ?_⟩
    · have hc : Continuous fun w : ℂ => reflectC w + (markPos U (T : ℝ) d : ℂ) :=
        LP.continuous_reflectC.add continuous_const
      have h0 := (hc.tendsto (v + (markPos U (T : ℝ) d : ℂ))).mono_left
        (nhdsWithin_le_nhds (s := H))
      have e : reflectC (v + (markPos U (T : ℝ) d : ℂ)) + (markPos U (T : ℝ) d : ℂ) = reflectC v := by
        rw [reflectC_add_ofReal]; ring
      rwa [e] at h0
    · show 0 < (reflectC w + (markPos U (T : ℝ) d : ℂ)).im
      have hw0 : 0 < w.im := hw
      simpa [LP.im_reflectC] using hw0
  have hcomp := hlim.comp hmap
  have hfun : ∀ w ∈ H, ((entryChart (-U) (T : ℝ) d).2.1 ∘
      fun w : ℂ => reflectC w + (markPos U (T : ℝ) d : ℂ)) w = reflectC (fwdMapInv U (T : ℝ) w) + (d : ℂ) := by
    intro w hw
    show (entryChart (-U) (T : ℝ) d).2.1 (reflectC w + (markPos U (T : ℝ) d : ℂ)) = _
    rw [entryChart_inv, hmL]
    have e : reflectC w + (markPos U (T : ℝ) d : ℂ) + ((-markPos U (T : ℝ) d : ℝ) : ℂ) = reflectC w := by
      push_cast; ring
    rw [e, CfNoReturn.fwdMapInv_neg hU hU0 hT hw]
  have h3 : Tendsto (fun w => reflectC (fwdMapInv U (T : ℝ) w) + (d : ℂ))
      (𝓝[H] (v + (markPos U (T : ℝ) d : ℂ))) (𝓝 (entryInv (-U) (T : ℝ) d (reflectC v))) :=
    hcomp.congr' (eventually_nhdsWithin_of_forall hfun)
  have h4 : Tendsto (fun w => reflectC (reflectC (fwdMapInv U (T : ℝ) w) + (d : ℂ)) + (d : ℂ))
      (𝓝[H] (v + (markPos U (T : ℝ) d : ℂ)))
      (𝓝 (reflectC (entryInv (-U) (T : ℝ) d (reflectC v)) + (d : ℂ))) :=
    ((LP.continuous_reflectC.tendsto _).comp h3).add tendsto_const_nhds
  refine h4.congr fun w => ?_
  rw [reflectC_add_ofReal, LP.reflectC_reflectC]
  ring

/-- The boundary extension of the Loewner inverse is `kInv`. -/
theorem extendFrom_eq {v : ℂ} (hv : 0 ≤ v.im) :
    extendFrom H (fwdMapInv U (T : ℝ)) (v + (markPos U (T : ℝ) d : ℂ)) = kInv U (T : ℝ) d v + (d : ℂ) := by
  have hne : (𝓝[H] (v + (markPos U (T : ℝ) d : ℂ))).NeBot :=
    neBot_nhdsWithin_H_of_im_nonneg (by simpa using hv)
  exact (h.tendsto_fwdMapInv hv).limUnder_eq

end IsKSample

/-- **`Term.termInv` in terms of `kInv`**: for a record `r` whose driver and time are those of the sample, the
inverse chart of the path statement at `v + τ` is the first path's point `kInv v + x₁`. -/
theorem termInv_eq_kInv {U : ℝ → ℝ} {T : ℝ≥0} {ρ₂ : ℝ → ℂ} {q d : ℝ} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {ρ₁ : ℝ≥0 → ℂ}
    (h : IsKSample U T ρ₂ q d w ζ ρ₁) {r : Exist.StagedLaw.RecData} (hU : Exist.StagedLaw.rdrv r = U)
    (hT : Exist.StagedLaw.rtime r = (T : ℝ)) {x₁ x₂ : ℝ} (hd : d = x₁ - x₂) {v : ℂ} (hv : 0 ≤ v.im) :
    termInv x₂ r (v + (markPos U (T : ℝ) d : ℂ)) = kInv U (T : ℝ) d v + (x₁ : ℂ) := by
  have hv' : 0 ≤ (v + (markPos U (T : ℝ) d : ℂ)).im := by simpa using hv
  rw [termInv, ite_eq_left hv', hU, hT, h.extendFrom_eq hv, hd]
  push_cast
  ring

end Term

end InteractingSLE.RealContact
