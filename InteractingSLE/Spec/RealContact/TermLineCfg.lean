/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermCfg
import InteractingSLE.Spec.Supplement.BW1PropFrozen
import InteractingSLE.Spec.Supplement.SB2LnMean

/-!
# The configuration record at a sample of a line

Packet PROVE-RC-TERM, second run (ruling R124). The inputs of SB2's line-mean theorem at one sample:

* `IsTermGood.image_ret`: at a good sample the retained path of the sample is the capped second version on `[0, N]`
  (any cap `capR t N`);
* **`isStagePullback_translate`**: the translation chart `Chart.id.recenter x₁` is a stage pull-back
  (`Theorem14.SB.Ln.IsStagePullback`) of any retained set and any translated hull;
* **`exists_isCfgDriver_sample`** (deterministic): at a good sample, a positive time `t` before the stop with the
  first tip in `ℍ`, a good record of the first driver at own time `t` and a flow type of the chart word: a relative
  driver with `Term.IsCfgDriver` for the translation stage chart, the physical chart, the record driver of the first
  path, the chart word and the stop word of the first record (`IsKSample.exists_isCfg`, `IsKSample.physChart_cfg`,
  `Theorem14.BW1Prop.exists_frozen_trace_close`, `Om.eqOn_explored_mean`, `Term.eqOn_mean_of_isFlowType`).

Deterministic; R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd chiC)

namespace InteractingSLE.RealContact

namespace Term

open LP (reflectC)
open Restart Restart.RetAux79 Supp7 Exist.Staged Exist.StagedLaw Sec2.Assembly Sec7.Lemma76F RLC.AStopProc
open Theorem14 Theorem14.SB
open Supp8.Q3Chain (flowedData flowedJumps)
open Exist.StagedLaw.BoundaryWord (shiftW isSorted_shiftW)

/-! ### The retained path of a good sample -/

section Ret

variable {Ω : Type*} {N : ℝ≥0} {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ηb₂ η₁' : Ω → ℝ≥0 → ℂ} {ζ₁ : Ω → ℝ≥0∞} {x₁ x₂ : ℝ}
  {ω : Ω}

/-- **At a good sample the retained path is the capped second version on `[0, N]`.** -/
theorem IsTermGood.image_ret (hG : IsTermGood N E ηb₂ η₁' ζ₁ x₁ x₂ ω) {η₂ : Ω → ℝ≥0 → ℂ} {ζ₂ : Ω → ℝ≥0∞}
    (hE2 : (E ω).2 = ζ₂ ω) (eb₂ : ∀ s, ηb₂ ω s = η₂ ω (capTime (capR 0 N) (ζ₂ ω) s)) {t : ℝ≥0}
    {ηc₂ : Ω → ℝ≥0 → ℂ} (ec₂ : ∀ s, ηc₂ ω s = η₂ ω (capTime (capR t N) (ζ₂ ω) s)) :
    (fun s : ℝ≥0 => pRho₂ ηb₂ x₂ ω (s : ℝ) + (x₂ : ℂ)) '' Icc 0 (pT N E ω) = ηc₂ ω '' Icc 0 N := by
  have hle : ζ₂ ω ≤ N := by rw [← hE2]; exact hG.life
  have hcap₂ : ∀ m : ℝ≥0, N ≤ m → ∀ s : ℝ≥0, capTime m (ζ₂ ω) s = min s (ζ₂ ω).toNNReal := by
    intro m hm s
    unfold capTime
    rw [min_eq_left (hle.trans (ENNReal.coe_le_coe.2 hm))]
  have h1 : (fun s : ℝ≥0 => pRho₂ ηb₂ x₂ ω (s : ℝ) + (x₂ : ℂ)) '' Icc 0 (pT N E ω) =
      ηb₂ ω '' Icc 0 (pT N E ω) := by
    refine image_congr fun s _ => ?_
    show ηb₂ ω (s : ℝ).toNNReal - (x₂ : ℂ) + (x₂ : ℂ) = ηb₂ ω s
    rw [Real.toNNReal_coe, sub_add_cancel]
  rw [h1, ← hG.image_Icc_N]
  refine image_congr fun s _ => ?_
  rw [eb₂ s, ec₂ s, hcap₂ _ (lt_capR_right 0 N).le, hcap₂ _ (lt_capR_right t N).le]

end Ret

/-! ### The translation stage chart -/

/-- **The translation chart is a stage pull-back** of any retained set and any translated set. -/
theorem isStagePullback_translate (x₁ : ℝ) (A₁ K : Set ℂ) :
    Ln.IsStagePullback (Chart.id.recenter x₁) (fun z : ℂ => z + (x₁ : ℂ)) A₁ ((fun z : ℂ => z + (x₁ : ℂ)) '' K)
      {z | (Chart.id.recenter x₁).2.1 z ∈ A₁} K := by
  have hdom : ∀ z : ℂ, z ∈ H → z ∈ ((Chart.id.recenter x₁).dom : Set ℂ) := by
    intro z hz
    have h := Exist.shiftChart_dom x₁
    have hz' : z ∈ (upperHalfPlaneOpens : Set ℂ) := hz
    rw [← h] at hz'
    exact hz'
  refine ⟨Chart.isConformal_id.recenter x₁, continuousOn_const, fun z _ => ?_,
    (continuous_id.add continuous_const).continuousOn, fun z _ => rfl, fun z => ?_, fun M => ?_, fun x => ?_,
    fun z hz => absurd (hdom z hz.1) hz.2, fun z hz => absurd (hdom z hz.1) hz.2, fun w _ => Iff.rfl,
    fun w _ => ?_⟩
  · have hd : deriv (fun z : ℂ => z - (x₁ : ℂ)) z = 1 := by
      rw [deriv_sub_const]
      exact deriv_id z
    show deriv (fun z : ℂ => z - (x₁ : ℂ)) z =
      ‖deriv (fun z : ℂ => z - (x₁ : ℂ)) z‖ * Complex.exp (((0 : ℝ) : ℂ) * Complex.I)
    rw [hd]
    simp
  · refine (Set.finite_singleton (z - (x₁ : ℂ))).subset fun w hw => ?_
    have h1 : w + (x₁ : ℂ) = z := hw.1
    show w = z - (x₁ : ℂ)
    rw [← h1, add_sub_cancel_right]
  · refine ⟨M + ‖(x₁ : ℂ)‖, fun z _ hz => ?_⟩
    have h1 : ‖z‖ ≤ ‖z + (x₁ : ℂ)‖ + ‖(x₁ : ℂ)‖ := by
      have := norm_sub_le (z + (x₁ : ℂ)) (x₁ : ℂ)
      rwa [add_sub_cancel_right] at this
    linarith
  · refine Or.inr ?_
    show ((x : ℂ) + (x₁ : ℂ)).im = 0
    simp
  · constructor
    · rintro ⟨k, hk, hkw⟩
      have h1 : k + (x₁ : ℂ) = w + (x₁ : ℂ) := hkw
      rw [← add_right_cancel h1]
      exact hk
    · exact fun hw => ⟨w, hw, rfl⟩

/-! ### The configuration at a sample -/

section Sample

variable {Ω : Type*} {N : ℝ≥0} {E₂ : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ηb₂ η₁' : Ω → ℝ≥0 → ℂ} {ζ₁ : Ω → ℝ≥0∞} {x₁ x₂ : ℝ}
  {ω : Ω}

/-- **A relative driver with a configuration record at a good sample** (see the module docstring). -/
theorem exists_isCfgDriver_sample {κ : ℝ} (hκ : 0 < κ) (hG : IsTermGood N E₂ ηb₂ η₁' ζ₁ x₁ x₂ ω) {t : ℝ≥0}
    (ht0 : 0 < t) (htL : (t : ℝ≥0∞) < pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂ ω)
    {e₁ : (ℝ≥0 → ℝ) × ℝ≥0∞} (he₁ : IsRegularDriver e₁) (he₁2 : e₁.2 = ζ₁ ω)
    (hg₁ : LocalExt.IsDrvGood (recHist (recOf (t : ℝ≥0∞) e₁))) {η₁ : ℝ≥0 → ℂ}
    (htr₁ : IsGeneratingTrace e₁.1 e₁.2 (fun s => η₁ s - x₁))
    (hv₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ s) (htip : η₁ t ∈ H)
    {Wv : ℝ≥0 → ℝ} (hWc : Continuous Wv) (hW0 : Wv 0 = 0)
    (hgen : IsGeneratingTrace Wv
      (aLife (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂) ω)
      (aPath (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂) (pStop N E₂ ηb₂ η₁' ζ₁ x₁ x₂) ω))
    {A₁ : Set ℂ}
    (hA₁ : A₁ = fillH ((fun s : ℝ≥0 => pRho₂ ηb₂ x₂ ω (s : ℝ) + (x₂ : ℂ)) '' Icc 0 (pT N E₂ ω)))
    {θ₁ θ₂ : ℝ} {c₁ c₂ : BoundaryWord} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ}
    (hft : FCDet.IsFlowType κ θ₁ (shiftW (pSeed N E₂ x₁ x₂ ω) (pWord κ θ₂ c₂ N E₂ ω)) xL xR ρL ρR)
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {Gu : ℂ → ℝ}
    (hGu : ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 →
      EqOn W (fun r : ℝ => Wv r.toNNReal) (Icc 0 (chartClock (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂ ω) t)) →
      ∀ G : ℂ → ℝ, IsBoundedHarmonicExtension
        (flowedData κ ρL ρR xL xR W (chartClock (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂ ω) t))
        (flowedJumps xL xR W (chartClock (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂ ω) t)) G → EqOn G Gu H) :
    ∃ W : ℝ → ℝ, IsCfgDriver κ θ₁ (Chart.id.recenter x₁)
      (physChart x₂ (pRec N E₂ ω) (pSeed N E₂ x₁ x₂ ω)) A₁ (rdrv (recOf (t : ℝ≥0∞) e₁))
      (rtime (recOf (t : ℝ≥0∞) e₁)) (fun r : ℝ => Wv r.toNNReal)
      (chartClock (pPath N E₂ ηb₂ η₁' ζ₁ x₁ x₂ ω) t)
      (shiftW (pSeed N E₂ x₁ x₂ ω) (pWord κ θ₂ c₂ N E₂ ω)) (stopWord κ (c₁, θ₁, recOf (t : ℝ≥0∞) e₁)).mean Gu
      W := by
  obtain ⟨q, w, -, hK⟩ := hG.sample
  have htζ : (t : ℝ≥0∞) < e₁.2 := by
    rw [he₁2]
    exact lt_of_lt_of_le htL (physStop_le _ _ _ _ _)
  have hmin : min (t : ℝ≥0∞) e₁.2 = t := min_eq_left htζ.le
  have hrt : rtime (recOf (t : ℝ≥0∞) e₁) = (t : ℝ) := by
    change (((min (t : ℝ≥0∞) e₁.2).toNNReal : ℝ≥0) : ℝ) = t
    rw [hmin, ENNReal.toNNReal_coe]
  have hrd : rdrv (recOf (t : ℝ≥0∞) e₁) =
      fun r : ℝ => e₁.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) t).toNNReal := by
    have h1 : rdrv (recOf (t : ℝ≥0∞) e₁) = stopDrv (t : ℝ≥0∞) e₁ := recDrv_eq_stopDrv he₁ hg₁
    rw [h1]
    funext r
    show e₁.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (min (t : ℝ≥0∞) e₁.2)).toNNReal = _
    rw [hmin]
  -- the global trace of the record driver
  have hα : IsGeneratingTrace e₁.1 (t : ℝ≥0∞) (fun s => η₁ s - x₁) := LP.isGeneratingTrace_mono htr₁ htζ.le
  have hwc : ContinuousOn e₁.1 {s : ℝ≥0 | (s : ℝ≥0∞) ≤ t} := he₁.1.mono fun s hs => lt_of_le_of_lt hs htζ
  obtain ⟨αr, hαr, hαeq⟩ := BW1Prop.exists_frozen_trace_close hα hwc he₁.2.1 ht0
  rw [← hrd] at hαr
  have hsle : ∀ r ∈ Icc (0 : ℝ) t, ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζ₁ ω := fun r hr => by
    rw [← he₁2]
    exact (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)).trans htζ.le
  have hα' : ∀ r ∈ Icc (0 : ℝ) t, αr r = pRho₁ η₁' x₁ ω r.toNNReal := fun r hr => by
    rw [hαeq r hr]
    show η₁ r.toNNReal - (x₁ : ℂ) = η₁' ω r.toNNReal - (x₁ : ℂ)
    rw [hv₁ _ (hsle r hr)]
  have htip' : pRho₁ η₁' x₁ ω t ∈ H := by
    show 0 < (η₁' ω t - (x₁ : ℂ)).im
    rw [hv₁ t (by rw [← he₁2]; exact htζ.le)]
    have : 0 < (η₁ t).im := htip
    simpa using this
  -- the chart identifications
  obtain ⟨hA, hinv, hlift⟩ := hK.physChart_cfg (r := pRec N E₂ ω) rfl rfl (x₁ := x₁) (x₂ := x₂) rfl
  rw [← hA₁] at hA
  have hFO := Theorem15.isOrderedForceWord_flowLine c₁.fn c₁.jumps 0
  have hres := hK.exists_isCfg (κ := κ) (ψ := θ₁) (c := Chart.id.recenter x₁)
    (Φ := physChart x₂ (pRec N E₂ ω) (pSeed N E₂ x₁ x₂ ω)) (A₁ := A₁) (ρL := ρL) (ρR := ρR) (xL := xL)
    (xR := xR) (ρL' := flowLineRhoL κ c₁.fn c₁.jumps 0 θ₁) (ρR' := flowLineRhoR κ c₁.fn c₁.jumps 0 θ₁)
    (xL' := flowLineXL c₁.fn c₁.jumps 0) (xR' := flowLineXR c₁.fn c₁.jumps 0) hxL hxR hFO.2.1 hFO.2.2.2 ht0
    htL (continuous_rdrv _) (rdrv_zero _) hαr hα' htip' hWc hW0 hgen hA hinv hlift
    (β₁ := shiftW (pSeed N E₂ x₁ x₂ ω) (pWord κ θ₂ c₂ N E₂ ω))
    (GE₀ := (stopWord κ (c₁, θ₁, recOf (t : ℝ≥0∞) e₁)).mean) (Gu := Gu)
    (fun G hG => eqOn_mean_of_isFlowType hκ (isSorted_shiftW (isSorted_stopWord κ _) _) hft hG)
    (fun G hG => Om.eqOn_explored_mean c₁ (recOf (t : ℝ≥0∞) e₁) (by rw [hrt]; exact hG)) hGu
  rw [hrt]
  exact hres

end Sample

end Term

end InteractingSLE.RealContact
