/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb9Trace
import InteractingSLE.Spec.Sec7.ContinuityProb3Steps

/-!
# §7.3 / Lemma LP9: the count prefix of the retargeting

Packet PROVE-SEC7-C10 (step R7 of `planning/handoffs/PROVE-SEC7-C8.md`). Specification §7.3, p. 379 ("The target-change
identity for the force-point equations is used only until the old and new targets are separated"; "At this endpoint
the first two original groups merge") and supplement Lemma LP9, p. 486 ("swallowing the target mark `x_j` is itself
such a merger because `j ≥ 2`").

The stopping time is the first meeting `τ` of the driver with the target mark `V_k` (`firstMeet`), the separation
time of PROVE-SEC7-C9's `sepTime`. Pathwise (`prefix_of_path`):

* the retargeted driver has a trace on `[0, T̃]` (R5, `ae_newW_trace`), which pulls back to a generating trace of the
  original driver on `[0, τ]`, transient when `τ = ∞` (R6, `Zhan.Retarget.PullData.exists_trace`; the driver is
  bounded before a finite `τ`: continuous through `τ < ζ`, or with a left limit at `τ = ζ`, Aux. lemma 3 /
  `ae_tendsto_threshold`);
* at `τ < ζ` the marks `V^R_0 ≤ ⋯ ≤ V^R_k` all meet the driver, so fewer than `N` distinct positions remain;
* at `τ < ζ` the trace is closed at `τ` with its tip: **named input** `TraceClosureStatement` (a deterministic
  Loewner fact — a generating trace on `[0, σ]` of a driver continuous beyond `σ` generates the hull at `σ` and is the
  boundary value of `F_σ` at the driving point; the landed `IsGeneratingTrace.isGeneratingTraceIcc` needs the trace
  beyond `σ`). The same input closes Aux. lemma 99's stopped assertion (PROVE-ZHAN-A6, item 4).

`hasCountPrefix_retarget` assembles `HasCountPrefix` for every distinct word whose transformed word is complete with a
separated start; `lp9PrefixStatement_of_closure` gives `LP9PrefixStatement κ`, the seed case (an original left mark and
an original right mark both at `0`, where the transformed start is not separated) from the named input
`LP9SeedTraceStatement κ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

open Zhan.Retarget

/-- **Named input: closing a generating trace at a time where the driver is still continuous** (deterministic
Loewner theory; Specification p. 379, "The transformed prefix, including its terminal point, is compact … Its inverse
image is a bounded continuous original prefix"; supplement p. 486; PROVE-ZHAN-A6 item 4). If `η` generates the chain
of `w` on `[0, σ]` (hulls before `σ`, continuity up to `σ`) and `w` is continuous on `[0, T)` for some `T > σ`, then
`η` generates the chain on the closed interval `[0, σ]` with its tip at `σ` (`IsGeneratingTraceIcc`). -/
def TraceClosureStatement : Prop :=
  ∀ (w : ℝ≥0 → ℝ) (σ : ℝ≥0) (T : ℝ≥0∞), (σ : ℝ≥0∞) < T → ContinuousOn w {t | (t : ℝ≥0∞) < T} → w 0 = 0 →
    ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace w σ η → IsGeneratingTraceIcc w σ η

/-- A driver continuous before `ζ`, with a left limit at a finite positive `ζ`, is bounded before every finite
`τ ≤ ζ`. -/
theorem exists_bound_before {w : ℝ≥0 → ℝ} {ζ τ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hτζ : τ ≤ ζ) (hτ : τ ≠ ⊤)
    (hlim : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ w₀ : ℝ, Tendsto w (𝓝[<] T) (𝓝 w₀)) :
    ∃ M : ℝ, ∀ s : ℝ≥0, (s : ℝ≥0∞) < τ → |w s| ≤ M := by
  set S := τ.toNNReal with hS
  have hS' : (S : ℝ≥0∞) = τ := ENNReal.coe_toNNReal hτ
  rcases hτζ.lt_or_eq with hlt | heq
  · -- `w` is continuous on `[0, τ]`
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := S)).exists_bound_of_continuousOn
      (hw.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans_lt (hS' ▸ hlt))
    refine ⟨M, fun s hs => ?_⟩
    have := hM s ⟨zero_le, by rw [← hS'] at hs; exact_mod_cast hs.le⟩
    rwa [Real.norm_eq_abs] at this
  · rcases eq_or_ne S 0 with h0 | h0
    · refine ⟨0, fun s hs => ?_⟩
      rw [← hS', h0] at hs
      exact absurd hs (by simp)
    obtain ⟨w₀, hw₀⟩ := hlim S (pos_iff_ne_zero.2 h0) (hS'.trans heq)
    obtain ⟨a, ha, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' (pos_iff_ne_zero.2 h0)).1
      (hw₀.eventually (Metric.ball_mem_nhds w₀ one_pos))
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := a)).exists_bound_of_continuousOn
      (hw.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans_lt (by rw [← heq, ← hS']; exact_mod_cast ha))
    refine ⟨max M (|w₀| + 1), fun s hs => ?_⟩
    have hsS : s < S := by rw [← hS'] at hs; exact_mod_cast hs
    rcases le_or_gt s a with hsa | hsa
    · have := hM s ⟨zero_le, hsa⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    · have h1 : dist (w s) w₀ < 1 := hsub ⟨hsa, hsS⟩
      rw [Real.dist_eq] at h1
      have : |w s| ≤ |w₀| + 1 := by
        have := abs_sub_abs_le_abs_sub (w s) w₀
        linarith
      exact this.trans (le_max_right _ _)

/-! ### The prefix along one path -/

section Path

variable {κ : ℝ} {nL j m : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin (j + 1 + m) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin (j + 1 + m) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

theorem sepTime_eq_firstMeet (w vk : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) :
    sepTime w vk ζ = firstMeet (fun t (_ : Unit) => w t) (fun t _ => vk t) (fun _ => ζ) () := rfl

/-- **At the separation time before the lifetime, the count drops**: the marks `V^R_0 ≤ ⋯ ≤ V^R_k` all meet the
driver, so fewer than `nL + nR` distinct positions remain (`k ≥ 1`). -/
theorem card_lt_of_sepTime_lt (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (hj : 1 ≤ j)
    (hlt : sepTime w (vR (LP.retargetIdx j m)) ζ < ζ) :
    (Finset.univ.image fun i => vL i (sepTime w (vR (LP.retargetIdx j m)) ζ).toNNReal -
        w (sepTime w (vR (LP.retargetIdx j m)) ζ).toNNReal).card +
      (Finset.univ.image fun i => vR i (sepTime w (vR (LP.retargetIdx j m)) ζ).toNNReal -
        w (sepTime w (vR (LP.retargetIdx j m)) ζ).toNNReal).card < nL + (j + 1 + m) := by
  set k := LP.retargetIdx j m with hk
  have hc : ContinuousOn (fun t => vR k t - w t) {t | (t : ℝ≥0∞) < ζ} :=
    (hp.isForcePath.continuousOn_vR k).sub hp.isForcePath.continuousOn_w
  rw [sepTime_eq_firstMeet] at hlt ⊢
  obtain ⟨t₀, ht₀, ht₀ζ, hle⟩ := exists_eq_firstMeet (W := fun t (_ : Unit) => w t)
    (V := fun t _ => vR k t) (ζ := fun _ => ζ) (ω := ()) hc hlt
  rw [ht₀, ENNReal.toNNReal_coe]
  have hwk : vR k t₀ = w t₀ := le_antisymm hle (hp.isForcePath.w_le_vR ht₀ζ k)
  set i₀ : Fin (j + 1 + m) := ⟨0, by omega⟩ with hi₀
  have h0k : i₀ ≤ k := by rw [Fin.le_def]; simp [hi₀]
  have hw0 : vR i₀ t₀ = w t₀ :=
    le_antisymm ((hp.isForcePath.monotone_vR ht₀ζ h0k).trans hwk.le) (hp.isForcePath.w_le_vR ht₀ζ i₀)
  have hne : i₀ ≠ k := by
    intro h
    have := congrArg Fin.val h
    simp [hi₀, hk, LP.retargetIdx] at this
    omega
  have hL : (Finset.univ.image fun i => vL i t₀ - w t₀).card ≤ nL :=
    (Finset.card_image_le).trans (by simp)
  have hR : (Finset.univ.image fun i => vR i t₀ - w t₀).card < j + 1 + m := by
    refine lt_of_le_of_ne ((Finset.card_image_le).trans (by simp)) fun he => ?_
    have hinj := Finset.card_image_iff.1 (he.trans (by simp))
    exact hne (hinj (Finset.mem_coe.2 (Finset.mem_univ _)) (Finset.mem_coe.2 (Finset.mem_univ _))
      (by simp only [hw0, hwk]))
  omega

/-- **The prefix of the retargeting along one path** (R6 + R7, deterministic): from the original path, its left limit
at a finite lifetime, and a trace of the retargeted driver on `[0, T̃]`, the separation time `τ ≤ ζ` carries a
generating trace of the original driver on `[0, τ]` (transient when `τ = ∞`), a count drop at `τ < ζ`, and, with
`TraceClosureStatement`, the closed trace at `τ < ζ`. -/
theorem prefix_of_path (hclose : TraceClosureStatement) (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j)
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hlim : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin (j + 1 + m) → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀)
    (htr : ∃ η' : ℝ≥0 → ℂ, IsGeneratingTrace (newW xR w vR)
        (newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) (sepTime w (vR (LP.retargetIdx j m)) ζ)) η' ∧
      (newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) (sepTime w (vR (LP.retargetIdx j m)) ζ) = ⊤ →
        Tendsto (fun t => ‖η' t‖) atTop atTop)) :
    sepTime w (vR (LP.retargetIdx j m)) ζ ≤ ζ ∧
      (sepTime w (vR (LP.retargetIdx j m)) ζ < ζ →
        (Finset.univ.image fun i => vL i (sepTime w (vR (LP.retargetIdx j m)) ζ).toNNReal -
            w (sepTime w (vR (LP.retargetIdx j m)) ζ).toNNReal).card +
          (Finset.univ.image fun i => vR i (sepTime w (vR (LP.retargetIdx j m)) ζ).toNNReal -
            w (sepTime w (vR (LP.retargetIdx j m)) ζ).toNNReal).card < nL + (j + 1 + m)) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w (sepTime w (vR (LP.retargetIdx j m)) ζ) η ∧
        (sepTime w (vR (LP.retargetIdx j m)) ζ = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) ∧
        (sepTime w (vR (LP.retargetIdx j m)) ζ < ζ →
          IsGeneratingTraceIcc w (sepTime w (vR (LP.retargetIdx j m)) ζ).toNNReal η) := by
  set τ := sepTime w (vR (LP.retargetIdx j m)) ζ with hτdef
  have hτζ : τ ≤ ζ := sepTime_le w _ ζ
  have hrd := retargetData_of_isSLEPathUpTo (hp.isSLEPathUpTo hτζ) hD hj fun t ht => lt_of_lt_sepTime ht
  have hdd : PullData w (vR (LP.retargetIdx j m)) (LP.retargetPos xR) τ :=
    ⟨hrd.pos, hp.1, hrd.sep, hrd.target⟩
  obtain ⟨η', hη', htr'⟩ := htr
  have hbdd : τ ≠ ⊤ → ∃ M : ℝ, ∀ s : ℝ≥0, (s : ℝ≥0∞) < τ → |w s| ≤ M := fun hτ =>
    exists_bound_before hp.isForcePath.continuousOn_w hτζ hτ fun T hT hTζ => by
      obtain ⟨w₀, vL₀, vR₀, hl, -⟩ := hlim T hT hTζ
      exact ⟨w₀, (continuous_fst.tendsto _).comp hl⟩
  obtain ⟨η, hη, hηtr⟩ := hdd.exists_trace hη' htr' hbdd
  refine ⟨hτζ, fun hlt => card_lt_of_sepTime_lt hp hj hlt, η, hη, hηtr, fun hlt => ?_⟩
  have hτ' : ((τ.toNNReal : ℝ≥0) : ℝ≥0∞) = τ := ENNReal.coe_toNNReal (ne_top_of_lt hlt)
  exact hclose w τ.toNNReal ζ (hτ'.symm ▸ hlt) hp.isForcePath.continuousOn_w hp.1 η (hτ'.symm ▸ hη)

end Path

/-! ### The count prefix -/

/-- **`HasCountPrefix` from almost-sure traces of the retargeted driver.** For a distinct-position word with `j ≥ 1`,
if every evolution's retargeted driver almost surely has a trace on `[0, T̃]` (transient when `T̃ = ∞`), then, with
`TraceClosureStatement`, the word has the count prefix at `N = nL + nR`, stopped at the first meeting of the driver
with the target mark. -/
theorem hasCountPrefix_retarget_of_trace {κ : ℝ} (hκ : 0 < κ) (hclose : TraceClosureStatement) {nL j m : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + m) → ℝ}
    (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j)
    (htrace : ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞), IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
      ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ,
        IsGeneratingTrace (newW xR (fun t => W t ω) (fun i t => VR i t ω))
          (newHorizon (LP.retargetPos xR) (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω)
            (sepTime (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω) (ζ ω))) η ∧
        (newHorizon (LP.retargetPos xR) (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω)
            (sepTime (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω) (ζ ω)) = ⊤ →
          Tendsto (fun t => ‖η t‖) atTop atTop)) :
    HasCountPrefix.{u} κ xL xR ρL ρR (nL + (j + 1 + m)) := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  set k := LP.retargetIdx j m with hk
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hE.2.2.2.2)
  have hgood : ∀ ω ∉ N, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) (fun t => B t ω) (ζ ω) := fun ω hω => by
    by_contra h
    exact hω (hNsub h)
  have hN𝓖 : ∀ t, MeasurableSet[usualAugmentation 𝓕 P t] N := fun t =>
    Ito.measurableSet_usualAugmentation_of_null hNm hN0 t
  have hc : ∀ ω ∉ N, ContinuousOn (fun t => VR k t ω - W t ω) {t | (t : ℝ≥0∞) < ζ ω} :=
    fun ω hω => ((hgood ω hω).isForcePath.continuousOn_vR k).sub (hgood ω hω).isForcePath.continuousOn_w
  refine ⟨zeroOn N (firstMeet W (VR k) ζ),
    isStoppingTime_firstMeet_off hE𝓖.2.1 (hE𝓖.2.2.2.1 k) hN𝓖 hc, ?_⟩
  filter_upwards [htrace P 𝓕 W VL VR B ζ hE, hE.ae_tendsto_threshold hκ,
    measure_eq_zero_iff_ae_notMem.1 hN0] with ω htr hlim hωN
  rw [zeroOn_of_notMem hωN]
  exact prefix_of_path hclose hD hj (hgood ω hωN) hlim htr

/-- **LP9's count prefix for a separated transformed start** (R7). -/
theorem hasCountPrefix_retarget {κ : ℝ} (hκ : 0 < κ) (hclose : TraceClosureStatement) {nL j m : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + m) → ℝ}
    (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j) (hsepT : ∀ i i', LP.retargetXL xL xR i < LP.retargetXR xR i')
    (hcT : LP.IsCompleteForceWord.{u} κ (LP.retargetXL xL xR) (LP.retargetXR xR) (LP.retargetρL κ ρL ρR)
      (LP.retargetρR ρR)) :
    HasCountPrefix.{u} κ xL xR ρL ρR (nL + (j + 1 + m)) :=
  hasCountPrefix_retarget_of_trace hκ hclose hD hj fun _ _ _ _ _ _ _ _ hE => ae_newW_trace hκ hD hj hE hsepT hcT

/-- **Named input: the trace of the retargeted driver at a two-sided seed.** When an original left mark and an
original right mark before the target both sit at the seed, LP9's transformed word has marks `0` on both sides, its
start is not separated, and pathwise uniqueness (used by `ae_trace_of_complete`) is not available. This is the
conclusion of `ae_newW_trace` for those words. -/
def LP9SeedTraceStatement (κ : ℝ) : Prop :=
  ∀ {nL j m : ℕ} (xL : Fin nL → ℝ) (xR : Fin (j + 1 + m) → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin (j + 1 + m) → ℝ),
    LP.IsDistinctForceWord xL xR → 1 ≤ j → ¬ (∀ i i', LP.retargetXL xL xR i < LP.retargetXR xR i') →
    LP.IsCompleteForceWord.{u} κ (LP.retargetXL xL xR) (LP.retargetXR xR) (LP.retargetρL κ ρL ρR)
      (LP.retargetρR ρR) →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞), IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
      ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ,
        IsGeneratingTrace (newW xR (fun t => W t ω) (fun i t => VR i t ω))
          (newHorizon (LP.retargetPos xR) (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω)
            (sepTime (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω) (ζ ω))) η ∧
        (newHorizon (LP.retargetPos xR) (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω)
            (sepTime (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω) (ζ ω)) = ⊤ →
          Tendsto (fun t => ‖η t‖) atTop atTop)

/-- **`Sec7.LP9PrefixStatement κ` from the two named inputs** (every `κ > 0`): the closing of a trace at a time where
the driver is continuous, and the seed case of the retargeted trace. -/
theorem lp9PrefixStatement_of_closure {κ : ℝ} (hκ : 0 < κ) (hclose : TraceClosureStatement)
    (hseed : LP9SeedTraceStatement.{u} κ) : LP9PrefixStatement.{u} κ := by
  intro N _ nL j m xL xR ρL ρR hD hsum hj hcT
  subst hsum
  by_cases hsep : ∀ i i', LP.retargetXL xL xR i < LP.retargetXR xR i'
  · exact hasCountPrefix_retarget hκ hclose hD hj hsep hcT
  · exact hasCountPrefix_retarget_of_trace hκ hclose hD hj fun P _ 𝓕 W VL VR B ζ hE =>
      hseed xL xR ρL ρR hD hj hsep hcT P 𝓕 W VL VR B ζ hE

/-! ### The one-sided step -/

/-- A complete word has the count prefix for every `N` (stop at the lifetime). -/
theorem hasCountPrefix_of_isCompleteForceWord {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (h : LP.IsCompleteForceWord.{u} κ xL xR ρL ρR) (N : ℕ) :
    HasCountPrefix.{u} κ xL xR ρL ρR N := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  refine ⟨ζ, Ito.isStoppingTime_lifetime (Ito.isIntegratedSLEEvolution_usualAugmentation hE).2.1, ?_⟩
  filter_upwards [h P 𝓕 W VL VR B ζ hE] with ω ⟨η, hη, htr⟩
  exact ⟨le_rfl, fun h => absurd h (lt_irrefl _), η, hη, htr, fun h => absurd h (lt_irrefl _)⟩

/-- With all marks on the right, LP9's transformed start (target the second mark) is separated: the left marks are
`−1` and `ψ(x_l) < −1`, the right mark `ψ(x_1) ≥ 0`. -/
theorem retarget_sep_of_left_empty {m : ℕ} {xL : Fin 0 → ℝ} {xR : Fin (1 + 1 + m) → ℝ}
    (hD : LP.IsDistinctForceWord xL xR) : ∀ i i', LP.retargetXL xL xR i < LP.retargetXR xR i' := by
  obtain ⟨⟨-, -, -, hR0⟩, -, hmono⟩ := hD
  have hpos := LP.retargetPos_pos hmono hR0 le_rfl
  intro i i'
  have hright : 0 ≤ LP.retargetXR xR i' :=
    Sec7.targetChangeReal_nonneg (hR0 _) (LP.xR_castAdd_castSucc_lt hmono i')
  have hleft : LP.retargetXL xL xR i ≤ -1 := by
    induction i using Fin.addCases with
    | left i => exact i.elim0
    | right k =>
      induction k using Fin.cases with
      | zero => rw [LP.retargetXL, Fin.append_right, Fin.cons_zero]
      | succ l =>
        simp only [LP.retargetXL, Fin.append_right, Fin.cons_succ]
        exact (Sec7.targetChangeReal_lt_neg_one hpos (LP.retargetPos_lt_xR_natAdd hmono _)).le
  linarith

/-- **`Sec7.OneSidedPrefixStatement` from the closing input** (R7, κ < 4 induction). All marks on the right: retarget
the second mark (LP9 with `j = 1`); the transformed word is two-sided with `N` marks (complete by the two-sided
hypothesis) and separated. All marks on the left: reflect, use the right case and the smaller-count hypothesis to
get completeness, reflect back, and stop at the lifetime. -/
theorem oneSidedPrefixStatement_of_closure (hclose : TraceClosureStatement) : OneSidedPrefixStatement.{u} := by
  intro κ hκ hκ4 N hN hbelow htwo nL nR xL xR ρL ρR hD hsum hside
  -- the right case, as a function of the word
  have hright : ∀ {nR' : ℕ} (xL' : Fin 0 → ℝ) (xR' : Fin nR' → ℝ) (ρL' : Fin 0 → ℝ) (ρR' : Fin nR' → ℝ),
      LP.IsDistinctForceWord xL' xR' → nR' = N → HasCountPrefix.{u} κ xL' xR' ρL' ρR' N := by
    intro nR' xL' xR' ρL' ρR' hD' hn
    obtain ⟨m, rfl⟩ : ∃ m, nR' = 1 + 1 + m := ⟨nR' - 2, by omega⟩
    subst hn
    have hcT : LP.IsCompleteForceWord.{u} κ (LP.retargetXL xL' xR') (LP.retargetXR xR')
        (LP.retargetρL κ ρL' ρR') (LP.retargetρR ρR') :=
      htwo (LP.retargetXL xL' xR') (LP.retargetXR xR') (LP.retargetρL κ ρL' ρR') (LP.retargetρR ρR')
        (LP.isDistinctForceWord_retarget hD' le_rfl) (by omega) (by omega) le_rfl
    have h : HasCountPrefix.{u} κ xL' xR' ρL' ρR' (0 + (1 + 1 + m)) :=
      hasCountPrefix_retarget hκ hclose hD' le_rfl (retarget_sep_of_left_empty hD') hcT
    rwa [Nat.zero_add] at h
  rcases hside with rfl | rfl
  · have h : HasCountPrefix.{u} κ xL xR ρL ρR N := hright xL xR ρL ρR hD (by omega)
    intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
    exact h P 𝓕 W VL VR B ζ hE
  · -- reflect
    have hD' := hD.reflect
    have h1 : HasCountPrefix.{u} κ (-xR) (-xL) ρR ρL N := hright (-xR) (-xL) ρR ρL hD' (by omega)
    have hbelow' : LP.DistinctCompleteBelow.{u} κ N := distinctCompleteBelow_of_le (by omega) hbelow
    have hc' : LP.IsCompleteForceWord.{u} κ (-xR) (-xL) ρR ρL :=
      isCompleteForceWord_of_hasCountPrefix hκ hbelow' h1
    have h2 : HasCountPrefix.{u} κ xL xR ρL ρR N :=
      hasCountPrefix_of_isCompleteForceWord (LP.isCompleteForceWord_reflect_iff.1 hc') N
    intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
    exact h2 P 𝓕 W VL VR B ζ hE

end Sec7

end InteractingSLE
