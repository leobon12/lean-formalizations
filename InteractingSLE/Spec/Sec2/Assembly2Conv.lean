/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly2Max

/-!
# Theorem 2.2, existence: convergence at the horizon in countable form

Packet PROVE-SEC2-PATCH3. For a code whose state is continuous before its horizon `cζ x = T`,
convergence of the state at `T⁻` is the countable condition `Conv x` (near `T` the dyadic values are
close to the dyadic limit `limState`), so it is measurable; and a local solution code that satisfies
the threshold condition at its horizon whenever it converges there is a solution of Definition 2.1
(`isIntegratedSLEPath_of_lRel`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Assembly2

open Assembly

variable {nL nR : ℕ} {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- The dyadic limit of the state at the horizon. -/
def limState (x : XCode nL nR) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) := (limW x, limVL x, limVR x)

/-- **Convergence at the horizon, countable form**: near the horizon the dyadic values of the state
are close to the dyadic limit. -/
def Conv (x : XCode nL nR) : Prop :=
  ∀ m : ℕ, ∃ n₀ k₀, (dyad n₀ k₀ : ℝ≥0∞) < cζ x ∧ ∀ n k, dyad n₀ k₀ ≤ dyad n k →
    (dyad n k : ℝ≥0∞) < cζ x → dist (stateAt x (dyad n k)) (limState x) ≤ 1 / ((m : ℝ) + 1)

theorem measurable_conv : Measurable fun x : XCode nL nR => Conv x := by
  unfold Conv
  refine Measurable.forall fun m => Measurable.exists fun n₀ => Measurable.exists fun k₀ =>
    (measurable_coe_lt _ measurable_cζ).and (Measurable.forall fun n => Measurable.forall fun k =>
      measurable_const_imp _ ((measurable_coe_lt _ measurable_cζ).imp
        (measurable_le' ((measurable_stateAt _).dist measurable_limState) measurable_const)))

/-- `Conv` gives the convergence of the state at the horizon (for a state continuous before it). -/
theorem tendsto_of_conv {x : XCode nL nR}
    (hc : ContinuousOn (stateAt x) {t | (t : ℝ≥0∞) < cζ x}) {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) = cζ x) (h : Conv x) :
    Tendsto (stateAt x) (𝓝[<] T) (𝓝 (limState x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨n₀, k₀, hd₀, hclose⟩ := h m
  have hd₀T : dyad n₀ k₀ < T := by rw [← hT] at hd₀; exact_mod_cast hd₀
  filter_upwards [Ioo_mem_nhdsLT hd₀T] with t ht
  have htT : (t : ℝ≥0∞) < cζ x := by rw [← hT]; exact_mod_cast ht.2
  have hcont : ContinuousAt (stateAt x) t :=
    hc.continuousAt ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds htT)
  have hseq : Tendsto (fun n => stateAt x (dyad n (flr n t))) atTop (𝓝 (stateAt x t)) :=
    hcont.tendsto.comp (tendsto_dyad_flr t)
  have hev : ∀ᶠ n in atTop, dist (stateAt x (dyad n (flr n t))) (limState x) ≤
      1 / ((m : ℝ) + 1) := by
    filter_upwards [(tendsto_dyad_flr t).eventually (Ioi_mem_nhds ht.1)] with n hn
    exact hclose n _ (le_of_lt hn) (lt_of_le_of_lt (by exact_mod_cast dyad_flr_le n t) htT)
  have hle : dist (stateAt x t) (limState x) ≤ 1 / ((m : ℝ) + 1) :=
    le_of_tendsto (((continuous_id.dist continuous_const).tendsto _).comp hseq) hev
  exact lt_of_le_of_lt hle hm

/-- Convergence of the state at the horizon gives `Conv`, and the limit is the dyadic limit. -/
theorem conv_of_tendsto {x : XCode nL nR} {T : ℝ≥0} (hT0 : 0 < T) (hT : (T : ℝ≥0∞) = cζ x)
    {q : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)} (h : Tendsto (stateAt x) (𝓝[<] T) (𝓝 q)) :
    Conv x ∧ limState x = q := by
  have hq : limState x = q := lim_eq_of_tendsto hT0 hT h
  refine ⟨fun m => ?_, hq⟩
  rw [hq]
  have hε : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  have hev := Metric.tendsto_nhds.1 h _ hε
  obtain ⟨u, huT, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hT0).1 hev
  obtain ⟨n₀, k₀, h1, h2⟩ := exists_dyad_btwn (t := u) (ζ := cζ x)
    (by rw [← hT]; exact_mod_cast huT)
  refine ⟨n₀, k₀, h2, fun n k hle hlt => le_of_lt (hsub ⟨lt_of_lt_of_le h1 hle, ?_⟩)⟩
  rw [← hT] at hlt
  exact_mod_cast hlt

/-- **A local solution code that satisfies the threshold condition at its horizon whenever it
converges there is a solution of Definition 2.1.** -/
theorem isIntegratedSLEPath_of_lRel {x : XCode nL nR} (hx : x ∈ LRel a ρL ρR)
    (h0 : cζ x = 0 → ForceWord.ThresholdCondition ρL ρR 0 (wordL x) (wordR x))
    (hlim : 0 < cζ x → cζ x < ⊤ → Conv x →
      ForceWord.ThresholdCondition ρL ρR (limW x) (limVL x) (limVR x)) :
    IsIntegratedSLEPath a (wordL x) (wordR x) ρL ρR (cw x) (cvL x) (cvR x) (cb x) (cζ x) := by
  obtain ⟨hg, -, -, h⟩ := hx
  refine ⟨h.w_zero, h.vL_zero, h.vR_zero, h.continuousOn_w, h.continuousOn_vL, h.continuousOn_vR,
    fun t ht => h.antitone_vL ht, fun t ht => h.vL_le_w ht, fun t ht => h.w_le_vR ht,
    fun t ht => h.monotone_vR ht, fun t ht => h.integrable_gapL ht,
    fun t ht => h.integrable_gapR ht, fun t ht => h.w_eq ht, fun t ht => h.vL_eq ht,
    fun t ht => h.vR_eq ht, h.volume_collisionL, h.volume_collisionR,
    fun t ht => h.not_threshold ht, h0, fun T hT0 hT w₀ vL₀ vR₀ hlimT => ?_⟩
  have hT' : cζ x < ⊤ := by rw [← hT]; exact ENNReal.coe_lt_top
  have h0' : 0 < cζ x := by rw [← hT]; exact_mod_cast hT0
  obtain ⟨hc, hq⟩ := conv_of_tendsto hT0 hT hlimT
  have := hlim h0' hT' hc
  have e : (limW x, limVL x, limVR x) = (w₀, vL₀, vR₀) := hq
  simp only [Prod.mk.injEq] at e
  rw [← e.1, ← e.2.1, ← e.2.2]
  exact this

end Assembly2

end Sec2

end InteractingSLE
