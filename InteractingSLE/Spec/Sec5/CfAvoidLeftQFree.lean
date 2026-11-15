/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfLineRegQ

/-!
# Proposition 5.1 in the chart `Q` from first contacts after rational restarts of the counterflow

Packet PROVE-CFAVOID. Specification §5, Proposition 5.1 and its proof (`source/spec/p097-144.md`, pp. 128–135), in the
reversed reading of PROVE-SEC5-P (`Prop51Q.lean`): condition on the flow-line prefix `γ(0, t]` and follow the
counterflow line `c = η′`.

PROVE-SEC5-P reduced `Cond44Ref.Prop51QStatement` to the named input `Prop51Q.CfAvoidLeftQStatement`, a statement
about the **whole life** of the counterflow (`Prop51Q.NoLeftPartHit`: no approach to the left part of
`∂(ℍ \ γ(0, t])` from the past, at any alive time, including approaches through earlier contacts with the prefix).
PROVE-SEC5-R found that this needs the law of the counterflow through all its contacts with the prefix.

This file shows that much less is needed: only **the first contact after each positive rational restart time** `q`
of the counterflow.

* `FirstContactNotLeft W t q c Z`: if `c` stays in `ℍ \ K_t` on `[q, u₀)`, then `c` does not hit the left part along
  `[q, u₀) ∋ u ↑ u₀`; and if `c` stays in `ℍ \ K_t` from `q` to the end of its life, then `c` does not hit the left part
  at the end of its life. Only approaches through a contact-free interval of times are constrained.
* `NoLeftPartHit.firstContactNotLeft`: the whole-life `NoLeftPartHit` implies it at every `q > 0`.
* **`notMem_leftSideOf_of_firstContactNotLeft`** (the no-wrap theorem, contact-free form): `FirstContactNotLeft` at
  every positive rational `t` and `q` already gives "no alive point of `c` lies on the left side of `γ`". The first exit
  from the left side after an alive time `u` is preceded by an interval `[q, v₁)` on which `c` is in the left side,
  hence off every prefix `γ(0, t]`; so only first contacts after a rational restart are used.
* `CfFirstContactQStatement`: the named input with `FirstContactNotLeft` per rational pair `(t, q)` in place of
  `NoLeftPartHit`, on the glued space of `Cond44Ref.Prop51QStatement`; `cfFirstContactQStatement_of_cfAvoidLeftQ`
  (it is implied by `CfAvoidLeftQStatement`);
* **`prop51QStatement_of_cfFirstContact`**: `Prop51QStatement` from `CfLineRegularQStatement` and
  `CfFirstContactQStatement`; with PROVE-SEC5-R's `cfLineRegularQStatement_of_partA`,
  **`prop51QStatement_of_partA_of_cfFirstContact`**.
* The converses (`fwdMap_mem_closure_rightSideOf`, `not_hitsLeftPartAlong_of_eventually`,
  `firstContactNotLeft_of_forall_notMem`, `noLeftPartHit_of_forall_notMem`, `forall_notMem_of_forall_rat`):
  `cfFirstContactQStatement_of_prop51Q` and `cfAvoidLeftQStatement_of_prop51Q`. Given `CfLineRegularQStatement`, the
  three statements `CfAvoidLeftQStatement`, `CfFirstContactQStatement` and `Prop51QStatement` are equivalent; in
  particular neither named input can be false if Proposition 5.1 holds.

The probabilistic content left is a restart statement: for fixed rational `t, q`, conditionally on the flow-line prefix
`γ(0, t]` and the counterflow prefix up to time `q`, the counterflow continued from `q` does not reach the left part of
`∂(ℍ \ γ(0, t])` at its first contact with that prefix (Lemma 5.4's pattern, with the roles of the curves exchanged).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC fwdHull fwdMap)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.CfAvoidLeftQ

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique Cond44Ref Prop51Q

/-! ### First contacts after a restart -/

/-- **The first contact of `c` with the prefix after the restart time `q` is not a hit of the left part** of
`∂(ℍ \ K_t)` (`K_t = fwdHull W t`, the slit `γ(0, t]` for a simple trace): if `c` stays in `ℍ \ K_t` on `[q, u₀)`
(`u₀` alive), then `c` does not hit the left part along `u ↑ u₀`, `u ∈ [q, u₀)`; and if `c` stays in `ℍ \ K_t` at every
alive time from `q` on, then `c` does not hit the left part at the end of its life. -/
def FirstContactNotLeft (W : ℝ → ℝ) (t q : ℝ) (c : ℝ → ℂ) (Z : ℝ≥0∞) : Prop :=
  (∀ u₀ ∈ aliveSet Z, q < u₀ → (∀ v ∈ Ico q u₀, c v ∈ H \ fwdHull W t) →
      ¬ HitsLeftPartAlong W t c (𝓝[Ico q u₀] u₀)) ∧
    (q ∈ aliveSet Z → (∀ v ∈ aliveSet Z ∩ Ici q, c v ∈ H \ fwdHull W t) →
      ¬ HitsLeftPartAlong W t c (termFilter Z ⊓ 𝓟 (aliveSet Z ∩ Ici q)))

/-- Hitting the left part along a filter is monotone in the filter. -/
theorem HitsLeftPartAlong.mono {W : ℝ → ℝ} {t : ℝ} {c : ℝ → ℂ} {F G : Filter ℝ}
    (h : HitsLeftPartAlong W t c F) (hFG : F ≤ G) : HitsLeftPartAlong W t c G := by
  obtain ⟨x, hx, hcl⟩ := h
  exact ⟨x, hx, hcl.mono (inf_le_inf_right _ hFG)⟩

/-- **The whole-life condition implies the restart condition** at every positive restart time. -/
theorem NoLeftPartHit.firstContactNotLeft {W : ℝ → ℝ} {t : ℝ} {c : ℝ → ℂ} {Z : ℝ≥0∞}
    (h : NoLeftPartHit W t c Z) {q : ℝ} (hq : 0 < q) : FirstContactNotLeft W t q c Z := by
  refine ⟨fun u₀ hu₀ _ _ hhit => h.1 u₀ hu₀ (HitsLeftPartAlong.mono hhit (nhdsWithin_mono _ fun v hv => ?_)),
    fun _ _ hhit => h.2 (HitsLeftPartAlong.mono hhit (inf_le_inf_left _ (principal_mono.2 inter_subset_left)))⟩
  exact ⟨⟨hq.trans_le hv.1, ofReal_lt_of_le_of_mem_aliveSet hv.2.le hu₀⟩, hv.2⟩

/-! ### The no-wrap theorem from first contacts after rational restarts -/

variable {W : ℝ → ℝ} {γ : ℝ → ℂ}

/-- **The no-wrap theorem, contact-free form.** Let `γ` be a simple proper Loewner trace of a continuous driver `W`
with `W 0 = 0`, and let `c` be continuous on its alive times and tend to `0` at the end of its life `Z`. If, for every
positive rational `t` and every positive rational restart time `q`, the first contact of `c` with `γ(0, t]` after `q`
is not a hit of the left part of `∂(ℍ \ γ(0, t])`, then no alive point of `c` lies on the left side of `γ`. -/
theorem notMem_leftSideOf_of_firstContactNotLeft (hη : IsLoewnerTrace W γ) (hγ : IsProperArc γ)
    (hW : Continuous W) (hW0 : W 0 = 0) {c : ℝ → ℂ} {Z : ℝ≥0∞} (hc : ContinuousOn c (aliveSet Z))
    (hterm : Tendsto c (termFilter Z ⊓ 𝓟 (aliveSet Z)) (𝓝 0))
    (hhit : ∀ t : ℚ, 0 < t → ∀ q : ℚ, 0 < q → FirstContactNotLeft W t q c Z) {u : ℝ} (hu : u ∈ aliveSet Z) :
    c u ∉ leftSideOf (arcRange γ) := by
  intro hL
  set L := leftSideOf (arcRange γ) with hLdef
  have hLo : IsOpen L := Cond44Ref.isOpen_leftSideOf_arcRange hγ
  have hAo := isOpen_aliveSet Z
  set B := {v | v ∈ aliveSet Z ∧ u ≤ v ∧ c v ∉ L} with hBdef
  by_cases hB : B.Nonempty
  · -- the first exit time `v₁` from the left side after `u`
    set v₁ := sInf B with hv₁def
    have hBb : BddBelow B := ⟨u, fun v hv => hv.2.1⟩
    have huv₁ : u ≤ v₁ := le_csInf hB fun v hv => hv.2.1
    obtain ⟨b, hb⟩ := hB
    have hv₁A : v₁ ∈ aliveSet Z :=
      ⟨hu.1.trans_le huv₁, ofReal_lt_of_le_of_mem_aliveSet (csInf_le hBb hb) hb.1⟩
    have hcv₁ : ContinuousAt c v₁ := hc.continuousAt (hAo.mem_nhds hv₁A)
    have hbelow : ∀ v, u ≤ v → v < v₁ → c v ∈ L := fun v huv hvv₁ => by
      by_contra hv
      have hvA : v ∈ aliveSet Z := ⟨hu.1.trans_le huv, ofReal_lt_of_le_of_mem_aliveSet hvv₁.le hv₁A⟩
      exact absurd (csInf_le hBb ⟨hvA, huv, hv⟩) (not_le.2 hvv₁)
    have hv₁L : c v₁ ∉ L := by
      intro hv₁L
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hcv₁.preimage_mem_nhds (hLo.mem_nhds hv₁L))
      obtain ⟨a, ha, hav⟩ := exists_lt_of_csInf_lt ⟨b, hb⟩ (show v₁ < v₁ + ε by linarith)
      have hv₁a : v₁ ≤ a := csInf_le hBb ha
      refine ha.2.2 (hball ?_)
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    have huv₁' : u < v₁ := lt_of_le_of_ne huv₁ fun h => hv₁L (h ▸ hL)
    -- a rational restart time `q ∈ (u, v₁)`
    obtain ⟨q, huq, hqv₁⟩ := exists_rat_btwn huv₁'
    have hq0 : (0 : ℝ) < q := hu.1.trans huq
    have hGne : (𝓝[Ico (q : ℝ) v₁] v₁).NeBot := by
      rw [nhdsWithin_Ico_eq_nhdsLT hqv₁]
      infer_instance
    have hcG : Tendsto c (𝓝[Ico (q : ℝ) v₁] v₁) (𝓝 (c v₁)) := hcv₁.tendsto.mono_left nhdsWithin_le_nhds
    have hcL : ∀ᶠ v in 𝓝[Ico (q : ℝ) v₁] v₁, c v ∈ L :=
      eventually_nhdsWithin_of_forall fun v hv => hbelow v (huq.le.trans hv.1) hv.2
    obtain ⟨t, ht0, hp, hpt⟩ :=
      exists_rat_of_mem_closure_leftSideOf hη hγ hv₁L (mem_closure_of_tendsto hcG hcL)
    have hfree : ∀ v ∈ Ico (q : ℝ) v₁, c v ∈ H \ fwdHull W t := fun v hv =>
      leftSideOf_subset_H_diff_fwdHull hη hγ (by exact_mod_cast ht0.le) (hbelow v (huq.le.trans hv.1) hv.2)
    exact (hhit t ht0 q (by exact_mod_cast hq0)).1 v₁ hv₁A hqv₁ hfree
      (hitsLeftPartAlong_of_tendsto hη hγ hW hW0 (by exact_mod_cast ht0) hp hpt le_rfl hcG hcL)
  · -- `c` stays on the left side up to the end of its life, and ends at `0 = γ(0)`
    have hall : ∀ v ∈ aliveSet Z, u ≤ v → c v ∈ L := fun v hv huv => by
      by_contra h
      exact hB ⟨v, hv, huv, h⟩
    -- a rational alive restart time `q ≥ u`
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hAo u hu
    obtain ⟨q, huq, hqε⟩ := exists_rat_btwn (show u < u + ε by linarith)
    have hqA : (q : ℝ) ∈ aliveSet Z := hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith)
    have hGne := termFilter_inf_neBot hqA
    have hcG : Tendsto c (termFilter Z ⊓ 𝓟 (aliveSet Z ∩ Ici (q : ℝ))) (𝓝 0) :=
      hterm.mono_left (inf_le_inf_left _ (principal_mono.2 inter_subset_left))
    have hcL : ∀ᶠ v in termFilter Z ⊓ 𝓟 (aliveSet Z ∩ Ici (q : ℝ)), c v ∈ L :=
      mem_inf_of_right (mem_principal.2 fun v hv => hall v hv.1 (huq.le.trans hv.2))
    have h0L : (0 : ℂ) ∉ L := fun h => lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h.1.1)
    obtain ⟨t, ht0, hp, hpt⟩ := exists_rat_of_mem_closure_leftSideOf hη hγ h0L (mem_closure_of_tendsto hcG hcL)
    have hfree : ∀ v ∈ aliveSet Z ∩ Ici (q : ℝ), c v ∈ H \ fwdHull W t := fun v hv =>
      leftSideOf_subset_H_diff_fwdHull hη hγ (by exact_mod_cast ht0.le) (hall v hv.1 (huq.le.trans hv.2))
    exact (hhit t ht0 q (by exact_mod_cast hu.1.trans huq)).2 hqA hfree
      (hitsLeftPartAlong_of_tendsto hη hγ hW hW0 (by exact_mod_cast ht0) hp hpt le_rfl hcG hcL)

/-! ### The converse: no point on the left side gives the restart condition -/

/-- **`f_t` sends the part of `ℍ \ K_t` off the left side of `γ` into the closure of the right side of the mapped
future** (points of the arc beyond the tip are adherent to the right side). -/
theorem fwdMap_mem_closure_rightSideOf (hη : IsLoewnerTrace W γ) (hγ : IsProperArc γ) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ H \ fwdHull W t)
    (hzL : z ∉ leftSideOf (arcRange γ)) : fwdMap W t z ∈ closure (rightSideOf (arcRange (futureArc W t))) := by
  have hcont : ContinuousOn (fwdMap W t) (H \ fwdHull W t) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ht).continuousOn
  have hRK : rightSideOf (arcRange γ) ⊆ H \ fwdHull W t := fun w hw =>
    ⟨hw.1.1, fun hK => hw.1.2 (fwdHull_subset_arcRange hη hγ ht hK)⟩
  have himg : fwdMap W t '' rightSideOf (arcRange γ) ⊆ rightSideOf (arcRange (futureArc W t)) := by
    rintro _ ⟨w, hw, rfl⟩
    exact fwdMap_mem_rightSideOf_futureArc hη hγ hW hW0 ht hw
  by_cases hzA : z ∈ arcRange γ
  · obtain ⟨s, hs, rfl⟩ := hzA
    have hs0 : 0 < s := by
      refine lt_of_le_of_ne hs fun h => ?_
      have hzH := hz.1
      rw [← h, hγ.zero] at hzH
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hzH)
    exact closure_mono himg
      (((hcont.continuousWithinAt hz).mono hRK).mem_closure_image (mem_closure_rightSideOf hγ hs0))
  · rcases hγ.mem_leftSideOf_or_mem_rightSideOf hz.1 hzA with h | h
    · exact absurd h hzL
    · exact subset_closure (fwdMap_mem_rightSideOf_futureArc hη hγ hW hW0 ht h)

/-- **Staying off the left side excludes a hit of the left part**: if, along `F`, eventually `c` is not on the left
side of `γ`, then `c` does not hit the left part of `∂(ℍ \ K_t)` along `F`. -/
theorem not_hitsLeftPartAlong_of_eventually (hη : IsLoewnerTrace W γ) (hγ : IsProperArc γ) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {c : ℝ → ℂ} {F : Filter ℝ}
    (hF : ∀ᶠ u in F, c u ∉ leftSideOf (arcRange γ)) : ¬ HitsLeftPartAlong W t c F := by
  rintro ⟨x, hx, hcl⟩
  set S := {u | c u ∈ H \ fwdHull W t} with hS
  have hS' : ∀ᶠ u in F ⊓ 𝓟 S, c u ∈ H \ fwdHull W t := mem_inf_of_right (mem_principal_self S)
  have hev : ∀ᶠ u in F ⊓ 𝓟 S, c u ∈ H \ fwdHull W t ∧ c u ∉ leftSideOf (arcRange γ) :=
    hS'.and (hF.filter_mono inf_le_left)
  have hxcl : (x : ℂ) ∈ closure (closure (rightSideOf (arcRange (futureArc W t)))) := by
    refine mem_closure_iff_nhds.2 fun n hn => ?_
    obtain ⟨u, hun, huS, huL⟩ := ((mapClusterPt_iff_frequently.1 hcl n hn).and_eventually hev).exists
    exact ⟨_, hun, fwdMap_mem_closure_rightSideOf hη hγ hW hW0 ht huS huL⟩
  rw [closure_closure] at hxcl
  exact (isProperArc_futureArc hη hγ hW hW0 ht).notMem_closure_rightSideOf_of_neg hx hxcl

/-- **The converse of the reduction, pathwise**: if no alive point of `c` lies on the left side of `γ`, the first
contact with `γ(0, t]` after any positive restart time is not a hit of the left part. -/
theorem firstContactNotLeft_of_forall_notMem (hη : IsLoewnerTrace W γ) (hγ : IsProperArc γ) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {q : ℝ} (hq : 0 < q) {c : ℝ → ℂ} {Z : ℝ≥0∞}
    (hmain : ∀ u ∈ aliveSet Z, c u ∉ leftSideOf (arcRange γ)) : FirstContactNotLeft W t q c Z := by
  refine ⟨fun u₀ hu₀ _ _ => not_hitsLeftPartAlong_of_eventually hη hγ hW hW0 ht ?_,
    fun _ _ => not_hitsLeftPartAlong_of_eventually hη hγ hW hW0 ht ?_⟩
  · exact eventually_nhdsWithin_of_forall fun v hv =>
      hmain v ⟨hq.trans_le hv.1, ofReal_lt_of_le_of_mem_aliveSet hv.2.le hu₀⟩
  · exact mem_inf_of_right (mem_principal.2 fun v hv => hmain v hv.1)

/-- **From rational alive times to all alive times**: if `c` is continuous at its alive times and no alive point at a
positive rational time lies on an open set `L`, then no alive point does. -/
theorem forall_notMem_of_forall_rat {c : ℝ → ℂ} {Z : ℝ≥0∞} (hc : ContinuousOn c (aliveSet Z)) {L : Set ℂ}
    (hL : IsOpen L) (hrat : ∀ s : ℚ, (s : ℝ) ∈ aliveSet Z → c s ∉ L) : ∀ u ∈ aliveSet Z, c u ∉ L := by
  intro u hu hcu
  have hnhds : c ⁻¹' L ∩ aliveSet Z ∈ 𝓝 u :=
    inter_mem ((hc.continuousAt ((isOpen_aliveSet Z).mem_nhds hu)).preimage_mem_nhds (hL.mem_nhds hcu))
      ((isOpen_aliveSet Z).mem_nhds hu)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  obtain ⟨s, hus, hsε⟩ := exists_rat_btwn (show u < u + ε by linarith)
  have hs : (s : ℝ) ∈ Metric.ball u ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  exact hrat s (hball hs).2 (hball hs).1

/-! ### The restart input on the glued space and Proposition 5.1 in the chart `Q` -/

/-- **Restart input: the counterflow's first contact with a flow-line prefix after a rational restart is not on the
left part** (the restart form of Lemma 4.7 at angle `θ > π/2`; Lemma 5.4's pattern with the two curves exchanged).
Same setting as `Prop51Q.CfAvoidLeftQStatement` and `Cond44Ref.Prop51QStatement`. For positive rationals `t` (a time
of the flow line) and `q` (a restart time of the counterflow), almost surely on the glued space, for the Loewner chart
`f_t` of the flow-line prefix `η(0, t]` (any continuous driver `W`, `W 0 = 0`, of which `η` is the trace), the first
contact of the counterflow line with that prefix after time `q` is not a hit of the left part of `∂(ℍ \ η(0, t])`
(`FirstContactNotLeft`). It is implied by `CfAvoidLeftQStatement` (`cfFirstContactQStatement_of_cfAvoidLeftQ`) and
suffices for `Prop51QStatement` (`prop51QStatement_of_cfFirstContact`). -/
def CfFirstContactQStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ a b θ₁ θ₂ : ℝ, θ₁ < θ₂ →
    sleLambda κ - θ₁ * chiC κ ≤ b → sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a →
    ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
      (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ)),
      IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P h η ζ →
      ∀ {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
        IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ →
        P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂ →
        ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
          P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k →
          ∀ t : ℚ, 0 < t → ∀ q : ℚ, 0 < q →
            ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
                ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))),
              ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 → IsLoewnerTrace W (fun s : ℝ => η p.1 s.toNNReal) →
                FirstContactNotLeft W t q (revLine p.2) p.2.1

/-- **The restart input is weaker than the whole-life input.** -/
theorem cfFirstContactQStatement_of_cfAvoidLeftQ (havoid : CfAvoidLeftQStatement.{u}) :
    CfFirstContactQStatement.{u} := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk t ht q hq
  filter_upwards [havoid κ hκ hκ4 a b θ₁ θ₂ h12 hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk t ht] with p hp
  exact fun W hWc hW0 hLT => NoLeftPartHit.firstContactNotLeft (hp W hWc hW0 hLT) (by exact_mod_cast hq)

/-- **`Cond44Ref.Prop51QStatement` from the counterflow's regularity and the restart input.** -/
theorem prop51QStatement_of_cfFirstContact (hreg : CfLineRegularQStatement.{u})
    (hfirst : CfFirstContactQStatement.{u}) : Prop51QStatement.{u} := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  have hχ := Sec4.chiC_pos hκ hκ4
  have hθχ : θ₁ * chiC κ ≤ θ₂ * chiC κ := mul_le_mul_of_nonneg_right h12.le hχ.le
  have hF := Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data a b) {0} 0
  have h44₂ := Sec7.Lemma71H.cond44_flowLine_prop74Data (θ := θ₂) hκ (a := a) (b := b) ha (by linarith)
  have hadm₂ := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44₂
  set X := fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)) with hXdef
  have hXm : Measurable X := (measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)
  -- the flow line, on the glued space
  have hfl' := ae_glue_fst (μ := P) k hXm (ae_exists_isLoewnerTrace_of_isFlowLine hκ hκ4.le hadm₂ hfl)
  -- the counterflow line, on the glued space
  have hregG := hreg κ hκ hκ4 a b θ₁ hb (by linarith) P h hh P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  -- the restart input at every pair of positive rationals
  have hfG : ∀ᵐ p ∂(glueMeasure P k X hXm), ∀ t : ℚ, 0 < t → ∀ q : ℚ, 0 < q →
      ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 → IsLoewnerTrace W (fun s : ℝ => η p.1 s.toNNReal) →
        FirstContactNotLeft W t q (revLine p.2) p.2.1 := by
    rw [ae_all_iff]
    intro t
    by_cases ht : 0 < t
    · have hall : ∀ᵐ p ∂(glueMeasure P k X hXm), ∀ q : ℚ, 0 < q →
          ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 → IsLoewnerTrace W (fun s : ℝ => η p.1 s.toNNReal) →
            FirstContactNotLeft W t q (revLine p.2) p.2.1 := by
        rw [ae_all_iff]
        intro q
        by_cases hq : 0 < q
        · filter_upwards [hfirst κ hκ hκ4 a b θ₁ θ₂ h12 hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk t ht q hq]
            with p hp
          exact fun _ => hp
        · exact Eventually.of_forall fun p h => absurd h hq
      filter_upwards [hall] with p hp
      exact fun _ => hp
    · exact Eventually.of_forall fun p h => absurd h ht
  filter_upwards [hfl', hregG, hfG] with p hp1 hp2 hp3 s
  obtain ⟨W, hWc, hW0, hLT, hγ⟩ := hp1
  obtain ⟨hy, -, -, hβ, hne, htend⟩ := hp2
  have hp2 := isRegularCfLine_of hy hβ.2.1 hne htend
  unfold cfPts
  split_ifs with hs
  · rw [← arcRange_toNNReal]
    exact notMem_leftSideOf_of_firstContactNotLeft hLT hγ hWc hW0 hp2.1 hp2.2
      (fun t ht q hq => hp3 t ht q hq W hWc hW0 hLT) ⟨by exact_mod_cast hs.1, hs.2⟩
  · exact fun h0 => lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h0.1.1)

/-- **`Cond44Ref.Prop51QStatement` from Zhan's Part A inputs at `16/κ` and the restart input.** -/
theorem prop51QStatement_of_partA_of_cfFirstContact (hA : PartAInputsSixteenDiv)
    (hfirst : CfFirstContactQStatement.{u}) : Prop51QStatement.{u} :=
  prop51QStatement_of_cfFirstContact (CfLineRegQ.cfLineRegularQStatement_of_partA hA) hfirst

/-- **The restart input is also necessary**: given the counterflow's regularity, `Prop51QStatement` implies
`CfFirstContactQStatement`. With `prop51QStatement_of_cfFirstContact`, the two are equivalent given
`CfLineRegularQStatement`; so the restart input is exactly the remaining content of Proposition 5.1 in the chart `Q`
(it is not stronger, and it is true if Proposition 5.1 is). -/
theorem cfFirstContactQStatement_of_prop51Q (hreg : CfLineRegularQStatement.{u})
    (h51 : Prop51QStatement.{u}) : CfFirstContactQStatement.{u} := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk t ht q hq
  have hχ := Sec4.chiC_pos hκ hκ4
  have hθχ : θ₁ * chiC κ ≤ θ₂ * chiC κ := mul_le_mul_of_nonneg_right h12.le hχ.le
  have hF := Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data a b) {0} 0
  have h44₂ := Sec7.Lemma71H.cond44_flowLine_prop74Data (θ := θ₂) hκ (a := a) (b := b) ha (by linarith)
  have hadm₂ := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44₂
  set X := fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)) with hXdef
  have hXm : Measurable X := (measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)
  have hfl' := ae_glue_fst (μ := P) k hXm (ae_exists_isLoewnerTrace_of_isFlowLine hκ hκ4.le hadm₂ hfl)
  have hregG := hreg κ hκ hκ4 a b θ₁ hb (by linarith) P h hh P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  have h51G := h51 κ hκ hκ4 a b θ₁ θ₂ h12 hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  filter_upwards [hfl', hregG, h51G] with p hp1 hp2 hp3 W hWc hW0 hLT
  obtain ⟨-, -, -, -, hγ⟩ := hp1
  obtain ⟨hy, -, -, hβ, hne, htend⟩ := hp2
  have hreg' := isRegularCfLine_of hy hβ.2.1 hne htend
  have hL : IsOpen (leftSideOf (arcRange fun s : ℝ => η p.1 s.toNNReal)) :=
    Cond44Ref.isOpen_leftSideOf_arcRange hγ
  refine firstContactNotLeft_of_forall_notMem hLT hγ hWc hW0 (by exact_mod_cast ht.le) (by exact_mod_cast hq)
    (forall_notMem_of_forall_rat hreg'.1 hL fun s hs => ?_)
  have h3 := hp3 s
  have hcf' : cfPts p.2 s = revLine p.2 s := by
    unfold cfPts
    split_ifs with hc
    · rfl
    · exact absurd ⟨by exact_mod_cast hs.1, hs.2⟩ hc
  rwa [hcf', ← arcRange_toNNReal] at h3

/-- **The whole-life condition from "no point on the left side"**, pathwise: if no alive point of `c` lies on the left
side of `γ`, then `c` never hits the left part of `∂(ℍ \ γ(0, t])`. -/
theorem noLeftPartHit_of_forall_notMem (hη : IsLoewnerTrace W γ) (hγ : IsProperArc γ) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {c : ℝ → ℂ} {Z : ℝ≥0∞}
    (hmain : ∀ u ∈ aliveSet Z, c u ∉ leftSideOf (arcRange γ)) : NoLeftPartHit W t c Z :=
  ⟨fun _ _ => not_hitsLeftPartAlong_of_eventually hη hγ hW hW0 ht
      (eventually_nhdsWithin_of_forall fun v hv => hmain v hv.1),
    not_hitsLeftPartAlong_of_eventually hη hγ hW hW0 ht (mem_inf_of_right (mem_principal.2 hmain))⟩

/-- **The whole-life input is also implied by Proposition 5.1** (given the counterflow's regularity). Hence, given
`CfLineRegularQStatement`, the three statements `CfAvoidLeftQStatement`, `CfFirstContactQStatement` and
`Prop51QStatement` are equivalent; `CfFirstContactQStatement` is the form whose proof needs only the law of the
counterflow from a rational restart time to its next contact with the flow-line prefix. -/
theorem cfAvoidLeftQStatement_of_prop51Q (hreg : CfLineRegularQStatement.{u})
    (h51 : Prop51QStatement.{u}) : CfAvoidLeftQStatement.{u} := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk t ht
  have hχ := Sec4.chiC_pos hκ hκ4
  have hθχ : θ₁ * chiC κ ≤ θ₂ * chiC κ := mul_le_mul_of_nonneg_right h12.le hχ.le
  have hF := Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data a b) {0} 0
  have h44₂ := Sec7.Lemma71H.cond44_flowLine_prop74Data (θ := θ₂) hκ (a := a) (b := b) ha (by linarith)
  have hadm₂ := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44₂
  set X := fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)) with hXdef
  have hXm : Measurable X := (measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)
  have hfl' := ae_glue_fst (μ := P) k hXm (ae_exists_isLoewnerTrace_of_isFlowLine hκ hκ4.le hadm₂ hfl)
  have hregG := hreg κ hκ hκ4 a b θ₁ hb (by linarith) P h hh P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  have h51G := h51 κ hκ hκ4 a b θ₁ θ₂ h12 hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  filter_upwards [hfl', hregG, h51G] with p hp1 hp2 hp3 W hWc hW0 hLT
  obtain ⟨-, -, -, -, hγ⟩ := hp1
  obtain ⟨hy, -, -, hβ, hne, htend⟩ := hp2
  have hreg' := isRegularCfLine_of hy hβ.2.1 hne htend
  have hL : IsOpen (leftSideOf (arcRange fun s : ℝ => η p.1 s.toNNReal)) :=
    Cond44Ref.isOpen_leftSideOf_arcRange hγ
  refine noLeftPartHit_of_forall_notMem hLT hγ hWc hW0 (by exact_mod_cast ht.le)
    (forall_notMem_of_forall_rat hreg'.1 hL fun s hs => ?_)
  have h3 := hp3 s
  have hcf' : cfPts p.2 s = revLine p.2 s := by
    unfold cfPts
    split_ifs with hc
    · rfl
    · exact absurd ⟨by exact_mod_cast hs.1, hs.2⟩ hc
  rwa [hcf', ← arcRange_toNNReal] at h3

end InteractingSLE.Sec5.CfAvoidLeftQ
