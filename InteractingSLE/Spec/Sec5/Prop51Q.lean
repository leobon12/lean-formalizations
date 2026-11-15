/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51QRev
import InteractingSLE.Spec.Sec5.Prop411Q
import InteractingSLE.Foundations.Loewner.YuanShift

/-!
# Proposition 5.1 in the chart `Q` (`Cond44Ref.Prop51QStatement`) from two counterflow inputs

Packet PROVE-SEC5-P. Specification §5, Proposition 5.1 (pp. 128–135), in the configuration of Proposition 5.5 and in
Lemma 4.5's chart `Q`, on PROVE-SEC5-N's glued space (`Cond44Ref.Prop51QStatement`): the GFF `h` with the data
`−a | b` of Figure 7.1, its flow line `η` of angle `θ₂` (the flow line of `h + (θ₁ − π/2)χ` of angle
`θ = θ₂ − θ₁ + π/2 > π/2`), and a sample of the centred counterflow line of `h + (θ₁ − π/2)χ` glued conditionally
independently given `h`.

The source proves the per-time statement by conditioning on the counterflow prefix and following the flow line (first
contact by Aux. lemma 22, Lemma 5.4 after contact, the no-wrap step). Here the roles are exchanged: one conditions on
the flow-line prefix `γ(0, t]` and follows the counterflow, and the deterministic no-wrap step is
`Prop51Q.notMem_leftSideOf_of_noLeftPartHit` (file `Prop51QRev.lean`), which needs only the side lemmas of the simple
flow line's own Loewner map. The two inputs are named statements (not proved here):

* **`CfLineRegularQStatement`**: the counterflow line of `h + (θ₁ − π/2)χ` (boundary data `≤ −λ′` on `ℝ₋`, `≥ λ′`
  on `ℝ₊`) has PROVE-SEC5-O's regularity (`Prop411Q.CfRegQStatement`: infinite lifetime, continuous driver, Loewner
  trace `β = histLine`), and `β` does not return to `0` and tends to `∞` (Remark 2.3's continuity of `η′` in this
  regime, and Aux. lemma 7 at `κ′ = 16/κ`). `isRegularCfLine_of` turns this into the regularity of `η′ = R ∘ β` used by
  the no-wrap theorem.
* **`CfAvoidLeftQStatement`**: for each positive rational `t`, almost surely the counterflow line never hits the left
  part of `∂(ℍ \ η(0, t])` (the left side of the flow-line prefix and `ℝ₋`; `Prop51Q.NoLeftPartHit`, read in the
  chart `f_t` of the prefix). This is the form at angle `θ > π/2` of Lemma 4.7 (whose `θ = π/2` case is Proposition
  4.11 (a)): conditional on `η([0, t])`, the counterflow is the counterflow line of the conditional field in
  `ℍ \ η([0, t])`, whose heights on `ℝ₋` (`≤ −λ′`) and on the left side of the prefix (`−λ − θχ ≤ −λ′`, since
  `θ ≥ −π/2`, in the flat chart) are in its non-hitting range.

* **`prop51QStatement_of_cfAvoidLeft`**: `Prop51QStatement` from the two inputs.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.Prop51Q

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique Cond44Ref

/-! ### The named inputs -/

/-- The counterflow line read from a history is **regular**: continuous at its alive times, and tending to its target
`0` at the end of its life. -/
def IsRegularCfLine (y : HistorySpace 0 0) : Prop :=
  ContinuousOn (revLine y) (aliveSet y.1) ∧ Tendsto (revLine y) (termFilter y.1 ⊓ 𝓟 (aliveSet y.1)) (𝓝 0)

/-- **Regularity of the counterflow line from that of its trace** (deterministic): if the history has infinite lifetime
and its curve `β = histLine y` is continuous, never returns to `0` at positive times and tends to `∞`, then the
counterflow line `R ∘ β` is continuous at its alive times and tends to `0`. -/
theorem isRegularCfLine_of {y : HistorySpace 0 0} (hy : y.1 = ⊤) (hβ : ContinuousOn (histLine y) (Ici 0))
    (hne : ∀ u : ℝ, 0 < u → histLine y u ≠ 0) (htend : Tendsto (fun u => ‖histLine y u‖) atTop atTop) :
    IsRegularCfLine y := by
  rw [IsRegularCfLine, hy]
  refine ⟨?_, ?_⟩
  · have hsub : aliveSet ⊤ ⊆ Ici 0 := fun u hu => mem_Ici.2 hu.1.le
    exact ((hβ.mono hsub).inv₀ fun u hu => hne u hu.1).neg
  · have hle : termFilter ⊤ ⊓ 𝓟 (aliveSet ⊤) ≤ atTop := by
      refine inf_le_left.trans fun S hS => ?_
      obtain ⟨M, hM⟩ := mem_atTop_sets.1 hS
      refine mem_comap.2 ⟨Ioo (ENNReal.ofReal (max M 0)) ⊤, Ioo_mem_nhdsLT ENNReal.ofReal_lt_top, fun u hu => ?_⟩
      have h1 : max M 0 < u := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_max_right _ _)).1 hu.1
      exact hM u (le_of_lt (lt_of_le_of_lt (le_max_left _ _) h1))
    refine tendsto_zero_iff_norm_tendsto_zero.2 ((tendsto_inv_atTop_zero.comp htend).mono_left hle |>.congr ?_)
    intro u
    simp [revLine, negInv]

/-- **Named input: regularity of the counterflow line** (specification §5, p. 129: "`η′` intersects `∂_L𝒮` only when it
terminates at `0`. Consequently, `η′` is almost surely continuous (recall Remark 2.3)"; Aux. lemma 7 at `κ′ = 16/κ`).
For the data `−a | b` of Figure 7.1 with `b ≥ λ − θ₁χ` and `a ≥ λ − πχ + θ₁χ` (so that `h + (θ₁ − π/2)χ` has heights
`≤ −λ′` on `ℝ₋` and `≥ λ′` on `ℝ₊`), almost surely the counterflow sample glued at `h + (θ₁ − π/2)χ` has PROVE-SEC5-O's
regularity (`Prop411Q.CfRegQStatement`: infinite lifetime, a continuous driver `cfDrv` started at `0`, of which the
curve `β = histLine` is a Loewner trace), and moreover `β` does not return to `0` at positive times and tends to `∞`
(the counterflow `η′ = R ∘ β` does not return to `∞` and reaches its target `0`). It is a statement about the law of
the counterflow history alone; it is stated on the glued space, as `CfRegQStatement` is, because `Measure.map` of a
non-measurable map is a junk Dirac measure in this Mathlib. -/
def CfLineRegularQStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ a b θ₁ : ℝ,
    sleLambda κ - θ₁ * chiC κ ≤ b → sleLambda κ - π * chiC κ + θ₁ * chiC κ ≤ a →
    ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens)
      (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ)),
      ∀ {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
        IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ →
        P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂ →
        ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
          P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k →
          ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
              ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))),
            p.2.1 = ⊤ ∧ Continuous (Prop411Q.cfDrv p.2) ∧ Prop411Q.cfDrv p.2 0 = 0 ∧
              IsLoewnerTrace (Prop411Q.cfDrv p.2) (histLine p.2) ∧ (∀ u : ℝ, 0 < u → histLine p.2 u ≠ 0) ∧
              Tendsto (fun u => ‖histLine p.2 u‖) atTop atTop

/-- **Named input: the counterflow avoids the left part of the boundary of the complement of a flow-line prefix**
(Lemma 4.7 at angle `θ > π/2`, for the whole life of the counterflow; see the module docstring). Same setting as
`Cond44Ref.Prop51QStatement`. For each positive rational `t`, almost surely on the glued space, for the Loewner chart
`f_t` of the flow-line prefix `η(0, t]` (any continuous driver `W`, `W 0 = 0`, of which `η` is the trace), the
counterflow line never hits the left part of `∂(ℍ \ η(0, t])` (`Prop51Q.NoLeftPartHit`). -/
def CfAvoidLeftQStatement : Prop :=
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
          ∀ t : ℚ, 0 < t →
            ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
                ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))),
              ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 → IsLoewnerTrace W (fun s : ℝ => η p.1 s.toNNReal) →
                NoLeftPartHit W t (revLine p.2) p.2.1

/-! ### The flow line as a simple proper Loewner trace -/

/-- **A flow line from `0` of an admissible word is almost surely a simple proper Loewner trace of a continuous
driver.** -/
theorem ae_exists_isLoewnerTrace_of_isFlowLine {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {b : ℝ → ℝ} {J : Finset ℝ}
    {θ : ℝ}
    (hadm : Sec4.HasAdmissiblePartialSums κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0))
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hfl : IsFlowLine κ b J 0 θ P h η ζ) :
    ∀ᵐ ω ∂P, ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ IsLoewnerTrace W (fun s : ℝ => η ω s.toNNReal) ∧
      IsProperArc (fun s : ℝ => η ω s.toNNReal) := by
  have harc := ae_isProperArc_of_isFlowLine hκ hκ4 hadm hfl
  obtain ⟨h', 𝓕, W, VL, VR, B, -, hC, htr⟩ := hfl
  have hF := Theorem15.isOrderedForceWord_flowLine b J 0
  filter_upwards [ae_seedLine_of_admissible hκ hκ4 hF hadm hC.1, htr, hC.1.2.2.2.2, harc]
    with ω hω ht hp ha
  obtain ⟨hζ, -, -⟩ := hω
  have e : (fun t => η ω t - ((0 : ℝ) : ℂ)) = η ω := by
    funext t
    simp
  rw [e, hζ] at ht
  have hWc : ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := hp.2.2.2.1
  rw [hζ] at hWc
  have hWc' : Continuous fun t => W t ω :=
    continuousOn_univ.1 (hWc.mono fun t _ => show (t : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top)
  refine ⟨fun s : ℝ => W s.toNNReal ω, hWc'.comp continuous_real_toNNReal, ?_,
    isLoewnerTrace_of_isGeneratingTrace ht, ha⟩
  simpa using hp.1

/-! ### Proposition 5.1 in the chart `Q` -/

/-- **`Cond44Ref.Prop51QStatement` from the two counterflow inputs.** -/
theorem prop51QStatement_of_cfAvoidLeft (hreg : CfLineRegularQStatement.{u})
    (havoid : CfAvoidLeftQStatement.{u}) : Prop51QStatement.{u} := by
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
  have havG : ∀ᵐ p ∂(glueMeasure P k X hXm), ∀ t : ℚ, 0 < t →
      ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 → IsLoewnerTrace W (fun s : ℝ => η p.1 s.toNNReal) →
        NoLeftPartHit W t (revLine p.2) p.2.1 := by
    rw [ae_all_iff]
    intro t
    by_cases ht : 0 < t
    · filter_upwards [havoid κ hκ hκ4 a b θ₁ θ₂ h12 hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk t ht]
        with p hp
      exact fun _ => hp
    · exact Eventually.of_forall fun p h => absurd h ht
  filter_upwards [hfl', hregG, havG] with p hp1 hp2 hp3 s
  obtain ⟨W, hWc, hW0, hLT, hγ⟩ := hp1
  obtain ⟨hy, -, -, hβ, hne, htend⟩ := hp2
  have hp2 := isRegularCfLine_of hy hβ.2.1 hne htend
  unfold cfPts
  split_ifs with hs
  · rw [← arcRange_toNNReal]
    exact notMem_leftSideOf_of_noLeftPartHit hLT hγ hWc hW0 hp2.1 hp2.2
      (fun t ht => hp3 t ht W hWc hW0 hLT) ⟨by exact_mod_cast hs.1, hs.2⟩
  · exact fun h0 => lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h0.1.1)

end InteractingSLE.Sec5.Prop51Q
