/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfAvoidLeftQFree
import InteractingSLE.Spec.Sec5.Prop51GQNoContact
import InteractingSLE.Spec.Sec5.Carrier

/-!
# Proposition 5.1's forward route in the chart `Q` (the stopped flow line of ruling R64)

Packet PROVE-PROP51G, steps (1)–(2). Specification §5, Proposition 5.1 and its proof (`source/spec/p097-144.md`,
pp. 128–135), as used in Proposition 5.5 (p. 140) on the route of Theorem 1.2.

## The stopping convention (R64) and the bridge to `Cond44Ref.Prop51QStatement`

The only consumer of Proposition 5.1 on the route of Theorem 1.2 is `Cond44Ref.Prop51QStatement` (chart `Q`: the
field `h` on `ℍ` with data `−a | b`, its flow line `η = η_{θ₂}` from `0` to `∞`, the counterflow `η′` of
`h + (θ₁ − π/2)χ` from `∞`). A real Möbius map `Φ` with `Φ(0) = 0` and `Φ(∞) = −1 − q` (any `q > 0`, any position of
its pole on `(0, ∞)`) carries this configuration onto the strip chart `E` of Figure 5.1 in the frame
`α = θ₁ − π/2`, with relative angle `θ = θ₂ − θ₁ + π/2 > π/2` and the parameters
`a_F = a − αχ`, `b_F = b + αχ`, `a'_F = a_F + πχ`, `b'_F = b_F + πχ` (the data `−a` fill `(−1 − q, 0)` with no jump
at the left strip end `−1`, and the data right of `z₀` are `b + 2πχ`, the branch jump of `arg (Φ⁻¹)′` at the pole).
These parameters satisfy the standing bounds and (5.1) (`isFig51Bounds_qParams`, `eq51_qParams`). Under `Φ` the flow
line `η` (a proper arc from `0` to `∞`, `Cond44Ref.ae_isProperArc_of_isFlowLine`) becomes the strip flow line **up
to its first contact with the upper boundary**, and that first contact is its terminal point `z₀` itself (where the
counterflow starts): the consumer uses exactly the stopped segment of R64, and nothing after it. Two consequences:

* the forward route's regularity (`ForwardRegularityStatement`) and Lemma 5.4's upper clause are statements about
  the stopped segment, which in the chart `Q` is the proper arc `η`: its simplicity, interior values and transience
  are landed, and there is no upper boundary to avoid (step (2) is discharged by working in `Q`);
* the terminal point is always the junction `z₀`, so the eastern terminal access of R50 (Astra C) is not an
  exceptional event but the whole question: in `Q` it is the eastern end at `∞` of `ℍ ∖ R(K_s)`.

A transport `Q → E` of the coupling (`Prop51Forward.QStripTransportStatement`) would need the change of target of
the flow line from `∞_Q` to `Φ⁻¹(∞)`; no such Möbius transport of `IsFlowLine` is landed. The forward route is
therefore stated in the chart `Q` directly.

## The forward route in the chart `Q`

Fix a positive rational counterflow time `s`; `K = R(K_s)` (`cfHullQ`) is the counterflow hull, `D = ℍ ∖ K`, and
`Ψ = revChart w s` maps `D` onto `ℍ` with `0 ↦ 0` and the tip `η′(s) ↦ ∞`; the western side of `K` (the side facing
`ℝ₋`) and the western end of `∞` go to negative reals, `ℝ₋` to negative reals near `0`, `ℝ₊` to positive reals near
`0`, and the eastern side and the eastern end of `∞` to the remaining positive reals.

* `HitsEastPartAlong w s η F`: along `F`, while in `D`, `Ψ ∘ η` clusters at a positive real point (an approach to the
  eastern part of `∂D`, or to `ℝ₊`, which a proper arc never approaches at positive times);
* `FirstContactNotEast w s t η`: restarted at time `t` (in `D` if `t > 0`), `η` does not hit the eastern part of `∂D`
  at the end of its excursion in `D` (Lemma 5.4's barrier and the eastern junction of R50 / Astra C, in one statement);
* **`FwdNoWrapQStatement`** (deterministic; the planar topology of the no-wrap step, step (3)): if no excursion of a
  proper arc `η` in `D` that starts at a rational time ends in the eastern part, the tip `η′(s)` is not on the left of
  `η`;
* `GluedQ G Φ`: a property `Φ s η w` almost surely on the glued space of `Cond44Ref.Prop51QStatement`, at every
  positive rational `s`, for the angles in a regime `G`; `Prop51QOn G` is `Prop51QStatement` on that regime, and
  `prop51QOn_of_gluedQ` is the pathwise reduction;
* **`FwdFirstContactNotEastQOn G`** (the probabilistic input): `FirstContactNotEast` at every rational `s > 0`, `t ≥ 0`;
  it splits (`fwdFirstContactNotEastQOn_of_split`) into the **first exit** (`t = 0`, `FwdFirstExitQOn`: the
  cross-conditioning law `CrossCondTheta*` up to the first contact and Aux. lemma 22) and the **post-contact barrier**
  (`FwdPostContactQOn`: restarts after a contact with `K`, the retained comparison of Aux. 61–65);
* **`prop51QStatement_of_fwd`**, **`cfFirstContactQStatement_of_fwd`**: `Prop51QStatement` and Theorem 1.2's input
  `CfAvoidLeftQ.CfFirstContactQStatement` from the no-wrap topology, the forward input and the counterflow's
  regularity;
* **the regimes.** At and above the critical gap `θ₂ − θ₁ ≥ πκ/(4 − κ)` (`IsLargeGap`) the flow line never meets the
  hull (`FwdNoContactQStatement`) and the contact-free crosscut separation
  (`negInv_notMem_leftSideOf_of_noContact`, proved) replaces the no-wrap topology: **`prop51QOn_largeGap`**. Below it
  the first exit is a hit of the western side. **`prop51QStatement_of_regimes`** and
  **`prop51QStatement_of_partA_of_fwd`** assemble the two.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC fwdHull fwdMap)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.Prop51G

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique Cond44Ref Prop51Q CfAvoidLeftQ

/-! ### The chart-`Q` parameters in the strip chart `E` (ruling R64's bridge check) -/

section Params

variable {κ : ℝ}

/-- `λ′ = λ − πχ/2`, from (5.3). -/
theorem sleLambda_sixteen_div_eq' (hκ : 0 < κ) (hκ4 : κ < 4) :
    sleLambda (16 / κ) = sleLambda κ - π * chiC κ / 2 := by
  have h := sleLambda_sixteen_div_sub_div_chiC hκ hκ4
  have hχ : chiC κ ≠ 0 := (Sec4.chiC_pos hκ hκ4).ne'
  rw [div_eq_iff hχ] at h
  linarith

/-- **The standing bounds of Proposition 5.1 for the chart-`Q` configuration** of `Cond44Ref.Prop51QStatement`, in
the frame `α = θ₁ − π/2`: `a_F = a − αχ`, `b_F = b + αχ`, `a'_F = a_F + πχ`, `b'_F = b_F + πχ`. -/
theorem isFig51Bounds_qParams (hκ : 0 < κ) (hκ4 : κ < 4) {a b θ₁ θ₂ : ℝ} (h12 : θ₁ < θ₂)
    (hb : sleLambda κ - θ₁ * chiC κ ≤ b) (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a) :
    IsFig51Bounds κ (a - (θ₁ - π / 2) * chiC κ) (b + (θ₁ - π / 2) * chiC κ)
      (a - (θ₁ - π / 2) * chiC κ + π * chiC κ) (b + (θ₁ - π / 2) * chiC κ + π * chiC κ) := by
  have hχ := Sec4.chiC_pos hκ hκ4
  have hθ : θ₁ * chiC κ ≤ θ₂ * chiC κ := mul_le_mul_of_nonneg_right h12.le hχ.le
  have hl := sleLambda_sixteen_div_eq' hκ hκ4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hl, hθ]

/-- **Condition (5.1) for the chart-`Q` configuration**, at the relative angle `θ = θ₂ − θ₁ + π/2`. -/
theorem eq51_qParams (hκ : 0 < κ) (hκ4 : κ < 4) {a b θ₁ θ₂ : ℝ} (h12 : θ₁ < θ₂)
    (hb : sleLambda κ - θ₁ * chiC κ ≤ b) (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a) :
    Eq51 κ (a - (θ₁ - π / 2) * chiC κ) (b + (θ₁ - π / 2) * chiC κ) (θ₂ - θ₁ + π / 2) := by
  have hχ := Sec4.chiC_pos hκ hκ4
  have hθ : θ₁ * chiC κ ≤ θ₂ * chiC κ := mul_le_mul_of_nonneg_right h12.le hχ.le
  have hπ := Real.pi_pos
  constructor <;> nlinarith [hθ, mul_pos hπ hχ]

/-- The relative angle of the chart-`Q` configuration exceeds `π/2`. -/
theorem pi_div_two_lt_qAngle {θ₁ θ₂ : ℝ} (h12 : θ₁ < θ₂) : π / 2 < θ₂ - θ₁ + π / 2 := by linarith

end Params

/-! ### The eastern part of the boundary of `ℍ ∖ R(K_s)` -/

section Defs

/-- **The counterflow hull `R(K_s)` in the chart `Q`** (`R z = −1/z`; `K_s = fwdHull w s` in the counterflow's own
chart). -/
def cfHullQ (w : ℝ → ℝ) (s : ℝ) : Set ℂ := negInv '' fwdHull w s

/-- **`η` hits the eastern part of `∂(ℍ ∖ R(K_s))` along `F`**: along `F`, at the times when `η` is in `ℍ ∖ R(K_s)`,
the chart `Ψ = revChart w s` of `η` clusters at a positive real point. In the chart `Ψ` the positive reals are the
images of `ℝ₊`, of the eastern end of `∞` and of the eastern side of the hull (the side facing `ℝ₊`). -/
def HitsEastPartAlong (w : ℝ → ℝ) (s : ℝ) (η : ℝ → ℂ) (F : Filter ℝ) : Prop :=
  ∃ x : ℝ, 0 < x ∧ MapClusterPt (x : ℂ) (F ⊓ 𝓟 {u | η u ∈ H \ cfHullQ w s}) fun u => revChart w s (η u)

/-- Hitting the eastern part is monotone in the filter. -/
theorem HitsEastPartAlong.mono {w : ℝ → ℝ} {s : ℝ} {η : ℝ → ℂ} {F G : Filter ℝ}
    (h : HitsEastPartAlong w s η F) (hFG : F ≤ G) : HitsEastPartAlong w s η G := by
  obtain ⟨x, hx, hcl⟩ := h
  exact ⟨x, hx, hcl.mono (inf_le_inf_right _ hFG)⟩

/-- **The excursion of `η` in `ℍ ∖ R(K_s)` running at the restart time `t` does not end in the eastern part**: if
`η(t) ∈ ℍ ∖ R(K_s)` (when `t > 0`) and `η` stays in `ℍ ∖ R(K_s)` on `(t, u₀)`, then `η` does not hit the eastern part
along `u ↑ u₀`, `u ∈ (t, u₀)`; and if `η` stays in `ℍ ∖ R(K_s)` after `t`, it does not hit the eastern part as
`u → ∞` (the eastern end of `∞`, R50 / Astra C). -/
def FirstContactNotEast (w : ℝ → ℝ) (s t : ℝ) (η : ℝ → ℂ) : Prop :=
  (0 < t → η t ∈ H \ cfHullQ w s) →
    (∀ u₀, t < u₀ → (∀ v ∈ Ioo t u₀, η v ∈ H \ cfHullQ w s) →
        ¬ HitsEastPartAlong w s η (𝓝[Ioo t u₀] u₀)) ∧
      ((∀ v ∈ Ioi t, η v ∈ H \ cfHullQ w s) → ¬ HitsEastPartAlong w s η atTop)

/-- **The restart condition after a contact**: `FirstContactNotEast` at `t`, required only when `η` has met
`R(K_s)` at some time in `(0, t]`. -/
def PostContactNotEast (w : ℝ → ℝ) (s t : ℝ) (η : ℝ → ℂ) : Prop :=
  (∃ v ∈ Ioc 0 t, η v ∉ H \ cfHullQ w s) → FirstContactNotEast w s t η

/-- **The first exit and the post-contact restarts give every restart** (deterministic): if `η` has not met
`R(K_s)` on `(0, t]`, its excursion running at `t` is the one started at `0`. -/
theorem firstContactNotEast_of_split {w : ℝ → ℝ} {s t : ℝ} {η : ℝ → ℂ} (ht : 0 ≤ t)
    (h0 : FirstContactNotEast w s 0 η) (hpost : PostContactNotEast w s t η) : FirstContactNotEast w s t η := by
  by_cases hc : ∃ v ∈ Ioc 0 t, η v ∉ H \ cfHullQ w s
  · exact hpost hc
  push Not at hc
  obtain ⟨h0a, h0b⟩ := h0 fun h => absurd h (lt_irrefl 0)
  intro _
  refine ⟨fun u₀ htu hD => ?_, fun hD => ?_⟩
  · have hD0 : ∀ v ∈ Ioo 0 u₀, η v ∈ H \ cfHullQ w s := fun v hv => by
      rcases le_or_gt v t with hvt | hvt
      · exact hc v ⟨hv.1, hvt⟩
      · exact hD v ⟨hvt, hv.2⟩
    exact fun hit => h0a u₀ (ht.trans_lt htu) hD0
      (hit.mono (nhdsWithin_mono _ (Ioo_subset_Ioo_left ht)))
  · refine h0b fun v hv => ?_
    rcases le_or_gt v t with hvt | hvt
    · exact hc v ⟨hv, hvt⟩
    · exact hD v hvt

end Defs

/-! ### The deterministic no-wrap statement (step (3)) -/

/-- **The no-wrap step of Proposition 5.1 in the chart `Q`** (deterministic; planar topology, PROVE-PROP51G step
(3)). Let `η` be a proper arc from `0` (the flow line), `β` a Loewner trace of a continuous driver `w` from `0` that
never returns to `0` (the counterflow `η′ = R ∘ β` from `∞`), and `s > 0`. If, for every rational restart time
`t ≥ 0`, the excursion of `η` in `ℍ ∖ R(K_s)` running at `t` does not end in the eastern part of the boundary
(`FirstContactNotEast`), then the counterflow tip `η′(s) = R(β(s))` is not on the left side of `η`. This is the
statement "`η′(τ′)` to the left of `η` forces `η` to wrap around the tip and reach the right side of the revealed
counterflow or its eastern junction" of the proof of Proposition 5.1 (p. 135, with R45, R50). -/
def FwdNoWrapQStatement : Prop :=
  ∀ (η : ℝ → ℂ) (w : ℝ → ℝ) (β : ℝ → ℂ) (s : ℝ), IsProperArc η → Continuous w → w 0 = 0 →
    IsLoewnerTrace w β → 0 < s → (∀ v : ℝ, 0 < v → β v ≠ 0) →
      (∀ t : ℚ, 0 ≤ t → FirstContactNotEast w s t η) → negInv (β s) ∉ leftSideOf (arcRange η)


/-! ### The glued setting of `Cond44Ref.Prop51QStatement`, restricted to a regime of angles -/

section Setting

/-- **The large-gap regime** `θ₂ − θ₁ ≥ πκ/(4 − κ)`: the image word of the flow line in the counterflow chart has
left-span weight `(3/2 + θ/π)(κ/2 − 2) ≤ κ/2 − 4` (`θ = θ₂ − θ₁ + π/2`), so Aux. lemma 22's span is not hit and the
flow line never meets the counterflow (the critical angle of Theorem 1.5). Below it (`¬ IsLargeGap`) Zhan's charge
condition `|κ − 6 − 2 W_L| < 2` holds and the first exit is a hit of the western side. -/
def IsLargeGap (κ θ₁ θ₂ : ℝ) : Prop := π * κ / (4 - κ) ≤ θ₂ - θ₁

/-- **Proposition 5.1 in the chart `Q` on a regime `G` of `(κ, θ₁, θ₂)`**: `Cond44Ref.Prop51QStatement` with the
extra hypothesis `G κ θ₁ θ₂`. -/
def Prop51QOn (G : ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ a b θ₁ θ₂ : ℝ, θ₁ < θ₂ → G κ θ₁ θ₂ →
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
          ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
              ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))),
            ∀ s : ℚ, cfPts p.2 s ∉ leftSideOf (range (η p.1))

/-- `Cond44Ref.Prop51QStatement` from its two regimes. -/
theorem prop51QStatement_of_on (G : ℝ → ℝ → ℝ → Prop) (h₁ : Prop51QOn.{u} G)
    (h₂ : Prop51QOn.{u} fun κ θ₁ θ₂ => ¬ G κ θ₁ θ₂) : Prop51QStatement.{u} := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂' W₂ ζ₂ hcf hlaw k _ hk
  by_cases hG : G κ θ₁ θ₂
  · exact h₁ κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂' W₂ ζ₂ hcf hlaw k hk
  · exact h₂ κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂' W₂ ζ₂ hcf hlaw k hk

/-- **A property `Φ s η w` of the flow line `η` and the counterflow driver `w` at the counterflow time `s`, almost
surely on the glued space of `Cond44Ref.Prop51QStatement`, for every positive rational `s`, on the regime `G`.** -/
def GluedQ (G : ℝ → ℝ → ℝ → Prop) (Φ : ℝ → (ℝ → ℂ) → (ℝ → ℝ) → Prop) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ a b θ₁ θ₂ : ℝ, θ₁ < θ₂ → G κ θ₁ θ₂ →
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
          ∀ s : ℚ, 0 < s →
            ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
                ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))),
              Φ s (fun u : ℝ => η p.1 u.toNNReal) (Prop411Q.cfDrv p.2)

/-- `GluedQ` is monotone in the property. -/
theorem GluedQ.mono {G : ℝ → ℝ → ℝ → Prop} {Φ Φ' : ℝ → (ℝ → ℂ) → (ℝ → ℝ) → Prop} (h : GluedQ.{u} G Φ)
    (hΦ : ∀ s η w, Φ s η w → Φ' s η w) : GluedQ.{u} G Φ' := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P _ hf η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  filter_upwards [h κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P hf η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs] with p hp
  exact hΦ _ _ _ hp

/-- Two `GluedQ` properties hold together. -/
theorem GluedQ.and {G : ℝ → ℝ → ℝ → Prop} {Φ Φ' : ℝ → (ℝ → ℂ) → (ℝ → ℝ) → Prop} (h : GluedQ.{u} G Φ)
    (h' : GluedQ.{u} G Φ') : GluedQ.{u} G fun s η w => Φ s η w ∧ Φ' s η w := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P _ hf η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  filter_upwards [h κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P hf η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs,
    h' κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P hf η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs] with p hp hp'
  exact ⟨hp, hp'⟩

/-- **The pathwise reduction on a regime**: if `Φ s η w` at every positive rational `s` forces the counterflow tip at
`s` off the left side of the flow line, for every proper arc `η` and every regular counterflow (continuous driver from
`0`, Loewner trace, no return to `0`), then `GluedQ G Φ` gives Proposition 5.1 in the chart `Q` on `G`. -/
theorem prop51QOn_of_gluedQ {G : ℝ → ℝ → ℝ → Prop} {Φ : ℝ → (ℝ → ℂ) → (ℝ → ℝ) → Prop}
    (hreg : CfLineRegularQStatement.{u}) (hΦ : GluedQ.{u} G Φ)
    (hdet : ∀ (η : ℝ → ℂ) (w : ℝ → ℝ) (β : ℝ → ℂ) (s : ℝ), IsProperArc η → Continuous w → w 0 = 0 →
      IsLoewnerTrace w β → 0 < s → (∀ v : ℝ, 0 < v → β v ≠ 0) → Φ s η w →
        negInv (β s) ∉ leftSideOf (arcRange η)) : Prop51QOn.{u} G := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
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
  -- the property at every positive rational time
  have hfG : ∀ᵐ p ∂(glueMeasure P k X hXm), ∀ s : ℚ, 0 < s →
      Φ s (fun u : ℝ => η p.1 u.toNNReal) (Prop411Q.cfDrv p.2) := by
    rw [ae_all_iff]
    intro s
    by_cases hs : 0 < s
    · filter_upwards [hΦ κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs] with p hp
      exact fun _ => hp
    · exact Eventually.of_forall fun p h => absurd h hs
  filter_upwards [hfl', hregG, hfG] with p hp1 hp2 hp3 s
  obtain ⟨-, -, -, -, hγ⟩ := hp1
  obtain ⟨-, hwc, hw0, hβ, hne, -⟩ := hp2
  unfold cfPts
  split_ifs with hs
  · rw [← arcRange_toNNReal]
    exact hdet _ _ _ _ hγ hwc hw0 hβ (by exact_mod_cast hs.1) hne (hp3 s hs.1)
  · exact fun h0 => lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h0.1.1)

end Setting

/-! ### The probabilistic inputs -/

section Inputs

/-- **The forward restart input** (Lemma 5.4's barrier and the eastern junction, in the chart `Q`) on the regime `G`:
for positive rational `s` (a counterflow time) and nonnegative rational `t` (a restart time of the flow line), almost
surely on the glued space the excursion of the flow line `η` in `ℍ ∖ R(K_s)` running at `t` does not end in the
eastern part of the boundary (`FirstContactNotEast`, in the chart of the counterflow's history). -/
def FwdFirstContactNotEastQOn (G : ℝ → ℝ → ℝ → Prop) : Prop :=
  GluedQ.{u} G fun s η w => ∀ t : ℚ, 0 ≤ t → FirstContactNotEast w s t η

/-- **The forward restart input** on all angles. -/
abbrev FwdFirstContactNotEastQStatement : Prop := FwdFirstContactNotEastQOn.{u} fun _ _ _ => True

/-- **The first exit** (`t = 0`) on the regime `G`: almost surely the flow line's first excursion in `ℍ ∖ R(K_s)`
(from `0`) does not end in the eastern part (the cross-conditioning law `CrossCondTheta*` at the relative angle
`θ₂ − θ₁ + π/2`, up to the first contact, with Aux. lemma 22 in the counterflow chart). -/
def FwdFirstExitQOn (G : ℝ → ℝ → ℝ → Prop) : Prop :=
  GluedQ.{u} G fun s η w => FirstContactNotEast w s 0 η

/-- **The post-contact barrier** on the regime `G` (Lemma 5.4 after a contact with the revealed counterflow, with the
eastern junction; the retained comparison of Aux. 61–65): for positive rationals `s` and `t`, almost surely, if the
flow line has met `R(K_s)` before `t`, its excursion in `ℍ ∖ R(K_s)` running at `t` does not end in the eastern part.
-/
def FwdPostContactQOn (G : ℝ → ℝ → ℝ → Prop) : Prop :=
  GluedQ.{u} G fun s η w => ∀ t : ℚ, 0 < t → PostContactNotEast w s t η

/-- **The forward restart input from the first exit and the post-contact barrier.** -/
theorem fwdFirstContactNotEastQOn_of_split {G : ℝ → ℝ → ℝ → Prop} (h0 : FwdFirstExitQOn.{u} G)
    (hpost : FwdPostContactQOn.{u} G) : FwdFirstContactNotEastQOn.{u} G := by
  refine (GluedQ.and h0 hpost).mono fun s η w hp t ht => ?_
  rcases eq_or_lt_of_le ht with rfl | ht'
  · simpa using hp.1
  · exact firstContactNotEast_of_split (by exact_mod_cast ht) hp.1 (hp.2 t ht')

/-- **No contact in the large-gap regime**: for `θ₂ − θ₁ ≥ πκ/(4 − κ)` and every positive rational `s`, almost surely
the flow line never meets the counterflow hull `R(K_s)` and, in the counterflow chart, tends to a negative real point
(it leaves `ℍ ∖ R(K_s)` through the western end of `∞`; Aux. lemma 22's left-end case for the image word, whose
left-span weight is at most `κ/2 − 4`). -/
def FwdNoContactQStatement : Prop :=
  GluedQ.{u} IsLargeGap fun s η w => (∀ t : ℝ, 0 < t → η t ∉ cfHullQ w s) ∧
    ∃ x₀ : ℝ, x₀ < 0 ∧ Tendsto (fun t => revChart w s (η t)) atTop (𝓝 (x₀ : ℂ))

end Inputs

/-! ### Proposition 5.1 in the chart `Q` and Theorem 1.2's input -/

section Wiring

/-- **Proposition 5.1 in the chart `Q` on a regime, from the forward route**: the counterflow's regularity, the
deterministic no-wrap step and the forward restart input on that regime. -/
theorem prop51QOn_of_fwd {G : ℝ → ℝ → ℝ → Prop} (hreg : CfLineRegularQStatement.{u})
    (htopo : FwdNoWrapQStatement) (hfwd : FwdFirstContactNotEastQOn.{u} G) : Prop51QOn.{u} G :=
  prop51QOn_of_gluedQ hreg hfwd fun η w β s hη hw hw0 hβ hs hne hΦ =>
    htopo η w β s hη hw hw0 hβ hs hne hΦ

/-- **`Cond44Ref.Prop51QStatement` from the forward route**: the counterflow's regularity, the deterministic no-wrap
step and the forward restart input. -/
theorem prop51QStatement_of_fwd (hreg : CfLineRegularQStatement.{u}) (htopo : FwdNoWrapQStatement)
    (hfwd : FwdFirstContactNotEastQStatement.{u}) : Prop51QStatement.{u} := by
  have h := prop51QOn_of_fwd hreg htopo hfwd
  refine prop51QStatement_of_on (fun _ _ _ => True) h ?_
  intro κ _ _ _ _ _ _ _ hG
  exact absurd trivial hG

/-- **Proposition 5.1 in the chart `Q` in the large-gap regime, without the no-wrap topology**: no contact with the
counterflow hull, and the contact-free crosscut separation (`negInv_notMem_leftSideOf_of_noContact`). -/
theorem prop51QOn_largeGap (hreg : CfLineRegularQStatement.{u}) (hnc : FwdNoContactQStatement.{u}) :
    Prop51QOn.{u} IsLargeGap :=
  prop51QOn_of_gluedQ hreg hnc fun _ _ _ _ hη hw hw0 hβ hs _ hΦ =>
    negInv_notMem_leftSideOf_of_noContact hη hβ hw hw0 hs.le hΦ.2.choose_spec.1 hΦ.1
      hΦ.2.choose_spec.2

/-- **`Cond44Ref.Prop51QStatement` by regimes**: the no-wrap topology and the forward restart input are needed only
below the critical gap; at and above it, no contact suffices. -/
theorem prop51QStatement_of_regimes (hreg : CfLineRegularQStatement.{u}) (htopo : FwdNoWrapQStatement)
    (hsmall : FwdFirstContactNotEastQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂)
    (hnc : FwdNoContactQStatement.{u}) : Prop51QStatement.{u} :=
  prop51QStatement_of_on IsLargeGap (prop51QOn_largeGap hreg hnc) (prop51QOn_of_fwd hreg htopo hsmall)

/-- **Theorem 1.2's input `CfAvoidLeftQ.CfFirstContactQStatement` from the forward route** (through
`cfFirstContactQStatement_of_prop51Q`). -/
theorem cfFirstContactQStatement_of_fwd (hreg : CfLineRegularQStatement.{u}) (htopo : FwdNoWrapQStatement)
    (hfwd : FwdFirstContactNotEastQStatement.{u}) : CfFirstContactQStatement.{u} :=
  cfFirstContactQStatement_of_prop51Q hreg (prop51QStatement_of_fwd hreg htopo hfwd)

/-- **`Cond44Ref.Prop51QStatement` from Zhan's Part A inputs at `16/κ` and the forward route, by regimes** (the
drop-in for `CfAvoidLeftQ.prop51QStatement_of_partA_of_cfFirstContact` on the route of Theorem 1.2): below the
critical gap the first exit, the post-contact barrier and the no-wrap topology; at and above it, no contact. -/
theorem prop51QStatement_of_partA_of_fwd (hA : PartAInputsSixteenDiv) (htopo : FwdNoWrapQStatement)
    (h0 : FwdFirstExitQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂)
    (hpost : FwdPostContactQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂)
    (hnc : FwdNoContactQStatement.{u}) : Prop51QStatement.{u} :=
  prop51QStatement_of_regimes (CfLineRegQ.cfLineRegularQStatement_of_partA hA) htopo
    (fwdFirstContactNotEastQOn_of_split h0 hpost) hnc

end Wiring

end InteractingSLE.Sec5.Prop51G
