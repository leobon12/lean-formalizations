/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StoppedExtendProofDet
import InteractingSLE.Spec.Supplement.FlowLocal
import InteractingSLE.Spec.Exist.StagedKernel
import InteractingSLE.Spec.Sec7.Lemma75Bridge
import InteractingSLE.Spec.Exist.FlowField

/-!
# Flow-line locality (Lemma G3's path half) from Aux. lemma 54 for general words

Packet PROVE-DOMAINMARKOV9 (orchestrator note: derive `RLC.FlowLocalityStatement` from the general stopped extension
and Theorem 1.2's determination, or state precisely what is missing). Source: Aux. lemma 97's proof (pp. 326–327) as
used in Lemma G3 (pp. 492–493): "a stopped flow-line coupling with these laws extends to a full one (Aux. 54) so that
Theorem 1.2 identifies its path with the field-determined reference path".

PROVE-RLC-E split the source argument into (L1) the identification of the stopped coupling under the changed law,
(L2) Aux. lemma 54 for that stop, (L3) the assembly by Theorem 1.2. This file proves (L3):

* `flowDetCode h12p hκ b jumps x θ`: the field-determined angle-`θ` flow line of the data `(b, jumps)` from `x` (Theorem
  1.2 in its word-measurable form, `Theorem12ParamStatement`, read at the flow-line word and the translated field), as a
  path code; **`isFlowDet_flowDetCode`**: every flow line of these data matches it (determination; any data, any
  universe);
* `FlowLineStopIdentStatement` (**named input (L1)**): in the setting of `FlowLocalityStatement`, the flow line `Γ` of
  `H₀` stopped at its exit time from the buffer is, under `Q`, a stopped flow line of `Ĥ` with the data `bR`;
* `stoppedAgree_of_matches` (pathwise): two paths, each matching on its own stopped interval the code of the other's
  full flow line, agree up to and including a common exit time;
* **`flowLocalityStatement_of_stopIdent`**: `RLC.FlowLocalityStatement` from (L1), Aux. lemma 54 for general words in
  kernel form ((L2), `StoppedHullExtendKStatement`), and Theorems 1.2 (word-measurable) and 1.3. (L1) is applied twice,
  with the roles of `(H₀, Q₀, b)` and `(Ĥ, Q, bR)` exchanged (the hypotheses are symmetric); this gives the equality of
  the two exit times without any lifetime clause in (L1).

**R43/R48.** Theorems 1.2–1.3 are hypotheses: these results serve Theorem 1.5 (Lemma G3) only.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

namespace StoppedExtend

open Sec2.Assembly Exist.Staged

/-! ### The field-determined flow line of fixed data -/

section Det

variable (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (b : ℝ → ℝ) (jumps : Finset ℝ) (x θ : ℝ)

/-- **The field-determined flow-line trace** of the data `(b, jumps)` from `x` at the angle `θ`: Theorem 1.2's
determination map (word-measurable form) at the flow-line word, applied to the translated field
`h(· + x) + θχ` (lifetime, and the trace frozen after the lifetime). -/
def flowDetTrace (f : DistOn upperHalfPlaneOpens) : ℝ≥0∞ × (ℝ≥0 → ℂ) :=
  paramΦ h12p hκ (flowLineNL b jumps x) (flowLineNR b jumps x)
    (((flowLineXL b jumps x, flowLineXR b jumps x), (flowLineRhoL κ b jumps x θ, flowLineRhoR κ b jumps x θ)),
      Exist.flowField x (θ * QuantumZipper.chiC κ) f)

/-- **The field-determined flow line as a path code**: `x +` the determined trace, with the determined lifetime. -/
def flowDetCode (f : DistOn upperHalfPlaneOpens) : (PCode × PCode) × ℝ≥0∞ :=
  encPath (fun t => (x : ℂ) + (flowDetTrace h12p hκ b jumps x θ f).2 t) (flowDetTrace h12p hκ b jumps x θ f).1

theorem measurable_flowDetTrace : Measurable (flowDetTrace h12p hκ b jumps x θ) :=
  (measurable_paramΦ h12p hκ _ _).comp (measurable_const.prodMk (Exist.measurable_flowField x _))

theorem measurable_flowDetCode : Measurable (flowDetCode h12p hκ b jumps x θ) := by
  have hT := measurable_flowDetTrace h12p hκ b jumps x θ
  exact measurable_encPath (fun t => measurable_const.add ((measurable_pi_apply t).comp (measurable_snd.comp hT)))
    (measurable_fst.comp hT)

/-- **Determination for fixed data**: every flow line of `(b, jumps)` from `x` at the angle `θ` (on any probability
space of universe `u`) almost surely matches the field-determined code (Theorem 1.2, word-measurable form). -/
theorem isFlowDet_flowDetCode : IsFlowDet.{u} κ b jumps x θ (flowDetCode h12p hκ b jumps x θ) := by
  intro Ω _ Q _ h η ζ hfl
  obtain ⟨h', 𝓕, W, VL, VR, B, htr, hC, hgen⟩ := hfl
  have hh' : h' = fun ω => Exist.flowField x (θ * QuantumZipper.chiC κ) (h ω) :=
    funext fun ω => Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htr ω)
  subst hh'
  have hF := Theorem15.isOrderedForceWord_flowLine b jumps x
  have hΦ := (h12p κ hκ _ _).choose_spec.2 _ _ _ _ hF hC
  filter_upwards [hΦ, hgen] with ω hΦω hgω
  have h1 : (flowDetTrace h12p hκ b jumps x θ (h ω)).1 = ζ ω := hΦω.1
  have h2 : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → (flowDetTrace h12p hκ b jumps x θ (h ω)).2 t = η ω t - x := by
    intro t ht
    refine (hΦω.2 _ hgω t).trans ?_
    rw [min_eq_left ht, ENNReal.toNNReal_coe]
  have hcont : ContinuousOn (fun t => (x : ℂ) + (flowDetTrace h12p hκ b jumps x θ (h ω)).2 t)
      {t | (t : ℝ≥0∞) ≤ (flowDetTrace h12p hκ b jumps x θ (h ω)).1} := by
    rw [h1]
    have hc0 : ContinuousOn (fun t : ℝ≥0 => (x : ℂ) + (η ω t - x)) {t | (t : ℝ≥0∞) ≤ ζ ω} :=
      continuousOn_const.add hgω.2.1
    refine hc0.congr fun t ht => ?_
    simp only [h2 t ht]
  refine ⟨h1.symm, fun t ht => ?_⟩
  rw [flowDetCode, decPath_encPath hcont (h1 ▸ ht), h2 t ht]
  ring

end Det

/-! ### (L1): the stopped flow line under the changed law -/

/-- **Named input (L1): the identification of the stopped flow line under the changed law** (Aux. lemma 97's proof,
pp. 326–327, as used in Lemma G3, pp. 492–493; PROVE-RLC-E's (L1): the weighted conditional mean is the reference
canonical mean off the stopped hull, Girsanov for the driver, uniqueness of the integrated driving equations up to the
stop). In the setting of `RLC.FlowLocalityStatement` (data `b`, `bR` agreeing on `O`; fields `H₀` under `Q₀` and `Ĥ`
under `Q ≈ Q₀` agreeing near `N ⊇ closure V`), the angle-`θ` flow line `Γ` of `H₀` from `y`, stopped at its exit time
from the buffer `V`, is under `Q` a stopped flow line of `Ĥ` with the data `bR` (`IsStoppedFlowLine`: a coupling
through the stop with the flow-line word of `bR`, whose driver has `Γ − y` as generating trace through the stop). -/
def FlowLineStopIdentStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b bR : ℝ → ℝ) (J Ĵ : Finset ℝ), IsPiecewiseConstantBoundaryData b J →
    IsPiecewiseConstantBoundaryData bR Ĵ → ∀ O : Set ℝ, IsOpen O → (∀ x ∈ O, b x = bR x) →
    ∀ N : Set ℂ, IsOpen N → (∀ z ∈ N, z.im = 0 → z.re ∈ O) →
    ∀ V : Set ℂ, IsOpen V → Bornology.IsBounded V → closure V ⊆ N → ∀ y θ : ℝ,
    ∀ {S : Type u} [MeasurableSpace S] (Q₀ Q : Measure S) [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q],
      Q₀ ≪ Q → Q ≪ Q₀ →
    ∀ (H₀ Ĥ : S → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q₀ H₀ b J →
      IsGFFWithBoundaryData Q Ĥ bR Ĵ →
      (∀ (x : S) (φ : TestOn upperHalfPlaneOpens), tsupport φ ⊆ N → Ĥ x φ = H₀ x φ) →
    ∀ (Γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞), IsFlowLine κ b J y θ Q₀ H₀ Γ U →
      IsStoppedFlowLine κ bR Ĵ y θ Q Ĥ Γ fun x => RLC.exitTime V (Γ x) (U x)

/-! ### The assembly -/

/-- **Two crosswise matches give agreement up to the common exit time** (pathwise). If `Γ`, stopped at its exit time
`e_Γ` from `V`, matches the code `p` of `α`'s full flow line, and `α`, stopped at its exit time `e_α`, matches the code
`q` of `Γ`'s full flow line, then `e_Γ = e_α` and the paths agree on `[0, e_Γ]`. If `e_Γ < e_α`: either `U < e_α`,
impossible since `e_α ≤ q.2 = U`; or `Γ` is outside `V` at some `s < e_α`, where `α s = Γ s`, so `e_α ≤ s`. -/
theorem stoppedAgree_of_matches {V : Set ℂ} {Γ α : ℝ≥0 → ℂ} {U ζ : ℝ≥0∞} {p q : (PCode × PCode) × ℝ≥0∞}
    (h1 : IsStopMatch p Γ (RLC.exitTime V Γ U)) (h2 : IsCodeMatch p α ζ)
    (h3 : IsStopMatch q α (RLC.exitTime V α ζ)) (h4 : IsCodeMatch q Γ U) :
    RLC.StoppedAgree V Γ U α ζ := by
  -- `e₁ < e₂` is impossible when the first path matches the second's code on `[0, e₁]` and conversely
  have key : ∀ {Γ α : ℝ≥0 → ℂ} {U ζ : ℝ≥0∞} {q : (PCode × PCode) × ℝ≥0∞},
      IsStopMatch q α (RLC.exitTime V α ζ) → IsCodeMatch q Γ U →
      ¬ RLC.exitTime V Γ U < RLC.exitTime V α ζ := by
    intro Γ α U ζ q h3 h4 hlt
    have heα : RLC.exitTime V α ζ ≤ U := h4.1 ▸ h3.1
    have hag : ∀ s : ℝ≥0, (s : ℝ≥0∞) < RLC.exitTime V α ζ → α s = Γ s := fun s hs =>
      (h3.2 s hs.le).trans (h4.2 s (hs.le.trans heα)).symm
    rcases min_lt_iff.1 hlt with hU | hX
    · exact absurd (heα.trans_lt hU) (lt_irrefl _)
    · obtain ⟨s, hs⟩ := iInf_lt_iff.1 hX
      obtain ⟨hsV, hslt⟩ := iInf_lt_iff.1 hs
      have hαs : α s ∉ V := by rw [hag s hslt]; exact hsV
      have hle : RLC.exitTime V α ζ ≤ (s : ℝ≥0∞) :=
        (min_le_right _ _).trans (iInf₂_le (f := fun (s : ℝ≥0) (_ : α s ∉ V) => (s : ℝ≥0∞)) s hαs)
      exact absurd (hle.trans_lt hslt) (lt_irrefl _)
  have heq : RLC.exitTime V Γ U = RLC.exitTime V α ζ :=
    le_antisymm (not_lt.1 (key h1 h2)) (not_lt.1 (key h3 h4))
  refine ⟨heq, fun s hs => ?_⟩
  exact (h1.2 s hs).trans (h2.2 s (hs.trans (h2.1 ▸ h1.1))).symm

/-- **Flow-line locality (Lemma G3's path half) from (L1), Aux. lemma 54 for general words and Theorems 1.2–1.3.**
`Γ`, stopped at its exit from `V`, is a stopped flow line of `Ĥ` under `Q` (L1), hence (Aux. lemma 54, Theorem 1.3)
matches on that interval the field-determined code of `Ĥ`'s data, which `α` matches in full (Theorem 1.2); exchanging
the roles gives the converse match; `stoppedAgree_of_matches` concludes (the `Q`-almost sure statements pass to `Q₀`
by `Q₀ ≪ Q`). -/
theorem flowLocalityStatement_of_stopIdent (hL1 : FlowLineStopIdentStatement.{u})
    (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → StoppedHullExtendKStatement.{u} κ) (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : RLC.FlowLocalityStatement.{u} := by
  intro κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN y θ S _ Q₀ Q _ _ hQ₀Q hQQ₀ H₀ Ĥ hH₀ hĤ hagr
    Γ α U ζ hΓ hα
  have hs1 := hL1 κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN y θ Q₀ Q hQ₀Q hQQ₀ H₀ Ĥ hH₀ hĤ hagr Γ U hΓ
  have hs2 := hL1 κ hκ hκ4 bR b Ĵ J hbR hb O hO (fun z hz => (hbO z hz).symm) N hN hNO V hV hVb hVN y θ Q Q₀
    hQQ₀ hQ₀Q Ĥ H₀ hĤ hH₀ (fun z φ hφ => (hagr z φ hφ).symm) α ζ hα
  have m1 := hs1.ae_stopMatch_of_extendK (hext κ hκ hκ4) h13 hκ (isFlowDet_flowDetCode h12p hκ bR Ĵ y θ)
  have c1 := isFlowDet_flowDetCode h12p hκ bR Ĵ y θ Q Ĥ α ζ hα
  have m2 := hs2.ae_stopMatch_of_extendK (hext κ hκ hκ4) h13 hκ (isFlowDet_flowDetCode h12p hκ b J y θ)
  have c2 := isFlowDet_flowDetCode h12p hκ b J y θ Q₀ H₀ Γ U hΓ
  filter_upwards [hQ₀Q.ae_le m1, hQ₀Q.ae_le c1, m2, c2] with z e1 e2 e3 e4
  exact stoppedAgree_of_matches e1 e2 e3 e4

end StoppedExtend

end Restart

end InteractingSLE
