/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedKCandRep
import InteractingSLE.Spec.Sec7.Aux122DisintEvol
import InteractingSLE.Spec.Sec2.Assembly2Stage

/-!
# Prop 5.9's killed law from a stopped representation of the piece (disintegration over the past)

Packet PROVE-STAGEDK-CAND (ruling R78). PROVE-STAGED8's bridge `isStageLawFarK_of_condLaw` needs a traced evolution
representing the piece's law under almost every regular conditional law given the past `𝓠`. This file produces it
from an **unconditional** statement on the space of the piece:

* `IsStoppedRepPath`, **`IsStoppedRep`**: a filtration `𝓕` with `𝓠 ≤ 𝓕 0` and a Brownian motion `B'` of `𝓕`, and
  processes adapted before the piece's lifetime `ζ`, which almost surely on the stage event form a local integrated
  path of the start's word before `ζ` (random start, `𝓠`-measurable), killed at the first far contact `ζ`
  continuously and traced up to it, and agree with the piece before `ζ` (Aux. lemma 122's form, p. 391, stopped at the
  first far contact);
* **`IsStoppedRep.ae_isSLEEvolutionUpTo`**: disintegration over `𝓠` (Aux. lemma 122, the landed
  `Aux122Disint.DisintSetting` machinery, for local paths): under almost every conditional law the modified processes
  form a local integrated evolution of the deterministic word `y ω₀`;
* **`IsStoppedRep.isStageLawFarK`**: the per-candidate killed law `IsStageLawFarK` (both clauses), through
  `hasKilledRep_of_isSLEEvolutionUpTo` (the continuation) and `isStageLawFarK_of_condLaw`.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedKCand

open Prop59Stage Prop59Nodes StagedKill Sec7.Aux122Disint

/-! ### The stopped representation -/

section Def

variable {nL nR : ℕ}

/-- **The pathwise part of a stopped representation** at one sample: the start `y₀` is an ordered strict word,
`(w', v', b')` is a local integrated path of its word before `τ`, killed at its first far contact `τ` continuously and
traced up to it, and the piece `(w, v, b)` agrees with it before `τ` and at time `0`. -/
structure IsStoppedRepPath (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (iL : Fin nL) (iR : Fin nR)
    (y₀ : Start nL nR) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ) (τ : ℝ≥0∞)
    (w' : ℝ≥0 → ℝ) (vL' : Fin nL → ℝ≥0 → ℝ) (vR' : Fin nR → ℝ≥0 → ℝ) (b' : ℝ≥0 → ℝ) : Prop where
  ordered : IsOrderedForceWord y₀.2.1 y₀.2.2
  anti : StrictAnti y₀.2.1
  mono : StrictMono y₀.2.2
  path : Sec2.IsSLEPathUpTo κ y₀.2.1 y₀.2.2 ρL ρR w' vL' vR' b' τ
  killed : IsKilledAtFar iL iR w' vL' vR' τ
  trace : ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w' τ η
  agree : AgreeBefore w' w vL' vL vR' vR τ
  agree0 : w 0 = w' 0 ∧ (∀ i, vL i 0 = vL' i 0) ∧ ∀ j, vR j 0 = vR' j 0
  agreeB : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → b t = b' t

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **A stopped representation of a stage** (`𝓠` the past, `R` the stage event, `y` the start, `(W, V, B, ζ)` the
piece): a filtration `𝓕` with `𝓠 ≤ 𝓕 0`, a Brownian motion `B'` of `𝓕` and processes `(W', V')` adapted before `ζ`
such that almost surely on `R` the pathwise conditions `IsStoppedRepPath` hold. This is Aux. lemma 122's form (p. 391:
"Brownian noise independent of that initial information") of the piece's conditional law, stopped at its first far
contact. -/
structure IsStoppedRep (κ : ℝ) (P : Measure Ω) (𝓠 : MeasurableSpace Ω) (R : Set Ω) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (iL : Fin nL) (iR : Fin nR) (y : Ω → Start nL nR) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (𝓕 : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ) (VR' : Fin nR → ℝ≥0 → Ω → ℝ)
    (B' : ℝ≥0 → Ω → ℝ) : Prop where
  le0 : 𝓠 ≤ 𝓕 0
  brownian : IsFilteredBrownianReal 𝓕 B' P
  adapted_W : AdaptedBefore 𝓕 ζ W'
  adapted_VL : ∀ i, AdaptedBefore 𝓕 ζ (VL' i)
  adapted_VR : ∀ j, AdaptedBefore 𝓕 ζ (VR' j)
  ae_path : ∀ᵐ ω ∂P, ω ∈ R → IsStoppedRepPath κ ρL ρR iL iR (y ω) (W · ω) (fun i t => VL i t ω)
    (fun j t => VR j t ω) (B · ω) (ζ ω) (W' · ω) (fun i t => VL' i t ω) (fun j t => VR' j t ω) (B' · ω)

end Def

/-! ### Disintegration over the past -/

section Disint

variable {Ω : Type*} {𝓠 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {nL nR : ℕ} {κ : ℝ} {R : Set Ω} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {iL : Fin nL}
  {iR : Fin nR} {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {𝓕 : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL' : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR' : Fin nR → ℝ≥0 → Ω → ℝ} {B' : ℝ≥0 → Ω → ℝ}

/-- **Disintegration of a stopped representation over the past** (Aux. lemma 122, p. 391, for local paths): there are
a measurable null set `N`, one filtration `𝓖` and processes that keep the pathwise conditions off `N` on `R` such that
for `P`-almost every `ω₀ ∈ R` they form a local integrated `SLE_κ(ρ)` evolution of the deterministic start `y ω₀`
before `ζ` under the conditional law `condExpKernel P 𝓠 ω₀`. -/
theorem IsStoppedRep.ae_isSLEEvolutionUpTo
    (h : IsStoppedRep κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ 𝓕 W' VL' VR' B') (hR : MeasurableSet[𝓠] R)
    (hy : Measurable[𝓠] y) :
    ∃ (N : Set Ω) (𝓖 : Filtration ℝ≥0 mΩ) (W'' : ℝ≥0 → Ω → ℝ) (VL'' : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR'' : Fin nR → ℝ≥0 → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
      MeasurableSet N ∧ P N = 0 ∧
      (∀ ω, ω ∉ N → ω ∈ R → IsStoppedRepPath κ ρL ρR iL iR (y ω) (W · ω) (fun i t => VL i t ω)
        (fun j t => VR j t ω) (B · ω) (ζ ω) (W'' · ω) (fun i t => VL'' i t ω) (fun j t => VR'' j t ω)
        (B'' · ω)) ∧
      ∀ᵐ ω₀ ∂P, ω₀ ∈ R →
        Sec2.IsSLEEvolutionUpTo κ (y ω₀).2.1 (y ω₀).2.2 ρL ρR (condExpKernel P 𝓠 ω₀) 𝓖 W'' VL'' VR'' B'' ζ := by
  have hgood : ∀ᵐ ω ∂P, (Continuous (fun t => B' t ω) ∧ B' 0 ω = 0) ∧
      (ω ∈ R → IsStoppedRepPath κ ρL ρR iL iR (y ω) (W · ω) (fun i t => VL i t ω)
        (fun j t => VR j t ω) (B · ω) (ζ ω) (W' · ω) (fun i t => VL' i t ω) (fun j t => VR' j t ω) (B' · ω)) :=
    (h.brownian.1.cont.and h.brownian.1.toIsPreBrownianReal.eval_zero_ae_eq_zero).and h.ae_path
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hoff : ∀ ω, ω ∉ N → (Continuous (fun t => B' t ω) ∧ B' 0 ω = 0) ∧
      (ω ∈ R → IsStoppedRepPath κ ρL ρR iL iR (y ω) (W · ω) (fun i t => VL i t ω)
        (fun j t => VR j t ω) (B · ω) (ζ ω) (W' · ω) (fun i t => VL' i t ω) (fun j t => VR' j t ω)
        (B' · ω)) := fun ω hω => by
    by_contra hc
    exact hω (hNsub hc)
  set X := wordData R W' VL' VR' with hX
  have hR𝓕 : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] R := fun t => 𝓕.mono (by positivity) _ (h.le0 _ hR)
  have hlt : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω} := fun t => by
    have := h.adapted_W t univ MeasurableSet.univ
    simpa using this
  have hkill : ∀ i t, Measurable[𝓕 t] (killAt ζ (X i) t) := by
    rintro (_ | i | j) t
    · exact measurable_killAt_onF h.adapted_W (hR𝓕 t)
    · exact measurable_killAt_onF (h.adapted_VL i) (hR𝓕 t)
    · exact measurable_killAt_onF (h.adapted_VR j) (hR𝓕 t)
  have hS : DisintSetting P 𝓠 𝓕 B' N ζ X :=
    ⟨h.le0, h.brownian, hNm, hN0, fun ω hω => (hoff ω hω).1.1, fun ω hω => (hoff ω hω).1.2, hlt, hkill⟩
  have hXc : ∀ ω, ω ∉ N → ∀ i, ContinuousOn (fun t => X i t ω) {t | (t : ℝ≥0∞) < ζ ω} := by
    intro ω hω i
    by_cases hωR : ω ∈ R
    · have hp := ((hoff ω hω).2 hωR).path
      rcases i with _ | i | j
      · simp only [hX, wordData, onF_of_mem hωR]
        exact hp.continuousOn_w
      · simp only [hX, wordData, onF_of_mem hωR]
        exact hp.continuousOn_vL i
      · simp only [hX, wordData, onF_of_mem hωR]
        exact hp.continuousOn_vR j
    · rcases i with _ | i | j <;> simp only [hX, wordData, onF_of_notMem hωR] <;> exact continuousOn_const
  have hle : 𝓠 ≤ mΩ := hS.le_mΩ
  have e1 : ∀ ω, ω ∉ N → ω ∈ R → (fun t => zeroOn N (X none) t ω) = fun t => W' t ω := fun ω hωN hωR =>
    funext fun t => by simp only [zeroOn_of_notMem hωN, hX, wordData, onF_of_mem hωR]
  have e2 : ∀ ω, ω ∉ N → ω ∈ R → (fun i t => zeroOn N (X (some (Sum.inl i))) t ω) = fun i t => VL' i t ω :=
    fun ω hωN hωR => funext fun i => funext fun t => by
      simp only [zeroOn_of_notMem hωN, hX, wordData, onF_of_mem hωR]
  have e3 : ∀ ω, ω ∉ N → ω ∈ R → (fun j t => zeroOn N (X (some (Sum.inr j))) t ω) = fun j t => VR' j t ω :=
    fun ω hωN hωR => funext fun j => funext fun t => by
      simp only [zeroOn_of_notMem hωN, hX, wordData, onF_of_mem hωR]
  have e4 : ∀ ω, ω ∉ N → (fun t => zeroOn N B' t ω) = fun t => B' t ω := fun ω hωN =>
    funext fun t => zeroOn_of_notMem hωN t
  refine ⟨N, dataFilt N ζ B' X, zeroOn N (X none), fun i => zeroOn N (X (some (Sum.inl i))),
    fun j => zeroOn N (X (some (Sum.inr j))), zeroOn N B', hNm, hN0, ?_, ?_⟩
  · intro ω hωN hωR
    have hp := (hoff ω hωN).2 hωR
    simp only []
    rw [e1 ω hωN hωR, e2 ω hωN hωR, e3 ω hωN hωR, e4 ω hωN]
    exact hp
  filter_upwards [hS.ae_isFilteredBrownianReal, hS.ae_condExpKernel_N, ae_ae_condExpKernel_mem hle hR,
    ae_ae_condExpKernel_eq hle hy] with ω₀ hBr hνN hmemR hy₀ hω₀R
  refine ⟨hBr, hS.dataMeas.adaptedBefore_zeroOn hXc none,
    fun i => hS.dataMeas.adaptedBefore_zeroOn hXc (some (Sum.inl i)),
    fun j => hS.dataMeas.adaptedBefore_zeroOn hXc (some (Sum.inr j)), ?_⟩
  filter_upwards [hmemR hω₀R, hy₀, measure_eq_zero_iff_ae_notMem.1 hνN] with ω hωR hωy hωN
  have hp := ((hoff ω hωN).2 hωR).path
  rw [hωy] at hp
  rw [e1 ω hωN hωR, e2 ω hωN hωR, e3 ω hωN hωR, e4 ω hωN]
  exact hp

end Disint

/-! ### The killed law from a stopped representation -/

section Main

variable {Ω : Type} {𝓠 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {nL nR : ℕ} {κ : ℝ} {R : Set Ω} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {iL : Fin nL}
  {iR : Fin nR} {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {𝓕 : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL' : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR' : Fin nR → ℝ≥0 → Ω → ℝ} {B' : ℝ≥0 → Ω → ℝ}

/-- **The per-candidate killed law from a stopped representation** (ruling R78). If the piece of a stage has a
stopped representation (`IsStoppedRep`: Aux. lemma 122's form of its conditional law given the past `𝓠`, stopped at its
first far contact), with `𝓠`-measurable stage event and start and measurable killed samples, then the stage obeys
`IsStageLawFarK`. Clause 1 is the pathwise part transported to the piece; clause 2 is PROVE-STAGED8's
`isStageLawFarK_of_condLaw`, its representation at almost every conditional law being the continuation
(`hasKilledRep_of_isSLEEvolutionUpTo`) of the disintegrated local evolution (`IsStoppedRep.ae_isSLEEvolutionUpTo`). -/
theorem IsStoppedRep.isStageLawFarK (hκ : 0 < κ)
    (h : IsStoppedRep κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ 𝓕 W' VL' VR' B') (hR : MeasurableSet[𝓠] R)
    (hy : Measurable[𝓠] y) (hobs : Measurable (pieceSamp W VL VR ζ)) :
    IsStageLawFarK κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ := by
  obtain ⟨N, 𝓖, W'', VL'', VR'', B'', -, hN0, hpt, hev⟩ := h.ae_isSLEEvolutionUpTo hR hy
  have hle : 𝓠 ≤ mΩ := h.le0.trans (𝓕.le 0)
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  refine isStageLawFarK_of_condLaw hle hy hobs ?_ ?_
  · filter_upwards [hNae] with ω hωN hωR
    have hp := hpt ω hωN hωR
    exact ⟨hp.ordered, hp.anti, hp.mono, Sec2.Assembly2.isSLEPathUpTo_congr hp.path hp.agree0.1 hp.agree0.2.1
      hp.agree0.2.2 (fun t ht => (hp.agree t ht).1) (fun t ht => (hp.agree t ht).2.1)
      (fun t ht => (hp.agree t ht).2.2) hp.agreeB⟩
  · filter_upwards [hev, ae_ae_condExpKernel hle hNae, ae_ae_condExpKernel_mem hle hR, hNae] with
      ω₀ hE hνN hmemR hω₀N hω₀R
    have hgood : ∀ᵐ ω ∂(condExpKernel P 𝓠 ω₀), ω ∉ N ∧ ω ∈ R := hνN.and (hmemR hω₀R)
    have hrep := hasKilledRep_of_isSLEEvolutionUpTo (iL := iL) (iR := iR) hκ (hpt ω₀ hω₀N hω₀R).ordered (hE hω₀R)
      (by filter_upwards [hgood] with ω hω using (hpt ω hω.1 hω.2).killed)
      (by filter_upwards [hgood] with ω hω using (hpt ω hω.1 hω.2).trace)
    have hmap : (condExpKernel P 𝓠 ω₀).map (pieceSamp W VL VR ζ) =
        (condExpKernel P 𝓠 ω₀).map (pieceSamp W'' VL'' VR'' ζ) :=
      Measure.map_congr (by filter_upwards [hgood] with ω hω using samp_congr (hpt ω hω.1 hω.2).agree)
    rw [hmap]
    exact hrep

end Main

end InteractingSLE.Sec5.CrossCond.StagedKCand
