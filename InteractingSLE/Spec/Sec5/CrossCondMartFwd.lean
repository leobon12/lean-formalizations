/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondMartAsm

/-!
# The chart clause at fixed forward times (general `κ`): the conditional law of the field given both stopped
histories, read in the counterflow chart

Packet PROVE-GLUECOND7 (Astra's E.3 at general `κ`; the general-`κ` form of PROVE-WW-B19's `ImgChartConstFwd`). At a
forward (flow) time `t > 0` before contact, the revealed union `A_t ∪ G_s` (flow hull and reflected counterflow hull)
is, in the counterflow chart `Ψ`, the image hull of the killed image word at the image time `σ(t)`:

`Ψ⁻¹(ℍ ∖ K̃_{σ(t)}) = ℍ ∖ (A_t ∪ G_s)` (`cfChart_inv_image_eq`).

PROVE-GLUECOND5's E.3 gives the conditional characteristic function of `(h, φ)` given the germ of `A_t ∪ G_s` and both
stopped histories in terms of the conditional mean. With the **identification of that mean** in the chart (`G3 (ii)`
of Proposition 4.9, PROVE-GLUECOND6, recorded here as the named input `MeanIdent49Statement`), the conditional
characteristic function is the explicit `cfF(σ(t))` (`ae_condExp_cfGlue_eq_cfF`, step R1).

## Main results

* `revChartInv_image_H_diff_union`: `Ψ⁻¹(ℍ ∖ Ψ(A)) = ℍ ∖ (A ∪ R(K_s))` for `A ⊆ ℍ ∖ R(K_s)`;
* `ae_hullAt_eq_image_seedLine`, `ae_cfReg`: almost surely the flow hull read from the history is the trace prefix, and
  the counterflow has infinite lifetime and a continuous driver from `0`;
* **`cfChart_inv_image_eq`**: the image identification above on every good sample;
* `MeanIdent49Statement` (**named input**: the conditional mean in the chart, G3 (ii) of Proposition 4.9);
* **`ae_condExp_cfGlue_eq_cfF`**: step R1 at general `κ`.

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H fwdHull fwdMap chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CrossCond

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q WholeField LocalSets
open ImgDrv MartChar
open Sec7.Lemma71C (capClock)

namespace Word49

/-! ### The image identification -/

section Ident

/-- `Ψ⁻¹(ℍ ∖ Ψ(A)) = ℍ ∖ (A ∪ R(K_s))` for `A ⊆ ℍ ∖ R(K_s)` (the set identity of PROVE-WW-B19's
`revChartInv_image_H_diff`, here for the counterflow chart). -/
theorem revChartInv_image_H_diff_union {Wβ : ℝ → ℝ} (hW : Continuous Wβ) (hW0 : Wβ 0 = 0) {s : ℝ} (hs : 0 ≤ s)
    {A : Set ℂ} (hA : A ⊆ H \ negInv '' fwdHull Wβ s) :
    revChartInv Wβ s '' (H \ revChart Wβ s '' A) = H \ (A ∪ negInv '' fwdHull Wβ s) := by
  ext z
  constructor
  · rintro ⟨w, ⟨hwH, hwA⟩, rfl⟩
    have hm := revChartInv_mem hW hW0 hs hwH
    refine ⟨hm.1, fun hz => ?_⟩
    rcases hz with hz | hz
    · exact hwA ⟨_, hz, revChart_revChartInv hW hW0 hs hwH⟩
    · exact hm.2 hz
  · rintro ⟨hzH, hz⟩
    have hzG : z ∈ H \ negInv '' fwdHull Wβ s := ⟨hzH, fun h => hz (Or.inr h)⟩
    refine ⟨revChart Wβ s z, ⟨revChart_mem_H hW hs hzG, ?_⟩, revChartInv_revChart hW hW0 hs hzG⟩
    rintro ⟨a, ha, e⟩
    exact hz (Or.inl (injOn_revChart hW hW0 hs (hA ha) hzG e ▸ ha))

variable {Ω : Type*} {nL nR : ℕ} {s : ℝ≥0} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)}

/-- **The image identification on a good sample.** Before contact, the counterflow chart pulls the remaining domain of
the image word at the image time `σ(t)` back to `ℍ ∖ (A_t ∪ G_s)`. -/
theorem cfChart_inv_image_eq (hEg : ∀ p ∈ E, IsGood49 s ζ W p) {p : Ω × HistorySpace 0 0} (hp : p ∈ E) {t : ℝ≥0}
    (htP : (t : ℝ) ∈ gPre s ζ W E p)
    (hA : hullAt t (killedHistory W VL VR ζ p.1) = seedLine ζ W p.1 '' Ioc 0 t) :
    (cfChart s p.2).2.1 '' (H \ fwdHull (Ito.rpath fun r => imgW s ζ W E r p)
      (((capClock (gCurve s ζ W E p) t).toNNReal : ℝ≥0) : ℝ)) =
      H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2) := by
  obtain ⟨hα, -, -, -, hGeq⟩ := hEg p hp
  set Wβ := cfDrv0 s p.2 with hWβdef
  have hWβc : Continuous Wβ := continuous_cfDrv0 s p.2
  have hWβ0 : Wβ 0 = 0 := cfDrv0_zero s p.2
  have hP : gPre s ζ W E p = preContact (seedLine ζ W p.1) (cfHullQ s p.2) := gPre_of_mem hp
  have hγ : gCurve s ζ W E p = imgCurve Wβ s (seedLine ζ W p.1) := gCurve_of_mem hp
  have htP' : (t : ℝ) ∈ preContact (seedLine ζ W p.1) (cfHullQ s p.2) := hP ▸ htP
  have hAsub : seedLine ζ W p.1 '' Ioc 0 t ⊆ H \ negInv '' fwdHull Wβ s := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨hα.mem_H u hu.1, ?_⟩
    rw [← hGeq]
    exact htP'.2 u ⟨hu.1.le, hu.2⟩
  have hγimg : gCurve s ζ W E p '' Ioc 0 t = revChart Wβ s '' (seedLine ζ W p.1 '' Ioc 0 t) := by
    rw [hγ, image_image]
    refine image_congr fun u hu => ?_
    exact imgCurve_of_pos hu.1
  have hkill : IsKilledArc (gCurve s ζ W E p) (gPre s ζ W E p) := isKilledArc_gCurve hEg p
  have hcap0 : 0 ≤ capClock (gCurve s ζ W E p) t := hkill.capClock_nonneg htP
  have hhull : fwdHull (Ito.rpath fun r => imgW s ζ W E r p)
      (((capClock (gCurve s ζ W E p) t).toNNReal : ℝ≥0) : ℝ) = revChart Wβ s '' (seedLine ζ W p.1 '' Ioc 0 t) := by
    rw [Real.coe_toNNReal _ hcap0, ← hγimg]
    exact hkill.fwdHull_eq_of_eqOn_chainDrv (fun S hS r hr => (hkill.kW_eq_chainDrv hS).2 r hr) htP
  rw [cfChart_inv, hhull, revChartInv_image_H_diff_union hWβc hWβ0 s.coe_nonneg hAsub, hGeq, hA]

end Ident

/-! ### Almost-sure regularity in the glued setting -/

section Reg

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂}
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- Almost surely the flow line has infinite lifetime and its hulls read from the history are its trace prefixes. -/
theorem ae_hullAt_eq_image_seedLine (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR)
    (h44 : Sec4.Cond44 κ ρL ρR) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t : ℝ≥0, hullAt t (killedHistory W VL VR ζ ω) = seedLine ζ W ω '' Ioc 0 t := by
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hline := ae_seedLine_of_admissible hκ hκ4.le hF hadm hC.1
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := by
    filter_upwards [hline] with ω hω using hω.1
  filter_upwards [hline, Aux50Hit.ae_isGoodPath hC.1 hζ] with ω ⟨hζω, ⟨η, hη, hseq⟩, hprop⟩ hg
  refine ⟨hζω, fun t => ?_⟩
  have hα : IsLoewnerTrace (fun r : ℝ => W r.toNNReal ω) (seedLine ζ W ω) := by
    rw [hseq]; exact isLoewnerTrace_of_isGeneratingTrace hη
  rw [hullAt, Aux50Hit.regHull_stopHistory_cstop hg t]
  exact fwdHull_eq_image_Ioc hα hprop t.coe_nonneg

/-- **The counterflow's regularity on its own space**: infinite lifetime and a continuous driver from `0`. -/
theorem ae_cfReg [IsProbabilityMeasure P₂] (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR)
    (h44 : Sec4.Cond44 κ ρL ρR) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂) :
    ∀ᵐ ω ∂P₂, ζ₂ ω = ⊤ ∧ W₂ 0 ω = 0 ∧ Continuous fun t => W₂ t ω := by
  obtain ⟨mL, mR, yL, yR, σL, σR, 𝓕₂, VL₂, VR₂, B₂, hF', hadm, hE⟩ :=
    exists_admissible_of_isCenteredCounterflowDriver hκ hκ4 hF h44 hC hcf hlaw
  have hk' : 0 < 16 / κ := by positivity
  filter_upwards [ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hk' hF' hadm hE,
    hE.2.2.2.2] with ω ⟨hζ, _, η, hη⟩ hp
  have hw : Continuous fun t => W₂ t ω := by
    have := hp.2.2.2.1
    rw [hζ] at this
    exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
  exact ⟨hζ, hp.1, hw⟩

end Reg

/-! ### Step R1: the conditional law at a forward time -/

/-- **Named input: the conditional mean of the field given both stopped histories, in the counterflow chart** (G3 (ii)
of Proposition 4.9 at general `κ`, PROVE-GLUECOND6's identification of the union mean; Astra's E.3). In the setting of
`Prop411Q.CfGlueAE`, for each counterflow time `s > 0`, forward time `t > 0` and test function `φ`, almost surely on
the forward validity event `cfAv φ t` (a good sample, `t` before contact, `supp φ` off the image hull at `σ(t)` in the
chart), the conditional mean of the centred field given the germ of `A_t ∪ G_s` and both stopped histories, plus
`∫ 𝔥₀ φ`, is the chart mean of the image word at the image time `σ(t)` (coupling mean of the image word composed with
`Ψ`, minus `χ (Im L_Ψ + 2π)`). -/
def MeanIdent49Statement (cL cR : ℝ → ℝ → ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR → Sec4.Cond44 κ ρL ρR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens)
      (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
      {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
      (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ →
      P.map (fun ω => cfField κ (h ω)) = P₂.map h₂ →
      ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
        P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k →
        ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀ →
        ∀ s : ℝ≥0, 0 < s → ∀ t : ℝ≥0, 0 < t → ∀ φ : TestOn upperHalfPlaneOpens,
          ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
            p ∈ cfAv s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
              ((measurable_cfField κ).comp hC.2.1)) s ζ W) φ t →
            (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1))[
                fun p' => cenT κ u₀ (cfField κ (h p'.1)) φ |
                germSigma (fun p : Ω × HistorySpace 0 0 => hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)
                  (fun p => cenT κ u₀ (cfField κ (h p.1))) ⊔ cfGlueMarks W VL VR ζ t s] p +
                ∫ z, u₀ z * φ z =
              Sec7.Lemma71D.chartMean κ (jwL cL κ ρL) (jwR cR κ ρR)
                (fun r => imgW s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
                  ((measurable_cfField κ).comp hC.2.1)) s ζ W) r p)
                (fun i r => imgVL xL s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
                  ((measurable_cfField κ).comp hC.2.1)) s ζ W) i r p)
                (fun j r => imgVR xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
                  ((measurable_cfField κ).comp hC.2.1)) s ζ W) j r p)
                (cfChart s p.2) (2 * Real.pi * chiC κ) (chiC κ) φ
                (capClock (gCurve s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
                  ((measurable_cfField κ).comp hC.2.1)) s ζ W) p) t).toNNReal

section R1

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- **Step R1 at general `κ`.** At a forward time `t > 0`, almost surely on the forward validity event, the
conditional characteristic function of `(h, φ)` given the germ of `A_t ∪ G_s` and both stopped histories is the
explicit `cfF(σ(t))` (E.3 with the identification of the mean). -/
theorem ae_condExp_cfGlue_eq_cfF {cL cR : ℝ → ℝ → ℝ} (hMI : MeanIdent49Statement.{u} cL cR) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {s : ℝ≥0} (hs : 0 < s) {t : ℝ≥0} (ht : 0 < t) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
      p ∈ cfAv s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
        ((measurable_cfField κ).comp hC.2.1)) s ζ W) φ t →
      (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1))[
          fun p' => Complex.exp (Complex.I * (h p'.1 φ : ℂ)) |
          germSigma (fun p : Ω × HistorySpace 0 0 => hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)
            (fun p => cenT κ u₀ (cfField κ (h p.1))) ⊔ cfGlueMarks W VL VR ζ t s] p =
        cfF cL cR κ ρL ρR xL xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) φ
          (capClock (gCurve s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) s ζ W) p) t).toNNReal p := by
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  set E := glueGood μ s ζ W with hEdef
  have hEg : ∀ p ∈ E, IsGood49 s ζ W p := isGood49_of_mem_glueGood
  set U : Ω × HistorySpace 0 0 → Set ℂ := fun p => hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2
    with hUdef
  set F : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens := fun p => cenT κ u₀ (cfField κ (h p.1)) with hFdef
  have hX := hC.2.2.2.1
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  have hYm : Measurable (killedHistory W VL VR ζ) := measurable_killedHistory hX
  have hFg := isZeroBoundaryGFF_cenT_glue (k := k) hC hu₀
  have hAm : Measurable[_, hittingSigma] U :=
    measurable_union_hitting (((measurable_hullAt t).comp hYm).comp measurable_fst)
      ((measurable_cfHullQ s).comp measurable_snd)
  have hAae := ae_hullAt_eq_image_seedLine hκ hκ4 hF h44 hC
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := by
    filter_upwards [hAae] with ω hω using hω.1
  have hreg₂ := ae_cfReg hκ hκ4 hF h44 hC hcf hlaw
  have hmark := isHistoryAvoidanceLocal_cfGlue hC hκ hζ hcf hreg₂ hlaw hk hu₀ t s
  have hℋ := cfGlueMarks_le (Ω := Ω) t s hX
  obtain ⟨M, -, hM1, hM2⟩ := exists_condExp_germSigma_history hFg hAm hℋ hmark
    (Eventually.of_forall fun p => union_relClosed t s _ p.2) φ
  -- the constant `e^{i ∫ 𝔥₀ φ}` is pulled out
  set c : ℂ := Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) with hc
  have e : (fun p : Ω × HistorySpace 0 0 => Complex.exp (Complex.I * (h p.1 φ : ℂ))) =
      c • fun p => Complex.exp (Complex.I * (F p φ : ℂ)) := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, hc, hFdef, cenT_cfField, ← Complex.exp_add]
    rw [show h p.1 - SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ =
      centredField h u₀ p.1 from rfl, centredField_apply h hu₀.1 p.1 φ]
    congr 1
    push_cast
    ring
  have hpull := condExp_smul (μ := μ) c (fun p : Ω × HistorySpace 0 0 => Complex.exp (Complex.I * (F p φ : ℂ)))
    (germSigma U F ⊔ cfGlueMarks W VL VR ζ t s)
  rw [← e] at hpull
  have hid := hMI κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk u₀ hu₀ s hs t ht φ
  filter_upwards [hM1, hM2, hpull, hid, ae_glue_fst (μ := P) k hXm hAae] with p h1 h2 h5 h4 hAp hAv
  obtain ⟨hpE, htP, hav⟩ := hAv
  have hset := cfChart_inv_image_eq hEg hpE htP (hAp.2 t)
  rw [h5, Pi.smul_apply, ← h2, smul_eq_mul]
  have hMp : M p = Sec7.Lemma71D.chartMean κ (jwL cL κ ρL) (jwR cR κ ρR) (fun r => imgW s ζ W E r p)
      (fun i r => imgVL xL s ζ W E i r p) (fun j r => imgVR xR s ζ W E j r p) (cfChart s p.2)
      (2 * Real.pi * chiC κ) (chiC κ) φ (capClock (gCurve s ζ W E p) t).toNNReal - ∫ z, u₀ z * φ z := by
    rw [h1, ← h4 ⟨hpE, htP, hav⟩]
    ring
  have hv : QuantumZipper.zeroGFFTestCov (H \ relClosureH (U p)) φ φ =
      Sec7.Lemma71D.chartVar (fun r => imgW s ζ W E r p) (cfChart s p.2) φ
        (capClock (gCurve s ζ W E p) t).toNNReal := by
    obtain ⟨hsub, hopen⟩ := union_relClosed t s (killedHistory W VL VR ζ p.1) p.2
    rw [Sec7.Lemma71D.chartVar, hset, relClosureH_eq hsub hopen]
  rw [hv, hMp, cfF, hc, ← mul_assoc, ← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end R1

end Word49

end InteractingSLE.Sec5.CrossCond
