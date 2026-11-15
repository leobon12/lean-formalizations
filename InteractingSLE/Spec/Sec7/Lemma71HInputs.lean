/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.CanonicalMain
import InteractingSLE.Spec.Sec7.Lemma71GSpace
import InteractingSLE.Spec.Sec7.Lemma75Bridge
import InteractingSLE.Spec.Sec7.Prop74ProofWord

/-!
# Lemma 7.1: the three-curve space from the non-boundary (§4.2) forms of its inputs

Packet PROVE-LEMMA71H, first item (ruling R43). The three-curve space of §7.1
(`Lemma71G.exists_threeCurveSpace`) took the frozen types of Theorems 1.2 and 1.3 and the all-words Lemma 7.5 as
named inputs. Theorems 1.2, 1.3 and Lemma 7.5 are proved *through* Lemma 7.1, so Lemma 7.1's chain may only use their
non-boundary-intersecting forms (specification p. 221: "By Theorem 1.2, in a certain non-boundary-intersecting regime,
which we proved in Section 4.2, we know that `η_{θ₁}`, `η` and `η_{θ₂}` are all almost surely determined by `h`").
This file restates the space with exactly those forms:

* Theorem 1.3 (traces): in Remark 4.1's regime (admissible side partial sums, `κ ≤ 4`) this is Aux. lemma 7
  (`Zhan.aux7Statement`, proved);
* Theorem 1.2 (determination): §4.2's proof under (4.4) = one reference coupling with a field-determined history
  (Proposition 4.11 and conditional independence, p. 122) plus the transfer to every coupling (Aux. lemma 23,
  `Sec4.hasFieldDeterminedHistories_of_admissible_of_reference`, proved). The reference half is the named input
  **`Cond44ReferenceStatement`** (PROVE-SEC4-B5's "only missing input");
* Lemma 7.5 (one Borel map for every flow line): `Lemma75Bridge.exists_flowLineMap_of_admissible` (Aux. 23 and the
  same reference; no Proposition 7.3);
* the existence of the flow lines on the given field: the landed realization chain
  (`Exist.exists_fieldDetermination_frz`, `…_realization`, `exists_isFlowLine_of_thm12_thm13_only`) used the frozen
  Theorems 1.2–1.3 only at the provider's coupling of the flow-line word; `exists_isFlowLine_of_det` below is the same
  chain with those two uses replaced by the §4.2 forms (the proofs are the landed ones, with the two inputs passed in);
* Aux. lemma 56 at first entrance times (`Restart.RetainedRangeEntranceStatement`) stays a named input: its source
  proof (Aux. lemmas 47 and 50, pp. 241–252) does not use Lemma 7.1, Proposition 7.3, Theorem 1.2 or Theorem 1.3, so
  it does not close the cycle.

**`exists_threeCurveSpace_nb`**: `Lemma71G.exists_threeCurveSpace` from `Cond44ReferenceStatement` and
`Restart.RetainedRangeEntranceStatement` only, with `b ≥ λ − θ₁χ` (so that the three flow-line words satisfy (4.4);
this is exactly Proposition 5.5's hypothesis (5.2) on `θ₁`).

**`exists_threeCurveSpace_ordered`**: the same space with the closed-side order of the three complete curves, from
the named input **`Prop55HalfPlaneStatement`** (Proposition 5.5 in `ℍ`, whole curves; proved in §5 without Lemma 7.1).

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Real unitInterval

universe u

namespace InteractingSLE.Sec7.Lemma71H

open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)
open Exist Sec2.Assembly WholeField

variable {nL nR : ℕ}

/-! ### The realization chain from a per-coupling Borel map and traces -/

section Realization

/-- **Field determination, frozen form, from a Borel map and traces of the given coupling** (the landed
`Exist.exists_fieldDetermination_frz` with its two uses of the frozen Theorems 1.2–1.3 replaced by hypotheses on the
coupling itself: a Borel map `Φ` of the field giving the lifetime and every generating trace, and the almost sure
existence of a generating trace). -/
theorem exists_fieldDetermination_frz_of_det
    {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {Ω₀ : Type u} {mΩ₀ : MeasurableSpace Ω₀}
    {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {𝓕₀ : Filtration ℝ≥0 mΩ₀} {W₀ : ℝ≥0 → Ω₀ → ℝ}
    {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B₀ : ℝ≥0 → Ω₀ → ℝ}
    {ζ₀ : Ω₀ → ℝ≥0∞} {h₀ : Ω₀ → LQGMetric.DistOn upperHalfPlaneOpens}
    (hcoup : IsOptionalHullCoupling κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀)
    (hdet : ∃ Φ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ᵐ ω ∂P₀, (Φ (h₀ ω)).1 = ζ₀ ω ∧
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₀ t ω) (ζ₀ ω) η →
          ∀ t : ℝ≥0, (Φ (h₀ ω)).2 t = η (min (t : ℝ≥0∞) (ζ₀ ω)).toNNReal)
    (htr : ∀ᵐ ω ∂P₀, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₀ t ω) (ζ₀ ω) η) :
    ∃ (Ψ : LQGMetric.DistOn upperHalfPlaneOpens → XCode nL nR)
      (S : Set (LQGMetric.DistOn upperHalfPlaneOpens))
      (ηf : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0 → ℂ) (B' : ℝ≥0 → Ω₀ → ℝ),
      Measurable Ψ ∧ MeasurableSet S ∧ (∀ t, Measurable (B' t)) ∧ (∀ ω, Continuous (B' · ω)) ∧
      (∀ ω, B' 0 ω = 0) ∧ ProbabilityTheory.IsBrownianReal B' P₀ ∧ (∀ᵐ ω ∂P₀, ∀ t, B' t ω = B₀ t ω) ∧
      (∀ᵐ ω ∂P₀, h₀ ω ∈ S ∧ Ψ (h₀ ω) = frz (codeOf xL xR B' W₀ VL₀ VR₀ ζ₀ ω) ∧
        cζ (Ψ (h₀ ω)) = ζ₀ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω →
        cw (Ψ (h₀ ω)) t = W₀ t ω ∧ (∀ i, cvL (Ψ (h₀ ω)) i t = VL₀ i t ω) ∧
          ∀ j, cvR (Ψ (h₀ ω)) j t = VR₀ j t ω) ∧
      ∀ f ∈ S, Ψ f ∈ DetSet κ xL xR ρL ρR ∧ IsGeneratingTrace (cw (Ψ f)) (cζ (Ψ f)) (ηf f) := by
  have hE := hcoup.1
  obtain ⟨Φ, hΦm, hΦ⟩ := hdet
  obtain ⟨B', hB'm, hB'c, hB'0, hB'B, hB'ae⟩ := QuantumZipper.RS.exists_good_version0 hE.1.1
  obtain ⟨G, hGm, hG⟩ := exists_measurable_leftInverse_of_injOn
    (measurable_traceOfCode (nL := nL) (nR := nR)) (measurableSet_detSet κ xL xR ρL ρR)
    (injOn_traceOfCode hκ)
  refine ⟨G ∘ codeΦ Φ, GoodField Φ G κ xL xR ρL ρR, traceOfΦ Φ, B', hGm.comp (measurable_codeΦ hΦm),
    measurableSet_goodField hΦm hGm κ xL xR ρL ρR, hB'm, hB'c, hB'0, hB'B, hB'ae, ?_,
    fun f hf => ⟨hf.1, isGeneratingTrace_of_mem_goodField hf⟩⟩
  filter_upwards [hΦ, htr, ae_codeOf_mem hκ hE hB'c hB'ae] with ω hΦω h13ω hcode
  obtain ⟨η, hη⟩ := h13ω
  obtain ⟨hx₁, hdec⟩ := hcode
  set x₀ := frz (codeOf xL xR B' W₀ VL₀ VR₀ ζ₀ ω) with hx₀def
  have hζx : cζ x₀ = ζ₀ ω := rfl
  have hcwx : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω → cw x₀ t = W₀ t ω := fun t ht => (hdec t ht).1
  have hηx : IsGeneratingTrace (cw x₀) (ζ₀ ω) η := Sec7.IsGeneratingTrace.congr_lt hη hcwx
  have hcrel : x₀ ∈ CRel κ xL xR ρL ρR := frz_mem_cRel hx₁
  have hmem : x₀ ∈ DetSet κ xL xR ρL ρR :=
    ⟨⟨hcrel, frozenB_frz hx₁.1.1⟩, fun n k hT => mem_traceSet_of_isGeneratingTrace hcrel hT hηx hT.le⟩
  have hcode : traceOfCode x₀ = codeΦ Φ (h₀ ω) := by
    refine Prod.ext hΦω.1.symm (funext fun n => funext fun k => ?_)
    simp only [traceOfCode, codeΦ, hζx, hΦω.1]
    by_cases hlt : ((dyad n k : ℝ≥0) : ℝ≥0∞) < ζ₀ ω
    · simp only [hlt, ↓reduceIte]
      rw [hΦω.2 η hη, min_eq_left hlt.le, ENNReal.toNNReal_coe]
      exact LP.traceAt_eq_of_isGeneratingTrace hηx hcrel.1.1.continuousOn_w hcrel.1.2.2.1 hlt
    · simp only [hlt, ↓reduceIte]
  have hΨ : G (codeΦ Φ (h₀ ω)) = x₀ := by rw [← hcode]; exact hG x₀ hmem
  have hγ := continuous_trace_min hη.2.1
  have hre : reCode Φ (h₀ ω) = enc fun t => (η (min (t : ℝ≥0∞) (ζ₀ ω)).toNNReal).re := by
    funext n k; simp only [reCode, enc, hΦω.2 η hη]
  have him : imCode Φ (h₀ ω) = enc fun t => (η (min (t : ℝ≥0∞) (ζ₀ ω)).toNNReal).im := by
    funext n k; simp only [imCode, enc, hΦω.2 η hη]
  refine ⟨⟨by simp only [hΨ]; exact hmem, by simp only [hΨ]; exact hcode,
    fun N => ⟨hre ▸ uc_enc (Complex.continuous_re.comp hγ).continuousOn,
      him ▸ uc_enc (Complex.continuous_im.comp hγ).continuousOn⟩, ?_⟩, by simp only [Function.comp_apply, hΨ], ?_,
      fun t ht => ?_⟩
  · rw [hΦω.2 η hη]
    simpa using hη.1
  · simp only [Function.comp_apply, hΨ]; rfl
  · simp only [Function.comp_apply, hΨ]
    exact ⟨(hdec t ht).1, (hdec t ht).2.1, (hdec t ht).2.2.1⟩

/-- **The driving evolution is realized on every space carrying the field, from a Borel map and traces of the given
coupling** (the landed `Exist.exists_fieldDetermination_realization` with the frozen Theorems 1.2–1.3 replaced by
the hypotheses `hdet`, `htr` on `hcoup` itself; same proof). -/
theorem exists_fieldDetermination_realization_of_det {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω₀ : Type u}
    {mΩ₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {𝓕₀ : Filtration ℝ≥0 mΩ₀}
    {W₀ : ℝ≥0 → Ω₀ → ℝ} {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ}
    {B₀ : ℝ≥0 → Ω₀ → ℝ} {ζ₀ : Ω₀ → ℝ≥0∞} {h₀ : Ω₀ → DistOn upperHalfPlaneOpens}
    (hcoup : IsOptionalHullCoupling κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀)
    (hdet : ∃ Φ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ᵐ ω ∂P₀, (Φ (h₀ ω)).1 = ζ₀ ω ∧
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₀ t ω) (ζ₀ ω) η →
          ∀ t : ℝ≥0, (Φ (h₀ ω)).2 t = η (min (t : ℝ≥0∞) (ζ₀ ω)).toNNReal)
    (htr : ∀ᵐ ω ∂P₀, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₀ t ω) (ζ₀ ω) η) :
    ∃ (Ψ : DistOn upperHalfPlaneOpens → XCode nL nR) (S : Set (DistOn upperHalfPlaneOpens))
      (ηf : DistOn upperHalfPlaneOpens → ℝ≥0 → ℂ),
      Measurable Ψ ∧ MeasurableSet S ∧
      (∀ᵐ ω ∂P₀, h₀ ω ∈ S ∧ cζ (Ψ (h₀ ω)) = ζ₀ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω →
        cw (Ψ (h₀ ω)) t = W₀ t ω ∧ (∀ i, cvL (Ψ (h₀ ω)) i t = VL₀ i t ω) ∧
          ∀ j, cvR (Ψ (h₀ ω)) j t = VR₀ j t ω) ∧
      (∀ f ∈ S, IsGeneratingTrace (cw (Ψ f)) (cζ (Ψ f)) (ηf f)) ∧
      ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistOn upperHalfPlaneOpens), Measurable h → P.map h = P₀.map h₀ →
        ∃ (𝓕 : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ),
          IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 (fun t ω => cw (Ψ (h ω)) t)
            (fun i t ω => cvL (Ψ (h ω)) i t) (fun j t ω => cvR (Ψ (h ω)) j t) B
            (fun ω => cζ (Ψ (h ω))) := by
  obtain ⟨Ψ, S, ηf, B', hΨm, hSm, hB'm, hB'c, hB'0, hB'B, hB'ae, hae, hS⟩ :=
    exists_fieldDetermination_frz_of_det hκ hcoup hdet htr
  refine ⟨Ψ, S, ηf, hΨm, hSm, hae.mono fun ω hω => ⟨hω.1, hω.2.2.1, hω.2.2.2⟩,
    fun f hf => (hS f hf).2, ?_⟩
  intro Ω mΩ P hP h hh hlaw
  have hh₀ : Measurable h₀ := hcoup.2.1
  set X₀ : Ω₀ → XCode nL nR := fun ω => Ψ (h₀ ω) with hX₀def
  have hX₀m : Measurable X₀ := hΨm.comp hh₀
  have hX₀ : ∀ᵐ ω ∂P₀, X₀ ω ∈ DetSet κ xL xR ρL ρR ∧ X₀ ω = frz (codeOf xL xR B' W₀ VL₀ VR₀ ζ₀ ω) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω → cw (X₀ ω) t = W₀ t ω ∧ (∀ i, cvL (X₀ ω) i t = VL₀ i t ω) ∧
        ∀ j, cvR (X₀ ω) j t = VR₀ j t ω := by
    filter_upwards [hae] with ω hω
    exact ⟨(hS _ hω.1).1, hω.2.1, hω.2.2.2⟩
  obtain ⟨𝓖, hE₀⟩ := model_isIntegratedSLEEvolution hcoup hκ hB'm hB'c hB'0 hB'B hB'ae hX₀m hX₀
  obtain ⟨U, hUm, hU01, hUlaw⟩ :=
    exists_uniform_field hcoup hκ hΨm (hX₀.mono fun ω hω => ⟨hω.1, hω.2.1⟩)
  have hencm := measurable_enc_proc hB'm
  have : IsProbabilityMeasure (P₀.map fun ω => enc fun t => B' t ω) :=
    (Measure.isProbabilityMeasure_map_iff hencm.aemeasurable).2 inferInstance
  obtain ⟨Fw, hFwm, hFw⟩ := (P₀.map fun ω => enc fun t => B' t ω).exists_measurable_map_eq
  set V : DistOn upperHalfPlaneOpens → XCode nL nR × PCode :=
    fun f => (Ψ f, killB (Ψ f) (Fw (projIcc 0 1 zero_le_one (U f)))) with hV
  have hVm : Measurable V := hΨm.prodMk (measurable_killB.comp (hΨm.prodMk
    (hFwm.comp (continuous_projIcc.measurable.comp hUm))))
  have hlawV := map_field_eq_model hh₀ hΨm hUm hU01 hUlaw hB'm hFwm hFw
  -- the good set of code pairs
  set GY : Set (XCode nL nR × PCode) := Prod.fst ⁻¹' DetSet κ xL xR ρL ρR ∩
    ⋂ N : ℕ, Prod.snd ⁻¹' {c : PCode | UC c N} with hGYdef
  have hGYm : MeasurableSet GY :=
    (measurable_fst (measurableSet_detSet κ xL xR ρL ρR)).inter
      (MeasurableSet.iInter fun N => measurable_snd (measurableSet_UC N))
  have hGY : ∀ y ∈ GY, Continuous (noiseY y) ∧ IsIntegratedSLEPath κ xL xR ρL ρR (cw y.1) (cvL y.1)
      (cvR y.1) (noiseY y) (cζ y.1) := by
    rintro y ⟨⟨⟨⟨⟨hg, -, hp⟩, -⟩, -⟩, -⟩, hUC⟩
    have hUC' : ∀ N : ℕ, UC y.2 N := fun N => mem_iInter.1 hUC N
    refine ⟨continuous_noiseY hg.continuous_b (continuous_dec_of_UC hUC'), ?_⟩
    exact isIntegratedSLEPath_congr hp rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) fun t ht => noiseY_of_lt ht
  have hg₀m := measurable_modelMap hX₀m hB'm
  have hmodelGY : ∀ᵐ p ∂(P₀.prod P₀), modelMap X₀ B' p ∈ GY := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hX₀] with p hp
    refine ⟨hp.1, mem_iInter.2 fun N => ?_⟩
    change UC (killB (X₀ p.1) (enc fun t => B' t p.2)) N
    unfold killB
    split_ifs
    · exact uc_enc (hB'c p.2).continuousOn
    · exact uc_enc (f := fun _ => (0 : ℝ)) continuousOn_const
  set g : Ω → XCode nL nR × PCode := fun ω => V (h ω) with hg
  have hgm : Measurable g := hVm.comp hh
  have hlawg : P.map g = (P₀.prod P₀).map (modelMap X₀ B') := by
    rw [show g = V ∘ h from rfl, ← Measure.map_map hVm hh, hlaw]
    exact hlawV
  have hgGY : ∀ᵐ ω ∂P, g ω ∈ GY := by
    have h1 : ∀ᵐ y ∂(P.map g), y ∈ GY := by
      rw [hlawg]; exact (ae_map_iff hg₀m.aemeasurable hGYm).2 hmodelGY
    exact (ae_map_iff hgm.aemeasurable hGYm).1 h1
  exact ⟨_, _, isIntegratedSLEEvolution_of_map_eq (Wy := fun t y => cw y.1 t)
    (VLy := fun i t y => cvL y.1 i t) (VRy := fun j t y => cvR y.1 j t) (ζy := fun y => cζ y.1)
    (By := fun t y => noiseY y t) isMeasurableKilledDriving_codeY measurable_noiseY hg₀m hE₀ hgm hlawg
    (hgGY.mono fun ω hω => (hGY _ hω).1) (hgGY.mono fun ω hω => (hGY _ hω).2)⟩

end Realization

/-! ### Flow lines on a given field in the non-boundary regime -/

section FlowLine

/-- **Existence of flow lines on a given field from the §4.2 forms of Theorems 1.2–1.3.** For `0 < κ ≤ 4`, a
GFF `h` with finite piecewise-constant data, and a flow-line word with admissible side partial sums (Remark 4.1's
regime) all of whose couplings have field-determined histories (`hdet`, the §4.2 Theorem 1.2), there is a flow line
of `h` with this seed and angle. Traces are Aux. lemma 7 (`Zhan.aux7Statement`). The proof is the landed
`Exist.exists_isFlowLine_of_thm12_thm13_only` with the frozen Theorems 1.2–1.3 replaced by these inputs. -/
theorem exists_isFlowLine_of_det {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hadm : Sec4.HasAdmissiblePartialSums κ (flowLineRhoL κ b jumps x θ) (flowLineRhoR κ b jumps x θ)
      (flowLineXL b jumps x) (flowLineXR b jumps x))
    (hdet : LP.HasFieldDeterminedHistories.{u} κ (flowLineXL b jumps x) (flowLineXR b jumps x)
      (flowLineRhoL κ b jumps x θ) (flowLineRhoR κ b jumps x θ)) :
    ∃ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ P h η ζ := by
  have hF := Theorem15.isOrderedForceWord_flowLine b jumps x
  -- the reference coupling of the flow-line word (Theorem 1.1)
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hcoup⟩ :=
    Spec.Provider.exists_isOptionalHullCoupling.{u} (κ := κ) (xL := flowLineXL b jumps x)
      (xR := flowLineXR b jumps x) (ρL := flowLineRhoL κ b jumps x θ) (ρR := flowLineRhoR κ b jumps x θ) hκ hF
  -- §4.2's Theorem 1.2 and Aux. lemma 7 at this coupling
  have hΦ := LP.exists_measurable_lifetime_trace_eq_comp_field_of_isFieldDeterminedHistory hcoup
    (hdet P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ hcoup)
  have htr₀ : ∀ᵐ ω ∂P₀, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₀ t ω) (ζ₀ ω) η := by
    filter_upwards [Zhan.aux7Statement hκ hκ4 _ _ _ _ P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ hF hadm hcoup.1] with ω hω
    obtain ⟨hζ, ⟨η, hη⟩, -⟩ := hω
    exact ⟨η, by rw [hζ]; exact hη⟩
  -- the history is a Borel function of the field, and the driving evolution is realized on every space
  obtain ⟨Ψ, S, ηf, hΨm, hSm, hae, htr, hreal⟩ := exists_fieldDetermination_realization_of_det hκ hcoup hΦ htr₀
  set h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens :=
    fun ω => flowField x (θ * QuantumZipper.chiC κ) (h ω) with hh'def
  have hh' := isGFFWithBoundaryData_flowField hκ hb x θ hh
  obtain ⟨u, hu, -⟩ := Spec.Provider.existsUnique_isBoundedHarmonicExtension_forceBoundaryData (κ := κ)
    (ρL := flowLineRhoL κ b jumps x θ) (ρR := flowLineRhoR κ b jumps x θ) (vL := flowLineXL b jumps x)
    (vR := flowLineXR b jumps x)
  have hh₀ : IsGFFWithBoundaryData P₀ h₀
      (forceBoundaryData κ (flowLineRhoL κ b jumps x θ) (flowLineRhoR κ b jumps x θ) (flowLineXL b jumps x)
        (flowLineXR b jumps x)) (forceJumpSet (flowLineXL b jumps x) (flowLineXR b jumps x)) :=
    ⟨hcoup.2.1, hcoup.2.2.1⟩
  have hlaw : P.map h' = P₀.map h₀ := map_eq_of_isGFFWithBoundaryData hh' hh₀ hu
  -- realization on the given space, then the hull clauses (named input (i), proved)
  obtain ⟨𝓕, B, hE⟩ := hreal P h' hh'.1 hlaw
  have hdet : ∀ᵐ ω ∂P₀, (pathsOfCode (Ψ (h₀ ω))).1 = ζ₀ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω →
      (pathsOfCode (Ψ (h₀ ω))).2.1 t = W₀ t ω ∧ (∀ i, (pathsOfCode (Ψ (h₀ ω))).2.2.1 i t = VL₀ i t ω) ∧
        ∀ j, (pathsOfCode (Ψ (h₀ ω))).2.2.2 j t = VR₀ j t ω := by
    filter_upwards [hae] with ω hω
    exact ⟨hω.2.1, hω.2.2⟩
  have hdatum : IsFieldRealizationDatum κ (flowLineXL b jumps x) (flowLineXR b jumps x)
      (flowLineRhoL κ b jumps x θ) (flowLineRhoR κ b jumps x θ) (pathsOfCode ∘ Ψ) P h' :=
    ⟨hκ, hF, measurable_pathsOfCode.comp hΨm, hh'.1, Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hcoup,
      hdet, hlaw⟩
  have hcoupΩ := hullClauseTransferStatement κ _ _ _ _ (pathsOfCode ∘ Ψ) P h' hdatum 𝓕 B hE
  -- the field lies in the good set almost surely
  have hS₀ : ∀ᵐ f ∂(P₀.map h₀), f ∈ S :=
    (ae_map_iff hcoup.2.1.aemeasurable hSm).2 (hae.mono fun ω hω => hω.1)
  rw [← hlaw] at hS₀
  have hSΩ : ∀ᵐ ω ∂P, h' ω ∈ S := (ae_map_iff hh'.1.aemeasurable hSm).1 hS₀
  refine ⟨fun ω t => ηf (h' ω) t + x, fun ω => cζ (Ψ (h' ω)), h', 𝓕, _, _, _, B,
    fun ω => isTranslateAddConst_flowField x _ (h ω), hcoupΩ, ?_⟩
  filter_upwards [hSΩ] with ω hω
  have e : (fun t => ηf (h' ω) t + (x : ℂ) - x) = ηf (h' ω) := by
    funext t; ring
  rw [e]
  exact htr _ hω

/-! ### The named input: the §4.2 reference coupling under (4.4) -/

/-- **Named input: the reference coupling of Theorem 1.2 under (4.4)** (specification §4.2, proof of Theorem 1.2 for
`κ ∈ (0, 4)` assuming (4.4), p. 122: "Proposition 4.11 implies that the flow line `η` … is equal to the left boundary
of the counterflow line `η′` …, where `η, η′, h` are coupled together so that `η` is conditionally independent of `η′`
given `h`. Since `η` and `η′` are conditionally independent given `h`, it follows that `η` is almost surely determined
by `h`"). For `0 < κ < 4` and every ordered force word satisfying (4.4), some coupling with the optional hull
specification of Theorem 1.1 has its killed driving history determined by its field. This is the reference half of
§4.2's proof; the transfer half (Aux. lemma 23) is proved (`Sec4.hasFieldDeterminedHistories_of_cond44_of_reference`).
It does not use Lemma 7.1. **Not proved in Lean** (PROVE-SEC4-B5, "What remains" 4: Proposition 4.11 for the
reference triple). -/
def Cond44ReferenceStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR → Sec4.Cond44 κ ρL ρR →
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h ∧ LP.IsFieldDeterminedHistory P h W VL VR ζ

/-- **Theorem 1.2 under (4.4), every coupling** (§4.2): from the reference (`Cond44ReferenceStatement`) and Aux.
lemma 23 (proved). -/
theorem hasFieldDeterminedHistories_of_cond44 (href : Cond44ReferenceStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR) :
    LP.HasFieldDeterminedHistories.{u} κ xL xR ρL ρR :=
  Sec4.hasFieldDeterminedHistories_of_cond44_of_reference.{u, u} hκ hκ4 hF h44 (href κ hκ hκ4 xL xR ρL ρR hF h44)

/-! ### (4.4) for the flow lines of Figure 7.1 -/

/-- A sum over an initial segment `{i | i < j}`, `1 ≤ j ≤ n`, of `Fin n` with `n = 1` is the single value. -/
theorem sum_filter_lt_of_eq_one {n : ℕ} (hn : n = 1) (f : Fin n → ℝ) {c : ℝ} (hf : ∀ i, f i = c) {j : ℕ}
    (hj1 : 1 ≤ j) (hjn : j ≤ n) : ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < j), f i = c := by
  subst hn
  have hj : j = 1 := le_antisymm hjn hj1
  subst hj
  rw [Finset.filter_true_of_mem fun i _ => i.isLt, Fin.sum_univ_one, hf]

/-- **(4.4) for the angle-`θ` flow line of the data of Figure 7.1** (`−a` left of `0`, `b` right of `0`): the
weights are `ρ^L = (a − θχ)/λ − 1` and `ρ^R = (b + θχ)/λ − 1`, so (4.4) holds as soon as `a − θχ ≥ λ − πχ` and
`b + θχ ≥ λ`. -/
theorem cond44_flowLine_prop74Data {κ : ℝ} (hκ : 0 < κ) {a b θ : ℝ}
    (ha : sleLambda κ - π * chiC κ + θ * chiC κ ≤ a) (hb : sleLambda κ - θ * chiC κ ≤ b) :
    Sec4.Cond44 κ (flowLineRhoL κ (prop74Data a b) {0} 0 θ) (flowLineRhoR κ (prop74Data a b) {0} 0 θ) := by
  have hlam := Sec4.sleLambda_pos hκ
  have e := Sec4.sleLambda_sub_pi_mul_chiC hκ
  refine ⟨fun j hj1 hjn => ?_, fun j hj1 hjn => ?_⟩
  · rw [sum_filter_lt_of_eq_one (flowLineNL_prop74Data a b) _ (Sec7.flowLineRhoL_prop74Data κ a b θ) hj1 hjn]
    rw [le_sub_iff_add_le, le_div_iff₀ hlam]
    linarith
  · rw [sum_filter_lt_of_eq_one (flowLineNR_prop74Data a b) _ (Sec7.flowLineRhoR_prop74Data κ a b θ) hj1 hjn]
    rw [sub_nonneg, le_div_iff₀ hlam]
    linarith

end FlowLine

/-! ### The three-curve space -/

section Version

open Lemma71G

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {θ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **One flow line of the three-curve configuration with all of Lemma 6.2's hypotheses, from a Borel map of the
field for this flow line** (the landed `Lemma71G.exists_lemma62Version` with its use of the all-words Lemma 7.5 replaced
by the determination of this one flow line, `hΦ`; same proof). -/
theorem exists_lemma62Version_of_map (hA56 : Restart.RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b J) (hh : IsGFFWithBoundaryData P h b J)
    (hL : ∀ x : ℝ, x < 0 → x ∉ J → b x + θ * chiC κ ≤ -sleLambda κ + π * chiC κ)
    (hR : ∀ x : ℝ, 0 < x → x ∉ J → sleLambda κ - π * chiC κ ≤ b x + θ * chiC κ)
    (hη : IsFlowLine κ b J 0 θ P h η ζ)
    (hΦ : ∃ Φ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ᵐ ω ∂P, (Φ (h ω)).1 = ζ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → (Φ (h ω)).2 t = η ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b J u₀) :
    ∃ η' : Ω → ℝ≥0 → ℂ, IsLemma62Curve η' (WholeField.centredField h u₀) P ∧
      ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ t, η' ω t = η ω t) ∧ ∀ t : ℝ≥0, ∀ x : ℝ, x ≠ 0 → η' ω t ≠ x := by
  classical
  obtain ⟨Φ, hΦm, hΦh⟩ := hΦ
  obtain ⟨η'', hη''m, hη''⟩ := Restart.exists_measurable_version_of_isFlowLine hη
  have hT := IsFlowLine.ae_tendsto_angle hκ hκ4.le hb hL hR hη
  obtain ⟨𝓕, W, VL, VR, B, hev, htr⟩ := IsFlowLine.exists_evolution_angle hη
  -- the good event
  set good : Ω → Prop := fun ω => ζ ω = ⊤ ∧ (∀ t, η'' ω t = η ω t) ∧ Continuous (η ω) ∧ η ω 0 = 0 ∧
    (∀ t, η ω t ∈ Hbar) ∧ (∀ t : ℝ≥0, ∀ x : ℝ, x ≠ 0 → η ω t ≠ x) ∧ Tendsto (fun t => ‖η ω t‖) atTop atTop ∧
    ∀ t, (Φ (h ω)).2 t = η ω t with hgooddef
  have hgood : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hT, hη'', htr, hev.2.2.2.2, hΦh] with ω hT hη'' htr hpath hΦω
    obtain ⟨hζ, hne, hlim⟩ := hT
    obtain ⟨hw0, -, -, hcw, -⟩ := hpath
    rw [hζ] at htr hη'' hΦω hcw
    refine ⟨hζ, fun t => hη'' t le_top, ?_, htr.1, fun t => ?_, hne, hlim, fun t => hΦω.2 t le_top⟩
    · rw [← continuousOn_univ]
      exact htr.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top
    · exact Sec7.IsGeneratingTrace.mem_Hbar htr hcw hw0 le_top
  set G : Set Ω := (toMeasurable P {ω | ¬ good ω})ᶜ with hGdef
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGg : ∀ ω ∈ G, good ω := fun ω hω => by
    by_contra hng
    exact hω (subset_toMeasurable _ _ hng)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    have e : {ω | ¬ ω ∈ G} = toMeasurable P {ω | ¬ good ω} := by ext ω; simp [hGdef]
    rw [e, measure_toMeasurable]
    exact ae_iff.1 hgood
  set η' : Ω → ℝ≥0 → ℂ := fun ω t => if ω ∈ G then η'' ω t else 0 with hη'def
  have hη'G : ∀ ω ∈ G, η' ω = η ω := fun ω hω => funext fun t => by
    simp only [hη'def, hω, ↓reduceIte]
    exact (hGg ω hω).2.1 t
  have hη'nG : ∀ ω ∉ G, η' ω = fun _ => 0 := fun ω hω => funext fun t => by
    simp only [hη'def, hω, ↓reduceIte]
  have hc : ∀ ω, Continuous (η' ω) := fun ω => by
    by_cases hω : ω ∈ G
    · rw [hη'G ω hω]; exact (hGg ω hω).2.2.1
    · rw [hη'nG ω hω]; exact continuous_const
  have h0 : ∀ ω, η' ω 0 = 0 := fun ω => by
    by_cases hω : ω ∈ G
    · rw [hη'G ω hω]; exact (hGg ω hω).2.2.2.1
    · rw [hη'nG ω hω]
  have hm : ∀ t, Measurable fun ω => η' ω t := fun t =>
    Measurable.ite hGm (hη''m t) measurable_const
  have hhm0 : Measurable (WholeField.centredField h u₀) := WholeField.measurable_centredField hh.1 u₀
  refine ⟨η', ⟨hc, h0, fun ω t => ?_, hm, fun t => ?_, ?_, ?_⟩, ?_⟩
  · by_cases hω : ω ∈ G
    · rw [hη'G ω hω]; exact (hGg ω hω).2.2.2.2.1 t
    · rw [hη'nG ω hω]; simp
  · refine ⟨fun g => (Φ (g + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀)).2 t,
      (measurable_pi_apply t).comp (measurable_snd.comp (hΦm.comp (WholeField.measurable_add_dist _))), ?_⟩
    filter_upwards [hGae] with ω hω
    simp only [WholeField.centredField, sub_add_cancel]
    rw [hη'G ω hω, (hGg ω hω).2.2.2.2.2.2.2 t]
  · -- history locality of the complete path from that of its finite prefixes (Aux. lemma 56)
    have h0H : (0 : ℂ) ∉ H := fun h0' => by
      have h' : (0 : ℝ) < (0 : ℂ).im := h0'
      simp at h'
    refine isEntranceHistoryLocal_of_capAt hhm0 hc hm (fun ω => by rw [h0 ω]; exact h0H) ?_
    intro n
    refine Restart.IsEntranceKilledHistoryLocal.isEntranceHistoryLocal
      (ζ := fun ω => Restart.cutLife (ζ ω) n) ?_
    refine hA56 κ hκ hκ4 b J hb 0 θ P h hh η ζ hη u₀ hu₀ n (fun ω => capAt (η' ω) n)
      (fun ω => continuous_capAt (hc ω) n) (fun t => hm _) ?_
    filter_upwards [hGae] with ω hω t
    rw [(hGg ω hω).1, capTime_top]
    show η' ω (min t n) = η ω (min t n)
    rw [hη'G ω hω]
  · filter_upwards [hGae] with ω hω
    rw [hη'G ω hω, ← tendsto_norm_atTop_iff_cobounded]
    exact (hGg ω hω).2.2.2.2.2.2.1
  · filter_upwards [hGae] with ω hω
    have hg := hGg ω hω
    exact ⟨hg.1, fun t => by rw [hη'G ω hω], fun t x hx => by rw [hη'G ω hω]; exact hg.2.2.2.2.2.1 t x hx⟩


end Version

/-- **The three-curve space of §7.1 from the non-boundary (§4.2) inputs.** `Lemma71G.exists_threeCurveSpace` with its
four named inputs (the frozen Theorems 1.2–1.3, the all-words Lemma 7.5 and Aux. lemma 56) replaced by the §4.2
reference `Cond44ReferenceStatement` and Aux. lemma 56 at first entrance times; the right boundary value is taken
`b ≥ λ − θ₁χ` so that the three flow-line words satisfy (4.4). For `0 < κ < 4` and `θ₁ < 0 < θ₂`, one probability
space carries a GFF `h` with the data of Figure 7.1, its bounded harmonic extension `u₀`, and its three flow lines from
`0` (`β = η_{θ₂}`, `α = η_{θ₁}`, `γ = η_0`), each with Lemma 6.2's hypotheses for the centred field, almost surely
with infinite lifetime and no contact with `ℝ ∖ {0}`. Conditional helper. -/
theorem exists_threeCurveSpace_nb (href : Cond44ReferenceStatement.{u})
    (hA56 : Restart.RetainedRangeEntranceStatement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ a b : ℝ} (hθ₁ : θ₁ < 0) (hθ₂ : 0 < θ₂)
    (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a) (hb : sleLambda κ - θ₁ * chiC κ ≤ b) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) (β α γ : Ω → ℝ≥0 → ℂ) (ζβ ζα ζγ : Ω → ℝ≥0∞),
      IsGFFWithBoundaryData P h (prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ) ∧
      IsBoundedHarmonicExtension (prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ) u₀ ∧
      LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P ∧
      IsFlowLine κ (prop74Data a b) {0} 0 θ₂ P h β ζβ ∧ IsFlowLine κ (prop74Data a b) {0} 0 θ₁ P h α ζα ∧
      IsFlowLine κ (prop74Data a b) {0} 0 0 P h γ ζγ ∧
      Lemma71G.IsLemma62Curve β (WholeField.centredField h u₀) P ∧
      Lemma71G.IsLemma62Curve α (WholeField.centredField h u₀) P ∧
      Lemma71G.IsLemma62Curve γ (WholeField.centredField h u₀) P ∧
      ∀ᵐ ω ∂P, ζβ ω = ⊤ ∧ ζα ω = ⊤ ∧ ζγ ω = ⊤ ∧
        ∀ i (t : ℝ≥0) (x : ℝ), x ≠ 0 → Sec6.Three.threeCurves β α γ i ω t ≠ x := by
  obtain ⟨Ω, mΩ, P, hP, h, hh⟩ := Lemma71G.exists_isGFFWithBoundaryData_prop74Data.{u} hκ a b
  have hbpc := isPiecewiseConstant_prop74Data a b
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hbpc
  have hχ := Sec4.chiC_pos hκ hκ4
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le hχ.le
  have hb41 : sleLambda κ - π * chiC κ - θ₁ * chiC κ ≤ b := by linarith
  have hF := Theorem15.isOrderedForceWord_flowLine (prop74Data a b) {0} 0
  -- one flow line per angle, and its version with Lemma 6.2's hypotheses
  have hcurve : ∀ θ : ℝ, θ₁ ≤ θ → θ ≤ θ₂ → ∃ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
      IsFlowLine κ (prop74Data a b) {0} 0 θ P h η ζ ∧
        Lemma71G.IsLemma62Curve η (WholeField.centredField h u₀) P ∧
        ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ (t : ℝ≥0) (x : ℝ), x ≠ 0 → η ω t ≠ x := by
    intro θ h1 h2
    have hθχ1 : θ₁ * chiC κ ≤ θ * chiC κ := mul_le_mul_of_nonneg_right h1 hχ.le
    have hθχ2 : θ * chiC κ ≤ θ₂ * chiC κ := mul_le_mul_of_nonneg_right h2 hχ.le
    have h44 := cond44_flowLine_prop74Data (θ := θ) hκ (a := a) (b := b) (by linarith) (by linarith)
    have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
    have hdet : LP.HasFieldDeterminedHistories.{u} κ (flowLineXL (prop74Data a b) {0} 0)
        (flowLineXR (prop74Data a b) {0} 0) (flowLineRhoL κ (prop74Data a b) {0} 0 θ)
        (flowLineRhoR κ (prop74Data a b) {0} 0 θ) := hasFieldDeterminedHistories_of_cond44 href hκ hκ4 hF h44
    obtain ⟨η₀, ζ, hη₀⟩ := exists_isFlowLine_of_det hκ hκ4.le hbpc hh hadm hdet
    -- Lemma 7.5 for this flow line in the non-boundary regime (Aux. 23 and the reference)
    obtain ⟨Φ, hΦm, hΦ⟩ := Lemma75Bridge.exists_flowLineMap_of_admissible hκ hκ4.le hadm
      (href κ hκ hκ4 _ _ _ _ hF h44)
    obtain ⟨hL, hR⟩ := Lemma71G.prop74Data_remark41 hκ hκ4 h1 h2 ha hb41
    obtain ⟨η, hη, hae⟩ := exists_lemma62Version_of_map hA56 hκ hκ4 hbpc hh hL hR hη₀
      ⟨Φ, hΦm, hΦ P h hh η₀ ζ hη₀⟩ hu₀
    refine ⟨η, ζ, Lemma71G.IsFlowLine.congr_ae hη₀ (hae.mono fun ω hω => hω.2.1), hη, ?_⟩
    filter_upwards [hae] with ω hω
    exact ⟨hω.1, hω.2.2⟩
  obtain ⟨β, ζβ, hβf, hβ, hβa⟩ := hcurve θ₂ (hθ₁.trans hθ₂).le le_rfl
  obtain ⟨α, ζα, hαf, hα, hαa⟩ := hcurve θ₁ le_rfl (hθ₁.trans hθ₂).le
  obtain ⟨γ, ζγ, hγf, hγ, hγa⟩ := hcurve 0 hθ₁.le hθ₂.le
  refine ⟨Ω, mΩ, P, hP, h, u₀, β, α, γ, ζβ, ζα, ζγ, hh, hu₀,
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀, hβf, hαf, hγf, hβ, hα, hγ, ?_⟩
  filter_upwards [hβa, hαa, hγa] with ω h1 h2 h3
  refine ⟨h1.1, h2.1, h3.1, fun i t x hx => ?_⟩
  fin_cases i
  · exact h1.2 t x hx
  · exact h2.2 t x hx
  · exact h3.2 t x hx

/-! ### The order of the three curves -/

/-- **Named input: Proposition 5.5 in `ℍ`, whole curves** (specification p. 135, (5.2), and the last sentence of the
proof, p. 136: "The result when the `η_{θᵢ}`, `i = 1, 2`, are flow lines of a GFF on `ℍ` follows from the result on
`𝒮` and Proposition 3.4"). For `0 < κ < 4`, the data of Figure 7.1 (`−a` on `ℝ₋`, `b` on `ℝ₊`) and angles
`(λ − b)/χ ≤ θ₁ < θ₂ ≤ (a + πχ − λ)/χ` (here multiplied out by `χ > 0`), the flow line `η_{θ₂}` almost surely lies to
the left of `η_{θ₁}`: when both lifetimes are infinite, the range of `η_{θ₂}` lies in the closed left side of `η_{θ₁}`
(the frozen W0 notion `closedLeftSide`). It is proved in §5 from Propositions 5.1, 4.11 and 3.4; it does not use
Lemma 7.1. **Not proved in Lean** (the landed form is the strip statement `Sec5.prop55_of_prop51`, conditional on
`Sec5.Prop51Statement`). -/
def Prop55HalfPlaneStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ a b θ₁ θ₂ : ℝ, θ₁ < θ₂ →
    sleLambda κ - θ₁ * chiC κ ≤ b → sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h (prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ) →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ (prop74Data a b) {0} 0 θ₁ P h η₁ ζ₁ → IsFlowLine κ (prop74Data a b) {0} 0 θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ζ₁ ω = ⊤ → ζ₂ ω = ⊤ → range (η₂ ω) ⊆ closedLeftSide (η₁ ω)

/-- **The ordered three-curve space of §7.1** ("Assume that `a, b` are chosen sufficiently large so that Proposition
5.5 applies to `η_{θ₁}`, `η`, and `η_{θ₂}`. Thus we know that `η_{θ₁}` lies to the right of `η` which in turn lies
to the right of `η_{θ₂}`", p. 221): `exists_threeCurveSpace_nb` together with, almost surely, the closed-side order of
the three complete curves (`β = η_{θ₂}` left of `γ = η` left of `α = η_{θ₁}`, and `β` left of `α`). Named inputs:
the §4.2 reference, Aux. lemma 56 at first entrance times and Proposition 5.5 in `ℍ`. Conditional helper. -/
theorem exists_threeCurveSpace_ordered (href : Cond44ReferenceStatement.{u})
    (hA56 : Restart.RetainedRangeEntranceStatement.{u}) (h55 : Prop55HalfPlaneStatement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ a b : ℝ} (hθ₁ : θ₁ < 0) (hθ₂ : 0 < θ₂)
    (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a) (hb : sleLambda κ - θ₁ * chiC κ ≤ b) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) (β α γ : Ω → ℝ≥0 → ℂ) (ζβ ζα ζγ : Ω → ℝ≥0∞),
      IsGFFWithBoundaryData P h (prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ) ∧
      IsBoundedHarmonicExtension (prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ) u₀ ∧
      LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P ∧
      IsFlowLine κ (prop74Data a b) {0} 0 θ₂ P h β ζβ ∧ IsFlowLine κ (prop74Data a b) {0} 0 θ₁ P h α ζα ∧
      IsFlowLine κ (prop74Data a b) {0} 0 0 P h γ ζγ ∧
      Lemma71G.IsLemma62Curve β (WholeField.centredField h u₀) P ∧
      Lemma71G.IsLemma62Curve α (WholeField.centredField h u₀) P ∧
      Lemma71G.IsLemma62Curve γ (WholeField.centredField h u₀) P ∧
      ∀ᵐ ω ∂P, ζβ ω = ⊤ ∧ ζα ω = ⊤ ∧ ζγ ω = ⊤ ∧
        (∀ i (t : ℝ≥0) (x : ℝ), x ≠ 0 → Sec6.Three.threeCurves β α γ i ω t ≠ x) ∧
        range (β ω) ⊆ closedLeftSide (γ ω) ∧ range (γ ω) ⊆ closedLeftSide (α ω) ∧
        range (β ω) ⊆ closedLeftSide (α ω) := by
  obtain ⟨Ω, mΩ, P, hP, h, u₀, β, α, γ, ζβ, ζα, ζγ, hh, hu₀, hz, hβf, hαf, hγf, hβ, hα, hγ, hae⟩ :=
    exists_threeCurveSpace_nb href hA56 hκ hκ4 hθ₁ hθ₂ ha hb
  have hχ := Sec4.chiC_pos hκ hκ4
  have h1 : 0 < θ₂ * chiC κ := mul_pos hθ₂ hχ
  have h2 : θ₁ * chiC κ < 0 := mul_neg_of_neg_of_pos hθ₁ hχ
  have hγβ := h55 κ hκ hκ4 a b 0 θ₂ hθ₂ (by linarith) ha P h hh γ β ζγ ζβ hγf hβf
  have hαγ := h55 κ hκ hκ4 a b θ₁ 0 hθ₁ hb (by linarith) P h hh α γ ζα ζγ hαf hγf
  have hαβ := h55 κ hκ hκ4 a b θ₁ θ₂ (hθ₁.trans hθ₂) hb ha P h hh α β ζα ζβ hαf hβf
  refine ⟨Ω, mΩ, P, hP, h, u₀, β, α, γ, ζβ, ζα, ζγ, hh, hu₀, hz, hβf, hαf, hγf, hβ, hα, hγ, ?_⟩
  filter_upwards [hae, hγβ, hαγ, hαβ] with ω hω hγβω hαγω hαβω
  obtain ⟨hζβ, hζα, hζγ, hne⟩ := hω
  exact ⟨hζβ, hζα, hζγ, hne, hγβω hζγ hζβ, hαγω hζα hζγ, hαβω hζα hζβ⟩

end InteractingSLE.Sec7.Lemma71H
