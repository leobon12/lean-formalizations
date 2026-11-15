/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripSysBorel
import InteractingSLE.Spec.ZhanGT4.A1RefCDLive

/-!
# A.1's complete marginal laws on standard Borel path spaces, regular at every sample

Packet PROVE-A1-MARG (R76). Source: Astra, *Follow-up 5* §1.3 (`source/external/AstraIG1/ig1_followup5.txt`
L197–L222): the coupling of A.1 lives on a product of two standard Borel path spaces carrying the two **complete**
marginal laws (the integrated evolutions of the two curves, with their full records).

`A1Core.IsRectImageCore` asks for measurability clauses (m1)–(m4) at **every** sample (progressive measurability of
the live events and image words; joint measurability of the canonical image). They hold when every sample of the path
space is a solution path. This file builds such marginals:

* `exists_code_evolution`: Theorem 2.2's evolution read through the dyadic code (`Sec2.Assembly.codeOf`, as in
  `Sec7.StripSysBorel.isIntegratedSLEEvolution_code`), with the extra information that almost every code lies in the
  measurable solution relation `Sec2.Assembly.CRel`;
* `RegCode a xL xR ρL ρR`: the subtype of codes in `CRel` (standard Borel: a measurable subset of a standard Borel
  space), with the restricted law;
* `killedVersion`: the progressive version of a process, killed at the lifetime to a constant (`A1RefCD.regularized`
  with an arbitrary fill value), strongly progressive (`isStronglyProgressive_killedVersion`);
* **`IsRegMarginal`**: an integrated evolution whose pathwise relation holds at every sample and whose coordinates are
  strongly progressive; **`exists_isRegMarginal`**: such a marginal exists on a standard Borel space for every ordered
  force word.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Marg

open Sec2.Assembly Sec2.Restart

variable {nL nR : ℕ}

/-! ### Theorem 2.2 on the code space, with the solution relation almost surely -/

/-- **Theorem 2.2's evolution on the code space, concentrated on the solution relation.** Every integrated evolution
has a copy on `XCode nL nR` (decoded paths, natural filtration) whose law gives full mass to `CRel`. The proof is that
of `Sec7.StripSysBorel.isIntegratedSLEEvolution_code`, keeping the almost sure membership. -/
theorem exists_code_evolution {a : ℝ} (ha : 0 < a) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω₀ : Type*} {m₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀}
    [IsProbabilityMeasure P₀] {𝓕 : Filtration ℝ≥0 m₀} {W : ℝ≥0 → Ω₀ → ℝ} {VL : Fin nL → ℝ≥0 → Ω₀ → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B : ℝ≥0 → Ω₀ → ℝ} {ζ : Ω₀ → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P₀ 𝓕 W VL VR B ζ) :
    ∃ (μ : Measure (XCode nL nR)) (_ : IsProbabilityMeasure μ) (𝓗 : Filtration ℝ≥0 (inferInstance :
      MeasurableSpace (XCode nL nR))),
      IsIntegratedSLEEvolution a xL xR ρL ρR μ 𝓗 (fun t x => cw x t) (fun i t x => cvL x i t)
        (fun j t x => cvR x j t) (fun t x => cb x t) cζ ∧ ∀ᵐ x ∂μ, x ∈ CRel a xL xR ρL ρR := by
  obtain ⟨B', hB'm, hB'c, -, hae⟩ := Sec2.Restart.exists_continuous_version hE.1
  set Φ := codeOf xL xR B' W VL VR ζ with hΦdef
  have hΦ : Measurable Φ := measurable_codeOf hB'm hE.2.1 hE.2.2.1 hE.2.2.2.1
  have hX := Sec7.StripSysBorel.isMeasurableKilledDriving_code (nL := nL) (nR := nR)
  have hB : ∀ t, Measurable fun x : XCode nL nR => cb x t := measurable_cb_at
  have hmem := ae_codeOf_mem ha hE hB'c hae
  have hE₀ : IsIntegratedSLEEvolution a xL xR ρL ρR P₀ (usualAugmentation 𝓕 P₀)
      (fun t ω => cw (Φ ω) t) (fun i t ω => cvL (Φ ω) i t) (fun j t ω => cvR (Φ ω) j t)
      (fun t ω => cb (Φ ω) t) (fun ω => cζ (Φ ω)) := by
    refine Sec7.StripSysBorel.isIntegratedSLEEvolution_of_ae_agree
      (Ito.isIntegratedSLEEvolution_usualAugmentation hE)
      (fun t N hN h0 => Ito.measurableSet_usualAugmentation_of_null hN h0 t)
      (Exist.isMeasurableKilledDriving_comp hX hΦ) (fun t => (hB t).comp hΦ) ?_ ?_
    · filter_upwards [hmem, hae] with ω h1 h2
      refine ⟨rfl, fun t ht => ⟨(h1.2 t ht).1, (h1.2 t ht).2.1, (h1.2 t ht).2.2.1⟩, fun t => ?_⟩
      show dec (enc (B' · ω)) t = B t ω
      rw [dec_enc (hB'c ω).continuousWithinAt, h2 t]
    · filter_upwards [hmem] with ω h1
      exact h1.1.1.2.2
  have hμ : ∀ᵐ x ∂(P₀.map Φ), x ∈ CRel a xL xR ρL ρR :=
    (ae_map_iff hΦ.aemeasurable (measurableSet_cRel a xL xR ρL ρR)).2 (hmem.mono fun ω h => h.1)
  refine ⟨P₀.map Φ, inferInstance, _,
    Exist.isIntegratedSLEEvolution_of_map_eq hX hB hΦ hE₀ (g := id) measurable_id Measure.map_id ?_ ?_, hμ⟩
  · filter_upwards [hμ] with x hx
    exact hx.1.1.continuous_b
  · filter_upwards [hμ] with x hx
    exact hx.1.2.2

/-! ### The regular code space -/

/-- **The regular code space**: codes in the solution relation `CRel` (every sample is a solution path). -/
abbrev RegCode (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Type :=
  {x : XCode nL nR // x ∈ CRel a xL xR ρL ρR}

instance instStandardBorelSpaceRegCode (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) : StandardBorelSpace (RegCode a xL xR ρL ρR) :=
  (measurableSet_cRel a xL xR ρL ρR).standardBorel

/-- Every sample of the regular code space is a solution path. -/
theorem RegCode.isIntegratedSLEPath {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (x : RegCode a xL xR ρL ρR) :
    IsIntegratedSLEPath a xL xR ρL ρR (cw x.1) (cvL x.1) (cvR x.1) (cb x.1) (cζ x.1) :=
  x.2.1.2.2

/-! ### Killed progressive versions -/

section Killed

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- The progressive version of `X` before the lifetime `ζ`, killed to the constant `c` from `ζ` on. -/
def killedVersion (ζ : Ω → ℝ≥0∞) (X : ℝ≥0 → Ω → ℝ) (c : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : ℝ≥0∞) < ζ ω then progVersion ζ X t ω else c

/-- The killed version agrees with the process before the lifetime, at every sample continuous there. -/
theorem killedVersion_eq {ζ : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ} {c : ℝ} {ω : Ω}
    (hc : ContinuousOn (X · ω) {s | (s : ℝ≥0∞) < ζ ω}) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ ω) :
    killedVersion ζ X c t ω = X t ω := by
  simp only [killedVersion, ht, ↓reduceIte, progVersion_eq hc ht]

theorem killedVersion_of_le {ζ : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ} {c : ℝ} {ω : Ω} {t : ℝ≥0}
    (ht : ζ ω ≤ (t : ℝ≥0∞)) : killedVersion ζ X c t ω = c := by
  simp only [killedVersion, not_lt.2 ht, ↓reduceIte]

/-- The event `{t < ζ}` is jointly measurable on `[0, t] × Ω` for the filtration at `t`. -/
theorem measurableSet_lt_lifetime_prod {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} (ha : AdaptedBefore 𝓕 ζ W)
    (t : ℝ≥0) : MeasurableSet[(inferInstance : MeasurableSpace (Iic t)).prod (𝓕 t)]
      {p : Iic t × Ω | (p.1.val : ℝ≥0∞) < ζ p.2} := by
  have hζ := Ito.isStoppingTime_lifetime ha
  have hm : Measurable[𝓕 t] (fun ω => min (ζ ω : WithTop ℝ≥0) t) :=
    (hζ.min_const t).measurable_of_le (fun _ => min_le_right _ _)
  have hlt : MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
    convert (hζ.measurableSet_le t).compl using 1
    ext ω
    change (t : ℝ≥0∞) < ζ ω ↔ ¬ ζ ω ≤ (t : ℝ≥0∞)
    exact lt_iff_not_ge
  have he : {p : Iic t × Ω | (p.1.val : ℝ≥0∞) < ζ p.2} =
      {p | (p.1.val : WithTop ℝ≥0) < min (ζ p.2 : WithTop ℝ≥0) t} ∪ {p | (t : ℝ≥0∞) < ζ p.2} := by
    ext p
    change (p.1.val : WithTop ℝ≥0) < ζ p.2 ↔
      (p.1.val : WithTop ℝ≥0) < min (ζ p.2 : WithTop ℝ≥0) t ∨ (t : WithTop ℝ≥0) < ζ p.2
    constructor
    · intro h
      have hpt : p.1.val ≤ t := p.1.property
      rcases hpt.lt_or_eq with hpt | hpt
      · exact Or.inl (lt_min h (WithTop.coe_lt_coe.2 hpt))
      · exact Or.inr (by simpa only [hpt] using h)
    · rintro (h | h)
      · exact (lt_min_iff.1 h).1
      · exact (WithTop.coe_le_coe.2 p.1.property).trans_lt h
  rw [he]
  exact (measurableSet_lt (WithTop.measurable_coe.comp (measurable_subtype_coe.comp measurable_fst))
    (hm.comp measurable_snd)).union (measurable_snd hlt)

/-- **The killed version is strongly progressive** (as `A1RefCD.isStronglyProgressive_regularized`, any fill). -/
theorem isStronglyProgressive_killedVersion {ζ : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ} (ha : AdaptedBefore 𝓕 ζ X)
    (c : ℝ) : IsStronglyProgressive 𝓕 (killedVersion ζ X c) := fun t =>
  StronglyMeasurable.ite (measurableSet_lt_lifetime_prod ha t) (isStronglyProgressive_progVersion ha t)
    stronglyMeasurable_const

end Killed

/-! ### Solution paths are determined before the lifetime -/

/-- **The pathwise relation only reads the paths before the lifetime** (and their values at time `0`). -/
theorem isIntegratedSLEPath_congr {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {w w' : ℝ≥0 → ℝ} {vL vL' : Fin nL → ℝ≥0 → ℝ} {vR vR' : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (hw0 : w' 0 = 0)
    (hL0 : ∀ i, vL' i 0 = xL i) (hR0 : ∀ i, vR' i 0 = xR i)
    (hw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w' t = w t) (hL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ i, vL' i t = vL i t)
    (hR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ i, vR' i t = vR i t) :
    IsIntegratedSLEPath a xL xR ρL ρR w' vL' vR' b ζ := by
  obtain ⟨-, -, -, hcw, hcL, hcR, hanL, hLw, hwR, hmR, higL, higR, hweq, hLeq, hReq, hcolL, hcolR, hnt, hth0,
    hthT⟩ := h
  have hset : ∀ s : ℝ, 0 ≤ s → (s.toNNReal : ℝ≥0∞) < ζ → w' s.toNNReal = w s.toNNReal ∧
      (∀ i, vL' i s.toNNReal = vL i s.toNNReal) ∧ ∀ i, vR' i s.toNNReal = vR i s.toNNReal :=
    fun s _ hs => ⟨hw _ hs, hL _ hs, hR _ hs⟩
  -- interval integrands agree on `[0, t]` for `t < ζ`
  have hIcc : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ s ∈ Set.uIcc (0 : ℝ) t, (s.toNNReal : ℝ≥0∞) < ζ := by
    intro t ht s hs
    rw [Set.uIcc_of_le t.coe_nonneg] at hs
    exact (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)).trans_lt ht
  refine ⟨hw0, hL0, hR0, hcw.congr fun t ht => hw t ht, fun i => (hcL i).congr fun t ht => hL t ht i,
    fun i => (hcR i).congr fun t ht => hR t ht i, fun t ht => ?_, fun t ht i => ?_, fun t ht i => ?_,
    fun t ht => ?_, fun t ht i => ?_, fun t ht i => ?_, fun t ht => ?_, fun t ht i => ?_, fun t ht i => ?_,
    fun i => ?_, fun i => ?_, fun t ht => ?_, hth0, fun T hT hTζ w₀ vL₀ vR₀ hlim => ?_⟩
  · have e : (fun i => vL' i t) = fun i => vL i t := funext (hL t ht)
    simp only [e]; exact hanL t ht
  · rw [hL t ht i, hw t ht]; exact hLw t ht i
  · rw [hR t ht i, hw t ht]; exact hwR t ht i
  · have e : (fun i => vR' i t) = fun i => vR i t := funext (hR t ht)
    simp only [e]; exact hmR t ht
  · refine (higL t ht i).congr fun s hs => ?_
    have hs' := hIcc t ht s (Set.uIoc_subset_uIcc hs)
    simp only [hw _ hs', hL _ hs' i]
  · refine (higR t ht i).congr fun s hs => ?_
    have hs' := hIcc t ht s (Set.uIoc_subset_uIcc hs)
    simp only [hw _ hs', hR _ hs' i]
  · have e1 : ∀ i, (∫ s in (0 : ℝ)..t, ρL i / (w' s.toNNReal - vL' i s.toNNReal)) =
        ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal) := fun i =>
      intervalIntegral.integral_congr fun s hs => by
        have hs' := hIcc t ht s hs
        simp only [hw _ hs', hL _ hs' i]
    have e2 : ∀ i, (∫ s in (0 : ℝ)..t, ρR i / (w' s.toNNReal - vR' i s.toNNReal)) =
        ∫ s in (0 : ℝ)..t, ρR i / (w s.toNNReal - vR i s.toNNReal) := fun i =>
      intervalIntegral.integral_congr fun s hs => by
        have hs' := hIcc t ht s hs
        simp only [hw _ hs', hR _ hs' i]
    simp only [e1, e2, hw t ht]
    exact hweq t ht
  · have e : (∫ s in (0 : ℝ)..t, 2 / (vL' i s.toNNReal - w' s.toNNReal)) =
        ∫ s in (0 : ℝ)..t, 2 / (vL i s.toNNReal - w s.toNNReal) :=
      intervalIntegral.integral_congr fun s hs => by
        have hs' := hIcc t ht s hs
        simp only [hw _ hs', hL _ hs' i]
    rw [e, hL t ht i]; exact hLeq t ht i
  · have e : (∫ s in (0 : ℝ)..t, 2 / (vR' i s.toNNReal - w' s.toNNReal)) =
        ∫ s in (0 : ℝ)..t, 2 / (vR i s.toNNReal - w s.toNNReal) :=
      intervalIntegral.integral_congr fun s hs => by
        have hs' := hIcc t ht s hs
        simp only [hw _ hs', hR _ hs' i]
    rw [e, hR t ht i]; exact hReq t ht i
  · have e : {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w' s.toNNReal = vL' i s.toNNReal} =
        {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = vL i s.toNNReal} := by
      ext s
      exact ⟨fun ⟨h0, h1, h2⟩ => ⟨h0, h1, by rw [← hw _ h1, ← hL _ h1 i]; exact h2⟩,
        fun ⟨h0, h1, h2⟩ => ⟨h0, h1, by rw [hw _ h1, hL _ h1 i]; exact h2⟩⟩
    rw [e]; exact hcolL i
  · have e : {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w' s.toNNReal = vR' i s.toNNReal} =
        {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = vR i s.toNNReal} := by
      ext s
      exact ⟨fun ⟨h0, h1, h2⟩ => ⟨h0, h1, by rw [← hw _ h1, ← hR _ h1 i]; exact h2⟩,
        fun ⟨h0, h1, h2⟩ => ⟨h0, h1, by rw [hw _ h1, hR _ h1 i]; exact h2⟩⟩
    rw [e]; exact hcolR i
  · have e1 : (fun i => vL' i t) = fun i => vL i t := funext (hL t ht)
    have e2 : (fun i => vR' i t) = fun i => vR i t := funext (hR t ht)
    rw [e1, e2, hw t ht]; exact hnt t ht
  · refine hthT T hT hTζ w₀ vL₀ vR₀ (hlim.congr' ?_)
    have hmem : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, (t : ℝ≥0∞) < ζ := by
      filter_upwards [self_mem_nhdsWithin] with t (ht : t < T)
      rw [← hTζ]; exact ENNReal.coe_lt_coe.2 ht
    filter_upwards [hmem] with t ht
    simp only [hw t ht, hL t ht, hR t ht]

/-! ### Regular marginals -/

/-- **A regular marginal**: an integrated `SLE_a(ρ)` evolution on `(X, P, 𝓕)` whose pathwise relation holds at
**every** sample (not only almost surely) and whose driver and force points are strongly progressive (at every time,
also after the lifetime). -/
structure IsRegMarginal (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {X : Type*} {mX : MeasurableSpace X} (P : Measure X) (𝓕 : Filtration ℝ≥0 mX) (W : ℝ≥0 → X → ℝ)
    (VL : Fin nL → ℝ≥0 → X → ℝ) (VR : Fin nR → ℝ≥0 → X → ℝ) (B : ℝ≥0 → X → ℝ) (ζ : X → ℝ≥0∞) : Prop where
  evol : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ
  path : ∀ x, IsIntegratedSLEPath a xL xR ρL ρR (W · x) (fun i t => VL i t x) (fun i t => VR i t x) (B · x) (ζ x)
  progW : IsStronglyProgressive 𝓕 W
  progVL : ∀ i, IsStronglyProgressive 𝓕 (VL i)
  progVR : ∀ i, IsStronglyProgressive 𝓕 (VR i)

/-- **Regular marginals exist on a standard Borel space** for every ordered force word (`a > 0`): Theorem 2.2's
evolution on the regular code space `RegCode`, with the killed progressive versions of its coordinates. -/
theorem exists_isRegMarginal {a : ℝ} (ha : 0 < a) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (hF : IsOrderedForceWord xL xR) :
    ∃ (X : Type) (mX : MeasurableSpace X) (_ : StandardBorelSpace X) (P : Measure X)
      (_ : IsProbabilityMeasure P) (𝓕 : Filtration ℝ≥0 mX) (W : ℝ≥0 → X → ℝ) (VL : Fin nL → ℝ≥0 → X → ℝ)
      (VR : Fin nR → ℝ≥0 → X → ℝ) (B : ℝ≥0 → X → ℝ) (ζ : X → ℝ≥0∞),
      IsRegMarginal a xL xR ρL ρR P 𝓕 W VL VR B ζ := by
  obtain ⟨Ω, mΩ, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀⟩ :=
    exists_isIntegratedSLEEvolution_assembled (ρL := ρL) (ρR := ρR) ha hF
  obtain ⟨μ, hμ, 𝓗, hE, hC⟩ := exists_code_evolution ha hE₀
  have hS := measurableSet_cRel a xL xR ρL ρR
  set P : Measure (RegCode a xL xR ρL ρR) := μ.comap Subtype.val with hPdef
  have hmap : P.map Subtype.val = μ := by
    rw [hPdef, map_comap_subtype_coe hS, Measure.restrict_eq_self_of_ae_mem hC]
  have hPp : IsProbabilityMeasure P := ⟨by
    have h := Measure.map_apply (μ := P) measurable_subtype_coe MeasurableSet.univ
    rw [hmap, preimage_univ, measure_univ] at h
    exact h.symm⟩
  have hE' := Coupling.IsIntegratedSLEEvolution.comap measurable_subtype_coe hmap hE
  set 𝓕 := Coupling.filtrationComap 𝓗 (measurable_subtype_coe (p := fun x => x ∈ CRel a xL xR ρL ρR))
  set ζX : RegCode a xL xR ρL ρR → ℝ≥0∞ := fun x => cζ x.1
  set WX : ℝ≥0 → RegCode a xL xR ρL ρR → ℝ := fun t x => cw x.1 t
  set LX : Fin nL → ℝ≥0 → RegCode a xL xR ρL ρR → ℝ := fun i t x => cvL x.1 i t
  set RX : Fin nR → ℝ≥0 → RegCode a xL xR ρL ρR → ℝ := fun i t x => cvR x.1 i t
  obtain ⟨hBr, hWa, hLa, hRa, -⟩ := hE'
  have hpath := fun x : RegCode a xL xR ρL ρR => RegCode.isIntegratedSLEPath x
  have hcW : ∀ x, ContinuousOn (WX · x) {s | (s : ℝ≥0∞) < ζX x} := fun x => (hpath x).2.2.2.1
  have hcL : ∀ x i, ContinuousOn (LX i · x) {s | (s : ℝ≥0∞) < ζX x} := fun x i => (hpath x).2.2.2.2.1 i
  have hcR : ∀ x i, ContinuousOn (RX i · x) {s | (s : ℝ≥0∞) < ζX x} := fun x i => (hpath x).2.2.2.2.2.1 i
  set W := killedVersion ζX WX 0
  set VL : Fin nL → ℝ≥0 → RegCode a xL xR ρL ρR → ℝ := fun i => killedVersion ζX (LX i) (xL i)
  set VR : Fin nR → ℝ≥0 → RegCode a xL xR ρL ρR → ℝ := fun i => killedVersion ζX (RX i) (xR i)
  have hagW : ∀ x (t : ℝ≥0), (t : ℝ≥0∞) < ζX x → W t x = WX t x := fun x t ht => killedVersion_eq (hcW x) ht
  have hagL : ∀ x (t : ℝ≥0), (t : ℝ≥0∞) < ζX x → ∀ i, VL i t x = LX i t x :=
    fun x t ht i => killedVersion_eq (hcL x i) ht
  have hagR : ∀ x (t : ℝ≥0), (t : ℝ≥0∞) < ζX x → ∀ i, VR i t x = RX i t x :=
    fun x t ht i => killedVersion_eq (hcR x i) ht
  have hpath' : ∀ x, IsIntegratedSLEPath a xL xR ρL ρR (W · x) (fun i t => VL i t x) (fun i t => VR i t x)
      (fun t => cb x.1 t) (ζX x) := by
    intro x
    refine isIntegratedSLEPath_congr (hpath x) ?_ (fun i => ?_) (fun i => ?_) (hagW x) (hagL x) (hagR x)
    · by_cases h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζX x
      · rw [hagW x 0 h0]; exact (hpath x).1
      · exact killedVersion_of_le (not_lt.1 h0)
    · by_cases h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζX x
      · rw [hagL x 0 h0 i]; exact (hpath x).2.1 i
      · exact killedVersion_of_le (not_lt.1 h0)
    · by_cases h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζX x
      · rw [hagR x 0 h0 i]; exact (hpath x).2.2.1 i
      · exact killedVersion_of_le (not_lt.1 h0)
  have hadapt : ∀ (X X' : ℝ≥0 → RegCode a xL xR ρL ρR → ℝ), AdaptedBefore 𝓕 ζX X →
      (∀ x (t : ℝ≥0), (t : ℝ≥0∞) < ζX x → X' t x = X t x) → AdaptedBefore 𝓕 ζX X' := by
    intro X X' hX hXX t A hA
    have e : {x | (t : ℝ≥0∞) < ζX x ∧ X' t x ∈ A} = {x | (t : ℝ≥0∞) < ζX x ∧ X t x ∈ A} := by
      ext x
      exact ⟨fun h => ⟨h.1, hXX x t h.1 ▸ h.2⟩, fun h => ⟨h.1, (hXX x t h.1).symm ▸ h.2⟩⟩
    rw [e]; exact hX t A hA
  exact ⟨RegCode a xL xR ρL ρR, inferInstance, inferInstance, P, hPp, 𝓕, W, VL, VR, fun t x => cb x.1 t, ζX,
    ⟨⟨hBr, hadapt WX W hWa hagW, fun i => hadapt (LX i) (VL i) (hLa i) fun x t ht => hagL x t ht i,
      fun i => hadapt (RX i) (VR i) (hRa i) fun x t ht => hagR x t ht i, Eventually.of_forall hpath'⟩,
      hpath', isStronglyProgressive_killedVersion hWa 0,
      fun i => isStronglyProgressive_killedVersion (hLa i) (xL i),
      fun i => isStronglyProgressive_killedVersion (hRa i) (xR i)⟩⟩

end InteractingSLE.ZhanGT4.A1Marg
