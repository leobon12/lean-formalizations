import QuantumZipper.Proofs.Zipper.E5PartsLvl
import QuantumZipper.Proofs.Zipper.E5Repair1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5-PARTSB, part A: the germ-free level data are independent of the germ

Task E5-PARTSB (Theorem 1.3, node E5, decisions D39/D40; Sheffield, arXiv:1012.4797, §5.4,
pp. 66–72, proof of Lemma 5.6).

`E5Repair6.esm_germ_fields'` needs its `V : ℝ≥0 × Ω → 𝕍` measurable on the **raw** `Ω`, while the
level time `T_ℓ` is only measurable on the completion (`measurable_levelTime_level`). We build a
raw-measurable modification `lvlTimeMod` of `T − T_ℓ`, equal to it off a `P`-null set: the length
process `lenA` is replaced by `G.indicator lenA`, where `G` is a raw-measurable full-measure set on
which `lenA q` agrees with a raw-measurable version at every rational `q`; this indicator process is
still continuous and monotone in `s` and is raw-measurable at every `s` (limit along rationals).
It satisfies the stopped-σ-algebra condition `hVT` (null sets lie in the augmented filtration),
so `esm_germ_fields'` applies to it, and independence passes to the true level time by a.e.
equality (`IndepFun.congr`).

Main result: `indepFun_lvl_germFree_data`.

Own elementary bookkeeping; standard fact used: a function measurable for the completion agrees
a.e. with a measurable one (`NullMeasurable.aemeasurable`).
-/

noncomputable section
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov LengthMarkov.GermDensity StrongMarkov B2 E1

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

/-- Rational points are dense in `ℝ≥0` along sequences. -/
theorem exists_seq_rat_tendsto_e5b (s : ℝ≥0) :
    ∃ q : ℕ → ℚ, Tendsto (fun n => Real.toNNReal (q n)) atTop (𝓝 s) := by
  have hs : (s : ℝ) ∈ closure (range ((↑) : ℚ → ℝ)) := by
    rw [Rat.denseRange_cast.closure_range]; exact mem_univ _
  obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.1 hs
  choose q hq using hx
  refine ⟨q, ?_⟩
  have h := (continuous_real_toNNReal.tendsto (s : ℝ)).comp hlim
  rw [Real.toNNReal_coe] at h
  refine h.congr fun n => ?_
  simp [Function.comp, hq n]

/-- The good set: raw-measurable, full measure, and on it `lenA q` equals a raw-measurable
function at every rational `q`. -/
theorem exists_good_lenA_e5b (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω)) :
    ∃ (G : Set Ω) (f : ℚ → Ω → ℝ≥0∞), MeasurableSet G ∧ P Gᶜ = 0 ∧ (∀ q, Measurable (f q)) ∧
      ∀ ω ∈ G, ∀ q : ℚ, lenA κ T B X (Real.toNNReal (q : ℝ)) ω = f q ω := by
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, -⟩ := id hS
  have hae : ∀ q : ℚ, AEMeasurable (lenA κ T B X (Real.toNNReal q)) P := fun q =>
    NullMeasurable.aemeasurable (fun _ hs =>
      measurable_lenA_compl_e5 hκ hκ4 hT hB hX hind hBc (Real.toNNReal q) hs)
  have hall : ∀ᵐ ω ∂P, ∀ q : ℚ, lenA κ T B X (Real.toNNReal q) ω = (hae q).mk _ ω :=
    ae_all_iff.2 fun q => (hae q).ae_eq_mk
  set N := {ω | ¬ ∀ q : ℚ, lenA κ T B X (Real.toNNReal q) ω = (hae q).mk _ ω} with hN
  have hN0 : P N = 0 := ae_iff.1 hall
  refine ⟨(toMeasurable P N)ᶜ, fun q => (hae q).mk _, (measurableSet_toMeasurable P N).compl,
    by rw [compl_compl, measure_toMeasurable, hN0], fun q => (hae q).measurable_mk, ?_⟩
  intro ω hω
  by_contra h
  exact hω (subset_toMeasurable P N h)

/-- The modified length process. -/
def lenMod (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (G : Set Ω) (s : ℝ≥0) (ω : Ω) :
    ℝ≥0∞ :=
  G.indicator (lenA κ T B X s) ω

theorem continuous_lenMod (hT : 0 ≤ T) (G : Set Ω) (ω : Ω) :
    Continuous fun s => lenMod κ T B X G s ω := by
  by_cases h : ω ∈ G
  · simp only [lenMod, indicator_of_mem h]; exact continuous_lenA hT ω
  · simp only [lenMod, indicator_of_notMem h]; exact continuous_const

theorem monotone_lenMod (hT : 0 ≤ T) (G : Set Ω) (ω : Ω) :
    Monotone fun s => lenMod κ T B X G s ω := by
  by_cases h : ω ∈ G
  · simp only [lenMod, indicator_of_mem h]; exact monotone_lenA hT ω
  · simp only [lenMod, indicator_of_notMem h]; exact monotone_const

theorem measurable_lenMod {G : Set Ω} {f : ℚ → Ω → ℝ≥0∞} (hT : 0 ≤ T) (hG : MeasurableSet G)
    (hf : ∀ q, Measurable (f q)) (hGf : ∀ ω ∈ G, ∀ q : ℚ, lenA κ T B X (Real.toNNReal (q : ℝ)) ω = f q ω)
    (s : ℝ≥0) : Measurable (lenMod κ T B X G s) := by
  have hq : ∀ q : ℚ, Measurable (lenMod κ T B X G (Real.toNNReal q)) := by
    intro q
    have e : lenMod κ T B X G (Real.toNNReal q) = G.indicator (f q) := by
      funext ω
      by_cases h : ω ∈ G
      · simp only [lenMod, indicator_of_mem h, hGf ω h q]
      · simp only [lenMod, indicator_of_notMem h]
    rw [e]; exact (hf q).indicator hG
  obtain ⟨q, hlim⟩ := exists_seq_rat_tendsto_e5b s
  refine measurable_of_tendsto_metrizable (fun n => hq (q n)) ?_
  refine tendsto_pi_nhds.2 fun ω => ?_
  exact ((continuous_lenMod (B := B) (X := X) (κ := κ) hT G ω).tendsto s).comp hlim

/-- The raw-measurable modification of the level collision time `T − T_ℓ`. -/
def lvlTimeMod (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (G : Set Ω)
    (p : ℝ≥0 × Ω) : ℝ :=
  T - ((levelTime (lenMod κ T B X G) T.toNNReal p.1 p.2 : ℝ≥0) : ℝ)

theorem levelTime_lenMod_of_mem {G : Set Ω} {ω : Ω} (h : ω ∈ G) (ℓ : ℝ≥0) :
    levelTime (lenMod κ T B X G) T.toNNReal ℓ ω = levelTime (lenA κ T B X) T.toNNReal ℓ ω := by
  simp only [levelTime, lenMod, indicator_of_mem h]

theorem levelTime_lenMod_of_notMem {G : Set Ω} {ω ω' : Ω} (h : ω ∉ G) (h' : ω' ∉ G)
    (ℓ : ℝ≥0) :
    levelTime (lenMod κ T B X G) T.toNNReal ℓ ω = levelTime (lenMod κ T B X G) T.toNNReal ℓ ω' := by
  simp only [levelTime, lenMod, indicator_of_notMem h, indicator_of_notMem h']

/-- **The germ-free level data are independent of the germ restricted to `[0, u₀]`.** -/
theorem indepFun_lvl_germFree_data (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω))
    (hpos : esmMeas κ T B X P lvlMu univ ≠ 0) {Ω' : Type} [MeasurableSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P'] (u₀ : ℝ≥0) :
    IndepFun (fun z : lvl Ω P Ω' =>
        ((lvlTime κ T B X P z.1, z.2), shiftP u₀ (esmGerm κ T B X P z.1)))
      (fun z => pathRestr u₀ (esmGerm κ T B X P z.1)) ((esmRr κ T B X P lvlMu).prod P') := by
  classical
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, -⟩ := id hS
  obtain ⟨G, f, hG, hG0, hf, hGf⟩ := exists_good_lenA_e5b hS hBc
  have hfin := esmMeas_lvlMu_ne_top (κ := κ) (T := T) (B := B) (X := X) (P := P)
  obtain ⟨W, hWp, hW⟩ := exists_wiener
  -- raw measurability
  have hVm : Measurable (lvlTimeMod κ T B X G) :=
    measurable_const.sub (NNReal.continuous_coe.measurable.comp
      (measurable_levelTime_uncurry (continuous_lenMod hT.le G) (monotone_lenMod hT.le G)
        (measurable_lenMod hT.le hG hf hGf) T.toNNReal))
  -- stopped-σ-algebra measurability
  have hVT : ∀ ℓ, Measurable[(complLevelStop hκ hκ4 hT hB hX hind hBc ℓ).measurableSpace]
      ((fun ω => lvlTimeMod κ T B X G (ℓ, ω)) ∘ ofCompl P) := by
    intro ℓ
    set hτ := complLevelStop hκ hκ4 hT hB hX hind hBc ℓ
    have hG0' : MeasurableSet[complFiltration hB hX 0]
        ((ofCompl P ⁻¹' G : Set (NullMeasurableSpace Ω P))) := by
      have h := (complFiltration_spec hB hX hind).2.2 (ofCompl P ⁻¹' G)ᶜ hG0
      simpa using h.compl
    have hGs : MeasurableSet[hτ.measurableSpace] (ofCompl P ⁻¹' G : Set (NullMeasurableSpace Ω P)) := by
      refine ⟨?_, fun i => ?_⟩
      · exact (le_iSup (fun t => (complFiltration hB hX t : MeasurableSpace _)) 0) _ hG0'
      · exact ((complFiltration hB hX).mono (show (0 : ℝ≥0) ≤ i from zero_le) _ hG0').inter (hτ i)
    have htrue := measurable_levelTime_complStop hκ hκ4 hT hB hX hind hBc (X := X) ℓ
    by_cases hne : ∃ ω₀, ω₀ ∉ G
    · obtain ⟨ω₀, hω₀⟩ := hne
      have e : (fun ω => lvlTimeMod κ T B X G (ℓ, ω)) ∘ ofCompl P =
          (ofCompl P ⁻¹' G).piecewise
            ((fun ω => T - ((levelTime (lenA κ T B X) T.toNNReal ℓ ω : ℝ≥0) : ℝ)) ∘ ofCompl P)
            (fun _ => lvlTimeMod κ T B X G (ℓ, ω₀)) := by
        funext ω
        by_cases h : ofCompl P ω ∈ G
        · simp only [Function.comp, Set.piecewise, mem_preimage, h, ite_true, lvlTimeMod,
            levelTime_lenMod_of_mem h]
        · simp only [Function.comp, Set.piecewise, mem_preimage, h, ite_false, lvlTimeMod,
            levelTime_lenMod_of_notMem h hω₀]
      rw [e]
      exact Measurable.piecewise hGs htrue measurable_const
    · push Not at hne
      have e : (fun ω => lvlTimeMod κ T B X G (ℓ, ω)) ∘ ofCompl P =
          (fun ω => T - ((levelTime (lenA κ T B X) T.toNNReal ℓ ω : ℝ≥0) : ℝ)) ∘ ofCompl P := by
        funext ω
        simp only [Function.comp, lvlTimeMod, levelTime_lenMod_of_mem (hne _)]
      rw [e]; exact htrue
  have hGF := esm_germ_fields' hκ hκ4 hT hB hX hind hBc lvlMu hpos hfin hVm hVT P'
    (Φ := id) measurable_id u₀ hW
  refine hGF.2.1.congr ?_ (ae_eq_refl _)
  -- a.e. equality with the true level time
  have hnull : (esmRr κ T B X P lvlMu).prod P'
      ((fun z : lvl Ω P Ω' => z.1) ⁻¹' {p | ofCompl P p.2 ∉ G}) = 0 := by
    have hS' : MeasurableSet {p : ℝ≥0 × NullMeasurableSpace Ω P | ofCompl P p.2 ∉ G} :=
      measurable_snd (hG.nullMeasurableSet.compl)
    rw [← Set.prod_univ, Measure.prod_prod, esmRr_apply]
    have h0 : esmMeas κ T B X P lvlMu {p | ofCompl P p.2 ∉ G} = 0 := by
      refine le_antisymm ?_ bot_le
      refine (Measure.restrict_apply_le _ _).trans ?_
      have e : {p : ℝ≥0 × NullMeasurableSpace Ω P | ofCompl P p.2 ∉ G} =
          univ ×ˢ (ofCompl P ⁻¹' G)ᶜ := by ext p; simp
      rw [e, Measure.prod_prod]
      have : P.completion (ofCompl P ⁻¹' G)ᶜ = 0 := hG0
      simp [this]
    simp [h0]
  refine measure_mono_null (fun z hz => ?_) hnull
  simp only [mem_preimage, mem_setOf_eq]
  intro hmem
  apply hz
  simp only [mem_setOf_eq, id, lvlTimeMod, lvlTime]
  rw [levelTime_lenMod_of_mem hmem]

end E5
end QuantumZipper
