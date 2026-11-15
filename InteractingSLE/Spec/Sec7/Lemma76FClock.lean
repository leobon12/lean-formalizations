/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76EMain

/-!
# Lemma 7.6: the second continuation's canonical retained clock, measurably, at disjoint pairs

Packet PROVE-T15-CLOSE1 (2), item (a) of `planning/handoffs/PROVE-LEMMA76E.md` ("a measurable restart variable"). The
determination identity (Det) of `Lemma76CondDetHeightsStatement` reads the second continuation through its canonical
retained clock `canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r A 0` with lifetime `canonRetLife …` (G7's retained
chart at the second tip, `Supp7.G7RestartPath`). PROVE-G7B's `Supp7.exists_retClock` gives measurable versions of both
continuations' clocks at *ordinary* retained pairs (interior first tip, ordered proper completions). Lemma 7.6 needs
only the second continuation, at every *disjoint* pair (`Lemma76Exit.IsDisjointPair`; the first tip may be real):

* **`exists_retClock_snd`**: a chart path `γ₂` measurable at every time, a measurable lifetime `V₂`, `γ₂ ω` continuous
  on `[0, V₂ ω]`, which almost surely at every disjoint pair are the canonical retained clock of the second
  continuation (for every time, not only up to the lifetime).

The proof is the second-path half of `Supp7.exists_retClock` (same events, same measurability lemmas
`measurable_contStop`, `measurable_contPath`, `clockData_of_measurable`), with the chart event reached through
`Sec7.mem_E_of_isDisjointPair` instead of the ordinary-pair version.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Sec7

open Supp7 Restart

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
  {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The second continuation's canonical retained clock, measurably, at disjoint pairs**: a chart path measurable at
every time and a measurable lifetime, continuous on the lifetime, which almost surely at every disjoint pair are the
canonical retained clock (`canonRetPath`, `canonRetLife`, chart translation `0`) of the second continuation. -/
theorem exists_retClock_snd (hκ : 0 < κ) (hκ4 : κ < 4) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) :
    ∃ (γ₂ : Ω → ℝ≥0 → ℂ) (V₂ : Ω → ℝ≥0∞), (∀ t, Measurable fun ω => γ₂ ω t) ∧ Measurable V₂ ∧
      (∀ ω, ContinuousOn (γ₂ ω) {s | (s : ℝ≥0∞) ≤ V₂ ω}) ∧
      ∀ᵐ ω ∂P, Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        V₂ ω = canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 ∧
        γ₂ ω = canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 := by
  classical
  obtain ⟨η₂', hm₂, ha₂⟩ := exists_measurable_version_of_isFlowLine hη₂
  have hζ₁ := measurable_lifetime_of_isFlowLine hη₁
  have hζ₂ := measurable_lifetime_of_isFlowLine hη₂
  -- the almost sure good event and a measurable full-measure part of it
  set Good : Set Ω := {ω | IsPathGood (η₂ ω) (ζ₂ ω) x₂ ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω t = η₂ ω t) ∧
      ((d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)} with hGood
  have haeGood : ∀ᵐ ω ∂P, ω ∈ Good := by
    filter_upwards [ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂, ha₂, hag] with ω h2 h4 h5
    exact ⟨h2, h4, h5⟩
  set G' : Set Ω := (toMeasurable P Goodᶜ)ᶜ with hG'
  have hG'm : MeasurableSet G' := (measurableSet_toMeasurable P _).compl
  have hG'sub : G' ⊆ Good := fun ω hω => by
    by_contra h'
    exact hω (subset_toMeasurable P _ h')
  have hG'ae : ∀ᵐ ω ∂P, ω ∈ G' := by
    rw [ae_iff]
    have : {ω | ¬ ω ∈ G'} = toMeasurable P Goodᶜ := by ext ω; simp [hG']
    rw [this, measure_toMeasurable]
    exact ae_iff.1 haeGood
  -- the event of the second continuation
  set E₂ : Set Ω := G' ∩ d.E ∩ {ω | (d.u : ℝ≥0∞) < ζ₁ ω} ∩ {ω | (d.r : ℝ≥0∞) < ζ₂ ω} with hE₂
  have hE₂m : MeasurableSet E₂ := ((hG'm.inter hd.measurableSet_E).inter
    (measurableSet_lt measurable_const hζ₁)).inter (measurableSet_lt measurable_const hζ₂)
  -- pathwise facts on the event
  have hbase : ∀ ω ∈ E₂, IsRetGood (d.η₁ ω) d.u (d.η₂ ω) d.r ∧
      IsRetChart (d.η₁ ω) d.u (d.η₂ ω) d.r (d.fwd ω) (d.inv ω) (d.lift ω) ∧
      (∃ x₀ : ℝ, ∀ z, d.fwd ω z = ConformalImage.mapOut (fillH (prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r)) z - x₀) ∧
      d.D ω = activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r := by
    rintro ω ⟨⟨⟨-, hωE⟩, -⟩, -⟩
    obtain ⟨⟨x₀, hx₀⟩, hC⟩ := hd.isRetChart hωE
    refine ⟨hd.good ω (RetData.E_subset_G hωE), hC, ⟨x₀, fun z => ?_⟩, hd.D_of_mem hωE⟩
    show d.g ω z - d.shift ω = _
    rw [hx₀, RetData.g, RetData.K_of_mem hωE]
  have hagE : ∀ ω ∈ E₂, IsPathGood (η₂ ω) (ζ₂ ω) x₂ ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω t = η₂ ω t) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t := by
    rintro ω ⟨⟨⟨hωG, -⟩, hu⟩, hr⟩
    obtain ⟨h2, h4, h5⟩ := hG'sub hωG
    obtain ⟨-, -, h7⟩ := h5 hu hr
    exact ⟨h2, h4, h7⟩
  have hβ' : ∀ ω ∈ E₂, ∀ t ≤ d.r, d.η₂ ω t = η₂' ω t := fun ω hω t ht => by
    obtain ⟨-, e₂, a₂⟩ := hagE ω hω
    exact (a₂ t ht).trans (e₂ t ((ENNReal.coe_le_coe.2 ht).trans hω.2.le)).symm
  have hR₂ : ∀ ω ∈ E₂, IsRetCont (η₂' ω) (ζ₂ ω) x₂ d.r (d.η₁ ω '' Icc 0 d.u) (d.fwd ω) (d.inv ω) := by
    intro ω hω
    obtain ⟨hg, hC, hφ, -⟩ := hbase ω hω
    obtain ⟨hp₂, e₂, -⟩ := hagE ω hω
    have hωE : ω ∈ d.E := hω.1.1.2
    refine isRetCont_snd hg hC hφ (IsPathGood.congr hp₂ e₂) (hβ' ω hω) hω.2 hωE.1.1.2 hωE.1.2 ?_
    rw [← hd.DOf_of_mem RetData.E₀_subset_G hωE.1]
    exact hωE.2
  have hDK₂ : ∀ ω ∈ E₂, d.D ω = H \ fillH (d.η₁ ω '' Icc 0 d.u ∪ η₂' ω '' Icc 0 d.r) := by
    intro ω hω
    obtain ⟨hg, -, -, hD⟩ := hbase ω hω
    rw [hD, activeDomain_eq (isCompact_prefixSet' hg.1 hg.2.1).isClosed, prefixSet,
      image_congr fun t ht => hβ' ω hω t ht.2]
  -- the measurable stop
  set V₂ : Ω → ℝ≥0∞ := fun ω => (if ω ∈ E₂ then contStop (η₂' ω) (ζ₂ ω) d.r
    (d.η₁ ω '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r) else 0) - d.r with hV₂def
  have hV₂m : Measurable V₂ := by
    have h1 := measurable_contStop hE₂m hm₂ hζ₂ d.r hd.meas₁ hd.meas₂ d.u d.r
      (fun ω hω => (hR₂ ω hω).path.continuousOn)
      (fun ω hω => by rw [← Icc_zero_eq_Iic]; exact (hbase ω hω).1.1)
      (fun ω hω => by rw [← Icc_zero_eq_Iic]; exact (hbase ω hω).1.2.1) fun ω hω => hω.2.le
    have h2 := h1.sub (measurable_const (a := ((d.r : ℝ≥0) : ℝ≥0∞)))
    convert h2 using 1
    funext ω
    simp only [hV₂def, Pi.sub_apply]
    split_ifs <;> rfl
  have hV₂ : ∀ ω ∈ E₂, V₂ ω = contLife (η₂' ω) (ζ₂ ω) d.r (d.η₁ ω '' Icc 0 d.u ∪ η₂' ω '' Icc 0 d.r) := by
    intro ω hω
    simp only [hV₂def, hω, ↓reduceIte]
    rw [image_congr fun t ht => hβ' ω hω t ht.2]
    rfl
  -- the chart path in continuation time
  set Γ₂ : Ω → ℝ≥0 → ℂ := fun ω s => if ω ∈ E₂ then contPath (d.D ω) (d.fwd ω) (η₂' ω) d.r (V₂ ω) s else 0
    with hΓ₂def
  have hΓ₂E : ∀ ω ∈ E₂, Γ₂ ω = contPath (H \ fillH (d.η₁ ω '' Icc 0 d.u ∪ η₂' ω '' Icc 0 d.r)) (d.fwd ω) (η₂' ω)
      d.r (contLife (η₂' ω) (ζ₂ ω) d.r (d.η₁ ω '' Icc 0 d.u ∪ η₂' ω '' Icc 0 d.r)) := by
    intro ω hω
    funext s
    simp only [hΓ₂def, hω, ↓reduceIte]
    rw [hDK₂ ω hω, hV₂ ω hω]
  have hΓ₂m : ∀ s, Measurable fun ω => Γ₂ ω s := by
    intro s
    have h := measurable_contPath hE₂m hd.isOpen_D hd.measurableSet_mem_D hd.measurable_indicator_fwd hm₂ d.r
      hV₂m (fun ω hω => by rw [hV₂ ω hω]; exact (hR₂ ω hω).pos_contLife)
      (fun ω hω r' hr' => by
        rw [hV₂ ω hω] at hr'
        exact (hR₂ ω hω).path.continuousOn.mono fun t ht =>
          (ENNReal.coe_le_coe.2 ht).trans ((coe_add_lt_iff.1 hr').le.trans contStop_le))
      (fun ω hω r' hr' => by
        rw [hV₂ ω hω] at hr'
        rw [hDK₂ ω hω]
        exact (hR₂ ω hω).mem_closure_of_mem_contSet (mem_contSet_of_le le_self_add (coe_add_lt_iff.1 hr').le))
      (fun ω hω r' hr' => by
        rw [hV₂ ω hω] at hr'
        rw [hDK₂ ω hω]
        exact ⟨_, ((hR₂ ω hω).contPath_spec_lt hr').2.1⟩)
      (fun ω hω => by rw [hDK₂ ω hω, hV₂ ω hω]; exact (hR₂ ω hω).continuous_contPath) s
    convert h using 2 with ω
    simp only [hΓ₂def]
    split_ifs <;> rfl
  have hΓ₂c : ∀ ω, Continuous (Γ₂ ω) := fun ω => by
    by_cases hω : ω ∈ E₂
    · rw [hΓ₂E ω hω]; exact (hR₂ ω hω).continuous_contPath
    · have : Γ₂ ω = fun _ => 0 := funext fun s => by simp [hΓ₂def, hω]
      rw [this]; exact continuous_const
  obtain ⟨mγ₂, mU₂, cγ₂⟩ := clockData_of_measurable hE₂m hΓ₂c hΓ₂m
    (fun ω hω => by rw [hΓ₂E ω hω]; exact (hR₂ ω hω).contPath_zero) hV₂m
    (fun ω hω => by rw [hΓ₂E ω hω, hV₂ ω hω]; exact (hR₂ ω hω).isClockOn)
    (fun ω hω => by rw [hΓ₂E ω hω]; exact (hR₂ ω hω).continuous_chartClock)
  -- the clock data
  set γ₂f : Ω → ℝ≥0 → ℂ := fun ω s => if ω ∈ E₂ then Γ₂ ω (invClock (chartClock (Γ₂ ω)) (V₂ ω) s) else 0
    with hγ₂f
  set U₂f : Ω → ℝ≥0∞ := fun ω => if ω ∈ E₂ then capLife (chartClock (Γ₂ ω)) (V₂ ω) else 0 with hU₂f
  refine ⟨γ₂f, U₂f, fun t => ?_, ?_, fun ω => ?_, ?_⟩
  · convert mγ₂ t using 2 with ω
    simp only [hγ₂f]
    split_ifs <;> rfl
  · convert mU₂ using 2 with ω
    simp only [hU₂f]
    split_ifs <;> rfl
  · by_cases hω : ω ∈ E₂
    · simp only [hγ₂f, hU₂f, hω, ↓reduceIte]
      exact cγ₂ ω hω
    · simp only [hγ₂f, hU₂f, hω, ↓reduceIte]
      exact continuousOn_const
  · -- the canonical identification at disjoint pairs
    filter_upwards [hG'ae] with ω hωG' hpair
    obtain ⟨-, e₂, hagω⟩ := hG'sub hωG'
    obtain ⟨hG, a₁, a₂⟩ := hagω hpair.1 hpair.2.1
    have hωE : ω ∈ d.E := mem_E_of_isDisjointPair hd hG a₁ a₂ hpair
    have hω₂ : ω ∈ E₂ := ⟨⟨⟨hωG', hωE⟩, hpair.1⟩, hpair.2.1⟩
    have hi₁ : d.η₁ ω '' Icc 0 d.u = η₁ ω '' Icc 0 d.u := image_congr fun s hs => a₁ s hs.2
    have hK₂ : d.η₁ ω '' Icc 0 d.u ∪ η₂' ω '' Icc 0 d.r = η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r := by
      rw [hi₁, image_congr fun t ht => e₂ t ((ENNReal.coe_le_coe.2 ht.2).trans hpair.2.1.le)]
    have hΓ₂ω : Γ₂ ω = contPath (d.D ω) (d.fwd ω) (η₂' ω) d.r
        (contLife (η₂' ω) (ζ₂ ω) d.r (d.η₁ ω '' Icc 0 d.u ∪ η₂' ω '' Icc 0 d.r)) := by
      funext s
      simp only [hΓ₂def, hω₂, ↓reduceIte]
      rw [hV₂ ω hω₂]
    have hP₂ : γ₂f ω = canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r
        (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 := by
      rw [← (canonRetPath_congr e₂).1, ← hK₂, canonRetPath_zero]
      funext s
      simp only [hγ₂f, hω₂, ↓reduceIte]
      rw [hΓ₂ω, hV₂ ω hω₂]
    have hL₂ : U₂f ω = canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r
        (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 := by
      rw [← (canonRetPath_congr e₂).2, ← hK₂, canonRetLife_zero]
      simp only [hU₂f, hω₂, ↓reduceIte]
      rw [hΓ₂ω, hV₂ ω hω₂]
    exact ⟨hL₂, hP₂⟩

end Sec7

end InteractingSLE
