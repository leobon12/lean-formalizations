/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetLifeLine
import InteractingSLE.Spec.Supplement.G7RetainedPath

/-!
# The retained continuation with the boundary stop: data, clock and driver processes

Packet PROVE-RETAUX79C (ruling R55). The objects of K2's input (S) for the second continuation of Lemma 7.6:

* **`exists_retG_of_version`**: for measurable versions `η₁'`, `η₂'` of the two flow lines, good events `G r'` for
  every second cutoff `r'` such that `retFam G η₁' η₂' u r'` (common paths) is measurable good retained data whose
  good event contains almost surely `{u < ζ₁, r' < ζ₂}` (as `exists_retData_of_isFlowLine`, with the versions fixed
  in advance so that all later lines share the paths);
* `retStopSet`, `retLifeP` (physical lifetime: first contact with `η₁'[0, u] ∪ η₂'[0, r] ∪ ℝ`), `retChartPath`,
  **`retClock`** (the capacity reached at physical time `t`, regularized off the good event so that it is continuous,
  monotone and `0` at `0` for every `ω`), **`retLife`** (the capacity lifetime);
* `IsRetDriver`, **`retDriver`**: a driver that is continuous with value `0` at `0` for every `ω` and, where one
  exists, generates the canonical retained path and satisfies the later-line facts (`exists_retLine_facts_R`);
* pathwise facts at a good disjoint pair: `isRetCont_of_retData`, `retClock_eq`, `lt_retLifeP_of_retClock_lt`,
  `exists_retClock_ge`, `exists_isRetDriver`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Restart.RetAux79

open Supp7 Sec7 Sec7.Lemma76G

/-! ### Retained data along the later lines -/

section Family

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
  {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **Good events for retained data with given measurable versions** (as `exists_retData_of_isFlowLine`). -/
theorem exists_retG_of_version (hκ : 0 < κ) (hκ4 : κ < 4) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {η₁' η₂' : Ω → ℝ≥0 → ℂ}
    (hm₁ : ∀ t, Measurable fun ω => η₁' ω t) (hm₂ : ∀ t, Measurable fun ω => η₂' ω t)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s) (u r : ℝ≥0) :
    ∃ G : Set Ω, (⟨G, η₁', η₂', u, r⟩ : RetData Ω).IsMeasGood ∧
      ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω → (r : ℝ≥0∞) < ζ₂ ω → ω ∈ G := by
  set Good : Set Ω := {ω | (u : ℝ≥0∞) < ζ₁ ω → (r : ℝ≥0∞) < ζ₂ ω → IsRetGood (η₁' ω) u (η₂' ω) r} with hGood
  have haeGood : ∀ᵐ ω ∂P, ω ∈ Good := by
    filter_upwards [ha₁, ha₂, Sec7.ae_continuousOn_of_isFlowLine hη₁, Sec7.ae_continuousOn_of_isFlowLine hη₂,
      ae_mem_Hbar_of_isFlowLine hη₁, ae_mem_Hbar_of_isFlowLine hη₂, Supp10.ae_apply_zero_of_isFlowLine hη₁,
      Supp10.ae_apply_zero_of_isFlowLine hη₂, Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂]
      with ω e₁ e₂ hc₁ hc₂ hH₁ hH₂ h0₁ h0₂ hi₂ hu hr
    have hle₁ : ∀ s ≤ u, (s : ℝ≥0∞) ≤ ζ₁ ω := fun s hs => (ENNReal.coe_le_coe.2 hs).trans hu.le
    have hle₂ : ∀ t ≤ r, (t : ℝ≥0∞) ≤ ζ₂ ω := fun t ht => (ENNReal.coe_le_coe.2 ht).trans hr.le
    have ag₁ : ∀ s ≤ u, η₁' ω s = η₁ ω s := fun s hs => e₁ s (hle₁ s hs)
    have ag₂ : ∀ t ≤ r, η₂' ω t = η₂ ω t := fun t ht => e₂ t (hle₂ t ht)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hc₁.mono fun s hs => hle₁ s hs.2).congr fun s hs => ag₁ s hs.2
    · exact (hc₂.mono fun t ht => hle₂ t ht.2).congr fun t ht => ag₂ t ht.2
    · intro s hs; rw [ag₁ s hs.2]; exact hH₁ s (hle₁ s hs.2)
    · intro t ht; rw [ag₂ t ht.2]; exact hH₂ t (hle₂ t ht.2)
    · rw [ag₁ 0 zero_le, h0₁]; simp
    · rw [ag₂ 0 zero_le, h0₂]; simp
    · intro t ht he
      rw [ag₂ t ht.le, ag₂ r le_rfl] at he
      exact (ne_of_lt ht) (hi₂ (hle₂ t ht.le) (hle₂ r le_rfl) he)
  set G₀ : Set Ω := (toMeasurable P Goodᶜ)ᶜ with hG₀
  have hG₀sub : G₀ ⊆ Good := fun ω hω => by
    by_contra h'
    exact hω (subset_toMeasurable P _ h')
  have hG₀ae : ∀ᵐ ω ∂P, ω ∈ G₀ := by
    rw [ae_iff]
    have : {ω | ¬ ω ∈ G₀} = toMeasurable P Goodᶜ := by ext ω; simp [hG₀]
    rw [this, measure_toMeasurable]
    exact ae_iff.1 haeGood
  have hζ₁ := measurable_lifetime_of_isFlowLine hη₁
  have hζ₂ := measurable_lifetime_of_isFlowLine hη₂
  refine ⟨G₀ ∩ {ω | (u : ℝ≥0∞) < ζ₁ ω} ∩ {ω | (r : ℝ≥0∞) < ζ₂ ω},
    ⟨?_, hm₁, hm₂, fun ω hω => hG₀sub hω.1.1 hω.1.2 hω.2⟩, ?_⟩
  · exact ((measurableSet_toMeasurable P _).compl.inter (measurableSet_lt measurable_const hζ₁)).inter
      (measurableSet_lt measurable_const hζ₂)
  · filter_upwards [hG₀ae] with ω hω hu hr
    exact ⟨⟨hω, hu⟩, hr⟩

end Family

/-! ### The processes -/

section Processes

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The boundary stop set** of the second continuation: `η₁'[0, u] ∪ η₂'[0, r] ∪ ℝ`. -/
def retStopSet (η₁' η₂' : Ω → ℝ≥0 → ℂ) (u r : ℝ≥0) (ω : Ω) : Set ℂ :=
  η₁' ω '' Icc 0 u ∪ η₂' ω '' Icc 0 r ∪ realLine

/-- **The physical lifetime** of the second continuation after `r`: until its first contact with the boundary stop
set (ruling R55). -/
def retLifeP (η₁' η₂' : Ω → ℝ≥0 → ℂ) (ζ₂ : Ω → ℝ≥0∞) (u r : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  contLife (η₂' ω) (ζ₂ ω) r (retStopSet η₁' η₂' u r ω)

/-- **The chart path** of the second continuation in physical time, in the retained chart of the stop line. -/
def retChartPath (G : ℝ≥0 → Set Ω) (η₁' η₂' : Ω → ℝ≥0 → ℂ) (ζ₂ : Ω → ℝ≥0∞) (u r : ℝ≥0) (ω : Ω) : ℝ≥0 → ℂ :=
  contPath ((retFam G η₁' η₂' u r).D ω) ((retFam G η₁' η₂' u r).fwd ω) (η₂' ω) r (retLifeP η₁' η₂' ζ₂ u r ω)

open scoped Classical in
/-- **The clock**: the capacity reached by the chart path at physical time `t` (regularized to `0` when the relative
capacity clock is not continuous, monotone and `0` at `0`). -/
def retClock (G : ℝ≥0 → Set Ω) (η₁' η₂' : Ω → ℝ≥0 → ℂ) (ζ₂ : Ω → ℝ≥0∞) (u r : ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  if Continuous (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω)) ∧
      Monotone (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω)) ∧ chartClock (retChartPath G η₁' η₂' ζ₂ u r ω) 0 = 0 then
    (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω) t).toNNReal
  else 0

/-- **The capacity lifetime** of the second continuation (the canonical retained lifetime with the boundary stop). -/
def retLife (G : ℝ≥0 → Set Ω) (η₁' η₂' : Ω → ℝ≥0 → ℂ) (ζ₂ : Ω → ℝ≥0∞) (u r : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  canonRetLife ((retFam G η₁' η₂' u r).D ω) ((retFam G η₁' η₂' u r).fwd ω) (η₂' ω) (ζ₂ ω) r
    (retStopSet η₁' η₂' u r ω) 0

/-- **The canonical retained path** of the second continuation with the boundary stop, in capacity time. -/
def retPath (G : ℝ≥0 → Set Ω) (η₁' η₂' : Ω → ℝ≥0 → ℂ) (ζ₂ : Ω → ℝ≥0∞) (u r : ℝ≥0) (ω : Ω) : ℝ≥0 → ℂ :=
  canonRetPath ((retFam G η₁' η₂' u r).D ω) ((retFam G η₁' η₂' u r).fwd ω) (η₂' ω) (ζ₂ ω) r
    (retStopSet η₁' η₂' u r ω) 0

omit [MeasurableSpace Ω] in
theorem continuous_retClock (G : ℝ≥0 → Set Ω) (η₁' η₂' : Ω → ℝ≥0 → ℂ) (ζ₂ : Ω → ℝ≥0∞) (u r : ℝ≥0) (ω : Ω) :
    Continuous fun t => retClock G η₁' η₂' ζ₂ u r t ω := by
  unfold retClock
  split_ifs with hc
  · exact continuous_real_toNNReal.comp hc.1
  · exact continuous_const

omit [MeasurableSpace Ω] in
theorem monotone_retClock (G : ℝ≥0 → Set Ω) (η₁' η₂' : Ω → ℝ≥0 → ℂ) (ζ₂ : Ω → ℝ≥0∞) (u r : ℝ≥0) (ω : Ω) :
    Monotone fun t => retClock G η₁' η₂' ζ₂ u r t ω := by
  unfold retClock
  split_ifs with hc
  · exact fun s t hst => Real.toNNReal_le_toNNReal (hc.2.1 hst)
  · exact fun _ _ _ => le_rfl

omit [MeasurableSpace Ω] in
theorem retClock_zero (G : ℝ≥0 → Set Ω) (η₁' η₂' : Ω → ℝ≥0 → ℂ) (ζ₂ : Ω → ℝ≥0∞) (u r : ℝ≥0) (ω : Ω) :
    retClock G η₁' η₂' ζ₂ u r 0 ω = 0 := by
  unfold retClock
  split_ifs with hc
  · rw [hc.2.2, Real.toNNReal_zero]
  · rfl

end Processes

/-! ### Pathwise facts at a good disjoint pair -/

section Pathwise

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The second continuation of retained data at a chart point is a retained continuation** (`isRetCont_snd` in the
retained chart of the data). -/
theorem isRetCont_of_retData {d : RetData Ω} (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) {η₂ : ℝ≥0 → ℂ}
    {ζ₂ : ℝ≥0∞} {x₂ : ℝ} (hp₂ : IsPathGood η₂ ζ₂ x₂) (hβ : ∀ t ≤ d.r, d.η₂ ω t = η₂ t)
    (hrζ : (d.r : ℝ≥0∞) < ζ₂) : IsRetCont η₂ ζ₂ x₂ d.r (d.η₁ ω '' Icc 0 d.u) (d.fwd ω) (d.inv ω) := by
  have hg := hd.good ω (RetData.E_subset_G hω)
  obtain ⟨⟨x₀, hx₀⟩, hC⟩ := hd.isRetChart hω
  have hφ : ∃ x₀ : ℝ, ∀ z, d.fwd ω z =
      ConformalImage.mapOut (fillH (prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r)) z - x₀ :=
    ⟨x₀, fun z => by
      show d.g ω z - d.shift ω = _
      rw [hx₀, RetData.g, RetData.K_of_mem hω]⟩
  have hωE₀ := RetData.E_subset_E₀ hω
  have hcl : d.η₂ ω d.r ∈ closure (activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r) := by
    rw [← hd.DOf_of_mem RetData.E₀_subset_G hωE₀]
    exact hω.2
  exact isRetCont_snd hg hC hφ hp₂ hβ hrζ hωE₀.1.2 hωE₀.2 hcl

/-- The domain of retained data at a chart point is `ℍ \ fill(η₁[0, u] ∪ η₂[0, r])`. -/
theorem D_eq_of_retData {d : RetData Ω} (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) {η₂ : ℝ≥0 → ℂ}
    (hβ : ∀ t ≤ d.r, d.η₂ ω t = η₂ t) : d.D ω = H \ fillH (d.η₁ ω '' Icc 0 d.u ∪ η₂ '' Icc 0 d.r) := by
  have hg := hd.good ω (RetData.E_subset_G hω)
  rw [hd.D_of_mem hω, activeDomain_eq (isCompact_prefixSet' hg.1 hg.2.1).isClosed, prefixSet,
    image_congr fun t ht => hβ t ht.2]

/-- **The relative capacity clock of a retained continuation is monotone** (strictly increasing up to the end of
the continuation and constant afterwards). -/
theorem monotone_chartClock_of_isRetCont {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {a : ℝ≥0} {O : Set ℂ} {φ ψ : ℂ → ℂ}
    (hR : IsRetCont η ζ x a O φ ψ) :
    Monotone (chartClock (contPath (H \ fillH (O ∪ η '' Icc 0 a)) φ η a (contLife η ζ a (O ∪ η '' Icc 0 a)))) := by
  set K := O ∪ η '' Icc 0 a with hK
  set V := contLife η ζ a K with hVdef
  set Γ := contPath (H \ fillH K) φ η a V with hΓ
  have hclk := hR.isClockOn
  by_cases hV : V = ⊤
  · intro s t hst
    exact hclk.strictMonoOn.monotoneOn (show (s : ℝ≥0∞) ≤ V by rw [hV]; exact le_top)
      (show (t : ℝ≥0∞) ≤ V by rw [hV]; exact le_top) hst
  · set c := V.toNNReal with hc
    have hcV : (c : ℝ≥0∞) = V := ENNReal.coe_toNNReal hV
    have hΓc : ∀ s, c ≤ s → Γ s = Γ c := fun s hs => by
      rw [hΓ, contPath_of_le (hcV ▸ ENNReal.coe_le_coe.2 hs), contPath_of_le hcV.symm.le]
    have hconst : ∀ r, chartClock Γ r = chartClock Γ (min r c) := by
      intro r
      rcases le_total r c with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h]
        unfold chartClock
        congr 3
        apply Subset.antisymm
        · rintro _ ⟨s, hs, rfl⟩
          by_cases hsc : s ≤ c
          · exact ⟨s, ⟨hs.1, hsc⟩, rfl⟩
          · exact ⟨c, ⟨zero_le, le_rfl⟩, (hΓc s (le_of_not_ge hsc)).symm⟩
        · exact image_mono (Icc_subset_Icc_right h)
    intro s t hst
    rw [hconst s, hconst t]
    exact hclk.strictMonoOn.monotoneOn
      (show ((min s c : ℝ≥0) : ℝ≥0∞) ≤ V from hcV ▸ ENNReal.coe_le_coe.2 (min_le_right _ _))
      (show ((min t c : ℝ≥0) : ℝ≥0∞) ≤ V from hcV ▸ ENNReal.coe_le_coe.2 (min_le_right _ _))
      (min_le_min_right c hst)

end Pathwise

/-! ### The driver -/

section Driver

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A driver of the second continuation with the later-line facts** at `ω`: continuous, `0` at `0`, generating the
canonical retained path with the boundary stop, and at every continuation time `0 < t` before the boundary stop (with
`ω` in the later good event) the later pair is a disjoint pair, `ω` is in the later chart event and the later-line facts
hold at the capacity time `C(t)` (`exists_retLine_facts_R`). -/
def IsRetDriver (G : ℝ≥0 → Set Ω) (η₁' η₂' : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (u r : ℝ≥0) (κ θ : ℝ)
    (c₀ : BoundaryWord) (g₃ g₄ : ℝ) (ω : Ω) (W : ℝ≥0 → ℝ) : Prop :=
  Continuous W ∧ W 0 = 0 ∧ IsGeneratingTrace W (retLife G η₁' η₂' ζ₂ u r ω) (retPath G η₁' η₂' ζ₂ u r ω) ∧
    ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < retLifeP η₁' η₂' ζ₂ u r ω → ω ∈ G (r + t) →
      Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) (r + t) ∧ ω ∈ (retFam G η₁' η₂' u (r + t)).E ∧
      IsRetLineFacts (retFam G η₁' η₂' u r) (retFam G η₁' η₂' u (r + t)) ω W
        (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω) t).toNNReal κ θ
        (wordM (retFam G η₁' η₂' u r) c₀ (-sleLambda κ - θ * QuantumZipper.chiC κ)
          (sleLambda κ - θ * QuantumZipper.chiC κ) g₃ g₄ ω)
        (wordM (retFam G η₁' η₂' u (r + t)) c₀ (-sleLambda κ - θ * QuantumZipper.chiC κ)
          (sleLambda κ - θ * QuantumZipper.chiC κ) g₃ g₄ ω)

open scoped Classical in
/-- **The driver process** of the second continuation: a driver with the later-line facts where one exists, `0`
otherwise. -/
def retDriver (G : ℝ≥0 → Set Ω) (η₁' η₂' : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (u r : ℝ≥0) (κ θ : ℝ)
    (c₀ : BoundaryWord) (g₃ g₄ : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if h : ∃ W, IsRetDriver G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄ ω W then h.choose t else 0

variable {G : ℝ≥0 → Set Ω} {η₁' η₂' : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r : ℝ≥0} {κ θ : ℝ} {c₀ : BoundaryWord}
  {g₃ g₄ : ℝ}

theorem isRetDriver_retDriver {ω : Ω} (h : ∃ W, IsRetDriver G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄ ω W) :
    IsRetDriver G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄ ω fun t => retDriver G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄ t ω := by
  have e : (fun t => retDriver G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄ t ω) = h.choose := by
    funext t
    simp only [retDriver, h, ↓reduceDIte]
  rw [e]
  exact h.choose_spec

theorem continuous_retDriver (ω : Ω) : Continuous fun t => retDriver G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄ t ω := by
  by_cases h : ∃ W, IsRetDriver G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄ ω W
  · exact (isRetDriver_retDriver h).1
  · have e : (fun t => retDriver G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄ t ω) = fun _ => 0 := by
      funext t
      simp only [retDriver, h, ↓reduceDIte]
    rw [e]
    exact continuous_const

theorem retDriver_zero (ω : Ω) : retDriver G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄ 0 ω = 0 := by
  by_cases h : ∃ W, IsRetDriver G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄ ω W
  · exact (isRetDriver_retDriver h).2.1
  · simp only [retDriver, h, ↓reduceDIte]

end Driver

/-! ### Pathwise facts of the processes at a good disjoint pair -/

section Good

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℝ≥0 → Set Ω} {η₁' η₂' : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
  {u r : ℝ≥0} {x₁ x₂ : ℝ} {ω : Ω}

/-- **At a good disjoint pair, the shortened second continuation is a retained continuation**, and the processes are
read from its relative capacity clock. -/
theorem isRetCont_retFam (hd : (retFam G η₁' η₂' u r).IsMeasGood) (hG : ω ∈ G r)
    (hp₂ : IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r) :
    IsRetCont (η₂' ω) (contStop (η₂' ω) (ζ₂ ω) r (retStopSet η₁' η₂' u r ω)) x₂ r (η₁' ω '' Icc 0 u)
        ((retFam G η₁' η₂' u r).fwd ω) ((retFam G η₁' η₂' u r).inv ω) ∧
      (retFam G η₁' η₂' u r).D ω = H \ fillH (η₁' ω '' Icc 0 u ∪ η₂' ω '' Icc 0 r) ∧
      retLifeP η₁' η₂' ζ₂ u r ω =
        contLife (η₂' ω) (contStop (η₂' ω) (ζ₂ ω) r (retStopSet η₁' η₂' u r ω)) r (η₁' ω '' Icc 0 u ∪ η₂' ω '' Icc 0 r)
      := by
  have hE := mem_E_of_isDisjointPair hd hG (α := η₁' ω) (β := η₂' ω) (fun _ _ => rfl) (fun _ _ => rfl) hpair
  have hR := isRetCont_of_retData hd hE hp₂ (fun _ _ => rfl) hpair.2.1
  refine ⟨isRetCont_shorten hR, D_eq_of_retData hd hE fun _ _ => rfl, ?_⟩
  unfold retLifeP retStopSet
  rw [contLife_shorten]

end Good

/-! ### Clocks -/

section Clock

variable {C : ℝ≥0 → ℝ} {L : ℝ≥0∞}

/-- A clock value below the capacity lifetime is reached before the physical lifetime. -/
theorem lt_of_toNNReal_lt_capLife (hC : Monotone C) {t : ℝ≥0} (h : ((C t).toNNReal : ℝ≥0∞) < capLife C L) :
    (t : ℝ≥0∞) < L := by
  unfold capLife at h
  split_ifs at h with hL
  · rw [hL]; exact ENNReal.coe_lt_top
  · rw [ENNReal.ofReal, ENNReal.coe_lt_coe] at h
    by_contra hle
    have hLt : L.toNNReal ≤ t := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hL]
      exact not_lt.1 hle
    exact absurd h (not_lt.2 (Real.toNNReal_le_toNNReal (hC hLt)))

/-- Every capacity below the capacity lifetime is reached by the clock. -/
theorem exists_le_toNNReal_of_lt_capLife (hC : IsClockOn C L) {q : ℝ≥0} (h : (q : ℝ≥0∞) < capLife C L) :
    ∃ t : ℝ≥0, q ≤ (C t).toNNReal := by
  unfold capLife at h
  split_ifs at h with hL
  · obtain ⟨t, ht⟩ := hC.unbounded hL q
    refine ⟨t, ?_⟩
    rw [← Real.toNNReal_coe (r := q)]
    exact Real.toNNReal_le_toNNReal ht
  · rw [ENNReal.ofReal, ENNReal.coe_lt_coe] at h
    exact ⟨L.toNNReal, h.le⟩

end Clock

/-! ### The processes at a good disjoint pair -/

section GoodProc

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℝ≥0 → Set Ω} {η₁' η₂' : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
  {u r : ℝ≥0} {x₁ x₂ : ℝ} {ω : Ω}

/-- **At a good disjoint pair the clock of the chart path is a clock on the physical lifetime**, monotone and
continuous. -/
theorem retChartPath_clock (hd : (retFam G η₁' η₂' u r).IsMeasGood) (hG : ω ∈ G r)
    (hp₂ : IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r) :
    IsClockOn (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω)) (retLifeP η₁' η₂' ζ₂ u r ω) ∧
      Monotone (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω)) ∧
      Continuous (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω)) := by
  obtain ⟨hR, hD, hL⟩ := isRetCont_retFam hd hG hp₂ hpair
  have e : retChartPath G η₁' η₂' ζ₂ u r ω = contPath (H \ fillH (η₁' ω '' Icc 0 u ∪ η₂' ω '' Icc 0 r))
      ((retFam G η₁' η₂' u r).fwd ω) (η₂' ω) r (contLife (η₂' ω)
        (contStop (η₂' ω) (ζ₂ ω) r (retStopSet η₁' η₂' u r ω)) r (η₁' ω '' Icc 0 u ∪ η₂' ω '' Icc 0 r)) := by
    unfold retChartPath
    rw [hD, hL]
  rw [e, hL]
  exact ⟨hR.isClockOn, monotone_chartClock_of_isRetCont hR, hR.continuous_chartClock⟩

/-- **At a good disjoint pair the regularized clock is the capacity reached at time `t`.** -/
theorem retClock_eq (hd : (retFam G η₁' η₂' u r).IsMeasGood) (hG : ω ∈ G r)
    (hp₂ : IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r) (t : ℝ≥0) :
    retClock G η₁' η₂' ζ₂ u r t ω = (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω) t).toNNReal := by
  obtain ⟨hclk, hmono, hcont⟩ := retChartPath_clock hd hG hp₂ hpair
  have hc : Continuous (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω)) ∧
      Monotone (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω)) ∧
      chartClock (retChartPath G η₁' η₂' ζ₂ u r ω) 0 = 0 := ⟨hcont, hmono, hclk.zero⟩
  unfold retClock
  simp only [hc, and_self, ↓reduceIte]

omit [MeasurableSpace Ω] in
/-- The capacity lifetime is the capacity lifetime of the clock on the physical lifetime. -/
theorem retLife_eq : retLife G η₁' η₂' ζ₂ u r ω =
    capLife (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω)) (retLifeP η₁' η₂' ζ₂ u r ω) := by
  unfold retLife
  rw [canonRetLife_zero]
  rfl

/-- **Before the capacity lifetime, the physical time is before the physical lifetime.** -/
theorem lt_retLifeP_of_retClock_lt (hd : (retFam G η₁' η₂' u r).IsMeasGood) (hG : ω ∈ G r)
    (hp₂ : IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r) {t : ℝ≥0}
    (ht : (retClock G η₁' η₂' ζ₂ u r t ω : ℝ≥0∞) < retLife G η₁' η₂' ζ₂ u r ω) :
    (t : ℝ≥0∞) < retLifeP η₁' η₂' ζ₂ u r ω := by
  rw [retClock_eq hd hG hp₂ hpair, retLife_eq] at ht
  exact lt_of_toNNReal_lt_capLife (retChartPath_clock hd hG hp₂ hpair).2.1 ht

/-- **Every capacity before the capacity lifetime is reached by the clock** (`hreach`). -/
theorem exists_retClock_ge (hd : (retFam G η₁' η₂' u r).IsMeasGood) (hG : ω ∈ G r)
    (hp₂ : IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < retLife G η₁' η₂' ζ₂ u r ω) : ∃ t, q ≤ retClock G η₁' η₂' ζ₂ u r t ω := by
  rw [retLife_eq] at hq
  obtain ⟨t, ht⟩ := exists_le_toNNReal_of_lt_capLife (retChartPath_clock hd hG hp₂ hpair).1 hq
  exact ⟨t, by rw [retClock_eq hd hG hp₂ hpair]; exact ht⟩

/-- **At a good disjoint pair a driver with the later-line facts exists** (`exists_retLine_facts_R`). -/
theorem exists_isRetDriver (hd : ∀ r', (retFam G η₁' η₂' u r').IsMeasGood) (hG : ω ∈ G r)
    (hp₁ : IsPathGood (η₁' ω) (ζ₁ ω) x₁) (hp₂ : IsPathGood (η₂' ω) (ζ₂ ω) x₂) (hx : x₂ < x₁)
    (hpair : Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) {κ : ℝ} (hκ : 0 < κ) (θ g₃ g₄ : ℝ) :
    ∃ W, IsRetDriver G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄ ω W :=
  exists_retLine_facts_R hd hp₁ hp₂ hx hpair hG (fun _ _ => rfl) (fun _ _ => rfl) hc₀ hκ θ g₃ g₄

end GoodProc

end Restart.RetAux79

end InteractingSLE
