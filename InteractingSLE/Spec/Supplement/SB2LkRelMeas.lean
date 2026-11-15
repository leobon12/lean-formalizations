/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6CoordBPrefix
import InteractingSLE.Spec.Sec5.CrossRestartMeasPathVersion

/-!
# Measurable relative drivers of lifted curves (the shared core of SB2(1) and SB2(2))

Packet PROVE-T14-SB2LIFT (round 3; the orchestrator's "shared core", with PROVE-T14-SB2DRV's K2 as consumer). K2 needs
the actual relative driver of a lifted curve as a measurable process. Two generic steps:

* **`exists_measurable_driver_of_drivenCurves`** (D): a family of curves measurable at every time, driven
  (`PocketTraversal.IsDrivenCurve`: local Loewner drivers in the capacity clock) on a measurable event, has a measurable
  driver from `0`, continuous before a measurable lifetime, which on that event is the terminal capacity time and
  generates the capacity reparametrization `capTrace` on every shorter horizon (GB6's `CoordB.drivenDriver`, the
  canonical driver `segDriver` made measurable, with a fixed driven curve off the event);
* **`measurable_of_dense_good`** (M): a family of curves continuous on an event, whose values at the "good" times of a
  countable enumeration of rationals are given by measurable functions, with good times dense on that event, is
  measurable at every time on that event (read along a measurably selected sequence of good rationals converging to
  the time). This turns the per-sample lift of a measurable curve through a frozen chart (read at the good times
  where the chart is applied in its domain) into a measurable family.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Sec7.PocketTraversal Sec7.Lemma71C

/-! ### A fixed driven curve -/

/-- The vertical ray `t ↦ t i` is a simple proper curve from `0` meeting `ℝ` only at `0`. -/
theorem isSegCurve_vert : IsSegCurve (fun t : ℝ => (t : ℂ) * Complex.I) := by
  refine ⟨(Complex.continuous_ofReal.mul continuous_const).continuousOn, fun s _ t _ hst => ?_, fun t ht => ?_,
    by simp, ?_, ?_⟩
  · have h := congrArg Complex.im hst
    simpa using h
  · show 0 ≤ ((t : ℂ) * Complex.I).im
    simpa using (show (0 : ℝ) ≤ t from ht)
  · refine (tendsto_abs_atTop_atTop).congr fun t => ?_
    simp
  · refine subset_empty_iff.1 (interior_subset.trans fun u hu => ?_)
    obtain ⟨-, hu0, him⟩ := hu
    have : u = 0 := by simpa using him
    exact absurd this hu0.ne'

/-- The vertical ray is a driven curve. -/
theorem isDrivenCurve_vert : IsDrivenCurve (fun t : ℝ => (t : ℂ) * Complex.I) :=
  isDrivenCurve_of_isSegCurve isSegCurve_vert

/-! ### (D) The measurable driver of driven curves -/

/-- **A measurable driver of a family of driven curves** (GB6's `CoordB.drivenDriver`): a family of curves
measurable at every time `t ≥ 0` and driven on a measurable event `G` has a measurable driver from `0`, continuous
before a measurable lifetime `U`, such that on `G` the lifetime is the terminal capacity time and the driver generates
the capacity reparametrization `capTrace` on every horizon `T < U`. -/
theorem exists_measurable_driver_of_drivenCurves {Ω : Type*} [MeasurableSpace Ω] {ρ : Ω → ℝ → ℂ}
    (hm : ∀ t, 0 ≤ t → Measurable fun ω => ρ ω t) {G : Set Ω} (hG : MeasurableSet G)
    (hρ : ∀ ω ∈ G, IsDrivenCurve (ρ ω)) :
    ∃ (W : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ≥0∞), (∀ t, Measurable (W t)) ∧ Measurable U ∧ (∀ ω, W 0 ω = 0) ∧
      (∀ ω, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < U ω}) ∧
      ∀ ω ∈ G, U ω = capLife (ρ ω) ∧
        ∀ T : ℝ≥0∞, T < U ω → IsGeneratingTrace (fun t => W t ω) T (capTrace (ρ ω)) := by
  classical
  set ρ' : Ω → ℝ → ℂ := fun ω => if ω ∈ G then ρ ω else fun t : ℝ => (t : ℂ) * Complex.I with hρ'
  have hρ'd : ∀ ω, IsDrivenCurve (ρ' ω) := fun ω => by
    by_cases hω : ω ∈ G
    · simp only [hρ', hω, ↓reduceIte]; exact hρ ω hω
    · simp only [hρ', hω, ↓reduceIte]; exact isDrivenCurve_vert
  have hm' : ∀ t, 0 ≤ t → Measurable fun ω => ρ' ω t := fun t ht => by
    have h : (fun ω => ρ' ω t) = fun ω => if ω ∈ G then ρ ω t else (t : ℂ) * Complex.I := by
      funext ω; by_cases hω : ω ∈ G <;> simp [hρ', hω]
    rw [h]
    exact Measurable.ite hG (hm t ht) measurable_const
  refine ⟨Supp8.GB6.CoordB.drivenDriver ρ', fun ω => capLife (ρ' ω),
    fun t => Supp8.GB6.CoordB.measurable_drivenDriver hρ'd hm' t,
    Supp8.GB6.CoordB.measurable_capLife hρ'd hm', fun ω => Supp8.GB6.CoordB.drivenDriver_zero hρ'd ω,
    fun ω => Supp8.GB6.CoordB.continuousOn_drivenDriver hρ'd ω, fun ω hω => ?_⟩
  have he : ρ' ω = ρ ω := by simp only [hρ', hω, ↓reduceIte]
  refine ⟨show capLife (ρ' ω) = capLife (ρ ω) by rw [he], fun T hT => ?_⟩
  have hT' : T < capLife (ρ ω) := by rw [← he]; exact hT
  have htr := (hρ ω hω).isGeneratingTrace hT'
  refine Sec5.CrossRestart.isGeneratingTrace_congr_drive htr fun t ht => ?_
  rw [Supp8.GB6.CoordB.drivenDriver_eq (lt_trans ht hT), he]

/-! ### (M) Measurability from dense good rational times -/

/-- A fixed enumeration of the nonnegative rationals (with repetitions; dense in `ℝ≥0`). -/
def ratPt (i : ℕ) : ℝ≥0 := (((Denumerable.ofNat ℚ i : ℚ) : ℝ)).toNNReal

open scoped Classical in
/-- **Measurability from dense good rational times** (M): let `ρ ω` be continuous for `ω` in a measurable event `M`,
and let the values at the good indices `i` (an event measurable in `ω` for each `i`) be `V i ω`, with `V i` measurable;
if on `M` the good times are dense, then `ω ↦ ρ ω t` is measurable on `M` for every `t`. -/
theorem measurable_of_dense_good {Ω : Type*} [MeasurableSpace Ω] {ρ : Ω → ℝ≥0 → ℂ} {V : ℕ → Ω → ℂ}
    {good : ℕ → Ω → Prop} (hgood : ∀ i, MeasurableSet {ω | good i ω}) (hV : ∀ i, Measurable (V i))
    {M : Set Ω} (hM : MeasurableSet M) (hcont : ∀ ω ∈ M, Continuous (ρ ω))
    (hval : ∀ ω ∈ M, ∀ i, good i ω → ρ ω (ratPt i) = V i ω)
    (hdense : ∀ ω ∈ M, ∀ (t : ℝ≥0) (ε : ℝ), 0 < ε → ∃ i, good i ω ∧ dist (ratPt i) t < ε) (t : ℝ≥0) :
    Measurable fun ω => if ω ∈ M then ρ ω t else 0 := by
  classical
  -- the window events and the measurable first good index in each window
  set win : ℕ → ℕ → Ω → Prop := fun n i ω => good i ω ∧ dist (ratPt i) t < 1 / ((n : ℝ) + 1) with hwin
  have hwinm : ∀ n i, MeasurableSet {ω | win n i ω} := fun n i => by
    by_cases hd : dist (ratPt i) t < 1 / ((n : ℝ) + 1)
    · have e : {ω | win n i ω} = {ω | good i ω} := by
        ext ω; exact ⟨fun h => h.1, fun h => ⟨h, hd⟩⟩
      rw [e]; exact hgood i
    · have e : {ω | win n i ω} = ∅ := by
        ext ω; exact ⟨fun h => hd h.2, fun h => h.elim⟩
      rw [e]; exact MeasurableSet.empty
  set M' : Set Ω := {ω | ∀ n, ∃ i, win n i ω} with hM'
  have hM'm : MeasurableSet M' := by
    have : M' = ⋂ n, ⋃ i, {ω | win n i ω} := by ext ω; simp [hM']
    rw [this]; exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun i => hwinm n i
  have hMM' : M ⊆ M' := fun ω hω n => hdense ω hω t _ (by positivity)
  set q : ℕ → Ω → ℕ → Prop := fun n ω i => ω ∉ M' ∨ win n i ω with hq
  have hqex : ∀ n ω, ∃ i, q n ω i := fun n ω => by
    by_cases hω : ω ∈ M'
    · obtain ⟨i, hi⟩ := hω n; exact ⟨i, Or.inr hi⟩
    · exact ⟨0, Or.inl hω⟩
  have hqm : ∀ n i, MeasurableSet {ω | q n ω i} := fun n i => hM'm.compl.union (hwinm n i)
  set idx : ℕ → Ω → ℕ := fun n ω => Nat.find (hqex n ω) with hidx
  have hidxm : ∀ n, Measurable (idx n) := fun n => measurable_find (hqex n) (hqm n)
  set F : ℕ → Ω → ℂ := fun n ω => V (idx n ω) ω with hF
  have hFm : ∀ n, Measurable (F n) := fun n => by
    intro s hs
    have e : F n ⁻¹' s = ⋃ i, idx n ⁻¹' {i} ∩ V i ⁻¹' s := by
      ext ω
      simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff, hF]
      exact ⟨fun h => ⟨idx n ω, rfl, h⟩, fun ⟨i, hi, h⟩ => hi ▸ h⟩
    rw [e]
    exact MeasurableSet.iUnion fun i => (hidxm n (measurableSet_singleton i)).inter (hV i hs)
  -- on `M`, the selected values converge to `ρ ω t`
  have hlim : ∀ ω ∈ M, Tendsto (fun n => F n ω) atTop (𝓝 (ρ ω t)) := by
    intro ω hω
    have hspec : ∀ n, win n (idx n ω) ω := fun n => by
      rcases Nat.find_spec (hqex n ω) with h | h
      · exact absurd (hMM' hω) h
      · exact h
    have hconv : Tendsto (fun n => ratPt (idx n ω)) atTop (𝓝 t) := by
      refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun n => (hspec n).2.le) ?_)
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := ((hcont ω hω).tendsto t).comp hconv
    refine h1.congr fun n => ?_
    exact hval ω hω _ (hspec n).1
  set Gl : Ω → ℂ := fun ω => limUnder atTop fun n => F n ω with hGl
  have hGlm : Measurable Gl :=
    (StronglyMeasurable.limUnder fun n => (hFm n).stronglyMeasurable).measurable
  have e : (fun ω => if ω ∈ M then ρ ω t else 0) = fun ω => if ω ∈ M then Gl ω else 0 := by
    funext ω
    by_cases hω : ω ∈ M
    · simp only [hω, ↓reduceIte, hGl]
      exact ((hlim ω hω).limUnder_eq).symm
    · simp only [hω, ↓reduceIte]
  rw [e]
  exact Measurable.ite hM hGlm measurable_const

end InteractingSLE.Theorem14.SB.Lk
