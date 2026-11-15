/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VkLife
import InteractingSLE.Spec.Supplement.BW1PropFrozen
import InteractingSLE.Spec.Sec7.ContinuityProbCollision
import InteractingSLE.Foundations.Loewner.YuanShift

/-!
# SB2(1)'s version half: the relative endpoint (named input) and the driver frozen at its lifetime

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108). The driver statement
`Vi.SB2DriverVersionStatement` asks for a driver `W` that is continuous at **every** time, generates the relative trace
`Γ` up to the relative lifetime `Vg` (a generating trace on the closed `[0, Vg]` when `Vg < ∞`), with a global Loewner
trace `ηr`, and `Γ + m` linked to the flow. The measurable driver (`Vk.exists_measurableDriver`) is continuous only
before `Vg`. When `Vg < ∞`, the remaining two facts concern the endpoint of the remainder. They are not formalized
anywhere in the project, so they form the named input **`SB2RelEndpointStatement`**:

almost surely at a launch on the entrance event, if the relative lifetime `relLife` of the flow's lift is finite, then
the physical remainder is finite (`ζ < ∞`), and every driver continuous from `0` that generates the lift in its
capacity clock before `relLife` converges at `relLife`, together with its trace.

The paper treats the remainder as an `SLE_κ(ρ)` process in the launch chart up to its continuation threshold, whose
driver and trace are continuous up to the threshold. Formally this needs the conformal transport of local growth to the
endpoint (and transience in the chart for `ζ = ∞`).

Deterministic part (proved):
* `frzDrv W V`, `frzTr Γ V`: driver / trace frozen at `V` at the left limit;
* `continuous_frz`: continuous at every time from continuity before `V` and the left limit at a finite `V`;
* **`isGeneratingTrace_frz`**: the frozen pair is a generating trace on `[0, V]`;
* **`exists_loewnerTrace_frz`**: the frozen driver has a global Loewner trace equal to `Γ` before `V`
  (`BW1Prop.exists_frozen_trace_close` for `V < ∞`, `isLoewnerTrace_of_isGeneratingTrace` for `V = ∞`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vk

open Lv Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

/-- **The relative lifetime of the flow's lift** at a sample: `sup {capClock (liftR flowLift) s : T_L + s < ζ}`. -/
def relLife {Ω : Type*} (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (k : ℕ) (u : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ⨆ (s : ℝ≥0) (_ : (((Ve.entT κ b jumps E k u η ζ ω).toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω),
    ENNReal.ofReal (capClock (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) s)

/-- **Named input: SB2(1)'s relative endpoint.** Almost surely at a launch on the entrance event, if the relative
lifetime of the flow's lift is finite, then the physical remainder is finite, and every driver `W`, continuous from `0`
before the relative lifetime, whose generating trace `Γ` reads the lift in its capacity clock, converges at the
relative lifetime together with `Γ`. -/
def SB2RelEndpointStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
    SB2LaunchProblem κ b jumps P h E k u ψ η ζ →
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      relLife κ b jumps E k u η ζ ω ≠ ⊤ → ζ ω ≠ ⊤ ∧
      ∀ (W : ℝ≥0 → ℝ) (Γ : ℝ≥0 → ℂ), W 0 = 0 →
        ContinuousOn W {t | (t : ℝ≥0∞) < relLife κ b jumps E k u η ζ ω} →
        (∀ T : ℝ≥0∞, T < relLife κ b jumps E k u η ζ ω → IsGeneratingTrace W T Γ) →
        (∀ s : ℝ≥0, (((Ve.entT κ b jumps E k u η ζ ω).toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω →
          Γ (capClock (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) s).toNNReal =
            Ve.flowLift κ b jumps E k u η ζ ω s) →
        ∃ (x : ℝ) (z : ℂ), Tendsto W (𝓝[<] (relLife κ b jumps E k u η ζ ω).toNNReal) (𝓝 x) ∧
          Tendsto Γ (𝓝[<] (relLife κ b jumps E k u η ζ ω).toNNReal) (𝓝 z)

/-! ### Freezing at the lifetime -/

section Freeze

variable {X : Type*} [TopologicalSpace X] [Nonempty X]

open scoped Classical in
/-- A function frozen at `V` at its left limit. -/
def frz (f : ℝ≥0 → X) (V : ℝ≥0∞) (q : ℝ≥0) : X :=
  if (q : ℝ≥0∞) < V then f q else limUnder (𝓝[<] V.toNNReal) f

theorem frz_of_lt {f : ℝ≥0 → X} {V : ℝ≥0∞} {q : ℝ≥0} (hq : (q : ℝ≥0∞) < V) : frz f V q = f q := by
  simp only [frz, hq, ↓reduceIte]

theorem frz_of_le {f : ℝ≥0 → X} {V : ℝ≥0∞} {q : ℝ≥0} (hq : V ≤ (q : ℝ≥0∞)) :
    frz f V q = limUnder (𝓝[<] V.toNNReal) f := by
  simp only [frz, not_lt.2 hq, ↓reduceIte]

theorem frz_top (f : ℝ≥0 → X) : frz f ⊤ = f := funext fun _ => frz_of_lt ENNReal.coe_lt_top

/-- **The frozen function is continuous** given continuity before `V` and a left limit at a finite `V > 0`. -/
theorem continuous_frz [T2Space X] {f : ℝ≥0 → X} {V : ℝ≥0∞} (hV0 : 0 < V) (hf : ContinuousOn f {t | (t : ℝ≥0∞) < V})
    (hlim : V ≠ ⊤ → ∃ x, Tendsto f (𝓝[<] V.toNNReal) (𝓝 x)) : Continuous (frz f V) := by
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < V} := isOpen_lt ENNReal.continuous_coe continuous_const
  rw [continuous_iff_continuousAt]
  intro q
  rcases lt_or_ge (q : ℝ≥0∞) V with hq | hq
  · -- before `V`: locally `f`
    have hev : f =ᶠ[𝓝 q] frz f V := by
      filter_upwards [hopen.mem_nhds hq] with t ht
      exact (frz_of_lt ht).symm
    exact ((hf.continuousAt (hopen.mem_nhds hq)).congr hev)
  · by_cases hVt : V = ⊤
    · rw [hVt] at hq; exact absurd hq (not_le.2 ENNReal.coe_lt_top)
    lift V to ℝ≥0 using hVt with v
    rw [ENNReal.coe_le_coe] at hq
    have hv0 : 0 < v := ENNReal.coe_pos.1 hV0
    have hvn : (v : ℝ≥0∞).toNNReal = v := ENNReal.toNNReal_coe v
    have hconst : ∀ t : ℝ≥0, v ≤ t → frz f v t = limUnder (𝓝[<] v) f := fun t ht => by
      rw [frz_of_le (ENNReal.coe_le_coe.2 ht), hvn]
    rcases hq.lt_or_eq with hq' | hq'
    · -- after `V`: locally constant
      have hev : (fun _ => limUnder (𝓝[<] v) f) =ᶠ[𝓝 q] frz f v := by
        filter_upwards [lt_mem_nhds hq'] with t ht
        exact (hconst t ht.le).symm
      exact continuousAt_const.congr hev
    · -- at `V`: the left limit
      subst hq'
      obtain ⟨x, hx⟩ := hlim ENNReal.coe_ne_top
      rw [hvn] at hx
      have : (𝓝[<] v).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hv0⟩
      have hlx : limUnder (𝓝[<] v) f = x := hx.limUnder_eq
      have hfv : frz f v v = x := by rw [hconst v le_rfl, hlx]
      refine continuousAt_iff_continuous_left'_right'.2 ⟨?_, ?_⟩
      · show Tendsto (frz f v) (𝓝[<] v) (𝓝 (frz f v v))
        rw [hfv]
        refine hx.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        exact (frz_of_lt (ENNReal.coe_lt_coe.2 ht)).symm
      · show Tendsto (frz f v) (𝓝[>] v) (𝓝 (frz f v v))
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        exact (hconst t (le_of_lt ht)).symm ▸ (hconst v le_rfl)

end Freeze

section Trace

variable {W : ℝ≥0 → ℝ} {Γ : ℝ≥0 → ℂ} {V : ℝ≥0∞}

/-- The trace is continuous before the horizon of its generating traces. -/
theorem continuousOn_of_forall_lt (hgen : ∀ T : ℝ≥0∞, T < V → IsGeneratingTrace W T Γ) :
    ContinuousOn Γ {t | (t : ℝ≥0∞) < V} := by
  intro t ht
  obtain ⟨T, htT, hTV⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have hc := (hgen T hTV).2.1
  have hnhds : {s : ℝ≥0 | (s : ℝ≥0∞) ≤ T} ∈ 𝓝 t :=
    mem_of_superset (Iio_mem_nhds (ENNReal.coe_lt_coe.1 htT)) fun s hs => ENNReal.coe_le_coe.2 (le_of_lt hs)
  exact (hc.continuousAt hnhds).continuousWithinAt

/-- **The generating trace at an infinite horizon** from all finite horizons. -/
theorem isGeneratingTrace_top_of_forall (hgen : ∀ T : ℝ≥0∞, T < ⊤ → IsGeneratingTrace W T Γ) :
    IsGeneratingTrace W ⊤ Γ := by
  refine ⟨(hgen 0 ENNReal.zero_lt_top).1, ?_, fun t _ => ?_⟩
  · have := continuousOn_of_forall_lt hgen
    exact this.mono fun s _ => ENNReal.coe_lt_top
  · exact (hgen (t + 1 : ℝ≥0) ENNReal.coe_lt_top).2.2 t (by exact_mod_cast lt_add_one t)

/-- **The frozen pair is a generating trace on `[0, V]`.** -/
theorem isGeneratingTrace_frz (hV0 : 0 < V) (hgen : ∀ T : ℝ≥0∞, T < V → IsGeneratingTrace W T Γ)
    (hΓ : V ≠ ⊤ → ∃ z, Tendsto Γ (𝓝[<] V.toNNReal) (𝓝 z)) :
    IsGeneratingTrace (frz W V) V (frz Γ V) := by
  have hc : Continuous (frz Γ V) := continuous_frz hV0 (continuousOn_of_forall_lt hgen) hΓ
  refine ⟨by rw [frz_of_lt (by exact_mod_cast hV0)]; exact (hgen 0 hV0).1, hc.continuousOn, fun t ht => ?_⟩
  obtain ⟨T, htT, hTV⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have hg := Sec5.CrossRestart.isGeneratingTrace_congr_drive (w := frz W V) (hgen T hTV)
    fun s hs => frz_of_lt (hs.trans hTV)
  have himg : Γ '' Icc 0 t = frz Γ V '' Icc 0 t :=
    image_congr fun s hs => (frz_of_lt (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) ht)).symm
  rw [← himg]
  exact hg.2.2 t htT

/-- **The frozen driver has a global Loewner trace** equal to `Γ` before `V`. -/
theorem exists_loewnerTrace_frz (hV0 : 0 < V) (hW0 : W 0 = 0) (hWc : ContinuousOn W {t | (t : ℝ≥0∞) < V})
    (hgen : ∀ T : ℝ≥0∞, T < V → IsGeneratingTrace W T Γ)
    (hlim : V ≠ ⊤ → (∃ x, Tendsto W (𝓝[<] V.toNNReal) (𝓝 x)) ∧ ∃ z, Tendsto Γ (𝓝[<] V.toNNReal) (𝓝 z)) :
    ∃ ηr : ℝ → ℂ, IsLoewnerTrace (fun r : ℝ => frz W V r.toNNReal) ηr ∧
      ∀ q : ℝ≥0, (q : ℝ≥0∞) < V → ηr q = Γ q := by
  have hgV := isGeneratingTrace_frz hV0 hgen fun h => (hlim h).2
  by_cases hVt : V = ⊤
  · subst hVt
    have hl := isLoewnerTrace_of_isGeneratingTrace hgV
    refine ⟨_, hl, fun q _ => ?_⟩
    simp only [Real.toNNReal_coe, frz_top]
  · lift V to ℝ≥0 using hVt with v
    have hWc' : Continuous (frz W v) := continuous_frz hV0 hWc fun h => (hlim h).1
    have hW0' : frz W v 0 = 0 := by rw [frz_of_lt (by exact_mod_cast hV0)]; exact hW0
    obtain ⟨αr, hαr, hαeq⟩ := BW1Prop.exists_frozen_trace_close hgV hWc'.continuousOn hW0'
      (ENNReal.coe_pos.1 hV0)
    have he : (fun r : ℝ => frz W v (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (v : ℝ≥0∞)).toNNReal) =
        fun r : ℝ => frz W v r.toNNReal := by
      funext r
      rcases le_total r.toNNReal v with hr | hr
      · rw [min_eq_left (ENNReal.coe_le_coe.2 hr), ENNReal.toNNReal_coe]
      · rw [min_eq_right (ENNReal.coe_le_coe.2 hr), ENNReal.toNNReal_coe, frz_of_le le_rfl,
          frz_of_le (ENNReal.coe_le_coe.2 hr)]
    rw [he] at hαr
    refine ⟨αr, hαr, fun q hq => ?_⟩
    rw [hαeq q ⟨q.2, by exact_mod_cast (ENNReal.coe_lt_coe.1 hq).le⟩, Real.toNNReal_coe, frz_of_lt hq]

end Trace

end InteractingSLE.Theorem14.SB.Vk
