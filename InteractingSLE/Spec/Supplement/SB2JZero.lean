/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JK2
import InteractingSLE.Spec.Supplement.GW1Base

/-!
# SB2(1) at the first launch: the root chart and a deterministic entry point

Packet PROVE-T14-SB2FIN4 (second round). At the first instruction (`k = 0`) of the lower walk the launch is the root
launch: it always happens, in the root chart `Chart.id.recenter 0` (`GW1.launches_run_one_of_cons`); the retained prefix
is `{0} ∪ [u, 0]`, so `L = realMin (lowerPrefix …) = u`, and the entry point is `launchEntry … 0 u = u` — a constant,
hence measurable in every σ-algebra (the first open item of K2's application, the past-measurable entry point, is
trivial at `k = 0`; `exists_k2ChartInputs`' `hG` does not cover `k = 0`, where `GW2aConn.IsLive` fails, but there
`pastSigma 0 = ⊥` and the conditional law is the law, `Exist.StagedLaw.pastSigma_zero`, `GW1.condExpKernel_bot_apply`).

* `boundaryWalkSpec_cons`, `launches_zero`, `mem_launchSet_zero`, `launchChart_zero`;
* `lowerPrefix_zero`, `realMin_lowerPrefix_zero`, **`launchEntry_zero`**, `measurable_launchEntry_zero`;
* `condExpKernel_pastSigma_zero`: the conditional law given the retained past at `k = 0` is `P`.

Deterministic (and one measure identity); no named input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The lower walk's program starts with an ordinary piece of angle `−π/2` and infinite stop. -/
theorem boundaryWalkSpec_cons (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool) :
    ∃ rest : List Instr, (boundaryWalkSpec b jumps θ right).2.2 = Sum.inl (θ, ⊤) :: rest :=
  ⟨_, rfl⟩

/-- **The root launch**: instruction `0` of the lower walk launches in the root chart `Chart.id.recenter 0`. -/
theorem launches_zero (ω : Ω) :
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (0 + 1)).2.2.2.1 0 =
        some (Chart.id.recenter 0, -(Real.pi / 2)) := by
  obtain ⟨rest, hrest⟩ := boundaryWalkSpec_cons b jumps (-(Real.pi / 2)) true
  exact GW1.launches_run_one_of_cons κ b jumps _ hrest _

theorem mem_launchSet_zero (ω : Ω) : ω ∈ launchSet κ b jumps E 0 :=
  mem_launchSet (launches_zero ω)

theorem launchChart_zero (ω : Ω) : launchChart κ b jumps E 0 ω = Chart.id.recenter 0 :=
  launchChart_eq (launches_zero ω)

/-- The retained prefix at the first instruction is the root and the bridge. -/
theorem lowerPrefix_zero (u : ℝ) (ω : Ω) :
    lowerPrefix κ b jumps E 0 u ω = {(0 : ℂ)} ∪ ((↑) : ℝ → ℂ) '' Icc u 0 := by
  simp [lowerPrefix, prefixPhysSet, ExplState.run, ExplState.init, boundaryWalkSpec]

/-- **`L = u` at the first instruction.** -/
theorem realMin_lowerPrefix_zero {u : ℝ} (hu : u ≤ 0) (ω : Ω) :
    realMin (lowerPrefix κ b jumps E 0 u ω) = u := by
  rw [lowerPrefix_zero]
  have e : {x : ℝ | (x : ℂ) ∈ ({(0 : ℂ)} ∪ ((↑) : ℝ → ℂ) '' Icc u 0)} = Icc u 0 := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_singleton_iff, mem_image, Complex.ofReal_inj, exists_eq_right,
      Complex.ofReal_eq_zero]
    constructor
    · rintro (rfl | h)
      · exact ⟨hu, le_rfl⟩
      · exact h
    · exact Or.inr
  rw [realMin, e, csInf_Icc hu]

/-- **The entry point at the first instruction is the upper seed**: `launchEntry … 0 u = u` (the root chart is the
identity). -/
theorem launchEntry_zero {u : ℝ} (hu : u ≤ 0) (ω : Ω) : launchEntry κ b jumps E 0 u ω = u := by
  unfold launchEntry
  rw [launchChart_zero, realMin_lowerPrefix_zero hu]
  have hid : (Chart.id.recenter 0).1 = fun z => z := by
    funext z
    simp [Chart.recenter, Chart.id]
  refine (Lx.IsLeftEntryValue.eq_leftEntry ⟨fun x => x, fun x _ => ?_,
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id⟩).symm
  rw [hid]
  exact tendsto_nhdsWithin_of_tendsto_nhds tendsto_id

/-- At the first instruction the entry point is measurable for every σ-algebra (it is constant). -/
theorem measurable_launchEntry_zero {u : ℝ} (hu : u ≤ 0) (m : MeasurableSpace Ω) :
    Measurable[m] (launchEntry κ b jumps E 0 u) := by
  have e : launchEntry κ b jumps E 0 u = fun _ => u := funext (launchEntry_zero hu)
  rw [e]
  exact measurable_const

/-- **At the first instruction the conditional law given the retained past is the law** (`pastSigma 0 = ⊥`). -/
theorem condExpKernel_pastSigma_zero {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (spec : ExplSpec) (E' : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω₀ : Ω) :
    condExpKernel P (pastSigma κ b jumps spec E' 0) ω₀ = P := by
  rw [Exist.StagedLaw.pastSigma_zero]
  exact GW1.condExpKernel_bot_apply P ω₀

/-- **SB2(1)'s active word at the root chart**: if the field read in the root chart (it is the field itself) is a GFF
with data `b'` off `jumps'`, every height of `b'` on `(u, 0)` off `jumps'` is an original bridge height (the data agree
with `b` off `jumps ∪ jumps'`, `Exist.StagedLaw.eq_of_isGFFWithBoundaryData`; at a point of `jumps \ jumps'` use local
constancy of `b'` and a nearby point off both finite sets). -/
theorem isActiveLowWord_root (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {h h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData Q h b jumps) {u : ℝ} {b' : ℝ → ℝ} {jumps' : Finset ℝ}
    (hb' : IsPiecewiseConstantBoundaryData b' jumps')
    (hT : ∀ ω, IsChartTransport (Chart.id.recenter 0) 1 0 (QuantumZipper.chiC κ) (h ω) (h' ω))
    (hG : IsGFFWithBoundaryData Q h' b' jumps') : IsActiveLowWord κ b jumps u b' jumps' u := by
  have hh' : h' = h := funext fun ω => by
    have hT' := hT ω
    rw [Exist.StagedLaw.Chart.recenter_zero] at hT'
    exact hT'.unique Chart.isConformal_id (isChartTransport_id (QuantumZipper.chiC κ) (h ω))
  rw [hh'] at hG
  have heq := Exist.StagedLaw.eq_of_isGFFWithBoundaryData hb hb' hh hG
  intro y hy hyJ'
  right
  have hfin : (((jumps ∪ jumps' : Finset ℝ) : Set ℝ) \ {y})ᶜ ∈ 𝓝 y :=
    ((jumps ∪ jumps').finite_toSet.sdiff).isClosed.compl_mem_nhds (by simp)
  have hloc : ∀ᶠ z in 𝓝 y, b' z = b' y := hb' y hyJ'
  have hI : ∀ᶠ z in 𝓝 y, z ∈ Ioo u 0 := Ioo_mem_nhds hy.1 hy.2
  have hS : ∀ᶠ z in 𝓝[≠] y, z ∈ (((jumps ∪ jumps' : Finset ℝ) : Set ℝ) \ {y})ᶜ ∧ z ∈ ({y}ᶜ : Set ℝ) :=
    Filter.Eventually.and (mem_nhdsWithin_of_mem_nhds hfin) self_mem_nhdsWithin
  have hev : ∀ᶠ z in 𝓝[≠] y, (b' z = b' y ∧ z ∈ Ioo u 0) ∧
      (z ∈ (((jumps ∪ jumps' : Finset ℝ) : Set ℝ) \ {y})ᶜ ∧ z ∈ ({y}ᶜ : Set ℝ)) :=
    Filter.Eventually.and ((hloc.and hI).filter_mono nhdsWithin_le_nhds) hS
  obtain ⟨z, ⟨hbz, hz⟩, hzS, hzy⟩ := hev.exists
  have hzS' : z ∉ jumps ∪ jumps' := fun hm => hzS ⟨by exact_mod_cast hm, hzy⟩
  refine ⟨z, hz, fun hm => hzS' (Finset.mem_union_left _ hm), ?_⟩
  rw [← hbz, heq z hzS']

/-- **Clause (2) of SB2(1) at the first instruction** (the form of `SB2RelCoreCfStatement`'s clause (2) at `k = 0`):
almost surely (in fact surely) at the root launch, every witness of the launch clause has SB2(1)'s active word on
`(launchEntry … 0 u, 0) = (u, 0)`. -/
theorem activeWord_zero {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} (hu : u ≤ 0) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E 0 →
      ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        IsPiecewiseConstantBoundaryData b' jumps' →
        (∀ ω, IsChartTransport (launchChart κ b jumps E 0 ω₀) 1 0 (QuantumZipper.chiC κ) (h ω) (h' ω)) →
        IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps
          (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) 0) ω₀) h' b' jumps' →
        IsActiveLowWord κ b jumps u b' jumps' (launchEntry κ b jumps E 0 u ω₀) :=
  Eventually.of_forall fun ω₀ _ b' J' h' hb' hT hG => by
    rw [launchEntry_zero hu]
    rw [launchChart_zero] at hT
    rw [condExpKernel_pastSigma_zero] at hG
    exact isActiveLowWord_root hb hh hb' hT hG

end InteractingSLE.Theorem14.SB.Lv
