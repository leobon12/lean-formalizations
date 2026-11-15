/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ClockInv
import InteractingSLE.Spec.Restart.ChartMeasReduce

/-!
# The W8.1 clock data at a first contact (deterministic)

Packet PROVE-RESTART-CPL5. At a first contact `η₁(s₀) = η₂(t₀)` with the canonical (hydrodynamic) chart, the
relative capacity clock `chartClock Γ` of the chart path `Γ` of the continuation `η₁(s₀ + ·)` is a clock on the
whole available continuation interval `[0, ζ₁ − s₀]` (`IsContinuationGood.isClockOn_chartClock`): it vanishes at `0`,
is continuous and strictly increasing (Proposition 6.12 for the mapped continuation, `ClockGeom.lean`), and is
unbounded when `ζ₁ = ∞` (capacity additivity, `ClockCap.lean`). Reading both chart paths in their relative capacity
gives exactly CPL4's clock data (`isChartClockData_of_isClockOn`):

  `cᵢ(u) = sᵢ + aᵢ⁻¹(u)`,  `γᵢ = Γᵢ ∘ aᵢ⁻¹`,  `Uᵢ = aᵢ(ζᵢ − sᵢ)` (or `∞`),

with `cᵢ` strictly increasing onto the available continuation interval, `γᵢ ∈ ℍ̄`, `ηᵢ ∘ cᵢ = ψ ∘ γᵢ`; and `γᵢ` is
continuous on `[0, Uᵢ]` (`continuousOn_comp_invClock`).

The second path is handled by the same theorems after swapping the two paths (`IsFirstContactChart.swap`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Restart

variable {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {s₀ t₀ : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}

/-! ### Swapping the two paths -/

theorem prefixSet_comm : prefixSet η₂ t₀ η₁ s₀ = prefixSet η₁ s₀ η₂ t₀ := union_comm _ _

theorem activeDomain_comm : activeDomain η₂ t₀ η₁ s₀ = activeDomain η₁ s₀ η₂ t₀ := by
  simp only [activeDomain, union_comm]

theorem IsFirstContactChart.swap (hp : η₁ s₀ = η₂ t₀) (hC : IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift) :
    IsFirstContactChart η₂ t₀ η₁ s₀ φ ψ lift := by
  unfold IsFirstContactChart IsChartRegularPoint at *
  rw [activeDomain_comm, prefixSet_comm, ← hp]
  exact hC

theorem IsFirstContact.swap (h : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀) : IsFirstContact η₂ ζ₂ η₁ ζ₁ t₀ s₀ :=
  ⟨h.2.1, h.1, h.2.2.1.symm, fun t s ht hs hts => (h.2.2.2 s t hs ht hts.symm).symm⟩

/-! ### The clock on the whole continuation -/

theorem coe_le_sub_iff {ζ : ℝ≥0∞} {s₀ r : ℝ≥0} (hs₀ : (s₀ : ℝ≥0∞) ≤ ζ) :
    (r : ℝ≥0∞) ≤ ζ - s₀ ↔ ((s₀ + r : ℝ≥0) : ℝ≥0∞) ≤ ζ := by
  rw [ENNReal.coe_add, ENNReal.le_sub_iff_add_le_left ENNReal.coe_ne_top hs₀]

variable {Γ : ℝ≥0 → ℂ}

/-- **The relative capacity clock is a clock on the whole continuation** (Aux. lemma 76 and (W8.1)): for the
hydrodynamic chart `φ = g − x₀` of a first contact, `chartClock Γ` vanishes at `0`, is continuous and strictly
increasing on `[0, ζ₁ − s₀]`, and is unbounded if `ζ₁ = ∞` (given `hcap fill η₁([0, s]) = 2 s`). -/
theorem IsContinuationGood.isClockOn_chartClock (hg : IsContinuationGood η₁ ζ₁ s₀ η₂ ζ₂ t₀)
    (hC : IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift) {g : ℂ → ℂ} {x₀ : ℂ}
    (hgm : IsMapOut (fillH (prefixSet η₁ s₀ η₂ t₀)) g) (hφ : ∀ z, φ z = g z - x₀) (hx₀ : x₀.im = 0)
    (h0₂ : (η₂ 0).im = 0)
    (hcap₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ₁ → ConformalImage.hcapSet (fillH (η₁ '' Icc 0 s)) = 2 * s)
    (hs₀ : (s₀ : ℝ≥0∞) < ζ₁) (hΓc : ContinuousOn Γ {r | (r : ℝ≥0∞) ≤ ζ₁ - s₀})
    (hΓH : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ ζ₁ - s₀ → Γ r ∈ Hbar)
    (hΓψ : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ ζ₁ - s₀ → ψ (Γ r) = η₁ (s₀ + r)) (hΓ0 : Γ 0 = 0) :
    IsClockOn (chartClock Γ) (ζ₁ - s₀) := by
  have hle : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ ζ₁ - s₀ ↔ ((s₀ + r : ℝ≥0) : ℝ≥0∞) ≤ ζ₁ := fun r =>
    coe_le_sub_iff hs₀.le
  have hIcc : ∀ S : ℝ≥0, (S : ℝ≥0∞) ≤ ζ₁ - s₀ → Icc 0 S ⊆ {r : ℝ≥0 | (r : ℝ≥0∞) ≤ ζ₁ - s₀} :=
    fun S hS r hr => (ENNReal.coe_le_coe.2 hr.2).trans hS
  have hdrv : ∀ S : ℝ≥0, 0 < S → (S : ℝ≥0∞) ≤ ζ₁ - s₀ →
      chartClock Γ 0 = 0 ∧ StrictMonoOn (chartClock Γ) (Icc 0 S) ∧ ContinuousOn (chartClock Γ) (Icc 0 S) :=
    fun S hS hSU => by
      obtain ⟨h1, h2, h3, -⟩ := hg.exists_driver_chartClock hC hS ((hle S).1 hSU) (hΓc.mono (hIcc S hSU))
        (fun r hr => hΓH r (hIcc S hSU hr)) (fun r hr => hΓψ r (hIcc S hSU hr)) hΓ0
      exact ⟨h1, h2, h3⟩
  have hU0 : 0 < ζ₁ - s₀ := tsub_pos_of_lt hs₀
  -- a positive horizon inside the continuation
  obtain ⟨S₀, hS₀, hS₀U⟩ : ∃ S₀ : ℝ≥0, 0 < S₀ ∧ (S₀ : ℝ≥0∞) ≤ ζ₁ - s₀ := by
    by_cases hU : ζ₁ - s₀ = ⊤
    · exact ⟨1, one_pos, by rw [hU]; exact le_top⟩
    · exact ⟨(ζ₁ - s₀).toNNReal, ENNReal.toNNReal_pos hU0.ne' hU, by rw [ENNReal.coe_toNNReal hU]⟩
  refine ⟨(hdrv S₀ hS₀ hS₀U).1, fun a ha b hb hab => ?_, fun r hr => ?_, fun hU M => ?_⟩
  · exact (hdrv b (lt_of_le_of_lt zero_le hab) hb).2.1 ⟨zero_le, hab.le⟩ ⟨zero_le, le_rfl⟩ hab
  · by_cases hU : ζ₁ - s₀ = ⊤
    · have hS : ((r + 1 : ℝ≥0) : ℝ≥0∞) ≤ ζ₁ - s₀ := by rw [hU]; exact le_top
      refine ((hdrv (r + 1) (by positivity) hS).2.2 r ⟨zero_le, le_self_add⟩).mono_of_mem_nhdsWithin ?_
      exact mem_nhdsWithin_of_mem_nhds (mem_of_superset (Iio_mem_nhds (lt_add_one r))
        fun x hx => ⟨zero_le, le_of_lt hx⟩)
    · have hS : (((ζ₁ - s₀).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζ₁ - s₀ := by rw [ENNReal.coe_toNNReal hU]
      refine ((hdrv _ (ENNReal.toNNReal_pos hU0.ne' hU) hS).2.2.mono fun x hx =>
        ⟨zero_le, IsClockOn.le_toNNReal hU hx⟩) r hr
  · -- unbounded clock: `2 · chartClock Γ t ≥ 2 (s₀ + t) − hcap(fill K)`
    have hζ : ζ₁ = ⊤ := (ENNReal.sub_eq_top_iff.1 hU).1
    set C := ConformalImage.hcapSet (fillH (prefixSet η₁ s₀ η₂ t₀)) with hCdef
    set t : ℝ≥0 := (M + C / 2).toNNReal with ht
    have htU : (t : ℝ≥0∞) ≤ ζ₁ - s₀ := by rw [hU]; exact le_top
    have hst : ((s₀ + t : ℝ≥0) : ℝ≥0∞) ≤ ζ₁ := by rw [hζ]; exact le_top
    have hge := chartClock_ge hC hgm hφ hx₀ hg.isClosed_prefixSet (hg.continuousOn₁_Icc hst)
      hg.continuousOn₂_Icc hg.seed₁ h0₂ (hΓc.mono (hIcc t htU)) (by rw [hΓ0]; simp)
      (fun r hr => hΓψ r (hIcc t htU hr))
    rw [hcap₁ _ (by rw [hζ]; exact ENNReal.coe_lt_top)] at hge
    refine ⟨t, ?_⟩
    have h1 : M + C / 2 ≤ t := Real.le_coe_toNNReal _
    have h2 : (0 : ℝ) ≤ s₀ := NNReal.coe_nonneg _
    push_cast at hge
    linarith

/-! ### The clock data -/

variable {a : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- The original-time clock `s₀ + a⁻¹(·)` maps the capacity range onto the available continuation interval. -/
theorem IsClockOn.image_add_invClock (ha : IsClockOn a (ζ - s₀)) (hs₀ : (s₀ : ℝ≥0∞) ≤ ζ) :
    (fun u => s₀ + invClock a (ζ - s₀) u) '' {u | (u : ℝ≥0∞) ≤ capLife a (ζ - s₀)} =
      {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ} := by
  rw [show (fun u => s₀ + invClock a (ζ - s₀) u) = (fun r => s₀ + r) ∘ invClock a (ζ - s₀) from rfl,
    image_comp, ha.image_invClock]
  ext s
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨le_self_add, (coe_le_sub_iff hs₀).1 hr⟩
  · rintro ⟨hs, hsζ⟩
    refine ⟨s - s₀, (coe_le_sub_iff hs₀).2 ?_, add_tsub_cancel_of_le hs⟩
    rwa [add_tsub_cancel_of_le hs]

theorem IsClockOn.continuousOn_comp_invClock (ha : IsClockOn a (ζ - s₀))
    (hΓc : ContinuousOn Γ {r | (r : ℝ≥0∞) ≤ ζ - s₀}) :
    ContinuousOn (fun u => Γ (invClock a (ζ - s₀) u)) {u | (u : ℝ≥0∞) ≤ capLife a (ζ - s₀)} :=
  hΓc.comp ha.continuousOn_invClock fun _ hu => (ha.invClock_spec hu).1

/-- **CPL4's clock data from two clocks**: reading the two chart paths in their relative capacity clocks gives
`IsChartClockData`. -/
theorem isChartClockData_of_isClockOn {a₁ a₂ : ℝ≥0 → ℝ} {Γ₁ Γ₂ : ℝ≥0 → ℂ}
    (ha₁ : IsClockOn a₁ (ζ₁ - s₀)) (ha₂ : IsClockOn a₂ (ζ₂ - t₀)) (hs₀ : (s₀ : ℝ≥0∞) ≤ ζ₁)
    (ht₀ : (t₀ : ℝ≥0∞) ≤ ζ₂) (hΓ₁H : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ ζ₁ - s₀ → Γ₁ r ∈ Hbar)
    (hΓ₂H : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ ζ₂ - t₀ → Γ₂ r ∈ Hbar)
    (hΓ₁ψ : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ ζ₁ - s₀ → ψ (Γ₁ r) = η₁ (s₀ + r))
    (hΓ₂ψ : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ ζ₂ - t₀ → ψ (Γ₂ r) = η₂ (t₀ + r)) :
    IsChartClockData ψ η₁ ζ₁ s₀ η₂ ζ₂ t₀ (fun u => Γ₁ (invClock a₁ (ζ₁ - s₀) u))
      (fun u => Γ₂ (invClock a₂ (ζ₂ - t₀) u)) (capLife a₁ (ζ₁ - s₀)) (capLife a₂ (ζ₂ - t₀)) := by
  refine ⟨fun u => s₀ + invClock a₁ (ζ₁ - s₀) u, fun u => t₀ + invClock a₂ (ζ₂ - t₀) u,
    fun u hu v hv huv => add_lt_add_right (ha₁.strictMonoOn_invClock hu hv huv) _, ha₁.image_add_invClock hs₀,
    fun u hu v hv huv => add_lt_add_right (ha₂.strictMonoOn_invClock hu hv huv) _, ha₂.image_add_invClock ht₀,
    fun u hu => hΓ₁H _ (ha₁.invClock_spec hu).1, fun u hu => hΓ₂H _ (ha₂.invClock_spec hu).1,
    fun u hu => (hΓ₁ψ _ (ha₁.invClock_spec hu).1).symm, fun u hu => (hΓ₂ψ _ (ha₂.invClock_spec hu).1).symm⟩

end Restart

end InteractingSLE
