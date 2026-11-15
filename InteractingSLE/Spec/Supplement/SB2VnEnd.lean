/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VnTr

/-!
# SB2(1)'s endpoint after the identification (decision D4, option B, steps 1–2)

Packet PROVE-AUX61-NOJUMP. Decision D4 (`planning/reviews/DECISIONS-FABLE-1.md`): the endpoint is proved after the
identification `W = Wc` on `[0, relLife)`, `Wc` the canonical conditional flow-line driver with lifetime `ζc`.

* **`tendsto_of_eqOn_canonical`** (step 1, deterministic): a driver equal before `V ≤ ζc` to a continuous driver `Wc`
  whose generating trace `ηc` is continuous on `[0, ζc]` (Theorem 1.3) converges at a finite `V`. Every generating
  trace of the driver before `V` converges there too, to `ηc V`.
* **`ae_relEndpoint_of_identified`** (steps 1 and 2): almost surely at a launch on the entrance event, if the
  canonical driver of the driven family agrees with such a `Wc` before `relLife = capLife ρ`, then a finite `relLife`
  forces `ζ < ∞` (`Vn.ae_ne_top_of_capTrace_tendsto`: transience in the launch chart), and the family's driver and
  capacity trace converge at `relLife`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vn

open Lv Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

/-- **Step 1 (deterministic): the endpoint from a canonical continuation.** -/
theorem tendsto_of_eqOn_canonical {W Wc : ℝ≥0 → ℝ} {Γ ηc : ℝ≥0 → ℂ} {V ζc : ℝ≥0∞} (hV0 : 0 < V) (hV : V ≠ ⊤)
    (hVζ : V ≤ ζc) (hWc : Continuous Wc) (hWc0 : Wc 0 = 0) (hηc : IsGeneratingTrace Wc ζc ηc)
    (hW : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V → W q = Wc q) (hgen : ∀ T : ℝ≥0∞, T < V → IsGeneratingTrace W T Γ) :
    Tendsto W (𝓝[<] V.toNNReal) (𝓝 (Wc V.toNNReal)) ∧ Tendsto Γ (𝓝[<] V.toNNReal) (𝓝 (ηc V.toNNReal)) := by
  lift V to ℝ≥0 using hV with v
  rw [ENNReal.toNNReal_coe]
  have hlt : ∀ q : ℝ≥0, q < v → (q : ℝ≥0∞) < (v : ℝ≥0∞) := fun q hq => ENNReal.coe_lt_coe.2 hq
  -- the traces agree before `v`
  have hΓ : ∀ q : ℝ≥0, q < v → Γ q = ηc q := by
    intro q hq
    have h1 := hgen q (hlt q hq)
    have h2 : IsGeneratingTrace W q ηc :=
      Sec5.CrossRestart.isGeneratingTrace_congr_drive (hηc.mono_horizon ((hlt q hq).le.trans hVζ))
        fun s hs => hW s (hs.trans (hlt q hq))
    have hWc' : ContinuousOn W {s : ℝ≥0 | (s : ℝ≥0∞) < q} :=
      hWc.continuousOn.congr fun s hs => hW s (lt_trans hs (hlt q hq))
    have hW0 : W 0 = 0 := by rw [hW 0 (by exact_mod_cast hV0)]; exact hWc0
    exact IsGeneratingTrace.eq_of_le h1 h2 hWc' hW0 le_rfl
  refine ⟨?_, ?_⟩
  · refine ((hWc.tendsto v).mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (hW q (hlt q hq)).symm
  · have hcw : ContinuousWithinAt ηc {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζc} v := hηc.2.1 v hVζ
    have hsub : Iio v ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζc} := fun t ht => ((hlt t ht).le).trans hVζ
    refine ((hcw.mono hsub).tendsto).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (hΓ q hq).symm

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **Steps 1 and 2: the relative endpoint after the identification.** Almost surely at a launch on the entrance
event, if the driven family's canonical driver agrees before its lifetime with a continuous canonical driver `Wc` from
`0` whose generating trace is continuous on `[0, ζc]`, `capLife ρ ≤ ζc`, then a finite `capLife ρ` forces `ζ < ∞`,
and the canonical driver and the capacity trace converge at `capLife ρ`. -/
theorem ae_relEndpoint_of_identified (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    {ρ : Ω → ℝ → ℂ}
    (hρ : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        (ζ ω = ⊤ → EqOn (ρ ω) (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) (Ici 0)) ∧
        (ζ ω ≠ ⊤ → EqOn (ρ ω) (relCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω))
          ((ζ ω).toReal - (Ve.entT κ b jumps E k u η ζ ω).toReal)) (Ici 0))) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      IsDrivenCurve (ρ ω) → ∀ (Wc : ℝ≥0 → ℝ) (ηc : ℝ≥0 → ℂ) (ζc : ℝ≥0∞), Continuous Wc → Wc 0 = 0 →
        IsGeneratingTrace Wc ζc ηc → capLife (ρ ω) ≤ ζc →
        (∀ q : ℝ≥0, (q : ℝ≥0∞) < capLife (ρ ω) → segDriver (ρ ω) q = Wc q) →
        capLife (ρ ω) ≠ ⊤ →
          ζ ω ≠ ⊤ ∧ Tendsto (segDriver (ρ ω)) (𝓝[<] (capLife (ρ ω)).toNNReal) (𝓝 (Wc (capLife (ρ ω)).toNNReal)) ∧
            Tendsto (capTrace (ρ ω)) (𝓝[<] (capLife (ρ ω)).toNNReal) (𝓝 (ηc (capLife (ρ ω)).toNNReal)) := by
  filter_upwards [ae_ne_top_of_capTrace_tendsto h13 hS3 HP hρ] with ω hfin hl hT hd Wc ηc ζc hWc hWc0 hηc hle hW
    hV
  have hgen : ∀ T : ℝ≥0∞, T < capLife (ρ ω) → IsGeneratingTrace (segDriver (ρ ω)) T (capTrace (ρ ω)) :=
    fun T hT => Sec5.CrossRestart.isGeneratingTrace_congr_drive (hd.isGeneratingTrace hT) fun _ _ => rfl
  obtain ⟨h1, h2⟩ := tendsto_of_eqOn_canonical (Vk.capLife_pos hd) hV hle hWc hWc0 hηc hW hgen
  exact ⟨hfin hl hT hd hV _ h2, h1, h2⟩

end

end InteractingSLE.Theorem14.SB.Vn
