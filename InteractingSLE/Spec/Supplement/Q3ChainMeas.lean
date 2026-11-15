/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3ChainConfig
import InteractingSLE.Spec.Supplement.GB6LifeBase
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# GB6's relative configuration read from the flow driver itself

Packet PROVE-Q3-REL3. `Q3Chain.ae_exists_isRelConfigOff_gb6_words` states GB6's relative configuration for a frozen
flow driver `U` chosen on each sample (equal to the flow driver `Wα` on `[0, t₂]`, `t₂ > s`). The probabilistic
consumers need the retained set as a function of `ω` that can be measurable: here every object of the configuration is
read from the flow driver `Uω = (r ↦ Wα(r⁺, ω))` itself. All the chart objects at the own time `s` depend only on the
driver on `[0, t₂]`:

* `invHull_eq_of_eqOn`, `relInv_eq_of_eqOn`, `relLog_eq_of_eqOn`, `chartAR_eq_of_eqOn`, `chartAL_eq_of_eqOn`,
  `relBad_eq_of_eqOn` (with `GB6.relMap_eq_of_eqOn`, `GB6.relClock_eq_of_eqOn`);
* `IsGB6RelChain`: the per-sample relative chain at the counterflow time `t` with its configuration property;
* **`ae_isRelConfigOff_gb6_flow`**: `ae_exists_isRelConfigOff_gb6_words` with `U` replaced by `Uω`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd)

universe u

namespace InteractingSLE.Supp8.Q3Chain

open GB6 (relMap relInv relClock firstContactTime sphereInv gb6WordOfRec gb6Rec)
open Q3Rel (invHull relLog relBad IsRelConfigOff)
open WangWu (chartAL chartAR)

/-! ### The chart objects depend only on the driver before a later time -/

section Congr

variable {U U' : ℝ → ℝ} {σ t₂ : ℝ}

theorem invHull_eq_of_eqOn (hσ : 0 ≤ σ) (hσt₂ : σ < t₂) (h : ∀ r ∈ Icc (0 : ℝ) t₂, U r = U' r) :
    invHull U σ = invHull U' σ := by
  unfold invHull
  rw [fwdHull_eq_of_eqOn hσ hσt₂ h]

theorem relInv_eq_of_eqOn (hσ : 0 ≤ σ) (hσt₂ : σ < t₂) (h : ∀ r ∈ Icc (0 : ℝ) t₂, U r = U' r) :
    relInv U σ = relInv U' σ := by
  funext v
  unfold relInv
  rw [fwdMapInv_eq_of_eqOn hσ hσt₂ h]

theorem relLog_eq_of_eqOn (hσ : 0 ≤ σ) (h : ∀ r ∈ Icc (0 : ℝ) σ, U r = U' r) : relLog U σ = relLog U' σ := by
  funext w
  unfold relLog
  rw [fwdMap_eq_of_eqOn hσ h, Ito.logDerivFwd_congr_of_eqOn (T := σ) (fun r hr => h r hr) hσ le_rfl]

theorem chartAR_eq_of_eqOn (hU : Continuous U) (hσ : 0 ≤ σ) (h : ∀ r ∈ Icc (0 : ℝ) σ, U' r = U r) :
    chartAR U' σ = chartAR U σ := by
  unfold chartAR
  rw [GB6.rightImg_congr hU hσ h, h σ ⟨hσ, le_rfl⟩]

theorem chartAL_eq_of_eqOn (hU : Continuous U) (hσ : 0 ≤ σ) (h : ∀ r ∈ Icc (0 : ℝ) σ, U' r = U r) :
    chartAL U' σ = chartAL U σ := by
  unfold chartAL
  rw [GB6.rightImg_congr (w := fun s => -U' s) (w' := fun s => -U s) hU.neg hσ
    (fun r hr => by simp only [h r hr]), h σ ⟨hσ, le_rfl⟩]

theorem relBad_eq_of_eqOn (hU : Continuous U) (hσ : 0 ≤ σ) (h : ∀ r ∈ Icc (0 : ℝ) σ, U' r = U r) :
    relBad U' σ = relBad U σ := by
  unfold relBad
  rw [chartAR_eq_of_eqOn hU hσ h, chartAL_eq_of_eqOn hU hσ h]

end Congr

/-- **GB6's relative chain at the counterflow time `t` on one sample** (with `Uω = (r ↦ Wα(r⁺, ω))`): `(Wr, ηr)` is a
continuous Loewner chain from `0` with a trace, the relative clock `u = a(t)` is positive, `Ψ(K'_t) = K̃_u`, and every
triple of bounded harmonic extensions of GB6's three words with the candidate mean forms an `IsRelConfigOff`. -/
def IsGB6RelChain (κ θ : ℝ) (c : Restart.BoundaryWord) (b' : ℝ → ℝ) (J' : Finset ℝ) (s t : ℝ≥0) {Ω : Type*}
    (Wα W : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ) (ω : Ω) (Wr : ℝ → ℝ) (ηr : ℝ → ℂ) : Prop :=
  Continuous Wr ∧ Wr 0 = 0 ∧ IsLoewnerTrace Wr ηr ∧
    0 < relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t ∧
    relMap (fun r : ℝ => Wα r.toNNReal ω) s '' fwdHull (fun r : ℝ => W r.toNNReal ω) t =
      fwdHull Wr (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t) ∧
    ∀ G₀ GE G v : ℂ → ℝ,
      IsBoundedHarmonicExtension
        (cfData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
          (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps)
        (cfJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
          (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps) G₀ →
      IsBoundedHarmonicExtension (cfFlowedData (16 / κ) b' J' (fun r : ℝ => W r.toNNReal ω) t)
        (cfFlowedJumps b' J' (fun r : ℝ => W r.toNNReal ω) t) GE →
      IsBoundedHarmonicExtension
        (cfFlowedData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
          (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps Wr
          (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t))
        (cfFlowedJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
          (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps Wr
          (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t)) G →
      (∀ z, v z = G (fwdMap Wr (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t)
          (relMap (fun r : ℝ => Wα r.toNNReal ω) s z)) -
        QuantumZipper.chiC (16 / κ) *
          ((logDerivFwd Wr (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t)
            (relMap (fun r : ℝ => Wα r.toNNReal ω) s z)).im +
            (relLog (fun r : ℝ => Wα r.toNNReal ω) s z).im)) →
      IsRelConfigOff (invHull (fun r : ℝ => Wα r.toNNReal ω) s) (relMap (fun r : ℝ => Wα r.toNNReal ω) s)
        (relInv (fun r : ℝ => Wα r.toNNReal ω) s) (relLog (fun r : ℝ => Wα r.toNNReal ω) s)
        (relBad (fun r : ℝ => Wα r.toNNReal ω) s)
        (fun r : ℝ => W r.toNNReal ω) Wr (fun r : ℝ => γ ω r.toNNReal) ηr t
        (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t)
        (QuantumZipper.chiC (16 / κ)) (Real.pi / Real.sqrt (16 / κ))
        (cfData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
          (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps)
        (cfFlowedData (16 / κ) b' J' (fun r : ℝ => W r.toNNReal ω) t)
        (cfFlowedData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
          (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps Wr
          (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t))
        (cfJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
          (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps)
        (cfFlowedJumps b' J' (fun r : ℝ => W r.toNNReal ω) t)
        (cfFlowedJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
          (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps Wr
          (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t)) G₀ GE G v

/-- **GB6's relative configuration with its actual words, read from the flow driver** (`0 < κ < 4`). As
`ae_exists_isRelConfigOff_gb6_words`, with every chart object at the own time `s` read from `Uω = (r ↦ Wα(r⁺, ω))`:
almost surely on `{s < ζα, α(s) ∈ ℍ}`, for all counterflow times `0 < t < t₁ < T_c` there is a relative chain
`(Wr, ηr)` at `u = a(t) > 0` with `Ψ(K'_t) = K̃_u` for which every triple of bounded harmonic extensions of GB6's three
words and the candidate mean form an `IsRelConfigOff` with the retained set `invHull Uω s`. -/
theorem ae_isRelConfigOff_gb6_flow {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    {θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {Wα W : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α γ : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (b' : ℝ → ℝ) (J' : Finset ℝ) (c : Restart.BoundaryWord) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      ∀ t t₁ : ℝ≥0, 0 < t → t < t₁ →
        (t₁ : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
          ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s) →
        ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), IsGB6RelChain κ θ c b' J' s t Wα W ζα γ ω Wr ηr := by
  filter_upwards [ae_exists_isRelConfigOff_gb6_words hκ hκ4 hF hα hW b' J' c s,
    GB6.ae_driver_zero_continuousOn hF] with ω hω hc hs hsH t t₁ ht0 htt₁ ht₁
  obtain ⟨U, t₂, hst₂, hUeq, hcfg⟩ := hω hs hsH
  have hs0 : (0 : ℝ) ≤ s := s.2
  have hUeq' : ∀ r ∈ Icc (0 : ℝ) t₂, U r = Wα r.toNNReal ω := hUeq
  have hUs : ∀ r ∈ Icc (0 : ℝ) s, U r = Wα r.toNNReal ω := fun r hr => hUeq r ⟨hr.1, hr.2.trans hst₂.le⟩
  -- a continuous driver equal to both on `[0, s]`
  have hcs : ContinuousOn (fun r : ℝ => Wα r.toNNReal ω) (Icc 0 (s : ℝ)) := by
    refine hc.2.comp continuous_real_toNNReal.continuousOn fun r hr => ?_
    show ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ζα ω
    refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) hs
  set V : ℝ → ℝ := Ito.clampDrv (fun r : ℝ => Wα r.toNNReal ω) s with hVdef
  have hV : Continuous V := Ito.continuous_clampDrv hs0 hcs
  have hVω : ∀ r ∈ Icc (0 : ℝ) s, Wα r.toNNReal ω = V r := fun r hr =>
    (Ito.clampDrv_eqOn (W := fun r : ℝ => Wα r.toNNReal ω) (T := (s : ℝ)) hr).symm
  have hVU : ∀ r ∈ Icc (0 : ℝ) s, U r = V r := fun r hr => (hUs r hr).trans (hVω r hr)
  have hrB : relBad U s = relBad (fun r : ℝ => Wα r.toNNReal ω) s := by
    rw [relBad_eq_of_eqOn hV hs0 hVU, relBad_eq_of_eqOn hV hs0 hVω]
  have hrM := GB6.relMap_eq_of_eqOn hs0 hUs
  have hrC := GB6.relClock_eq_of_eqOn hs0 hUs (fun r : ℝ => W r.toNNReal ω)
  have hiH := invHull_eq_of_eqOn hs0 hst₂ hUeq'
  have hrI := relInv_eq_of_eqOn hs0 hst₂ hUeq'
  have hrL := relLog_eq_of_eqOn hs0 hUs
  obtain ⟨Wr, ηr, hWr, hWr0, hηr, hu, hK, hall⟩ := hcfg t t₁ ht0 htt₁ ht₁
  rw [hrM, hrC] at hK
  rw [hrC] at hu
  rw [hrM, hrC, hiH, hrI, hrL, hrB] at hall
  exact ⟨Wr, ηr, hWr, hWr0, hηr, hu, hK, hall⟩

end InteractingSLE.Supp8.Q3Chain
