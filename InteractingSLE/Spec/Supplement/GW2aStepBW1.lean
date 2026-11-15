/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aContStepAux
import InteractingSLE.Spec.Supplement.BW1
import InteractingSLE.Spec.Supplement.GW1ConnectorFirst
import InteractingSLE.Spec.Supplement.StagedRegularize

/-!
# Proposition BW1 for one flow line at a real endpoint (GW2a's launch step), from the source-form BW1

Packet PROVE-GW2A-STEP. GW2a (supplement p. 623): "In the already established complete conditional counterflow pair
targeted at the current incoming tip, GB6 and BW1 apply to the next ordinary piece".

**The landed named input `GW2aCont.BW1PrefixPairStatement` reads the given driver at its lifetime.** At a finite
continuation threshold `ζα ≤ t` the chart `Chart.id.loewner (stopDrv t (Wα, ζα)) (stopTime t (Wα, ζα))` uses the value
`Wα(ζα)`, which `IsFlowLineDriver` does not constrain (`StagedReg.isFlowLineDriver_congr_ae`: only the driver before the
lifetime is seen). If `Wα(ζα)` differs from the left limit, no forward solution exists on `[0, ζα]` (`IsForwardSol`
asks for continuity on `[0, T]`), the forward map is the junk `0`, every point of `ℍ` lies in the forward hull, the
chart's inverse is the constant `0`, and the field "read in" this chart is the deterministic distribution
`φ ↦ χ · lift(0) · ∫ φ`; a deterministic field has no centred counterflow (its coupling needs a Gaussian field). Hence
the statement fails as soon as a threshold has positive probability and the driver is modified there (a null-free
modification keeping `IsFlowLineDriver`). Its only consumer (`GW2aCont.ae_hasStatePair_succ_of_launch`) applies it to
staged drivers that are measurable, regular at every sample, and continuous on the stopped interval at the
conditioning sample (`GW1P.PieceRegular`, ruling R51). This file states and proves that corrected form.

* **`BW1PrefixPairRegStatement`**: `BW1PrefixPairStatement` for a measurable driver `e` regular at every sample, with
  the premise that the conditioning sample's piece is continuous on its stopped interval.
* **`FlowFixedTimeInteriorStatement`** (named input): a deterministic positive own time before the lifetime is almost
  surely not a boundary time of a flow line (its tip is interior). This disposes of BW1's real-tip case at a
  deterministic own time, which the source-form `BW1.BW1Statement` (thresholds only) does not cover.
* **`bw1PrefixPairRegStatement_of_bw1`**: the corrected statement from `BW1.BW1Statement` and
  `FlowFixedTimeInteriorStatement`, by restarting the piece as the only instruction of a one-instruction staged history
  `⟨0, false, [flow θ t]⟩`, showing that at a finite positive lifetime the restarted state is a threshold on some side
  (`ae_exists_hit`: the colliding force group swallows a real point), and identifying the regular conditional laws
  (the record `g` and the retained past are almost surely equal).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar IsForwardSol)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2aStep

open Exist.Staged Exist.StagedLaw GW2Later CounterflowRange GW2aMulti

/-! ### The corrected statement and the fixed-time input -/

/-- **Proposition BW1 for one flow line at a real endpoint, for regular drivers** (supplement pp. 613–615; GW2a,
p. 623). As `GW2aCont.BW1PrefixPairStatement`, for a flow line given by a measurable driver `e` regular at every sample
(`IsRegularDriver`: at a finite positive lifetime its value is the continuous left limit when it has one), at the
samples whose piece is continuous on its stopped interval `[0, min t ζ]` (`GW1P.PieceRegular`; the source's pieces are
continuous curves, ruling R51). -/
def BW1PrefixPairRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ : ℝ, θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) →
  ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q h b jumps →
  ∀ (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ Q h W ζ → (∀ᵐ ω ∂Q, ζ ω = ⊤) →
  ∀ e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, Measurable e → (∀ ω, IsRegularDriver (e ω)) →
    IsFlowLineDriver κ b jumps θ Q h (fun s ω => (e ω).1 s) (fun ω => (e ω).2) →
  ∀ t : ℝ≥0∞, ∀ g : Ω → RecData, Measurable g → (∀ᵐ ω ∂Q, g ω = recOf t (e ω)) →
    ∀ᵐ ω ∂Q, 0 < min t (e ω).2 → min t (e ω).2 ≠ ⊤ →
      ((e ω).2 ≤ t ∨ ¬ IsInteriorStop (e ω).1 (min t (e ω).2)) →
      GW1P.PieceRegular (e ω).1 (min t (e ω).2) →
      ∀ h₂ : Ω → DistOn upperHalfPlaneOpens,
        (∀ ω', IsChartTransport (Chart.id.loewner (stopDrv t (e ω)) (stopTime t (e ω))) 1 0
          (QuantumZipper.chiC κ) (h ω') (h₂ ω')) →
        ∃ (W₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞),
          IsCenteredCounterflowDriver κ (condExpKernel Q (MeasurableSpace.comap g inferInstance) ω) h₂ W₂ ζ₂ ∧
          (∀ᵐ ω' ∂(condExpKernel Q (MeasurableSpace.comap g inferInstance) ω), ζ₂ ω' = ⊤) ∧
          ∀ᵐ ω' ∂(condExpKernel Q (MeasurableSpace.comap g inferInstance) ω), ∀ (r : ℝ≥0) (z : ℂ),
            ((Chart.id.loewner (stopDrv t (e ω)) (stopTime t (e ω))).trans infinitySourceChart).tipAt
                (fun s => W₂ s ω') r z →
              z ∈ counterflowCompletedRange (fun s => W s ω')

/-- **Named input: a deterministic own time is almost surely not a boundary time of a flow line.** For `0 < κ < 4`, a
flow line of angle `θ ∈ [−π/2, π/2]` of a GFF with piecewise-constant data, and a deterministic own time `t > 0`:
almost surely, if `t` is before the lifetime, the tip at `t` is an interior point. (Standard: the force gaps of an
`SLE_κ(ρ)` driver have no atom at `0` at a fixed positive time; with nonzero gaps the trace is in `ℍ`,
`IsIntegratedSLEEvolution.ae_mem_H_of_forall_ne`. The deterministic Lebesgue-null collision sets
`MartChar.volume_rightImg_eq_zero` give this only for almost every `t`.) -/
def FlowFixedTimeInteriorStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ : ℝ, θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) →
  ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q h b jumps →
  ∀ (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞), IsFlowLineDriver κ b jumps θ Q h Wα ζα →
  ∀ t : ℝ≥0, 0 < t → ∀ᵐ ω ∂Q, (t : ℝ≥0∞) < ζα ω → IsInteriorStop (fun s => Wα s ω) t

/-! ### The one-instruction staged history -/

/-- **The one-instruction program** of a flow of angle `θ` from the root `0`, run for own time `t`. -/
abbrev oneSpec (θ : ℝ) (t : ℝ≥0∞) : ExplSpec := ⟨0, false, [Sum.inl (θ, t)]⟩

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

theorem run_oneSpec_one (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (t : ℝ≥0∞)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplState.run κ b jumps (oneSpec θ t) D 1 = ExplState.launch (ExplState.init 0) 0 (D 0) θ t := rfl

theorem launches_oneSpec_zero (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (t : ℝ≥0∞)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (ExplState.run κ b jumps (oneSpec θ t) D 1).2.2.2.1 0 = some (Chart.id.recenter 0, θ) := by
  rw [run_oneSpec_one, launches_launch, Function.update_self]
  rfl

theorem launches_oneSpec_of_pos (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (t : ℝ≥0∞)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} (hk : 1 ≤ k) :
    (ExplState.run κ b jumps (oneSpec θ t) D (k + 1)).2.2.2.1 k = none :=
  GW2Sched.launches_run_succ_of_length_le κ b jumps (oneSpec θ t) D (by simpa [oneSpec] using hk)

/-- **The retained past of the one-instruction history is the record of its piece.** -/
theorem pastMap_oneSpec_one {Ω : Type*} (θ : ℝ) (t : ℝ≥0∞) (e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) :
    pastMap κ b jumps (oneSpec θ t) (fun _ => e) 1 ω = fun _ => recOf t (e ω) := by
  funext i
  have hi : i = Fin.last 0 := Subsingleton.elim _ _
  subst hi
  have h := GW2aCont.lastRec_of_launch (κ := κ) (b := b) (jumps := jumps) (oneSpec θ t) (fun _ => e) 0 (ω := ω)
    (by rw [launches_oneSpec_zero]; exact Option.some_ne_none _)
  exact h

/-- **The σ-algebra of the retained past is generated by the record of the piece.** -/
theorem pastSigma_oneSpec_one {Ω : Type*} (θ : ℝ) (t : ℝ≥0∞) (e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    pastSigma κ b jumps (oneSpec θ t) (fun _ => e) 1 =
      MeasurableSpace.comap (fun ω => recOf t (e ω)) inferInstance := by
  rw [pastSigma_eq_comap]
  have he : pastMap κ b jumps (oneSpec θ t) (fun _ => e) 1 =
      (fun x : RecData => fun _ : Fin 1 => x) ∘ fun ω => recOf t (e ω) :=
    funext fun ω => pastMap_oneSpec_one θ t e ω
  rw [he, ← MeasurableSpace.comap_comp]
  congr 1
  refine le_antisymm (Measurable.comap_le (measurable_pi_iff.2 fun _ => measurable_id)) ?_
  have hψ : Measurable fun f : Fin 1 → RecData => f 0 := measurable_pi_apply 0
  have h1 := hψ.comap_le
  calc (inferInstance : MeasurableSpace RecData)
      = MeasurableSpace.comap ((fun f : Fin 1 → RecData => f 0) ∘ fun x : RecData => fun _ : Fin 1 => x)
          inferInstance := (MeasurableSpace.comap_id).symm
    _ = MeasurableSpace.comap (fun x : RecData => fun _ : Fin 1 => x)
          (MeasurableSpace.comap (fun f : Fin 1 → RecData => f 0) inferInstance) :=
        MeasurableSpace.comap_comp.symm
    _ ≤ _ := MeasurableSpace.comap_mono h1

/-- **A measurable regular flow-line driver is a one-instruction staged history.** -/
theorem isStagedHistory_oneSpec {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {θ : ℝ} (t : ℝ≥0∞)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Q : Measure Ω} [IsProbabilityMeasure Q]
    {h : Ω → DistOn upperHalfPlaneOpens} {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hem : Measurable e)
    (hreg : ∀ ω, IsRegularDriver (e ω))
    (hfl : IsFlowLineDriver κ b jumps θ Q h (fun s ω => (e ω).1 s) (fun ω => (e ω).2)) :
    IsStagedHistory κ b jumps Q h (oneSpec θ t) (fun _ => e) := by
  refine ⟨fun _ => hem, fun k => ?_, fun _ => Eventually.of_forall fun ω => (hreg ω).2.2.2, fun k => ?_⟩
  · rw [pastSigma_eq_comap]
    exact (measurable_pastMap (κ := κ) runMeasStatement hb (oneSpec θ t) (E := fun _ => e) (k := k)
      (fun _ _ => hem) (fun _ _ => hreg) k le_rfl).comap_le
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine Eventually.of_forall fun ω₀ c θ' hl => ?_
      rw [launches_oneSpec_zero] at hl
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
      refine ⟨b, jumps, h, hb, fun ω => ?_, ?_⟩
      · rw [Chart.recenter_zero]
        exact isChartTransport_id _ _
      · rw [GW1.pastSigma_zero_eq_bot, GW1.condExpKernel_bot_apply]
        exact hfl
    · refine Eventually.of_forall fun ω₀ c θ' hl => ?_
      rw [launches_oneSpec_of_pos κ b jumps θ t _ hk] at hl
      exact absurd hl (by simp)

/-! ### A finite positive lifetime swallows a real point -/

section Hit

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- A real point is alive on every `[0, r]`, `r < T`, and not on `[0, T]`. -/
def IsHitAt (U : ℝ → ℝ) (T : ℝ) (x : ℝ) : Prop :=
  (∀ r : ℝ, r < T → ∃ u, IsForwardSol U (x : ℂ) r u) ∧ ¬ ∃ u, IsForwardSol U (x : ℂ) T u

/-- **At a finite positive lifetime some real point is swallowed** (deterministic; both sides of
`GW1Conn.exists_hit_right_of_tendsto` and `GW1Conn.exists_hit_left_of_tendsto`, without an admissibility hypothesis):
the colliding force group has weight `≤ −2` on the right (a right force point `x > 0` is hit) or on the left (a left
force point `x < 0` is hit). -/
theorem exists_hit_of_tendsto (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {T : ℝ≥0} (hT : 0 < T)
    (hζ : (T : ℝ≥0∞) = ζ) {w₀ : ℝ} {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ}
    (hlim : Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)))
    (hthr : ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) {U : ℝ → ℝ}
    (hU : ∀ r : ℝ, 0 ≤ r → r < T → U r = w r.toNNReal) :
    (∃ x : ℝ, 0 < x ∧ IsHitAt U T x) ∨ ∃ x : ℝ, x < 0 ∧ IsHitAt U T x := by
  have := Sec2.IsForcePath.neBot_nhdsLT hT
  have hw : Tendsto w (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
  rcases hthr with hLs | hR
  · -- the left group, through the reflection
    right
    have hlim' : Tendsto (fun t => ((-w) t, fun i => -vR i t, fun i => -vL i t)) (𝓝[<] T)
        (𝓝 (-w₀, fun i => -vR₀ i, fun i => -vL₀ i)) := by
      have hcont : Continuous fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) =>
          (-p.1, fun i => -p.2.2 i, fun i => -p.2.1 i) := by fun_prop
      exact (hcont.tendsto _).comp hlim
    have hS : (∑ i ∈ Finset.univ.filter (fun i => -vL₀ i = -w₀), ρL i) ≤ -2 := by
      simpa only [neg_inj] using hLs
    obtain ⟨k, hk, hk0⟩ := h.reflect.exists_gapR_of_tendsto hT hζ hlim' hS
    have hk' : ∀ t : ℝ≥0, t < T → vL k t < w t := fun t ht => by simpa using hk t ht
    have hk0' : vL₀ k = w₀ := neg_inj.1 hk0
    have hv : Tendsto (vL k) (𝓝[<] T) (𝓝 (vL₀ k)) := tendsto_pi_nhds.1 hlim.snd_nhds.fst_nhds k
    refine ⟨xL k, ?_, fun r hr => ⟨_, h.isForwardSol_gapL hζ hk' hU hr⟩,
      Sec2.IsForcePath.not_exists_isForwardSol_of_tendsto hT (fun r hr => h.isForwardSol_gapL hζ hk' hU hr) ?_⟩
    · have h0 := hk' 0 hT
      rwa [h.w_zero, h.vL_zero] at h0
    · have hg : Tendsto (fun t => vL k t - w t) (𝓝[<] T) (𝓝 0) := by
        simpa [hk0'] using hv.sub hw
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp
        (hg.comp (Sec2.IsForcePath.tendsto_toNNReal_nhdsLT T))
      rw [Complex.ofReal_zero] at h2
      exact h2
  · left
    obtain ⟨k, hk, hk0⟩ := h.exists_gapR_of_tendsto hT hζ hlim hR
    have hv : Tendsto (vR k) (𝓝[<] T) (𝓝 (vR₀ k)) := tendsto_pi_nhds.1 hlim.snd_nhds.snd_nhds k
    refine ⟨xR k, ?_, fun r hr => ⟨_, h.isForwardSol_gapR hζ hk hU hr⟩,
      Sec2.IsForcePath.not_exists_isForwardSol_of_tendsto hT (fun r hr => h.isForwardSol_gapR hζ hk hU hr) ?_⟩
    · have h0 := hk 0 hT
      rwa [h.w_zero, h.vR_zero] at h0
    · have hg : Tendsto (fun t => vR k t - w t) (𝓝[<] T) (𝓝 0) := by
        simpa [hk0] using hv.sub hw
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp
        (hg.comp (Sec2.IsForcePath.tendsto_toNNReal_nhdsLT T))
      rw [Complex.ofReal_zero] at h2
      exact h2

end Hit

/-- **Almost surely a finite positive lifetime of a flow line swallows a real point** (for every driver agreeing with
the flow line's driver before the lifetime). -/
theorem ae_exists_hit {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q] {θ : ℝ}
    (hκ : 0 < κ) {h : Ω → DistOn upperHalfPlaneOpens} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞}
    (hfl : IsFlowLineDriver κ b jumps θ Q h Wα ζα) :
    ∀ᵐ ω ∂Q, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζα ω → ∀ U : ℝ → ℝ,
      (∀ r : ℝ, 0 ≤ r → r < T → U r = Wα r.toNNReal ω) →
      (∃ x : ℝ, 0 < x ∧ IsHitAt U T x) ∨ ∃ x : ℝ, x < 0 ∧ IsHitAt U T x := by
  obtain ⟨h', 𝓕, VL, VR, B, -, hC⟩ := hfl
  have hEv := hC.1
  filter_upwards [hEv.ae_isIntegratedSLEPath, hEv.ae_tendsto_threshold hκ] with ω hp hth T hT hζ U hU
  obtain ⟨w₀, vL₀, vR₀, hlim, hthr⟩ := hth T hT hζ
  exact exists_hit_of_tendsto hp.isForcePath hT hζ hlim hthr hU

/-- **A launch from the root ending at a finite positive lifetime that swallows a real point is a threshold on some
side.** -/
theorem endsAtThresholdSide_of_hit {d : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ) {t : ℝ≥0∞} (hle : d.2 ≤ t) (hfin : d.2 ≠ ⊤)
    (h0 : d.2 ≠ 0)
    (hhit : (∃ x : ℝ, 0 < x ∧ IsHitAt (stopDrv t d) (stopTime t d) x) ∨
      ∃ x : ℝ, x < 0 ∧ IsHitAt (stopDrv t d) (stopTime t d) x) :
    ∃ r : Bool, BW1.EndsAtThresholdSide (ExplState.launch (ExplState.init 0) 0 d θ t) r := by
  have hm : min t d.2 ≠ ⊤ := by rw [min_eq_right hle]; exact hfin
  have hst := (launch_eq_of_ne_top (ExplState.init 0) 0 d θ t hm).2.2.2.2.1
  have hc : stChart (ExplState.init 0) = Chart.id := Chart.recenter_zero _
  have hhit' : ∀ x : ℝ, IsHitAt (stopDrv t d) (stopTime t d) x → lHit (stChart (ExplState.init 0)) t d x := by
    intro x hx
    rw [hc]
    exact hx
  unfold BW1.EndsAtThresholdSide
  change ∃ r : Bool, stStatus (ExplState.launch (ExplState.init 0) 0 d θ t) = stThr (some r)
  rw [hst]
  unfold lStatus
  simp only [not_lt.2 hle, h0, ↓reduceIte]
  by_cases hR : ∃ x : ℝ, stRecR (ExplState.init 0) < x ∧ lHit (stChart (ExplState.init 0)) t d x
  · exact ⟨true, by simp only [hR, ↓reduceIte]⟩
  · simp only [hR, ↓reduceIte]
    rcases hhit with ⟨x, hx, hxh⟩ | ⟨x, hx, hxh⟩
    · exact absurd ⟨x, hx, hhit' x hxh⟩ hR
    · have hL : ∃ x : ℝ, x < stRecL (ExplState.init 0) ∧ lHit (stChart (ExplState.init 0)) t d x :=
        ⟨x, hx, hhit' x hxh⟩
      exact ⟨false, by simp only [hL, ↓reduceIte]⟩

/-! ### BW1 at a real endpoint from the source-form BW1 -/

/-- **The conclusion at one sample, from BW1's pair on one side** (bookkeeping): if the restarted state at `ω` ends at a
threshold on the side `r`, BW1's driver `Wr` (a centred counterflow of the field read in the state chart under the
conditional law given the retained past, with infinite lifetime and tips equal to the original ones through a clock)
gives the conclusion of `BW1PrefixPairRegStatement` at `ω`. -/
theorem conclusion_of_side {Ω : Type u} [MeasurableSpace Ω] {ν : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {C : Chart} (hC : C.IsConformal)
    {Wr : ℝ≥0 → Ω → ℝ} {ζr : Ω → ℝ≥0∞} {ℓ : Ω → ℝ≥0 → ℝ≥0}
    (hcf : ∃ h' : Ω → DistOn upperHalfPlaneOpens,
      (∀ ω', IsChartTransport C 1 0 (QuantumZipper.chiC κ) (h ω') (h' ω')) ∧
      IsCenteredCounterflowDriver κ ν h' Wr ζr)
    (hζr : ∀ᵐ ω' ∂ν, ζr ω' = ⊤)
    (htip : ∀ᵐ ω' ∂ν, ∀ (s : ℝ≥0) (z : ℂ),
      (C.trans infinitySourceChart).tipAt (fun s => Wr s ω') s z →
        infinitySourceChart.tipAt (fun s => W s ω') (ℓ ω' s) z)
    (h₂ : Ω → DistOn upperHalfPlaneOpens)
    (htr₂ : ∀ ω', IsChartTransport C 1 0 (QuantumZipper.chiC κ) (h ω') (h₂ ω')) :
    ∃ (W₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞),
      IsCenteredCounterflowDriver κ ν h₂ W₂ ζ₂ ∧
      (∀ᵐ ω' ∂ν, ζ₂ ω' = ⊤) ∧
      ∀ᵐ ω' ∂ν, ∀ (r : ℝ≥0) (z : ℂ),
        (C.trans infinitySourceChart).tipAt (fun s => W₂ s ω') r z →
          z ∈ counterflowCompletedRange (fun s => W s ω') := by
  obtain ⟨h', htr', hcf'⟩ := hcf
  have hh : h' = h₂ := funext fun ω' => (htr' ω').unique hC (htr₂ ω')
  subst hh
  refine ⟨Wr, ζr, hcf', hζr, ?_⟩
  filter_upwards [htip] with ω' hω' r z hz
  have h1 := hω' r z hz
  have h2 : z ∈ infinitySourceChart.tipSet (fun s => W s ω') ⊤ := by
    rw [Chart.tipSet_eq_tipAt]
    exact ⟨ℓ ω' r, le_top, h1⟩
  exact mem_union_left _ h2

/-- **`BW1PrefixPairRegStatement` from the source-form Proposition BW1 and the fixed-time input** (conditional helper
with a distinct name). -/
theorem bw1PrefixPairRegStatement_of_bw1 (hBW1 : BW1.BW1Statement.{u})
    (hFix : FlowFixedTimeInteriorStatement.{u}) : BW1PrefixPairRegStatement.{u} := by
  intro κ hκ hκ4 θ hθ b jumps hb Ω mΩ hSB Q hQ h hG W ζ hcf hζ e hem hreg hfl t g hgm hgeq
  have hst := isStagedHistory_oneSpec (κ := κ) t hb hem hreg hfl
  have h𝒢 : pastSigma κ b jumps (oneSpec θ t) (fun _ => e) 1 =
      MeasurableSpace.comap (fun ω => recOf t (e ω)) inferInstance := pastSigma_oneSpec_one θ t e
  have hrm : Measurable fun ω => recOf t (e ω) := measurable_recOf hem hreg t
  have hK : ∀ᵐ ω ∂Q, condExpKernel Q (MeasurableSpace.comap g inferInstance) ω =
      condExpKernel Q (pastSigma κ b jumps (oneSpec θ t) (fun _ => e) 1) ω := by
    rw [h𝒢]
    exact StagedReg.ae_condExpKernel_eq_of_ae_eq hgm hrm hgeq
  have hrun := ae_ae_run_eq (κ := κ) runMeasStatement hb (oneSpec θ t) (E := fun _ => e) (k := 1)
    (fun _ _ => hem) (fun _ _ => hreg) (P := Q)
  obtain ⟨W₁, ζ₁, ℓ₁, hc₁, -, hp₁⟩ :=
    hBW1 κ hκ hκ4 b jumps hb Q h hG W ζ hcf hζ θ hθ t false [] (fun _ => e) hst true
  obtain ⟨W₀, ζ₀, ℓ₀, hc₀, -, hp₀⟩ :=
    hBW1 κ hκ hκ4 b jumps hb Q h hG W ζ hcf hζ θ hθ t false [] (fun _ => e) hst false
  have hle : pastSigma κ b jumps (oneSpec θ t) (fun _ => e) 1 ≤ mΩ := hst.2.1 1
  have hp₁K := Sec7.Aux122Disint.ae_ae_condExpKernel hle hp₁
  have hp₀K := Sec7.Aux122Disint.ae_ae_condExpKernel hle hp₀
  have hhit := ae_exists_hit hκ hfl
  have hfix : ∀ᵐ ω ∂Q, t ≠ ⊤ → 0 < t → t < (e ω).2 → IsInteriorStop (e ω).1 t := by
    by_cases ht : t = ⊤
    · exact Eventually.of_forall fun _ h => absurd ht h
    by_cases ht0 : t = 0
    · exact Eventually.of_forall fun _ _ h => absurd ht0 h.ne'
    have htpos : 0 < t.toNNReal := ENNReal.toNNReal_pos ht0 ht
    filter_upwards [hFix κ hκ hκ4 θ hθ b jumps hb Q h hG _ _ hfl t.toNNReal htpos] with ω hω _ _ hlt
    have e1 : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) = t := ENNReal.coe_toNNReal ht
    rw [e1] at hω
    exact hω hlt
  filter_upwards [hK, hrun, hc₁, hc₀, hp₁K, hp₀K, hhit, hfix] with ω hKω hrunω hc₁ω hc₀ω hp₁ω hp₀ω hhitω hfixω
  intro hpos htop hcase hpr h₂ htr₂
  -- the real-tip case at a deterministic time is null: the stop is a finite threshold
  have hζt : (e ω).2 ≤ t := by
    rcases hcase with hc | hc
    · exact hc
    by_contra hlt'
    have hlt : t < (e ω).2 := not_le.1 hlt'
    have hmin : min t (e ω).2 = t := min_eq_left hlt.le
    rw [hmin] at hc hpos
    exact hc (hfixω (ne_top_of_lt hlt) hpos hlt)
  have hmin : min t (e ω).2 = (e ω).2 := min_eq_right hζt
  have hfin : (e ω).2 ≠ ⊤ := by rw [← hmin]; exact htop
  have hζ0 : (e ω).2 ≠ 0 := by rw [← hmin]; exact hpos.ne'
  -- the restarted state ends at a threshold on some side
  obtain ⟨r, hr⟩ : ∃ r : Bool,
      BW1.EndsAtThresholdSide (ExplState.run κ b jumps (oneSpec θ t) (fun _ => e ω) 1) r := by
    rw [run_oneSpec_one]
    refine endsAtThresholdSide_of_hit θ hζt hfin hζ0 ?_
    have hT : (((e ω).2.toNNReal : ℝ≥0) : ℝ≥0∞) = (e ω).2 := ENNReal.coe_toNNReal hfin
    have hTpos : 0 < (e ω).2.toNNReal := ENNReal.toNNReal_pos hζ0 hfin
    have hsT : stopTime t (e ω) = (((e ω).2.toNNReal : ℝ≥0) : ℝ) := by
      simp only [stopTime, hmin]
    rw [hsT]
    refine hhitω _ hTpos hT (stopDrv t (e ω)) fun s hs0 hsT' => ?_
    have hlt : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < (e ω).2 := by
      rw [← hT, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]
      exact hsT'
    simp only [stopDrv, retOf, hmin, min_eq_left hlt.le, ENNReal.toNNReal_coe]
  -- the state chart is the flow's own chart at the stop
  have hchart : BW1.stateChart (ExplState.run κ b jumps (oneSpec θ t) (fun _ => e ω) 1) =
      Chart.id.loewner (stopDrv t (e ω)) (stopTime t (e ω)) := by
    rw [run_oneSpec_one]
    have hm : min t (e ω).2 ≠ ⊤ := htop
    rw [BW1.stateChart, show (ExplState.launch (ExplState.init 0) 0 (e ω) θ t).2.2.2.2.1 =
      stChart (ExplState.launch (ExplState.init 0) 0 (e ω) θ t) from rfl,
      (launch_eq_of_ne_top (ExplState.init 0) 0 (e ω) θ t hm).1]
    rw [show stChart (ExplState.init 0) = Chart.id from Chart.recenter_zero _]
  have hU : Continuous (stopDrv t (e ω)) := hpr.continuous_stoppedReal.1
  have hU0 : stopDrv t (e ω) 0 = 0 := hpr.continuous_stoppedReal.2
  have hT0 : (0 : ℝ) ≤ stopTime t (e ω) := NNReal.coe_nonneg _
  have hconf := Chart.isConformal_id.loewner hU hU0 hT0
  rw [hKω]
  cases r
  · refine conclusion_of_side hconf (Wr := W₀) (ζr := ζ₀) (ℓ := ℓ₀) ?_ ?_ ?_ h₂ htr₂
    · obtain ⟨h', htr', hcf'⟩ := hc₀ω hr
      exact ⟨h', fun ω' => by rw [← hchart]; exact htr' ω', hcf'⟩
    · filter_upwards [hp₀ω, hrunω] with ω' h1 h2
      rw [h2] at h1
      exact (h1 hr).1
    · filter_upwards [hp₀ω, hrunω] with ω' h1 h2 s z hz
      rw [h2] at h1
      rw [← hchart] at hz
      exact ((h1 hr).2.2.2.2.2.2 s z).1 hz
  · refine conclusion_of_side hconf (Wr := W₁) (ζr := ζ₁) (ℓ := ℓ₁) ?_ ?_ ?_ h₂ htr₂
    · obtain ⟨h', htr', hcf'⟩ := hc₁ω hr
      exact ⟨h', fun ω' => by rw [← hchart]; exact htr' ω', hcf'⟩
    · filter_upwards [hp₁ω, hrunω] with ω' h1 h2
      rw [h2] at h1
      exact (h1 hr).1
    · filter_upwards [hp₁ω, hrunω] with ω' h1 h2 s z hz
      rw [h2] at h1
      rw [← hchart] at hz
      exact ((h1 hr).2.2.2.2.2.2 s z).1 hz

end GW2aStep

end Theorem14

end InteractingSLE
