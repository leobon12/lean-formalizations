/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1TermLift

/-!
# BW1 at a walk launch: a piece with zero lifetime

Packet PROVE-BW1. When the launched piece dies at once (`D.2 = 0`, an immediately inadmissible seed), the post-piece
chart is the launch chart, the root and the piece are the single launch point, and BW1's relation is the identity:

* `termChart_inv_of_zero`, `termChart_fwd_of_zero`, `termChart_lift_of_zero`, **`isChartTransport_termChart_zero`**:
  the chart of a piece of zero lifetime reads every field as itself;
* **`isTermRelOf_self_of_zero`**: a regular counterflow driver is its own relative counterflow after such a piece.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMapInv)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.BW1Term

open Exist Exist.StagedLaw Exist.Staged GW1RestartPair

/-! ### The chart of a piece of zero lifetime -/

section Zero

variable {D : (ℝ≥0 → ℝ) × ℝ≥0∞}

theorem stopTime_of_zero (h0 : D.2 = 0) : stopTime ⊤ D = 0 := by
  simp [stopTime, h0]

theorem stopDrv_of_zero (hD : IsRegularDriver D) (h0 : D.2 = 0) : stopDrv ⊤ D = fun _ => 0 := by
  funext x
  simp [stopDrv, retOf, h0, hD.2.1]

theorem termChart_inv_of_zero (hD : IsRegularDriver D) (h0 : D.2 = 0) {w : ℂ} (hw : w ∈ H) :
    (termChart D).2.1 w = w := by
  simp only [termChart, Chart.loewner, Chart.recenter, Chart.id, stopTime_of_zero h0, stopDrv_of_zero hD h0]
  rw [fwdMapInv_zero_time continuous_const rfl hw]
  simp

theorem termChart_fwd_of_zero (hD : IsRegularDriver D) (h0 : D.2 = 0) {z : ℂ} (hz : z ∈ H) :
    (termChart D).1 z = z := by
  simp only [termChart, Chart.loewner, Chart.recenter, Chart.id, stopTime_of_zero h0, stopDrv_of_zero hD h0]
  have h1 := QuantumZipper.RS.fwdMap_fwdMapInv (W := fun _ => (0 : ℝ)) continuous_const rfl le_rfl hz
  rw [fwdMapInv_zero_time continuous_const rfl hz] at h1
  simpa only [Complex.ofReal_zero, sub_zero] using h1

theorem termChart_lift_of_zero (h0 : D.2 = 0) (x : ℂ) : (termChart D).2.2 x = 0 := by
  simp only [termChart, Chart.loewner, Chart.recenter, Chart.id, stopTime_of_zero h0,
    Coupling.MartMeans2.logDerivFwd_zero, Complex.zero_im, add_zero]

theorem image_termChart_inv_of_zero (hD : IsRegularDriver D) (h0 : D.2 = 0) : (termChart D).2.1 '' H = H := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    rwa [termChart_inv_of_zero hD h0 hv]
  · intro hw
    exact ⟨w, hw, termChart_inv_of_zero hD h0 hw⟩

/-- **The chart of a piece of zero lifetime reads every field as itself.** -/
theorem isChartTransport_termChart_zero (hD : IsRegularDriver D) (h0 : D.2 = 0) (k : ℝ)
    (h : DistOn upperHalfPlaneOpens) : IsChartTransport (termChart D) 1 0 k h h := by
  intro φ φ' _ hφ
  rw [image_termChart_inv_of_zero hD h0] at hφ
  have hd : ∀ z ∈ H, ‖deriv (termChart D).1 z‖ = 1 := by
    intro z hz
    have hev : (termChart D).1 =ᶠ[𝓝 z] id :=
      Filter.eventually_of_mem (QuantumZipper.isOpen_H.mem_nhds hz) fun y hy => termChart_fwd_of_zero hD h0 hy
    rw [hev.deriv_eq, deriv_id, norm_one]
  have e : φ = φ' := by
    ext z
    by_cases hz : z ∈ H
    · rw [hφ z hz, termChart_fwd_of_zero hD h0 hz, hd z hz, one_pow, mul_one]
    · rw [testOn_eq_zero_of_notMem_H φ hz, testOn_eq_zero_of_notMem_H φ' hz]
  subst e
  simp [termChart_lift_of_zero h0]

end Zero

/-! ### The relation for a piece of zero lifetime -/

section Self

/-- **No tip of a regular counterflow driver, read through the inversion, is at the root.** -/
theorem not_tipAt_zero {V : ℝ≥0 → ℝ} (hV : GW1Path.IsRegCf V) (t : ℝ≥0) : ¬ infinitySourceChart.tipAt V t 0 := by
  obtain ⟨hVc, hV0, γ, hγ, -⟩ := hV
  intro htip
  have hU : Continuous fun s : ℝ => V s.toNNReal := hVc.comp continuous_real_toNNReal
  have hU0 : (fun s : ℝ => V s.toNNReal) 0 = 0 := by simpa using hV0
  have hF := hγ.tendsto_fwdMapInv_mul_I hVc.continuousOn hV0 (ENNReal.coe_lt_top (r := t))
  have hmemH : ∀ y : ℝ, 0 < y → fwdMapInv (fun s : ℝ => V s.toNNReal) t ((y : ℂ) * Complex.I) ∈ H := fun y hy =>
    QuantumZipper.RS.fwdMapInv_mem_H hU hU0 (NNReal.coe_nonneg t)
      (show 0 < ((y : ℂ) * Complex.I).im by simpa using hy)
  have hpos : Tendsto (fun y : ℝ => ‖fwdMapInv (fun s : ℝ => V s.toNNReal) t ((y : ℂ) * Complex.I)‖⁻¹)
      (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h1 := htip.norm
      simp only [infinitySourceChart, norm_neg, norm_inv, norm_zero] at h1
      exact h1
    · filter_upwards [self_mem_nhdsWithin] with y hy
      have hne : fwdMapInv (fun s : ℝ => V s.toNNReal) t ((y : ℂ) * Complex.I) ≠ 0 := fun h0 => by
        have := hmemH y hy
        rw [h0] at this
        exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
      exact inv_pos.2 (norm_pos_iff.2 hne)
  have hbig : Tendsto (fun y : ℝ => ‖fwdMapInv (fun s : ℝ => V s.toNNReal) t ((y : ℂ) * Complex.I)‖)
      (𝓝[>] 0) atTop := by
    refine (tendsto_inv_nhdsGT_zero.comp hpos).congr fun y => ?_
    simp only [Function.comp_apply, inv_inv]
  exact not_tendsto_atTop_of_tendsto_nhds hF.norm hbig

theorem retOf_fst_of_zero {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : IsRegularDriver D) (h0 : D.2 = 0) :
    (retOf ⊤ D).1 = fun _ => 0 := by
  funext r
  simp [retOf, h0, hD.2.1]

/-- The root and a piece of zero lifetime are the launch point. -/
theorem termSet_of_zero {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : IsRegularDriver D) (h0 : D.2 = 0) :
    termSet D ⊆ {0} := by
  rintro z (hz | ⟨t, ht, hlim⟩)
  · exact hz
  · have hs : (retOf ⊤ D).2.1 = 0 := by simp [retOf, h0]
    rw [hs, nonpos_iff_eq_zero, ENNReal.coe_eq_zero] at ht
    subst ht
    rw [retOf_fst_of_zero hD h0] at hlim
    have hval : ∀ y : ℝ, 0 < y → (Chart.id.recenter 0).2.1
        (fwdMapInv (fun r : ℝ => (fun _ : ℝ≥0 => (0 : ℝ)) r.toNNReal) ((0 : ℝ≥0) : ℝ) ((y : ℂ) * Complex.I)) =
          (y : ℂ) * Complex.I := fun y hy => by
      have hyH : (y : ℂ) * Complex.I ∈ H := show 0 < ((y : ℂ) * Complex.I).im by simpa using hy
      simp only [Chart.recenter, Chart.id, NNReal.coe_zero]
      rw [fwdMapInv_zero_time continuous_const rfl hyH]
      simp
    have hI : Tendsto (fun y : ℝ => (y : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous fun y : ℝ => (y : ℂ) * Complex.I := Complex.continuous_ofReal.mul continuous_const
      have := hc.tendsto 0
      simp only [Complex.ofReal_zero, zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hlim2 : Tendsto (fun y : ℝ => (Chart.id.recenter 0).2.1
        (fwdMapInv (fun r : ℝ => (fun _ : ℝ≥0 => (0 : ℝ)) r.toNNReal) ((0 : ℝ≥0) : ℝ) ((y : ℂ) * Complex.I)))
        (𝓝[>] (0 : ℝ)) (𝓝 z) := hlim
    have hlim' := hlim2.congr' (eventually_nhdsWithin_of_forall (s := Set.Ioi (0 : ℝ)) fun y hy => hval y hy)
    exact mem_singleton_iff.2 (tendsto_nhds_unique hlim' hI)

/-- **A regular counterflow driver is its own relative counterflow after a piece of zero lifetime.** -/
theorem isTermRelOf_self_of_zero {V : ℝ≥0 → ℝ} (hV : GW1Path.IsRegCf V) {D : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hD : IsRegularDriver D) (h0 : D.2 = 0) : IsTermRelOf V V D := by
  have htop : firstTipTime infinitySourceChart V (termSet D) = ⊤ := by
    refine iInf₂_eq_top.2 fun t ht => ?_
    obtain ⟨z, hz, htip⟩ := ht
    rw [termSet_of_zero hD h0 hz] at htip
    exact absurd htip (not_tipAt_zero hV t)
  refine ⟨id, continuous_id, strictMono_id, ?_, fun r z => ?_⟩
  · rw [htop, range_id]
    ext s
    simp
  · obtain ⟨hVc, hV0, -⟩ := hV
    have hU : Continuous fun s : ℝ => V s.toNNReal := hVc.comp continuous_real_toNNReal
    have hU0 : (fun s : ℝ => V s.toNNReal) 0 = 0 := by simpa using hV0
    have heq : ∀ y : ℝ, 0 < y →
        ((termChart D).trans infinitySourceChart).2.1
          (fwdMapInv (fun s : ℝ => V s.toNNReal) r ((y : ℂ) * Complex.I)) =
        infinitySourceChart.2.1 (fwdMapInv (fun s : ℝ => V s.toNNReal) r ((y : ℂ) * Complex.I)) := by
      intro y hy
      have hmem : fwdMapInv (fun s : ℝ => V s.toNNReal) r ((y : ℂ) * Complex.I) ∈ H :=
        QuantumZipper.RS.fwdMapInv_mem_H hU hU0 (NNReal.coe_nonneg r)
          (show 0 < ((y : ℂ) * Complex.I).im by simpa using hy)
      rw [Chart.trans_inv]
      exact termChart_inv_of_zero hD h0 (GW2aPiece.neg_inv_mem_H hmem)
    exact tendsto_congr' (eventually_nhdsWithin_of_forall (s := Set.Ioi (0 : ℝ)) fun y hy => heq y hy)

end Self

/-! ### The identification for a piece of zero lifetime -/

section ZeroLaw

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **`P`-almost surely at a next launch whose piece has zero lifetime, the canonical post-piece counterflow is the
launch counterflow.** Under the conditional law `P₀` given the retained past before the launch, the piece is a flow
line of the field read in the launch chart, so its lifetime is almost surely `0` exactly when the seed is a threshold
(the frozen path conditions, `Coupling.ae_zeta_eq_zero_of_threshold`). If it is, the record of the piece is almost
surely constant, the conditional law given the retained past before `2n + 1` is `P₀` itself, the post-piece chart reads
the field as the launch chart does, and determination identifies the two centred counterflows; otherwise the event is
null. -/
theorem ae_isTermRelOf_zero (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {right : Bool} {n : ℕ}
    {V : ℝ≥0 → Ω → ℝ} {ζV : Ω → ℝ≥0∞} {ℓ : Ω → ℝ≥0 → ℝ≥0}
    (hdata : RestartData κ b jumps P h W' ζ' E right n V ζV ℓ) {Q : ℝ≥0 → Ω → ℝ} {ζQ : Ω → ℝ≥0∞}
    (hQ : GW1Laws.IsTerminalRestartCond κ b jumps P h right (E (GW1Z.walkSpec b jumps right)) n Q ζQ)
    (hQreg : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      ζQ ω = ⊤ ∧ Continuous (fun t => Q t ω) ∧ Q 0 ω = 0) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      (E (GW1Z.walkSpec b jumps right) (2 * n) ω).2 = 0 →
      GW1Path.IsRegCf (fun t => Q t ω) ∧
        IsTermRelOf (fun t => Q t ω) (fun t => V t ω) (E (GW1Z.walkSpec b jumps right) (2 * n) ω) := by
  classical
  have hκ := hdata.pos
  have hκ4 := hdata.lt_four
  have hb := hdata.boundary
  have hh := hdata.field
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (GW1Z.walkAngle_mem_Icc right) right
  have hE := hdata.staged _ hprog
  have hreg := hdata.regular (GW1Z.walkSpec b jumps right)
  have hRp := hdata.pieces _ hprog
  obtain ⟨hambL, hambR⟩ := GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀)
    hκ hκ4 hb hh hdata.counterflow hdata.complete
  obtain ⟨β₀, Y₀, hW₀⟩ : ∃ (β : Ω → Restart.BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) (2 * n) β Y := by
    cases right
    · obtain ⟨β, Y, hW, -⟩ := GW1W.exists_witness_left hκ hb hh hE hreg hambR (2 * n)
      exact ⟨β, Y, hW⟩
    · obtain ⟨β, Y, hW, -⟩ := GW1W.exists_witness_right hκ hb hh hE hreg hambL (2 * n)
      exact ⟨β, Y, hW⟩
  have hpm : ∀ k, Measurable[pastSigma κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) k]
      (pastMap κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) k) := fun k s hs => by
    rw [pastSigma_eq_comap]
    exact ⟨s, hs, rfl⟩
  have hpmΩ : ∀ k, Measurable (pastMap κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) k) :=
    fun k => (hpm k).mono (hE.2.1 k) le_rfl
  have hcg : @MeasurableSpace.CountablyGenerated Ω
      (pastSigma κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) (2 * n + 1)) := by
    rw [pastSigma_eq_comap]
    exact MeasurableSpace.CountablyGenerated.comap _
  have hL0 := GW1W.measurableSet_pastSigma_launch (κ := κ) hb (GW1Z.walkSpec b jumps right) hE.1 hreg (2 * n)
  have hLn := GW1W.measurableSet_pastSigma_launch (κ := κ) hb (GW1Z.walkSpec b jumps right) hE.1 hreg (2 * (n + 1))
  have hrun0 := CondDriverBridge.ae_ae_run_eq_of_le (κ := κ) (b := b) (jumps := jumps) (P := P)
    (GW1Z.walkSpec b jumps right) (k := 2 * n) (fun j _ => hreg j) (hE.2.1 (2 * n)) le_rfl
  have hVreg : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * n + 1)).2.2.2.1 (2 * n) ≠ none →
      GW1Path.IsRegCf (fun t => V t ω) := by
    filter_upwards [hdata.current.2.2] with ω hω hl
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
    obtain ⟨-, hc, h0, htr, -⟩ := hω c θ hcθ
    exact ⟨hc, h0, htr⟩
  have hprev : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω)
        (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω)
        (2 * n + 1)).2.2.2.1 (2 * n) ≠ none := by
    filter_upwards [hdata.stages, hRp] with ω hs hp
    apply GW1LaunchClock.previous_launch_of_next hκ hb _ (fun j => hreg j ω) hs ?_ hdata.lt_card
    intro j c θ hl
    exact hp j θ _ c (eq_launch_of_launches _ _ hl).1 hl
  -- the measurable events
  set A : Set Ω := ⋂ q : ℚ, {ω | Q (Real.toNNReal q) ω = V (Real.toNNReal q) ω} with hAdef
  have hA : MeasurableSet A :=
    MeasurableSet.iInter fun q => measurableSet_eq_fun (hQ.1 _) (hdata.current.1 _)
  set NZ : Set Ω := {ω | (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none} ∩
    {ω | (E (GW1Z.walkSpec b jumps right) (2 * n) ω).2 = 0} with hNZdef
  have hNZ : MeasurableSet NZ :=
    (hE.2.1 _ _ hLn).inter ((measurable_snd.comp (hE.1 (2 * n))) (measurableSet_singleton 0))
  -- (1) under the conditional law given the retained past before `2n`
  have h1 : ∀ᵐ ω₀ ∂P, ω₀ ∈ {ω | (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * n + 1)).2.2.2.1 (2 * n) ≠ none} →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀), ω ∈ NZᶜ ∪ A := by
    filter_upwards [hE.2.2.2 (2 * n), hW₀.2.2.1, hdata.current.2.1,
      KernelTower.ae_ae_condExpKernel_condExpKernel_eq (P := P)
        (pastSigma_mono (κ := κ) (b := b) (jumps := jumps) (GW1Z.walkSpec b jumps right)
          (E (GW1Z.walkSpec b jumps right)) (Nat.le_succ (2 * n))) (hE.2.1 (2 * n + 1)) hcg,
      Sec7.Aux122Disint.ae_ae_condExpKernel_eq (hE.2.1 (2 * n)) (hpm (2 * n)), hrun0,
      Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) (hE.2.1 (2 * n)) hL0,
      Sec7.Aux122Disint.ae_ae_condExpKernel (hE.2.1 (2 * n)) hQ.2]
      with ω₀ hst hconf hclock hkk hpmω hrunω hLω hQω hl0
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl0
    obtain ⟨hc_eq, -⟩ := launch_record_walk hcθ
    obtain ⟨b', J', hc, hb', htrc, hfl⟩ := hst c θ hcθ
    have hgff := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hb' hfl
    obtain ⟨hcfV, hζV⟩ := hclock c θ hcθ hc htrc
    obtain ⟨hcconf, hclift, -⟩ := hconf hl0
    have hcconf' : c.IsConformal := by rw [hc_eq]; exact hcconf
    have hclift' : ContinuousOn (fun w => c.2.2 (c.2.1 w)) QuantumZipper.H := by rw [hc_eq]; exact hclift
    obtain ⟨h₁, 𝓕, VL, VR, B, -, hcoup⟩ := hfl
    by_cases hthr : ForceWord.ThresholdCondition (flowLineRhoL κ b' J' 0 θ) (flowLineRhoR κ b' J' 0 θ) 0
      (flowLineXL b' J' 0) (flowLineXR b' J' 0)
    · have hζ0 := Coupling.ae_zeta_eq_zero_of_threshold hcoup.1 hthr
      -- the retained past before `2n + 1` is trivial under `P₀`
      have hK0 : ∀ᵐ ω₁ ∂(condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
          (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀),
          condExpKernel (condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
            (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀) (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
              (E (GW1Z.walkSpec b jumps right)) (2 * n + 1)) ω₁ =
            condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
              (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀ := by
        have hc0 := KernelTower.ae_condExpKernel_comap_eq (P := condExpKernel P (pastSigma κ b jumps
          (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀)
          (hpmΩ (2 * n + 1)) (measurable_const (a := ()))
          (φ := fun _ => Fin.snoc (α := fun _ => RecData)
            (pastMap κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) (2 * n) ω₀)
            (((fun _ : ℚ => (0 : ℝ)), (0 : ℝ≥0∞), true) : RecData)) measurable_const
          (ψ := fun _ => ()) measurable_const ?_ (Eventually.of_forall fun _ => rfl)
        · rw [← pastSigma_eq_comap, MeasurableSpace.comap_const] at hc0
          filter_upwards [hc0] with ω₁ hω₁
          rw [hω₁, GW1.condExpKernel_bot_apply]
        · filter_upwards [hpmω, hLω hl0, hζ0] with ω hω hl hz
          rw [GW2Later.pastMap_succ_eq_snoc _ _ (2 * n) ω, hω]
          congr 1
          simp only [pastMap, Fin.val_last]
          rw [retained_run_walk hl, retOf_fst_of_zero (hreg (2 * n) ω) hz]
          simp [retOf, hz]
      -- determination under `P₀` at every next launch
      have h2 : ∀ᵐ ω₁ ∂(condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
          (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀),
          (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω₁)
            (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
          ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
            (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀), ω ∈ A := by
        filter_upwards [hK0, hkk, hrunω, hLω hl0, hζ0, hQω] with ω₁ hK0ω hkkω hrunω₁ hl1 hz1 hQ₁ hn1
        have hμ := hkkω.symm.trans hK0ω
        have hfin : (E (GW1Z.walkSpec b jumps right) (2 * n) ω₁).2 ≠ ⊤ := by
          rw [hz1]
          exact ENNReal.zero_ne_top
        have hc1 : stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
            (fun j => E (GW1Z.walkSpec b jumps right) j ω₁) (2 * n)) = c := by rw [hc_eq, hrunω₁]
        have hU : Continuous (stopDrv ⊤ (E (GW1Z.walkSpec b jumps right) (2 * n) ω₁)) ∧
            stopDrv ⊤ (E (GW1Z.walkSpec b jumps right) (2 * n) ω₁) 0 = 0 := by
          rw [stopDrv_of_zero (hreg (2 * n) ω₁) hz1]
          exact ⟨continuous_const, rfl⟩
        have hT : 0 ≤ stopTime ⊤ (E (GW1Z.walkSpec b jumps right) (2 * n) ω₁) := stopTime_nonneg _ _
        have hc₂ : (termChart (E (GW1Z.walkSpec b jumps right) (2 * n) ω₁)).IsConformal := by
          rw [termChart, Chart.recenter_zero]
          exact Chart.isConformal_id.loewner hU.1 hU.2 hT
        have hℓ₂ : ContinuousOn (fun w => (termChart (E (GW1Z.walkSpec b jumps right) (2 * n) ω₁)).2.2
            ((termChart (E (GW1Z.walkSpec b jumps right) (2 * n) ω₁)).2.1 w)) QuantumZipper.H := by
          rw [termChart, Chart.recenter_zero]
          exact (Chart.isConformal_id.loewner hU.1 hU.2 hT).continuousOn_lift_inv
            (Chart.continuousOn_lift_loewner hU.1 hU.2 hT)
        have htrd : ∀ ω, IsChartTransport (stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
            (fun j => E (GW1Z.walkSpec b jumps right) j ω₁) (2 * n + 1))) 1 0 (QuantumZipper.chiC κ) (h ω)
              (hc ω) := fun ω => by
          rw [stChart_run_succ_eq_trans hl1 hfin, hc1]
          exact IsChartTransport.trans hcconf' hc₂ hclift' hℓ₂ (htrc ω)
            (isChartTransport_termChart_zero (hreg (2 * n) ω₁) hz1 _ _)
        obtain ⟨hcfQ, hζQ⟩ := hQ₁ hn1 hc htrd
        rw [hμ] at hcfQ hζQ
        have hdet := GW4Ident.ae_eq_of_isCenteredCounterflowDriver h12p hT13 hκ hb' hgff hcfQ hζQ hcfV hζV
        filter_upwards [hdet] with ω hω
        exact mem_iInter.2 fun q => congrFun hω _
      by_cases hall : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
          (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀), ω ∈ A
      · filter_upwards [hall] with ω hω
        exact Or.inr hω
      · have hn : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
            (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀),
            ¬ (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
              (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none :=
          h2.mono fun ω₁ h hn => hall (h hn)
        filter_upwards [hn] with ω hω
        exact Or.inl fun h' => hω h'.1
    · have hpos : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
          (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀), (E (GW1Z.walkSpec b jumps right) (2 * n) ω).2 ≠ 0 := by
        filter_upwards [hcoup.1.2.2.2.2] with ω hP hz
        exact hthr (hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hz)
      filter_upwards [hpos] with ω hω
      exact Or.inl fun h' => hω h'.2
  -- (2) under `P`
  have h2 := GW2Later.ae_of_ae_condExpKernel_on' (hE.2.1 (2 * n)) hL0 (hNZ.compl.union hA) h1
  filter_upwards [h2, hprev, hVreg, hQreg] with ω hω hpv hVr hQr hn hz
  have hl := hpv hn
  have hA' : ω ∈ A := (hω hl).resolve_left fun h' => h' ⟨hn, hz⟩
  have hQV : (fun t => Q t ω) = fun t => V t ω :=
    Continuous.ext_on denseRange_toNNReal_rat (hQr hn).2.1 (hVr hl).1
      (by rintro _ ⟨q, rfl⟩; exact (mem_iInter.1 hA') q)
  rw [hQV]
  exact ⟨hVr hl, isTermRelOf_self_of_zero (hVr hl) (hreg (2 * n) ω) hz⟩

end ZeroLaw

end InteractingSLE.Theorem14.BW1Term
