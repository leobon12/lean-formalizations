/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5LfSide
import InteractingSLE.Spec.Sec7.R5LfSplit
import InteractingSLE.Spec.Sec7.PocketSideInPatchTip
import InteractingSLE.Spec.Sec7.PocketSideInSyncClock

/-!
# Lemma R.5's common phase from a fresh interior tip

Packet PROVE-R5-LIFT2 (third round). The pathwise part of `R5Lift.R7LiftCurTip(Inf)`: when the counterflow point
`η(T⁰(q))` at the left stop lies in the open pocket, the current inverse tends to it at the driver `0`, and `0` lies in
the open seed interval. What remains of `R7LiftCurTip` are two almost-sure facts (kept as named inputs, ruling of the
orchestrator): the fresh interior tip (`T⁰(q)` a cut time with `η(T⁰(q))` in the pocket) and the seed-interval
landings in `ℍ`.

* **`capTrace_eq_leftStop`**, **`tendsto_cur_tip_of_mem`**: at an interior left stop, the capacity trace at `q` is
  `ψ(η(T⁰(q)))` (the two ends of the erasure fibre coincide at a visit) and the current inverse lands at `η(T⁰(q))`
  from `0` (`PocketStopSide.tendsto_relative_inverse_tip`);

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Lift

open LocalSets PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide PhaseSel
  PocketWordAssembly PocketSeedOpen PocketCoord PocketJordan R5Phase R5Same R5Ref MartChar.RealFlow Sec6
  PocketStopWallsFin PocketStopMarked

variable {Ω : Type*}

section Bounded

variable {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ}
  {ω : Ω}

/-- **The capacity trace at an interior left stop** (bounded change pocket): if `η(T⁰(q)) ∈ C` at a positive live
relative capacity `q`, the relative trace at `q` is `ψ(η(T⁰(q)))`. -/
theorem capTrace_eq_leftStop (hcfg : IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) {q : ℝ≥0} (hq0 : 0 < q)
    (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω))
    (hin : η ω (leftStop R L r η ψ q ω) ∈ cfPocket (R ω) (L ω) r) :
    capTrace (travAll R L r η ψ ω) q = ψ ω (η ω (leftStop R L r η ψ q ω)) := by
  obtain ⟨hP, hψ'⟩ := pocket_of_cfg (W := fun ω (s : ℝ) => W' s.toNNReal ω) hcfg hψ
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (trav (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω)) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hq
  have hτT := lt_ambTime0 hP hcfg.attach hψ' (NNReal.coe_pos.2 hq0) hq'
  have hTσ := (ambTime0_mem_Ico hP hcfg.attach hψ' q.coe_nonneg hq').2
  have hvis : leftStop R L r η ψ q ω ∈ visitSet (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) :=
    ⟨⟨hτT, hTσ⟩, hin⟩
  have hγ := isDrivenCurve_relCurve_of_isReversePocket hP hcfg.attach hψ'
  have hL := hP.clock_σ_pos hcfg.attach
  obtain ⟨hc0, -⟩ := hγ.capInv_spec q.coe_nonneg hq'
  have hv := clockOf_mem_Ico hL hc0
  have hclock := clock_pocketFibreLeft hP ⟨hv.1, hv.2.le⟩
  have hfib := hP.fibre_clock_of_mem hvis
  have hLR : pocketFibre (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))
      (clockOf (pocketClock (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)))
        (capInv (trav (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
          (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω)) q)) = leftStop R L r η ψ q ω := by
    conv_lhs => rw [← hclock]
    exact hfib
  dsimp only [capTrace]
  change ψ ω (η ω (pocketFibre (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))
      (clockOf (pocketClock (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)))
        (capInv (trav (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
          (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω)) q)))) = _
  rw [hLR]

/-- **The current tip lands at `η(T⁰(q))`** (bounded change pocket): if `η(T⁰(q))` lies in the pocket at a positive
live relative capacity `q`, the current inverse tends to it at the driver `0`. -/
theorem tendsto_cur_tip_of_mem (hcfg : IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω))
    (hin : η ω (leftStop R L r η ψ q ω) ∈ cfPocket (R ω) (L ω) r) :
    Tendsto (relChart c (travAll R L r η ψ) q ω).2.1 (𝓝[H] ((0 : ℝ) : ℂ)) (𝓝 (η ω (leftStop R L r η ψ q ω))) := by
  have hγ := (hcfg.isDrivenCurve hψ).1
  have hp : η ω (leftStop R L r η ψ q ω) ∈ ((c ω).dom : Set ℂ) := by rw [hdom]; exact hin
  have h := tendsto_relative_inverse_tip hc hγ hq hp
    ((capTrace_eq_leftStop (W' := W') hcfg hψ hq0 hq hin).trans (heq hin).symm)
  rw [ofReal_zero]
  exact h

end Bounded

section BoundedRandom

variable [MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}

/-- **The two almost-sure facts of R.5's common phase** (bounded change pocket; named input): almost surely on the
live test, (i) every coordinate of the current open seed interval lands in `ℍ` (the base-point case of (G5) for the
relative chain), and (ii) the counterflow point at the left stop `T = T⁰(q)` is a fresh interior tip: it lies in the
pocket and `T` is a cut time (`η(T) ∉ η([0, T))`). -/
def R7FreshTip {nL nR : ℕ} (P : Measure Ω) (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart)
    (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) →
    (∀ u ∈ Ioo (geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL 0 q ω -
          segDriver (travAll R L r η ψ ω) q)
        (geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR 0 q ω -
          segDriver (travAll R L r η ψ ω) q), extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 u ∈ H) ∧
    η ω (leftStop R L r η ψ q ω) ∈ cfPocket (R ω) (L ω) r ∧
    YuanSimpleApprox.IsCutTime (η ω) (leftStop R L r η ψ q ω)

/-- **`R5Lift.R7LiftCurTip` from the two almost-sure facts** (bounded change pocket, positive capacity). -/
theorem r7LiftCurTip_of_fresh {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0) (hq0 : 0 < q) (h : R7FreshTip P A R L r η ψ xL xR c q) :
    R7LiftCurTip P A R L r η ψ xL xR c q := by
  filter_upwards [h] with ω hω hA hlive
  obtain ⟨hN1, hin, hcut⟩ := hω hA hlive
  have hγ := ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1
  have htip := tendsto_cur_tip_of_mem (hcfg ω hA) (hψ ω hA) (hc ω hA) (hdom ω hA) (heq ω hA) hq0 hlive hin
  have h0 := mem_seed_interval_of_landing (iL := 0) (iR := 0) (ξ := 0) (hxL ω) (hxR ω) (hc ω hA) hγ hlive htip
    (show _ ∈ ((c ω).dom : Set ℂ) by rw [hdom ω hA]; exact hin)
  obtain ⟨hP, hψ'⟩ := pocket_of_cfg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA)
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (trav (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω)) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hlive
  have hT0 : 0 < leftStop R L r η ψ q ω :=
    hP.nonneg.trans_lt (lt_ambTime0 hP (hcfg ω hA).attach hψ' (NNReal.coe_pos.2 hq0) hq')
  exact ⟨hN1, h0, hT0, hcut, htip⟩

/-- **`R5Lift.R7LiftCurGeom` from the two almost-sure facts** (bounded change pocket; vacuous at `q = 0`). -/
theorem r7LiftCurGeom_of_fresh {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0) (h : 0 < q → R7FreshTip P A R L r η ψ xL xR c q) :
    R7LiftCurGeom P A R L r η ψ xL xR c W' q := by
  rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h0q | h0q
  · subst h0q
    refine Eventually.of_forall fun ω hA hlive u hu => ?_
    rw [seed_interval_eq_empty_zero (c := c) (hxL ω) (hxR ω) ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1 hlive] at hu
    exact hu.elim
  · exact r7LiftCurGeom_of_tip hcfg hψ hc hdom heq hxL hxR
      (r7LiftCurTip_of_fresh (W' := W') hcfg hψ hc hdom heq hxL hxR h0q (h h0q))

/-- **`R5Lift.R7OuterLiftGeom` from the two almost-sure facts and the outer collars' `K_s`-landing** (bounded change
pocket; the side clause is vacuous at `q = 0`). -/
theorem r7OuterLiftGeom_of_fresh {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {X : Ω → Set ℂ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0) (h : 0 < q → R7FreshTip P A R L r η ψ xL xR c q)
    (ho : R7OuterRefl P A R L r η ψ xL xR c W' ζ' X q) :
    R7OuterLiftGeom P A R L r η ψ xL xR c W' ζ' X q := by
  rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h0q | h0q
  · subst h0q
    refine Eventually.of_forall fun ω hA hlive ξ _ _ hsel => ?_
    have hu := not_not.1 hsel.1
    rw [seed_interval_eq_empty_zero (c := c) (hxL ω) (hxR ω) ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1 hlive] at hu
    exact hu.elim
  · exact r7OuterLiftGeom_of_tip hcfg hψ hc hdom heq hxL hxR
      (r7LiftCurTip_of_fresh (W' := W') hcfg hψ hc hdom heq hxL hxR h0q (h h0q)) ho

end BoundedRandom

section SeedOpen

variable {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ}
  {ω : Ω}

/-- **The capacity trace at an interior left stop** (pocket opening at the flow seed). -/
theorem capTrace_eq_leftStopInf
    (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) {q : ℝ≥0} (hq0 : 0 < q)
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (hin : η ω (leftStopInf R L r η ψ q ω) ∈ cfPocket (R ω) (L ω) r) :
    capTrace (travAllInf R L r η ψ ω) q = ψ ω (η ω (leftStopInf R L r η ψ q ω)) := by
  obtain ⟨hP, hψ'⟩ := pocket_of_cfgInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hcfg hψ
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (travInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω)
      (cfArcRInf (R ω) (L ω) r 0)) (ψ ω)) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hq
  have hτT := lt_ambTime0Inf hP hcfg.attach hψ' (NNReal.coe_pos.2 hq0) hq'
  have hvis : leftStopInf R L r η ψ q ω ∈ visitSetInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω)
      (cfArcRInf (R ω) (L ω) r 0)) := ⟨hτT, hin⟩
  have hγ := isDrivenCurve_relCurve_of_isReversePocketInf hP hcfg.attach hψ'
  have hL := hP.clockEnd_pos hcfg.attach
  obtain ⟨hc0, -⟩ := hγ.capInv_spec q.coe_nonneg hq'
  have hv := clockOf_mem_Ico hL hc0
  have hclock := clock_pocketFibreLeftInf hP hv
  have hfib := hP.fibre_clock_of_mem hvis
  have hLR : pocketFibreInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))
      (clockOf (clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)))
      (capInv (travInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))
          (ψ ω)) q)) = leftStopInf R L r η ψ q ω := by
    conv_lhs => rw [← hclock]
    exact hfib
  dsimp only [capTrace]
  change ψ ω (η ω (pocketFibreInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))
      (clockOf (clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)))
      (capInv (travInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω)) q)))) = _
  rw [hLR]

/-- **The current tip lands at `η(T⁰(q))`** (pocket opening at the flow seed). -/
theorem tendsto_cur_tip_of_memInf
    (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (hin : η ω (leftStopInf R L r η ψ q ω) ∈ cfPocket (R ω) (L ω) r) :
    Tendsto (relChart c (travAllInf R L r η ψ) q ω).2.1 (𝓝[H] ((0 : ℝ) : ℂ))
      (𝓝 (η ω (leftStopInf R L r η ψ q ω))) := by
  have hγ := (hcfg.isDrivenCurve hψ).1
  have hp : η ω (leftStopInf R L r η ψ q ω) ∈ ((c ω).dom : Set ℂ) := by rw [hdom]; exact hin
  have h := tendsto_relative_inverse_tip hc hγ hq hp
    ((capTrace_eq_leftStopInf (W' := W') hcfg hψ hq0 hq hin).trans (heq hin).symm)
  rw [ofReal_zero]
  exact h

end SeedOpen

section SeedOpenRandom

variable [MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}

/-- **The two almost-sure facts of R.5's common phase** (pocket opening at the flow seed; named input): almost surely on
the live test, (i) every coordinate of the current open seed interval lands in `ℍ` (the base-point case of (G5) for the
relative chain), and (ii) the counterflow point at the left stop `T = T⁰(q)` is a fresh interior tip: it lies in the
pocket and `T` is a cut time (`η(T) ∉ η([0, T))`). -/
def R7FreshTipInf {nL nR : ℕ} (P : Measure Ω) (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart)
    (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
    (∀ u ∈ Ioo (geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL 0 q ω -
          segDriver (travAllInf R L r η ψ ω) q)
        (geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR 0 q ω -
          segDriver (travAllInf R L r η ψ ω) q), extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 u ∈ H) ∧
    η ω (leftStopInf R L r η ψ q ω) ∈ cfPocket (R ω) (L ω) r ∧
    YuanSimpleApprox.IsCutTime (η ω) (leftStopInf R L r η ψ q ω)

/-- **`R5Lift.R7LiftCurTipInf` from the two almost-sure facts** (pocket opening at the flow seed, positive capacity). -/
theorem r7LiftCurTipInf_of_fresh {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0) (hq0 : 0 < q) (h : R7FreshTipInf P A R L r η ψ xL xR c q) :
    R7LiftCurTipInf P A R L r η ψ xL xR c q := by
  filter_upwards [h] with ω hω hA hlive
  obtain ⟨hN1, hin, hcut⟩ := hω hA hlive
  have hγ := ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1
  have htip := tendsto_cur_tip_of_memInf (hcfg ω hA) (hψ ω hA) (hc ω hA) (hdom ω hA) (heq ω hA) hq0 hlive hin
  have h0 := mem_seed_interval_of_landing (iL := 0) (iR := 0) (ξ := 0) (hxL ω) (hxR ω) (hc ω hA) hγ hlive htip
    (show _ ∈ ((c ω).dom : Set ℂ) by rw [hdom ω hA]; exact hin)
  obtain ⟨hP, hψ'⟩ := pocket_of_cfgInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA)
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (travInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω)
      (cfArcRInf (R ω) (L ω) r 0)) (ψ ω)) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hlive
  have hT0 : 0 < leftStopInf R L r η ψ q ω :=
    hP.nonneg.trans_lt (lt_ambTime0Inf hP (hcfg ω hA).attach hψ' (NNReal.coe_pos.2 hq0) hq')
  exact ⟨hN1, h0, hT0, hcut, htip⟩

/-- **`R5Lift.R7LiftCurGeomInf` from the two almost-sure facts** (pocket opening at the flow seed; vacuous at `q = 0`).
-/
theorem r7LiftCurGeomInf_of_fresh {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0) (h : 0 < q → R7FreshTipInf P A R L r η ψ xL xR c q) :
    R7LiftCurGeomInf P A R L r η ψ xL xR c W' q := by
  rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h0q | h0q
  · subst h0q
    refine Eventually.of_forall fun ω hA hlive u hu => ?_
    rw [seed_interval_eq_empty_zero (c := c) (hxL ω) (hxR ω) ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1 hlive] at hu
    exact hu.elim
  · exact r7LiftCurGeomInf_of_tip hcfg hψ hc hdom heq hxL hxR
      (r7LiftCurTipInf_of_fresh (W' := W') hcfg hψ hc hdom heq hxL hxR h0q (h h0q))

/-- **`R5Lift.R7OuterLiftGeomInf` from the two almost-sure facts and the outer collars' `K_s`-landing** (bounded change
pocket; the side clause is vacuous at `q = 0`). -/
theorem r7OuterLiftGeomInf_of_fresh {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {X : Ω → Set ℂ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0) (h : 0 < q → R7FreshTipInf P A R L r η ψ xL xR c q)
    (ho : R7OuterReflInf P A R L r η ψ xL xR c W' ζ' X q) :
    R7OuterLiftGeomInf P A R L r η ψ xL xR c W' ζ' X q := by
  rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h0q | h0q
  · subst h0q
    refine Eventually.of_forall fun ω hA hlive ξ _ _ hsel => ?_
    have hu := not_not.1 hsel.1
    rw [seed_interval_eq_empty_zero (c := c) (hxL ω) (hxR ω) ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1 hlive] at hu
    exact hu.elim
  · exact r7OuterLiftGeomInf_of_tip hcfg hψ hc hdom heq hxL hxR
      (r7LiftCurTipInf_of_fresh (W' := W') hcfg hψ hc hdom heq hxL hxR h0q (h h0q)) ho

end SeedOpenRandom

end InteractingSLE.Sec7.R5Lift
