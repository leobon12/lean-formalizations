/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5FreshAnchor

/-!
# Lemma R.5's current-chart geometry from the seed-interval landings alone

Packet PROVE-R5-FRESHTIP. The two almost-sure facts `R5Lift.R7FreshTip(Inf)` were (i) every coordinate of the current
open seed interval lands in `ℍ` and (ii) the left stop `T⁰(q)` is a fresh interior tip. Fact (ii) is **not needed**:
the side agreement it served is proved here pathwise from (i) (`R5Fresh.curSide_of_seedLand`), at every left stop.

* **`exists_lt_leftStop(Inf)`**: the left stops of smaller capacities approach `T⁰(q)` from below (`T⁰(q') ≤ t ↔
  q' ≤ relCap(t)`);
* `R7SeedLand(Inf)` (defs, **named input**): fact (i) alone; `r7SeedLand(Inf)_of_fresh` (it is implied by
  `R7FreshTip(Inf)`), `r7SeedLand(Inf)_zero` (it holds at `q = 0`), **`r7SeedLand(Inf)_of_corner_mem_H`** (it holds
  pathwise when the pocket's corner is not real: fact (i) is a genuine input only for pockets closing at the flow
  target, whose corner is the counterflow's start);
* **`ae_curSide(Inf)_of_seedLand`**: the side agreement at `T⁰(q)` from fact (i);
* **`r7LiftCurGeom(Inf)_of_seedLand`**, **`r7OuterLiftGeom(Inf)_of_seedLand`**: the two current-chart inputs of
  `R5Wall.TwoSeedSplitInputCur(Inf)` from fact (i) (and, for the outer one, `R5Lift.R7OuterRefl(Inf)`).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Fresh

open LocalSets PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide PhaseSel
  PocketWordAssembly PocketSeedOpen PocketCoord PocketJordan R5Phase R5Same R5Ref MartChar.RealFlow Sec6
  PocketStopWallsFin PocketStopMarked R5Lift

variable {Ω : Type*}

/-! ### The left stops of smaller capacities -/

section Stops

variable {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {ω : Ω}

/-- **The left stops of smaller capacities approach `T⁰(q)` from below** (bounded change pocket): for `q > 0` live
and `t₀ < T⁰(q)` some `q' < q` has `t₀ < T⁰(q') ≤ T⁰(q)` (take `q'` between `relCap(max τ t₀)` and `q`). -/
theorem exists_lt_leftStop (hcfg : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) {q : ℝ≥0} (hq0 : 0 < q)
    (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) {t₀ : ℝ} (ht₀ : t₀ < leftStop R L r η ψ q ω) :
    ∃ q' : ℝ≥0, q' < q ∧ t₀ < leftStop R L r η ψ q' ω ∧ leftStop R L r η ψ q' ω ≤ leftStop R L r η ψ q ω := by
  obtain ⟨hP, hψ'⟩ := pocket_of_cfg hcfg hψ
  have hAC := hcfg.attach
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (trav (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω)) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hq
  have hT := ambTime0_mem_Ico hP hAC hψ' q.coe_nonneg hq'
  have hτT := lt_ambTime0 hP hAC hψ' (NNReal.coe_pos.2 hq0) hq'
  set t₁ := max (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) t₀ with ht₁
  have ht₁T : t₁ < leftStop R L r η ψ q ω := max_lt hτT ht₀
  have ht₁m : t₁ ∈ Ico (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) :=
    ⟨le_max_left _ _, ht₁T.trans hT.2⟩
  have hrc := relCap_lt_of_lt_ambTime0 hP hAC hψ' q.coe_nonneg hq' ht₁m ht₁T
  have hrc0 : 0 ≤ relCap (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) t₁ :=
    (isDrivenCurve_relCurve_of_isReversePocket hP hAC hψ').capClock_nonneg (relTime_nonneg hP hAC ht₁m)
  set ρ := relCap (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) t₁ with hρ
  set q' : ℝ≥0 := ⟨(ρ + q) / 2, by positivity⟩ with hq'def
  have hq'c : (q' : ℝ) = (ρ + q) / 2 := rfl
  have hq'q : (q' : ℝ) < q := by rw [hq'c]; linarith
  have hq'live : ENNReal.ofReal (q' : ℝ) < capLife (trav (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω)) :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hq'q.le) hq'
  have hqrel := (ambTime0_le_iff hP hAC hψ' q.coe_nonneg hq' hT).1 le_rfl
  refine ⟨q', by exact_mod_cast hq'q, ?_, (ambTime0_le_iff hP hAC hψ' q'.coe_nonneg hq'live hT).2
    (hq'q.le.trans hqrel)⟩
  by_contra hle
  push Not at hle
  have h := (ambTime0_le_iff hP hAC hψ' q'.coe_nonneg hq'live ht₁m).1 (hle.trans (le_max_right _ _))
  rw [hq'c] at h
  linarith

/-- **The left stops of smaller capacities approach `T⁰(q)` from below** (pocket opening at the flow seed). -/
theorem exists_lt_leftStopInf (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) {q : ℝ≥0} (hq0 : 0 < q)
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) {t₀ : ℝ} (ht₀ : t₀ < leftStopInf R L r η ψ q ω) :
    ∃ q' : ℝ≥0, q' < q ∧ t₀ < leftStopInf R L r η ψ q' ω ∧
      leftStopInf R L r η ψ q' ω ≤ leftStopInf R L r η ψ q ω := by
  obtain ⟨hP, hψ'⟩ := pocket_of_cfgInf hcfg hψ
  have hAC := hcfg.attach
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (travInf (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω)) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hq
  have hTτ := le_ambTime0Inf hP hAC (ψ ω) q
  have hτT := lt_ambTime0Inf hP hAC hψ' (NNReal.coe_pos.2 hq0) hq'
  set t₁ := max (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) t₀ with ht₁
  have ht₁T : t₁ < leftStopInf R L r η ψ q ω := max_lt hτT ht₀
  have ht₁m : firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0) ≤ t₁ := le_max_left _ _
  have hrc := relCapInf_lt_of_lt_ambTime0Inf hP hAC hψ' q.coe_nonneg hq' ht₁m ht₁T
  have hrc0 : 0 ≤ relCapInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) t₁ :=
    (isDrivenCurve_relCurve_of_isReversePocketInf hP hAC hψ').capClock_nonneg (relTimeInf_nonneg hP hAC ht₁m)
  set ρ := relCapInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) t₁ with hρ
  set q' : ℝ≥0 := ⟨(ρ + q) / 2, by positivity⟩ with hq'def
  have hq'c : (q' : ℝ) = (ρ + q) / 2 := rfl
  have hq'q : (q' : ℝ) < q := by rw [hq'c]; linarith
  have hq'live : ENNReal.ofReal (q' : ℝ) < capLife (travInf (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω)) :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hq'q.le) hq'
  have hqrel := (ambTime0Inf_le_iff hP hAC hψ' q.coe_nonneg hq' hTτ).1 le_rfl
  refine ⟨q', by exact_mod_cast hq'q, ?_, (ambTime0Inf_le_iff hP hAC hψ' q'.coe_nonneg hq'live hTτ).2
    (hq'q.le.trans hqrel)⟩
  by_contra hle
  push Not at hle
  have h := (ambTime0Inf_le_iff hP hAC hψ' q'.coe_nonneg hq'live ht₁m).1 (hle.trans (le_max_right _ _))
  rw [hq'c] at h
  linarith

end Stops

/-! ### Bounded change pocket -/

section Bounded

variable [MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}

/-- **The seed-interval landings of the current chart** (bounded change pocket; named input): almost surely on the
live test, every coordinate of the current open seed interval lands in `ℍ` (off the pocket's possible real corner) —
the base-point case of Zhan's (G5) for the relative chain. This is fact (i) of `R5Lift.R7FreshTip` alone. -/
def R7SeedLand {nL nR : ℕ} (P : Measure Ω) (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart)
    (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) →
    ∀ u ∈ Ioo (geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL 0 q ω -
          segDriver (travAll R L r η ψ ω) q)
        (geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR 0 q ω -
          segDriver (travAll R L r η ψ ω) q), extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 u ∈ H

/-- `R5Lift.R7FreshTip` implies `R7SeedLand` (its first clause). -/
theorem r7SeedLand_of_fresh {nL nR : ℕ} {P : Measure Ω} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    {c : Ω → Chart} {q : ℝ≥0} (h : R7FreshTip P A R L r η ψ xL xR c q) : R7SeedLand P A R L r η ψ xL xR c q := by
  filter_upwards [h] with ω hω hA hlive
  exact (hω hA hlive).1

/-- **`R7SeedLand` when the pocket's closing corner is not real** (bounded change pocket; pathwise): every landing
lies in the closed pocket, whose only possible real point is the corner `cfArcR 1` (`m(y₀)`). So fact (i) is a
genuine input only for pockets closing at the flow target (corner `η(0) = 0`). -/
theorem r7SeedLand_of_corner_mem_H {nL nR : ℕ} {P : Measure Ω} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hcorner : ∀ ω ∈ A, cfArcR (R ω) (L ω) r 1 ∈ H) : R7SeedLand P A R L r η ψ xL xR c q := by
  refine Eventually.of_forall fun ω hA hlive u _ => ?_
  obtain ⟨-, hcl, -⟩ := current_landing (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA)
    (hdom ω hA) (heq ω hA) hlive u
  have hP := (pocket_of_cfg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA)).1
  have hsub := closure_cfPocket_subset_H_union_seed ((hcfg ω hA).conf.isCfPocket
    (PocketMarks.zero_notMem_closure_of_rightLo_pos (hcfg ω hA).conf (hcfg ω hA).bounded)) hP.subset_H
  rcases hsub hcl with h | h
  · exact h
  · rw [mem_singleton_iff.1 h]
    exact hcorner ω hA

/-- `R7SeedLand` holds at capacity `0` (the open seed interval is empty). -/
theorem r7SeedLand_zero {nL nR : ℕ} {P : Measure Ω} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0) :
    R7SeedLand P A R L r η ψ xL xR c 0 := by
  refine Eventually.of_forall fun ω hA hlive u hu => ?_
  rw [seed_interval_eq_empty_zero (c := c) (hxL ω) (hxR ω) ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1 hlive] at hu
  exact hu.elim

/-- **The side agreement at the left stop from the seed-interval landings** (bounded change pocket): under
`R7SeedLand`, almost surely on the live test, at every coordinate `u` of the current open seed interval every real
limit `y` of `f_T ∘ cur⁻¹` (`T = T⁰(q)`) satisfies `u < 0 ↔ y < 0`. No fresh tip is used. -/
theorem ae_curSide_of_seedLand {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0) (h : R7SeedLand P A R L r η ψ xL xR c q) :
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) →
      ∀ u ∈ Ioo (geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL 0 q ω - segDriver (travAll R L r η ψ ω) q)
        (geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR 0 q ω - segDriver (travAll R L r η ψ ω) q), ∀ y : ℝ,
        Tendsto (fun z => fwdMap (fun t : ℝ => W' t.toNNReal ω) (leftStop R L r η ψ q ω)
          ((relChart c (travAll R L r η ψ) q ω).2.1 z)) (𝓝[H] (u : ℂ)) (𝓝 (y : ℂ)) → (u < 0 ↔ y < 0) := by
  filter_upwards [h] with ω hω hA hlive u hu
  have hN1 := hω hA hlive
  have hγ := ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1
  have hq0 : 0 < q := by
    rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h0q | h0q
    · exfalso
      subst h0q
      rw [seed_interval_eq_empty_zero (c := c) (hxL ω) (hxR ω) hγ hlive] at hu
      exact hu
    · exact h0q
  obtain ⟨E, hE, hEc, -⟩ := exists_inverse_extension_of_jordan_cases
    (jordan_of_cfg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA))
    (hc ω hA) (hdom ω hA) (heq ω hA)
  refine curSide_of_seedLand (hxL ω) (hxR ω) (hc ω hA) hγ hlive hq0 hE hEc (hdom ω hA) (hcfg ω hA).trace
    (hcfg ω hA).continuous_W (hcfg ω hA).W_zero
    (T := fun q' => leftStop R L r η ψ q' ω)
    (fun q' => leftStop_nonneg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA) q')
    (fun q' hq' => ?_) (fun t₀ ht₀ => exists_lt_leftStop (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA)
      (hψ ω hA) hq0 hlive ht₀) hN1 u hu
  have hq'live : (q' : ℝ≥0∞) < capLife (travAll R L r η ψ ω) :=
    lt_of_le_of_lt (by exact_mod_cast hq') hlive
  rw [current_dom_eq (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA) (hdom ω hA)
      (heq ω hA) hq'live, ← (hcfg ω hA).trace.2.2 _
      (leftStop_nonneg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA) q')]

/-- **`R5Lift.R7LiftCurGeom` from the seed-interval landings** (bounded change pocket). -/
theorem r7LiftCurGeom_of_seedLand {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0) (h : R7SeedLand P A R L r η ψ xL xR c q) :
    R7LiftCurGeom P A R L r η ψ xL xR c W' q := by
  filter_upwards [h, ae_curSide_of_seedLand (W' := W') hcfg hψ hc hdom heq hxL hxR h] with ω hω hs hA hlive u hu
  exact ⟨hω hA hlive u hu, fun _ => hs hA hlive u hu⟩

/-- **`R5Lift.R7OuterLiftGeom` from the seed-interval landings and the outer collars' `K_s`-landing** (bounded change
pocket). -/
theorem r7OuterLiftGeom_of_seedLand {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {X : Ω → Set ℂ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0) (h : R7SeedLand P A R L r η ψ xL xR c q)
    (ho : R7OuterRefl P A R L r η ψ xL xR c W' ζ' X q) :
    R7OuterLiftGeom P A R L r η ψ xL xR c W' ζ' X q := by
  filter_upwards [ho, ae_curSide_of_seedLand (W' := W') hcfg hψ hc hdom heq hxL hxR h] with ω hω hs hA hlive ξ hξ hX
    hsel
  exact ⟨fun y hy => hs hA hlive ξ (not_not.1 hsel.1) y hy, hω hA hlive ξ hξ hX hsel⟩

end Bounded

/-! ### Change pocket opening at the flow seed -/

section SeedOpen

variable [MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}

/-- **The seed-interval landings of the current chart** (pocket opening at the flow seed; named input): fact (i) of
`R5Lift.R7FreshTipInf` alone. -/
def R7SeedLandInf {nL nR : ℕ} (P : Measure Ω) (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart)
    (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
    ∀ u ∈ Ioo (geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL 0 q ω -
          segDriver (travAllInf R L r η ψ ω) q)
        (geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR 0 q ω -
          segDriver (travAllInf R L r η ψ ω) q), extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 u ∈ H

/-- `R5Lift.R7FreshTipInf` implies `R7SeedLandInf` (its first clause). -/
theorem r7SeedLandInf_of_fresh {nL nR : ℕ} {P : Measure Ω} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {q : ℝ≥0} (h : R7FreshTipInf P A R L r η ψ xL xR c q) :
    R7SeedLandInf P A R L r η ψ xL xR c q := by
  filter_upwards [h] with ω hω hA hlive
  exact (hω hA hlive).1

/-- **`R7SeedLandInf` when the pocket's corner `cfArcRInf 0` is not real** (pocket opening at the flow seed;
pathwise). -/
theorem r7SeedLandInf_of_corner_mem_H {nL nR : ℕ} {P : Measure Ω} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hcorner : ∀ ω ∈ A, cfArcRInf (R ω) (L ω) r 0 ∈ H) : R7SeedLandInf P A R L r η ψ xL xR c q := by
  refine Eventually.of_forall fun ω hA hlive u _ => ?_
  obtain ⟨-, hcl, -⟩ := current_landingInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA)
    (hc ω hA) (hdom ω hA) (heq ω hA) hlive u
  have hsub := closure_cfPocketInf_subset_H_union_seed ((hcfg ω hA).conf.isCfPocketInf (hcfg ω hA).seed)
  rcases hsub hcl with h | h
  · exact h
  · rw [mem_singleton_iff.1 h]
    exact hcorner ω hA

/-- `R7SeedLandInf` holds at capacity `0` (the open seed interval is empty). -/
theorem r7SeedLandInf_zero {nL nR : ℕ} {P : Measure Ω} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0) :
    R7SeedLandInf P A R L r η ψ xL xR c 0 := by
  refine Eventually.of_forall fun ω hA hlive u hu => ?_
  rw [seed_interval_eq_empty_zero (c := c) (hxL ω) (hxR ω) ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1 hlive] at hu
  exact hu.elim

/-- **The side agreement at the left stop from the seed-interval landings** (pocket opening at the flow seed). -/
theorem ae_curSideInf_of_seedLand {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0) (h : R7SeedLandInf P A R L r η ψ xL xR c q) :
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
      ∀ u ∈ Ioo (geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL 0 q ω -
          segDriver (travAllInf R L r η ψ ω) q)
        (geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR 0 q ω -
            segDriver (travAllInf R L r η ψ ω) q), ∀ y : ℝ,
        Tendsto (fun z => fwdMap (fun t : ℝ => W' t.toNNReal ω) (leftStopInf R L r η ψ q ω)
          ((relChart c (travAllInf R L r η ψ) q ω).2.1 z)) (𝓝[H] (u : ℂ)) (𝓝 (y : ℂ)) → (u < 0 ↔ y < 0) := by
  filter_upwards [h] with ω hω hA hlive u hu
  have hN1 := hω hA hlive
  have hγ := ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1
  have hq0 : 0 < q := by
    rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h0q | h0q
    · exfalso
      subst h0q
      rw [seed_interval_eq_empty_zero (c := c) (hxL ω) (hxR ω) hγ hlive] at hu
      exact hu
    · exact h0q
  obtain ⟨E, hE, hEc, -⟩ := exists_inverse_extension_of_jordan_cases (Or.inr (hψ ω hA)) (hc ω hA) (hdom ω hA)
    (heq ω hA)
  refine curSide_of_seedLand (hxL ω) (hxR ω) (hc ω hA) hγ hlive hq0 hE hEc (hdom ω hA) (hcfg ω hA).trace
    (hcfg ω hA).continuous_W (hcfg ω hA).W_zero
    (T := fun q' => leftStopInf R L r η ψ q' ω)
    (fun q' => leftStopInf_nonneg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA) q')
    (fun q' hq' => ?_) (fun t₀ ht₀ => exists_lt_leftStopInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA)
      (hψ ω hA) hq0 hlive ht₀) hN1 u hu
  have hq'live : (q' : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) :=
    lt_of_le_of_lt (by exact_mod_cast hq') hlive
  rw [current_dom_eqInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA) (hdom ω hA)
      (heq ω hA) hq'live, ← (hcfg ω hA).trace.2.2 _
      (leftStopInf_nonneg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA) q')]

/-- **`R5Lift.R7LiftCurGeomInf` from the seed-interval landings** (pocket opening at the flow seed). -/
theorem r7LiftCurGeomInf_of_seedLand {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0) (h : R7SeedLandInf P A R L r η ψ xL xR c q) :
    R7LiftCurGeomInf P A R L r η ψ xL xR c W' q := by
  filter_upwards [h, ae_curSideInf_of_seedLand (W' := W') hcfg hψ hc hdom heq hxL hxR h] with ω hω hs hA hlive u hu
  exact ⟨hω hA hlive u hu, fun _ => hs hA hlive u hu⟩

/-- **`R5Lift.R7OuterLiftGeomInf` from the seed-interval landings and the outer collars' `K_s`-landing** (pocket
opening at the flow seed). -/
theorem r7OuterLiftGeomInf_of_seedLand {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {X : Ω → Set ℂ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0) (h : R7SeedLandInf P A R L r η ψ xL xR c q)
    (ho : R7OuterReflInf P A R L r η ψ xL xR c W' ζ' X q) :
    R7OuterLiftGeomInf P A R L r η ψ xL xR c W' ζ' X q := by
  filter_upwards [ho, ae_curSideInf_of_seedLand (W' := W') hcfg hψ hc hdom heq hxL hxR h] with ω hω hs hA hlive ξ hξ
    hX hsel
  exact ⟨fun y hy => hs hA hlive ξ (not_not.1 hsel.1) y hy, hω hA hlive ξ hξ hX hsel⟩

end SeedOpen

end InteractingSLE.Sec7.R5Fresh
