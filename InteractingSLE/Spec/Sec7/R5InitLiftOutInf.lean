/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5InitLiftOut

/-!
# R.5's common phase on outer pockets opening at the flow seed (ruling R88)

Packet PROVE-R5-INIT (outer round). The `Inf` twins of `R5InitLiftOut`: on outer pockets opening at the flow seed
(`HOuter.IsOuterCfgInf`), with the incident-component current domains (inclusion
`R5Out.current_dom_subset_ambientInf`, frontier in `K_{T⁰(q)}` from `R5Out.frontier_relDomainInf_subset_trace`):

* `leftStopInf_nonneg_outer`, **`exists_lt_leftStopInf_outer`**, `frontier_cur_dom_subset_outerInf`,
  `refChartInf_frontier_subset_outer`;
* **`ae_curSideInf_of_seedLand_outer`**, **`r7LiftCurGeomInf_of_seedLand_outer`** (side agreement from the seed-interval
  landings);
* **`ae_exists_isCurPhaseIntInf_outer`**, **`r7AmbientLiftWordInf_of_cur_outer`** (`R5Ref.R7AmbientLiftWordInf` at
  the current phase integer);
* **`r7SeedLandInf_of_noReturn_outer`** (the seed-interval landings from the counterflow's no-return).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Init

open LocalSets PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide PhaseSel
  PocketWordAssembly PocketSeedOpen PocketCoord PocketJordan R5Phase R5Same R5Ref Sec6 PocketStopWallsFin R5Lift
  R5Fresh R5Out PocketStopMarked MartChar.RealFlow
open Wire.Current.SideTest (rationalOriginalTime)

variable {Ω : Type*}

section FactsInf

variable {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {ω : Ω}

/-- The left stop of an outer pocket opening at the flow seed is nonnegative. -/
theorem leftStopInf_nonneg_outer (hcfg : HOuter.IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (q : ℝ≥0) :
    0 ≤ leftStopInf R L r η ψ q ω :=
  hcfg.erase.nonneg.trans (HOuter.pocketFibreLeftInf_props hcfg.erase
    (clockOf_mem_Ico hcfg.erase.clockEnd_pos (capInv_nonneg _ _))).1

/-- **The left stops of smaller capacities approach `T⁰(q)` from below** (outer pocket opening at the flow seed). -/
theorem exists_lt_leftStopInf_outer (hcfg : HOuter.IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) {q : ℝ≥0} (hq0 : 0 < q)
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) {t₀ : ℝ} (ht₀ : t₀ < leftStopInf R L r η ψ q ω) :
    ∃ q' : ℝ≥0, q' < q ∧ t₀ < leftStopInf R L r η ψ q' ω ∧
      leftStopInf R L r η ψ q' ω ≤ leftStopInf R L r η ψ q ω := by
  have hP := hcfg.toPocketInf hψ
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (travInf (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω)) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hq
  have hTτ := PocketStopMarked.Outer.le_ambTime0Inf' hP (ψ ω) q
  have hτT := R5Out.lt_ambTime0Inf hP (NNReal.coe_pos.2 hq0) hq'
  set t₁ := max (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) t₀ with ht₁
  have ht₁T : t₁ < leftStopInf R L r η ψ q ω := max_lt hτT ht₀
  have ht₁m : firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0) ≤ t₁ := le_max_left _ _
  have hrc := R5Out.relCapInf_lt_of_lt_ambTime0Inf hP q.coe_nonneg hq' ht₁m ht₁T
  have hrc0 : 0 ≤ relCapInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) t₁ :=
    hP.driven.capClock_nonneg (PocketStopMarked.Outer.relTimeInf_nonneg hP ht₁m)
  set ρ := relCapInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) t₁ with hρ
  set q' : ℝ≥0 := ⟨(ρ + q) / 2, by positivity⟩ with hq'def
  have hq'c : (q' : ℝ) = (ρ + q) / 2 := rfl
  have hq'q : (q' : ℝ) < q := by rw [hq'c]; linarith
  have hq'live : ENNReal.ofReal (q' : ℝ) < capLife (travInf (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω)) :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hq'q.le) hq'
  have hqrel := (PocketStopMarked.Outer.ambTime0Inf_le_iff hP q.coe_nonneg hq' hTτ).1 le_rfl
  refine ⟨q', by exact_mod_cast hq'q, ?_, (PocketStopMarked.Outer.ambTime0Inf_le_iff hP q'.coe_nonneg hq'live hTτ).2
    (hq'q.le.trans hqrel)⟩
  by_contra hle
  push Not at hle
  have h := (PocketStopMarked.Outer.ambTime0Inf_le_iff hP q'.coe_nonneg hq'live ht₁m).1
    (hle.trans (le_max_right _ _))
  rw [hq'c] at h
  linarith

/-- **The frontier of the current domain inside an outer pocket opening at the seed lies in `K_{T⁰(q)}`**. -/
theorem frontier_cur_dom_subset_outerInf {A : Set Ω} {c : Ω → Chart} (hω : ω ∈ A)
    (hcfg : HOuter.IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hc : (c ω).IsConformal) (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) :
    frontier ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) ∩ cfPocket (R ω) (L ω) r ⊆
      fwdHull (W ω) (leftStopInf R L r η ψ q ω) := by
  have hP := hcfg.toPocketInf hψ
  rw [current_dom_eq_relHull (C := fun ω => cfPocket (R ω) (L ω) r) (ψ := ψ) hω hq (hcfg.props hψ).1 hc hdom heq
    hP.subset_H hψ.2.2.2.1]
  intro y hy
  have h1 := frontier_relDomainInf_subset_trace hP hq hy
  rw [hcfg.trace.2.2 _ (leftStopInf_nonneg_outer (ψ := ψ) hcfg q)]
  exact ⟨hP.subset_H hy.2, Or.inl (subset_closure h1)⟩

/-- **The frontier of an interior-visit reference chart inside an outer pocket opening at the seed lies in `K_s`**. -/
theorem refChartInf_frontier_subset_outer {A : Set Ω} {c : Ω → Chart} {i : ℕ} (hω : ω ∈ A)
    (hcfg : HOuter.IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hc : (c ω).IsConformal) (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hp : ((visitCapInf R L r η ψ ω (rationalOriginalTime i)).toNNReal : ℝ≥0∞) <
      capLife (travAllInf R L r η ψ ω))
    (hv : η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r) :
    frontier ((refChartInf c R L r η ψ i ω).dom : Set ℂ) ∩ cfPocket (R ω) (L ω) r ⊆
      fwdHull (W ω) (rationalOriginalTime i) := by
  have hP := hcfg.toPocketInf hψ
  have hs := (rationalOriginalTime i).coe_nonneg
  have hvis : ((rationalOriginalTime i : ℝ≥0) : ℝ) ∈ visitSetInf (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) :=
    ⟨hcfg.erase.mem_Ioi _ hs hv, hv⟩
  have h1 := frontier_cur_dom_subset_outerInf hω hcfg hψ hc hdom heq hp
  have hnn : 0 ≤ visitCapInf R L r η ψ ω (rationalOriginalTime i) :=
    hP.driven.capClock_nonneg (PocketStopMarked.Outer.relTimeInf_nonneg hP hvis.1.le)
  have hT : leftStopInf R L r η ψ (visitCapInf R L r η ψ ω (rationalOriginalTime i)).toNNReal ω =
      rationalOriginalTime i := by
    show ambTime0Inf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω)
      ((visitCapInf R L r η ψ ω (rationalOriginalTime i)).toNNReal : ℝ) = rationalOriginalTime i
    rw [Real.coe_toNNReal _ hnn]
    exact R5Out.ambTime0Inf_relCapInf_of_visit hP hvis
  rw [hT] at h1
  exact h1

end FactsInf

section SeedOpen

variable [MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}

/-- **The side agreement at the left stop from the seed-interval landings** (pocket opening at the flow seed). -/
theorem ae_curSideInf_of_seedLand_outer {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
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
  have hγ := ((hcfg ω hA).props (hψ ω hA)).1
  have hq0 : 0 < q := by
    rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h0q | h0q
    · exfalso
      subst h0q
      rw [seed_interval_eq_empty_zero (c := c) (hxL ω) (hxR ω) hγ hlive] at hu
      exact hu
    · exact h0q
  obtain ⟨E, hE, hEc, -⟩ := exists_inverse_extension_of_jordan_cases (Or.inr (hψ ω hA)) (hc ω hA) (hdom ω hA)
    (heq ω hA)
  refine curSide_of_seedLand_of_frontier (hxL ω) (hxR ω) (hc ω hA) hγ hlive hq0 hE hEc (hdom ω hA) (hcfg ω hA).trace
    (hcfg ω hA).continuous_W (hcfg ω hA).W_zero
    (T := fun q' => leftStopInf R L r η ψ q' ω)
    (fun q' => leftStopInf_nonneg_outer (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) q')
    (fun q' hq' => ?_)
    (frontier_cur_dom_subset_outerInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA)
      (hdom ω hA) (heq ω hA) hlive)
    (fun t₀ ht₀ => exists_lt_leftStopInf_outer (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA)
      (hψ ω hA) hq0 hlive ht₀) hN1 u hu
  have hq'live : (q' : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) :=
    lt_of_le_of_lt (by exact_mod_cast hq') hlive
  exact current_dom_subset_ambientInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA)
    (hdom ω hA) (heq ω hA) hq'live

/-- **`R5Lift.R7LiftCurGeomInf` from the seed-interval landings** (pocket opening at the flow seed). -/
theorem r7LiftCurGeomInf_of_seedLand_outer {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0) (h : R7SeedLandInf P A R L r η ψ xL xR c q) :
    R7LiftCurGeomInf P A R L r η ψ xL xR c W' q := by
  filter_upwards [h, ae_curSideInf_of_seedLand_outer (W' := W') hcfg hψ hc hdom heq hxL hxR h] with ω hω hs hA hlive u
    hu
  exact ⟨hω hA hlive u hu, fun _ => hs hA hlive u hu⟩


/-- **The current phase integer exists** (pocket opening at the flow seed): almost surely on the live test at a positive
capacity, every coordinate of the current open seed interval lands in the ambient hull `K_T` (from `R7LiftCurGeomInf`'s
first clause and `R5Lift.landing_mem_hull_of_mem_seed_interval`), so the current transition reflects along it. -/
theorem ae_exists_isCurPhaseIntInf_outer {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0} {ℓ : Ω → ℂ → ℂ}
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hℓ : ∀ ω ∈ A, IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧ ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im)
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0)
    (h : R7LiftCurGeomInf P A R L r η ψ xL xR c W' q) :
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) → 0 < q →
      ∃ n, IsCurPhaseIntInf R L r η ψ xL xR c W' q ω n := by
  have hcursub : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
      ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) ⊆ cfPocket (R ω) (L ω) r ∩
        (H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (leftStopInf R L r η ψ q ω)) := fun ω hA hlive =>
    current_dom_subset_ambientInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA)
      (hdom ω hA) (heq ω hA) hlive
  have hcurfr : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
      frontier ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) ∩ cfPocket (R ω) (L ω) r ⊆
        fwdHull (fun t : ℝ => W' t.toNNReal ω) (leftStopInf R L r η ψ q ω) := fun ω hA hlive =>
    frontier_cur_dom_subset_outerInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA)
      (hdom ω hA) (heq ω hA) hlive
  filter_upwards [h] with ω hω hA hlive hq0
  have hγ := ((hcfg ω hA).props (hψ ω hA)).1
  have hT := leftStopInf_nonneg_outer (ψ := ψ) (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) q
  obtain ⟨E, hE, hEc, -⟩ := exists_inverse_extension_of_jordan_cases
    (Or.inr (hψ ω hA))
    (hc ω hA) (hdom ω hA) (heq ω hA)
  obtain ⟨Fc, hFc, hFcc, -⟩ :=
    exists_relative_inverse_extension (c := c) (γ := travAllInf R L r η ψ) hγ hlive hE hEc
  obtain ⟨Lc, hLc, hlc⟩ :=
    Aux29Cor.exists_isDerivLog_relChart (c := c) hγ hlive (hc ω hA) (hℓ ω hA).1 (hℓ ω hA).2
  have hcur := isConformal_relChart_of_driven (c := c) hγ hlive (hc ω hA)
  refine exists_int_forall_tendsto_cur hcur hLc hlc hFc hFcc (hcfg ω hA).trace (hcfg ω hA).continuous_W
    (hcfg ω hA).W_zero hT ((hcursub ω hA hlive).trans inter_subset_right) fun u hu => ?_
  obtain ⟨hlim, hFu⟩ := tendsto_of_ext hFc hFcc u
  refine landing_mem_hull_of_mem_seed_interval_of_frontier (hxL ω) (hxR ω) (hc ω hA) hγ hlive hq0 hE hEc
    (hdom ω hA) (QuantumZipper.FwdHolo.isOpen_compl_fwdHull (hcfg ω hA).continuous_W hT) (hcurfr ω hA hlive) hu hlim
    ?_
  rw [hFu]; exact ((hω hA hlive) u hu).1

/-- **`R5Ref.R7AmbientLiftWordInf` at the current phase integer** (pocket opening at the flow seed; two-seed current
words with seeds at `0`; ambient force processes of an integrated path with ordered marks and infinite lifetime): an
integer field `N` such that the lift-difference limit is `2π N ω` and the word identity holds at the phase `χ·2π N ω +
a`. -/
theorem r7AmbientLiftWordInf_of_cur_outer {κ : ℝ} {ρL : Fin (0 + 1) → ℝ} {ρR : Fin (0 + 1) → ℝ} {mL mR : ℕ}
    {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ} {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ}
    {xR : Ω → Fin (0 + 1) → ℝ} {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {X : Ω → Set ℂ} {q : ℝ≥0}
    {ℓ : Ω → ℂ → ℂ} {α : ℝ} {xL₀ ρL₀ : Fin mL → ℝ} {xR₀ ρR₀ : Fin mR → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hℓ : ∀ ω ∈ A, IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧ ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im)
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0)
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath α xL₀ xR₀ ρL₀ ρR₀ (fun t => W' t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ' ω))
    (hζ : ∀ ω ∈ A, ζ' ω = ⊤) (hxL₀ : ∀ i, xL₀ i ≤ 0) (hxR₀ : ∀ j, 0 ≤ xR₀ j)
    (h : R7LiftCurGeomInf P A R L r η ψ xL xR c W' q) (a : ℝ) :
    R7AmbientLiftWordInf κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR
      (fun ω => chiC κ * (2 * Real.pi * curPhaseIntInf R L r η ψ xL xR c W' q ω) + a) X q := by
  have hcursub : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
      ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) ⊆ cfPocket (R ω) (L ω) r ∩
        (H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (leftStopInf R L r η ψ q ω)) := fun ω hA hlive =>
    current_dom_subset_ambientInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA)
      (hdom ω hA) (heq ω hA) hlive
  have hcurfr : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
      frontier ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) ∩ cfPocket (R ω) (L ω) r ⊆
        fwdHull (fun t : ℝ => W' t.toNNReal ω) (leftStopInf R L r η ψ q ω) := fun ω hA hlive =>
    frontier_cur_dom_subset_outerInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA)
      (hdom ω hA) (heq ω hA) hlive
  have hex := ae_exists_isCurPhaseIntInf_outer hcfg hψ hc hdom heq hℓ hxL hxR h
  have hspec := R5Out.refEventInf_spec hcfg hψ hc hdom heq (refHull W' ζ') q
  filter_upwards [h, hex, hpath] with ω hω hexω hpω hA hlive ξ hξ hX hC i x ε x' s hM hv hcol hland hx' hfx hfo
  have hγ := ((hcfg ω hA).props (hψ ω hA)).1
  have hcur := isConformal_relChart_of_driven (c := c) hγ hlive (hc ω hA)
  have hcurland := (R5Out.current_landingInf (W := fun ω (s : ℝ) => W' s.toNNReal ω)
    (hcfg ω hA) (hψ ω hA) (hc ω hA) (hdom ω hA)
    (heq ω hA) hlive ξ).1
  -- `q > 0`: at `q = 0` no real coordinate lands in the pocket
  have hq0 : 0 < q := by
    rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h0 | h0
    · exfalso
      subst h0
      have hn := landing_notMem_dom hcur hcurland
      rw [relChart_zero_dom (c := c) hγ, hdom ω hA] at hn
      exact hn hC
    · exact h0
  have hNspec := curPhaseIntInf_spec (hexω hA hlive hq0)
  -- the charts and their inverse extensions
  have hT := leftStopInf_nonneg_outer (ψ := ψ) (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) q
  have hCo : IsOpen (cfPocket (R ω) (L ω) r) := by rw [← hdom ω hA]; exact (c ω).dom.isOpen
  have hCH : cfPocket (R ω) (L ω) r ⊆ H := by rw [← hdom ω hA]; exact (hc ω hA).dom_subset
  obtain ⟨E, hE, hEc, -⟩ := exists_inverse_extension_of_jordan_cases
    (Or.inr (hψ ω hA))
    (hc ω hA) (hdom ω hA) (heq ω hA)
  obtain ⟨Fc, hFc, hFcc, -⟩ :=
    exists_relative_inverse_extension (c := c) (γ := travAllInf R L r η ψ) hγ hlive hE hEc
  have hp : ((visitCapInf R L r η ψ ω (rationalOriginalTime i)).toNNReal : ℝ≥0∞) <
      capLife (travAllInf R L r η ψ ω) := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hM.2.2.2.1) hlive
  obtain ⟨Fo, hFo, hFoc, -⟩ := exists_relative_inverse_extension (c := c) (γ := travAllInf R L r η ψ)
    (q := (visitCapInf R L r η ψ ω (rationalOriginalTime i)).toNNReal) hγ hp hE hEc
  have holdsub : ((refChartInf c R L r η ψ i ω).dom : Set ℂ) ⊆
      cfPocket (R ω) (L ω) r ∩ (H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (s : ℝ)) := by
    have h1 := (hspec i ω hM).2.2.2.2
    rwa [R5Phase.H_diff_liveExt_zero hA hγ, hM.2.2.2.2] at h1
  have holdfr : frontier ((refChartInf c R L r η ψ i ω).dom : Set ℂ) ∩ cfPocket (R ω) (L ω) r ⊆
      fwdHull (fun t : ℝ => W' t.toNNReal ω) (s : ℝ) :=
    refChartInf_frontier_subset_outer (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA)
      (hdom ω hA) (heq ω hA) hp hv
  have hξC : Fc ξ ∈ cfPocket (R ω) (L ω) r := by rw [(tendsto_of_ext hFc hFcc ξ).2]; exact hC
  have hxC : Fo x ∈ cfPocket (R ω) (L ω) r := by
    have h1 := (tendsto_of_ext hFo hFoc x).1
    have h2 : Tendsto (refChartInf c R L r η ψ i ω).2.1 (𝓝[H] (x : ℂ))
        (𝓝 (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ)) :=
      hcol.2.2.2.1.mono_right nhdsWithin_le_nhds
    have := nhdsWithin_H_neBot x
    rw [tendsto_nhds_unique h1 h2]; exact hC
  have hx'0 : x' ≠ 0 := fun h0 => hx' (h0 ▸ Set.mem_insert 0 _)
  -- the current positions
  have hξI := mem_seed_interval_of_landing (iL := 0) (iR := 0) (hxL ω) (hxR ω) (hc ω hA) hγ hlive hcurland
    (show _ ∈ ((c ω).dom : Set ℂ) by rw [hdom ω hA]; exact hC)
  -- the comparison with the current ambient time
  obtain ⟨hlim, hside⟩ := ref_lift_side_of_cur_land hcur (hspec i ω hM).2.2.1 hFc hFcc hFo hFoc
    (hcfg ω hA).trace (hcfg ω hA).continuous_W (hcfg ω hA).W_zero s.coe_nonneg hT
    ((hcursub ω hA hlive).trans inter_subset_right) (holdsub.trans inter_subset_right) (hspec i ω hM).2.2.2.1
    hcol.1 hcol.2.1 (exists_ball_landing_mem_hull_of_frontier hcur hFc hFcc hCo (hcurfr ω hA hlive) hξC)
    (exists_ball_landing_mem_hull_of_frontier (hspec i ω hM).2.2.1 hFo hFoc hCo holdfr hxC) hx'0 hfx hfo
    (A := (relChart c (travAllInf R L r η ψ) q ω).2.2) (hNspec ξ hξI) ((hω hA hlive ξ hξI).2 hC)
  -- the ambient positions
  have hcurK : ∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c (travAllInf R L r η ψ) q ω).2.1 y ∈
      H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (s : ℝ) := by
    refine eventually_nhdsWithin_of_forall fun y hy => ?_
    exact (holdsub ((hspec i ω hM).2.2.2.1 (hcur.inv_mem_dom hy))).2
  have hamb := mem_ambient_seed_interval (hcfg ω hA).trace (hcfg ω hA).continuous_W (hcfg ω hA).W_zero
    (s.coe_nonneg) (hCH hC) hcurland hcurK hfx
  have hV : Continuous fun t : ℝ≥0 => W' t ω := by
    have h1 := (hcfg ω hA).continuous_W.comp NNReal.continuous_coe
    simpa only [Function.comp_def, Real.toNNReal_coe] using h1
  obtain ⟨hL, hR⟩ := Sec5.CfStep.force_eq_geom_of_path_top hpω (hζ ω hA) hV fun _ => rfl
  have hWs : W' (s : ℝ).toNNReal ω = W' s ω := by rw [Real.toNNReal_coe]
  obtain ⟨hVLpos, hVRpos⟩ := ambient_force_positions (VL := fun j => VL j s ω) (VR := fun j => VR j s ω)
    (xL := xL₀) (xR := xR₀) (hcfg ω hA).continuous_W s.coe_nonneg hxL₀ hxR₀ (fun j => hL j s)
    (fun j => hR j s) hamb
  rw [hWs] at hVLpos hVRpos
  refine ⟨2 * Real.pi * curPhaseIntInf R L r η ψ xL xR c W' q ω, hlim, ?_⟩
  have hvL' : ∀ i' : Fin (0 + 1), (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL i q ω -
      segDriver (travAllInf R L r η ψ ω) q) i' ≤ (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL i
      q ω - segDriver (travAllInf R L r η ψ ω) q) 0 := fun i' => by rw [Fin.fin_one_eq_zero i']
  have hvR' : ∀ j' : Fin (0 + 1), (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR j q ω -
      segDriver (travAllInf R L r η ψ ω) q) 0 ≤ (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR j
      q ω - segDriver (travAllInf R L r η ψ ω) q) j' := fun j' => by rw [Fin.fin_one_eq_zero j']
  exact word_identity_exposed ρL ρR ρL' ρR' hvL' hvR' hξI (fun _ => hVLpos) (fun _ => hVRpos) hside
    (curPhaseIntInf R L r η ψ xL xR c W' q ω) a



omit [MeasurableSpace Ω] in
/-- **The relative capacity trace does not return to the corner** (pocket opening at the flow seed). -/
theorem capTrace_ne_zero_of_noReturnInf_outer {W : Ω → ℝ → ℝ} {ω : Ω}
    (hcfg : HOuter.IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hy₀ : cfArcRInf (R ω) (L ω) r 0 = 0) (hnr : ∀ t : ℝ, 0 < t → η ω t ≠ 0) {s : ℝ} (hs : 0 < s)
    (hsl : ENNReal.ofReal s < capLife (travAllInf R L r η ψ ω)) :
    capTrace (travAllInf R L r η ψ ω) s.toNNReal ≠ 0 := by
  have hP := hcfg.toPocketInf hψ
  have hψ' := hP.jordan
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := (hcfg.props hψ).1
  have hspec : 0 ≤ capInv (travAllInf R L r η ψ ω) s ∧
      capClock (travAllInf R L r η ψ ω) (capInv (travAllInf R L r η ψ ω) s) = s := hγ.capInv_spec hs.le hsl
  set u := capInv (travAllInf R L r η ψ ω) s with hudef
  have hc0 : capClock (travAllInf R L r η ψ ω) 0 = 0 := hγ.capClock_zero
  have hupos : 0 < u := by
    refine lt_of_le_of_ne hspec.1 fun h => ?_
    have h2 := hspec.2
    rw [← h, hc0] at h2
    linarith
  set L₀ := clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) with hL₀
  have hL : 0 < L₀ := hP.erase.clockEnd_pos
  set v := clockOf L₀ u with hvdef
  have hv : v ∈ Ico 0 L₀ := clockOf_mem_Ico hL hspec.1
  have hvpos : 0 < v := by
    simp only [hvdef, clockOf]
    have : 0 < u / (1 + u) := by positivity
    positivity
  have hm := hP.erase.erasedPath_mem hv
  have hpk := hcfg.conf.isCfPocketInf hcfg.seed
  have hy₀m : cfArcRInf (R ω) (L ω) r 0 ∈ closure (cfPocket (R ω) (L ω) r) := by
    refine frontier_subset_closure ?_
    rw [hpk.frontier_eq]
    exact Or.inl ⟨0, Set.mem_Ici.2 le_rfl, rfl⟩
  intro h0
  have hval : capTrace (travAllInf R L r η ψ ω) s.toNNReal = ψ ω (erasedPathInf (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) v) := by
    simp only [capTrace, Real.coe_toNNReal _ hs.le]
    rfl
  rw [hval] at h0
  have heqp := hψ'.2.1 hm hy₀m (h0.trans hψ'.2.2.2.2.2.1.symm)
  have hf := hP.erase.fibre_mem hv
  have hcf := hP.erase.clock_fibre hv
  have hτ := hP.erase.nonneg
  have hfpos : 0 < pocketFibreInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) v := by
    rcases (hτ.trans hf).lt_or_eq with h | h
    · exact h
    · exfalso
      have hfτ := le_antisymm (h ▸ hτ) hf
      rw [hfτ, R7StopIn.IsErasurePocketInf.clock_τ] at hcf
      linarith
  exact hnr _ hfpos (heqp.trans hy₀)

omit [MeasurableSpace Ω] in
/-- **The seed-interval landings at one sample from the counterflow's no-return** (pocket opening at the flow seed). -/
theorem seedLandInf_of_noReturn_sample_outer {W : Ω → ℝ → ℝ} {c : Ω → Chart} {ω : Ω} (hω : ω ∈ A)
    (hcfg : HOuter.IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hc : (c ω).IsConformal) (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} (hxL : xL ω 0 = 0) (hxR : xR ω 0 = 0) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) (hnr : ∀ t : ℝ, 0 < t → η ω t ≠ 0) :
    ∀ u ∈ Ioo (geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL 0 q ω -
          segDriver (travAllInf R L r η ψ ω) q)
        (geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR 0 q ω - segDriver (travAllInf R L r η ψ ω) q),
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 u ∈ H := by
  intro u hu
  have hγ := (hcfg.props hψ).1
  have hq0 : 0 < q := by
    rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h0q | h0q
    · exfalso
      subst h0q
      rw [seed_interval_eq_empty_zero (c := c) hxL hxR hγ hq] at hu
      exact hu
    · exact h0q
  obtain ⟨hland, hcl, -⟩ := R5Out.current_landingInf hcfg hψ hc hdom heq hq u
  have hP := hcfg.toPocketInf hψ
  have hψ' := hP.jordan
  have hpk := hcfg.conf.isCfPocketInf hcfg.seed
  rcases closure_cfPocketInf_subset_H_union_seed hpk hcl with h | h
  · exact h
  rw [mem_singleton_iff] at h
  rcases cfArcRInf_zero_mem_H_or_eq_zero hcfg.conf hcfg.seed with h1 | h1
  · rw [h]
    exact h1
  exfalso
  have hy₀m : cfArcRInf (R ω) (L ω) r 0 ∈ closure (cfPocket (R ω) (L ω) r) := by
    refine frontier_subset_closure ?_
    rw [hpk.frontier_eq]
    exact Or.inl ⟨0, Set.mem_Ici.2 le_rfl, rfl⟩
  have hcur := isConformal_relChart_of_driven (c := c) hγ hq hc
  have hd := current_dom_subset_ambientInf hω hcfg hψ hc hdom heq hq
  refine not_tendsto_corner (c := c) hxL hxR hγ hq hq0 (ψ := ψ ω) (fun w hw => ?_)
    (S := closure (cfPocket (R ω) (L ω) r)) (fun z hz => ?_) (hψ'.1 _ hy₀m) hψ'.2.2.2.2.2.1
    (fun s hs hsq => capTrace_ne_zero_of_noReturnInf_outer hcfg hψ h1 hnr hs
      (lt_of_le_of_lt (by rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hsq) hq)) hu
    (h ▸ hland)
  · have hmem : (c ω).2.1 w ∈ cfPocket (R ω) (L ω) r := by rw [← hdom]; exact hc.inv_mem_dom hw
    rw [← heq hmem]
    exact hc.2.2 w hw
  · have hz' := hd (hcur.inv_mem_dom hz)
    exact subset_closure hz'.1

/-- **`R7SeedLandInf` from the counterflow's no-return** (pocket opening at the flow seed). -/
theorem r7SeedLandInf_of_noReturn_outer {nL nR : ℕ} {P : Measure Ω} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (hxL : ∀ ω, xL ω 0 = 0)
    (hxR : ∀ ω, xR ω 0 = 0) (hnr : ∀ᵐ ω ∂P, ω ∈ A → ∀ t : ℝ, 0 < t → η ω t ≠ 0) :
    R7SeedLandInf P A R L r η ψ xL xR c q := by
  filter_upwards [hnr] with ω hω hA hlive
  exact seedLandInf_of_noReturn_sample_outer (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA)
    (hdom ω hA) (heq ω hA) (hxL ω) (hxR ω) hlive (hω hA)


end SeedOpen

end InteractingSLE.Sec7.R5Init
