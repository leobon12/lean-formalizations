/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermConclude
import InteractingSLE.Spec.RealContact.TermClock
import InteractingSLE.Spec.Supplement.AStopPartType

/-!
# The path statement from Theorem 1.3 and Lemma 7.5

Packet PROVE-RC-TERM, second run (ruling R124).

* **`ae_path_of_le`**: for one own time `N`, almost surely on the trigger event with `T ≤ N`, the conclusion of
  `TerminalRetainedPathStatement`. Proof: line data at `(t, N)` (`exists_isLineData`); the base event
  (`baseEv`, `measurableSet_baseEv`) contains the trigger event with `T ≤ N` almost surely
  (`ae_mem_baseEv_of_trigger`) and almost surely consists of good samples (`ae_isTermGood_of_baseEv`), so it has an
  everywhere good `retSigma76 … 0 N` sub-event `M` of full relative measure (`exists_subset_of_ae`); the chart word
  `stopWord κ (c, θ₂, r)` has a length and heights independent of the record `r`, so finitely many measurable type
  events cover (`RLC.AStopPart.exists_typeCover_shiftW`); on each part of positive probability the code match
  `ae_codeMatch_term` (observations `termObs`) and the clock clauses `IsTermGood.conclusion`; the record at own time
  `N` is the completed record (`recOf_coe_eq_top`).
* **`terminalRetainedPath_of_inputs`**: the path statement from Theorem 1.3 and Lemma 7.5 (countable union over `N`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.RealContact

namespace Term

open Restart Restart.RetAux79 Supp7 Sec7 Sec7.Lemma76F Exist.Staged Exist.StagedLaw Sec2.Assembly RLC.AStopProc

section Main

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {κ : ℝ}
  {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}

/-- **The path statement at one own time** (see the module docstring). -/
theorem ae_path_of_le (h13 : Exist.Theorem13Statement.{0}) (hL75 : Theorem15.Lemma75Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁)
    (hgap : κ / 2 - 2 ≤ Sec4.cumWeightRight κ ((-sleLambda κ - θ₁ * chiC κ) + θ₂ * chiC κ))
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hF : IsCanonicalFlowCode κ θ₁ F)
    {c : BoundaryWord} {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hcJ : c.jumps = jumps.image (· - x₂))
    (hcb : ∀ y ∉ jumps.image (· - x₂), c.fn y = b (y + x₂)) (hEm : Measurable E)
    (hreg : ∀ ω, IsRegularDriver (E ω)) (hE2 : ∀ ω, (E ω).2 = ζ₂ ω)
    (hfl : IsFlowLineDriver κ c.fn c.jumps θ₂ P (fun ω => Exist.flowField x₂ 0 (h ω)) (fun s ω => (E ω).1 s)
      (fun ω => (E ω).2))
    (htrace : ∀ᵐ ω ∂P, IsGeneratingTrace (E ω).1 (ζ₂ ω) (fun t => η₂ ω t - x₂))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {η₁' : Ω → ℝ≥0 → ℂ} (hm₁ : ∀ t, Measurable fun ω => η₁' ω t)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s) (N : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (e : ℝ), (T : ℝ≥0∞) = ζ₂ ω → η₂ ω T = e → e < x₂ →
      (∃ (s : ℝ≥0) (y : ℝ), (s : ℝ≥0∞) < ζ₁ ω ∧ η₁ ω s = y ∧ y ≤ e) → T ≤ N →
      ∃ (c₁ : ℝ≥0 → ℝ≥0) (σ : ℝ≥0∞),
        σ ≤ (F ((termWord κ θ₂ c (termRec (E ω)), termSeed x₁ x₂ (termRec (E ω))),
          termField κ x₂ (termRec (E ω)) (h ω))).2 ∧
        StrictMonoOn c₁ {s | (s : ℝ≥0∞) ≤ σ} ∧
        c₁ '' {s | (s : ℝ≥0∞) ≤ σ} =
          {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ₁ ω ∧ ∀ t' : ℝ≥0, 0 < t' → t' < t → η₁ ω t' ∉ η₂ ω '' Icc 0 T} ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ σ → η₁ ω (c₁ s) = termInv x₂ (termRec (E ω))
          (decPath (F ((termWord κ θ₂ c (termRec (E ω)), termSeed x₁ x₂ (termRec (E ω))),
            termField κ x₂ (termRec (E ω)) (h ω))) s) := by
  classical
  have hθ := lt_of_gap hκ hκ4 hgap
  have hζ₁ := measurable_lifetime_of_isFlowLine hη₁
  have hζ₂ := measurable_lifetime_of_isFlowLine hη₂
  choose ηc₁ ηc₂ d using fun t : ℝ≥0 => exists_isLineData hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ t N
  have hB : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N] (baseEv N (ηc₂ 0) ζ₁ ζ₂ x₁ x₂) :=
    measurableSet_baseEv hζ₁ hζ₂ (d 0).cont₂ (d 0).meas₂ (d 0).ae₂
  obtain ⟨M, -, hMm, hBM, hMg⟩ := exists_subset_of_ae hB
    (ae_isTermGood_of_baseEv hκ hκ4 hb hx hgap hh hη₁ hη₂ hreg hE2 hfl htrace ha₁ (d 0).cont₂ (d 0).ae₂)
  have hrecm : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N] (pRec N E) :=
    measurable_recOf_retSigma76 hκ hEm hreg hE2 hfl htrace hζ₂ (d 0).cont₂ (d 0).meas₂ (d 0).ae₂
  -- the finite type cover: the chart word has a length and heights independent of the record
  set r₀ : RecData := recOf 0 (fun _ => 0, 0) with hr₀
  set L₀ : ℕ := (stopWord κ (c, θ₂, r₀)).1 with hL₀
  set heights : Finset ℝ := (Finset.range (L₀ + 1)).image (stopWord κ (c, θ₂, r₀)).2.2 with hheights
  obtain ⟨n, a, Tc, hTm, hcover, htypes⟩ := RLC.AStopPart.exists_typeCover_shiftW
    (m := retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N) (P := P) (κ := κ) (θ := θ₁) (N := L₀) (heights := heights)
    (c := pWord κ θ₂ c N E) (measurable_pWord hrecm κ θ₂ c) (τ := pSeed N E x₁ x₂)
    (measurable_pSeed hrecm x₁ x₂) (G := fun _ => True)
    (Eventually.of_forall fun ω _ => ⟨pWord κ θ₂ c N E ω, ∅,
      ⟨le_rfl, fun j hj => Finset.mem_image_of_mem _ (Finset.mem_range.2 (Nat.lt_succ_of_le hj))⟩,
      fun _ _ => rfl⟩)
  -- the code match on every part
  have hpart : ∀ i, ∀ᵐ ω ∂P, ω ∈ M ∩ Tc i →
      aLife (pPath N E (ηc₂ 0) η₁' ζ₁ x₁ x₂) (pStop N E (ηc₂ 0) η₁' ζ₁ x₁ x₂) ω ≤
          (F ((pWord κ θ₂ c N E ω, pSeed N E x₁ x₂ ω), termField κ x₂ (pRec N E ω) (h ω))).2 ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ aLife (pPath N E (ηc₂ 0) η₁' ζ₁ x₁ x₂) (pStop N E (ηc₂ 0) η₁' ζ₁ x₁ x₂) ω →
          aPath (pPath N E (ηc₂ 0) η₁' ζ₁ x₁ x₂) (pStop N E (ηc₂ 0) η₁' ζ₁ x₁ x₂) ω t + (pSeed N E x₁ x₂ ω : ℂ) =
            decPath (F ((pWord κ θ₂ c N E ω, pSeed N E x₁ x₂ ω), termField κ x₂ (pRec N E ω) (h ω))) t := by
    intro i
    by_cases hz : P (M ∩ Tc i) = 0
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hz] with ω hω hωM
      exact (hω hωM).elim
    · have hMi : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N] (M ∩ Tc i) := hMm.inter (hTm i)
      have hMgi : ∀ ω ∈ M ∩ Tc i, IsTermGood N E (ηc₂ 0) η₁' ζ₁ x₁ x₂ ω := fun ω hω => hMg ω hω.1
      have ho := termObs hκ hEm hreg hE2 hfl htrace hζ₁ hζ₂ hm₁ ha₁ (d 0).cont₂ (d 0).meas₂ (d 0).ae₂ ηc₁
        (fun t ω => (d t).cont₁ ω) (fun t s => (d t).meas₁ s) (fun t => (d t).ae₁) hMi hMgi
      exact ae_codeMatch_term h13 hL75 hκ hκ4 hb hθ hh hη₁ hη₂ hu₀ hcJ hcb hEm hreg hE2 hfl htrace ha₁ (d 0).ae₂
        hMi hMgi (fun ω hω => lt_of_lt_of_le (hMgi ω hω).isAGood.pos (physStop_le _ _ _ _ _)) ho (a i)
        (fun ω hω => htypes i ω hω.2) hz hF
  filter_upwards [ae_mem_baseEv_of_trigger hκ hκ4 hb hx hgap hh hη₁ hη₂ (d 0).ae₂, hBM, hcover,
    ae_all_iff.2 hpart, ha₁, (d 0).ae₂] with ω hbase hBMω hcov hpω ha₁ω hag₂ω T e hT he he2 htrig hTN
  have hωM := hBMω (hbase T e hT he he2 htrig hTN)
  obtain ⟨i, hi⟩ := hcov trivial
  obtain ⟨hV, hγ⟩ := hpω i ⟨hωM, hi⟩
  have hrec : pRec N E ω = termRec (E ω) := recOf_coe_eq_top (hMg ω hωM).life
  obtain ⟨c₁, σ, h1, h2, h3, h4⟩ := (hMg ω hωM).conclusion (hE2 ω) hT ha₁ω hag₂ω hV hγ
  have h1' : σ ≤ (F ((termWord κ θ₂ c (pRec N E ω), termSeed x₁ x₂ (pRec N E ω)),
      termField κ x₂ (pRec N E ω) (h ω))).2 := h1
  have h4' : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ σ → η₁ ω (c₁ s) = termInv x₂ (pRec N E ω)
      (decPath (F ((termWord κ θ₂ c (pRec N E ω), termSeed x₁ x₂ (pRec N E ω)),
        termField κ x₂ (pRec N E ω) (h ω))) s) := h4
  rw [hrec] at h1' h4'
  exact ⟨c₁, σ, h1', h2, h3, h4'⟩

end Main

/-- **The path statement from Theorem 1.3 and Lemma 7.5** (conditional helper; see the module docstring). -/
theorem terminalRetainedPath_of_inputs (h13 : Exist.Theorem13Statement.{0})
    (hL75 : Theorem15.Lemma75Statement.{u}) : TerminalRetainedPathStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hgap Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ F hF c E _ hcJ hcb hEm hreg hE2
    hfl htrace
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  obtain ⟨η₁', hm₁, ha₁⟩ := exists_measurable_version_of_isFlowLine hη₁
  have key := fun n : ℕ => ae_path_of_le h13 hL75 hκ hκ4 hb hx hgap hh hη₁ hη₂ hF hcJ hcb hEm hreg hE2 hfl htrace
    hu₀ hm₁ ha₁ (n : ℝ≥0)
  filter_upwards [ae_all_iff.2 key] with ω hω T e hT he he2 htrig
  obtain ⟨n, hn⟩ := exists_nat_ge T
  exact hω n T e hT he he2 htrig hn

end Term

end InteractingSLE.RealContact
