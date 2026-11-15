/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseClauseStop

/-!
# GW4's protected martingales, part 1: the phase-word law (S) from deterministic physical lines

Packet PROVE-GW4-MART (Theorem 1.4's `GW4Fix.GW4ComponentPhaseInputsStatement`, the protected-martingale half;
Astra's follow-up 3, Q3 §§3.4–3.7, `source/external/AstraIG1/ig1_followup3_audited.txt` L897–L1000: the optional
Gaussian kernels of the phase-shifted word (Q3.6)–(Q3.7) in the time-changed filtration, then the continuous local
martingales (Q3.9)).

`Restart.DomainMarkov.Aux79.hasSafeLaw_of_lineLaw` transfers conditional laws on deterministic physical lines to K2's
input (S) at deterministic capacity times, for the canonical force word. Here the same discretization is run for
the **phase word** with a random phase `c` constant in time (`PhaseClause.HasPhaseSafeLaw`, positive times only), and
with a capacity-time filtration whose events are only asked to be cut into line events **on the line safe events**
(the line σ-algebras `𝒢L t` need not increase in `t`). The phase continuity is
`PhaseClause.exists_eventually_isSafeAt_tendsto_cfAt_phase`.

## Main results

* **`hasPhaseSafeLaw_of_lineLaw`**: `HasPhaseSafeLaw` for `𝓗'` from the phase line laws at positive clock values.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW4Fix.Mart

open Coupling Restart.DomainMarkov Restart.DomainMarkov.Aux79 Sec7.PhaseSel Sec7.PhaseClause

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ} {κ : ℝ}
  {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {Qc : ℝ≥0 → Ω → ℝ≥0}

/-- **The phase-word law (S) from conditional laws on deterministic physical lines.** Let `Qc` be a continuous
nondecreasing clock from `0`, adapted to a physical filtration `𝓖`, and `𝒢L t ⊇ 𝓖 t` line σ-algebras (not
necessarily increasing). Suppose that for every positive `q`, every `𝓗' q`-event cut by `{q ≤ Qc t}` and the line
safe event of `ψ` is a `𝒢L t`-event, that the clock reaches every capacity time before `ζ`, that the continuation is
regular, and that at every physical time `t` with positive clock value the field has, given `𝒢L t`, the
protected-kernel law of the phase-`c` word at the capacity time `Qc t` on the line safe event. Then the field has
the phase-word law (S) for `𝓗'` at every positive capacity time. -/
theorem hasPhaseSafeLaw_of_lineLaw [IsProbabilityMeasure P] (hκ : 0 < κ) {𝓖 𝓗' : Filtration ℝ≥0 mΩ}
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable fun ω => X ω ψ)
    (hc : ∀ ω, Continuous fun t => Qc t ω) (hm : ∀ ω, Monotone fun t => Qc t ω) (h0 : ∀ ω, Qc 0 ω = 0)
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t)) (𝒢L : ℝ≥0 → MeasurableSpace Ω) (h𝒢L : ∀ t, 𝓖 t ≤ 𝒢L t)
    (h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ)
    (h𝓗' : ∀ q : ℝ≥0, 0 < q → ∀ D, MeasurableSet[𝓗' q] D → ∀ (ψ : TestOn upperHalfPlaneOpens) t,
      MeasurableSet[𝒢L t] (D ∩ {ω | q ≤ Qc t ω} ∩ lineSafe Qc W ζ (tsupport ψ) t))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ ω → ∃ t, q ≤ Qc t ω)
    (hreg : ∀ᵐ ω ∂P, IsForceReg W VL VR ζ ω)
    (c : Ω → ℝ)
    (hline : ∀ (ψ : TestOn upperHalfPlaneOpens) (t : ℝ≥0), ∀ᵐ ω ∂P, 0 < Qc t ω →
      ω ∈ lineSafe Qc W ζ (tsupport ψ) t → P[fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ)) | 𝒢L t] ω =
        cfAt κ W (phaseProc κ ρL ρR W VL VR c) ψ 1 (Qc t) ω) :
    HasPhaseSafeLaw κ ρL ρR P 𝓗' ζ W VL VR c X := by
  intro ψ q hq D hD hDs
  set f : Ω → ℂ := fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ)) with hf
  have hfm : Measurable f :=
    (by fun_prop : Measurable fun x : ℝ => Complex.exp (Complex.I * x)).comp (hX ψ)
  have hfn : ∀ ω, ‖f ω‖ ≤ 1 := fun ω => by
    simp only [hf, Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, Real.exp_zero, le_refl]
  have hfi : Integrable f P := Integrable.of_bound hfm.aestronglyMeasurable 1 (Eventually.of_forall hfn)
  set u := phaseProc κ ρL ρR W VL VR c with hu
  set S : ℝ≥0 → Set Ω := lineSafe Qc W ζ (tsupport ψ) with hSdef
  set E : ℕ → ℕ → Set Ω := linePiece Qc q D S with hEdef
  set g : ℕ → ℕ → Ω → ℂ := fun n k => cfAt κ W u ψ 1 (Qc (dyT n k)) with hgdef
  have hDm : MeasurableSet D := 𝓗'.le q _ hD
  have hEm : ∀ n k, MeasurableSet[𝒢L (dyT n k)] (E n k) := by
    intro n k
    have hj : MeasurableSet[𝓖 (dyT n k)] {ω | ∀ j < k, Qc (dyT n j) ω < q} := by
      have e : {ω | ∀ j < k, Qc (dyT n j) ω < q} = ⋂ j : Fin k, {ω | Qc (dyT n j) ω < q} := by
        ext ω
        simp only [mem_ofPred_eq, mem_iInter]
        exact ⟨fun h j => h j j.2, fun h j hj => h ⟨j, hj⟩⟩
      rw [e]
      refine MeasurableSet.iInter fun j => ?_
      exact 𝓖.mono (dyT_mono n j.2.le) _ (measurableSet_lt (hQa _) measurable_const)
    have e : E n k = (D ∩ {ω | q ≤ Qc (dyT n k) ω} ∩ S (dyT n k)) ∩ {ω | ∀ j < k, Qc (dyT n j) ω < q} := by
      ext ω
      simp only [hEdef, linePiece, mem_inter_iff, mem_ofPred_eq]
      tauto
    rw [e]
    exact (h𝓗' q hq D hD ψ _).inter (h𝒢L _ _ hj)
  have hEm' : ∀ n k, MeasurableSet (E n k) := fun n k => h𝒢Lm _ _ (hEm n k)
  have hDF : ∀ᵐ ω ∂P, ω ∈ D → IsForceReg W VL VR ζ ω ∧ ω ∈ avoidSet W ζ ψ q := by
    filter_upwards [hDs, hreg] with ω h1 h2 hωD using ⟨h2, h1 hωD⟩
  -- the bound of the pieces' `cfAt`
  have hgb : ∀ᵐ ω ∂P, ∀ n k, ω ∈ E n k → ‖g n k ω‖ ≤ 1 := by
    filter_upwards [hDF] with ω hω n k hωE
    exact norm_cfAt_le_one_of_isForceReg u ψ (hω (linePiece_subset D S n k hωE)).1 hωE.2.1 hωE.2.2
  -- the line identity on each piece
  have hpiece : ∀ n k, AEStronglyMeasurable ((E n k).indicator (g n k)) P ∧
      ∫ ω, (E n k).indicator f ω ∂P = ∫ ω, (E n k).indicator (g n k) ω ∂P := by
    intro n k
    have hae : (E n k).indicator (g n k) =ᵐ[P] (E n k).indicator (P[f | 𝒢L (dyT n k)]) := by
      filter_upwards [hline ψ (dyT n k)] with ω hω
      by_cases hωE : ω ∈ E n k
      · rw [indicator_of_mem hωE, indicator_of_mem hωE]
        have hpos : 0 < Qc (dyT n k) ω := lt_of_lt_of_le hq hωE.1.2.1
        exact (hω hpos hωE.2).symm
      · rw [indicator_of_notMem hωE, indicator_of_notMem hωE]
    have hm' : AEStronglyMeasurable ((E n k).indicator (P[f | 𝒢L (dyT n k)])) P :=
      ((stronglyMeasurable_condExp.mono (h𝒢Lm _)).indicator (hEm' n k)).aestronglyMeasurable
    refine ⟨hm'.congr hae.symm, ?_⟩
    rw [integral_congr_ae hae, integral_indicator (hEm' n k), integral_indicator (hEm' n k),
      setIntegral_condExp (h𝒢Lm _) hfi (hEm n k)]
  have hgi : ∀ n k, Integrable ((E n k).indicator (g n k)) P := fun n k => by
    refine Integrable.of_bound (hpiece n k).1 1 ?_
    filter_upwards [hgb] with ω hω
    by_cases hωE : ω ∈ E n k
    · rw [indicator_of_mem hωE]; exact hω n k hωE
    · rw [indicator_of_notMem hωE, norm_zero]; exact zero_le_one
  -- the summed identity at every level
  have hsum : ∀ n, ∫ ω, ∑ k ∈ Finset.range (4 ^ n), (E n k).indicator f ω ∂P =
      ∫ ω, ∑ k ∈ Finset.range (4 ^ n), (E n k).indicator (g n k) ω ∂P := fun n => by
    rw [integral_finsetSum _ fun k _ => hfi.indicator (hEm' n k),
      integral_finsetSum _ fun k _ => hgi n k]
    exact Finset.sum_congr rfl fun k _ => (hpiece n k).2
  -- pointwise limits
  have hgood : ∀ᵐ ω ∂P, ω ∈ D → (∃ t, q ≤ Qc t ω) ∧
      (∀ t : ℕ → ℝ≥0, Tendsto (fun n => Qc (t n) ω) atTop (𝓝 q) → ∀ᶠ n in atTop, ω ∈ S (t n)) ∧
      IsForceReg W VL VR ζ ω ∧ ω ∈ avoidSet W ζ ψ q := by
    filter_upwards [hDF, hreach q] with ω hω hr hωD
    obtain ⟨hp, hav⟩ := hω hωD
    exact ⟨hr hav.1, fun t ht => eventually_mem_lineSafe ψ.hasCompactSupport.isCompact
      (Coupling.tsupport_subset_H ψ) hp hav.1 hav.2 t ht, hp, hav⟩
  have hlimf := ae_tendsto_sum_linePiece (P := P) (D := D) (S := S) hc hm h0 (fun _ _ => f) f (by
    filter_upwards [hgood] with ω hω hωD
    obtain ⟨hr, hS', -, -⟩ := hω hωD
    exact ⟨hr, hS', tendsto_const_nhds⟩)
  have hlimg := ae_tendsto_sum_linePiece (P := P) (D := D) (S := S) hc hm h0 g
    (cfAt κ W u ψ 1 fun _ => q) (by
    filter_upwards [hgood] with ω hω hωD
    obtain ⟨hr, hS', hp, hav⟩ := hω hωD
    have huω : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω → IsBoundedHarmonicExtension
        (phaseData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω) (c ω))
        (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s) := fun s hs =>
      isBoundedHarmonicExtension_phaseProc hκ c ((hp.2.2.2.2 s hs).1 0) ((hp.2.2.2.2 s hs).2 0)
    obtain ⟨-, -, hT⟩ := exists_eventually_isSafeAt_tendsto_cfAt_phase hκ ψ huω hp hav.1 hav.2
      (tendsto_Qc_dyT_hitT (hc ω) (hm ω) (h0 ω) hr)
    exact ⟨hr, hS', hT⟩)
  have hTf := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => (Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
      (hfm.aestronglyMeasurable.indicator (hEm' n k))))
    (integrable_const 1) (fun n => Eventually.of_forall fun ω =>
      norm_sum_linePiece_le hc hm (fun _ _ => f) n _ fun k _ => hfn ω) hlimf
  have hTg := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => Finset.aestronglyMeasurable_fun_sum _ fun k _ => (hpiece n k).1)
    (integrable_const 1) (fun n => by
      filter_upwards [hgb] with ω hω
      exact norm_sum_linePiece_le hc hm g n _ fun k hk => hω n k hk) hlimg
  rw [integral_indicator hDm] at hTf hTg
  exact tendsto_nhds_unique (hTf.congr fun n => hsum n) hTg

end InteractingSLE.Theorem14.GW4Fix.Mart
