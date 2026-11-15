/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.ProbCrossingSetup
import InteractingSLE.Spec.Sec5.ProbBesselEvent
import InteractingSLE.Spec.Sec5.Crossing
import InteractingSLE.Spec.Sec2.OneForceLaw
import InteractingSLE.Spec.Sec2.AddMarksGirsanov

/-!
# Lemma 5.10: the crossing estimate

Packet PROVE-SEC5-B (specification §5.2, Lemma 5.10 and its proof, `source/spec/p097-144.md` L922–L959, with
the correction printed on p. 141 and the controlling replacement "Corrected crossing lemma",
`source/spec/p433-480.md` §2.2, pp. 451–452).

**Lemma 5.10.** Let `(W, V^{i,q})` be an `SLE_κ(ρ_L; ρ_R)` process with `W_0 = 0` and `ρ_{1,R} > −2`, put
`τ = inf {t ≥ 0 : |W_t| ≥ 1}` and assume the process is defined through `ζ = τ ∧ 1`. If the sum `U` of the force
drifts other than the first right one satisfies `|U_t| ≤ C` for almost every `t ≤ ζ`, almost surely, then
`ℙ[τ ≥ 1] ≥ p₀ > 0`, where `p₀` depends only on `C`, `κ` and `ρ_{1,R}`; it may be chosen uniformly for `ρ_{1,R}`
in a compact subset of `(−2, ∞)` (`crossing_lower_bound`).

Proof, as in the specification with one change of measure:

1. Girsanov's theorem (`girsanov_cutDriftT`) removes `U` up to `1 ∧ (lifetime)` (clamped at `C/√κ`, inactive
   before `τ ∧ 1`) and, after a fixed time `s`, the first right force drift while the gap is at least `g/2`.
   The second moment of the density gives `ℙ(A) ≥ e^{−2M²} ℚ(A)²` (`le_measureReal_of_girsanov`).
2. Under `ℚ`, the changed Brownian motion `β` has the canonical Wiener law (`QuantumZipper.RS.map_toCPath_eq`);
   on the event `pastEvent ∩ incrEvent` of `β` (independent pieces, positive probability, fixed by
   `κ, C, J` only: `ProbBesselEvent`) the pathwise argument `crossing_path` gives `|W_t| ≤ 3/8` up to time `1`.

Notation: `τ ≥ 1` is the event `∀ t < 1, |W_t| < 1`; "`t ≤ τ ∧ 1`" is `t ≤ 1 ∧ ∀ u < t, |W_u| < 1`; "defined
through `ζ`" is "every `t ≤ τ ∧ 1` is before the lifetime".
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper.RS
open scoped NNReal ENNReal

noncomputable section

namespace InteractingSLE

namespace Sec5

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ}

/-- The measurable event `|W_q| ≤ 3/8` before the lifetime at the countably many times `ratTimesLE 1`. -/
def goodEvent (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Set Ω :=
  ⋂ q ∈ ratTimesLE 1, {ω | (q : ℝ≥0∞) < ζ ω ∧ W q ω ∈ Set.Icc (-(3 / 8)) (3 / 8)}

theorem measurableSet_goodEvent {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hW : AdaptedBefore 𝓕 ζ W) : MeasurableSet (goodEvent W ζ) :=
  MeasurableSet.biInter (countable_ratTimesLE 1) fun q _ =>
    𝓕.le q _ (hW q _ measurableSet_Icc)

/-- On a path continuous before its lifetime, `goodEvent` forces `|W_t| < 1` for all `t < 1`. -/
theorem forall_abs_lt_of_mem_goodEvent {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (hc : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω}) (hω : ω ∈ goodEvent W ζ) :
    ∀ t : ℝ≥0, t < 1 → |W t ω| < 1 := by
  simp only [goodEvent, Set.mem_iInter, Set.mem_ofPred_eq] at hω
  have h1 : ((1 : ℝ≥0) : ℝ≥0∞) < ζ ω := (hω 1 (Set.mem_insert _ _)).1
  have hγ : Continuous fun t : ℝ≥0 => W (min t 1) ω := by
    refine hc.comp_continuous (continuous_id.min continuous_const) fun t => ?_
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) h1
  have hall := (forall_le_iff_ratTimesLE (S := Set.Icc (-(3 / 8)) (3 / 8)) hγ isClosed_Icc 1).2
    fun q hq => by
      simp only [min_eq_left (le_of_mem_ratTimesLE hq)]
      exact (hω q hq).2
  intro t ht
  have := hall t ht.le
  simp only [min_eq_left ht.le, Set.mem_Icc] at this
  rw [abs_lt]
  constructor <;> linarith [this.1, this.2]

theorem markL_allMarks (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (r : ℝ≥0)
    (ω : Ω) : markL (fun j => allMarks VL VR j r ω) = fun i => VL i r ω :=
  funext fun i => by simp [markL, allMarks]

theorem markR_allMarks (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (r : ℝ≥0)
    (ω : Ω) : markR (fun j => allMarks VL VR j r ω) = fun i => VR i r ω :=
  funext fun i => by simp [markR, allMarks]

theorem crossF_allMarks (κ C : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin (nR + 1) → ℝ) (g : ℝ) (s t : ℝ≥0)
    (w : ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (r : ℝ≥0) (ω : Ω) :
    crossF κ C ρL ρR g s t w (fun j => allMarks VL VR j r ω)
      = crossIntegrand κ C (ρR 0) g s t w (VR 0 r ω)
          (otherDrift ρL ρR w (fun i => VL i r ω) (fun i => VR i r ω)) := by
  rw [crossF, markL_allMarks, markR_allMarks]

/-- Splitting the driving equation into the first right force and `U`. -/
theorem w_eq_split {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin (nR + 1) → ℝ} {w b : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ}
    {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) :
    IntervalIntegrable (fun r : ℝ => otherDrift ρL ρR (w r.toNNReal) (fun i => vL i r.toNNReal)
        (fun i => vR i r.toNNReal)) volume 0 t ∧
      w t = Real.sqrt a * b t + (∫ r in (0 : ℝ)..t, ρR 0 / (w r.toNNReal - vR 0 r.toNNReal))
        + ∫ r in (0 : ℝ)..t, otherDrift ρL ρR (w r.toNNReal) (fun i => vL i r.toNNReal)
          (fun i => vR i r.toNNReal) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgL, hgR, hweq, -⟩ := hp
  have hL : ∀ i, IntervalIntegrable (fun r : ℝ => ρL i / (w r.toNNReal - vL i r.toNNReal))
      volume 0 t := fun i => ((hgL t ht i).const_mul (ρL i)).congr fun r _ => by
    simp only [div_eq_mul_inv]
  have hR : ∀ i, IntervalIntegrable (fun r : ℝ => ρR i / (w r.toNNReal - vR i r.toNNReal))
      volume 0 t := fun i => ((hgR t ht i).const_mul (ρR i)).congr fun r _ => by
    simp only [div_eq_mul_inv]
  have hsL : IntervalIntegrable (fun r : ℝ => ∑ i, ρL i / (w r.toNNReal - vL i r.toNNReal))
      volume 0 t := by
    have := IntervalIntegrable.sum Finset.univ fun i _ => hL i
    rwa [Finset.sum_fn] at this
  have hsR : IntervalIntegrable (fun r : ℝ => ∑ i : Fin nR, ρR i.succ /
      (w r.toNNReal - vR i.succ r.toNNReal)) volume 0 t := by
    have := IntervalIntegrable.sum Finset.univ fun (i : Fin nR) _ => hR i.succ
    rwa [Finset.sum_fn] at this
  refine ⟨hsL.add hsR, ?_⟩
  have h1 := hweq t ht
  simp only [otherDrift]
  rw [intervalIntegral.integral_add hsL hsR, intervalIntegral.integral_finsetSum fun i _ => hL i,
    intervalIntegral.integral_finsetSum fun i _ => hR i.succ]
  rw [Fin.sum_univ_succ] at h1
  linarith

/-- **Lemma 5.10** (the crossing estimate, in the uniform form of its proof and of the corrected crossing lemma,
specification §2.2). Fix `κ > 0`, `C`, and a compact `J ⊂ (−2, ∞)`. There is `p₀ > 0` such that for every
integrated `SLE_κ(ρ_L; ρ_R)` evolution `(W, V^L, V^R)` (with at least one right force point; `V^R_0` is the first
one) on any probability space, whose first right weight `ρ_{1,R}` lies in `J`, which is defined through
`ζ = τ ∧ 1` (`τ = inf {t : |W_t| ≥ 1}`), and whose remaining drift `U = otherDrift` satisfies `|U_t| ≤ C` for
almost every `t ≤ τ ∧ 1`, almost surely: `ℙ[τ ≥ 1] ≥ p₀`. -/
theorem crossing_lower_bound {κ C : ℝ} (hκ : 0 < κ) {J : Set ℝ} (hJ : IsCompact J)
    (hJ2 : J ⊆ Set.Ioi (-2)) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin (nR + 1) → ℝ)
      (ρL : Fin nL → ℝ) (ρR : Fin (nR + 1) → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ → ρR 0 ∈ J →
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ 1 → (∀ u < t, |W u ω| < 1) → (t : ℝ≥0∞) < ζ ω) →
      (∀ᵐ ω ∂P, ∀ᵐ r ∂(volume : Measure ℝ), 0 ≤ r → r.toNNReal ≤ 1 →
        (∀ u < r.toNNReal, |W u ω| < 1) →
        |otherDrift ρL ρR (W r.toNNReal ω) (fun i => VL i r.toNNReal ω)
          (fun i => VR i r.toNNReal ω)| ≤ C) →
      p₀ ≤ P.real {ω | ∀ t : ℝ≥0, t < 1 → |W t ω| < 1} := by
  obtain ⟨ρlo, ρmax, hρlo, hρmax0, hJb⟩ := exists_crossing_params hJ hJ2
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set sk : ℝ := Real.sqrt κ with hskdef
  have hsk : 0 < sk := Real.sqrt_pos.2 hκ
  set cl : ℝ := (2 + ρlo) / κ with hcldef
  have hcl : 0 < cl := div_pos (by linarith) hκ
  set a₁ : ℝ := 1 / (8 * sk) with ha₁def
  have ha₁ : 0 < a₁ := by positivity
  set b₁ : ℝ := cl * sk / (8 * (ρmax + 1)) with hb₁def
  have hb₁ : 0 < b₁ := by positivity
  -- the reference Wiener measure
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, B₀, hB₀, hB₀c, -⟩ := OneForce.exists_filteredBrownian
  have hB₀m : ∀ t, Measurable (B₀ t) := fun t => (hB₀.2.1 t).mono (𝓕₀.le t) le_rfl
  set μ₀ : Measure CPath := P₀.map (toCPath B₀ hB₀c) with hμ₀def
  have : IsProbabilityMeasure μ₀ := by rw [hμ₀def]; infer_instance
  have hμ₀ : IsPreBrownianReal canonBM μ₀ :=
    (isBrownianReal_canonBM hB₀.1.toIsPreBrownianReal hB₀m hB₀c).toIsPreBrownianReal
  obtain ⟨s, hs0, hs1, gY, hgY, hq₁⟩ :=
    exists_pos_measureReal_pastEvent hμ₀ hcl ha₁ hb₁ (s₁ := 1) one_pos
  set a₂ : ℝ := min (1 / 8) (sk * gY / 4) / sk with ha₂def
  have ha₂ : 0 < a₂ := div_pos (lt_min (by norm_num) (by positivity)) hsk
  set q₂ : ℝ := Real.exp (-(Real.pi ^ 2 * ((1 - s : ℝ≥0) : ℝ) / (8 * a₂ ^ 2))) with hq₂def
  set q : ℝ := μ₀.real (pastEvent cl a₁ b₁ gY s) * q₂ with hqdef
  have hq : 0 < q := mul_pos hq₁ (Real.exp_pos _)
  set g : ℝ := sk * gY with hgdef
  have hg : 0 < g := mul_pos hsk hgY
  set M : ℝ := C' / sk + ρmax / sk * (g / 2)⁻¹ with hMdef
  refine ⟨Real.exp (-(M ^ 2 * 2)) * q ^ 2, by positivity, ?_⟩
  intro Ω mΩ P hP 𝓕 nL nR xL xR ρL ρR W VL VR B ζ hE hρJ hlife hU
  obtain ⟨hBF, hWad, hVLad, hVRad, hpath⟩ := hE
  obtain ⟨hρlo', hρmax'⟩ := hJb _ hρJ
  have hmad : ∀ j, AdaptedBefore 𝓕 ζ (allMarks VL VR j) := Sec2.allMarks_adaptedBefore hVLad hVRad
  have hFm : Measurable (uncurry3 (crossF κ C' ρL ρR g s)) := measurable_crossF κ C' ρL ρR hg s
  have hFb : ∀ t w u, |crossF κ C' ρL ρR g s t w u| ≤ M := fun t w u =>
    abs_crossF_le hC'0 hρmax' hg s t w u
  -- the cut time `1 ∧ (lifetime)`
  have hτ : ∀ u : ℝ≥0, MeasurableSet[𝓕 u] {ω | min (1 : ℝ≥0∞) (ζ ω) ≤ u} := by
    intro u
    have h1 : MeasurableSet[𝓕 u] {ω | (u : ℝ≥0∞) < ζ ω} := by
      simpa using hWad u Set.univ MeasurableSet.univ
    have : {ω | min (1 : ℝ≥0∞) (ζ ω) ≤ u} = {_ω | (1 : ℝ≥0∞) ≤ u} ∪ {ω | (u : ℝ≥0∞) < ζ ω}ᶜ := by
      ext ω
      simp [min_le_iff, not_lt]
    rw [this]
    exact (MeasurableSet.const _).union h1.compl
  have hτζ : ∀ ω, min (1 : ℝ≥0∞) (ζ ω) ≤ ζ ω := fun ω => min_le_right _ _
  have hτT : ∀ ω, min (1 : ℝ≥0∞) (ζ ω) ≤ ((1 : ℝ≥0) : ℝ≥0∞) := fun ω => by
    simp
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ j, ContinuousOn (fun s => allMarks VL VR j s ω) {s | (s : ℝ≥0∞) < ζ ω} := by
    filter_upwards [hpath] with ω hp
    refine ⟨hp.2.2.2.1, fun k => ?_⟩
    cases k using Fin.addCases with
    | left i => simpa [allMarks] using hp.2.2.2.2.1 i
    | right i => simpa [allMarks] using hp.2.2.2.2.2.1 i
  have hFc : ∀ᵐ ω ∂P, ∀ᵐ r ∂(volume : Measure ℝ), 0 < r →
      (r.toNNReal : ℝ≥0∞) < min (1 : ℝ≥0∞) (ζ ω) →
      ContinuousAt (uncurry3 (crossF κ C' ρL ρR g s))
        (r.toNNReal, W r.toNNReal ω, fun j => allMarks VL VR j r.toNNReal ω) := by
    filter_upwards [hpath] with ω hp
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcL, hcR, -⟩ := hp
    have hL : ∀ᵐ r ∂(volume : Measure ℝ), ∀ i, r ∉ {r : ℝ | 0 ≤ r ∧
        (r.toNNReal : ℝ≥0∞) < ζ ω ∧ W r.toNNReal ω = VL i r.toNNReal ω} :=
      ae_all_iff.2 fun i => measure_eq_zero_iff_ae_notMem.1 (hcL i)
    have hR : ∀ᵐ r ∂(volume : Measure ℝ), ∀ i, r ∉ {r : ℝ | 0 ≤ r ∧
        (r.toNNReal : ℝ≥0∞) < ζ ω ∧ W r.toNNReal ω = VR i r.toNNReal ω} :=
      ae_all_iff.2 fun i => measure_eq_zero_iff_ae_notMem.1 (hcR i)
    filter_upwards [hL, hR, ae_ne_real (s : ℝ)] with r hrL hrR hrs hr0 hrτ
    have hrζ : (r.toNNReal : ℝ≥0∞) < ζ ω := hrτ.trans_le (hτζ ω)
    refine continuousAt_crossF κ C' ρL ρR hg s ?_ (fun i => ?_) (fun i => ?_)
    · intro h
      apply hrs
      rw [← h, Real.coe_toNNReal _ hr0.le]
    · rw [markL_allMarks]
      exact fun h => hrL i ⟨hr0.le, hrζ, h⟩
    · rw [markR_allMarks]
      exact fun h => hrR i ⟨hr0.le, hrζ, h⟩
  -- Girsanov
  obtain ⟨hequiv, hBQ, hid⟩ := girsanov_cutDriftT hBF hFm hFb hWad hmad hτ hτζ hτT hcont hFc
  have hQprob := hequiv.isProb
  have hQP := hequiv.ac
  have := isFilteredPreBrownian_of_isFilteredBrownianReal hBF
  have hθp := isStronglyProgressive_cutDriftT hFm hWad hmad hτ
  have hθb := abs_cutDriftT_le (τ := fun ω => min (1 : ℝ≥0∞) (ζ ω)) (ζ := ζ) (W := W)
    (U := allMarks VL VR) hFb
  have hθreg := isRiemannRegular_cutDriftT (P := P) hFb hτζ hcont hFc
  have hA'm := measurableSet_goodEvent hWad
  have htr := le_measureReal_of_girsanov (B := B) hθp.stronglyAdapted hθb hθreg (1 + 1) hA'm
  set θ := cutDriftT (fun ω => min (1 : ℝ≥0∞) (ζ ω)) ζ (crossF κ C' ρL ρR g s) W (allMarks VL VR)
    with hθdef
  set Q := girsanovMeasure P 𝓕 B θ (1 + 1) with hQdef
  -- `goodEvent ⊆ {τ ≥ 1}`
  have hAA : P.real (goodEvent W ζ) ≤ P.real {ω | ∀ t : ℝ≥0, t < 1 → |W t ω| < 1} := by
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
    filter_upwards [hcont] with ω hω hωA
    exact forall_abs_lt_of_mem_goodEvent hω.1 hωA
  -- the changed Brownian motion has the reference law
  obtain ⟨Bt, hBtm, hBtc, -, hBt, hBteq⟩ := exists_good_version0 hBQ.1
  have hmap : Q.map (toCPath Bt hBtc) = μ₀ :=
    map_toCPath_eq hBt.toIsPreBrownianReal hB₀.1.toIsPreBrownianReal hBtm hB₀m hBtc hB₀c
  set E : Set CPath := pastEvent cl a₁ b₁ gY s ∩ incrEvent s (1 - s) a₂ with hEdef
  have hshift : Measurable fun f : CPath => shiftPath s f :=
    measurable_pi_iff.2 fun u => (measurable_canonBM _).sub (measurable_canonBM s)
  have hEm : MeasurableSet E :=
    (canonFilt.le s _ (measurableSet_pastEvent hcl a₁ b₁ gY s)).inter
      (hshift.comap_le _ (measurableSet_incrEvent s (1 - s) a₂))
  have hQE : Q.real (toCPath Bt hBtc ⁻¹' E) = μ₀.real E := by
    rw [← hmap, measureReal_def, measureReal_def,
      Measure.map_apply (measurable_toCPath hBtm hBtc) hEm]
  have hμE : q ≤ μ₀.real E := by
    rw [hEdef, measureReal_pastEvent_inter_incrEvent hμ₀ hcl]
    exact mul_le_mul_of_nonneg_left (exp_le_measureReal_incrEvent hμ₀ s (1 - s) ha₂)
      measureReal_nonneg
  have hBes : ∀ᵐ ω ∂Q, Bessel.IsBesselPath cl 0 (fun t => -(toCPath Bt hBtc ω).1 t)
      (fun t => besY cl (toCPath Bt hBtc ω) t) := by
    have h := ae_isBesselPath_besY hμ₀ hcl
    rw [← hmap] at h
    exact ae_of_ae_map (measurable_toCPath hBtm hBtc).aemeasurable h
  -- the pathwise argument on `E`
  have hincl : toCPath Bt hBtc ⁻¹' E ≤ᵐ[Q] goodEvent W ζ := by
    filter_upwards [hQP.ae_le hpath, hQP.ae_le hlife, hQP.ae_le hU, hQP.ae_le hid, hBteq, hBes]
      with ω hp hl hu hgi hBe hYb hωE
    obtain ⟨⟨hE1, hE2, hE3⟩, hF⟩ := hωE
    have hsplit := fun (t : ℝ≥0) (ht : (t : ℝ≥0∞) < ζ ω) => w_eq_split hp ht
    obtain ⟨hw0, -, hvR0, hwc, -, hvRc, -, -, hwvR, -, -, hgR, -, -, hvReq, -, hcR, -⟩ := hp
    have hlife' : ∀ t, InDom (fun t => W t ω) t → (t : ℝ≥0∞) < ζ ω := fun t ht => hl t ht.1 ht.2
    have hx : 0 ≤ xR 0 := by
      have h0 := hwvR 0 (hlife' 0 ⟨zero_le_one, fun u hu => absurd hu (not_lt_zero)⟩) 0
      rw [hw0, hvR0 0] at h0
      exact h0
    have ho : ∀ᵐ r ∂(volume : Measure ℝ), 0 ≤ r → InDom (fun t => W t ω) r.toNNReal →
        |otherDrift ρL ρR (W r.toNNReal ω) (fun i => VL i r.toNNReal ω)
          (fun i => VR i r.toNNReal ω)| ≤ C' := by
      filter_upwards [hu] with r hr hr0 hd
      exact (hr hr0 hd.1 hd.2).trans (le_max_left _ _)
    have hgir : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ min 1 (ζ ω) → Bt t ω = B t ω + ∫ r in (0 : ℝ)..t,
        crossIntegrand κ C' (ρR 0) g s r.toNNReal (W r.toNNReal ω)
          (VR 0 r.toNNReal ω) (otherDrift ρL ρR (W r.toNNReal ω) (fun i => VL i r.toNNReal ω)
            (fun i => VR i r.toNNReal ω)) := by
      intro t ht
      rw [hBe t, hgi t ht]
      simp only [crossF_allMarks]
    have hsk0 := hsk.ne'
    have hcl0 := hcl.ne'
    have ha₁' : sk * a₁ + ρmax * b₁ / (cl * sk) ≤ 1 / 4 := by
      have e1 : sk * a₁ = 1 / 8 := by
        rw [ha₁def]; field_simp
      have e2 : ρmax * b₁ / (cl * sk) = ρmax / (8 * (ρmax + 1)) := by
        rw [hb₁def]; field_simp
      have e3 : ρmax / (8 * (ρmax + 1)) ≤ 1 / 8 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    have ha₂' : sk * a₂ ≤ min (1 / 8) (sk * gY / 4) := by
      rw [ha₂def, mul_div_cancel₀ _ hsk.ne']
    have hclc : cl ≤ (2 + ρR 0) / κ := div_le_div_of_nonneg_right (by linarith) hκ.le
    have hpath' := crossing_path (w := fun t => W t ω) (v := fun t => VR 0 t ω)
      (o := fun t => otherDrift ρL ρR (W t ω) (fun i => VL i t ω) (fun i => VR i t ω))
      (b := fun t => B t ω) (bq := fun t => Bt t ω) (y := fun t => besY cl (toCPath Bt hBtc ω) t)
      (ζ := ζ ω) (C := C') hκ hgY hρmax' hcl hclc hx hw0 hlife' hwc (hvRc 0)
      (fun t ht => hwvR t ht 0) (fun t ht => hgR t ht 0) (fun t ht => (hsplit t ht).1)
      (fun t ht => (hsplit t ht).2) (fun t ht => hvReq t ht 0) (hcR 0) ho hgir hYb hE1 hE2 hE3 hF
      ha₁' ha₂'
    simp only [goodEvent, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_Icc]
    intro q hq
    obtain ⟨h1, h2⟩ := hpath' q (le_of_mem_ratTimesLE hq)
    exact ⟨h1, (abs_le.1 h2).1, (abs_le.1 h2).2⟩
  have hQA : q ≤ Q.real (goodEvent W ζ) :=
    hμE.trans (hQE ▸ ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hincl))
  have h2 : ((1 + 1 : ℝ≥0) : ℝ) = 2 := by norm_num
  rw [h2] at htr
  calc Real.exp (-(M ^ 2 * 2)) * q ^ 2
      ≤ Real.exp (-(M ^ 2 * 2)) * (Q.real (goodEvent W ζ)) ^ 2 := by
        gcongr
    _ ≤ P.real (goodEvent W ζ) := htr
    _ ≤ _ := hAA

/-- **Lemma 5.10** as printed: for a fixed first right weight `ρ_{1,R} > −2` the constant depends only on
`C`, `κ` and `ρ_{1,R}` (`crossing_lower_bound` with `J = {ρ_{1,R}}`). -/
theorem crossing_lower_bound_of_gt {κ C ρ : ℝ} (hκ : 0 < κ) (hρ : -2 < ρ) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin (nR + 1) → ℝ)
      (ρL : Fin nL → ℝ) (ρR : Fin (nR + 1) → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ → ρR 0 = ρ →
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ 1 → (∀ u < t, |W u ω| < 1) → (t : ℝ≥0∞) < ζ ω) →
      (∀ᵐ ω ∂P, ∀ᵐ r ∂(volume : Measure ℝ), 0 ≤ r → r.toNNReal ≤ 1 →
        (∀ u < r.toNNReal, |W u ω| < 1) →
        |otherDrift ρL ρR (W r.toNNReal ω) (fun i => VL i r.toNNReal ω)
          (fun i => VR i r.toNNReal ω)| ≤ C) →
      p₀ ≤ P.real {ω | ∀ t : ℝ≥0, t < 1 → |W t ω| < 1} := by
  obtain ⟨p₀, hp₀, h⟩ := crossing_lower_bound (C := C) hκ (J := {ρ}) isCompact_singleton
    (Set.singleton_subset_iff.2 hρ)
  exact ⟨p₀, hp₀, fun P _ 𝓕 _ _ xL xR ρL ρR W VL VR B ζ hE hρR hl hU =>
    h P 𝓕 xL xR ρL ρR W VL VR B ζ hE (hρR ▸ Set.mem_singleton ρ) hl hU⟩

end Sec5

end InteractingSLE
