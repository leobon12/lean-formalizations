/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SchedRuleCand

/-!
# GW2's one-root rule: the raw-driver capacity is incompatible with the record σ-algebras

Packet PROVE-GW2-ROOT. PROVE-GW2-SCHED's concrete one-root rule `GW2TipSystem.gw2RootRule` measures the relative
capacity of a schedule's prefix (`schedCap`, field `cap`) in the joint chart of the **raw** counterflow driver `W'`,
while its stage-start σ-algebras (`stageSigma`) see the counterflow only through the **regularized record**
`GW2JointKernel.cfE s W' ζ'` (`StagedReg.regularize`), which reads the driver at dyadic times only. The unit clause
`hcapU` of `CandClaims` is deterministic (every sample of `A ∩ V`), whereas `A` and `V` must be measurable for the
record σ-algebras. Two samples with the same records but different raw drivers therefore must be treated alike by `A`
and `V`, but `hcapU` is checked at both.

This file proves, in Lean, every step of the resulting obstruction except the construction of the twin probability
space:

* `SchedRule.RootClaims.measure_R₀_eq_zero_of_twin` (generic): if every sample has a twin which no stage σ-algebra
  separates from it and at which the capacity never increases along an extension, then the stage claims of a rule with
  total tolerance `ε₀ < 1` force every root event to be null (a unit outcome cannot occur, so the success and the
  no-unit events coincide; Lemma 5.10's bound then contradicts the stage claim at a deep even depth, and the stage claim
  propagates the nullity back to the root);
* `subset_fwdHull_of_not_continuousOn`: a forward Loewner flow whose driver is discontinuous on `[0, T]` swallows all of
  `ℍ` by time `T` (QuantumZipper's centred forward solutions are continuous);
* `schedCap_cons_le_of_subset_fwdHull`: at such a sample every prefix image is empty, so the concrete capacity never
  increases;
* `cfE_congr_dyad`, `stageMap_eq_of_dyad`: the stage records only read the counterflow driver at dyadic times;
* **`measure_eq_zero_of_rootClaims_twin`**, **`measure_eq_zero_of_candClaims_twin`**: the stage claims of
  `gw2RootRule` (`RootClaims`, for any stage data, as in `GW2RootStageStatement`; or `CandClaims`, as in
  `GW2RootCandStatement`) with `ε₀ < 1` force the initial event to be null as soon as every sample has a twin with the
  same stage records whose raw driver is discontinuous on `[0, s]`.

**Consequence (mathematical, recorded in the handoff).** Given any admissible configuration `(Ω, P, h, W', ζ', γ)` with
`P(γ(s) ∈ ℍ) > 0`, the twin space `Ω × Bool` with `P ⊗ δ_false`, the field and lifetime of the first coordinate, and
the driver modified at `(ω, true)` at one non-dyadic time `t₀ < s` (raising it by `1`) is again admissible (all
hypotheses of `GW2RootCandStatement` are laws or almost-sure properties; `StagedReg.isFlowLineDriver_congr_ae`), every
sample has a twin as above (if `W'(·, ω)` is continuous at `t₀` the twin is `(ω, true)`, otherwise `(ω, false)` itself
is discontinuous), and `GW2RootCandStatement` (or `GW2RootStageStatement`) would give `P(γ(s) ∈ ℍ) = 0`. Hence both
statements are false for such configurations; the repaired statement computes the capacity from the regularized
record (`GW2RootReg.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2TipSystem

open GW2Schedule GW2Cone GW2Later GW2Tip GW2TipStage Exist Staged StagedLaw Restart LQGMetric

/-! ### The generic obstruction -/

namespace SchedRule

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {T : SchedRule Ω}

/-- A failed stage claim: `1 − ε ≤ ofReal (1 − p₀)` is impossible when `ε < ofReal p₀` and `p₀ ≤ 1`. -/
theorem not_one_sub_le_ofReal_one_sub {ε : ℝ≥0∞} {p₀ : ℝ} (hp₀1 : p₀ ≤ 1) (hε : ε < ENNReal.ofReal p₀) :
    ¬ 1 - ε ≤ ENNReal.ofReal (1 - p₀) := by
  intro hle
  have hp₀ : 0 ≤ p₀ := by
    by_contra hneg
    rw [ENNReal.ofReal_of_nonpos (le_of_lt (not_le.1 hneg))] at hε
    exact absurd hε not_lt_zero
  have hεt : ε ≠ ⊤ := ne_top_of_lt hε
  have hε1 : ε < 1 := lt_of_lt_of_le hε (ENNReal.ofReal_le_one.2 hp₀1)
  have h1 : (1 - ε).toReal ≤ (ENNReal.ofReal (1 - p₀)).toReal :=
    (ENNReal.toReal_le_toReal (ENNReal.sub_ne_top ENNReal.one_ne_top) ENNReal.ofReal_ne_top).2 hle
  rw [ENNReal.toReal_sub_of_le hε1.le ENNReal.one_ne_top, ENNReal.toReal_one,
    ENNReal.toReal_ofReal (by linarith)] at h1
  have h2 : ε.toReal < p₀ := by
    have := (ENNReal.toReal_lt_toReal hεt ENNReal.ofReal_ne_top).2 hε
    rwa [ENNReal.toReal_ofReal hp₀] at this
  linarith

/-- **The generic obstruction.** Let `T` satisfy its stage claims with total tolerance `ε₀ < 1`, with sub-σ-algebras
`T.𝒢`. If every sample `ω` has a twin `ω'` that lies in every stage-measurable event containing `ω` and at which the
capacity never increases along an extension, then every root event is null.

Proof: a twin of a sample of `O ∩ V(extension)` is again in `O ⊆ A(extension)` and in `V(extension)`, where `hcapU`
asks for an increase; so `O ∩ V(extension) = ∅`, every success is a no-unit outcome (`E ⊆ D`), and at a deep even depth
with `ε_j < p₀` the stage claim and the uniform Lemma 5.10 contradict each other on `A`. Backwards, if every extension
of a schedule is null then so is every success event, its conditional probabilities vanish almost surely, and the stage
claim (`ε_j < 1`) makes the schedule's own alive event null. -/
theorem RootClaims.measure_R₀_eq_zero_of_twin [StandardBorelSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ε₀ : ℝ≥0∞} (hc : T.RootClaims P ε₀) (hε₀ : ε₀ < 1) (h𝒢 : ∀ s, T.𝒢 s ≤ mΩ)
    (htwin : ∀ ω, ∃ ω', (∀ s (S : Set Ω), MeasurableSet[T.𝒢 s] S → ω ∈ S → ω' ∈ S) ∧
      ∀ r l x, T.cap (r, x :: l) ω' ≤ T.cap (r, l) ω') (r : T.ι) : P (T.R₀ r) = 0 := by
  -- no unit outcome
  have hOV : ∀ (l : List T.X) (i : ℕ) (o : T.K), ∀ ω, ω ∈ T.O (r, l) i o → ω ∉ T.V (r, T.entry i o :: l) := by
    intro l i o ω hO hV
    obtain ⟨ω', hsame, hcap⟩ := htwin ω
    have hO' := hsame _ _ (hc.hO r l i o) hO
    have hV' := hsame _ _ (hc.hV _) hV
    have hA' := hc.hOA r l i o hO'
    have h1 := hc.hcapU r l (T.entry i o) ω' hA' hV'
    have h2 := hcap r l (T.entry i o)
    linarith
  have hED : ∀ (l : List T.X) (i : ℕ), T.E (r, l) i ⊆ T.D (r, l) i := by
    intro l i ω hω
    obtain ⟨o, ho⟩ := mem_iUnion.1 (hc.hEO _ i hω)
    exact hc.hOD r l i o ⟨ho, hOV l i o ω ho⟩
  -- tolerances
  have hsum : ∑' j, T.ε j ≠ ⊤ := ne_top_of_le_ne_top (ne_top_of_lt hε₀) hc.hε
  have hεlt : ∀ j, T.ε j < 1 := fun j => lt_of_le_of_lt ((ENNReal.le_tsum j).trans hc.hε) hε₀
  have hp₀pos : (0 : ℝ≥0∞) < ENNReal.ofReal T.p₀ := ENNReal.ofReal_pos.2 hc.hp₀
  obtain ⟨N, hN⟩ := ((ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsum).eventually
    (gt_mem_nhds hp₀pos)).exists_forall_of_atTop
  set k := N with hk
  -- the deep even depth is null
  have hdeep : ∀ l : List T.X, l.length = 2 * k + 4 → P (T.A (r, l)) = 0 := by
    intro l hl
    have hlt : T.ε (r, l).2.length < ENNReal.ofReal T.p₀ := hN _ (by simp only [hl]; omega)
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hc.hstep (r, l), hc.hunit k (r, l) hl] with ω h1 h2 hA
    obtain ⟨i, hi⟩ := h1 hA
    have h3 := h2 hA i
    exact not_one_sub_le_ofReal_one_sub hc.hp₀1 hlt (hi.trans ((measure_mono (hED l i)).trans h3))
  -- backwards induction
  have hback : ∀ d (l : List T.X), l.length + d = 2 * k + 4 → P (T.A (r, l)) = 0 := by
    intro d
    induction d with
    | zero => exact fun l hl => hdeep l hl
    | succ d ih =>
      intro l hl
      have hext : ∀ x, P (T.A (r, x :: l)) = 0 := fun x => ih (x :: l) (by simp only [List.length_cons]; omega)
      have hE0 : ∀ i, P (T.E (r, l) i) = 0 := by
        intro i
        have := T.countableK
        refine measure_mono_null (fun ω hω => ?_) (measure_iUnion_null fun o => hext (T.entry i o))
        obtain ⟨o, ho⟩ := mem_iUnion.1 (hc.hEO _ i hω)
        exact mem_iUnion.2 ⟨o, hc.hOA r l i o ho⟩
      have hκ0 : ∀ i, ∀ᵐ ω ∂P, condExpKernel P (T.𝒢 (r, l)) ω (T.E (r, l) i) = 0 := by
        intro i
        have hEm := hc.hE (r, l) i
        have hmeas : Measurable fun ω => condExpKernel P (T.𝒢 (r, l)) ω (T.E (r, l) i) :=
          (measurable_condExpKernel hEm).mono (h𝒢 _) le_rfl
        have hint := KernelTower.setLIntegral_condExpKernel (P := P) (h𝒢 (r, l)) MeasurableSet.univ hEm
        rw [Measure.restrict_univ, univ_inter, hE0 i, lintegral_eq_zero_iff hmeas] at hint
        exact hint
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hc.hstep (r, l), ae_all_iff.2 hκ0] with ω h1 h2 hA
      obtain ⟨i, hi⟩ := h1 hA
      rw [h2 i, nonpos_iff_eq_zero, tsub_eq_zero_iff_le] at hi
      exact absurd (hεlt _) (not_lt.2 hi)
  exact measure_mono_null (hc.hR₀A r) (hback (2 * k + 4) [] (by simp))

end SchedRule

/-! ### Discontinuous drivers swallow the half-plane -/

/-- **A forward flow whose driver is discontinuous on `[0, T]` swallows all of `ℍ` by time `T`**: a centred forward
solution `u t = z − W t + ∫₀ᵗ 2/u` is continuous and nonvanishing, so the driver would be continuous on the interval of
the solution. -/
theorem subset_fwdHull_of_not_continuousOn {W : ℝ → ℝ} {T : ℝ} (hW : ¬ ContinuousOn W (Icc 0 T)) :
    H ⊆ QuantumZipper.fwdHull W T := by
  intro z hz
  refine ⟨hz, ?_⟩
  unfold QuantumZipper.swallowTime
  refine sSup_le ?_
  rintro _ ⟨T', ⟨hT'0, u, hu⟩, rfl⟩
  apply ENNReal.ofReal_le_ofReal
  by_contra hlt
  push Not at hlt
  apply hW
  have hu0 : ∀ t ∈ Icc 0 T', u t ≠ 0 := fun t ht => (hu.2 t ht).1
  have hcont : ContinuousOn (fun t => 2 / u t) (Icc 0 T') := continuousOn_const.div hu.1 hu0
  have hprim : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, 2 / u s) (Icc 0 T') := by
    have h1 := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := T')
      (f := fun s => 2 / u s) (by rw [uIcc_of_le hT'0]; exact hcont.integrableOn_Icc)
    rwa [uIcc_of_le hT'0] at h1
  have hWc : ContinuousOn (fun t => ((W t : ℝ) : ℂ)) (Icc 0 T') := by
    refine (((continuousOn_const (c := z)).add hprim).sub hu.1).congr fun t ht => ?_
    have e := (hu.2 t ht).2
    simp only [Pi.add_apply, Pi.sub_apply]
    linear_combination e
  have hWc' : ContinuousOn W (Icc 0 T') :=
    (Complex.continuous_re.comp_continuousOn hWc).congr fun t _ => by simp
  exact hWc'.mono (Icc_subset_Icc le_rfl hlt.le)

/-! ### The concrete capacity at a sample with a discontinuous raw driver -/

theorem capOf_nonneg (A : Set ℂ) : 0 ≤ capOf A := by
  unfold capOf
  split_ifs with hA
  · exact div_nonneg (HPHull.hcap_nonneg _) zero_le_two
  · exact le_rfl

section Cap

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u}) (βA : BoundaryWord × ℝ × RecData → BoundaryWord)
  (b : ℝ → ℝ) (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u} (h : Ω → DistOn upperHalfPlaneOpens)
  (W' : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (Θ : Set ℝ) (Q : Set ℝ≥0)

/-- An admissible schedule's initial segments are admissible. -/
theorem SchedAdm.of_cons {x : ℝ} {e₀ y : ℝ × ℝ≥0} {xs : List (ℝ × ℝ≥0)}
    (h : SchedAdm b jumps Θ Q (κ := κ) x e₀ (y :: xs)) : SchedAdm b jumps Θ Q (κ := κ) x e₀ xs := by
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  rw [schedOf_cons] at h2
  exact ⟨fun p hp => h2.1 p (List.mem_append_left _ hp), (List.pairwise_append.1 h2.2).1⟩

/-- The capacity of one schedule is nonnegative. -/
theorem capV_nonneg (x : ℝ) (e₀ : ℝ × ℝ≥0) (xs : List (ℝ × ℝ≥0)) (ω : Ω) :
    0 ≤ capV hκ h12p βA b jumps c₀ h W' s Θ Q x e₀ xs ω := by
  unfold capV
  split_ifs
  · exact capOf_nonneg _
  · exact le_rfl

/-- At a sample whose counterflow hull at `s` is all of `ℍ`, every prefix image is empty. -/
theorem capV_eq_of_subset_fwdHull {ω : Ω}
    (hH : H ⊆ QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal ω) s) (x : ℝ) (e₀ : ℝ × ℝ≥0)
    (xs : List (ℝ × ℝ≥0)) :
    capV hκ h12p βA b jumps c₀ h W' s Θ Q x e₀ xs ω =
      (open scoped Classical in if SchedAdm b jumps Θ Q (κ := κ) x e₀ xs then capOf ∅ else 0) := by
  have he : H \ QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal ω) s = ∅ := sdiff_eq_empty.2 hH
  have hP : prefixImage hκ h12p βA b jumps c₀ h W' s x (schedOf e₀ xs) ω = ∅ := by
    unfold prefixImage
    rw [he, image_empty, inter_empty, image_empty]
  unfold capV
  rw [hP]

/-- **At a sample whose counterflow hull at `s` is all of `ℍ`, the concrete capacity never increases.** -/
theorem schedCap_cons_le_of_subset_fwdHull {ω : Ω}
    (hH : H ⊆ QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal ω) s) (x : ℝ) (e₀ y : ℝ × ℝ≥0)
    (xs : List (ℝ × ℝ≥0)) :
    schedCap hκ h12p βA b jumps c₀ h W' s Θ Q x e₀ (y :: xs) ω ≤
      schedCap hκ h12p βA b jumps c₀ h W' s Θ Q x e₀ xs ω := by
  classical
  have hle : capV hκ h12p βA b jumps c₀ h W' s Θ Q x e₀ (y :: xs) ω ≤
      capV hκ h12p βA b jumps c₀ h W' s Θ Q x e₀ xs ω := by
    rw [capV_eq_of_subset_fwdHull hκ h12p βA b jumps c₀ h W' s Θ Q hH,
      capV_eq_of_subset_fwdHull hκ h12p βA b jumps c₀ h W' s Θ Q hH]
    by_cases had : SchedAdm b jumps Θ Q (κ := κ) x e₀ (y :: xs)
    · simp only [had, SchedAdm.of_cons b jumps Θ Q had, ↓reduceIte, le_refl]
    · simp only [had, ↓reduceIte]
      split_ifs
      · exact capOf_nonneg _
      · exact le_rfl
  exact max_le le_rfl (hle.trans (capV_le_schedCap hκ h12p βA b jumps c₀ h W' s Θ Q x e₀ xs ω))

end Cap

/-! ### The stage records read the counterflow at dyadic times only -/

open Sec2.Assembly in
/-- The regularization of a driver only depends on its dyadic codes and its lifetime. -/
theorem regularize_congr {t : ℝ≥0∞} {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞} (h1 : enc e.1 = enc e'.1) (h2 : e.2 = e'.2) :
    StagedReg.regularize t e = StagedReg.regularize t e' := by
  have h0 : e.1 0 = e'.1 0 := by
    have := congrFun (congrFun h1 0) 0
    simpa [enc, dyad] using this
  unfold StagedReg.regularize StagedReg.GoodAll StagedReg.GoodTo
  rw [h0, h1, h2]

open Sec2.Assembly in
/-- **The regularized counterflow record only reads the driver at dyadic times** (and its lifetime). -/
theorem cfE_congr_dyad {Ω : Type*} (s : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) {ω ω' : Ω} (hζ : ζ ω = ζ ω')
    (hW : ∀ n k, W (dyad n k) ω = W (dyad n k) ω') : GW2JointKernel.cfE s W ζ ω = GW2JointKernel.cfE s W ζ ω' := by
  unfold GW2JointKernel.cfE
  refine regularize_congr ?_ hζ
  funext n k
  simp only [enc, GW2JointKernel.cfKW, hζ, hW n k]

open Sec2.Assembly in
/-- **Two samples with the same field, the same lifetime and the same counterflow driver at dyadic times have the
same stage records** (for every history and every number of pieces). -/
theorem stageMap_eq_of_dyad {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
    (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord) {Ω : Type u}
    (h : Ω → DistOn upperHalfPlaneOpens) (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) {ω ω' : Ω}
    (hh : h ω = h ω') (hζ : ζ' ω = ζ' ω') (hW : ∀ n k, W' (dyad n k) ω = W' (dyad n k) ω') (spec : ExplSpec)
    (n : ℕ) : stageMap hκ h12p βA c₀ h s W' ζ' spec n ω = stageMap hκ h12p βA c₀ h s W' ζ' spec n ω' := by
  simp only [stageMap, cfRec, stopRec, cfE_congr_dyad s W' ζ' hζ hW, hh]

/-! ### The obstruction for the concrete one-root rule -/

section Concrete

variable {κ : ℝ} {hκ : 0 < κ} {h12p : Theorem12ParamStatement.{u}} {βA : BoundaryWord × ℝ × RecData → BoundaryWord}
  {b : ℝ → ℝ} {jumps : Finset ℝ} {c₀ : BoundaryWord} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {Θ : Set ℝ} {Q : Set ℝ≥0}
  {hΘc : Θ.Countable} {hQc : Q.Countable} {s : ℝ≥0} {r : ScaledRootIdx Θ Q} {G : Set Ω}

/-- **The stage claims of the concrete one-root rule force a null initial event on a twinned space** (any stage data
`d`). If every sample `ω` has a twin `ω'` with the same stage records (`stageMap`, for every history and number of
pieces) whose raw counterflow driver is discontinuous on `[0, s]`, then `RootClaims` with total tolerance `ε₀ < 1`
gives `P G = 0`. -/
theorem measure_eq_zero_of_rootClaims_twin [StandardBorelSpace Ω] (hβA : Measurable βA) (hh : Measurable h)
    {P : Measure Ω} [IsFiniteMeasure P] (hcf : IsCenteredCounterflowDriver κ P h W' ζ') {ε₀ : ℝ≥0∞} (hε₀ : ε₀ < 1)
    {d : GW2StageData Θ Q Ω} (hR : (gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d).RootClaims P ε₀)
    (htwin : ∀ ω, ∃ ω', (∀ spec n, stageMap hκ h12p βA c₀ h s W' ζ' spec n ω' =
        stageMap hκ h12p βA c₀ h s W' ζ' spec n ω) ∧
      ¬ ContinuousOn (fun t : ℝ => W' t.toNNReal ω') (Icc 0 (s : ℝ))) :
    P G = 0 := by
  have hle : ∀ n, (gw2RootRule hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d).𝒢 n ≤ mΩ :=
    gw2RootRule_sigma_le hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G d hβA hh hcf
  refine hR.measure_R₀_eq_zero_of_twin hε₀ hle (fun ω => ?_) ()
  obtain ⟨ω', hmap, hdisc⟩ := htwin ω
  have hH : H ⊆ QuantumZipper.fwdHull (fun t : ℝ => W' t.toNNReal ω') s := subset_fwdHull_of_not_continuousOn hdisc
  refine ⟨ω', ?_, ?_⟩
  · intro (sch : Unit × List (EntryIdx Θ Q)) S hS hω
    obtain ⟨B, -, rfl⟩ := hS
    change stageMap hκ h12p βA c₀ h s W' ζ' (schedSpecOf r.1 sch.2) ((entryList sch.2).length + 1) ω' ∈ B
    rw [hmap]
    exact hω
  · intro (r' : Unit) (l : List (EntryIdx Θ Q)) (x : EntryIdx Θ Q)
    change 4 ^ r.2 * schedCap hκ h12p βA b jumps c₀ h W' s Θ Q (rootPt r.1) (rootEntry r.1) (entryList (x :: l)) ω' ≤
      4 ^ r.2 * schedCap hκ h12p βA b jumps c₀ h W' s Θ Q (rootPt r.1) (rootEntry r.1) (entryList l) ω'
    rw [entryList_cons]
    exact mul_le_mul_of_nonneg_left
      (schedCap_cons_le_of_subset_fwdHull hκ h12p βA b jumps c₀ h W' s Θ Q hH _ _ _ _) (by positivity)

/-- **The per-test claims of the concrete one-root rule force a null initial event on a twinned space** (the
`CandClaims` form, through `GW2CandData.rootClaims`). -/
theorem measure_eq_zero_of_candClaims_twin [StandardBorelSpace Ω] (hβA : Measurable βA) (hh : Measurable h)
    {P : Measure Ω} [IsFiniteMeasure P] (hcf : IsCenteredCounterflowDriver κ P h W' ζ') {ε₀ : ℝ≥0∞} (hε₀ : ε₀ < 1)
    {cd : GW2CandData Θ Q Ω} (hc : CandClaims hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G P ε₀ cd)
    (htwin : ∀ ω, ∃ ω', (∀ spec n, stageMap hκ h12p βA c₀ h s W' ζ' spec n ω' =
        stageMap hκ h12p βA c₀ h s W' ζ' spec n ω) ∧
      ¬ ContinuousOn (fun t : ℝ => W' t.toNNReal ω') (Icc 0 (s : ℝ))) :
    P G = 0 :=
  measure_eq_zero_of_rootClaims_twin hβA hh hcf hε₀ (GW2CandData.rootClaims hβA hh hcf hc) htwin

end Concrete

end GW2TipSystem

end Theorem14

end InteractingSLE
