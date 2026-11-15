/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux97GermPost
import InteractingSLE.Spec.Sec7.Lemma725RefK2
import InteractingSLE.Spec.Sec7.Lemma725Det

/-!
# Aux. lemma 126 at the level of the field: the exact stopped two-seed coupling and its stopped graph

Packet PROVE-LEMMA725REF. Specification §7.4, Aux. lemma 126 and its proof (`source/spec/p385-432.md` L251–L316,
pp. 399–402), the paragraphs "An exact stopped two-seed coupling" (FS11.1)–(FS11.4) and the measurable factorization
before "Finite-time continuity by dilation of the driving law":

> If `H` denotes the reference field under `ℙ`, make the equivalent whole-field change of measure (FS11.2) […]
> Consequently `(H₀, W_{·∧S_r})` is a genuine stopped coupling under the original two-seed specification. […] Thus there
> is one Borel map whose graph carries the reference stopped pair law. Equivalence in (FS11.2) preserves continuity of
> the reference trace through `S_r` and this same graph. Since `f − q` is deterministic, the invertible Borel recoding
> `H = H₀ − f + q` makes the recorded stopped driver […] a Borel function of the whole `H₀` under `ℚ`. […] Aux. lemma 54
> extends our stopped pair to a full original two-seed coupling, preserving the entire initial field and its stopped
> graph.

PROVE-AUX126 proved the driving part (`Aux126.exists_twoSeed_bufferedTrace`). Here the field part is assembled from
landed results: the change of measure and the stopped seed coupling of Aux. lemma 55 at time `0`
(`LocalExt.srcMeasure`, `LocalExt.isStoppedSeedCoupling_srcMeasure`, (HL3)–(HL9) = (FS11.2)–(FS11.4) with the seed
radius of `LocalExt.seedRadius` as the buffer), Aux. lemma 54 in the source's form
(`LocalExt.stoppedSeedExtendStatement`: the extension keeps the field and agrees with the stopped history), and the determination of stopped histories in a
field-determined coupling (`IsOptionalHullCoupling.isAEDeterminedBy_stoppedHistory`).

## Main results

* `seedProj_eq_self`, `recode_add_neg`: the seed normalization is trivial for a word with a seed on each side; the
  recoding `h₀ = h + f − q` is inverted by adding `−(f − q)`;
* **`exists_twoSeed_stoppedGraph_of_reference`**: from the hypothesis of Aux. lemma 126 (`Aux126Reference κ r_L r_R`,
  field level), there are a radius `r > 0` and a **full** coupling of `SLE_κ(r_L; r_R)` with the original optional hull
  specification, with a good event `G`, whose history stopped at the capped local stop of radius `r` is a Borel function
  of its field.
* `StoppedToFullDeterminationStatement` (**named input**: the paragraphs "Finite-time continuity by dilation …" and
  "Universal field determination" of Aux. lemma 126, p. 401–402: dilation of the stopped pair, Aux. lemma 50 through
  the bounded stops `S_{R_n}`, the consistent assembly of the stopped graphs) and
  **`lemma725DetReferenceStatement_of_ref`**: `Aux50Hit.Lemma725DetReferenceStatement` from `Lemma725ReferenceStatement` (the field-level pocket reference with its
  distant marks, `Lemma725RefK2.lemma725ReferenceStatement_of_pocketWordField`) and that input.

Ruling R48: nothing here takes Theorem 1.2/1.3, `Theorem12ParamStatement` or `Theorem13Statement` as a hypothesis.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Lemma725RefStop

open LocalExt LQGMetric

universe u

/-- For a word with a seed mark on each side, the seed normalization of a two-seed history is trivial. -/
theorem seedProj_eq_self {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hL : ∃ i, xL i = 0)
    (hR : ∃ j, xR j = 0) (y : TwoSeedHist) : seedProj xL xR y = y := by
  unfold seedProj
  simp only [hL, hR, ite_true]
  refine Prod.ext rfl (funext fun q => Prod.ext rfl (Prod.ext (funext fun i => ?_) (funext fun i => ?_))) <;>
    rw [Subsingleton.elim i 0]

/-- The recoding of (HL8) is inverted by a deterministic translation. -/
theorem recode_add_neg {κ : ℝ} {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (r : ℝ) (T : DistOn upperHalfPlaneOpens) :
    recode κ xL xR ρL ρR r T +
        -SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (recodeShift κ xL xR ρL ρR r) = T := by
  rw [recode, add_neg_cancel_right]

/-- **Aux. lemma 126, the exact stopped two-seed coupling at the level of the field** (pp. 400–401). From the hypothesis
of Aux. lemma 126 (a field-determined reference whose seeds at `0⁻, 0⁺` have the weights `r_L, r_R` and whose other
marks are strictly separated from `0`): a radius `r > 0` and a full coupling of `SLE_κ(r_L; r_R)` with the original
optional hull specification, with a good event `G`, whose history stopped at the capped local stop of radius `r` is a
Borel function of its field.

Proof: the reference history stopped at the capped local stop `S` of its seed radius is field-determined
(`IsOptionalHullCoupling.isAEDeterminedBy_stoppedHistory`); before `S` the completed state is the driving state; the
change of measure `Q = Z·P` ((HL3) = (FS11.2), `Q ≪ P`) keeps the determination, and under `Q` the original driver with
the recoded field `h₀ = h + f − q` is a stopped seed coupling of the two-seed word (`isStoppedSeedCoupling_srcMeasure`);
Aux. lemma 54 (`stoppedSeedExtendStatement`) extends it to a full two-seed coupling of the field `h₀` whose stopped
history agrees with the original one; and `h = h₀ − (f − q)`. -/
theorem exists_twoSeed_stoppedGraph_of_reference {κ rL rR : ℝ} (hκ : 0 < κ) (hrL : -2 < rL) (hrR : -2 < rR)
    (href : Aux126Reference.{u} κ rL rR) :
    ∃ r : ℝ, 0 < r ∧ ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h ∧
      ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧
        (∀ ω ∈ G, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) W VL VR B ζ ω) ∧
        IsAEDeterminedBy P h (stoppedHistory (completedState W VL VR ζ) (capStop r G ζ W)) := by
  obtain ⟨nL, nR, xL, xR, ρL, ρR, hF, hxL0, hxR0, hxLn, hxRp, hρL, hρR, Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h,
    hC, -, hdet⟩ := href
  have hsL : Sec2.seedSum xL ρL = rL := by rw [Aux126.seedSum_eq hxL0 fun i hi => (hxLn i hi).ne, hρL]
  have hsR : Sec2.seedSum xR ρR = rR := by rw [Aux126.seedSum_eq hxR0 fun j hj => (hxRp j hj).ne', hρR]
  have hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR :=
    (Sec2.not_thr_iff_seedSum xL xR ρL ρR).2 ⟨by rw [hsL]; exact hrL, by rw [hsR]; exact hrR⟩
  have hLs : seedSumL xL ρL = rL := by rw [seedSumL_eq]; exact hsL
  have hRs : seedSumR xR ρR = rR := by rw [seedSumR_eq]; exact hsR
  have hr : IsSeedRadius xL xR (seedRadius xL xR) := isSeedRadius_seedRadius xL xR
  obtain ⟨G, hGm, hG0, hG⟩ := exists_goodEvent hC.1 hκ
  obtain ⟨G', hG'G, hG'm, hG'0, hG'⟩ := exists_goodNoise_subset hC.1 hκ hGm hG0
  have hG'p : ∀ ω ∈ G', IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω := fun ω hω => (hG' ω hω).1
  obtain ⟨hQ, -, hQP⟩ := srcMeasure_isEquiv hκ hC hF hr hseed
  have hc := isStoppedSeedCoupling_srcMeasure hκ hC hF hr hseed hG'm hG'0 hG'
  obtain ⟨C, mC, E, hE, 𝓕', W', VL', VR', B', ζ', hEQ, hC', G'', hG''m, hG''0, hG'', hagree⟩ :=
    stoppedSeedExtendStatement hκ xL xR ρL ρR (seedRadius xL xR) hF ⟨⟨0, hxL0⟩, ⟨0, hxR0⟩⟩ hr.1
      (by rw [hLs]; exact hrL) (by rw [hRs]; exact hrR) _ W VL VR _ _ hc
  rw [hLs, hRs] at hC' hG''
  -- the reference history stopped at `S`, field-determined, read through the driving state
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hdetS := hC.isAEDeterminedBy_stoppedHistory hκ hdet
    (isStoppingTime_capStop hX hG'm hG'0 hG'p (seedRadius xL xR)) (capStop_le (seedRadius xL xR))
  have hcd : stoppedHistory (completedState W VL VR ζ) (capStop (seedRadius xL xR) G' ζ W) =ᵐ[P]
      stoppedHistory (drivingState W VL VR) (capStop (seedRadius xL xR) G' ζ W) := by
    have hGP : ∀ᵐ ω ∂P, ω ∈ G' := ae_iff.2 hG'0
    filter_upwards [hGP] with ω hω
    have e1 := capStop_eq_localStopPath hG'p hF hr hseed hω
    refine Prod.ext rfl (funext fun q => ?_)
    have hlt : ((stopAt (capStop (seedRadius xL xR) G' ζ W) q ω : ℝ≥0) : ℝ≥0∞) < ζ ω :=
      lt_of_le_of_lt (stopAt_le _ q ω) e1.2
    simp only [stoppedHistory, completedState, hlt, ite_true]
  obtain ⟨g, hg, hZg⟩ := ((hdetS.congr_ae hcd).comp (measurable_twoSeedProj xL xR)).of_absolutelyContinuous hQP
  rw [← hEQ] at hZg
  have hZE := ae_of_ae_map measurable_fst.aemeasurable hZg
  -- the extension's stopped history is the same function of its field
  set c := SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens
    (recodeShift κ xL xR ρL ρR (seedRadius xL xR)) with hc_def
  refine ⟨seedRadius xL xR, hr.1, Ω × C, inferInstance, E, hE, 𝓕', W', VL', VR', B', ζ', _, hC', G'', hG''m, hG''0,
    hG'', fun x => g (x + -c), hg.comp (Coupling.measurable_add_distOnConst _), ?_⟩
  filter_upwards [hagree, hZE] with p h1 h2
  rw [← seedProj_eq_self (xL := xL) (xR := xR) ⟨0, hxL0⟩ ⟨0, hxR0⟩
    (stoppedHistory (completedState W' VL' VR' ζ') (capStop (seedRadius xL xR) G'' ζ' W') p), ← h1]
  rw [h2, recode_add_neg]

/-! ### The remaining step of Aux. lemma 126 and the reference of Lemma 7.25 -/

/-- **Named input: Aux. lemma 126 from one stopped graph to a determined coupling** (p. 401–402, "Finite-time
continuity by dilation of the driving law" and "Universal field determination": "Dilation of a whole two-seed pair acts
on its field by `H₀^{(a)}(z) = H₀(z/a)` … Dilating the reference extension constructed above therefore gives, for each
`R_n`, a full original two-seed coupling whose stopped history at `S_{R_n}` is determined by its whole field. …
**Aux.** lemma 50 therefore applies to every original two-seed coupling through the bounded stop `S_{R_n}` … Choose
these functions for the countable radii once and for all … this gives a Borel function recovering the entire driving
evolution in every original coupling"): if some full coupling of `SLE_κ(r_L; r_R)` with the original optional hull
specification has, for some radius `r > 0` and good event `G`, a field-determined history stopped at the capped local
stop of radius `r`, then some such coupling has a field-determined killed driving history. **Not proved in Lean**: it
needs the dilation of a coupling at the level of the field (the driving part is landed:
`Aux126.lemma725TraceStatement_of_driverReference`), Aux. lemma 50 at the bounded stops and the assembly over the radii
`2^n r`. -/
def StoppedToFullDeterminationStatement (κ rL rR : ℝ) : Prop :=
  (∃ r : ℝ, 0 < r ∧ ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h ∧
      ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧
        (∀ ω ∈ G, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) W VL VR B ζ ω) ∧
        IsAEDeterminedBy P h (stoppedHistory (completedState W VL VR ζ) (capStop r G ζ W))) →
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h ∧
        LP.IsFieldDeterminedHistory P h W VL VR ζ

/-- **Lemma 7.25's determination reference (`href725`) from the field-level reference with distant marks**
(`Lemma725ReferenceStatement`, the hypothesis of Aux. lemma 126) and the remaining step of Aux. lemma 126. -/
theorem lemma725DetReferenceStatement_of_ref (hRef : Lemma725ReferenceStatement.{u})
    (hS : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      StoppedToFullDeterminationStatement.{u} κ rL rR) :
    Aux50Hit.Lemma725DetReferenceStatement.{u} := fun κ hκ rL rR hL hL' hR hR' =>
  hS κ hκ rL rR hL hL' hR hR'
    (exists_twoSeed_stoppedGraph_of_reference (by linarith) hL hR (hRef κ hκ rL rR hL hL' hR hR'))

/-- **Lemma 7.25's determination reference (`href725`) from the `P`-side pockets with their distant marks**
(`Lemma725RefK2.PocketWordFieldStatement`: Aux. lemmas 119–125 in the fixed-exterior form of ruling R52) and the
remaining step of Aux. lemma 126. -/
theorem lemma725DetReferenceStatement_of_pocketWordField
    (h : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Lemma725RefK2.PocketWordFieldStatement.{u} κ rL rR)
    (hS : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      StoppedToFullDeterminationStatement.{u} κ rL rR) :
    Aux50Hit.Lemma725DetReferenceStatement.{u} :=
  lemma725DetReferenceStatement_of_ref (Lemma725RefK2.lemma725ReferenceStatement_of_pocketWordField h) hS

end Lemma725RefStop

end Sec7

end InteractingSLE
