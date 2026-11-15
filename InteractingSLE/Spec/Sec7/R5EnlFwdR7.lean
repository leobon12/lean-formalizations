/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5EnlFwd
import InteractingSLE.Spec.Sec7.R5EnlR7Walls
import InteractingSLE.Spec.Sec7.R5RefFamily
import InteractingSLE.Spec.Sec7.PocketTraversalMeasRand

/-!
# `hfwd` for the R.7 reference charts, and clause 4 of `R5ClausesOn` on the reference family

Packet PROVE-R5-ENLARGED (continued). R5-REFCHART's `i`-th reference chart (`R5Ref.refChart`) is the relative chart of
the pocket traversal at the random capacity `visitCap s` reached at the original time `s = rationalOriginalTime i`.
Its forward map is measurable for the reference record `refInfo s = σ(walls) ∨ 𝓕_s`:

* **window identity** (`stopTimeM_le_iff_visitCap`): when the counterflow visits the pocket at `s`,
  `T⁰(q) ≤ s ↔ q ≤ visitCap s`; and `visitCap s ≤ q` gives `s ≤ T⁰(q)` (`le_stopTimeM_of_visitCap_le`);
* **the transfer** (`htrans` of `R5Enl.measurable_indicator_fwd_relChart_rand`): a relative-prefix event at the fixed
  capacity `q`, cut to `{q ≤ visitCap s}` on the visit event, is the marked-stop event `{T⁰(q) ≤ s} ∩ M` there
  (Galmarino: `PocketStopMarked.isMarkedStop_stopTimeM`), an event of `σ(walls) ∨ 𝓕_s`;
* **`measurable_indicator_fwd_visitRef`**: `hfwd` on the reference window `refWindow` (a visit at `s`, or `s = 0`);
* **`r7HasOldChartIncrementLawOn_visit`**: R.5's conditioned increment law for the visit reference at any original
  time `s`, on every event inside the window with `visitCap s ≤ q` and `q` live, with `hfwd`, the reference event and
  every pathwise input discharged;
* **`r7HasOldChartIncrementLawOn_ref`**, **`r5ClausesOn_clause4_ref`**: clause 4 of `R5ClausesOn` for R5-REFCHART's
  family (`refEvent`, `refChart`, `F = refHull`) on an R.7 test.

Conditional helpers with distinct names; nothing here uses Theorem 1.2/1.3 or any `*_of_param` (R43, R48).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Enl

open WholeField PocketStopField PocketStopWalls PocketCoupling Lemma71C Lemma71I PocketCoord PocketJordan
  PocketMarks PocketWordAssembly PocketTraversal PocketAdapt PocketStop PocketStopWallsFin PocketStopMarked
  PocketWordPerQ PocketUnionPt R5Phase LocalSets

/-! ### The window identity at a visit -/

section Path

variable {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
  {A : Set Ω}

/-- **The window identity**: if the counterflow visits the pocket at the original time `s`, the left stop of `q` is
at most `s` iff `q` is at most the capacity reached at `s`. -/
theorem stopTimeM_le_iff_visitCap
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) {ω : Ω} (hω : ω ∈ A) {s : ℝ≥0}
    (hvisit : η ω s ∈ cfPocket (R ω) (L ω) r) (q : ℝ≥0) :
    stopTimeM A R L r η ψ q ω ≤ s ↔ q ≤ (visitCap R L r η ψ ω s).toNNReal := by
  obtain ⟨hP, hψ'⟩ := R5Ref.pocket_of_cfg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (η := η) (hcfg ω hω) (hψ ω hω)
  have hv := hP.mem_visitSet s.coe_nonneg hvisit
  obtain ⟨hpos, -⟩ := PocketStopSide.relCap_pos_lt_of_visit hP (hcfg ω hω).attach hψ' hv
  unfold visitCap
  rw [stopTimeM_le_iff hcfg hψ q hω s, Real.le_toNNReal_iff_coe_le hpos.le]
  constructor
  · rintro (⟨-, -, h⟩ | ⟨h, -⟩)
    · exact h
    · exact absurd h (not_le.2 hv.1.2)
  · exact fun h => Or.inl ⟨hv.1.1.le, hv.1.2, h⟩

/-- **After the capacity reached at a visit, the left stop is after the visit**: `visitCap s ≤ q` (`q` live) gives
`s ≤ T⁰(q)`. -/
theorem le_stopTimeM_of_visitCap_le
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) {ω : Ω} (hω : ω ∈ A) {s : ℝ≥0}
    (hvisit : η ω s ∈ cfPocket (R ω) (L ω) r) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω))
    (hle : (visitCap R L r η ψ ω s).toNNReal ≤ q) : (s : ℝ≥0∞) ≤ stopTimeM A R L r η ψ q ω := by
  obtain ⟨hP, hψ'⟩ := R5Ref.pocket_of_cfg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (η := η) (hcfg ω hω) (hψ ω hω)
  have hAC := (hcfg ω hω).attach
  have hv := hP.mem_visitSet s.coe_nonneg hvisit
  obtain ⟨hpos, hlive⟩ := PocketStopSide.relCap_pos_lt_of_visit hP hAC hψ' hv
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (travAll R L r η ψ ω) := by rwa [ENNReal.ofReal_coe_nnreal]
  have hT : stopTimeM A R L r η ψ q ω = stopTime0 R L r η ψ q ω := by
    unfold stopTimeM
    exact ite_eq_left ⟨hω, hq⟩
  rw [hT, stopTime0, ← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal (le_of_not_gt fun hlt => ?_)
  unfold visitCap at hle
  have hQq := (Real.toNNReal_le_iff_le_coe).1 hle
  have hm := ambTime0_mem_Ico hP hAC hψ' q.coe_nonneg hq'
  have h1 := (ambTime0_le_iff hP hAC hψ' q.coe_nonneg hq' hm).1 le_rfl
  have hTQ := PocketStopSide.ambTime0_relCap_of_visit hP hAC hψ' hv
  have h2 := R5Ref.relCap_lt_of_lt_ambTime0 hP hAC hψ' hpos.le hlive hm (by rw [hTQ]; exact hlt)
  linarith

end Path

/-! ### The reference window and its record -/

section Window

variable {Ω : Type*}

/-- **The reference window at the original time `s`**: `ω` in the test, and the counterflow visits the pocket at
`s`, or `s = 0` (the pair events `R5Ref.refEvent` lie in it at every capacity). -/
def refWindow (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (s : ℝ≥0) : Set Ω :=
  {ω | ω ∈ A ∧ (η ω s ∈ cfPocket (R ω) (L ω) r ∨ s = 0)}

theorem refWindow_of_ne {A : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {s : ℝ≥0} (hs : s ≠ 0) :
    refWindow A R L r η s = {ω | ω ∈ A ∧ η ω s ∈ cfPocket (R ω) (L ω) r} := by
  ext ω
  simp only [refWindow, mem_ofPred_eq, hs, or_false]

theorem refWindow_zero (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) :
    refWindow A R L r η 0 = A := by
  ext ω
  simp only [refWindow, mem_ofPred_eq, or_true, and_true]

variable {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {η : Ω → ℝ → ℂ}
  {ψ : Ω → ℂ → ℂ} {A : Set Ω} {c : Ω → Chart}

/-- **The reference chart on the window** (bounded change pocket): its capacity is live, it is conformal, and its
domain is the reference complement `ℍ ∖ liveExt(K̃_s, 0)`. -/
theorem refWindow_spec
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hc : ∀ ω ∈ A, (c ω).IsConformal) (hcdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (hceq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (s : ℝ≥0) :
    ∀ ω ∈ refWindow A R L r η s,
      ((visitCap R L r η ψ ω s).toNNReal : ℝ≥0∞) < capLife (travAll R L r η ψ ω) ∧
      (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).IsConformal ∧
      ((relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).dom : Set ℂ) =
        H \ liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0 ω := by
  rintro ω ⟨hω, hv | hz⟩
  · have hHull : regHull W' ζ' s ω = fwdHull (fun s : ℝ => W' s.toNNReal ω) s :=
      regHull_eq (continuous_nnreal_of_continuous_real (hcfg ω hω).continuous_W) (hζA ω hω) s
    obtain ⟨-, hlive, -⟩ := visitCap_spec (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω (hcfg ω hω) (hψ ω hω)
      (hc ω hω) (hcdom ω hω) (hceq ω hω) s.coe_nonneg hv
    obtain ⟨hconf, -, hdom⟩ := reference_chart_at_visit (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω (hcfg ω hω)
      (hψ ω hω) (hc ω hω) (hcdom ω hω) (hceq ω hω) (F := regHull W' ζ' s) hv hHull hlive le_rfl
    exact ⟨hlive, hconf, hdom⟩
  · subst hz
    have hγ := ((hcfg ω hω).isDrivenCurve (hψ ω hω)).1
    have h0 : (visitCap R L r η ψ ω ((0 : ℝ≥0) : ℝ)).toNNReal = 0 := by
      rw [NNReal.coe_zero, R5Ref.visitCap_zero (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hω) (hψ ω hω),
        Real.toNNReal_zero]
    have hCH : cfPocket (R ω) (L ω) r ⊆ H := by
      rw [← hcdom ω hω, (hc ω hω).coe_dom]
      exact (hc ω hω).2.1.image_subset
    have hlive : ((0 : ℝ≥0) : ℝ≥0∞) < capLife (travAll R L r η ψ ω) := by
      rw [ENNReal.coe_zero]
      exact PocketPhaseMeans.capLife_pos hγ
    have hHull : regHull W' ζ' 0 ω = ∅ := by
      rw [regHull_eq (continuous_nnreal_of_continuous_real (hcfg ω hω).continuous_W) (hζA ω hω), NNReal.coe_zero,
        QuantumZipper.RS.fwdHull_zero_eq_empty (hcfg ω hω).continuous_W]
    rw [h0]
    refine ⟨hlive, PocketStopSide.isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ) hγ hlive
      (hc ω hω), ?_⟩
    rw [R5Ref.relChart_zero_dom (c := c) (γ := travAll R L r η ψ) hγ, hcdom ω hω, H_diff_liveExt_zero hω hγ, hHull,
      sdiff_empty]
    exact (inter_eq_left.2 hCH).symm

variable {nL nR : ℕ} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {G : Set Ω}

/-- **The reference window is an event of the reference record** `σ(walls) ∨ 𝓕_s`: on the test the counterflow is
the trace of the adapted driver (`PocketStopMarked.adTrace`). -/
theorem measurableSet_refWindow (hX : IsMeasurableKilledDriving W' VL VR ζ')
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω))
    (hGm : MeasurableSet[wallsSigma P R L] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (s : ℝ≥0) :
    MeasurableSet[refInfo P hX R L s] (refWindow A R L r η s) := by
  have h𝓦s : wallsSigma P R L ≤ refInfo P hX R L s := wallsSigma_le_refInfo hX R L s
  by_cases hs : s = 0
  · subst hs
    rw [refWindow_zero]
    exact h𝓦s _ hA
  rw [refWindow_of_ne hs]
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ' W' :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  have e : {ω | ω ∈ A ∧ η ω s ∈ cfPocket (R ω) (L ω) r} =
      {ω | ω ∈ A ∧ adTrace W' ζ' ω s ∈ cfPocket (R ω) (L ω) r} := by
    ext ω
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨hω, h⟩
      exact ⟨hω, by rw [adTrace_eq_of_mem hcfg hζA hω s.coe_nonneg]; exact h⟩
    · rintro ⟨hω, h⟩
      exact ⟨hω, by rw [← adTrace_eq_of_mem hcfg hζA hω s.coe_nonneg]; exact h⟩
  rw [e]
  exact measurableSet_visit (mΩ := refInfo P hX R L s) (e := adTrace W' ζ') h𝓦s
    (measurable_right_wallsSigma hRc hLc) (measurable_left_wallsSigma hRc hLc) hGm hG (h𝓦s _ hA) hAG
    (measurable_adTrace_sup (X := fullHist ![R, L]) hWad le_rfl)

end Window

/-! ### `hfwd` for the reference chart -/

section Fwd

variable {Ω : Type*} {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {h'' : Ω → DistOn upperHalfPlaneOpens}
  {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
  {G A : Set Ω} {c : Ω → Chart}

/-- **The base chart and the active complements of an R.7 test are measurable** (the fixed-capacity inputs `hcfwd`,
`hKm` of `measurable_indicator_fwd_relChart_rand`), from the walls' data and the counterflow's measurability. -/
theorem r7_fixed_inputs (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω))
    (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hGm : MeasurableSet[wallsSigma P R L] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hψm : @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ)
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    (hc : ∀ ω ∈ A, (c ω).IsConformal) (hcdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (hceq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) :
    (∀ z, Measurable[wallsSigma P R L] ((A ∩ {ω | z ∈ (c ω).dom}).indicator fun ω => (c ω).1 z)) ∧
      ∀ q : ℝ≥0, Measurable[locPrefixSigma (wallsSigma P R L) A (travAll R L r η ψ) q, hittingSigma]
        (activeCompl A (travAll R L r η ψ) c q) := by
  classical
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have h𝓦 : wallsSigma P R L ≤ mΩ := wallsSigma_le hRm hLm
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω =>
    ((hcfg ω hω).isDrivenCurve (hψ ω hω)).1
  have hCm : ∀ z, MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm' hLm' hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[wallsSigma P R L]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω =>
      ⟨subset_closure hω.2, fun h => (hG ω (hAG hω.1)).cfPt_openPt_notMem (h ▸ hω.2)⟩
  refine ⟨fun z => ?_, fun q => ?_⟩
  · have e : ((A ∩ {ω | z ∈ (c ω).dom}).indicator fun ω => (c ω).1 z) =
        {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z := by
      funext ω
      by_cases hω : ω ∈ A
      · have hmem : z ∈ (c ω).dom ↔ z ∈ cfPocket (R ω) (L ω) r := by
          rw [← SetLike.mem_coe, hcdom ω hω]
        by_cases hz : z ∈ cfPocket (R ω) (L ω) r
        · rw [indicator_of_mem (show ω ∈ A ∩ {ω | z ∈ (c ω).dom} from ⟨hω, hmem.2 hz⟩),
            indicator_of_mem (show ω ∈ {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} from ⟨hω, hz⟩), hceq ω hω hz]
        · rw [indicator_of_notMem (show ω ∉ A ∩ {ω | z ∈ (c ω).dom} from fun h => hz (hmem.1 h.2)),
            indicator_of_notMem (show ω ∉ {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} from fun h => hz h.2)]
      · rw [indicator_of_notMem (show ω ∉ A ∩ {ω | z ∈ (c ω).dom} from fun h => hω h.1),
          indicator_of_notMem (show ω ∉ {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} from fun h => hω h.1)]
    rw [e]
    exact hψm' z
  · have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travAll R L r η ψ ω u :=
      PocketTraversalMeasRand.traversalMeasStatement_of_measurable (G := A) h𝓦 hRm' hLm' hA hcfg hηm A
        (h𝓦 _ hA) subset_rfl ψ hψ (fun A' hA' hA'A p hp hpC => hψm A' hA' (hA'A.trans hAG) p hp hpC)
    have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω => by
      rw [← hcdom ω hω]
      exact (c ω).dom.isOpen
    have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω => by
      rw [← hcdom ω hω, (hc ω hω).coe_dom]
      exact (hc ω hω).2.1.image_subset
    exact PhaseCont.measurable_activeCompl_locPrefixSigma h𝓦 hA hγ hγm hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1)
      hCm hψm' (fun U hUo hUH => Lemma725RefMarks.measurableSet_subset_cfPocket hRm' hLm' hGm hG hA hAG hUo hUH)
      (fun ω hω => ⟨hc ω hω, hcdom ω hω, hceq ω hω⟩) q

/-- **`hfwd` for the reference chart at the original time `s`** (bounded change pocket): on the reference window,
the forward map of the relative chart at the random capacity `visitCap s` is measurable for the reference record
`σ(walls) ∨ 𝓕_s`. -/
theorem measurable_indicator_fwd_visitRef [IsProbabilityMeasure P] (hX : IsMeasurableKilledDriving W' VL VR ζ')
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'') (hκ' : 0 < κ')
    (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤) (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω))
    (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hGm : MeasurableSet[wallsSigma P R L] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ) (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    (hc : ∀ ω ∈ A, (c ω).IsConformal) (hcdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (hceq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (s : ℝ≥0) (z : ℂ) :
    Measurable[refInfo P hX R L s] ((refWindow A R L r η s ∩
        {ω | z ∈ (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).dom}).indicator
      fun ω => (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).1 z) := by
  classical
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have h𝓦s : wallsSigma P R L ≤ refInfo P hX R L s := wallsSigma_le_refInfo hX R L s
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω =>
    ((hcfg ω hω).isDrivenCurve (hψ ω hω)).1
  obtain ⟨hcfwd, hKm⟩ := r7_fixed_inputs hRc hLc hRm hLm hGm hG hA hAG hcfg hψ hψm hηm hc hcdom hceq
  have hspec := refWindow_spec (ζ' := ζ') hcfg hζA hψ hc hcdom hceq s
  by_cases hs : s = 0
  · -- the zero reference: the relative chart at capacity `0`, measurable for the walls
    subst hs
    have hrel : ∀ ω ∈ A, relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω ((0 : ℝ≥0) : ℝ)).toNNReal ω =
        relChart c (travAll R L r η ψ) 0 ω := fun ω hω => by
      rw [NNReal.coe_zero, R5Ref.visitCap_zero (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hω) (hψ ω hω),
        Real.toNNReal_zero]
    have hfix := measurable_indicator_fwd_relChart_fixed hγ hc hcfwd 0 (hKm 0) z
    rw [PocketStopSide.locPrefixSigma_zero_of_driven hA hγ] at hfix
    have eS : refWindow A R L r η 0 ∩
        {ω | z ∈ (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω ((0 : ℝ≥0) : ℝ)).toNNReal ω).dom} =
        {ω | ω ∈ A ∧ ((0 : ℝ≥0) : ℝ≥0∞) < capLife (travAll R L r η ψ ω)} ∩
          {ω | z ∈ (relChart c (travAll R L r η ψ) 0 ω).dom} := by
      ext ω
      simp only [refWindow_zero, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨hω, hz⟩
        refine ⟨⟨hω, ?_⟩, by rwa [hrel ω hω] at hz⟩
        rw [ENNReal.coe_zero]
        exact PocketPhaseMeans.capLife_pos (hγ ω hω)
      · rintro ⟨⟨hω, -⟩, hz⟩
        exact ⟨hω, by rwa [hrel ω hω]⟩
    rw [eS, indicator_congr (g := fun ω => (relChart c (travAll R L r η ψ) 0 ω).1 z)
      fun ω hω => by simp only [hrel ω hω.1.1]]
    exact hfix.2.mono h𝓦s le_rfl
  -- a visit reference: the random capacity `visitCap s`
  have hG₀ := measurableSet_refWindow (P := P) hX hRc hLc hGm hG hA hAG hcfg hζA s
  have hG₀A : refWindow A R L r η s ⊆ A := fun ω hω => hω.1
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ' W' :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  have htrans : ∀ (q : ℝ≥0) (M : Set Ω),
      MeasurableSet[locPrefixSigma (wallsSigma P R L) A (travAll R L r η ψ) q] M →
      MeasurableSet[refInfo P hX R L s]
        (refWindow A R L r η s ∩ {ω | q ≤ (visitCap R L r η ψ ω s).toNNReal} ∩ M) := by
    intro q M hM
    have hGpre := isMarkedStop_stopTimeM (wallsSigma_le_drivingFiltration hX R L) hWad hRm' hLm' hGm hG hA hAG
      hcfg hζA hψ hψm q
    have h1 := measurableSet_le_inter_of_isMarkedStop hGpre s hM
    have e : refWindow A R L r η s ∩ {ω | q ≤ (visitCap R L r η ψ ω s).toNNReal} ∩ M =
        refWindow A R L r η s ∩ ({ω | stopTimeM A R L r η ψ q ω ≤ (s : ℝ≥0∞)} ∩ M) := by
      rw [refWindow_of_ne hs]
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨hω, hq⟩, hMω⟩
        exact ⟨hω, (stopTimeM_le_iff_visitCap hcfg hψ hω.1 hω.2 q).2 hq, hMω⟩
      · rintro ⟨hω, hq, hMω⟩
        exact ⟨⟨hω, (stopTimeM_le_iff_visitCap hcfg hψ hω.1 hω.2 q).1 hq⟩, hMω⟩
    rw [e]
    exact hG₀.inter h1
  have hBs := measurable_refSet_refInfo hC hκ' hX hζ hRc hLc hGm hG hA hAG hγ s
  have hdom := measurableSet_inter_mem_dom_of_hitting (ℋ₀ := refInfo P hX R L s) hG₀ hBs
    (old := fun ω => relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω)
    (fun ω hω => (hspec ω hω).2.2)
    (fun ω hω => by rw [← (hspec ω hω).2.2]; exact (relChart _ _ _ ω).dom.isOpen) z
  exact measurable_indicator_fwd_relChart_rand (ℳ := refInfo P hX R L s) hγ hc hcfwd hKm hG₀ hG₀A
    (fun ω hω => (hspec ω hω).1) htrans z hdom

end Fwd

/-! ### Clause 4 of `R5ClausesOn` on the reference family -/

section Clause4

open Wire.Current.SideTest (rationalOriginalTime)

variable {Ω : Type*} {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c₀ : ℝ} {u₀ : ℂ → ℝ}
  {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {u₀' : ℂ → ℝ} {R L : Ω → ℝ≥0 → ℂ}

/-- **R.5's enlarged-stop increment law for the visit reference at the original time `s`** (bounded change pocket;
clause 4 of `R5ClausesOn`): the R.7 assembly `PocketStopMarked.r7HasOldChartIncrementLawOn` with the reference event
(`refWindow`), the reference chart's facts and its forward-map measurability (`measurable_indicator_fwd_visitRef`)
discharged, on every event `M` on which `ω` is in the test, `q` is live, `s` is a visit or `0`, and the capacity
reached at `s` is at most `q`; the order `s ≤ T⁰(q)` on `M` from `le_stopTimeM_of_visitCap_le`. -/
theorem r7HasOldChartIncrementLawOn_visit
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c₀ (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'') (hκ' : 0 < κ')
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {G A : Set Ω}
    (hGm : MeasurableSet[wallsSigma P R L] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ) (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    {c : Ω → Chart} (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hcdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (hceq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (q s : ℝ≥0) {M : Set Ω}
    (hM : ∀ ω ∈ M, ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) ∧
      (η ω s ∈ cfPocket (R ω) (L ω) r ∨ s = 0) ∧ (visitCap R L r η ψ ω s).toNNReal ≤ q) :
    ∀ gOld : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (liveExt A (travAll R L r η ψ)
        (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0) (centredField h'' u₀') P gOld →
      ∀ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (activeCompl A (travAll R L r η ψ) c q) (centredField h'' u₀') P g →
        HasOldChartIncrementLawOn P M (fun ω => relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω)
          (relChart c (travAll R L r η ψ) q) gOld g := by
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω =>
    ((hcfg ω hω).isDrivenCurve (hψ ω hω)).1
  have hspec := refWindow_spec (ζ' := ζ') hcfg hζA hψ hc hcdom hceq s
  have hle : refInfo P hX R L s ≤ germSigma (liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
      (regHull W' ζ' s) 0) (centredField h'' u₀') ⊔ locPrefixSigma (refInfo P hX R L s) A (travAll R L r η ψ) 0 :=
    le_sup_left.trans le_sup_right
  refine r7HasOldChartIncrementLawOn hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR
    hlocL hGm hG hA hAG hcfg hζA hψ hψm hγ hc hcdom hceq q s (G' := refWindow A R L r η s)
    (hle _ (measurableSet_refWindow hX hRc hLc hGm hG hA hAG hcfg hζA s))
    (old := fun ω => relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω)
    (fun ω hω => (hspec ω hω).2.1)
    (fun z => (measurable_indicator_fwd_visitRef hX hC hκ' hζ hRc hLc hRm hLm hGm hG hA hAG hcfg hζA hψ hψm hηm hc
      hcdom hceq s z).mono hle le_rfl)
    (fun ω hω => (hspec ω hω).2.2) (fun ω hω => ⟨(hM ω hω).1, (hM ω hω).2.2.1⟩) (fun ω hω => ?_)
    (fun ω hω => ⟨(hM ω hω).1, (hM ω hω).2.1⟩)
  obtain ⟨hω, hq, hv | hz, hQ⟩ := hM ω hω
  · exact le_stopTimeM_of_visitCap_le hcfg hψ hω hv hq hQ
  · rw [hz, ENNReal.coe_zero]
    exact zero_le

/-- **R.5's enlarged-stop increment law for R5-REFCHART's `i`-th reference** (bounded change pocket; clause 4 of
`R5ClausesOn` with `M = R5Ref.refEvent`, `old = R5Ref.refChart`, `F = refHull`): `r7HasOldChartIncrementLawOn_visit`
at `s = rationalOriginalTime i`. -/
theorem r7HasOldChartIncrementLawOn_ref
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c₀ (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'') (hκ' : 0 < κ')
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {G A : Set Ω}
    (hGm : MeasurableSet[wallsSigma P R L] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ) (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    {c : Ω → Chart} (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hcdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (hceq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (q : ℝ≥0) (i : ℕ) :
    ∀ gOld : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (liveExt A (travAll R L r η ψ)
        (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0) (centredField h'' u₀') P gOld →
      ∀ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (activeCompl A (travAll R L r η ψ) c q) (centredField h'' u₀') P g →
        HasOldChartIncrementLawOn P
          (R5Ref.refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i)
          (R5Ref.refChart c R L r η ψ i) (relChart c (travAll R L r η ψ) q) gOld g :=
  r7HasOldChartIncrementLawOn_visit hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL
    hGm hG hA hAG hcfg hζA hψ hψm hηm hc hcdom hceq q (rationalOriginalTime i)
    fun _ hω => ⟨hω.1, hω.2.1, hω.2.2.1, hω.2.2.2.1⟩

/-- **Clause 4 of `R5ClausesOn` for R5-REFCHART's reference family** (bounded change pocket), in the clause's own
form: for local-set means of every reference and of the active complement, the conditioned increment law on every
pair event `R5Ref.refEvent … q i` with the reference chart `R5Ref.refChart … i`. -/
theorem r5ClausesOn_clause4_ref
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c₀ (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'') (hκ' : 0 < κ')
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {G A : Set Ω}
    (hGm : MeasurableSet[wallsSigma P R L] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ) (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    {c : Ω → Chart} (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hcdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (hceq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (q : ℝ≥0) :
    ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0)
        (centredField h'' u₀') P (gB i)) →
      ∀ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (activeCompl A (travAll R L r η ψ) c q) (centredField h'' u₀') P g →
        ∀ i, HasOldChartIncrementLawOn P
          (R5Ref.refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i)
          (R5Ref.refChart c R L r η ψ i) (relChart c (travAll R L r η ψ) q) (gB i) g :=
  fun gB hgB g hg i => r7HasOldChartIncrementLawOn_ref hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm
    hdetR hdetL hlocR hlocL hGm hG hA hAG hcfg hζA hψ hψm hηm hc hcdom hceq q i (gB i) (hgB i) g hg

end Clause4

end InteractingSLE.Sec7.R5Enl
