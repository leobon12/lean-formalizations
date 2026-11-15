/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS4Win

/-!
# The validity events of the restarted word on the dyadic windows are events of the marks (`hAv`)

Packet PROVE-STAGED-S5 (the fact `hAv` of `StagedS4.ae_condExp_candFilt`). After the last switch (own time `τ`, image
capacity `S₀ = σ(τ)`), the restarted chart sends the remaining domain of the restarted word at the restarted time
`σ(u) − S₀` onto the remaining domain of the staged path at its own time `u` (`rChart_restart` and
`cfChart_inv_image_eq'`):

* **`s3Chart_image_eq`**: `s3Chart '' (ℍ ∖ K'_{σ(u) − S₀}) = ℍ ∖ (η((0, u]) ∪ K_cf)` (deterministic, good sample);
* **`isChartAvoid_s3_iff`**: hence the restarted validity event at `σ(u) − S₀` is the template's forward validity event
  at `u` (`isChartAvoid_capClock_iff'`);
* **`exists_candSigma_ae_eq_candWin_s4Av`** (`hAv`): on the window at a dyadic own time `Q`, the restarted validity
  event is the template's `cfAv Q`, which is almost surely a marks event (`exists_marks_ae_eq_avoid` and the transfer
  `exists_candSigma_ae_eq_of_cfGlueMarks`); the window itself is `hE`.

R48: only `h44` (R74) is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedS5

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref Word49 StagedS3 StagedS4
open Restart Exist.StagedLaw Exist.Staged
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces StagedRepLater
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Sec7.Lemma71C (capClock)
open WangWu.ChartConst (dyq dyqQ dyqQ_coe)

/-! ### The restarted remaining domain at an own time -/

section Sample

variable {Ω : Type*} {s : ℝ≥0} {Wj : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)} {τ : ℝ}
  {p : Ω × HistorySpace 0 0}

/-- **The restarted chart's remaining domain at the restarted time of an own time `u ≥ τ` before contact** is the
remaining domain of the staged path at `u`. -/
theorem s3Chart_image_eq (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (hp : p ∈ s3Alive s Wj E τ) {u : ℝ}
    (hu : u ∈ gPre s (fun _ => ⊤) Wj E p) (hτu : τ ≤ u) :
    (s3Chart s Wj E τ p).2.1 '' (H \ fwdHull (Ito.rpath fun r => s3W s Wj E τ r p)
        ((((capClock (gCurve s (fun _ => ⊤) Wj E p) u).toNNReal - s3Start s Wj E τ p : ℝ≥0) : ℝ))) =
      H \ (seedLine (fun _ => ⊤) Wj p.1 '' Ioc 0 u ∪ cfHullQ s p.2) := by
  set γ := gCurve s (fun _ => ⊤) Wj E p with hγdef
  set Pp := gPre s (fun _ => ⊤) Wj E p with hPdef
  have hγ : IsKilledArc γ Pp := isKilledArc_gCurve hEg p
  set S₀ := s3Start s Wj E τ p with hS₀def
  set r := (capClock γ u).toNNReal - S₀ with hrdef
  have hsumle : S₀ ≤ (capClock γ u).toNNReal := by
    rw [hS₀def, s3Start_of_alive hp]
    exact Real.toNNReal_le_toNNReal (hγ.strictMonoOn_capClock.monotoneOn hp.2 hu hτu)
  have hsum : S₀ + r = (capClock γ u).toNNReal := add_tsub_cancel_of_le hsumle
  have hr : ((S₀ + r : ℝ≥0) : WithTop ℝ≥0) < kLife γ Pp := by rw [hsum]; exact hγ.lt_kLife hu
  have hw' : ∀ v : ℝ≥0, ((S₀ + v : ℝ≥0) : WithTop ℝ≥0) < kLife γ Pp →
      s3W s Wj E τ v p = kW γ Pp (S₀ + v) - kW γ Pp S₀ := fun v hv =>
    Prop59Pieces.arcW_of_lt (Prop59Pieces.lt_arcζ_iff.2 ⟨mem_univ p, hv⟩)
  obtain ⟨himg, -⟩ := rChart_restart (isConformal_cfChart p.2) hγ hr hw' 0 0 (fun _ => 0)
  change (rChart (cfChart s p.2) γ Pp S₀).2.1 '' _ = _
  have himg' : (rChart (cfChart s p.2) γ Pp S₀).2.1 '' (H \ fwdHull (Ito.rpath fun r => s3W s Wj E τ r p) r) =
      (cfChart s p.2).2.1 '' (H \ fwdHull (kPath γ Pp) ((S₀ + r : ℝ≥0) : ℝ)) := himg
  rw [himg', hsum, ← cfChart_inv_image_eq' hEg hp.1 hu]
  rfl

/-- **The restarted validity event at the restarted time of an own time `u ≥ τ` before contact** is the avoidance of
the staged path up to `u` and of the counterflow hull. -/
theorem isChartAvoid_s3_iff (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (hp : p ∈ s3Alive s Wj E τ) {u : ℝ}
    (hu : u ∈ gPre s (fun _ => ⊤) Wj E p) (hτu : τ ≤ u) (φ : TestOn upperHalfPlaneOpens) :
    Sec7.Lemma71D.IsChartAvoid (fun r => s3W s Wj E τ r p) (s3ζ s Wj E τ p) (s3Chart s Wj E τ p) φ
        ((capClock (gCurve s (fun _ => ⊤) Wj E p) u).toNNReal - s3Start s Wj E τ p) ↔
      tsupport φ ⊆ H \ (seedLine (fun _ => ⊤) Wj p.1 '' Ioc 0 u ∪ cfHullQ s p.2) := by
  have hγ : IsKilledArc (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p) := isKilledArc_gCurve hEg p
  have hsumle : s3Start s Wj E τ p ≤ (capClock (gCurve s (fun _ => ⊤) Wj E p) u).toNNReal := by
    rw [s3Start_of_alive hp]
    exact Real.toNNReal_le_toNNReal (hγ.strictMonoOn_capClock.monotoneOn hp.2 hu hτu)
  have hlt : ((((capClock (gCurve s (fun _ => ⊤) Wj E p) u).toNNReal - s3Start s Wj E τ p : ℝ≥0) : ℝ≥0∞)) <
      s3ζ s Wj E τ p := by
    rw [lt_s3ζ_iff, add_tsub_cancel_of_le hsumle]
    exact hγ.lt_kLife hu
  unfold Sec7.Lemma71D.IsChartAvoid
  rw [s3Chart_image_eq hEg hp hu hτu]
  exact ⟨fun h => h.2, fun h => ⟨hlt, h⟩⟩

end Sample

/-! ### `hAv` -/

section Cand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

omit [StandardBorelSpace Ω] in
/-- On a window at the own time `Q`, the restarted validity event at `Q` is the template's forward validity event. -/
theorem candWin_inter_s4Av_eq (hhm : Measurable h) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} {s : ℝ≥0}
    (φ : TestOn upperHalfPlaneOpens) (r : ℝ≥0) (Q : ℚ) (hQ0 : (0 : ℝ) ≤ Q) :
    candWin x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s Q r ∩
        s4Av s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) (lastO ℓ t : ℝ) φ
          (Q : ℝ).toNNReal =
      candWin x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s Q r ∩
        cfAv s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) φ
          (Q : ℝ).toNNReal := by
  set Wc := candW x₀ h44 hκ hκ4 hb h ℓ t with hWc
  set Eg := candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s with hEgdef
  have hEg : ∀ p ∈ Eg, IsGood49 s (fun _ => ⊤) Wc p := fun p hp => isGood49_of_mem_glueGood p hp
  have hQQ : (((Q : ℝ).toNNReal : ℝ≥0) : ℝ) = Q := Real.coe_toNNReal _ hQ0
  ext p
  simp only [mem_inter_iff]
  refine and_congr_right fun hW => ?_
  have hW' := hW
  rw [candWin, mem_ofPred_eq] at hW'
  obtain ⟨halive, hlt, hQP, -⟩ := hW'
  have hτQ : (lastO ℓ t : ℝ) ≤ Q := by exact_mod_cast hlt.le
  have hav := isChartAvoid_s3_iff hEg halive hQP hτQ φ
  have hav' := isChartAvoid_capClock_iff' hEg halive.1 hQP φ
  simp only [s4Av, cfAv, s4R, mem_ofPred_eq, hQQ]
  constructor
  · rintro ⟨-, -, -, h⟩
    exact ⟨halive.1, hQP, hav'.2 (hav.1 h)⟩
  · rintro ⟨-, -, h⟩
    exact ⟨halive, by exact_mod_cast hlt, hQP, hav.2 (hav'.1 h)⟩

include hκ4 in
/-- **`hAv`: on the window at a dyadic own time, the restarted validity event is almost surely an event of the
marks.** -/
theorem exists_candSigma_ae_eq_candWin_s4Av (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) (φ : TestOn upperHalfPlaneOpens) (r : ℝ≥0) (n k : ℕ)
    (hq : lastO ℓ t < dyqQ n k) :
    ∃ B, MeasurableSet[candSigma x₀ h44 hκ hκ4 hb h us ℓ t (dyqQ n k) s] B ∧
      B =ᵐ[candMu x₀ (κ := κ) P h W ζ hG.1] (candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s (dyqQ n k) r ∩
        s4Av s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ) φ
          (dyq n k)) := by
  set Wc := candW x₀ h44 hκ hκ4 hb h ℓ t with hWc
  set Eg := candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s with hEgdef
  have hEg : ∀ p ∈ Eg, IsGood49 s (fun _ => ⊤) Wc p := fun p hp => isGood49_of_mem_glueGood p hp
  have hQpos : 0 < dyqQ n k := lt_of_le_of_lt (lastO_nonneg hv) hq
  have hQ0 : (0 : ℝ) ≤ (dyqQ n k : ℝ) := by exact_mod_cast hQpos.le
  have hdq : dyq n k = ((dyqQ n k : ℚ) : ℝ).toNNReal := by
    rw [dyqQ_coe, Real.toNNReal_coe]
  have hgood : ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1), p ∈ Eg ∧
      Aux50Hit.IsGoodPath Wc (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) p.1 :=
    (ae_good_cand x₀ h44 hκ hκ4 hb P h W ζ hG hcf ℓ t hv hs).mono fun p hp => ⟨hp.1, hp.2.1⟩
  obtain ⟨B₁, hB₁, hB₁e⟩ := exists_candMarks_ae_eq_candWin x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs (dyqQ n k) r
  rw [candMarks_of_lt x₀ h44 hκ hκ4 hb h hq] at hB₁
  obtain ⟨B', hB', hB'e⟩ := exists_marks_ae_eq_avoid (μ := candMu x₀ (κ := κ) P h W ζ hG.1) hQpos hEg hgood φ
  obtain ⟨B₂, hB₂, hB₂e⟩ := exists_candSigma_ae_eq_of_cfGlueMarks x₀ h44 hκ hκ4 hb P h W ζ hG us hv hq s hB'
  refine ⟨B₁ ∩ B₂, hB₁.inter hB₂, (hB₁e.inter (hB₂e.trans hB'e)).trans ?_⟩
  rw [hdq, candWin_inter_s4Av_eq x₀ h44 hκ hκ4 hb P h W ζ hG.1 φ r (dyqQ n k) hQ0]

end Cand

end InteractingSLE.Sec5.CrossCond.StagedS5
