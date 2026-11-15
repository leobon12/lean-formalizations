/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS4Good

/-!
# The windows of the candidate's Galmarino filtration are events of the marks

Packet PROVE-STAGED-S4 (the facts `hE` and `hK` of `ae_condExp_cand_galFilt`). On good glued samples, the window
`candWin q r` (alive, `q` before contact, `S₀ + r < σ(q)`) intersected with `{u before contact, S₀ + r < σ(u)}` for a
rational `u ≤ q` is the preimage under Word49's stopped data `stopD (candW) ∅ ∅ ⊤ q s` of a Borel set (the pre-contact
events and capacity clocks at the rational times `τ = lastO`, `u`, `q` of the good stopped data,
`measurableSet_mem_PcD`, `measurable_indicator_capClock_gammaD`), hence almost surely an event of DEPTH's σ-algebra
(`exists_candSigma_ae_eq_stopD`):

* **`exists_candSigma_ae_eq_candWin_inter`** (general rational `u ≤ q`);
* **`exists_candMarks_ae_eq_candWin`** (`hE`, `u = q`);
* **`exists_candSigma_ae_eq_candWin_left`** (`hK`, `u = k/2ⁿ`).

R48: only `h44` (R74) is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedS4

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref Word49 StagedS3
open Restart Exist.StagedLaw Exist.Staged
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces StagedRepLater
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Sec7.Lemma71C (capClock)
open WangWu.ChartConst (dyq dyqQ dyqQ_coe)

/-! ### Capacities of the image curve read from stopped data -/

section Stop

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)} {s : ℝ≥0} {t : ℚ}
  {p : Ω × HistorySpace 0 0}

theorem capClock_gCurve_stopD (hp : p ∈ E)
    (hg : Aux50Hit.IsGoodPath W (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) p.1)
    {u : ℝ} (hu : u ≤ t) :
    capClock (gCurve s (fun _ => ⊤) W E p) u =
      capClock (gammaD s (stopD W (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
        (fun _ => ⊤) t s p)) u :=
  WangWu.capClock_congr fun _ hv => (gammaD_stopD hp hg (hv.2.trans hu)).symm

end Stop

/-! ### The windows -/

section Cand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

include hκ4 in
/-- **A window intersected with a pre-contact capacity event at a rational `u ≤ q` is almost surely an event of
DEPTH's σ-algebra.** -/
theorem exists_candSigma_ae_eq_candWin_inter (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) {q u : ℚ} (hq : lastO ℓ t < q) (hu0 : (0 : ℝ) ≤ u) (huq : u ≤ q)
    (r : ℝ≥0) :
    ∃ B, MeasurableSet[candSigma x₀ h44 hκ hκ4 hb h us ℓ t q s] B ∧
      B =ᵐ[candMu x₀ (κ := κ) P h W ζ hG.1] (candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s q r ∩
        {p | (u : ℝ) ∈ gPre s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t)
            (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) p ∧
          ((s3Start s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
            (lastO ℓ t : ℝ) p + r : ℝ≥0) : ℝ) < capClock (gCurve s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t)
              (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) p) u}) := by
  set Wc := candW x₀ h44 hκ hκ4 hb h ℓ t with hWc
  set Eg := candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s with hEgdef
  set τ : ℚ := lastO ℓ t with hτ
  have hτ0 : (0 : ℝ) ≤ τ := by exact_mod_cast lastO_nonneg hv
  have hτq : (τ : ℝ) ≤ q := by exact_mod_cast hq.le
  have hq0 : (0 : ℝ) ≤ q := hτ0.trans hτq
  have hqpos : 0 < q := lt_of_le_of_lt (lastO_nonneg hv) hq
  have huq' : (u : ℝ) ≤ q := by exact_mod_cast huq
  have hEg : ∀ p ∈ Eg, IsGood49 s (fun _ => ⊤) Wc p := fun p hp => isGood49_of_mem_glueGood p hp
  -- the Borel set of good stopped data
  set A : ℚ → Set {y : Y49 0 0 // IsGoodD s q y} := fun v => {x | (v : ℝ) ∈ PcD s x.1} with hA
  set c : ℚ → {y : Y49 0 0 // IsGoodD s q y} → ℝ := fun v => (A v).indicator fun x => capClock (gammaD s x.1) v
    with hcdef
  have hcm : ∀ v : ℚ, (0 : ℝ) ≤ v → (v : ℝ) ≤ q → Measurable (c v) := fun v hv0 hvq =>
    measurable_indicator_capClock_gammaD v hv0 hvq
  have hAm : ∀ v : ℚ, (0 : ℝ) ≤ v → (v : ℝ) ≤ q → MeasurableSet (A v) := fun v hv0 hvq =>
    measurableSet_mem_PcD v hv0 hvq
  set S : Set {y : Y49 0 0 // IsGoodD s q y} := A τ ∩ A q ∩ A u ∩
    {x | (((c τ x).toNNReal + r : ℝ≥0) : ℝ) < c q x} ∩ {x | (((c τ x).toNNReal + r : ℝ≥0) : ℝ) < c u x} with hS
  have hL : Measurable fun x => (((c τ x).toNNReal + r : ℝ≥0) : ℝ) :=
    measurable_coe_nnreal_real.comp ((measurable_real_toNNReal.comp (hcm τ hτ0 hτq)).add_const r)
  have hSm : MeasurableSet S :=
    ((((hAm τ hτ0 hτq).inter (hAm q hq0 le_rfl)).inter (hAm u hu0 huq')).inter
      (measurableSet_lt hL (hcm q hq0 le_rfl))).inter (measurableSet_lt hL (hcm u hu0 huq'))
  obtain ⟨C, hC, hCS⟩ := exists_measurableSet_of_subtypeD hSm
  obtain ⟨B, hB, hBe⟩ := exists_candSigma_ae_eq_stopD x₀ h44 hκ hκ4 hb P h W ζ hG us hv hq s hC
  refine ⟨B, hB, hBe.trans ?_⟩
  filter_upwards [ae_good_cand x₀ h44 hκ hκ4 hb P h W ζ hG hcf ℓ t hv hs] with p hpg
  obtain ⟨hpE, hg, _⟩ := hpg
  set y := stopD Wc (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) q s p
    with hy
  have hyg : IsGoodD s q y := isGoodD_stopD hqpos hEg hpE hg
  have hmem : ∀ v : ℚ, (v : ℝ) ≤ q → ((v : ℝ) ∈ gPre s (fun _ => ⊤) Wc Eg p ↔ (v : ℝ) ∈ PcD s y) := fun v hvq =>
    (mem_PcD_stopD_iff hpE hg hvq).symm
  have hcap : ∀ v : ℚ, (v : ℝ) ≤ q → (v : ℝ) ∈ gPre s (fun _ => ⊤) Wc Eg p →
      c v ⟨y, hyg⟩ = capClock (gCurve s (fun _ => ⊤) Wc Eg p) v := fun v hvq hv => by
    rw [hcdef]
    simp only
    rw [indicator_of_mem (show (⟨y, hyg⟩ : {y : Y49 0 0 // IsGoodD s q y}) ∈ A v from (hmem v hvq).1 hv),
      capClock_gCurve_stopD hpE hg hvq]
  have hiff := hCS ⟨y, hyg⟩
  show (p ∈ stopD Wc _ _ _ q s ⁻¹' C) = (p ∈ _)
  rw [mem_preimage, ← hy, eq_iff_iff, ← hiff]
  constructor
  · rintro ⟨⟨⟨⟨hτA, hqA⟩, huA⟩, h1⟩, h2⟩
    have hτP := (hmem τ hτq).2 hτA
    have hqP := (hmem q le_rfl).2 hqA
    have huP := (hmem u huq').2 huA
    have halive : p ∈ s3Alive s Wc Eg (τ : ℝ) := ⟨hpE, hτP⟩
    have hS0 : s3Start s Wc Eg (τ : ℝ) p = (c τ ⟨y, hyg⟩).toNNReal := by
      rw [s3Start_of_alive halive, hcap τ hτq hτP]
    have h1' : (((c τ ⟨y, hyg⟩).toNNReal + r : ℝ≥0) : ℝ) < c q ⟨y, hyg⟩ := h1
    have h2' : (((c τ ⟨y, hyg⟩).toNNReal + r : ℝ≥0) : ℝ) < c u ⟨y, hyg⟩ := h2
    rw [hcap q le_rfl hqP, ← hS0] at h1'
    rw [hcap u huq' huP, ← hS0] at h2'
    exact ⟨⟨halive, hq, hqP, h1'⟩, huP, h2'⟩
  · rintro ⟨⟨halive, -, hqP, h1⟩, huP, h2⟩
    have hτA := (hmem τ hτq).1 halive.2
    have hS0 : s3Start s Wc Eg (τ : ℝ) p = (c τ ⟨y, hyg⟩).toNNReal := by
      rw [s3Start_of_alive halive, hcap τ hτq halive.2]
    rw [hS0] at h1 h2
    refine ⟨⟨⟨⟨hτA, (hmem q le_rfl).1 hqP⟩, (hmem u huq').1 huP⟩, ?_⟩, ?_⟩
    · show (((c τ ⟨y, hyg⟩).toNNReal + r : ℝ≥0) : ℝ) < c q ⟨y, hyg⟩
      rw [hcap q le_rfl hqP]; exact h1
    · show (((c τ ⟨y, hyg⟩).toNNReal + r : ℝ≥0) : ℝ) < c u ⟨y, hyg⟩
      rw [hcap u huq' huP]; exact h2

include hκ4 in
/-- **`hE`: every window is almost surely an event of the marks.** -/
theorem exists_candMarks_ae_eq_candWin (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) (q : ℚ) (r : ℝ≥0) :
    ∃ B, MeasurableSet[candMarks x₀ h44 hκ hκ4 hb h us ℓ t s q] B ∧
      B =ᵐ[candMu x₀ (κ := κ) P h W ζ hG.1] candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s q r := by
  classical
  by_cases hq : lastO ℓ t < q
  · rw [candMarks_of_lt x₀ h44 hκ hκ4 hb h hq]
    have hq0 : (0 : ℝ) ≤ q := by exact_mod_cast (lastO_nonneg hv).trans hq.le
    obtain ⟨B, hB, hBe⟩ := exists_candSigma_ae_eq_candWin_inter x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs hq hq0
      le_rfl r
    refine ⟨B, hB, hBe.trans (Eventually.of_forall fun p => ?_)⟩
    simp only [eq_iff_iff, mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun h => h.1, fun h => ⟨h, h.2.2.1, h.2.2.2⟩⟩
  · refine ⟨∅, ?_, ?_⟩
    · rw [candMarks, ite_eq_right_of_eq_false _ _ (eq_false hq)]
      exact @MeasurableSet.empty _ ⊥
    · have he : candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s q r = ∅ :=
        eq_empty_of_forall_notMem fun p hp => hq hp.2.1
      rw [he]

include hκ4 in
/-- **`hK`: on a window at a dyadic own time, the left-endpoint event is almost surely an event of DEPTH's
σ-algebra.** -/
theorem exists_candSigma_ae_eq_candWin_left
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) (r : ℝ≥0) (n k : ℕ) (hq : lastO ℓ t < dyqQ n k) :
    ∃ B, MeasurableSet[candSigma x₀ h44 hκ hκ4 hb h us ℓ t (dyqQ n k) s] B ∧
      B =ᵐ[candMu x₀ (κ := κ) P h W ζ hG.1] (candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s (dyqQ n k) r ∩
        {p | (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) ∈ gPre s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t)
            (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) p ∧
          ((s3Start s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
            (lastO ℓ t : ℝ) p + r : ℝ≥0) : ℝ) < capClock (gCurve s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t)
              (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) p) (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ)}) := by
  have hcast : (((k : ℚ) / 2 ^ n : ℚ) : ℝ) = (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) := by push_cast; ring
  have hu0 : (0 : ℝ) ≤ (((k : ℚ) / 2 ^ n : ℚ) : ℝ) := by rw [hcast]; exact NNReal.coe_nonneg _
  have huq : ((k : ℚ) / 2 ^ n : ℚ) ≤ dyqQ n k := by
    rw [dyqQ]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  obtain ⟨B, hB, hBe⟩ := exists_candSigma_ae_eq_candWin_inter x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs hq hu0 huq r
  refine ⟨B, hB, hBe.trans (Eventually.of_forall fun p => ?_)⟩
  simp only [eq_iff_iff, mem_inter_iff, mem_ofPred_eq]
  rw [hcast]

/-- **The candidate's conditioning filtration**: the Galmarino filtration of the windows `candWin` and the marks
`candMarks` (the windows are marks events by `exists_candMarks_ae_eq_candWin`). -/
def candFilt (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × HistorySpace 0 0)) :=
  galFilt (candMu x₀ (κ := κ) P h W ζ hG.1) (candMarks x₀ h44 hκ hκ4 hb h us ℓ t s)
    (candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
    (fun q r => exists_candMarks_ae_eq_candWin x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs q r)
    (fun q => candWin_antitone x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s q)

include hκ4 in
/-- **The candidate's chart clause at a fixed restarted time `r` for `candFilt`**, from the three remaining
measurability facts (`hAv`: the validity events on the dyadic windows; `hEr`, `hFm`: the validity event and the chart
formula at `r` for `candFilt r`). -/
theorem ae_condExp_candFilt (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ}
    (hus : IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us)
    {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) (φ : TestOn upperHalfPlaneOpens)
    (r : ℝ≥0)
    (hAv : ∀ n k : ℕ, lastO ℓ t < dyqQ n k →
      ∃ B, MeasurableSet[candSigma x₀ h44 hκ hκ4 hb h us ℓ t (dyqQ n k) s] B ∧
        B =ᵐ[candMu x₀ (κ := κ) P h W ζ hG.1] (candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s (dyqQ n k) r ∩
          s4Av s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ) φ
            (dyq n k)))
    (hEr : MeasurableSet[candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs r]
      (candEr x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r))
    (hFm : StronglyMeasurable[candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs r]
      ((candEr x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r).indicator (candF x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r))) :
    ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1), p ∈ candEr x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r →
      (candMu x₀ (κ := κ) P h W ζ hG.1)[fun p' => Complex.exp (Complex.I *
          (rootField (κ := κ) (x₀ := x₀) h p'.1 φ : ℂ)) | candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs r] p =
        candF x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r p :=
  ae_condExp_cand_galFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf hus hv hs φ r
    (fun q r => exists_candMarks_ae_eq_candWin x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs q r)
    (fun n k hq => exists_candSigma_ae_eq_candWin_left x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs r n k hq)
    hAv hEr hFm

end Cand

end InteractingSLE.Sec5.CrossCond.StagedS4
