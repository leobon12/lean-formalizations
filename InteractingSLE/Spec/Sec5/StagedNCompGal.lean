/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNCompPast
import InteractingSLE.Spec.Sec5.StagedS4Win

/-!
# The flag candidate's conditioning filtration (Galmarino) and its chart clause

Packet PROVE-STAGED-NODECOMP. PROVE-STAGED-S4's `StagedS4Meas`/`Gal`/`Good`/`Win` (candidate part) for the flag
candidate of arbitrary angle flags `fl` (`StagedNCompInst`); the generic parts of those files are reused.

* `adaptedBefore_candWF`, `measurable_s4Theta_candF`: measurability of the driver and of the own-time map;
* `candWinF` (windows), `candMarksF` (marks), `hmeas_galFiltF`, `ae_condExp_candF_galFilt`;
* **`ae_good_candF`**: almost every glued sample is good for the flag candidate's driver;
* `exists_candSigmaF_ae_eq_candWinF_inter`, `exists_candMarksF_ae_eq_candWinF`, `exists_candSigmaF_ae_eq_candWinF_left`;
* **`candFiltF`** (the Galmarino filtration) and **`ae_condExp_candFiltF`** (its chart clause from `hAv`, `hEr`, `hFm`).

R48: the only named input is `h44 : Theorem12ParamCond44Statement` (R74).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open QuantumZipper (chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedNComp

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q Word49 Theta StagedS3
open Restart Exist.StagedLaw Exist.Staged
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target StagedGlue StagedDepth Prop59Pieces StagedRepLater
open StagedS4 Prop59NodeTree
open Prop59Pieces.IsKilledFamily (kInvK kInv_lt_iff)
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Sec7.Lemma71C (capClock)
open WangWu.ChartConst (dyq dyIdx dyqQ dyqQ_coe)

/-! ### Ported from `StagedS4Meas` -/

section Cand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞) (fl : ℕ → Bool)

omit [StandardBorelSpace Ω] in
/-- The candidate's driver is a measurable process (adapted before `⊤` to the constant filtration). -/
theorem adaptedBefore_candWF (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) :
    AdaptedBefore (Filtration.const ℝ≥0 mΩ le_rfl) (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) := by
  intro r A hA
  have hqm : Measurable (qField x₀ κ h) :=
    (measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hhm
  have hm : Measurable fun ω => candWF x₀ h44 hκ hκ4 hb h fl ℓ t r ω :=
    (measurable_pi_apply r).comp (measurable_continuedDriver
      (fun k => (measurable_codeDriver h44 hκ hκ4 _ _ k).comp hqm) _ _ _)
  have e : {ω | (r : ℝ≥0∞) < (fun _ => (⊤ : ℝ≥0∞)) ω ∧ candWF x₀ h44 hκ hκ4 hb h fl ℓ t r ω ∈ A} =
      (fun ω => candWF x₀ h44 hκ hκ4 hb h fl ℓ t r ω) ⁻¹' A := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, ENNReal.coe_lt_top, true_and]
  rw [e]
  exact hm hA

omit [StandardBorelSpace Ω] in
/-- **The candidate's own-time map of a restarted time is measurable** (hypothesis `hθ` of
`ae_condExp_candF_of_meas`). -/
theorem measurable_s4Theta_candF (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) (r : ℝ≥0) :
    Measurable (s4Theta s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s)
      (lastO ℓ t : ℝ) r) :=
  measurable_s4Theta (adaptedBefore_candWF x₀ h44 hκ hκ4 hb h fl hhm ℓ t) measurableSet_glueGood
    (fun p hp => isGood49_of_mem_glueGood p hp) (lastO ℓ t) r

end Cand

/-! ### Ported from `StagedS4Gal` -/

section Cand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞) (fl : ℕ → Bool)

/-- **The window of the candidate's Galmarino filtration** at the rational own time `q` and the restarted time `r`. -/
def candWinF (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) (q : ℚ) (r : ℝ≥0) :
    Set (Ω × HistorySpace 0 0) :=
  {p | p ∈ s3Alive s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s) (lastO ℓ t :
      ℝ) ∧
    lastO ℓ t < q ∧
    (q : ℝ) ∈ gPre s (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s) p ∧
    ((s3Start s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s) (lastO ℓ t : ℝ) p
        + r :
      ℝ≥0) : ℝ) < capClock (gCurve s (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
        (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s) p) q}

omit [StandardBorelSpace Ω] in
theorem candWinF_antitone (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) (q : ℚ) :
    Antitone (candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s q) := by
  intro r r' hrr' p hp
  refine ⟨hp.1, hp.2.1, hp.2.2.1, lt_of_le_of_lt ?_ hp.2.2.2⟩
  exact_mod_cast add_le_add_right hrr' _

open scoped Classical in
/-- **The marks of the candidate's Galmarino filtration**: DEPTH's σ-algebra after the last switch, `⊥` before. -/
@[instance_reducible]
def candMarksF (us : ℂ → ℝ) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) (q : ℚ) : MeasurableSpace (Ω × HistorySpace 0 0) :=
  if lastO ℓ t < q then candSigmaF x₀ h44 hκ hκ4 hb h fl us ℓ t q s else ⊥

omit mΩ [StandardBorelSpace Ω] in
theorem candMarksF_of_lt {us : ℂ → ℝ} {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} {s : ℝ≥0} {q : ℚ} (hq : lastO ℓ t < q) :
    candMarksF x₀ h44 hκ hκ4 hb h fl us ℓ t s q = candSigmaF x₀ h44 hκ hκ4 hb h fl us ℓ t q s := by
  classical
  rw [candMarksF, ite_eq_left_of_eq_true _ _ (eq_true hq)]

omit [StandardBorelSpace Ω] in
/-- **The dyadic pieces of `galFilt` events are marks events** (hypothesis `hmeas` of `ae_condExp_candF_of_meas` for
the Galmarino filtration), given that on the windows at dyadic own times the left-endpoint event and the validity
event are almost surely marks events. -/
theorem hmeas_galFiltF (hhm : Measurable h) {us : ℂ → ℝ} {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} {s : ℝ≥0}
    {φ : TestOn upperHalfPlaneOpens} {r : ℝ≥0}
    (hE : ∀ q r, ∃ B, MeasurableSet[candMarksF x₀ h44 hκ hκ4 hb h fl us ℓ t s q] B ∧
      B =ᵐ[candMu x₀ (κ := κ) P h W ζ hhm] candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s q r)
    (hK : ∀ n k : ℕ, lastO ℓ t < dyqQ n k →
      ∃ B, MeasurableSet[candSigmaF x₀ h44 hκ hκ4 hb h fl us ℓ t (dyqQ n k) s] B ∧
        B =ᵐ[candMu x₀ (κ := κ) P h W ζ hhm] (candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s (dyqQ n k) r ∩
          {p | (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) ∈ gPre s (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
              (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s) p ∧
            ((s3Start s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s)
              (lastO ℓ t : ℝ) p + r : ℝ≥0) : ℝ) < capClock (gCurve s (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
                (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s) p) (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ)}))
    (hAv : ∀ n k : ℕ, lastO ℓ t < dyqQ n k →
      ∃ B, MeasurableSet[candSigmaF x₀ h44 hκ hκ4 hb h fl us ℓ t (dyqQ n k) s] B ∧
        B =ᵐ[candMu x₀ (κ := κ) P h W ζ hhm] (candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s (dyqQ n k) r ∩
          s4Av s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s) (lastO ℓ t : ℝ) φ
            (dyq n k))) :
    ∀ D : Set (Ω × HistorySpace 0 0),
      MeasurableSet[galFilt (candMu x₀ (κ := κ) P h W ζ hhm) (candMarksF x₀ h44 hκ hκ4 hb h fl us ℓ t s)
        (candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s) hE
        (fun q => candWinF_antitone x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s q) r] D →
      D ⊆ candErF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s φ r → ∀ n k : ℕ, lastO ℓ t < dyqQ n k →
        ∃ B, MeasurableSet[candSigmaF x₀ h44 hκ hκ4 hb h fl us ℓ t (dyqQ n k) s] B ∧
          B =ᵐ[candMu x₀ (κ := κ) P h W ζ hhm] (D ∩ {p | dyIdx n (s4Theta s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
            (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s) (lastO ℓ t : ℝ) r p) = k} ∩
            s4Av s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s) (lastO ℓ t : ℝ)
              φ (dyq n k)) := by
  intro D hD hDE n k hq
  have hEg : ∀ p ∈ candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s,
      IsGood49 s (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) p := fun p hp => isGood49_of_mem_glueGood p hp
  obtain ⟨B₁, hB₁, hB₁e⟩ := hD.2 (dyqQ n k)
  rw [candMarksF_of_lt x₀ h44 hκ hκ4 hb h fl hq] at hB₁
  obtain ⟨B₂, hB₂, hB₂e⟩ := hK n k hq
  obtain ⟨B₃, hB₃, hB₃e⟩ := hAv n k hq
  refine ⟨B₁ ∩ B₂ᶜ ∩ B₃, (hB₁.inter hB₂.compl).inter hB₃, ((hB₁e.inter hB₂e.compl).inter hB₃e).trans ?_⟩
  refine Eventually.of_forall fun p => ?_
  simp only [mem_inter_iff, mem_compl_iff, mem_ofPred_eq, eq_iff_iff]
  constructor
  · rintro ⟨⟨⟨hpD, hpW⟩, hnK⟩, -, hpAv⟩
    have hpE := hDE hpD
    have hiff := dyIdx_s4Theta_and_mem_s4Av_iff hEg hpE.1 hpE.2.1 n k φ
    have hW' := hpW
    rw [candWinF, mem_ofPred_eq, dyqQ_coe] at hW'
    exact ⟨⟨hpD, (hiff.2 ⟨⟨hW'.2.2.1, hW'.2.2.2⟩, fun hh => hnK ⟨hpW, hh⟩, hpAv⟩).1⟩,
      (hiff.2 ⟨⟨hW'.2.2.1, hW'.2.2.2⟩, fun hh => hnK ⟨hpW, hh⟩, hpAv⟩).2⟩
  · rintro ⟨⟨hpD, hidx⟩, hpAv⟩
    have hpE := hDE hpD
    have hiff := dyIdx_s4Theta_and_mem_s4Av_iff hEg hpE.1 hpE.2.1 n k φ
    obtain ⟨⟨hP, hlt⟩, hnK, -⟩ := hiff.1 ⟨hidx, hpAv⟩
    have hW : p ∈ candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s (dyqQ n k) r := by
      refine ⟨hpE.1, hq, ?_, ?_⟩
      · rw [dyqQ_coe]; exact hP
      · rw [dyqQ_coe]; exact hlt
    exact ⟨⟨⟨hpD, hW⟩, fun hh => hnK hh.2⟩, hW, hpAv⟩

include hκ4 in
/-- **The candidate's chart clause at a fixed restarted time `r` for its Galmarino filtration**, from the remaining
measurability facts of that filtration: the windows are a.s. marks events (`hE`); on the windows at dyadic own times
the left-endpoint events (`hK`) and the validity events (`hAv`) are a.s. marks events; the validity event at `r` and the
chart formula at `r` are events/measurable for `galFilt r` (`hEr`, `hFm`). -/
theorem ae_condExp_candF_galFilt (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ}
    (hus : IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us)
    {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) (φ : TestOn upperHalfPlaneOpens)
    (r : ℝ≥0)
    (hE : ∀ q r, ∃ B, MeasurableSet[candMarksF x₀ h44 hκ hκ4 hb h fl us ℓ t s q] B ∧
      B =ᵐ[candMu x₀ (κ := κ) P h W ζ hG.1] candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s q r)
    (hK : ∀ n k : ℕ, lastO ℓ t < dyqQ n k →
      ∃ B, MeasurableSet[candSigmaF x₀ h44 hκ hκ4 hb h fl us ℓ t (dyqQ n k) s] B ∧
        B =ᵐ[candMu x₀ (κ := κ) P h W ζ hG.1] (candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s (dyqQ n k) r ∩
          {p | (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) ∈ gPre s (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
              (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) p ∧
            ((s3Start s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
              (lastO ℓ t : ℝ) p + r : ℝ≥0) : ℝ) < capClock (gCurve s (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
                (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) p) (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ)}))
    (hAv : ∀ n k : ℕ, lastO ℓ t < dyqQ n k →
      ∃ B, MeasurableSet[candSigmaF x₀ h44 hκ hκ4 hb h fl us ℓ t (dyqQ n k) s] B ∧
        B =ᵐ[candMu x₀ (κ := κ) P h W ζ hG.1] (candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s (dyqQ n k) r ∩
          s4Av s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ) φ
            (dyq n k)))
    (hEr : MeasurableSet[galFilt (candMu x₀ (κ := κ) P h W ζ hG.1) (candMarksF x₀ h44 hκ hκ4 hb h fl us ℓ t s)
      (candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) hE
      (fun q => candWinF_antitone x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s q) r]
        (candErF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s φ r))
    (hFm : StronglyMeasurable[galFilt (candMu x₀ (κ := κ) P h W ζ hG.1) (candMarksF x₀ h44 hκ hκ4 hb h fl us ℓ t s)
      (candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) hE
      (fun q => candWinF_antitone x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s q) r]
        ((candErF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s φ r).indicator
          (candFF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s φ r))) :
    ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1), p ∈ candErF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s φ r →
      (candMu x₀ (κ := κ) P h W ζ hG.1)[fun p' => Complex.exp (Complex.I *
          (rootFieldT κ x₀ (flagAngle (fl 0)) h p'.1 φ : ℂ)) |
        galFilt (candMu x₀ (κ := κ) P h W ζ hG.1) (candMarksF x₀ h44 hκ hκ4 hb h fl us ℓ t s)
          (candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) hE
          (fun q => candWinF_antitone x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s q) r] p =
        candFF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s φ r p :=
  ae_condExp_candF_of_meas x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf hus hv hs φ r _ hEr hFm
    (measurable_s4Theta_candF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s r)
    (hmeas_galFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 hE hK hAv)

end Cand

/-! ### Ported from `StagedS4Good` -/

section Cand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞) (fl : ℕ → Bool)

include hκ4 in
/-- **Almost every glued sample is good for the candidate's driver**: it lies in `candEg`, the candidate's driver is a
good path (`ζ = ⊤`, continuous from `0`), and the staged trace is a proper arc. -/
theorem ae_good_candF (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (hv : IsValid ℓ t)
    {s : ℝ≥0} (hs : 0 < s) :
    ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1), p ∈ candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s ∧
      Aux50Hit.IsGoodPath (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
        (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) p.1 ∧
      IsProperArc (seedLine (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) p.1) := by
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  have hhm : Measurable h := hG.1
  obtain ⟨_, 𝓕, VL, VR, B, hC⟩ := exists_rootCoupling h44 hκ hκ4 hb (P := P) hhm hG
  have hcfc := isCenteredCounterflowDriver_of_strip hκ hcf
  have hcfm := measurable_cfHistory_of_strip hcf
  have hqm : Measurable (qField x₀ κ h) := (measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hhm
  have hk : P.map (fun ω => (qField x₀ κ h ω, Cond44Ref.cfHistory W ζ ω)) =
      P.map (qField x₀ κ h) ⊗ₘ candK x₀ (κ := κ) P h W ζ :=
    (compProd_map_condDistrib hqm.aemeasurable hcfm.aemeasurable).symm
  have hlaw : P.map (fun ω => cfFieldT κ (π / 2) (rootField (κ := κ) (x₀ := x₀) h ω)) = P.map (qField x₀ κ h) := by
    congr 1
    funext ω
    rw [cfFieldT_pi_div_two]
    exact cfField_rootField ω
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have h44' : Sec4.Cond44 κ (flowLineRhoL κ c.fn c.jumps 0 (π / 2)) (flowLineRhoR κ c.fn c.jumps 0 (π / 2)) :=
    cond44_upper hκ (sourceWord_extreme hκ hb)
  have hθb := cfThetaBounds_of_cond44 hκ hκ4 hF h44'
  have hh : IsGFFWithBoundaryData P (qField x₀ κ h) c.fn c.jumps := sourceWord_gff hκ hb hG
  set sc := candSchedF fl ℓ t with hsc
  have hlt : lastO ℓ t < lastO ℓ t + 1 := lt_add_one _
  have hE := Prop59Sched.isStagedHistory_schedDrivers h44 hκ hκ4 c (sourceWord_extreme hκ hb) hh sc
  have hreg := Prop59Sched.schedDrivers_regular h44 hκ hκ4 c sc (qField x₀ κ h)
  have hXm : Measurable fun ω => cfFieldT κ (π / 2) (rootField (κ := κ) (x₀ := x₀) h ω) :=
    (measurable_cfFieldT κ (π / 2)).comp (measurable_rootField (κ := κ) (x₀ := x₀) hhm)
  have hGg := WangWu.ae_glue_fst (X := fun ω => cfFieldT κ (π / 2) (rootField (κ := κ) (x₀ := x₀) h ω))
    (candK x₀ (κ := κ) P h W ζ) hXm (ae_schedule_goodPath h44 hκ hκ4 c (sourceWord_extreme hκ hb) hh sc hE hreg)
  have hcfg := ae_cfGood_glueT hκ hC hθb hcfc hlaw (candK x₀ (κ := κ) P h W ζ) hk hs
  have hW : candWF x₀ h44 hκ hκ4 hb h fl ℓ t = joinProc sc (Prop59Sched.schedDrivers h44 hκ hκ4 c sc (qField x₀ κ h)) :=
    (joinProc_mkSchedF_eq_qDrvF h44 hκ hκ4 c (qField x₀ κ h) fl hv hlt).symm
  have hgood : ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1),
      IsGood49 s (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) p ∧
      Aux50Hit.IsGoodPath (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
        (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) p.1 ∧
      IsProperArc (seedLine (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) p.1) := by
    filter_upwards [hGg, hcfg] with p hgp ⟨_, hy⟩
    obtain ⟨hjc, hj0, hαp, -⟩ := properArc_seedLine_joinProc sc (fun j => hreg j p.1) hgp
    rw [hW]
    refine ⟨isGood49_of_mem hαp hy, ⟨rfl, hj0, ?_, fun i => i.elim0, fun i => i.elim0⟩, hαp⟩
    exact hjc.continuousOn
  filter_upwards [hgood, ae_mem_glueGood (hgood.mono fun p hp => hp.1)] with p hp hpE
  exact ⟨hpE, hp.2⟩

end Cand

/-! ### Ported from `StagedS4Win` -/

section Cand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞) (fl : ℕ → Bool)

include hκ4 in
/-- **A window intersected with a pre-contact capacity event at a rational `u ≤ q` is almost surely an event of
DEPTH's σ-algebra.** -/
theorem exists_candSigmaF_ae_eq_candWinF_inter (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) {q u : ℚ} (hq : lastO ℓ t < q) (hu0 : (0 : ℝ) ≤ u) (huq : u ≤ q)
    (r : ℝ≥0) :
    ∃ B, MeasurableSet[candSigmaF x₀ h44 hκ hκ4 hb h fl us ℓ t q s] B ∧
      B =ᵐ[candMu x₀ (κ := κ) P h W ζ hG.1] (candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s q r ∩
        {p | (u : ℝ) ∈ gPre s (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
            (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) p ∧
          ((s3Start s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
            (lastO ℓ t : ℝ) p + r : ℝ≥0) : ℝ) < capClock (gCurve s (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
              (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) p) u}) := by
  set Wc := candWF x₀ h44 hκ hκ4 hb h fl ℓ t with hWc
  set Eg := candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s with hEgdef
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
  obtain ⟨B, hB, hBe⟩ := exists_candSigmaF_ae_eq_stopD x₀ h44 hκ hκ4 hb P h W ζ fl hG us hv hq s hC
  refine ⟨B, hB, hBe.trans ?_⟩
  filter_upwards [ae_good_candF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf ℓ t hv hs] with p hpg
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
theorem exists_candMarksF_ae_eq_candWinF (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) (q : ℚ) (r : ℝ≥0) :
    ∃ B, MeasurableSet[candMarksF x₀ h44 hκ hκ4 hb h fl us ℓ t s q] B ∧
      B =ᵐ[candMu x₀ (κ := κ) P h W ζ hG.1] candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s q r := by
  classical
  by_cases hq : lastO ℓ t < q
  · rw [candMarksF_of_lt x₀ h44 hκ hκ4 hb h fl hq]
    have hq0 : (0 : ℝ) ≤ q := by exact_mod_cast (lastO_nonneg hv).trans hq.le
    obtain ⟨B, hB, hBe⟩ := exists_candSigmaF_ae_eq_candWinF_inter x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs hq hq0
      le_rfl r
    refine ⟨B, hB, hBe.trans (Eventually.of_forall fun p => ?_)⟩
    simp only [eq_iff_iff, mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun h => h.1, fun h => ⟨h, h.2.2.1, h.2.2.2⟩⟩
  · refine ⟨∅, ?_, ?_⟩
    · rw [candMarksF, ite_eq_right_of_eq_false _ _ (eq_false hq)]
      exact @MeasurableSet.empty _ ⊥
    · have he : candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s q r = ∅ :=
        eq_empty_of_forall_notMem fun p hp => hq hp.2.1
      rw [he]

include hκ4 in
/-- **`hK`: on a window at a dyadic own time, the left-endpoint event is almost surely an event of DEPTH's
σ-algebra.** -/
theorem exists_candSigmaF_ae_eq_candWinF_left
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) (r : ℝ≥0) (n k : ℕ) (hq : lastO ℓ t < dyqQ n k) :
    ∃ B, MeasurableSet[candSigmaF x₀ h44 hκ hκ4 hb h fl us ℓ t (dyqQ n k) s] B ∧
      B =ᵐ[candMu x₀ (κ := κ) P h W ζ hG.1] (candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s (dyqQ n k) r ∩
        {p | (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) ∈ gPre s (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
            (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) p ∧
          ((s3Start s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
            (lastO ℓ t : ℝ) p + r : ℝ≥0) : ℝ) < capClock (gCurve s (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
              (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) p) (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ)}) := by
  have hcast : (((k : ℚ) / 2 ^ n : ℚ) : ℝ) = (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) := by push_cast; ring
  have hu0 : (0 : ℝ) ≤ (((k : ℚ) / 2 ^ n : ℚ) : ℝ) := by rw [hcast]; exact NNReal.coe_nonneg _
  have huq : ((k : ℚ) / 2 ^ n : ℚ) ≤ dyqQ n k := by
    rw [dyqQ]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  obtain ⟨B, hB, hBe⟩ := exists_candSigmaF_ae_eq_candWinF_inter x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs hq hu0 huq r
  refine ⟨B, hB, hBe.trans (Eventually.of_forall fun p => ?_)⟩
  simp only [eq_iff_iff, mem_inter_iff, mem_ofPred_eq]
  rw [hcast]

/-- **The candidate's conditioning filtration**: the Galmarino filtration of the windows `candWinF` and the marks
`candMarksF` (the windows are marks events by `exists_candMarksF_ae_eq_candWinF`). -/
def candFiltF (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × HistorySpace 0 0)) :=
  galFilt (candMu x₀ (κ := κ) P h W ζ hG.1) (candMarksF x₀ h44 hκ hκ4 hb h fl us ℓ t s)
    (candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
    (fun q r => exists_candMarksF_ae_eq_candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs q r)
    (fun q => candWinF_antitone x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s q)

include hκ4 in
/-- **The candidate's chart clause at a fixed restarted time `r` for `candFiltF`**, from the three remaining
measurability facts (`hAv`: the validity events on the dyadic windows; `hEr`, `hFm`: the validity event and the chart
formula at `r` for `candFiltF r`). -/
theorem ae_condExp_candFiltF (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ}
    (hus : IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us)
    {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) (φ : TestOn upperHalfPlaneOpens)
    (r : ℝ≥0)
    (hAv : ∀ n k : ℕ, lastO ℓ t < dyqQ n k →
      ∃ B, MeasurableSet[candSigmaF x₀ h44 hκ hκ4 hb h fl us ℓ t (dyqQ n k) s] B ∧
        B =ᵐ[candMu x₀ (κ := κ) P h W ζ hG.1] (candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s (dyqQ n k) r ∩
          s4Av s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ) φ
            (dyq n k)))
    (hEr : MeasurableSet[candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs r]
      (candErF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s φ r))
    (hFm : StronglyMeasurable[candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs r]
      ((candErF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s φ r).indicator (candFF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s
          φ r))) :
    ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1), p ∈ candErF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s φ r →
      (candMu x₀ (κ := κ) P h W ζ hG.1)[fun p' => Complex.exp (Complex.I *
          (rootFieldT κ x₀ (flagAngle (fl 0)) h p'.1 φ : ℂ)) | candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs
              r] p =
        candFF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s φ r p :=
  ae_condExp_candF_galFilt x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf hus hv hs φ r
    (fun q r => exists_candMarksF_ae_eq_candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs q r)
    (fun n k hq => exists_candSigmaF_ae_eq_candWinF_left x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs r n k hq)
    hAv hEr hFm

end Cand

end InteractingSLE.Sec5.CrossCond.StagedNComp
