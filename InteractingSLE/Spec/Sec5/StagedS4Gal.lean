/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS4Meas
import InteractingSLE.Spec.Sec5.StagedS3Gal

/-!
# The candidate's Galmarino filtration and its dyadic pieces

Packet PROVE-STAGED-S4 (§5.2 of `planning/handoffs/PROVE-STAGED-S3.md`). The conditioning filtration of the restarted
word is PROVE-STAGED-S3's Galmarino filtration `galFilt` with

* marks `candMarks q` (DEPTH's σ-algebra `candSigma … q s` for rational own times `q` after the last switch, `⊥`
  otherwise) and
* windows `candWin q r` (alive, `q` after the last switch and before the first contact, `S₀ + r < σ(q)`), shrinking in
  the restarted time `r` (`candWin_antitone`).

Main result: **`hmeas_galFilt`** — the hypothesis `hmeas` of `ae_condExp_cand_of_meas` holds for `galFilt` as soon as,
on every window at a dyadic own time, the two events `{k/2ⁿ before contact, S₀ + r < σ(k/2ⁿ)}` and the validity
event `s4Av (dyq n k)` are almost surely events of the marks (`hK`, `hAv`). The events of `galFilt r` meet every
window in a marks event by construction; the dyadic level sets of the own time are rewritten with
`dyIdx_s4Theta_and_mem_s4Av_iff`.

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
open WangWu.ChartConst (dyq dyIdx dyqQ dyqQ_coe)

section Cand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

/-- **The window of the candidate's Galmarino filtration** at the rational own time `q` and the restarted time `r`. -/
def candWin (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) (q : ℚ) (r : ℝ≥0) :
    Set (Ω × HistorySpace 0 0) :=
  {p | p ∈ s3Alive s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) (lastO ℓ t : ℝ) ∧
    lastO ℓ t < q ∧
    (q : ℝ) ∈ gPre s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) p ∧
    ((s3Start s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) (lastO ℓ t : ℝ) p + r :
      ℝ≥0) : ℝ) < capClock (gCurve s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t)
        (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) p) q}

omit [StandardBorelSpace Ω] in
theorem candWin_antitone (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) (q : ℚ) :
    Antitone (candWin x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s q) := by
  intro r r' hrr' p hp
  refine ⟨hp.1, hp.2.1, hp.2.2.1, lt_of_le_of_lt ?_ hp.2.2.2⟩
  exact_mod_cast add_le_add_right hrr' _

open scoped Classical in
/-- **The marks of the candidate's Galmarino filtration**: DEPTH's σ-algebra after the last switch, `⊥` before. -/
@[instance_reducible]
def candMarks (us : ℂ → ℝ) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) (q : ℚ) : MeasurableSpace (Ω × HistorySpace 0 0) :=
  if lastO ℓ t < q then candSigma x₀ h44 hκ hκ4 hb h us ℓ t q s else ⊥

omit mΩ [StandardBorelSpace Ω] in
theorem candMarks_of_lt {us : ℂ → ℝ} {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} {s : ℝ≥0} {q : ℚ} (hq : lastO ℓ t < q) :
    candMarks x₀ h44 hκ hκ4 hb h us ℓ t s q = candSigma x₀ h44 hκ hκ4 hb h us ℓ t q s := by
  classical
  rw [candMarks, ite_eq_left_of_eq_true _ _ (eq_true hq)]

omit [StandardBorelSpace Ω] in
/-- **The dyadic pieces of `galFilt` events are marks events** (hypothesis `hmeas` of `ae_condExp_cand_of_meas` for
the Galmarino filtration), given that on the windows at dyadic own times the left-endpoint event and the validity
event are almost surely marks events. -/
theorem hmeas_galFilt (hhm : Measurable h) {us : ℂ → ℝ} {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} {s : ℝ≥0}
    {φ : TestOn upperHalfPlaneOpens} {r : ℝ≥0}
    (hE : ∀ q r, ∃ B, MeasurableSet[candMarks x₀ h44 hκ hκ4 hb h us ℓ t s q] B ∧
      B =ᵐ[candMu x₀ (κ := κ) P h W ζ hhm] candWin x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s q r)
    (hK : ∀ n k : ℕ, lastO ℓ t < dyqQ n k →
      ∃ B, MeasurableSet[candSigma x₀ h44 hκ hκ4 hb h us ℓ t (dyqQ n k) s] B ∧
        B =ᵐ[candMu x₀ (κ := κ) P h W ζ hhm] (candWin x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s (dyqQ n k) r ∩
          {p | (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) ∈ gPre s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t)
              (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) p ∧
            ((s3Start s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s)
              (lastO ℓ t : ℝ) p + r : ℝ≥0) : ℝ) < capClock (gCurve s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t)
                (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) p) (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ)}))
    (hAv : ∀ n k : ℕ, lastO ℓ t < dyqQ n k →
      ∃ B, MeasurableSet[candSigma x₀ h44 hκ hκ4 hb h us ℓ t (dyqQ n k) s] B ∧
        B =ᵐ[candMu x₀ (κ := κ) P h W ζ hhm] (candWin x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s (dyqQ n k) r ∩
          s4Av s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) (lastO ℓ t : ℝ) φ
            (dyq n k))) :
    ∀ D : Set (Ω × HistorySpace 0 0),
      MeasurableSet[galFilt (candMu x₀ (κ := κ) P h W ζ hhm) (candMarks x₀ h44 hκ hκ4 hb h us ℓ t s)
        (candWin x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) hE
        (fun q => candWin_antitone x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s q) r] D →
      D ⊆ candEr x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s φ r → ∀ n k : ℕ, lastO ℓ t < dyqQ n k →
        ∃ B, MeasurableSet[candSigma x₀ h44 hκ hκ4 hb h us ℓ t (dyqQ n k) s] B ∧
          B =ᵐ[candMu x₀ (κ := κ) P h W ζ hhm] (D ∩ {p | dyIdx n (s4Theta s (candW x₀ h44 hκ hκ4 hb h ℓ t)
            (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) (lastO ℓ t : ℝ) r p) = k} ∩
            s4Av s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) (lastO ℓ t : ℝ)
              φ (dyq n k)) := by
  intro D hD hDE n k hq
  have hEg : ∀ p ∈ candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s,
      IsGood49 s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t) p := fun p hp => isGood49_of_mem_glueGood p hp
  obtain ⟨B₁, hB₁, hB₁e⟩ := hD.2 (dyqQ n k)
  rw [candMarks_of_lt x₀ h44 hκ hκ4 hb h hq] at hB₁
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
    rw [candWin, mem_ofPred_eq, dyqQ_coe] at hW'
    exact ⟨⟨hpD, (hiff.2 ⟨⟨hW'.2.2.1, hW'.2.2.2⟩, fun hh => hnK ⟨hpW, hh⟩, hpAv⟩).1⟩,
      (hiff.2 ⟨⟨hW'.2.2.1, hW'.2.2.2⟩, fun hh => hnK ⟨hpW, hh⟩, hpAv⟩).2⟩
  · rintro ⟨⟨hpD, hidx⟩, hpAv⟩
    have hpE := hDE hpD
    have hiff := dyIdx_s4Theta_and_mem_s4Av_iff hEg hpE.1 hpE.2.1 n k φ
    obtain ⟨⟨hP, hlt⟩, hnK, -⟩ := hiff.1 ⟨hidx, hpAv⟩
    have hW : p ∈ candWin x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s (dyqQ n k) r := by
      refine ⟨hpE.1, hq, ?_, ?_⟩
      · rw [dyqQ_coe]; exact hP
      · rw [dyqQ_coe]; exact hlt
    exact ⟨⟨⟨hpD, hW⟩, fun hh => hnK hh.2⟩, hW, hpAv⟩

include hκ4 in
/-- **The candidate's chart clause at a fixed restarted time `r` for its Galmarino filtration**, from the remaining
measurability facts of that filtration: the windows are a.s. marks events (`hE`); on the windows at dyadic own times
the left-endpoint events (`hK`) and the validity events (`hAv`) are a.s. marks events; the validity event at `r` and the
chart formula at `r` are events/measurable for `galFilt r` (`hEr`, `hFm`). -/
theorem ae_condExp_cand_galFilt (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ}
    (hus : IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us)
    {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) (φ : TestOn upperHalfPlaneOpens)
    (r : ℝ≥0)
    (hE : ∀ q r, ∃ B, MeasurableSet[candMarks x₀ h44 hκ hκ4 hb h us ℓ t s q] B ∧
      B =ᵐ[candMu x₀ (κ := κ) P h W ζ hG.1] candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s q r)
    (hK : ∀ n k : ℕ, lastO ℓ t < dyqQ n k →
      ∃ B, MeasurableSet[candSigma x₀ h44 hκ hκ4 hb h us ℓ t (dyqQ n k) s] B ∧
        B =ᵐ[candMu x₀ (κ := κ) P h W ζ hG.1] (candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s (dyqQ n k) r ∩
          {p | (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) ∈ gPre s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t)
              (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) p ∧
            ((s3Start s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s)
              (lastO ℓ t : ℝ) p + r : ℝ≥0) : ℝ) < capClock (gCurve s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t)
                (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) p) (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ)}))
    (hAv : ∀ n k : ℕ, lastO ℓ t < dyqQ n k →
      ∃ B, MeasurableSet[candSigma x₀ h44 hκ hκ4 hb h us ℓ t (dyqQ n k) s] B ∧
        B =ᵐ[candMu x₀ (κ := κ) P h W ζ hG.1] (candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s (dyqQ n k) r ∩
          s4Av s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) (lastO ℓ t : ℝ) φ
            (dyq n k)))
    (hEr : MeasurableSet[galFilt (candMu x₀ (κ := κ) P h W ζ hG.1) (candMarks x₀ h44 hκ hκ4 hb h us ℓ t s)
      (candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) hE
      (fun q => candWin_antitone x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s q) r]
        (candEr x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r))
    (hFm : StronglyMeasurable[galFilt (candMu x₀ (κ := κ) P h W ζ hG.1) (candMarks x₀ h44 hκ hκ4 hb h us ℓ t s)
      (candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) hE
      (fun q => candWin_antitone x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s q) r]
        ((candEr x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r).indicator
          (candF x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r))) :
    ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1), p ∈ candEr x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r →
      (candMu x₀ (κ := κ) P h W ζ hG.1)[fun p' => Complex.exp (Complex.I *
          (rootField (κ := κ) (x₀ := x₀) h p'.1 φ : ℂ)) |
        galFilt (candMu x₀ (κ := κ) P h W ζ hG.1) (candMarks x₀ h44 hκ hκ4 hb h us ℓ t s)
          (candWin x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) hE
          (fun q => candWin_antitone x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s q) r] p =
        candF x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s φ r p :=
  ae_condExp_cand_of_meas x₀ h44 hκ hκ4 hb P h W ζ hG hcf hus hv hs φ r _ hEr hFm
    (measurable_s4Theta_cand x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s r)
    (hmeas_galFilt x₀ h44 hκ hκ4 hb P h W ζ hG.1 hE hK hAv)

end Cand

end InteractingSLE.Sec5.CrossCond.StagedS4
