import QuantumZipper.Proofs.Zipper.LocLenStmtsF1Node
import QuantumZipper.Proofs.Zipper.LocLenLocalityF1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), task R6e-C: node F1c with open arcs

Open-arc copies (`unzipLengths ↦ unzipLengthsArc`) of `F1.ae_eq_level_of_local`
(F1Germ.lean:71) and of `F1.f1c_unscaled_const`, `F1.f1c_pstar` (F1NodeC.lean).

Source: Sheffield, *Conformal weldings of random surfaces: SLE and the quantum gravity zipper*,
arXiv:1012.4797, §5.4 p. 71 (the ratio of the two quantum lengths is a.s. constant by a 0-1 law
for the germ σ-algebra at the tip). Own bookkeeping around the cited 0-1 laws, as in F1NodeC.lean.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open F1

/-- Open-arc copy of `F1.ae_eq_level_of_local`: level versions of the ratio from locality of the
open-arc lengths at the times `s m` (Sheffield arXiv:1012.4797 §5.4 p. 71). -/
theorem ae_eq_level_of_localArc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {𝒢 : MeasurableSpace Ω} (c : Ω → FieldSample × (ℝ → ℝ))
    {f : Ω → ℝ≥0∞} (s : ℕ → ℝ) (hs : ∀ m, 0 ≤ s m)
    (hlin : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t →
      (unzipLengthsArc γ (c ω) t).2 = f ω * (unzipLengthsArc γ (c ω) t).1)
    (hposs : ∀ᵐ ω ∂P, ∀ m, 0 < (unzipLengthsArc γ (c ω) (s m)).1 ∧
      (unzipLengthsArc γ (c ω) (s m)).1 < ⊤)
    (E : ℕ → Set Ω) (h : ℕ → Ω → ℝ≥0∞ × ℝ≥0∞)
    (hEm : ∀ m, MeasurableSet[𝒢] (E m)) (hhm : ∀ m, Measurable[𝒢] (h m))
    (hev : ∀ᵐ ω ∂P, ∀ᶠ m in atTop, ω ∈ E m)
    (hEh : ∀ᵐ ω ∂P, ∀ m, ω ∈ E m → unzipLengthsArc γ (c ω) (s m) = h m ω) :
    ∃ g : Ω → ℝ≥0∞, Measurable[𝒢] g ∧ f =ᵐ[P] g := by
  refine ⟨fun ω => limsup (fun m => (E m).indicator (fun ω => lenRatio (h m ω)) ω) atTop,
    Measurable.limsup (mδ := 𝒢) fun m =>
      (measurable_lenRatio.comp (hhm m)).indicator (hEm m), ?_⟩
  filter_upwards [hlin, hposs, hev, hEh] with ω hl hp he hh
  have hevq : ∀ᶠ m in atTop,
      (E m).indicator (fun ω => lenRatio (h m ω)) ω = (fun _ : ℕ => f ω) m := by
    filter_upwards [he] with m hm
    rw [indicator_of_mem hm, ← hh m hm]
    exact lenRatio_eq_of (hl (s m) (hs m)) (hp m).1 (hp m).2
  rw [limsup_congr hevq, limsup_const]

/-- Open-arc copy of `F1.f1c_unscaled_const`: on the unscaled configuration, B5 locality of the
open-arc lengths (`B5.F1LocalityArcStmt`) makes the length ratio a.s. constant
(Sheffield arXiv:1012.4797 §5.4 p. 71). -/
theorem f1c_unscaled_constArc {γ α κ : ℝ} (hL : B5.F1LocalityArcStmt γ α κ) (hκ : 0 < κ)
    (hκ4 : κ < 4) (hγ : γ = Real.sqrt κ) (hα : α < Qc γ) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample} {A : ℝ → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ}
    (hX : IsFreeGFFModConstH X P) (hA : IsWedgeProcess α (Qc γ) A P) (hB : IsBrownianReal B P)
    (hAm : ∀ t, Measurable (A t)) (hBm : ∀ t, Measurable (B t))
    (hind : iIndep (srcSigma X A B) P) {g : Ω → ℝ≥0∞}
    (hlin : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → (unzipLengthsArc γ (unscaledConfig γ κ X A B ω) t).2 =
      g ω * (unzipLengthsArc γ (unscaledConfig γ κ X A B ω) t).1)
    (hposs : ∀ᵐ ω ∂P, ∀ m,
      0 < (unzipLengthsArc γ (unscaledConfig γ κ X A B ω) (GermZeroOne.epsSeq m : ℝ)).1 ∧
      (unzipLengthsArc γ (unscaledConfig γ κ X A B ω) (GermZeroOne.epsSeq m : ℝ)).1 < ⊤) :
    ∃ k : ℝ≥0∞, ∀ᵐ ω ∂P, g ω = k := by
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have h𝒢 : Antitone fun n => ⨆ i ∈ (Finset.univ : Finset (Fin 3)), germFam X P A B i n :=
    fun a b hab => iSup₂_mono fun i _ => germFam_anti X P A B i hab
  obtain ⟨g', hg', hgg⟩ := exists_iInf_version (P := P) h𝒢 fun n => by
    obtain ⟨E, h, hEm, hhm, hev, hEh⟩ :=
      hL hκ hκ4 hγ hα Ω P X A B inferInstance hX hA hB hAm hBm hind n
    exact ae_eq_level_of_localArc (unscaledConfig γ κ X A B)
      (fun m => (GermZeroOne.epsSeq m : ℝ)) (fun m => NNReal.coe_nonneg _) hlin hposs E h hEm
      hhm hev hEh
  obtain ⟨k, hk⟩ := f1c_ae_const_of_germ (germFam X P A B) (germFam_le hXm hAm hBm)
    (germFam_anti X P A B) (germFam_indep hind) (germFam_triv hX hA hAm hB hBm) Finset.univ hg'
  exact ⟨k, by filter_upwards [hgg, hk] with ω h1 h2; rw [h1, h2]⟩

/-- Open-arc copy of `F1.f1c_pstar`: **F1c for `P_*` samples** from the embedding step
(`F1EmbedArcStmt`) and B5 locality (`B5.F1LocalityArcStmt`) (Sheffield arXiv:1012.4797 §5.4
p. 71). -/
theorem f1c_pstarArc (hE : F1EmbedArcStmt)
    (hL : ∀ κ : ℝ, B5.F1LocalityArcStmt (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) κ)
    (hall : HLinAllArcStmt) {κ : ℝ} {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Y : Ω' → FieldSample} {B' : ℝ≥0 → Ω' → ℝ}
    (h : Thm13Asm.IsPStarSample κ P' Y B') :
    ∃ k : ℝ≥0∞, ∀ᵐ ω ∂P',
      lenRatio (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) 1) = k := by
  obtain ⟨hφ, Ω, _, P, X, A, B, g, hP, hX, hA, hB, hAm, hBm, hind, hlin, hposs, hlaw⟩ :=
    hE hall κ P' Y B' h
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 h.1
  have hγ2 : Real.sqrt κ < 2 := sqrt_lt_two_of h.2.1
  obtain ⟨k, hk⟩ := f1c_unscaled_constArc (hL κ) h.1 h.2.1 rfl (Thm18Asm.alpha_lt_Qc hγ hγ2) hX
    hA hB hAm hBm hind hlin hposs
  refine ⟨k, ae_of_ae_map (p := fun y => y = k) hφ ?_⟩
  rw [hlaw, Measure.map_congr hk, Measure.map_const, measure_univ, one_smul]
  exact (ae_dirac_iff (measurableSet_singleton k)).2 rfl

end LocLen
end QuantumZipper
