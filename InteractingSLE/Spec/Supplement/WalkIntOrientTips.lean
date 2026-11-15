/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntOrientHistory
import InteractingSLE.Spec.Supplement.WalkWordsPiece

/-!
# Chronological PieceData supply WalkWords' tipAt contact order

This adapter uses the continuous physical boundary extension already in
PieceData. Endpoint and orientation facts come from ArcHistory; physical
tip uniqueness makes the conclusion independent of the chosen witnesses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkIntOrient

open WalkBdry WalkWords GW1WalkChain

/-- A chronological physical piece has increasing full-walk parameter
through its entire recorded lifetime, including a finite endpoint. -/
theorem strictMonoOn_piece_curveTime {γ : ℝ≥0 → ℂ}
    (hγ : Supp9B.IsProperCurve γ) {pc : Piece} {A : Set ℂ}
    {f : ℂ → ℂ} {W : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ}
    (d : PieceData pc A f W η) (hHist : ArcHistory (γ 0) A (f (η 0)))
    (hA : A ⊆ range γ) (hpc : pc.1.tipSet pc.2.1 pc.2.2 ⊆ range γ) :
    StrictMonoOn (fun t => curveTime γ (f (η t))) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ pc.2.2} := by
  obtain ⟨a, hcarrier, hstart⟩ := arcHistory_endpoint_initial_segment hγ hHist hA
  intro s hs t ht hst
  have hI : Icc (0 : ℝ≥0) t ⊆ {u : ℝ≥0 | (u : ℝ≥0∞) ≤ pc.2.2} :=
    fun u hu => (ENNReal.coe_le_coe.2 hu.2).trans ht
  have hmono := strictMonoOn_curveTime_of_initial_segment hγ (show (0 : ℝ≥0) ≤ t from zero_le)
    (d.continuousOn.mono hI) (d.inj.mono hI) (fun z hz => hpc (by
      rw [d.tipSet_eq]
      exact (image_mono hI) hz)) hstart (fun u hu hmem => by
        rcases eq_zero_or_pos u with hzero | hpos
        · exact hzero
        · exact False.elim (d.avoid u hpos (hI hu) (hcarrier ▸ hmem)))
  exact hmono ⟨zero_le, hst.le⟩ ⟨zero_le, le_rfl⟩ hst

/-- Exact own-time order for the physical tipAt contacts of two
chronological pieces, derived from the full walks' contact order. -/
theorem tipAt_contact_order_of_histories {γR γL : ℝ≥0 → ℂ}
    (hγR : Supp9B.IsProperCurve γR) (hγL : Supp9B.IsProperCurve γL)
    (horder : ∀ u u' v v' : ℝ≥0, γR u = γL v → γR u' = γL v' → (u < u' ↔ v < v'))
    {pcR pcL : Piece} {AR AL : Set ℂ} {fR fL : ℂ → ℂ}
    {WR WL : ℝ≥0 → ℝ} {ηR ηL : ℝ≥0 → ℂ}
    (dR : PieceData pcR AR fR WR ηR) (dL : PieceData pcL AL fL WL ηL)
    (hHistR : ArcHistory (γR 0) AR (fR (ηR 0))) (hHistL : ArcHistory (γL 0) AL (fL (ηL 0)))
    (hAR : AR ⊆ range γR) (hAL : AL ⊆ range γL)
    (hR : pcR.1.tipSet pcR.2.1 pcR.2.2 ⊆ range γR)
    (hL : pcL.1.tipSet pcL.2.1 pcL.2.2 ⊆ range γL)
    {a a' c c' : ℝ≥0} {z z' : ℂ}
    (ha : (a : ℝ≥0∞) ≤ pcR.2.2) (ha' : (a' : ℝ≥0∞) ≤ pcR.2.2)
    (hc : (c : ℝ≥0∞) ≤ pcL.2.2) (hc' : (c' : ℝ≥0∞) ≤ pcL.2.2)
    (hza : pcR.1.tipAt pcR.2.1 a z) (hza' : pcR.1.tipAt pcR.2.1 a' z')
    (hzc : pcL.1.tipAt pcL.2.1 c z) (hzc' : pcL.1.tipAt pcL.2.1 c' z')
    (haa' : a < a') : c < c' := by
  have hmR := strictMonoOn_piece_curveTime hγR dR hHistR hAR hR
  have hmL := strictMonoOn_piece_curveTime hγL dL hHistL hAL hL
  have hmemR (t : ℝ≥0) (ht : (t : ℝ≥0∞) ≤ pcR.2.2) : fR (ηR t) ∈ range γR := by
    apply hR
    rw [dR.tipSet_eq]
    exact ⟨t, ht, rfl⟩
  have hmemL (t : ℝ≥0) (ht : (t : ℝ≥0∞) ≤ pcL.2.2) : fL (ηL t) ∈ range γL := by
    apply hL
    rw [dL.tipSet_eq]
    exact ⟨t, ht, rfl⟩
  have hp : fR (ηR a) = fL (ηL c) :=
    (Chart.tipAt_unique (dR.tipAt ha) hza).trans (Chart.tipAt_unique hzc (dL.tipAt hc))
  have hp' : fR (ηR a') = fL (ηL c') :=
    (Chart.tipAt_unique (dR.tipAt ha') hza').trans (Chart.tipAt_unique hzc' (dL.tipAt hc'))
  have ho := horder (curveTime γR (fR (ηR a))) (curveTime γR (fR (ηR a')))
    (curveTime γL (fL (ηL c))) (curveTime γL (fL (ηL c')))
    ((apply_curveTime (hmemR a ha)).trans (hp.trans (apply_curveTime (hmemL c hc)).symm))
    ((apply_curveTime (hmemR a' ha')).trans (hp'.trans (apply_curveTime (hmemL c' hc')).symm))
  exact (hmL.lt_iff_lt hc hc').1 (ho.1 (hmR ha ha' haa'))

/-- Per-piece chronological histories supply the precise hdir argument
of WalkWords.exists_arcData, including contacts at finite lifetimes. -/
theorem tipAt_contact_order_of_piece_histories {sR sL : ExplState} {γR γL : ℝ≥0 → ℂ}
    (hγR : Supp9B.IsProperCurve γR) (hγL : Supp9B.IsProperCurve γL)
    (horder : ∀ u u' v v' : ℝ≥0, γR u = γL v → γR u' = γL v' → (u < u' ↔ v < v'))
    (hordR : ordOf sR ⊆ range γR) (hordL : ordOf sL ⊆ range γL)
    (hChronR : ∀ pc ∈ sR.1, ∃ (A : Set ℂ) (f : ℂ → ℂ) (W : ℝ≥0 → ℝ) (η : ℝ≥0 → ℂ),
      PieceData pc A f W η ∧ ArcHistory (γR 0) A (f (η 0)) ∧ A ⊆ range γR)
    (hChronL : ∀ pc ∈ sL.1, ∃ (A : Set ℂ) (f : ℂ → ℂ) (W : ℝ≥0 → ℝ) (η : ℝ≥0 → ℂ),
      PieceData pc A f W η ∧ ArcHistory (γL 0) A (f (η 0)) ∧ A ⊆ range γL) :
    ∀ pR ∈ sR.1, ∀ pL ∈ sL.1, ∀ (a a' c c' : ℝ≥0) (z z' : ℂ),
      (a : ℝ≥0∞) ≤ pR.2.2 → (a' : ℝ≥0∞) ≤ pR.2.2 →
      (c : ℝ≥0∞) ≤ pL.2.2 → (c' : ℝ≥0∞) ≤ pL.2.2 →
      pR.1.tipAt pR.2.1 a z → pR.1.tipAt pR.2.1 a' z' →
      pL.1.tipAt pL.2.1 c z → pL.1.tipAt pL.2.1 c' z' → a < a' → c < c' := by
  intro pR hpR pL hpL a a' c c' z z' ha ha' hc hc' hza hza' hzc hzc' haa'
  obtain ⟨AR, fR, WR, ηR, dR, hHistR, hAR⟩ := hChronR pR hpR
  obtain ⟨AL, fL, WL, ηL, dL, hHistL, hAL⟩ := hChronL pL hpL
  exact tipAt_contact_order_of_histories hγR hγL horder dR dL hHistR hHistL hAR hAL
    (fun _ hz => hordR (mem_iUnion₂.2 ⟨pR, hpR, hz⟩))
    (fun _ hz => hordL (mem_iUnion₂.2 ⟨pL, hpL, hz⟩))
    ha ha' hc hc' hza hza' hzc hzc' haa'

end InteractingSLE.Theorem14.WalkIntOrient
