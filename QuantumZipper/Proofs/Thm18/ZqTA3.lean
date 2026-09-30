import QuantumZipper.Proofs.Thm18.ZqTA2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-TYP (A3): the scheme clause `G3ZqTSchemeSideStmt`

* Scheme `B` at the partner: Cameron–Martin transfer from the free scheme (`palmB_nullR`, as
  `palmB_null`).
* The free field at the partner: on `(0, 1)` by the proved fixed-Palm-point certificate and the
  free Palm transfer (window `(−1, 1)`), on `[1, ∞)` by the node `G3ZqTFreeFarStmt`
  (`ae_free_nullR`).
* Scheme `C` at the partner: `ae_prof_null` with `side = false` and `ν₀ + ν₂ ≪ ν_h`.
* `g3ZqTSchemeSideStmt_of`: `G3ZqTSchemeSideStmt` from `G3ZqTVPalmStmt` and `G3ZqTFreeFarStmt`.

Sheffield, arXiv:1012.4797, proof of Prop. 5.5, p. 65; Duplantier–Sheffield, arXiv:0808.1560,
§3.3; Berestycki–Powell, arXiv:2004.04720, Lemma 3.12 (Cameron–Martin). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqT

open R18 PalmNorm G3Zq G3Z2b2 G3ZqL Factorization

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- **Null partner events of the free scheme are null for scheme `B`.** -/
theorem palmB_nullR {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {Bd : Set ((ℕ → ℝ) × ℝ)}
    (hBd : MeasurableSet Bd) (hpos : ∀ q ∈ Bd, (0 : ℝ) < q.2)
    (hA : ∀ᵐ ω ∂gffBase.P, (g3pν₀ γ 0 i ω + g3pν₂ γ 0 i ω)
      {x | (coords (g3pField γ 0 ω), x) ∈ Bd} = 0) :
    g3pPalmLaw γ (g3wCut γ i.η) i
      {p | (coords (g3pField γ (g3wCut γ i.η) p.1), g3pR γ (g3wCut γ i.η) i p) ∈ Bd} = 0 := by
  have hZB := g3pBZ_pos_lt_top hγ hγ2 i
  have hZA : 0 < g3pZ γ 0 i ∧ g3pZ γ 0 i < ⊤ := by rw [g3pZ_zero]; exact g3Z_pos_lt_top hγ hγ2 i
  have hA0 := palm_nullR_of_ae hZA hBd hpos hA
  set S₀ : Set (FieldSample × ℝ) := {q | (coords q.1, sR γ i q) ∈ Bd} with hS₀def
  have hS₀ : MeasurableSet S₀ :=
    ((measurable_coords.comp measurable_fst).prodMk (measurable_sR γ i)) hBd
  set Φ : FieldSample × ℝ → ℝ≥0∞ := S₀.indicator (sW0 γ i) with hΦdef
  have hΦ : Measurable Φ := (measurable_sW0 γ i).indicator hS₀
  have hloc : ∀ (x x' : FieldSample) (s : ℝ),
      (∀ μ : Measure ℂ, IsAdmissibleH μ → μ univ = 1 → x μ = x' μ) → Φ (x, s) = Φ (x', s) := by
    intro x x' s hxx
    have hfc : FcEq x x' := fun c ρ hρ =>
      hxx _ (D3Plus.isAdmissibleH_foldedCircle' c hρ) measure_univ
    have hc : coords x = coords x' := funext fun j => hfc _ _ (radius_pos _)
    have hmem : (x, s) ∈ S₀ ↔ (x', s) ∈ S₀ := by
      show (coords x, sR γ i (x, s)) ∈ Bd ↔ (coords x', sR γ i (x', s)) ∈ Bd
      rw [hc, sR_fc hfc γ i s]
    by_cases hx' : (x', s) ∈ S₀
    · rw [hΦdef, indicator_of_mem hx', indicator_of_mem (hmem.2 hx'), sW0_fc hfc γ i s]
    · rw [hΦdef, indicator_of_notMem hx', indicator_of_notMem (fun h => hx' (hmem.1 h))]
  have hT := lintegral_g3pField_eq_tilt γ (contDiff_g3wCut γ i.η i.hη)
    (hasCompactSupport_g3wCut γ i.η) (g3wCut_conj γ i.η) (g3wCut_unit γ i.η) hΦ hloc
  have hRB : Measurable (g3pR γ (g3wCut γ i.η) i) :=
    (measurable_g3pR γ _ i).mono (sig_le_g3 i _ _) le_rfl
  have hRA : Measurable (g3pR γ 0 i) := (measurable_g3pR γ _ i).mono (sig_le_g3 i _ _) le_rfl
  set SB := {p : gffBase.Ω × ℝ |
    (coords (g3pField γ (g3wCut γ i.η) p.1), g3pR γ (g3wCut γ i.η) i p) ∈ Bd} with hSBdef
  set SA := {p : gffBase.Ω × ℝ | (coords (g3pField γ 0 p.1), g3pR γ 0 i p) ∈ Bd} with hSAdef
  have hSB : MeasurableSet SB :=
    (((measurable_coords.comp (measurable_g3pField γ _)).comp measurable_fst).prodMk hRB) hBd
  have hSA : MeasurableSet SA :=
    (((measurable_coords.comp (measurable_g3pField γ _)).comp measurable_fst).prodMk hRA) hBd
  have hWA : Measurable (g3pW0 γ 0 i) := (measurable_g3pW0 γ 0 i).mono (sig_le_g3 i _ _) le_rfl
  rw [g3pPalmLaw_apply hZA hSA] at hA0
  have hA1 : ∫⁻ p, SA.indicator (g3pW0 γ 0 i) p ∂(gffBase.P.prod L₀) = 0 := by
    rcases mul_eq_zero.1 hA0 with h | h
    · exact absurd h (ENNReal.inv_ne_zero.2 hZA.2.ne)
    · exact h
  have hA2 := (lintegral_eq_zero_iff (hWA.indicator hSA)).1 hA1
  rw [g3pPalmLaw_apply hZB hSB]
  have eB : ∀ p : gffBase.Ω × ℝ, SB.indicator (g3pW0 γ (g3wCut γ i.η) i) p =
      Φ (g3pField γ (g3wCut γ i.η) p.1, p.2) := fun p => rfl
  have eA : ∀ p : gffBase.Ω × ℝ, Φ (normField γ gffBase.X p.1, p.2) =
      SA.indicator (g3pW0 γ 0 i) p := fun p => by
    rw [← g3pField_zero]; rfl
  rw [lintegral_congr eB, hT]
  have hz : ∫⁻ p, Φ (normField γ gffBase.X p.1, p.2) *
      ENNReal.ofReal (cmTilt gffBase.X (g3wCut γ i.η) p.1) ∂(gffBase.P.prod L₀) = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hA2] with p hp
    rw [eA, hp, Pi.zero_apply, zero_mul]
  rw [hz, mul_zero]

/-- **Node: the certificate of the free field at quantum-typical points of `[1, ∞)`** (the
far-right part of `G3ZqLPalmCertStmt`, which is proved on `(−1, 1)` only). -/
def G3ZqTFreeFarStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ a : ℝ≥0 → ℝ, G3ZqGoodPath γ a →
    ∀ᵐ ω ∂gffBase.P, ∀ᵐ x ∂(qBoundaryMeasure γ (normField γ gffBase.X ω)), 1 ≤ x →
      LocCertC γ (g3coordsM γ 0 Ψ false (normField γ gffBase.X ω, a, 1, x))

theorem badSet_pos {γ : ℝ} {a : ℝ≥0 → ℝ} : ∀ q ∈ badSet γ Ψ false a, (0 : ℝ) < q.2 :=
  fun q hq => by simpa [g1SideHalf] using hq.1

/-- **The free field at the partner.** -/
theorem ae_free_nullR (hF : G3ZqTFreeFarStmt) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ} (ha : G3ZqGoodPath γ a) :
    ∀ᵐ ω ∂gffBase.P, ∀ i : G3Idx, (g3pν₀ γ 0 i ω + g3pν₂ γ 0 i ω)
      {x | (coords (g3pField γ 0 ω), x) ∈ badSet γ Ψ false a} = 0 := by
  have hab : Icc (-1 : ℝ) 1 ⊆ Icc (-((1 : ℕ) : ℝ)) ((1 : ℕ) : ℝ) := by simp
  have hPal : ∀ᵐ x ∂(volume.restrict (Ioo (-1 : ℝ) 1)), ∀ᵐ ω ∂gffBase.P,
      (coords (normField γ (xPalm γ x) ω), x) ∉ badSet γ Ψ false a := by
    filter_upwards [ZqR.g3ZqLPalmCertStmt_holds γ hγ hγ2 Ψ hsel a ha false] with x hx
    by_cases hxs : x ∈ g1SideHalf false
    · filter_upwards [hx hxs] with ω hω
      intro hb
      exact hb.2 (by rw [g3coordsM_reconstruct_coords]; exact hω)
    · exact Eventually.of_forall fun ω hb => hxs hb.1
  have hT := ae_hν_of_palm_null hγ hγ2 (measurableSet_badSet hsel false a) hab hPal
  filter_upwards [hT, hF γ hγ hγ2 Ψ hsel a ha, G3Fid.ae_normField_good gffBase.gff hγ hγ2]
    with ω hω hfar hgood i
  obtain ⟨hv, hfin, hat⟩ := hgood
  set Bx := {x | (coords (normField γ gffBase.X ω), x) ∈ badSet γ Ψ false a} with hBx
  have hq : qBoundaryMeasure γ (normField γ gffBase.X ω) Bx = 0 := by
    have hsub : Bx ⊆ (Bx ∩ Ioo (-1 : ℝ) 1) ∪
        {x | ¬(1 ≤ x → LocCertC γ (g3coordsM γ 0 Ψ false (normField γ gffBase.X ω, a, 1, x)))} := by
      intro x hx
      by_cases h1 : x < 1
      · exact Or.inl ⟨hx, by linarith [badSet_pos _ hx], h1⟩
      · refine Or.inr fun h => hx.2 ?_
        rw [g3coordsM_reconstruct_coords]
        exact h (not_lt.1 h1)
    refine measure_mono_null hsub (measure_union_null ?_ (ae_iff.1 hfar))
    rw [← Measure.restrict_apply' measurableSet_Ioo]
    exact measure_mono_null (fun x hx => not_not_intro hx) (ae_iff.1 hω)
  show (bdryM γ (restrictField (circOut i.t₁ i.r₁ i.t₂ i.r₂) (g3pField γ 0 ω)) +
    bdryM γ (restrictField (circIn i.t₂ i.r₂) (g3pField γ 0 ω))) _ = 0
  rw [g3pField_zero]
  exact partner_meas_null hγ hv hfin hat i hq

end ZqT
end Thm18Asm
end QuantumZipper
