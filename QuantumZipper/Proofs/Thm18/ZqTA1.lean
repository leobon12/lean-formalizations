import QuantumZipper.Proofs.Thm18.ZqT8Partner
import QuantumZipper.Proofs.Thm18.G3ZqL20TypQ
import QuantumZipper.Proofs.Thm18.G3ZqL10Cert
import QuantumZipper.Proofs.GFF.CircleContinuity
import QuantumZipper.Proofs.Thm18.G3ZqL11Reg
import QuantumZipper.Proofs.Thm18.G3ZqTop
import QuantumZipper.Proofs.Thm18.G3ZqPath
import QuantumZipper.Proofs.Thm18.G3ZqFLeaf
import QuantumZipper.Proofs.Thm18.G3ZqG3LRegG
import QuantumZipper.Proofs.Thm18.G3ZqG3Unif
import QuantumZipper.Proofs.Thm18.G3ZqSTop
import QuantumZipper.Proofs.Thm18.G3ZqS2Top
import QuantumZipper.Proofs.Thm18.G3ZqO7CoreD
import QuantumZipper.Proofs.Thm18.G3ZqL14RegU
import QuantumZipper.Proofs.Thm18.ZqR2Palm
import QuantumZipper.Proofs.Thm18.R18G3TCM6
import QuantumZipper.Proofs.Thm18.R18G3TXSide3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-TYP (A1): the Palm point of the schemes `B` and `C` is typical

The Palm law of a scheme is a Lebesgue mixture in the Palm length `ℓ ∈ (0, ν[−δ, 0]]`
(`g3pPalmLaw_apply_eq_lebesgue`), and the Palm point `X = lenLeft ν ℓ` is the left quantile
transform of `ν = ν₁ + ν₀`: it pushes Lebesgue measure on `(0, ν[−δ,0]]` to `ν|[−δ,0]`
(`map_lenLeft_restrict_Ioc`). Hence a null event of `(coords h, X)` at the Palm law follows from
an a.s. statement at `ν|[−δ,0]`-a.e. point (`palm_null_of_ae`), and by fidelity (`ν = ν_h` on the
window) at `ν_h`-a.e. point.

* Scheme `C` (profile `−γ log|·|`): the field has the coordinates of `normX X + logSing`
  (`coords_g3pField_prof`), so the fixed-Palm-point node `G3ZqTVPalmStmt` gives it through the
  Palm transfer `ae_typ_of_palm_V` (`ae_prof_null`).
* Scheme `B` (profile `g3wCut`, a Cameron–Martin shift): the Palm integrals of `B` are the tilted
  Palm integrals of the free scheme (`lintegral_g3pField_eq_tilt`), so null events of the free
  scheme are null for `B` (`palmB_null`); the free scheme is handled by the proved fixed-point
  certificate `ZqR.g3ZqLPalmCertStmt_holds` and the free Palm transfer `ae_hν_of_palm_null`
  (`ae_free_null`).

Duplantier–Sheffield, arXiv:0808.1560, §3.3 (rooted measure); Sheffield, arXiv:1012.4797, proof
of Prop. 5.5, p. 65 ("once we condition on `x`"); Cameron–Martin tilt as in Berestycki–Powell,
arXiv:2004.04720, Lemma 3.12. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqT

open R18 PalmNorm G3Zq G3Z2b2 G3ZqL Factorization

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- The left quantile transform does not charge null sets of `ν|[−δ,0]`. -/
theorem vol_lenLeft_null {m : Measure ℝ} {δ : ℝ} (hδ : 0 < δ) (hfin : ∀ b : ℝ, m (Icc b 0) ≠ ⊤)
    {T : Set ℝ} (hT : m.restrict (Icc (-δ) 0) T = 0) :
    volume ({ℓ | lenLeft m ℓ ∈ T} ∩ Ioc 0 (m (Icc (-δ) 0)).toReal) = 0 := by
  set T' := toMeasurable (m.restrict (Icc (-δ) 0)) T with hT'
  have hT'm : MeasurableSet T' := measurableSet_toMeasurable _ _
  have hT'0 : m.restrict (Icc (-δ) 0) T' = 0 := by rw [hT', measure_toMeasurable]; exact hT
  have hmap := map_lenLeft_restrict_Ioc (m := m) hδ hfin
  have h1 : volume (lenLeft m ⁻¹' T' ∩ Ioc 0 (m (Icc (-δ) 0)).toReal) = 0 := by
    rw [← Measure.restrict_apply (measurable_lenLeft_left m hT'm),
      ← Measure.map_apply (measurable_lenLeft_left m) hT'm, hmap]
    exact hT'0
  exact measure_mono_null (inter_subset_inter_left _ (preimage_mono (subset_toMeasurable _ _))) h1

/-- **Palm null events from a.s. `ν|[−δ,0]`-null events.** -/
theorem palm_null_of_ae {γ : ℝ} {g : ℂ → ℝ} {i : G3Idx} (hZ : 0 < g3pZ γ g i ∧ g3pZ γ g i < ⊤)
    {Bd : Set ((ℕ → ℝ) × ℝ)} (hBd : MeasurableSet Bd)
    (h : ∀ᵐ ω ∂gffBase.P, (g3pν₁ γ g i ω + g3pν₀ γ g i ω).restrict (Icc (-i.δ) 0)
      {x | (coords (g3pField γ g ω), x) ∈ Bd} = 0) :
    g3pPalmLaw γ g i {p | (coords (g3pField γ g p.1), g3pX γ g i p) ∈ Bd} = 0 := by
  have hXm : Measurable (g3pX γ g i) := (measurable_g3pX γ g i).mono (sig_le_g3 i _ _) le_rfl
  have hS : MeasurableSet {p : gffBase.Ω × ℝ | (coords (g3pField γ g p.1), g3pX γ g i p) ∈ Bd} :=
    (((measurable_coords.comp (measurable_g3pField γ g)).comp measurable_fst).prodMk hXm) hBd
  rw [g3pPalmLaw_apply_eq_lebesgue γ g i hZ hS]
  have hδ : 0 < i.δ := i.hη.trans i.hηδ
  have h0 : (fun ω => volume ({ℓ | (ω, ℓ) ∈
      {p : gffBase.Ω × ℝ | (coords (g3pField γ g p.1), g3pX γ g i p) ∈ Bd}} ∩
        Ioc 0 (g3pMass γ g i ω).toReal)) =ᵐ[gffBase.P] 0 := by
    filter_upwards [h] with ω hω
    exact vol_lenLeft_null (m := g3pν₁ γ g i ω + g3pν₀ γ g i ω) hδ
      (fun b => (g3pm_Icc_lt_top γ g i ω b 0).ne)
      (T := {x | (coords (g3pField γ g ω), x) ∈ Bd}) hω
  rw [lintegral_congr_ae h0]
  simp

/-- The certificate gives the local area. -/
theorem locArea_of_not_bad {γ : ℝ} {side : Bool} {a : ℝ≥0 → ℝ} {y : FieldSample} {x : ℝ}
    (h : (coords y, x) ∉ badSet γ Ψ side a) (hx : x ∈ g1SideHalf side) :
    LocAreaQ γ (g3zqPull γ Ψ side a y x) := by
  have hc : LocCertC γ (g3coordsM γ 0 Ψ side (y, a, 1, x)) := by
    by_contra hn
    exact h ⟨hx, by rw [g3coordsM_reconstruct_coords]; exact hn⟩
  exact locAreaQ_of_locCertC hc

/-- From a Palm-null bad event to the Palm-a.e. local area. -/
theorem ae_palm_side_of_null {γ : ℝ} {g : ℂ → ℝ} {i : G3Idx} {side : Bool} {a : ℝ≥0 → ℝ}
    {F : gffBase.Ω × ℝ → ℝ}
    (h0 : g3pPalmLaw γ g i {p | (coords (g3pField γ g p.1), F p) ∈ badSet γ Ψ side a} = 0) :
    ∀ᵐ p ∂(g3pPalmLaw γ g i), F p ∈ g1SideHalf side →
      LocAreaQ γ (g3zqPull γ Ψ side a (g3pField γ g p.1) (F p)) := by
  rw [ae_iff]
  refine measure_mono_null (fun p hp => ?_) h0
  by_contra hn
  exact hp fun hs => locArea_of_not_bad hn hs

/-! ## The free scheme -/

/-- **The free field: a.s. no bad points on `[−δ, 0]` for the Palm mass of any index.** -/
theorem ae_free_null {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ}
    (ha : G3ZqGoodPath γ a) (side : Bool) :
    ∀ᵐ ω ∂gffBase.P, ∀ i : G3Idx, (g3pν₁ γ 0 i ω + g3pν₀ γ 0 i ω).restrict (Icc (-i.δ) 0)
      {x | (coords (g3pField γ 0 ω), x) ∈ badSet γ Ψ side a} = 0 := by
  have hab : Icc (-1 : ℝ) 1 ⊆ Icc (-((1 : ℕ) : ℝ)) ((1 : ℕ) : ℝ) := by simp
  have hPal : ∀ᵐ x ∂(volume.restrict (Ioo (-1 : ℝ) 1)), ∀ᵐ ω ∂gffBase.P,
      (coords (normField γ (xPalm γ x) ω), x) ∉ badSet γ Ψ side a := by
    filter_upwards [ZqR.g3ZqLPalmCertStmt_holds γ hγ hγ2 Ψ hsel a ha side] with x hx
    by_cases hxs : x ∈ g1SideHalf side
    · filter_upwards [hx hxs] with ω hω
      intro hb
      exact hb.2 (by rw [g3coordsM_reconstruct_coords]; exact hω)
    · exact Eventually.of_forall fun ω hb => hxs hb.1
  have hT := ae_hν_of_palm_null hγ hγ2 (measurableSet_badSet hsel side a) hab hPal
  filter_upwards [hT, ae_g3Fid_sets hγ hγ2] with ω hω hF i
  have hsub : Icc (-i.δ) 0 ⊆ Ioo (-i.δ - i.η / 4) (3 * i.η / 4) :=
    Icc_neg_subset_win i (by linarith [i.hη])
  have hsub2 : Icc (-i.δ) 0 ⊆ Ioo (-1 : ℝ) 1 := fun z hz =>
    ⟨by linarith [hz.1, i.hδ], by linarith [hz.2]⟩
  have e1 : g3pν₁ γ 0 i ω + g3pν₀ γ 0 i ω = g3ν₁ γ i ω + g3ν₀ γ i ω := by
    simp only [g3pν₁, g3pν₀, g3pField_zero]; rfl
  rw [e1, g3pField_zero, Measure.restrict_apply' measurableSet_Icc,
    (hF i).1 _ (inter_subset_right.trans hsub)]
  refine measure_mono_null (inter_subset_inter_right _ hsub2) ?_
  rw [← Measure.restrict_apply' measurableSet_Ioo]
  exact measure_mono_null (fun x hx => not_not_intro hx) (ae_iff.1 hω)

/-! ## Scheme `B` by the Cameron–Martin tilt -/

/-- **Null events of the free scheme are null for scheme `B`.** -/
theorem palmB_null {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {Bd : Set ((ℕ → ℝ) × ℝ)}
    (hBd : MeasurableSet Bd)
    (hA : ∀ᵐ ω ∂gffBase.P, (g3pν₁ γ 0 i ω + g3pν₀ γ 0 i ω).restrict (Icc (-i.δ) 0)
      {x | (coords (g3pField γ 0 ω), x) ∈ Bd} = 0) :
    g3pPalmLaw γ (g3wCut γ i.η) i
      {p | (coords (g3pField γ (g3wCut γ i.η) p.1), g3pX γ (g3wCut γ i.η) i p) ∈ Bd} = 0 := by
  have hZB := g3pBZ_pos_lt_top hγ hγ2 i
  have hZA : 0 < g3pZ γ 0 i ∧ g3pZ γ 0 i < ⊤ := by rw [g3pZ_zero]; exact g3Z_pos_lt_top hγ hγ2 i
  have hA0 := palm_null_of_ae hZA hBd hA
  set S₀ : Set (FieldSample × ℝ) := {q | (coords q.1, sX γ i q) ∈ Bd} with hS₀def
  have hS₀ : MeasurableSet S₀ :=
    ((measurable_coords.comp measurable_fst).prodMk (measurable_sX γ i)) hBd
  set Φ : FieldSample × ℝ → ℝ≥0∞ := S₀.indicator (sW0 γ i) with hΦdef
  have hΦ : Measurable Φ := (measurable_sW0 γ i).indicator hS₀
  have hloc : ∀ (x x' : FieldSample) (s : ℝ),
      (∀ μ : Measure ℂ, IsAdmissibleH μ → μ univ = 1 → x μ = x' μ) → Φ (x, s) = Φ (x', s) := by
    intro x x' s hxx
    have hfc : FcEq x x' := fun c ρ hρ =>
      hxx _ (D3Plus.isAdmissibleH_foldedCircle' c hρ) measure_univ
    have hc : coords x = coords x' := funext fun j => hfc _ _ (radius_pos _)
    have hmem : (x, s) ∈ S₀ ↔ (x', s) ∈ S₀ := by
      show (coords x, sX γ i (x, s)) ∈ Bd ↔ (coords x', sX γ i (x', s)) ∈ Bd
      rw [hc, sX_fc hfc γ i s]
    by_cases hx' : (x', s) ∈ S₀
    · rw [hΦdef, indicator_of_mem hx', indicator_of_mem (hmem.2 hx'), sW0_fc hfc γ i s]
    · rw [hΦdef, indicator_of_notMem hx', indicator_of_notMem (fun h => hx' (hmem.1 h))]
  have hT := lintegral_g3pField_eq_tilt γ (contDiff_g3wCut γ i.η i.hη)
    (hasCompactSupport_g3wCut γ i.η) (g3wCut_conj γ i.η) (g3wCut_unit γ i.η) hΦ hloc
  have hXB : Measurable (g3pX γ (g3wCut γ i.η) i) :=
    (measurable_g3pX γ _ i).mono (sig_le_g3 i _ _) le_rfl
  have hXA : Measurable (g3pX γ 0 i) := (measurable_g3pX γ _ i).mono (sig_le_g3 i _ _) le_rfl
  set SB := {p : gffBase.Ω × ℝ |
    (coords (g3pField γ (g3wCut γ i.η) p.1), g3pX γ (g3wCut γ i.η) i p) ∈ Bd} with hSBdef
  set SA := {p : gffBase.Ω × ℝ | (coords (g3pField γ 0 p.1), g3pX γ 0 i p) ∈ Bd} with hSAdef
  have hSB : MeasurableSet SB :=
    (((measurable_coords.comp (measurable_g3pField γ _)).comp measurable_fst).prodMk hXB) hBd
  have hSA : MeasurableSet SA :=
    (((measurable_coords.comp (measurable_g3pField γ _)).comp measurable_fst).prodMk hXA) hBd
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

end ZqT
end Thm18Asm
end QuantumZipper
