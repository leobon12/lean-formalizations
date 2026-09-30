import QuantumZipper.Proofs.Thm18.ZqTA1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-TYP (A2): scheme `C` and the partner point

* `coords_g3pField_prof`: the scheme-`C` field `normField + ofFun (−γ log|·|)` has the dyadic
  coordinates of `normX X + logSing` (`(2/γ) − γ = −(γ − 2/γ)`).
* `ae_V_bad_of_palm`: the badSet form of `ae_V_side_of_palm` (Palm transfer, windows exhausting
  the side half-line).
* The partner `R = lenRight (ν₀ + ν₂) ℓ`: the right quantile does not charge null sets
  (`vol_lenRight_null`, as in `partner_ae_not_mem`), and `ν₀ + ν₂ ≪ ν_h` on the whole line since
  both pieces are restrictions of `ν_h` (`G3Fid.regionCut`, `G3Fid.gapCut`;
  `partner_meas_null`). Hence `palm_nullR_of_ae`.

Sheffield, arXiv:1012.4797, proof of Prop. 5.5, p. 65; Duplantier–Sheffield, arXiv:0808.1560,
§3.3. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqT

open R18 PalmNorm G3Zq G3Z2b2 G3ZqL Factorization

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- **The scheme-`C` field has the coordinates of `normX X + logSing`.** -/
theorem coords_g3pField_prof {γ : ℝ} (hγ : 0 < γ) (ω : gffBase.Ω) :
    coords (g3pField γ (g3wProf γ) ω) =
      coords (normX gffBase.X ω + F2.logSingField (γ ^ 2)) := by
  funext j
  simp only [coords, g3pField, normField, Pi.add_apply]
  rw [normX_of_prob, g3pl4_logSingField_eq hγ]
  simp only [ofFun, h0rev, g3wProf, LogSingGood.Lf, integral_const_mul, integral_neg,
    Real.sqrt_sq hγ.le]
  ring

/-- **Badset form of the Palm transfer for `V + logSing`.** -/
theorem ae_V_bad_of_palm {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hsel : G1PsiSel γ Ψ)
    {a : ℝ≥0 → ℝ} (side : Bool) {Ω'' : Type} [MeasurableSpace Ω'']
    {P'' : Measure Ω''} [IsProbabilityMeasure P''] {V : Ω'' → FieldSample}
    (hV : IsFreeGFFModConstH V P'') (hV0 : ∀ᵐ ω ∂P'', V ω (foldedCircle 0 1) = 0)
    (hP : ∀ᵐ x ∂(volume.restrict (g1SideHalf side)), ∀ᵐ ω ∂P'',
      LocCertC γ (g3coordsM γ 0 Ψ side
        (normAt g3zS (ofFun (shiftFun γ (LogSingGood.Lf (γ - 2 / γ)) g3zS x) + V ω), a, 1, x))) :
    ∀ᵐ ω ∂P'', qBoundaryMeasure γ (V ω + F2.logSingField (γ ^ 2))
      {x | (coords (V ω + F2.logSingField (γ ^ 2)), x) ∈ badSet γ Ψ side a} = 0 := by
  obtain ⟨J, hJ, hU⟩ := side_windows side
  have hn : ∀ n, ∀ᵐ ω ∂P'', ∀ᵐ x ∂((qBoundaryMeasure γ
      (V ω + F2.logSingField (γ ^ 2))).restrict (J n)),
      (coords (V ω + F2.logSingField (γ ^ 2)), x) ∉ badSet γ Ψ side a := by
    intro n
    obtain ⟨a', b', N, hJn, hsub, h0⟩ := hJ n
    rw [hJn]
    refine ae_typ_of_palm_V hγ hγ2 hV hV0 (measurableSet_badSet hsel side a) hsub h0 ?_
    have hJs : Ioo a' b' ⊆ g1SideHalf side := by
      rw [← hJn, ← hU]; exact subset_iUnion J n
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hJs hP] with x hx
    filter_upwards [hx] with ω hω
    intro hb
    exact hb.2 (by rw [g3coordsM_reconstruct_coords]; exact hω)
  filter_upwards [ae_all_iff.2 hn] with ω hω
  have hall : ∀ᵐ x ∂((qBoundaryMeasure γ (V ω + F2.logSingField (γ ^ 2))).restrict (⋃ n, J n)),
      (coords (V ω + F2.logSingField (γ ^ 2)), x) ∉ badSet γ Ψ side a :=
    (ae_restrict_iUnion_iff _ _).2 hω
  rw [hU, ae_restrict_iff' (msSide side)] at hall
  rw [← ae_iff.1 hall]
  refine congrArg _ (Set.ext fun x => ⟨fun hb => ?_, fun hb => ?_⟩)
  · exact fun h => h hb.1 hb
  · by_contra hn'
    exact hb fun _ => hn'

/-- **Scheme `C`, Palm point: a.s. no bad points on `[−δ, 0]`.** -/
theorem ae_prof_null {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ}
    (side : Bool)
    (hP : ∀ᵐ x ∂(volume.restrict (g1SideHalf side)), ∀ᵐ ω ∂gffBase.P,
      LocCertC γ (g3coordsM γ 0 Ψ side (normAt g3zS (ofFun (shiftFun γ
        (LogSingGood.Lf (γ - 2 / γ)) g3zS x) + normX gffBase.X ω), a, 1, x))) :
    ∀ᵐ ω ∂gffBase.P, qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω)
      {x | (coords (g3pField γ (g3wProf γ) ω), x) ∈ badSet γ Ψ side a} = 0 := by
  have hV := isFreeGFFModConstH_normX gffBase.gff
  have hV0 : ∀ᵐ ω ∂gffBase.P, normX gffBase.X ω (foldedCircle 0 1) = 0 :=
    Eventually.of_forall fun ω => normX_refS _ ω
  filter_upwards [ae_V_bad_of_palm hγ hγ2 hsel side hV hV0 hP] with ω hω
  have hq : qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω) =
      qBoundaryMeasure γ (normX gffBase.X ω + F2.logSingField (γ ^ 2)) := by
    rw [← WedgeBdry.qBoundaryMeasure_reconstruct γ (g3pField γ (g3wProf γ) ω),
      coords_g3pField_prof hγ, WedgeBdry.qBoundaryMeasure_reconstruct]
  rw [hq, coords_g3pField_prof hγ]
  exact hω

/-- The Palm measure `ν₁ + ν₀` restricted to `[−δ, 0]` does not charge `ν_h`-null sets. -/
theorem left_restrict_null {γ : ℝ} {g : ℂ → ℝ} {i : G3Idx} {ω : gffBase.Ω}
    (hF : ∀ s ⊆ Ioo (-i.δ - i.η / 4) (3 * i.η / 4),
      (g3pν₁ γ g i ω + g3pν₀ γ g i ω) s = qBoundaryMeasure γ (g3pField γ g ω) s)
    {T : Set ℝ} (hT : qBoundaryMeasure γ (g3pField γ g ω) T = 0) :
    (g3pν₁ γ g i ω + g3pν₀ γ g i ω).restrict (Icc (-i.δ) 0) T = 0 := by
  have hsub : Icc (-i.δ) 0 ⊆ Ioo (-i.δ - i.η / 4) (3 * i.η / 4) :=
    Icc_neg_subset_win i (by linarith [i.hη])
  rw [Measure.restrict_apply' measurableSet_Icc, hF _ (inter_subset_right.trans hsub)]
  exact measure_mono_null inter_subset_left hT

/-! ## The partner point -/

/-- The right quantile does not charge null subsets of `(0, ∞)`. -/
theorem vol_lenRight_null {m : Measure ℝ} (hfin0 : ∀ b : ℝ, m (Icc 0 b) ≠ ⊤) {T : Set ℝ}
    (hTpos : T ⊆ Ioi 0) (hT : m T = 0) :
    volume {ℓ : ℝ | 0 < ℓ ∧ lenRight m ℓ ∈ T} = 0 := by
  set S' := toMeasurable m T ∩ Ioi 0 with hS'
  have hS'm : MeasurableSet S' := (measurableSet_toMeasurable m T).inter measurableSet_Ioi
  have hS'0 : m S' = 0 :=
    measure_mono_null inter_subset_left (by rw [measure_toMeasurable]; exact hT)
  have hmeas : Measurable (lenRight m) :=
    measurable_lenRight.comp (measurable_const.prodMk measurable_id)
  have hsub : {ℓ : ℝ | 0 < ℓ ∧ lenRight m ℓ ∈ T} ⊆
      ⋃ K : ℕ, Ioc 0 (m (Icc 0 ((K : ℝ) + 1))).toReal ∩ lenRight m ⁻¹' S' := by
    rintro ℓ ⟨hℓ, hℓT⟩
    obtain ⟨K, hK⟩ := exists_nat_of_lenRight_pos (hTpos hℓT)
    refine mem_iUnion.2 ⟨K, ⟨hℓ, ?_⟩, subset_toMeasurable m T hℓT, hTpos hℓT⟩
    rw [← ENNReal.ofReal_le_iff_le_toReal (hfin0 _)]
    exact hK.trans (measure_mono (Icc_subset_Icc_right (by linarith)))
  refine measure_mono_null hsub (measure_iUnion_null fun K => ?_)
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  rw [inter_comm, ← Measure.restrict_apply (hmeas hS'm), ← Measure.map_apply hmeas hS'm,
    map_lenRight_restrict_Ioc hK hfin0, Measure.restrict_apply hS'm]
  exact measure_mono_null inter_subset_left hS'0

theorem g3pm2_Icc_lt_top (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) (ω : gffBase.Ω) (a b : ℝ) :
    (g3pν₀ γ g i ω + g3pν₂ γ g i ω) (Icc a b) < ⊤ := by
  have h₁ := Measure.le_iff'.1 (bdryM_le_qBoundaryMeasure γ
    (restrictField (circOut i.t₁ i.r₁ i.t₂ i.r₂) (g3pField γ g ω))) (Icc a b)
  have h₂ := Measure.le_iff'.1 (bdryM_le_qBoundaryMeasure γ
    (restrictField (circIn i.t₂ i.r₂) (g3pField γ g ω))) (Icc a b)
  rw [Measure.add_apply]
  exact ENNReal.add_lt_top.2
    ⟨h₁.trans_lt (qBoundaryMeasure_Icc_lt_top γ _ _ _),
      h₂.trans_lt (qBoundaryMeasure_Icc_lt_top γ _ _ _)⟩

/-- **Palm null events at the partner from a.s. `ν₀ + ν₂`-null events.** -/
theorem palm_nullR_of_ae {γ : ℝ} {g : ℂ → ℝ} {i : G3Idx} (hZ : 0 < g3pZ γ g i ∧ g3pZ γ g i < ⊤)
    {Bd : Set ((ℕ → ℝ) × ℝ)} (hBd : MeasurableSet Bd) (hpos : ∀ q ∈ Bd, (0 : ℝ) < q.2)
    (h : ∀ᵐ ω ∂gffBase.P, (g3pν₀ γ g i ω + g3pν₂ γ g i ω)
      {x | (coords (g3pField γ g ω), x) ∈ Bd} = 0) :
    g3pPalmLaw γ g i {p | (coords (g3pField γ g p.1), g3pR γ g i p) ∈ Bd} = 0 := by
  have hRm : Measurable (g3pR γ g i) := (measurable_g3pR γ g i).mono (sig_le_g3 i _ _) le_rfl
  have hS : MeasurableSet {p : gffBase.Ω × ℝ | (coords (g3pField γ g p.1), g3pR γ g i p) ∈ Bd} :=
    (((measurable_coords.comp (measurable_g3pField γ g)).comp measurable_fst).prodMk hRm) hBd
  rw [g3pPalmLaw_apply_eq_lebesgue γ g i hZ hS]
  have h0 : (fun ω => volume ({ℓ | (ω, ℓ) ∈
      {p : gffBase.Ω × ℝ | (coords (g3pField γ g p.1), g3pR γ g i p) ∈ Bd}} ∩
        Ioc 0 (g3pMass γ g i ω).toReal)) =ᵐ[gffBase.P] 0 := by
    filter_upwards [h] with ω hω
    refine measure_mono_null ?_ (vol_lenRight_null
      (m := g3pν₀ γ g i ω + g3pν₂ γ g i ω) (fun b => (g3pm2_Icc_lt_top γ g i ω 0 b).ne)
      (T := {x | (coords (g3pField γ g ω), x) ∈ Bd}) (fun x hx => hpos _ hx) hω)
    intro ℓ hℓ
    exact ⟨hℓ.2.1, hℓ.1⟩
  rw [lintegral_congr_ae h0]
  simp

/-- **`ν₀ + ν₂ ≪ ν_h`** (both pieces are restrictions of `ν_h`). -/
theorem partner_meas_null {γ : ℝ} (hγ : 0 < γ) {y : FieldSample}
    (hv : IsVagueLimitR (bdryApprox γ y) (qBoundaryMeasure γ y))
    (hfin : ∀ k, IsFiniteMeasureOnCompacts (bdryApprox γ y k))
    (hat : ∀ s, qBoundaryMeasure γ y {s} = 0) (i : G3Idx) {T : Set ℝ}
    (hT : qBoundaryMeasure γ y T = 0) :
    (bdryM γ (restrictField (circOut i.t₁ i.r₁ i.t₂ i.r₂) y) +
      bdryM γ (restrictField (circIn i.t₂ i.r₂) y)) T = 0 := by
  obtain ⟨-, e2⟩ := G3Fid.regionCut hγ hv hfin hat (t := i.t₂) i.r₂_pos
  obtain ⟨-, e0⟩ := G3Fid.gapCut hγ hv hfin hat (t₁ := i.t₁) (t₂ := i.t₂) i.r₁_pos i.r₂_pos
  have h0 : bdryM γ (restrictField (circOut i.t₁ i.r₁ i.t₂ i.r₂) y) T = 0 :=
    nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 (bdryM_le_qBoundaryMeasure γ _) T).trans
      (le_of_eq (by rw [e0]; exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self hT)))
  have h2 : bdryM γ (restrictField (circIn i.t₂ i.r₂) y) T = 0 :=
    nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 (bdryM_le_qBoundaryMeasure γ _) T).trans
      (le_of_eq (by rw [e2]; exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self hT)))
  rw [Measure.add_apply, h0, h2, add_zero]

end ZqT
end Thm18Asm
end QuantumZipper
