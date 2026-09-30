import QuantumZipper.Proofs.Thm18.R18G1ArcLenDet
import QuantumZipper.Proofs.Thm18.G4Rezip2Weld
import QuantumZipper.Proofs.Thm18.G4BSideLen
import QuantumZipper.Proofs.Zipper.LocLenR6cMono

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 T7c: the welding core of `Z^LEN_ℓ ∘ Z^LEN_{−ℓ}`, deterministic part (open arcs)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1), p. 26:
the inverse of `Z^LEN_{−ℓ}` is conformal welding by quantum length; this holds because the two
sides of every sub-arc `η[t − r, t]` of the unzipped segment have the same quantum length
(Theorem 1.8, §5.4 pp. 69–72; lengths read in the unzipped picture, §1.4).

Deterministic copy of `Thm18Asm.g4UpWeldBaseStmt_of` (G4Rezip2Base.lean) and
`Thm18Asm.G4Core.side_eq_of_cocycle` (G4BSideLen.lean) with open-arc lengths (D75): the side
lengths of the restarted unzipping are read with the open-arc lengths (`LocLen.arcLen`) of the
field `x_T` unzipped at `T`, and converted into the GLOBAL boundary measure of the rescaled field
`x' = rescale x_T Q a` by `R18.g1zArc_Ioo` (on arcs avoiding `{O⁻_T, 0, O⁺_T}`); `x'` is
globally good, atomless and charges open intervals (`BReg`, transferred by E6 in the a.s. part).
The welding homeomorphism is then identified by `Thm18Asm.weldingHom_eq_weldHomR_of`
(G4Rezip2Weld.lean) directly for the rescaled driver. Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm Thm18Asm.G4Core LocLen

/-- `0₋` of the rescaled time reversal at time `r ≤ T/a²`. -/
theorem zeroMinus_revDrv_of_le {W : ℝ → ℝ} (hWc : Continuous W) {T a r : ℝ} (hT : 0 ≤ T)
    (ha : 0 < a) (hr0 : 0 ≤ r) (hr : r ≤ (revDrv W T a).1) :
    zeroMinus (revDrv W T a).2 r = zeroMinus (B2.vrev W T) (a ^ 2 * r) / a := by
  rw [F2.zeroMinus_congr_drive ((revDrv_eqOn_vrev W hT ha).mono (Icc_subset_Icc_right hr))]
  have h := zeroMinus_scale (B2.continuous_vrev hWc T) ha (T := a ^ 2 * r) (by positivity)
  have e : a ^ 2 * r / a ^ 2 = r := by field_simp
  rwa [e] at h

/-- `0₊` of the rescaled time reversal at time `r ≤ T/a²`. -/
theorem zeroPlus_revDrv_of_le {W : ℝ → ℝ} (hWc : Continuous W) {T a r : ℝ} (hT : 0 ≤ T)
    (ha : 0 < a) (hr0 : 0 ≤ r) (hr : r ≤ (revDrv W T a).1) :
    zeroPlus (revDrv W T a).2 r = zeroPlus (B2.vrev W T) (a ^ 2 * r) / a := by
  rw [F2.zeroPlus_congr_drive ((revDrv_eqOn_vrev W hT ha).mono (Icc_subset_Icc_right hr))]
  have hV := B2.continuous_vrev hWc T
  have hV' : Continuous fun s => B2.vrev W T (a ^ 2 * s) / a :=
    (hV.comp (continuous_const.mul continuous_id)).div_const a
  rw [zeroPlus_eq_neg_zeroMinus_neg hV' hr0,
    zeroPlus_eq_neg_zeroMinus_neg hV (by positivity)]
  have h := zeroMinus_scale hV.neg ha (T := a ^ 2 * r) (by positivity)
  have e : a ^ 2 * r / a ^ 2 = r := by field_simp
  rw [e] at h
  have hf : (-fun s => B2.vrev W T (a ^ 2 * s) / a) = fun s => (-B2.vrev W T) (a ^ 2 * s) / a := by
    funext s; simp [neg_div]
  rw [hf, h, neg_div]

/-- **Welding core of `Z_ℓ ∘ Z_{−ℓ}`, deterministic, open arcs.** With `T` the open-arc length
time, `x = x_T` the unzipped field, `a > 0`, `x' = rescale x Q a` globally regular (`BReg`), the
pair cocycle, finiteness and equality of the open-arc lengths, the capacity field cocycle and the
Loewner facts of `V = vrev W T`: the base point of `revDrv W T a` is `lenWeldPoint x' ℓ` and its
welding homeomorphism is `R_{x'}`. -/
theorem weldCoreA_det {γ ℓ : ℝ} (hγ : 0 < γ) {c : FieldSample × (ℝ → ℝ)} {T a : ℝ}
    (hT : 0 < T) (ha : 0 < a) (hWc : Continuous c.2) (hW0 : c.2 0 = 0)
    (hK : IsSimpleCurveHull (revHull (revDrv c.2 T a).2 (revDrv c.2 T a).1))
    (hr : IsRegularSample (unzippedField γ c T)) {ν : Measure ℝ}
    (hν : HasBdryLimitOn γ (unzippedField γ c T) (offSet c.2 T)ᶜ ν)
    (hB : WedgeBdry.BReg γ (rescale (unzippedField γ c T) (Qc γ) a))
    (hpass : (unzipLengthsArc γ c T).1 = ENNReal.ofReal ℓ)
    (hcoc : ∀ u s : ℝ, 0 ≤ u → 0 ≤ s →
      (unzipLengthsArc γ c (u + s)).1 =
          (unzipLengthsArc γ c u).1 + (unzipLengthsArc γ (zipCapDown γ u c) s).1 ∧
        (unzipLengthsArc γ c (u + s)).2 =
          (unzipLengthsArc γ c u).2 + (unzipLengthsArc γ (zipCapDown γ u c) s).2)
    (hfin : ∀ t : ℝ, 0 ≤ t → (unzipLengthsArc γ c t).1 < ⊤)
    (hEq : ∀ t : ℝ, 0 ≤ t → (unzipLengthsArc γ c t).1 = (unzipLengthsArc γ c t).2)
    (hcap : UnzipCapRegData γ c)
    (hanti : StrictAntiOn (zeroMinus (B2.vrev c.2 T)) (Icc 0 T))
    (hO : (sideImages c.2 T).1 = zeroMinus (B2.vrev c.2 T) T)
    (hmono : StrictMonoOn (zeroPlus (B2.vrev c.2 T)) (Icc 0 T))
    (hOp : (sideImages c.2 T).2 = zeroPlus (B2.vrev c.2 T) T)
    (hsi : ∀ r ∈ Ioc (0 : ℝ) T,
      (sideImages (zipCapDown γ (T - r) c).2 r).1 = zeroMinus (B2.vrev c.2 T) r ∧
      (sideImages (zipCapDown γ (T - r) c).2 r).2 = zeroPlus (B2.vrev c.2 T) r) :
    zeroMinus (revDrv c.2 T a).2 (revDrv c.2 T a).1 =
        lenWeldPoint γ (rescale (unzippedField γ c T) (Qc γ) a) ℓ ∧
      ∀ s ∈ Icc (zeroMinus (revDrv c.2 T a).2 (revDrv c.2 T a).1) 0,
        weldingHom (revDrv c.2 T a).2 (revDrv c.2 T a).1 s =
          weldHomR γ (rescale (unzippedField γ c T) (Qc γ) a) s := by
  set V := B2.vrev c.2 T with hVdef
  set x := unzippedField γ c T with hxdef
  have : NullSingletonClass (qBoundaryMeasure γ (rescale x (Qc γ) a)) := ⟨hB.noAtom⟩
  have hm0 : (sideImages c.2 T).1 ≤ 0 := sideImages_fst_nonpos_of_cont hWc hW0 hT.le
  have hp0 : 0 ≤ (sideImages c.2 T).2 := sideImages_snd_nonneg_of_cont hWc hW0 hT.le
  have hconv : ∀ p q : ℝ, Ioo (a * p) (a * q) ⊆ (offSet c.2 T)ᶜ →
      qBoundaryMeasure γ (rescale x (Qc γ) a) (Icc p q) = arcLen γ x (a * p) (a * q) := by
    intro p q h
    rw [measure_congr Ioo_ae_eq_Icc.symm]
    exact g1zArc_Ioo hγ hr hν ha hB.1 h
  have hL : ∀ m : ℝ, (sideImages c.2 T).1 ≤ m → Ioo (a * (m / a)) (a * 0) ⊆ (offSet c.2 T)ᶜ := by
    intro m hm
    rw [mul_div_cancel₀ m ha.ne', mul_zero]
    exact fun u hu hmem => Set.disjoint_left.1
      ((Ioo_left_disjoint_offSet c.2 T hp0).mono_left (Ioo_subset_Ioo_left hm)) hu hmem
  have hR : ∀ p : ℝ, p ≤ (sideImages c.2 T).2 → Ioo (a * 0) (a * (p / a)) ⊆ (offSet c.2 T)ᶜ := by
    intro p hp
    rw [mul_div_cancel₀ p ha.ne', mul_zero]
    exact fun u hu hmem => Set.disjoint_left.1
      ((Ioo_right_disjoint_offSet c.2 T hm0).mono_left (Ioo_subset_Ioo_right hp)) hu hmem
  have eT : a ^ 2 * (revDrv c.2 T a).1 = T := by simp only [revDrv]; field_simp
  have hq0 : 0 < (revDrv c.2 T a).1 := by simp only [revDrv]; positivity
  have hzT : zeroMinus (revDrv c.2 T a).2 (revDrv c.2 T a).1 = (sideImages c.2 T).1 / a := by
    rw [zeroMinus_revDrv_of_le hWc hT.le ha hq0.le le_rfl, eT, hO]
  refine ⟨?_, ?_⟩
  · rw [hzT]
    symm
    refine lenWeldPoint_eq_of_exact (div_nonpos_iff.2 (Or.inr ⟨hm0, ha.le⟩)) ?_
      fun v hv _ => hB.pos hv
    rw [hconv _ _ (hL _ le_rfl), mul_div_cancel₀ _ ha.ne', mul_zero]
    exact hpass
  · refine weldingHom_eq_weldHomR_of (by simp only [revDrv]; fun_prop) (by simp [revDrv]) hq0
      hK ?_ fun v w _ hvw => hB.pos hvw
    intro r hr
    have hr' : a ^ 2 * r ∈ Ioc (0 : ℝ) T := by
      refine ⟨mul_pos (pow_pos ha 2) hr.1, ?_⟩
      rw [← eT]
      exact mul_le_mul_of_nonneg_left hr.2 (by positivity)
    rw [zeroMinus_revDrv_of_le hWc hT.le ha hr.1.le hr.2,
      zeroPlus_revDrv_of_le hWc hT.le ha hr.1.le hr.2]
    set r' := a ^ 2 * r with hr'def
    have hmle : (sideImages c.2 T).1 ≤ zeroMinus V r' := by
      rw [hO]; exact hanti.antitoneOn ⟨hr'.1.le, hr'.2⟩ ⟨hT.le, le_rfl⟩ hr'.2
    have hple : zeroPlus V r' ≤ (sideImages c.2 T).2 := by
      rw [hOp]; exact hmono.monotoneOn ⟨hr'.1.le, hr'.2⟩ ⟨hT.le, le_rfl⟩ hr'.2
    rw [hconv _ _ (hL _ hmle), hconv _ _ (hR _ hple), mul_div_cancel₀ _ ha.ne',
      mul_div_cancel₀ _ ha.ne', mul_zero]
    have hu : 0 ≤ T - r' := by linarith [hr'.2]
    have hcapT := hcap (T - r') r' hu hr'.1.le
    rw [sub_add_cancel] at hcapT
    obtain ⟨h1, h2⟩ := hcoc (T - r') r' hu hr'.1.le
    rw [sub_add_cancel] at h1 h2
    have e1 : (unzipLengthsArc γ (zipCapDown γ (T - r') c) r').1 = arcLen γ x (zeroMinus V r') 0 := by
      show arcLen γ (unzippedField γ (zipCapDown γ (T - r') c) r')
        (sideImages (zipCapDown γ (T - r') c).2 r').1 0 = _
      rw [(hsi r' hr').1, arcLen_congr (B3d.avgReg_eq_of_regEq hcapT)]
    have e2 : (unzipLengthsArc γ (zipCapDown γ (T - r') c) r').2 = arcLen γ x 0 (zeroPlus V r') := by
      show arcLen γ (unzippedField γ (zipCapDown γ (T - r') c) r') 0
        (sideImages (zipCapDown γ (T - r') c).2 r').2 = _
      rw [(hsi r' hr').2, arcLen_congr (B3d.avgReg_eq_of_regEq hcapT)]
    rw [← e1, ← e2]
    have key : (unzipLengthsArc γ c (T - r')).1 + (unzipLengthsArc γ (zipCapDown γ (T - r') c) r').1 =
        (unzipLengthsArc γ c (T - r')).1 + (unzipLengthsArc γ (zipCapDown γ (T - r') c) r').2 := by
      rw [← h1, hEq T hT.le, h2, hEq (T - r') hu]
    exact (ENNReal.add_right_inj (hfin (T - r') hu).ne).1 key

end R18
end QuantumZipper
