import QuantumZipper.Proofs.Zipper.LocLenR6cCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75 / R6h (1): the local boundary measures of the unzipped fields have no atoms off the root
images, at all times (`Γ⁰`, `x`, unscaled wedge and `P_*` pictures)

Sheffield arXiv:1012.4797 p. 56 (quantum boundary length is an atomless measure on the boundary
arcs) and §5.4 rule (5.1); Berestycki–Powell arXiv:2404.16642 Def 6.41 p. 229, Def 8.12 p. 281.

The chain is the atomless copy of the open-arc positivity chain of R8a (`LocLenPosY`,
`LocLenPosMain`: `ae_posOff_unzY` → `ae_posOff_unzX` → `wedgePosOffAll_of_yGood` →
`pStarPosOff_of_core`), with `PosOff` replaced by `AtomOff`:

* `AtomOff γ x S`: `x` has a local boundary limit `ν` off the closed set `S` with no atom off `S`.
  Transfer rules: coordinates, enlarging `S`, rule (5.1) (a density measure of an atomless
  measure is atomless), rescaling.
* `ae_atomOff_unzY`: at the `Γ⁰` level, the local limit of `y_t` off the tip agrees on every
  rational window avoiding `0` with the atomless window limit of the proved uniform off-tip
  statement `RegUnif.unifOffTipAllStmt_of_extAll` (the same input as `yGoodOffAll_of_extAll`),
  by uniqueness of local limits.
* then `x_t` (rule (5.1)), the unscaled wedge, and `P_*` (rescaling), as in R8a.
Bookkeeping own (as in the copied proofs).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- `x` has a local boundary limit off the closed set `S` without atoms off `S`. -/
def AtomOff (γ : ℝ) (x : FieldSample) (S : Set ℝ) : Prop :=
  ∃ ν : Measure ℝ, HasBdryLimitOn γ x Sᶜ ν ∧ ∀ p : ℝ, p ∉ S → ν {p} = 0

variable {γ : ℝ} {x : FieldSample} {S : Set ℝ}

theorem AtomOff.congr_coords {y : FieldSample}
    (h : Factorization.coords x = Factorization.coords y) (hy : AtomOff γ y S) :
    AtomOff γ x S := by
  obtain ⟨ν, hν, hat⟩ := hy
  have havg : avgReg x = avgReg y := by
    rw [← Factorization.avgReg_reconstruct_coords x, h, Factorization.avgReg_reconstruct_coords]
  exact ⟨ν, (hasBdryLimitOn_congr_avg havg).2 hν, hat⟩

theorem AtomOff.mono {S' : Set ℝ} (hx : AtomOff γ x S) (hS' : IsClosed S') (hSS' : S ⊆ S') :
    AtomOff γ x S' := by
  obtain ⟨ν, hν, hat⟩ := hx
  exact ⟨_, hν.mono hS'.isOpen_compl (compl_subset_compl.2 hSS'), fun p hp =>
    nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans (hat p fun h => hp (hSS' h)).le)⟩

theorem AtomOff.add_ofFun (hx : IsRegularSample x) (hS : IsClosed S) (h : AtomOff γ x S)
    {φ : ℂ → ℝ} {W : Set ℂ} (hW : IsOpen W) (hUW : ∀ t ∈ Sᶜ, (t : ℂ) ∈ W)
    (hφ : ContinuousOn φ (W ∩ Hbar)) : AtomOff γ (x + ofFun φ) S := by
  obtain ⟨ν, hν, hat⟩ := h
  exact ⟨_, hν.add_ofFun hx hS.isOpen_compl hW hUW hφ, fun p hp =>
    withDensity_absolutelyContinuous _ _ (hat p hp)⟩

theorem AtomOff.rescale (hx : IsRegularSample x) (hγ : 0 < γ) (h : AtomOff γ x S) {a : ℝ}
    (ha : 0 < a) : AtomOff γ (rescale x (Qc γ) a) ((fun u => a * u) ⁻¹' S) := by
  obtain ⟨ν, hν, hat⟩ := h
  refine ⟨_, by rw [← preimage_compl]; exact hν.rescale hx hγ ha, fun p hp => ?_⟩
  have hpre : (fun x : ℝ => x / a) ⁻¹' {p} = {p * a} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, div_eq_iff ha.ne']
  rw [Measure.map_apply (f := fun x : ℝ => x / a) (by fun_prop) (measurableSet_singleton p), hpre]
  exact hat _ fun h' => hp (by simpa [mem_preimage, mul_comm] using h')

open B2 B5

/-- **`Γ⁰` fields: no atoms off the tip, at all times.** -/
theorem ae_atomOff_unzY (hYG : YGoodOffAllStmt) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hI : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → AtomOff (Real.sqrt κ) (F2.unzY κ (X ω) (drive κ B ω) t) {0} := by
  have hUO := RegUnif.unifOffTipAllStmt_of_extAll hκ hκ4 hB hX hI
    (E5.extAllInput_holds κ P B X hκ hκ4 hB hX hI)
  have hy := F2.ae_forall_nonneg_of_horizons (P := P) (Q := fun s ω =>
      ∀ u v : ℚ, (0 : ℝ) ∉ Icc (u : ℝ) v →
        ∃ ν, IsVagueLimitOnR (Ioo (u : ℝ) v) (bdryApprox (Real.sqrt κ) (B2.h0f κ s B X ω)) ν ∧
          ∀ x, ν {x} = 0)
    fun n => hUO _ (Nat.cast_add_one_pos n)
  filter_upwards [hy, hYG κ hκ hκ4 P B X hB hX hI] with ω hyω hyg t ht
  obtain ⟨hreg, ⟨ν, hν⟩, -⟩ := hyg t ht
  refine ⟨ν, hν, fun p hp => ?_⟩
  have hp0 : p ≠ 0 := fun h => hp (by simp [h])
  -- a rational window around `p` avoiding `0`
  obtain ⟨u, v, hu, hv, h0⟩ : ∃ u v : ℚ, (u : ℝ) < p ∧ p < v ∧ (0 : ℝ) ∉ Icc (u : ℝ) v := by
    rcases lt_or_gt_of_ne hp0 with hlt | hgt
    · obtain ⟨u, hu⟩ := exists_rat_lt p
      obtain ⟨v, hv1, hv2⟩ := exists_rat_btwn hlt
      exact ⟨u, v, hu, hv1, fun h => (not_le.2 hv2) h.2⟩
    · obtain ⟨u, hu1, hu2⟩ := exists_rat_btwn hgt
      obtain ⟨v, hv⟩ := exists_rat_gt p
      exact ⟨u, v, hu2, hv, fun h => (not_le.2 hu1) h.1⟩
  obtain ⟨μ, hμ, hμa⟩ := hyω t ht u v h0
  rw [F2.h0f_eq_unzY] at hμ
  have hsub : Ioo (u : ℝ) v ⊆ ({0} : Set ℝ)ᶜ := fun z hz hz0 => h0 (by
    rw [mem_singleton_iff] at hz0; rw [← hz0]; exact ⟨hz.1.le, hz.2.le⟩)
  have heq : ν.restrict (Ioo (u : ℝ) v) = μ :=
    LocalRule.isVagueLimitOnR_unique isOpen_Ioo
      ((hν.mono isOpen_Ioo hsub).isVagueLimitOnR hreg) hμ
  have hpm : ({p} : Set ℝ) ⊆ Ioo (u : ℝ) v := singleton_subset_iff.2 ⟨hu, hv⟩
  calc ν {p} = ν.restrict (Ioo (u : ℝ) v) {p} := by
        rw [Measure.restrict_apply (measurableSet_singleton p), inter_eq_left.2 hpm]
    _ = 0 := by rw [heq]; exact hμa p

/-- **`x` fields: no atoms off the root images, at all times** (copy of `ae_posOff_unzX`). -/
theorem ae_atomOff_unzX (hYG : YGoodOffAllStmt) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hI : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → AtomOff (Real.sqrt κ) (F2.unzX κ (X ω) (drive κ B ω) t)
      (offSet (drive κ B ω) t) := by
  filter_upwards [WedgeUnzip.coords_unzX_eq hκ hκ4 hB hX hI, ae_atomOff_unzY hYG hκ hκ4 hB hX hI,
    hYG κ hκ hκ4 P B X hB hX hI,
    WedgeUnzip.globalCaraStmt_holds κ hκ hκ4 P B hB,
    WedgeUnzip.extNonvanishStmt_holds κ hκ hκ4 P B hB]
    with ω hco hyP hyω hCω hNVω t ht
  refine AtomOff.congr_coords (hco t ht.le) ?_
  have hψ : ContinuousOn (WedgeUnzip.logTipFun κ (drive κ B ω) t)
      ((((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet (drive κ B ω) t)ᶜ ∩ Hbar) := by
    intro u hu
    have hc : ContinuousWithinAt (F2.extInv (drive κ B ω) t)
        ((((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet (drive κ B ω) t)ᶜ ∩ Hbar) u :=
      (hCω t ht.le u hu.2).mono inter_subset_right
    have hne : F2.extInv (drive κ B ω) t u ≠ 0 := hNVω t ht.le u hu.2 hu.1
    have hlog : ContinuousWithinAt (fun v => Real.log ‖F2.extInv (drive κ B ω) t v‖)
        ((((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet (drive κ B ω) t)ᶜ ∩ Hbar) u :=
      hc.norm.log (norm_ne_zero_iff.2 hne)
    exact (hlog.const_mul (Real.sqrt κ)).neg
  have hWo : IsOpen ((((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet (drive κ B ω) t)ᶜ) :=
    ((WedgeUnzip.isCompact_tipSet _ t).image Complex.continuous_ofReal).isClosed.isOpen_compl
  have hUW : ∀ s ∈ (offSet (drive κ B ω) t)ᶜ,
      (s : ℂ) ∈ (((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet (drive κ B ω) t)ᶜ := by
    rintro s hs ⟨u, hu, hus⟩
    obtain rfl := Complex.ofReal_injective hus
    apply hs
    rcases hu with rfl | rfl <;> simp [offSet]
  exact ((hyP t ht.le).mono (isClosed_offSet _ t) (singleton_subset_iff.2 (by simp [offSet]))
    ).add_ofFun (hyω t ht.le).1 (isClosed_offSet _ t) hWo hUW hψ

/-- No atoms off the root images for the unzipped unscaled wedge fields at all times. -/
def WedgeAtomOffAllStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P → IsBrownianReal B'' P →
    IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → AtomOff (Real.sqrt κ)
      (unzippedField (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) t)
      (offSet (drive κ B'' ω) t)

/-- **Unscaled wedge** (copy of `wedgePosOffAll_of_yGood`). -/
theorem wedgeAtomOffAll_of_yGood (hYG : YGoodOffAllStmt) : WedgeAtomOffAllStmt := by
  intro κ hκ hκ4 Ω _ P _ X' A B'' hX hA hI hB hIB
  obtain ⟨Ω₂, _, Q, _, X'', G, hX'', hB2, hI2, hae⟩ :=
    WedgeUnzip.WDec.wedgeDecompStmt_holds κ hκ hκ4 P X' A B'' hX hA hI hB hIB
  refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q) ?_
  filter_upwards [ae_atomOff_unzX hYG hκ hκ4 hB2 hX'' hI2,
    xGoodOffAll_of_yGoodOff hYG κ hκ hκ4 _ _ X'' hB2 hX'' hI2,
    WedgeUnzip.xContinuumStmt_holds κ hκ hκ4 _ _ X'' hB2 hX'' hI2,
    WedgeUnzip.globalCaraStmt_holds κ hκ hκ4 _ _ hB2, hae, hB2.cont,
    hB2.eval_zero_ae_eq_zero] with ω hxP hG hCo hCa hZ hc h0
  obtain ⟨hGc, -, hZfc⟩ := hZ
  intro t ht
  set W := drive κ (fun t (ω : Ω × Ω₂) => B'' t ω.1) ω
  have hW : Continuous W := by
    show Continuous (drive κ _ ω)
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : W 0 = 0 := by simp [W, drive, h0]
  have hreg : RegEq (F2.zU (Real.sqrt κ) X' A ω.1) (X'' ω + F2.logSingField κ + ofFun (G ω)) :=
    S5.FieldShift.regEq_of_fc hZfc
  have e1 : unzippedField (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω.1, drive κ B'' ω.1) t =
      unzippedField (Real.sqrt κ) (X'' ω + F2.logSingField κ + ofFun (G ω), W) t :=
    Factorization.coordChange_congr (funext fun k => funext fun z => hreg k z) _ _
  rw [e1]
  have hraw := WedgeUnzip.unzipAddFun (Real.sqrt κ) (X'' ω + F2.logSingField κ) (G ω) W t ht.le
    hW hW0 hGc hCo.1 (fun d _ r hr => hCo.2 t ht.le d r hr)
  refine AtomOff.congr_coords (WedgeUnzip.coords_eq_of_fc hraw) ?_
  exact (hxP t ht).add_ofFun (hG t ht.le).1 (isClosed_offSet _ t) isOpen_univ
    (fun _ _ => mem_univ _) (by rw [univ_inter]; exact hGc.comp_continuousOn (hCa t ht.le))

end LocLen
end QuantumZipper
