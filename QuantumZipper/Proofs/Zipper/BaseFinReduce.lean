import QuantumZipper.Proofs.Zipper.UnifRCSplit
import QuantumZipper.Proofs.LQG.RevCouplingReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X1 (decision D75): base finiteness of the open-arc lengths at a fixed time

`BaseFiniteStmt` is the one fact the paper needs but does not prove (handoff/FIDELITY-TIP-MAX.md
§3 row X1, handoff/FIDELITY-TIP.md item B1): for `x = X + α₀(−log|·|)` (`α₀ = γ − 2/γ`,
`X` a free boundary GFF modulo constants, `W = √κ B` independent), at a fixed capacity time
`q > 0`, the local boundary measure of the unzipped field `x_q` on each open arc `(O⁻_q, 0)`,
`(0, O⁺_q)` has finite total mass. Berestycki–Powell, arXiv:2404.16642, assert it without proof
(p. 285, "L(1) < ∞"; Remark 8.10, pp. 280–281); Sheffield, arXiv:1012.4797, p. 70, obtains it
implicitly from the wedge decomposition.

## What is proved here

* `ae_unzY_vague_fixed`: at a fixed time `T > 0`, a.s. the `Γ⁰` field `y_T` (= `h⁰` unzipped)
  has a global boundary measure, finite on compacts (Sheffield Thm 1.2 + boundary GMC, through
  the proved `RevCouplingReg.revCouplingBoundaryMeasureRegular` and `B2.b2_ident_qBoundaryMeasure`;
  the argument is the one of `E1NuExist.ae_exists_isVagueLimitR_nuPalm`).
* `ae_arc_isVagueLimitOnR`: **F2 transfer on open arcs at a fixed time** (FIDELITY-TIP-MAX L6,
  fixed-time form): a.s., on every open `U ⊆ (O⁻_T, O⁺_T)`, the local limit of `x_T` exists and
  equals `|F_T|^{−γ²/2} ν_{y_T}` on `U`. This is rule (5.1) of Sheffield pp. 60–62
  (Duplantier–Sheffield 2011, (5.1)) applied with `φ = −γ log|F_T|`, continuous on the open arc,
  using the proved circle-level identity `F2.step3FieldCircDy_holds`, Carathéodory
  `F2.step3BdryExt_holds` and `LocalRule.isVagueLimitOnR_add_ofFun`. No endpoint clauses.
* `baseFinite_of_baseWeight`: `BaseWeightStmt → BaseFiniteStmt`. The tip `0` of the unzipped
  picture and every compact subarc are handled here (the density `|F_T|^{−γ²/2}` is bounded on
  compacts of `(O⁻_T, O⁺_T)`, and `ν_{y_T}` is finite on compacts). What remains,
  `BaseWeightStmt`, is only the integrability of `|F_q|^{−κ/2}` against the `Γ⁰` measure
  `ν_{y_q}` in some neighbourhood `(O⁻_q, O⁻_q + δ)` of the base point (and its mirror at `O⁺_q`):
  the fixed-time, capacity-picture content of X1, with no local limits of `x` involved.

Own bookkeeping (covering of the arc, bound on the compact middle part); the analytic inputs are
the cited proved nodes.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace BaseFin

/-- **X1, base finiteness (D75).** At every fixed capacity time `q > 0`, a.s. the local boundary
measures of the unzipped field `x_q` (`x = X + α₀(−log|·|)`) on the open arcs `(O⁻_q, 0)` and
`(0, O⁺_q)` have finite total mass. (Their existence is proved separately,
`ae_exists_arc_limits`, so the junk value `0` of `qBoundaryMeasureOn` does not occur.) -/
def BaseFiniteStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ q : ℝ, 0 < q → ∀ᵐ ω ∂P,
      qBoundaryMeasureOn (Real.sqrt κ) (F2.unzX κ (X ω) (drive κ B ω) q)
          (Ioo (sideImages (drive κ B ω) q).1 0) (Ioo (sideImages (drive κ B ω) q).1 0) < ⊤ ∧
      qBoundaryMeasureOn (Real.sqrt κ) (F2.unzX κ (X ω) (drive κ B ω) q)
          (Ioo 0 (sideImages (drive κ B ω) q).2) (Ioo 0 (sideImages (drive κ B ω) q).2) < ⊤

/-- **X1 core, capacity picture.** At every fixed `q > 0`, a.s. for some `δ > 0` the weight
`|F_q|^{−κ/2}` (`F_q = f_q⁻¹` on the boundary, `F_q(O^±_q) = 0` is the base of the curve) is
integrable against the `Γ⁰` boundary measure `ν_{y_q}` on `(O⁻_q, O⁻_q + δ)` and on
`(O⁺_q − δ, O⁺_q)`. -/
def BaseWeightStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ q : ℝ, 0 < q → ∀ᵐ ω ∂P, ∃ δ > 0,
      ∫⁻ s in Ioo (sideImages (drive κ B ω) q).1 ((sideImages (drive κ B ω) q).1 + δ),
          ENNReal.ofReal (‖F2.invBdry (drive κ B ω) q s‖ ^ (-(κ / 2)))
          ∂qBoundaryMeasure (Real.sqrt κ) (F2.unzY κ (X ω) (drive κ B ω) q) < ⊤ ∧
      ∫⁻ s in Ioo ((sideImages (drive κ B ω) q).2 - δ) (sideImages (drive κ B ω) q).2,
          ENNReal.ofReal (‖F2.invBdry (drive κ B ω) q s‖ ^ (-(κ / 2)))
          ∂qBoundaryMeasure (Real.sqrt κ) (F2.unzY κ (X ω) (drive κ B ω) q) < ⊤

/-- A local vague limit determines `qBoundaryMeasureOn`. -/
theorem qBoundaryMeasureOn_eq_of_lim {γ : ℝ} {x : FieldSample} {U : Set ℝ} (hU : IsOpen U)
    {ν : Measure ℝ} (h : IsVagueLimitOnR U (bdryApprox γ x) ν) :
    qBoundaryMeasureOn γ x U = ν := by
  have hex : ∃ ν', IsVagueLimitOnR U (bdryApprox γ x) ν' := ⟨ν, h⟩
  rw [qBoundaryMeasureOn, dif_pos hex]
  exact LocalRule.isVagueLimitOnR_unique hU hex.choose_spec h

/-- `e^{(√κ/2)(−√κ log r)} = r^{−κ/2}` for `r > 0`. -/
theorem ofReal_exp_eq_rpow {κ r : ℝ} (hκ : 0 ≤ κ) (hr : 0 < r) :
    ENNReal.ofReal (Real.exp (Real.sqrt κ / 2 * -(Real.sqrt κ * Real.log r))) =
      ENNReal.ofReal (r ^ (-(κ / 2))) := by
  congr 1
  rw [Real.rpow_def_of_pos hr]
  congr 1
  have h := Real.mul_self_sqrt hκ
  linear_combination (-(Real.log r) / 2) * h

/-- **Pathwise covering argument.** Let `ν` be finite on compacts and `G` continuous and
nonvanishing on `(a, b)`. If `|G|^{−κ/2}` is `ν`-integrable near `a` and near `b`, then the
density `e^{(√κ/2)(−√κ log|G|)}` is `ν`-integrable on every measurable `U ⊆ (a, b)`. -/
theorem lintegral_arc_lt_top {κ : ℝ} (hκ : 0 ≤ κ) {ν : Measure ℝ}
    (hfin : ∀ u v : ℝ, ν (Icc u v) < ⊤) {a b : ℝ} {G : ℝ → ℂ}
    (hGc : ContinuousOn G (Ioo a b)) (hG0 : ∀ s ∈ Ioo a b, G s ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (hA : ∫⁻ s in Ioo a (a + δ), ENNReal.ofReal (‖G s‖ ^ (-(κ / 2))) ∂ν < ⊤)
    (hC : ∫⁻ s in Ioo (b - δ) b, ENNReal.ofReal (‖G s‖ ^ (-(κ / 2))) ∂ν < ⊤)
    {U : Set ℝ} (hUm : MeasurableSet U) (hU : U ⊆ Ioo a b) :
    ∫⁻ s in U, ENNReal.ofReal (Real.exp (Real.sqrt κ / 2 * -(Real.sqrt κ * Real.log ‖G s‖)))
      ∂ν < ⊤ := by
  set g : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (‖G s‖ ^ (-(κ / 2))) with hg
  have hcongr : ∫⁻ s in U,
      ENNReal.ofReal (Real.exp (Real.sqrt κ / 2 * -(Real.sqrt κ * Real.log ‖G s‖))) ∂ν =
      ∫⁻ s in U, g s ∂ν :=
    setLIntegral_congr_fun hUm fun s hs =>
      ofReal_exp_eq_rpow hκ (norm_pos_iff.2 (hG0 s (hU hs)))
  rw [hcongr]
  -- the middle compact piece
  set M := Icc (a + δ) (b - δ) with hM
  have hMsub : M ⊆ Ioo a b := fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hMc : ContinuousOn (fun s => ‖G s‖ ^ (-(κ / 2))) M :=
    ((hGc.mono hMsub).norm).rpow_const fun s hs => Or.inl (norm_ne_zero_iff.2 (hG0 s (hMsub hs)))
  obtain ⟨Cb, hCb⟩ := isCompact_Icc.exists_bound_of_continuousOn hMc
  have hMint : ∫⁻ s in M, g s ∂ν < ⊤ := by
    calc ∫⁻ s in M, g s ∂ν ≤ ∫⁻ _ in M, ENNReal.ofReal Cb ∂ν := by
          refine setLIntegral_mono' measurableSet_Icc fun s hs => ENNReal.ofReal_le_ofReal ?_
          exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hCb s hs))
      _ = ENNReal.ofReal Cb * ν M := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin _ _)
  have hcover : U ⊆ Ioo a (a + δ) ∪ (M ∪ Ioo (b - δ) b) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hU hs
    by_cases hsa : s < a + δ
    · exact Or.inl ⟨h1, hsa⟩
    · by_cases hsb : b - δ < s
      · exact Or.inr (Or.inr ⟨hsb, h2⟩)
      · exact Or.inr (Or.inl ⟨not_lt.1 hsa, not_lt.1 hsb⟩)
  calc ∫⁻ s in U, g s ∂ν ≤ ∫⁻ s in Ioo a (a + δ) ∪ (M ∪ Ioo (b - δ) b), g s ∂ν :=
        lintegral_mono_set hcover
    _ ≤ ∫⁻ s in Ioo a (a + δ), g s ∂ν + (∫⁻ s in M, g s ∂ν + ∫⁻ s in Ioo (b - δ) b, g s ∂ν) :=
        (lintegral_union_le _ _ _).trans (add_le_add le_rfl (lintegral_union_le _ _ _))
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hA, ENNReal.add_lt_top.2 ⟨hMint, hC⟩⟩

section Fixed

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **Fixed-time regularity of `y_T`.** At a fixed `T > 0`, a.s. the boundary approximations of
the `Γ⁰` field `y_T` converge vaguely to `qBoundaryMeasure`, which is finite on compacts. -/
theorem ae_unzY_vague_fixed (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, IsVagueLimitR (bdryApprox (Real.sqrt κ) (F2.unzY κ (X ω) (drive κ B ω) T))
        (qBoundaryMeasure (Real.sqrt κ) (F2.unzY κ (X ω) (drive κ B ω) T)) ∧
      ∀ u v : ℝ,
        qBoundaryMeasure (Real.sqrt κ) (F2.unzY κ (X ω) (drive κ B ω) T) (Icc u v) < ⊤ := by
  obtain ⟨B'', hB'', hind'', hV⟩ := B2.b2_V_brownian (κ := κ) hB hind hT.le
  filter_upwards [RevCouplingReg.revCouplingBoundaryMeasureRegular κ hκ hκ4 T hT P B'' X hB''
      hX hind'', hV, B2.b2_ident_qBoundaryMeasure (κ := κ) hB hX hind hT.le]
    with ω hRω hVω hid
  have hrevV : revMap (B2.Vr κ T B ω) T = revMap (drive κ B'' ω) T :=
    funext fun z => ReverseFlow.revMap_congr_drive z hVω
  have hcf : couplingFieldRev κ (B2.Vr κ T B ω) T (X ω) =
      couplingFieldRev κ (drive κ B'' ω) T (X ω) := by
    simp only [couplingFieldRev, hrevV]
  have hne : qBoundaryMeasure (Real.sqrt κ) (B2.h0f κ T B X ω) ≠ 0 := by
    rw [hid, hcf]
    intro h0
    have := hRω.2.1 0 1 one_pos
    rw [h0] at this
    simp at this
  have hex : ∃ ν, IsVagueLimitR (bdryApprox (Real.sqrt κ) (B2.h0f κ T B X ω)) ν := by
    by_contra hn
    exact hne (by rw [qBoundaryMeasure, dif_neg hn])
  obtain ⟨ν, hν⟩ := hex
  rw [← F2.h0f_eq_unzY, qBoundaryMeasure_eq hν]
  refine ⟨hν, fun u v => ?_⟩
  rw [← qBoundaryMeasure_eq hν, hid, hcf]
  exact hRω.2.2 u v

/-- **F2 transfer on open arcs, fixed time** (rule (5.1), Sheffield pp. 60–62). At a fixed
`T > 0`, a.s., on every open `U ⊆ (O⁻_T, O⁺_T)` the boundary approximations of `x_T` converge
locally to `|F_T|^{−γ²/2} ν_{y_T}`, written `e^{(γ/2)(−γ log|F_T|)} ν_{y_T}`. -/
theorem ae_arc_isVagueLimitOnR (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ U : Set ℝ, IsOpen U →
      U ⊆ Ioo (sideImages (drive κ B ω) T).1 (sideImages (drive κ B ω) T).2 →
      IsVagueLimitOnR U (bdryApprox (Real.sqrt κ) (F2.unzX κ (X ω) (drive κ B ω) T))
        (((qBoundaryMeasure (Real.sqrt κ) (F2.unzY κ (X ω) (drive κ B ω) T)).restrict U
          ).withDensity fun s => ENNReal.ofReal (Real.exp (Real.sqrt κ / 2 *
            -(Real.sqrt κ * Real.log ‖F2.extInv (drive κ B ω) T (s : ℂ)‖)))) := by
  filter_upwards [ae_unzY_vague_fixed hκ hκ4 hB hX hind hT,
    RegUnif.ae_forall_isRegularSample (κ := κ) (γ := Real.sqrt κ) hB hX hind,
    F2.step3BdryExt_holds κ hκ hκ4 P B X hB hX hind,
    F2.step3FieldCircDy_holds κ hκ hκ4 P B X hB hX hind] with ω hY hR hC hF U hU hUsub
  obtain ⟨V, hVo, hUV, hGc, hG0⟩ := hC T hT.le
  have hreg : IsRegularSample (F2.unzY κ (X ω) (drive κ B ω) T) := by
    have e : F2.unzY κ (X ω) (drive κ B ω) T =
        unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) T := by
      rw [F2.unzY, F2.h0rev_add_eq]
    rw [e]
    exact (hR T hT.le).1
  have hφ : ContinuousOn
      (fun z => -(Real.sqrt κ * Real.log ‖F2.extInv (drive κ B ω) T z‖)) (V ∩ Hbar) :=
    ((continuous_norm.comp_continuousOn hGc).log fun z hz => norm_ne_zero_iff.2 (hG0 z hz)
      ).const_smul (Real.sqrt κ) |>.neg
  have h1 := LocalRule.isVagueLimitOnR_add_ofFun hreg hU
    (PalmNorm.isVagueLimitOnR_restrict_of_R hY.1 hU) hVo (fun s hs => hUV s (hUsub hs)) hφ
  exact F2.isVagueLimitOnR_congr_avgReg hU h1
    (Eventually.of_forall fun k s _ => F2.forall_avgReg_eq_of_lpt (hF T hT.le) k (s : ℂ))

end Fixed

/-- **X1 from its capacity-picture core.** -/
theorem baseFinite_of_baseWeight (hW : BaseWeightStmt) : BaseFiniteStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind q hq
  filter_upwards [hW κ hκ hκ4 P B X hB hX hind q hq, ae_arc_isVagueLimitOnR hκ hκ4 hB hX hind hq,
    ae_unzY_vague_fixed hκ hκ4 hB hX hind hq, F2.step3BdryExt_holds κ hκ hκ4 P B X hB hX hind,
    F2.step3SideSign_holds κ hκ hκ4 P B X hB hX hind] with ω hWω hAω hYω hCω hSω
  obtain ⟨δ, hδ, hL, hR⟩ := hWω
  obtain ⟨V, -, hUV, hGc, hG0⟩ := hCω q hq.le
  set a := (sideImages (drive κ B ω) q).1
  set b := (sideImages (drive κ B ω) q).2
  have hGc' : ContinuousOn (fun s : ℝ => F2.extInv (drive κ B ω) q (s : ℂ)) (Ioo a b) :=
    hGc.comp Complex.continuous_ofReal.continuousOn fun s hs =>
      ⟨hUV s hs, show (0 : ℝ) ≤ (s : ℂ).im by simp⟩
  have hG0' : ∀ s ∈ Ioo a b, F2.extInv (drive κ B ω) q (s : ℂ) ≠ 0 := fun s hs =>
    hG0 _ ⟨hUV s hs, show (0 : ℝ) ≤ (s : ℂ).im by simp⟩
  simp only [← F2.extInv_ofReal] at hL hR
  have key : ∀ U : Set ℝ, IsOpen U → U ⊆ Ioo a b →
      qBoundaryMeasureOn (Real.sqrt κ) (F2.unzX κ (X ω) (drive κ B ω) q) U U < ⊤ := by
    intro U hU hUab
    rw [qBoundaryMeasureOn_eq_of_lim hU (hAω U hU hUab), withDensity_apply _ hU.measurableSet,
      Measure.restrict_restrict hU.measurableSet, inter_self]
    exact lintegral_arc_lt_top hκ.le hYω.2 hGc' hG0' hδ hL hR hU.measurableSet hUab
  exact ⟨key _ isOpen_Ioo (Ioo_subset_Ioo le_rfl (hSω q hq.le).2),
    key _ isOpen_Ioo (Ioo_subset_Ioo (hSω q hq.le).1 le_rfl)⟩

end BaseFin
end QuantumZipper
