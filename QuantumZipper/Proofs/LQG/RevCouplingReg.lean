import QuantumZipper.Proofs.LQG.RevCouplingRegCert
import QuantumZipper.Proofs.Zipper.B2Markov
import QuantumZipper.Proofs.Zipper.E1NuExist
import QuantumZipper.Proofs.LQG.AtomlessUncond
import QuantumZipper.Proofs.LQG.PalmFree

/-!
# RCBMR: regularity of the boundary measure of the reverse coupling field

Proof of the blueprint item `Blueprint.RevCouplingBoundaryMeasureRegular` (M4 blueprint, T6 and
AUDIT3 M4; E-branch B3(a)): for `κ ∈ (0,4)`, `T > 0`, a Brownian motion `B` and an independent
free-boundary GFF `X`, almost surely the `√κ`-LQG boundary measure of
`h = couplingFieldRev κ (√κ B) T X = 𝔥_T + X ∘ f_T` has no atoms, charges every nondegenerate open
interval and is finite on compact intervals.

Route (the blueprint's, via Theorem 1.2; Sheffield, *Conformal weldings of random surfaces: SLE
and the quantum gravity zipper*, arXiv:1012.4797, Theorem 1.2):
1. **Time reversal.** With `B₁` a continuous version of `B` and `B̃ = revBM B₁ T` (a Brownian
   motion independent of `X`), the reversed driver `V` of `B̃` is `√κ B` on `[0,T]`, so
   `B2.b2_ident_qBoundaryMeasure` identifies `ν_h` with the boundary measure of the field `h⁰`
   obtained by unzipping `Γ⁰ = 𝔥₀ + X` along `√κ B̃` for time `T`.
2. **Law transfer (Theorem 1.2 / B1-FULL).** `B1Full.b1_full`: the normalized full circle
   coordinates of `h⁰` have the law of those of `Γ⁰`. The regularity of the boundary measure is
   the measurable coordinate event `certSet` (`RevCouplingRegCert`), which holds a.s. for `Γ⁰`
   (`AtomlessUncond.ae_gamma0_logSingularity`: `ν_{Γ⁰} = |t| ν_X` with no atom at `0`; `ν_X`
   atomless, M4-P5, and positive on intervals, M4-P2), hence a.s. for `h⁰`.
3. **Constants.** The normalization is an additive constant; since the raw circle averages of
   `h⁰` converge (`E1.ae_rawConverges_h0f`), it multiplies `ν` by a positive finite factor
   (`LocalRule.qBoundaryMeasure_addConst'`), which preserves the three clauses.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RevCouplingReg

open CharFun UnzipInvariance UnzipFull B1Full B2

/-- The three regularity clauses of `Blueprint.RevCouplingBoundaryMeasureRegular`. -/
def Good (ν : Measure ℝ) : Prop :=
  (∀ t : ℝ, ν {t} = 0) ∧ (∀ u v : ℝ, u < v → 0 < ν (Ioo u v)) ∧
    (∀ u v : ℝ, ν (Icc u v) < ∞)

theorem good_of_smul {ν : Measure ℝ} {c : ℝ≥0∞} (hc0 : c ≠ 0) (h : Good (c • ν)) : Good ν := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun t => ?_, fun u v huv => ?_, fun u v => ?_⟩
  · have := h1 t
    rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero] at this
    exact this.resolve_left hc0
  · have := h2 u v huv
    rw [Measure.smul_apply, smul_eq_mul] at this
    exact pos_iff_ne_zero.2 fun h0 => by simp [h0] at this
  · have := h3 u v
    rw [Measure.smul_apply, smul_eq_mul] at this
    rcases ENNReal.mul_lt_top_iff.1 this with h | h | h
    · exact h.2
    · exact absurd h hc0
    · rw [h]; exact ENNReal.zero_lt_top

theorem good_qBM_of_cert {γ : ℝ} {x : FieldSample} (h : Cert γ x) : Good (qBoundaryMeasure γ x) := by
  obtain ⟨ν, hν, h1, h2, h3⟩ := RevCouplingReg.good_of_cert h
  rw [qBoundaryMeasure_eq hν]
  exact ⟨h1, h2, h3⟩

/-- **`Γ⁰` side.** A.s. the normalized `Γ⁰ = 𝔥₀ + X` has a certificate. -/
theorem ae_cert_nrm_gamma0 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) :
    ∀ᵐ ω ∂P, Cert (Real.sqrt κ) (nrm (ofFun (h0rev κ) + X ω)) := by
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt hκ.le hκ4
  filter_upwards [AtomlessUncond.ae_gamma0_logSingularity hX hκ hκ4,
    RegSample.ae_isRegularSample hX, AtomlessUncond.ae_noAtoms_free' hX hγ hγ2,
    Positivity.ae_forall_pos_qBoundaryMeasure_Ioo hX hγ hγ2] with ω hω hreg hna hpos
  obtain ⟨hvag, heq, -⟩ := hω
  have hYreg : IsRegularSample (ofFun (h0rev κ) + X ω) := by
    rw [AtomlessUncond.gamma0_decomp κ (X ω)]
    exact ((hreg.addConst' _).add_ofFun_log' (-2 / Real.sqrt κ) 0).add_ofFun' continuousOn_const
  set c := -((ofFun (h0rev κ) + X ω) (foldedCircle 0 1)) with hc
  set C := ENNReal.ofReal (Real.exp (Real.sqrt κ * c / 2)) with hC
  have hb : bdryApprox (Real.sqrt κ) (nrm (ofFun (h0rev κ) + X ω)) =
      fun k => C • bdryApprox (Real.sqrt κ) (ofFun (h0rev κ) + X ω) k :=
    funext (LocalRule.bdryApprox_addConst hYreg.rawConverges _ c)
  have hν : IsVagueLimitR (bdryApprox (Real.sqrt κ) (nrm (ofFun (h0rev κ) + X ω)))
      (C • qBoundaryMeasure (Real.sqrt κ) (ofFun (h0rev κ) + X ω)) := by
    rw [hb]; exact BdryVague.IsVagueLimitR.const_smul hvag ENNReal.ofReal_ne_top
  obtain ⟨F, hF⟩ := hYreg.addConst' c
  refine cert_of_vague hν (fun k => PalmFree.isFiniteMeasureOnCompacts_bdryApprox hF k)
    (fun t => ?_) (fun u v huv => ?_)
  · rw [Measure.smul_apply, smul_eq_mul, heq]
    refine mul_eq_zero_of_right _ (withDensity_absolutelyContinuous _ _ ?_)
    exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans
      (hna.measure_singleton t).le)
  · rw [Measure.smul_apply, smul_eq_mul, heq]
    refine ENNReal.mul_pos (LocalRule.ofReal_exp_ne_zero _) fun h0 => ?_
    rw [withDensity_apply_eq_zero' (by fun_prop),
      Measure.restrict_apply' (measurableSet_singleton 0).compl] at h0
    have hsub : Ioo u v ⊆ ({x : ℝ | ENNReal.ofReal |x| ≠ 0} ∩ Ioo u v ∩ {0}ᶜ) ∪ {0} := by
      intro x hx
      by_cases hx0 : x = 0
      · exact Or.inr hx0
      · refine Or.inl ⟨⟨?_, hx⟩, hx0⟩
        show ENNReal.ofReal |x| ≠ 0
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        exact abs_pos.2 hx0
    exact (hpos u v huv).ne'
      (measure_mono_null hsub (measure_union_null h0 (hna.measure_singleton 0)))

/-- **RCBMR.** `Blueprint.RevCouplingBoundaryMeasureRegular` holds. -/
theorem revCouplingBoundaryMeasureRegular : Blueprint.RevCouplingBoundaryMeasureRegular := by
  intro κ hκ hκ4 T hT Ω _ P _ B X hB hX hind
  -- time reversal of a continuous version of `B`
  obtain ⟨B₁, hB₁m, hB₁c, hB₁eq⟩ := exists_good_version hB
  have hB₁ : IsPreBrownianReal B₁ P := hB.toIsPreBrownianReal.congr fun s => by
    filter_upwards [hB₁eq] with ω h using (h s).symm
  have hind₁ : IndepFun (pathOf B₁) X P :=
    hind.congr (hB₁eq.mono fun ω h => (funext fun s => (h s).symm : pathOf B ω = pathOf B₁ ω))
      (ae_eq_refl _)
  have hBt : IsBrownianReal (revBM B₁ T.toNNReal) P := isBrownianReal_revBM hB₁ hB₁c _
  have hindt : IndepFun (pathOf (revBM B₁ T.toNNReal)) X P := by
    have hΦ : Measurable fun p : ℝ≥0 → ℝ =>
        fun s => p (T.toNNReal - s) + p (max s T.toNNReal) - 2 * p T.toNNReal := by
      fun_prop
    exact hind₁.comp hΦ measurable_id
  -- Step 1: identification with the unzipped `Γ⁰` field
  have hid : ∀ᵐ ω ∂P, qBoundaryMeasure (Real.sqrt κ) (h0f κ T (revBM B₁ T.toNNReal) X ω) =
      qBoundaryMeasure (Real.sqrt κ) (couplingFieldRev κ (drive κ B ω) T (X ω)) := by
    filter_upwards [b2_ident_qBoundaryMeasure (κ := κ) hBt hX hindt hT.le, hB₁eq,
      hB₁.eval_zero_ae_eq_zero] with ω h hb h0
    have hV : EqOn (Vr κ T (revBM B₁ T.toNNReal) ω) (drive κ B ω) (Icc 0 T) := by
      intro s hs
      have hs' : T - s ∈ Icc 0 T := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have e1 := drive_revBM_eq (κ := κ) B₁ hT.le ω hs'
      have e2 := drive_revBM_eq (κ := κ) B₁ hT.le ω (⟨hT.le, le_rfl⟩ : T ∈ Icc 0 T)
      rw [Vr, vrev_of_mem hs, e1, e2, sub_sub_cancel, sub_self]
      simp only [drive, Real.toNNReal_zero, h0, hb]
      ring
    have hrev : revMap (Vr κ T (revBM B₁ T.toNNReal) ω) T = revMap (drive κ B ω) T :=
      funext fun z => ReverseFlow.revMap_congr_drive z hV
    rw [h]
    simp only [couplingFieldRev, hrev]
  -- Step 2: law transfer from `Γ⁰` (Theorem 1.2 at the level of circle coordinates)
  have hlaw := b1_full κ hκ P (revBM B₁ T.toNNReal) X hBt hX hindt hT
  have hF1 := aemeasurable_data_unzip (κ := κ) hBt hX hindt hT.le
  have hA : MeasurableSet {p : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) |
      p.1.1 ∈ certSet (Real.sqrt κ)} :=
    (measurableSet_certSet _).preimage (measurable_fst.comp measurable_fst)
  have hF0 := aemeasurable_data0 (κ := κ) hBt hX
  have h0side : ∀ᵐ p ∂(P.map fun ω => (lawData (fun ω => nrm (ofFun (h0rev κ) + X ω)) ω,
      fun s : ℝ≥0 => drive κ (revBM B₁ T.toNNReal) ω s)),
      p.1.1 ∈ certSet (Real.sqrt κ) := by
    have key : ∀ᵐ ω ∂P, (CoordsFull.coordsFull (nrm (ofFun (h0rev κ) + X ω))) ∈
        certSet (Real.sqrt κ) := by
      filter_upwards [ae_cert_nrm_gamma0 hX hκ hκ4] with ω hω
      exact (mem_certSet_iff _ _).2 hω
    exact (ae_map_iff hF0 (p := fun p : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) =>
      p.1.1 ∈ certSet (Real.sqrt κ)) hA).2 key
  rw [← hlaw] at h0side
  have h1side := ae_of_ae_map hF1 h0side
  -- Step 3: remove the normalization and conclude
  filter_upwards [hid, h1side,
    E1.ae_rawConverges_h0f (κ := κ) hBt hX hindt hT.le] with ω hidω hcert hraw
  have hc : Cert (Real.sqrt κ) (nrm (h0f κ T (revBM B₁ T.toNNReal) X ω)) := by
    rw [h0f_eq_unzippedField]
    exact (mem_certSet_iff _ _).1 hcert
  have hg := good_qBM_of_cert hc
  unfold nrm at hg
  rw [LocalRule.qBoundaryMeasure_addConst' hraw] at hg
  have := good_of_smul (LocalRule.ofReal_exp_ne_zero _) hg
  rw [hidω] at this
  exact this

end RevCouplingReg
end QuantumZipper
