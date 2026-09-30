import QuantumZipper.Proofs.Zipper.WedgeAddConstPos

/-!
# WEDGE-ADDCONST (4): the law part of B4(c) from two nodes

Sheffield, arXiv:1012.4797, §1.6 ((1.8), the canonical description of the `α`-wedge);
Duplantier–Miller–Sheffield, arXiv:1409.7055, proof of Prop. 4.6 (adding a constant to the field
and re-embedding gives the same law, by re-centring the radial part at its first hitting time).

With `Z = wedgeField (lateralPart X) A Q` and `W = canonical γ Z` the reference wedge, write
`Z_m = Z + m`. The law part `WedgeRefAddConstLawStmt` of B4(c) follows from:

* `WedgeReembedStmt` (**re-embedding**): `canonical γ (W + k)` and `canonical γ (Z + k)` have the
  same data law (a.s. they have the same data: `W + k = rescale (Z + k) Q s` at the level of
  regularized averages, and the canonical description does not see a rescaling);
* `WedgeShiftLawStmt` (**translation**): for `c > 0`, `canonical γ Z_m` and `canonical γ Z_{m+c}`
  have the same data law (DMS Prop. 4.6: `A(T_c + ·) + c` has the law of `A`,
  `Wire5.wedge_translation_uncond`, which turns `Z_m` into a rescaling of `Z'_{m+c}`, where `Z'`
  is built from the lateral part of `rescale X Q e^{T_c}`; the latter has the joint law of the
  lateral part of `X` with `A`, `F1.map_prod_lateralData_rescale_indep`).

For `k ≥ 0` take `m = 0, c = k`; for `k < 0` take `m = k, c = -k` (`wedgeRefAddConstLawStmt_of`).
Own bookkeeping argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace QuantumZipper
namespace F1

/-- The shifted wedge field `Z + m`, `Z = wedgeField (lateralPart X) A Q`. -/
def wedgeShift (γ : ℝ) {Ω : Type*} (X : Ω → FieldSample) (A : ℝ → Ω → ℝ) (m : ℝ) (ω : Ω) :
    FieldSample :=
  addConst (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) m

/-- **Node: re-embedding.** -/
def WedgeReembedStmt (γ α : ℝ) : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ), IsFreeGFFModConstH X P' →
    IsWedgeProcess α (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' → ∀ k : ℝ,
      P'.map (fun ω => WedgeMeas.dataFull H
          (canonical γ (addConst (WedgeMeas.wedgeRef γ X A ω) k))) =
        P'.map (fun ω => WedgeMeas.dataFull H (canonical γ (wedgeShift γ X A k ω)))

/-- **Node: translation.** -/
def WedgeShiftLawStmt (γ α : ℝ) : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ), IsFreeGFFModConstH X P' →
    IsWedgeProcess α (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' → ∀ m c : ℝ, 0 < c →
      P'.map (fun ω => WedgeMeas.dataFull H (canonical γ (wedgeShift γ X A m ω))) =
        P'.map (fun ω => WedgeMeas.dataFull H (canonical γ (wedgeShift γ X A (m + c) ω)))

theorem addConst_zero' (x : FieldSample) : addConst x 0 = x := by
  funext μ
  simp [addConst]

/-- **The law part of B4(c) for the reference wedge, from the two nodes.** -/
theorem wedgeRefAddConstLawStmt_of {γ α : ℝ} (hR : WedgeReembedStmt γ α)
    (hS : WedgeShiftLawStmt γ α) : WedgeRefAddConstLawStmt γ α := by
  intro Ω' _ P' _ X A hX hA hI k
  have h0 : (fun ω => WedgeMeas.dataFull H (canonical γ (wedgeShift γ X A 0 ω))) =
      fun ω => WedgeMeas.dataFull H (WedgeMeas.wedgeRef γ X A ω) := by
    funext ω
    simp only [wedgeShift, addConst_zero', WedgeMeas.wedgeRef]
  have hk : P'.map (fun ω => WedgeMeas.dataFull H (canonical γ (wedgeShift γ X A k ω))) =
      P'.map (fun ω => WedgeMeas.dataFull H (canonical γ (wedgeShift γ X A 0 ω))) := by
    rcases lt_trichotomy k 0 with hk | rfl | hk
    · have := hS P' X A hX hA hI k (-k) (neg_pos.2 hk)
      rwa [add_neg_cancel] at this
    · rfl
    · have := hS P' X A hX hA hI 0 k hk
      rw [zero_add] at this
      exact this.symm
  show P'.map (fun ω => WedgeMeas.dataFull H
      (canonical γ (addConst (WedgeMeas.wedgeRef γ X A ω) k))) =
    P'.map (fun ω => WedgeMeas.dataFull H (WedgeMeas.wedgeRef γ X A ω))
  rw [hR P' X A hX hA hI k, hk, h0]

/-- **Field-level B4(c) from the two nodes.** -/
theorem wedgeAddConstLawStmt_of_nodes
    (hR : ∀ γ α : ℝ, 0 < γ → γ < 2 → α < Qc γ → WedgeReembedStmt γ α)
    (hS : ∀ γ α : ℝ, 0 < γ → γ < 2 → α < Qc γ → WedgeShiftLawStmt γ α) :
    WedgeAddConstLawStmt :=
  wedgeAddConstLawStmt_of_refLaw fun γ α hγ hγ2 hα =>
    wedgeRefAddConstLawStmt_of (hR γ α hγ hγ2 hα) (hS γ α hγ hγ2 hα)

end F1
end QuantumZipper
