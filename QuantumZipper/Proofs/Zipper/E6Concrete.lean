import QuantumZipper.Proofs.Zipper.E6
import QuantumZipper.Proofs.Zipper.E5Stmt
import QuantumZipper.Proofs.Zipper.EWire
import QuantumZipper.Proofs.Zipper.B5ZeroMinus
import QuantumZipper.Proofs.RS.RohdeSchrammSimple
import QuantumZipper.Proofs.LQG.PalmFormula

/-!
# E6 for the Palm-zip setting of Theorem 1.3

Instantiates the abstract core `E6.e6_core` with the Palm boundary measure `nuPalm` (as a kernel,
NU-KER `NuMeas.exists_kernel_nuPalm`), the collided points `τ_x < T`, `z = zeroMinus V T`
(`B5.ae_zeroMinus_Vr_facts`), Z-FIN and E3-POS (`EWire.zfin`, `EWire.e3_pos`), B3(a)
(`RevCouplingReg.revCouplingBoundaryMeasureRegular`), and E5 in the form `E5.E5Stmt loc`.

Remaining explicit hypotheses (each is a separate node): the deterministic identity `hId`
(E6-ID: `Z_C C̄_x ≈ zipLenDown γ ℓ₁ (Z_C C̄_y)` when `ν[y, x] = ℓ₁ e^{−C/2}`; needs the
`zipCapDown` cocycle, B3(d) and uniform B5-V, cf. decision D21 and `ESM.ae_b5v_uniform`), B5
locality `LocalAbs` of `zipLenDown`, the regularity set `Reg`, `ConfigEq`-invariance of `loc`,
and measurability of the collided set and of the local data (`loc` is S5-TV's still undefined
local data map, R12).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper.E6

open B2 E1

variable {Ω : Type} [MeasurableSpace Ω] {Ω' : Type} [MeasurableSpace Ω']

/-- The zoomed collided configuration of E5 (`zc` in `E5.E5Stmt`). -/
def zcC (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ) (C : ℝ) (ω : Ω)
    (x : ℝ) : Cfg :=
  canonConfig (Real.sqrt κ) (addConst (collided κ T B X ω x).1
    (-(mReg κ T B X ϖ ω) + C / Real.sqrt κ), (collided κ T B X ω x).2)

/-- B3(a) transferred to `nuPalm`: a.s. atomless and locally finite. -/
theorem ae_nuPalm_atom_fin {P : Measure Ω} [IsProbabilityMeasure P] {κ T : ℝ}
    {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hReg : Blueprint.RevCouplingBoundaryMeasureRegular)
    (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (ϖ : Measure ℂ) :
    ∀ᵐ ω ∂P, (∀ x, nuPalm κ T B X ϖ ω {x} = 0) ∧
      ∀ u v, nuPalm κ T B X ϖ ω (Icc u v) ≠ ∞ := by
  obtain ⟨B'', hB'', hind'', hV⟩ := b2_V_brownian (κ := κ) hB hind hT.le
  filter_upwards [hReg κ hκ hκ4 T hT P B'' X hB'' hX hind'', hV,
    b2_ident_qBoundaryMeasure hB hX hind hT.le, ae_nuPalm_eq_smul (κ := κ) hB hX hind hT.le ϖ]
    with ω hRω hVω hid hsm
  have hrevV : revMap (Vr κ T B ω) T = revMap (drive κ B'' ω) T :=
    funext fun z => ReverseFlow.revMap_congr_drive z hVω
  have hcf : couplingFieldRev κ (Vr κ T B ω) T (X ω) =
      couplingFieldRev κ (drive κ B'' ω) T (X ω) := by
    simp only [couplingFieldRev, hrevV]
  refine ⟨fun x => ?_, fun u v => ?_⟩
  · rw [hsm, Measure.smul_apply, hid, hcf, smul_eq_mul, hRω.1 x, mul_zero]
  · rw [hsm, Measure.smul_apply, hid, hcf, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hRω.2.2 u v).ne

/-- An a.s. locally finite kernel on `ℝ` agrees a.s. with an s-finite kernel (sum over the unit
intervals `[z, z+1)` of its restrictions, after zeroing it off the locally finite set). -/
lemma exists_sfinite_version {P : Measure Ω} (K : Kernel Ω ℝ)
    (h : ∀ᵐ ω ∂P, ∀ u v, K ω (Icc u v) ≠ ∞) :
    ∃ K' : Kernel Ω ℝ, IsSFiniteKernel K' ∧ ∀ᵐ ω ∂P, K' ω = K ω := by
  classical
  set S := {ω | ∀ n : ℕ, K ω (Icc (-(n : ℝ)) n) < ∞}
  have hS : MeasurableSet S := by
    simp only [S, ofPred_forall]
    exact MeasurableSet.iInter fun n =>
      measurableSet_lt (K.measurable_coe measurableSet_Icc) measurable_const
  set K₀ := Kernel.piecewise hS K 0
  have hfinK : ∀ z : ℤ, ∀ ω, K₀ ω (Ico (z : ℝ) (z + 1)) ≠ ∞ := by
    intro z ω
    rw [Kernel.piecewise_apply]
    split_ifs with hω
    · refine ne_top_of_le_ne_top (hω (Int.natAbs z + 1)).ne (measure_mono ?_)
      have habs : ((Int.natAbs z : ℕ) : ℝ) = |(z : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      intro x hx
      have h1 := neg_abs_le (z : ℝ)
      have h2 := le_abs_self (z : ℝ)
      push_cast
      rw [habs]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · simp
  have hfin' : ∀ z : ℤ,
      IsSFiniteKernel (K₀.restrict (measurableSet_Ico (a := (z : ℝ)) (b := z + 1))) :=
    fun z => Palm.isSFiniteKernel_of_ne_top _ fun ω => by
      rw [Kernel.restrict_apply, Measure.restrict_apply_univ]; exact hfinK z ω
  refine ⟨Kernel.sum fun z : ℤ => K₀.restrict (measurableSet_Ico (a := (z : ℝ)) (b := z + 1)),
    inferInstance, ?_⟩
  filter_upwards [h] with ω hω
  have hωS : ω ∈ S := fun n => (hω _ _).lt_top
  rw [Kernel.sum_apply]
  simp_rw [Kernel.restrict_apply, K₀, Kernel.piecewise_apply, if_pos hωS]
  rw [← Measure.restrict_iUnion (pairwise_disjoint_Ico_intCast ℝ) (fun z => measurableSet_Ico),
    iUnion_Ico_intCast ℝ, Measure.restrict_univ]

end QuantumZipper.E6
