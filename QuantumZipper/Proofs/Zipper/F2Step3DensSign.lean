import QuantumZipper.Proofs.Zipper.F2Step3Dens
import QuantumZipper.Proofs.Zipper.UnifClB5
import QuantumZipper.Proofs.RS.RohdeSchrammSimple
import QuantumZipper.Proofs.Zipper.B5VSide
import QuantumZipper.Proofs.Zipper.B5ZeroMinus
import QuantumZipper.Proofs.Zipper.B5VHccZero
import QuantumZipper.Proofs.Zipper.F1Side3
import QuantumZipper.Proofs.RS.RealAlive

/-!
# F2 step (3), input (iv-a): `O⁻_t ≤ 0 ≤ O⁺_t` at all times

`Step3SideSignStmt` holds. For `t > 0`, `O⁻_t = 0₋(vrev W t, t) < 0`
(`B5.sideImages_fst_eq_zeroMinus_vrev`, `B5.swallowedSet_eq_Icc_zeroMinus`), because the reverse
hull `revHull (vrev W t) t = η(0,t]` is a simple arc (Rohde–Schramm, *Basic properties of SLE*,
Ann. of Math. 161 (2005), Thm 6.1, proved as `RS.rohdeSchrammSimple`; all horizons at once:
`RegUnif.ae_forall_isSimpleCurveHull_revHull_Vr`) and real points are never swallowed
(`RS.ae_real_alive`); at `t = 0`, `O⁻_0 = 0`. The right side follows by the reflection
`B ↦ −B` (`F1.sideImages_reflect_swap`). Same argument as `Thm18Asm.lenSideNegStmt_holds`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

/-- a.s., for every `t ≥ 0`, `O⁻_t ≤ 0`. -/
theorem ae_forall_sideImages_fst_nonpos {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (sideImages (drive κ B ω) t).1 ≤ 0 := by
  filter_upwards [RegUnif.ae_forall_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ
      hκ4.le P B hB, hB.cont, hB.eval_zero_ae_eq_zero, RS.ae_real_alive hB hκ hκ4.le]
    with ω hK hc h0 halive t ht
  have hWc : Continuous (drive κ B ω) := Thm14FromThm13.continuous_drive hc
  have hW0 : drive κ B ω 0 = 0 := by simp [drive, h0]
  rcases ht.eq_or_lt with rfl | ht'
  · exact (B5.sideImages_fst_zero_time hW0).le
  rw [B5.sideImages_fst_eq_zeroMinus_vrev hWc hW0 ht' (hK t ht') fun x hx => halive x hx t ht]
  exact (B5.swallowedSet_eq_Icc_zeroMinus (B2.continuous_vrev hWc t) (B2.vrev_zero ht) ht'
    (hK t ht')).1.le

/-- **`Step3SideSignStmt` holds.** -/
theorem step3SideSign_holds : Step3SideSignStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB _ _
  filter_upwards [ae_forall_sideImages_fst_nonpos hκ hκ4 hB,
    ae_forall_sideImages_fst_nonpos hκ hκ4 hB.neg, RS.ae_real_alive hB hκ hκ4.le]
    with ω h1 hneg halive t ht
  refine ⟨h1 t ht, ?_⟩
  obtain ⟨a, b, hL, hR⟩ := F1.exists_tendsto_sideImages_of_alive ht fun x hx => halive x hx t ht
  have hdr : drive κ (-B) ω = -drive κ B ω := by
    funext s; simp [drive]
  have h := hneg t ht
  rw [hdr, F1.sideImages_reflect_swap ht hL hR] at h
  simp only at h
  linarith

end F2
end QuantumZipper
