import QuantumZipper.Proofs.Zipper.Cor15RegZy
import QuantumZipper.Proofs.Zipper.Cor15WRCore

/-!
# COR15-HREG (2): the generic reduction behind `hZc`

`aemeasurable_mod0Data_zipCapUp_of_reading`: for any random configuration `x ω`, the data
`mod0Data (Z_t (x ω))` is a.e.-measurable as soon as
* the full circle coordinates of `(x ω).1` are a.e.-measurable,
* the driver `(x ω).2` agrees a.s. on `(0,∞)` with a pointwise-measurable family, and
* a.s. the welding driver of `(x ω).1` agrees on `[0,t]` with `Vp (e ω)`, for an a.e.-measurable
  `e` and a family `Vp` of continuous drivers (measurable in the parameter, `Vp a 0 = 0`), whose
  time-reversed forward hull is Lebesgue-null.

For `x = D_t c` this is how `hZy` was proved (`Cor15RegZy`); for `x = c` the last input is the one
remaining statement `Cor15ZcReadStmt`. Own assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open CharFun CoordsFull

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **Generic reduction of the a.e.-measurability of `mod0Data ∘ Z_t`.** -/
theorem aemeasurable_mod0Data_zipCapUp_of_reading {γ t : ℝ} (ht : 0 < t)
    {x : Ω → FieldSample × (ℝ → ℝ)}
    (hc : AEMeasurable (fun ω => coordsFull (x ω).1) P)
    {D : Ω → ℝ → ℝ} (hDm : ∀ r, Measurable fun ω => D ω r)
    (hD : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → (x ω).2 r = D ω r)
    {α : Type*} [MeasurableSpace α] {e : Ω → α} (he : AEMeasurable e P) {Vp : α → ℝ → ℝ}
    (hVc : ∀ a, Continuous (Vp a)) (hV0 : ∀ a, Vp a 0 = 0)
    (hVm : ∀ s, Measurable fun a => Vp a s)
    (hread : ∀ᵐ ω ∂P, EqOn (weldDriver γ (x ω).1 t) (Vp (e ω)) (Icc 0 t) ∧
      volume (fwdHull (ArcDriver.trev (Vp (e ω)) t) t) = 0) :
    AEMeasurable (fun ω => mod0Data (zipCapUp γ t (x ω))) P := by
  set Q := Qc γ
  set a' := hc.mk _
  have ha'm : Measurable a' := hc.measurable_mk
  set e' := he.mk _
  have he'm : Measurable e' := he.measurable_mk
  set Φ : ((ℕ → ℝ) × α) × Ω → (TestFun0 H → ℝ) × (ℝ≥0 → ℝ) := fun p =>
    (fun ρ => CInv Vp t Q (tdens ρ.1.1) p.1 - CInv Vp t Q (tdens fun z => -ρ.1.1 z) p.1,
      fun u => if (u : ℝ) ≤ t then Vp p.1.2 (t - max (u : ℝ) 0) - Vp p.1.2 t
        else D p.2 ((u : ℝ) - t) - Vp p.1.2 t) with hΦ
  have hΦm : Measurable Φ := by
    refine Measurable.prodMk (measurable_pi_iff.2 fun ρ => ?_) (measurable_pi_iff.2 fun u => ?_)
    · exact ((measurable_CInv hVc hV0 hVm ht Q _).sub
        (measurable_CInv hVc hV0 hVm ht Q _)).comp measurable_fst
    · by_cases hu : (u : ℝ) ≤ t
      · simp only [hu, ↓reduceIte]
        exact (((hVm _).comp (measurable_snd.comp measurable_fst)).sub
          ((hVm _).comp (measurable_snd.comp measurable_fst)))
      · simp only [hu, ↓reduceIte]
        exact ((hDm _).comp measurable_snd).sub
          ((hVm _).comp (measurable_snd.comp measurable_fst))
  refine (hΦm.comp ((ha'm.prodMk he'm).prodMk measurable_id)).aemeasurable.congr ?_
  filter_upwards [hc.ae_eq_mk, he.ae_eq_mk, hD, hread] with ω hae hee hDω ⟨hE, hn⟩
  rw [hee] at hE hn
  have hinv : revMapInv (weldDriver γ (x ω).1 t) t = revMapInv (Vp (e' ω)) t :=
    revMapInv_congr_H fun z _ => ReverseFlow.revMap_congr_drive z hE
  have ht0 : t ∈ Icc (0 : ℝ) t := ⟨ht.le, le_rfl⟩
  symm
  refine Prod.ext (funext fun ρ => ?_) (funext fun u => ?_)
  · show pairRaw (coordChange (x ω).1 (revMapInv (weldDriver γ (x ω).1 t) t) Q) ρ.1.1 = _
    rw [hinv, pairRaw_revMapInv_eq_CInv hVc hV0 ht Q ρ.1 _ (e' ω) hn, hae]
    rfl
  · show (if (u : ℝ) ≤ t then weldDriver γ (x ω).1 t (t - max (u : ℝ) 0) -
        weldDriver γ (x ω).1 t t else (x ω).2 ((u : ℝ) - t) - weldDriver γ (x ω).1 t t) = _
    by_cases hu : (u : ℝ) ≤ t
    · have hu0 : (0 : ℝ) ≤ u := u.coe_nonneg
      have hm : t - max (u : ℝ) 0 ∈ Icc (0 : ℝ) t :=
        ⟨by rw [max_eq_left hu0]; linarith, by rw [max_eq_left hu0]; linarith⟩
      simp only [hΦ, Function.comp_apply, id_eq, hu, ↓reduceIte]
      rw [hE hm, hE ht0]
    · simp only [hΦ, Function.comp_apply, id_eq, hu, ↓reduceIte]
      rw [hE ht0, hDω _ (by linarith [not_le.1 hu])]

/-- **Remaining input of `hZc`** (not proved here): a measurable continuous reading `Vp` of the
welding driver of `Γ⁰ = 𝔥₀ + X` from its B1 data, a.s. equal to the welding driver on `[0,t]`,
with Lebesgue-null time-reversed forward hull. -/
def Cor15ZcReadStmt (κ t : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) : Prop :=
  ∃ Vp : B1E → ℝ → ℝ, (∀ e, Continuous (Vp e)) ∧ (∀ e, Vp e 0 = 0) ∧
    (∀ s, Measurable fun e => Vp e s) ∧
    ∀ᵐ ω ∂P, EqOn (weldDriver (Real.sqrt κ) (ofFun (h0rev κ) + X ω) t)
        (Vp (b1Data (ofFun (h0rev κ) + X ω, drive κ B ω))) (Icc 0 t) ∧
      volume (fwdHull (ArcDriver.trev (Vp (b1Data (ofFun (h0rev κ) + X ω, drive κ B ω))) t) t) = 0

/-- **COR15-HREG (2), `hZc`, conditional on `Cor15ZcReadStmt`.** -/
theorem aemeasurable_mod0Data_zipCapUp_c_of_read {κ : ℝ} (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) {t : ℝ} (ht : 0 < t) (hread : Cor15ZcReadStmt κ t P B X) :
    AEMeasurable (fun ω => mod0Data (zipCapUp (Real.sqrt κ) t
      (ofFun (h0rev κ) + X ω, drive κ B ω))) P := by
  obtain ⟨Vp, hVc, hV0, hVm, hr⟩ := hread
  obtain ⟨B₁, hB₁m, -, -, -, hB₁eq⟩ := RS.exists_good_version0 hB
  refine aemeasurable_mod0Data_zipCapUp_of_reading (x := fun ω => (ofFun (h0rev κ) + X ω,
    drive κ B ω)) ht (measurable_coordsFull_c κ hX).aemeasurable (D := drive κ B₁)
    (fun r => by simp only [drive]; exact (hB₁m _).const_mul _) ?_
    (aemeasurable_b1Data_c κ hB hX) hVc hV0 hVm hr
  filter_upwards [hB₁eq] with ω hb r _
  simp [drive, hb]

end Cor15Group
end QuantumZipper
