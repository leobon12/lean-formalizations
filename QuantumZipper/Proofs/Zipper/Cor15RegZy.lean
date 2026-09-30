import QuantumZipper.Proofs.Zipper.Cor15RegDeriv
import QuantumZipper.Proofs.Zipper.Cor15PosZip
import QuantumZipper.Proofs.Zipper.Cor15LawTransfer
import QuantumZipper.Proofs.RS.TransienceCanon
import QuantumZipper.Proofs.Thm11.CharFunRhs

/-!
# COR15-HREG (2): `hZy`

`AEMeasurable (mod0Data ∘ Z_t ∘ D_t ∘ c)`. A.s. the welding driver of the unzipped field is the
reversed driver `vrev (√κ B) t` on `[0,t]` (`ae_eqOn_weldDriver_zipCapDown`), whose forward hull is
the SLE hull `K_t`, Lebesgue-null a.s. (`NonSwallow.ae_measure_fwdHull_eq_zero`). On that single
event, for every test function at once, the pairings of `Z_t (D_t c)` are `CInv` (`Cor15RegDeriv`)
evaluated at the full circle coordinates of the unzipped field (a.e.-measurable) and at `ω`
(through a continuous version of `B`); the driver coordinates are those of `√κ B`
(`ae_zipCapUp_zipCapDown_snd`). Own assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open CharFun CoordsFull

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

omit [MeasurableSpace Ω] in
theorem continuous_drive_of {B₁ : ℝ≥0 → Ω → ℝ} (hB₁c : ∀ ω, Continuous (B₁ · ω)) (κ : ℝ)
    (ω : Ω) : Continuous (drive κ B₁ ω) :=
  continuous_const.mul ((hB₁c ω).comp continuous_real_toNNReal)

theorem trev_vrev_eqOn {W : ℝ → ℝ} (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∀ r ∈ Icc (0 : ℝ) t, ArcDriver.trev (B2.vrev W t) t r = W r := by
  intro r hr
  simp only [ArcDriver.trev, B2.vrev]
  rw [max_eq_left (by linarith [hr.2] : (0 : ℝ) ≤ t - r),
    min_eq_left (by linarith [hr.1] : t - r ≤ t), max_eq_left ht, min_self, sub_sub_cancel,
    sub_self, hW0]
  ring

/-- **COR15-HREG (2), `hZy`.** -/
theorem aemeasurable_mod0Data_zipCapUp_y (h13 : theorem1_3) (hRSS : Blueprint.RohdeSchrammSimple)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 < t) :
    AEMeasurable (fun ω => mod0Data (zipCapUp (Real.sqrt κ) t
      (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)))) P := by
  obtain ⟨B₁, hB₁m, hB₁c, hB₁0, hB₁, hB₁eq⟩ := RS.exists_good_version0 hB
  set Vp : Ω → ℝ → ℝ := fun ω => B2.vrev (drive κ B₁ ω) t with hVp
  have hW0 : ∀ ω, drive κ B₁ ω 0 = 0 := fun ω => by simp [drive, hB₁0]
  have hVc : ∀ ω, Continuous (Vp ω) := fun ω => by
    have hc := continuous_drive_of hB₁c κ ω
    simp only [hVp]
    exact (hc.comp (continuous_const.sub
      ((continuous_id.max continuous_const).min continuous_const))).sub continuous_const
  have hV0 : ∀ ω, Vp ω 0 = 0 := fun ω => by
    simp only [hVp, B2.vrev, max_self, min_eq_left ht.le, sub_zero, sub_self]
  have hVm : ∀ s, Measurable fun ω => Vp ω s := fun s => by
    simp only [hVp, B2.vrev, drive]
    exact ((hB₁m _).const_mul _).sub ((hB₁m _).const_mul _)
  set Q := Qc (Real.sqrt κ)
  -- the hull is Lebesgue-null
  have hnull : ∀ᵐ ω ∂P, volume (fwdHull (ArcDriver.trev (Vp ω) t) t) = 0 := by
    filter_upwards [NonSwallow.ae_measure_fwdHull_eq_zero hB₁.toIsPreBrownianReal hB₁m hB₁c
      hκ hκ4.le volume t] with ω hω
    rw [CharFunRhs.fwdHull_eq_of_eqOn (ArcDriver.continuous_trev (hVc ω) t)
      (continuous_drive_of hB₁c κ ω) ht.le (trev_vrev_eqOn (hW0 ω) ht.le)]
    exact hω
  -- coordinates of the unzipped field
  have ha := aemeasurable_coordsFull_unzip κ hB hX hind ht.le
  set a' := ha.mk _ with ha'
  have ha'm : Measurable a' := ha.measurable_mk
  -- the candidate
  set Φ : (ℕ → ℝ) × Ω → (TestFun0 H → ℝ) × (ℝ≥0 → ℝ) := fun p =>
    (fun ρ => CInv Vp t Q (tdens ρ.1.1) p - CInv Vp t Q (tdens fun z => -ρ.1.1 z) p,
      fun u => drive κ B₁ p.2 u) with hΦ
  have hΦm : Measurable Φ := by
    refine Measurable.prodMk (measurable_pi_iff.2 fun ρ => ?_) (measurable_pi_iff.2 fun u => ?_)
    · exact (measurable_CInv hVc hV0 hVm ht Q _).sub (measurable_CInv hVc hV0 hVm ht Q _)
    · simp only [drive]
      exact ((hB₁m _).const_mul _).comp measurable_snd
  refine (hΦm.comp (ha'm.prodMk measurable_id)).aemeasurable.congr ?_
  filter_upwards [ha.ae_eq_mk, hnull, hB₁eq,
    ae_eqOn_weldDriver_zipCapDown h13 hRSS hκ hκ4 P B X hB hX hind ht,
    ae_zipCapUp_zipCapDown_snd (P := P) (B := B) (X := X) (h13 := h13) (hRSS := hRSS)
      (hκ := hκ) (hκ4 := hκ4) (hB := hB) (hX := hX) (hind := hind) (ht := ht)] with ω hae hn hb hE hsnd
  have hdr : drive κ B ω = drive κ B₁ ω := by funext r; simp [drive, hb]
  have hE' : EqOn (weldDriver (Real.sqrt κ)
      (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1 t) (Vp ω) (Icc 0 t) := by
    intro r hr; rw [hE hr, hdr]
  have hinv : revMapInv (weldDriver (Real.sqrt κ)
      (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1 t) t =
      revMapInv (Vp ω) t :=
    revMapInv_congr_H fun z _ => ReverseFlow.revMap_congr_drive z hE'
  symm
  refine Prod.ext (funext fun ρ => ?_) (funext fun u => ?_)
  · show pairRaw (coordChange (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1
      (revMapInv (weldDriver (Real.sqrt κ)
        (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1 t) t) Q) ρ.1.1 = _
    rw [hinv, pairRaw_revMapInv_eq_CInv hVc hV0 ht Q ρ.1 _ ω hn, hae]
    rfl
  · show (zipCapUp (Real.sqrt κ) t
      (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω))).2 u = drive κ B₁ ω u
    rw [hsnd u u.2, hdr]

end Cor15Group
end QuantumZipper
