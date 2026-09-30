import QuantumZipper.Proofs.Zipper.Cor15LastPair
import QuantumZipper.Proofs.Zipper.Cor15PosRezip
import QuantumZipper.Proofs.Zipper.Cor15RezipRegGood

/-!
# COR15-LAST (3): `hraw` from a per-test-function regularity statement

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18; no
proof in the paper). Own assembly, on the pattern of `cor15RezipFieldStmt_of` (folded circles)
with the folded circle replaced by the two signed parts `tdens (±ρ)` of a test function:

* a.s. the welding driver of the unzipped field is `V = vrev (√κ B) t` on `[0,t]`
  (`ae_eqOn_weldDriver_zipCapDown`), so the zipped field is
  `coordChange (coordChange c F Q) (revMapInv V t) Q` with `F = fwdMapInv (√κ B) t = revMap V t`
  on `ℍ`;
* `tdens (±ρ)` does not charge `(revMap V t '' ℍ)ᶜ = ℍᶜ ∪ K_t` (`tdens_compl_H`; the hull is
  the SLE hull `K_t`, Lebesgue-null a.s., `rezip_revHull_vrev_eq_fwdHull`,
  `NonSwallow.ae_volume_fwdHull_eq_zero`);
* the deterministic re-zip identity `rezip_apply` then gives `evalReg c.1 (tdens ±ρ)`, provided
  the unzipped field is regular at `(tdens ±ρ).map (revMapInv V t)` (`Cor15RawRegStmt`, the
  remaining input);
* `evalReg (𝔥₀ + X) (tdens ±ρ) = (𝔥₀ + X) (tdens ±ρ)` a.s. (`ae_evalReg_h0rev_add`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **Remaining input for `hraw`** (not proved here): a.s. the unzipped field is regular
(`evalReg` = raw value) at the pushforwards, under `f_t = revMapInv (vrev (√κ B) t) t`, of the two
signed parts of each test function (the analogue of `Cor15RezipRegStmt` for `tdens (±ρ)`). -/
def Cor15RawRegStmt (κ t : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) : Prop :=
  ∀ ρ : TestFun H, ∀ᵐ ω ∂P,
    evalReg (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1
        ((CharFun.tdens ρ.1).map (revMapInv (B2.vrev (drive κ B ω) t) t)) =
      (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1
        ((CharFun.tdens ρ.1).map (revMapInv (B2.vrev (drive κ B ω) t) t)) ∧
    evalReg (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1
        ((CharFun.tdens fun z => -ρ.1 z).map (revMapInv (B2.vrev (drive κ B ω) t) t)) =
      (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1
        ((CharFun.tdens fun z => -ρ.1 z).map (revMapInv (B2.vrev (drive κ B ω) t) t))

/-- **COR15-LAST (3): `hraw`**, conditional on `Cor15RawRegStmt`. -/
theorem hraw_of_reg (h13 : theorem1_3) (hRSS : Blueprint.RohdeSchrammSimple)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 < t)
    (hR : Cor15RawRegStmt κ t P B X) :
    ∀ ρ : TestFun0 H, ∀ᵐ ω ∂P,
      pairRaw (zipCapUp (Real.sqrt κ) t
        (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω))).1 ρ.1.1 =
      pairRaw (ofFun (h0rev κ) + X ω) ρ.1.1 := by
  intro ρ
  obtain ⟨B₁, hB₁m, hB₁c, hB₁0, hB₁, hB₁eq⟩ := RS.exists_good_version0 hB
  obtain ⟨M, δ, hd⟩ := CharFun.exists_dens ρ.1
  obtain ⟨hH1, hH2⟩ := UnzipInvariance.tdens_compl_H ρ.1
  filter_upwards [hR ρ.1, ae_eqOn_weldDriver_zipCapDown h13 hRSS hκ hκ4 P B X hB hX hind ht,
    hB₁eq, NonSwallow.ae_volume_fwdHull_eq_zero hB₁.toIsPreBrownianReal hB₁m hB₁c hκ hκ4.le t,
    UnzipInvariance.ae_evalReg_h0rev_add κ hX hd.tdens_le hd.compact hd.delta hd.sub
      hd.tdens_compl,
    UnzipInvariance.ae_evalReg_h0rev_add κ hX hd.neg.tdens_le hd.neg.compact hd.neg.delta
      hd.neg.sub hd.neg.tdens_compl] with ω hr hE hb hn e1 e2
  obtain ⟨r1, r2⟩ := hr
  have hdr : drive κ B ω = drive κ B₁ ω := by funext r; simp [drive, hb]
  have hWc : Continuous (drive κ B ω) := hdr ▸ continuous_drive_of hB₁c κ ω
  have hW0 : drive κ B ω 0 = 0 := by rw [hdr]; simp [drive, hB₁0]
  have hVc : Continuous (B2.vrev (drive κ B ω) t) := B2.continuous_vrev hWc t
  have hinv : revMapInv (weldDriver (Real.sqrt κ)
      (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1 t) t =
      revMapInv (B2.vrev (drive κ B ω) t) t :=
    revMapInv_congr_H fun z _ => ReverseFlow.revMap_congr_drive z hE
  have hnull : volume (H \ revMap (B2.vrev (drive κ B ω) t) t '' H) = 0 := by
    have h := rezip_revHull_vrev_eq_fwdHull hWc hW0 ht
    rw [revHull] at h
    rw [h, hdr]
    exact hn
  have hμ : ∀ a : ℂ → ℝ, CharFun.tdens a Hᶜ = 0 →
      CharFun.tdens a (revMap (B2.vrev (drive κ B ω) t) t '' H)ᶜ = 0 := by
    intro a ha
    refine measure_mono_null (fun z hz => ?_)
      (measure_union_null ha (withDensity_absolutelyContinuous _ _ hnull))
    by_cases hzH : z ∈ H
    · exact Or.inr ⟨hzH, hz⟩
    · exact Or.inl hzH
  have hF : EqOn (fwdMapInv (drive κ B ω) t) (revMap (B2.vrev (drive κ B ω) t) t) H :=
    fun z hz => B2.fwdMapInv_eq_revMap_vrev hWc hW0 ht.le hz
  have k1 := rezip_apply hVc ht.le (ofFun (h0rev κ) + X ω) (Qc (Real.sqrt κ)) hF (hμ _ hH1) r1
  have k2 := rezip_apply hVc ht.le (ofFun (h0rev κ) + X ω) (Qc (Real.sqrt κ)) hF (hμ _ hH2) r2
  show coordChange (coordChange (ofFun (h0rev κ) + X ω) (fwdMapInv (drive κ B ω) t)
      (Qc (Real.sqrt κ))) (revMapInv (weldDriver (Real.sqrt κ)
        (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1 t) t)
      (Qc (Real.sqrt κ)) (CharFun.tdens ρ.1.1) -
    coordChange (coordChange (ofFun (h0rev κ) + X ω) (fwdMapInv (drive κ B ω) t)
      (Qc (Real.sqrt κ))) (revMapInv (weldDriver (Real.sqrt κ)
        (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1 t) t)
      (Qc (Real.sqrt κ)) (CharFun.tdens fun z => -ρ.1.1 z) =
    (ofFun (h0rev κ) + X ω) (CharFun.tdens ρ.1.1) -
      (ofFun (h0rev κ) + X ω) (CharFun.tdens fun z => -ρ.1.1 z)
  rw [hinv, k1, k2, e1, e2]
  rfl

end Cor15Group
end QuantumZipper
