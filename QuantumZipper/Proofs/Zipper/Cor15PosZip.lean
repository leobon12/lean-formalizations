import QuantumZipper.Proofs.Zipper.Cor15PosDriver

/-!
# Corollary 1.5, positive times: zipping up an unzipped configuration

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18;
no proof in the paper). Blocker 1 of `handoff/COR15.md`: for `t > 0`, almost surely
`ConfigEq (Z^CAP_t (Z^CAP_{−t} c)) c`, `c = (𝔥₀ + X, √κ B)`.

* `ae_zipCapUp_zipCapDown_snd` (conditional on Theorem 1.3 and Rohde–Schramm simplicity only):
  the driver of `zipCapUp √κ t (zipCapDown √κ t c)` is `W` on `[0,∞)`.
* `ae_zipCapUp_zipCapDown_fst`: its field is `coordChange y.1 (revMapInv (vrev W t) t) Q`,
  `y.1` the unzipped field.
* `Cor15RezipFieldStmt`: the remaining **field statement** (re-zipping the unzipped field along
  the inverse of the unzipping map restores the field up to `RegEq`). It is *not* proved here;
  it is taken as an explicit hypothesis of
* `ae_configEq_zipCapUp_zipCapDown` (blocker 1) and
* `theorem1_5b_pos_cancel`: Corollary 1.5 (b) for `s > 0`, `t = −s`.

All arguments are **own arguments** (driver algebra of `zipCapUp`, `zipCapDown`); the paper
calls the corollary immediate.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open B2

/-- **Remaining field statement for blocker 1** (not proved; stated for the orchestrator).
For `κ ∈ (0,4)`, `t > 0`, `c = (𝔥₀ + X, W)`, `W = √κ B`, almost surely the unzipped field
`unzippedField √κ c t = coordChange (𝔥₀ + X) (fwdMapInv W t) Q`, re-zipped along the inverse
`revMapInv (vrev W t) t` of the unzipping map (`= f_t`, the centered forward map, on
`ℍ \ η[0,t]`), has the regularized circle averages of `𝔥₀ + X`. -/
def Cor15RezipFieldStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ t : ℝ, 0 < t →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, RegEq
      (coordChange (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t)
        (revMapInv (vrev (drive κ B ω) t) t) (Qc (Real.sqrt κ)))
      (ofFun (h0rev κ) + X ω)

theorem revMapInv_congr_drive {V₁ V₂ : ℝ → ℝ} {t : ℝ} (h : EqOn V₁ V₂ (Icc 0 t)) :
    revMapInv V₁ t = revMapInv V₂ t := by
  have e : revMap V₁ t = revMap V₂ t := funext fun z => ReverseFlow.revMap_congr_drive z h
  unfold revMapInv
  rw [e]

variable {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample)

/-- **Driver half of blocker 1.** A.s. the driver of `Z^CAP_t (Z^CAP_{−t} c)` is `W` on
`[0,∞)`. -/
theorem ae_zipCapUp_zipCapDown_snd (h13 : theorem1_3) (hRSS : Blueprint.RohdeSchrammSimple)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ∀ u : ℝ, 0 ≤ u →
      (zipCapUp (Real.sqrt κ) t
        (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω))).2 u =
      drive κ B ω u := by
  filter_upwards [ae_eqOn_weldDriver_zipCapDown h13 hRSS hκ hκ4 P B X hB hX hind ht,
    hB.eval_zero_ae_eq_zero] with ω hE h0 u hu
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  have eT : weldDriver (Real.sqrt κ)
      (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1 t t =
        0 - drive κ B ω t := by
    rw [hE ⟨ht.le, le_rfl⟩, vrev_of_mem ⟨ht.le, le_rfl⟩, sub_self, hW0]
  show (if u ≤ t then _ else _) = _
  split_ifs with hut
  · rw [eT, max_eq_left hu, hE ⟨by linarith, by linarith⟩,
      vrev_of_mem ⟨by linarith, by linarith⟩, sub_sub_cancel]
    ring
  · rw [not_le] at hut
    rw [eT]
    show drive κ B ω (t + max (u - t) 0) - drive κ B ω t - (0 - drive κ B ω t) = _
    rw [max_eq_left (by linarith), add_sub_cancel]
    ring

/-- **Field of `Z^CAP_t (Z^CAP_{−t} c)`.** A.s. it is the unzipped field re-zipped along
`revMapInv (vrev W t) t`. -/
theorem ae_zipCapUp_zipCapDown_fst (h13 : theorem1_3) (hRSS : Blueprint.RohdeSchrammSimple)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P,
      (zipCapUp (Real.sqrt κ) t
        (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω))).1 =
      coordChange (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t)
        (revMapInv (vrev (drive κ B ω) t) t) (Qc (Real.sqrt κ)) := by
  filter_upwards [ae_eqOn_weldDriver_zipCapDown h13 hRSS hκ hκ4 P B X hB hX hind ht]
    with ω hE
  show coordChange _ (revMapInv _ t) _ = _
  rw [revMapInv_congr_drive hE]
  rfl

/-- **Blocker 1** (conditional on Theorem 1.3, Rohde–Schramm simplicity and the field
statement `Cor15RezipFieldStmt`). For `t > 0`, a.s. `Z^CAP_t (Z^CAP_{−t} c)` agrees with `c`
up to `ConfigEq`. -/
theorem ae_configEq_zipCapUp_zipCapDown (h13 : theorem1_3)
    (hRSS : Blueprint.RohdeSchrammSimple) (hF : Cor15RezipFieldStmt) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ConfigEq
      (zipCapUp (Real.sqrt κ) t
        (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)))
      (ofFun (h0rev κ) + X ω, drive κ B ω) := by
  filter_upwards [ae_zipCapUp_zipCapDown_fst P B X h13 hRSS hκ hκ4 hB hX hind ht,
    ae_zipCapUp_zipCapDown_snd P B X h13 hRSS hκ hκ4 hB hX hind ht,
    hF κ hκ hκ4 t ht P B X hB hX hind] with ω h1 h2 hR
  refine ⟨?_, h2⟩
  rw [h1]
  exact hR

/-- **Corollary 1.5 (b) for `s > 0`, `t = −s`** (conditional as blocker 1):
a.s. `Z^CAP_{s+t} c` and `Z^CAP_s (Z^CAP_t c)` agree up to `ConfigEq`. -/
theorem theorem1_5b_pos_cancel (h13 : theorem1_3) (hRSS : Blueprint.RohdeSchrammSimple)
    (hF : Cor15RezipFieldStmt) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {s t : ℝ} (hs : 0 < s)
    (hst : s + t = 0) :
    ∀ᵐ ω ∂P, ConfigEq
      (zipCap (Real.sqrt κ) (s + t) (ofFun (h0rev κ) + X ω, drive κ B ω))
      (zipCap (Real.sqrt κ) s (zipCap (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω))) := by
  have ht : t < 0 := by linarith
  have hts : -t = s := by linarith
  rw [hst, zipCap_of_nonneg le_rfl, zipCap_of_nonneg hs.le, zipCap_of_neg ht, hts]
  filter_upwards [ae_zipCapUp_zero_eq κ P B X hB hX,
    ae_configEq_zipCapUp_zipCapDown P B X h13 hRSS hF hκ hκ4 hB hX hind hs]
    with ω ⟨e1, e2⟩ ⟨hR, hd⟩
  refine ⟨fun k z => ?_, fun u hu => ?_⟩
  · rw [show avgReg (zipCapUp (Real.sqrt κ) 0 (ofFun (h0rev κ) + X ω, drive κ B ω)).1 k z =
      avgReg (ofFun (h0rev κ) + X ω) k z from congrFun (congrFun e1 k) z, hR k z]
  · rw [e2, hd u hu]

end Cor15Group
end QuantumZipper
