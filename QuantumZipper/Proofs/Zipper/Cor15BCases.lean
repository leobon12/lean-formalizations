import QuantumZipper.Proofs.Zipper.Cor15PosZip
import QuantumZipper.Proofs.Zipper.Cor15LawCongr
import QuantumZipper.Proofs.Zipper.Cor15RezipFin2
import QuantumZipper.Proofs.RS.RohdeSchrammSimple

/-!
# COR15-B: Corollary 1.5(b), case split and the remaining positive-time inputs

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5(b)
(pp. 17–18; the paper calls it an immediate corollary and gives no proof).

Write `c = (𝔥₀ + X, √κ B)`, `U_s = zipCapUp √κ s` (zip, `s ≥ 0`) and `D_a = zipCapDown √κ a`
(unzip, `a ≥ 0`), so `Z^CAP_s = U_s` for `s ≥ 0` and `Z^CAP_{−a} = D_a` for `a > 0`.

Proved (unconditionally, from Theorem 1.3 where indicated):
* `s, t ≤ 0`: `theorem1_5b_nonpos` (`Cor15GroupZero`);
* `s > 0, s + t = 0`: `theorem1_5b_pos_cancel` (`Cor15PosZip`), from Theorem 1.3, Rohde–Schramm
  (`RS.rohdeSchrammSimple`) and `cor15RezipFieldStmt_holds`;
* `s ≥ 0, t = 0`: `theorem1_5b_nonneg_zero` below (own elementary argument: `U_0 c` has the
  regularized field and the driver of `c`, and `U_s` reads only these).

Remaining (stated as exact named Props, not proved here):
* `Cor15ZipUnzipMixStmt`: `U_s (D_a c) ≈ Z_{s−a} c` for `s, a > 0`, `s ≠ a`;
* `Cor15UnzipZipStmt`: `D_b (U_t c) ≈ Z_{t−b} c` for `b, t > 0`;
* `Cor15ZipZipStmt`: `U_s (U_t c) ≈ U_{s+t} c` for `s ≥ 0`, `t > 0`.

Why these are not reducible to the proved cases pathwise (own analysis, see the COR15 handoff):
every derivation of them from the round trip `U_a D_a c ≈ c` and the unzipping semigroup needs one
of these identities at a configuration that is only *equal in law* to `c` (e.g. `D_a c` or
`U_t c`), i.e. a law transfer of an a.s. statement (the pull-back step of
`ZipperGroup.zipperGroup_abstract_law`), or the injectivity of `D_t` on a full-measure set
(`D_t U_t c ≈ c`, which in the abstract lemma comes from Lusin–Souslin + measure preservation).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuantumZipper
namespace Cor15Group

/-- **Remaining input 1** (zipping an unzipped configuration by a different time): for
`s, a > 0`, `s ≠ a`, a.s. `Z^CAP_{s−a} c ≈ U_s (D_a c)`. This is Corollary 1.5(b) for
`s > 0 > t = −a`, `s + t ≠ 0`. -/
def Cor15ZipUnzipMixStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ s a : ℝ, 0 < s → 0 < a → s ≠ a →
    ∀ᵐ ω ∂P, ConfigEq (zipCap (Real.sqrt κ) (s - a) (ofFun (h0rev κ) + X ω, drive κ B ω))
      (zipCapUp (Real.sqrt κ) s (zipCapDown (Real.sqrt κ) a (ofFun (h0rev κ) + X ω, drive κ B ω)))

/-- **Remaining input 2** (unzipping a zipped configuration): for `b, t > 0`, a.s.
`Z^CAP_{t−b} c ≈ D_b (U_t c)`. This is Corollary 1.5(b) for `s = −b < 0 < t`; the case
`b = t` is the round trip `D_t U_t c ≈ c`. -/
def Cor15UnzipZipStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ b t : ℝ, 0 < b → 0 < t →
    ∀ᵐ ω ∂P, ConfigEq (zipCap (Real.sqrt κ) (t - b) (ofFun (h0rev κ) + X ω, drive κ B ω))
      (zipCapDown (Real.sqrt κ) b (zipCapUp (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)))

/-- **Remaining input 3** (zipping semigroup): for `s ≥ 0`, `t > 0`, a.s.
`U_{s+t} c ≈ U_s (U_t c)`. This is Corollary 1.5(b) for `s ≥ 0`, `t > 0`. -/
def Cor15ZipZipStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ s t : ℝ, 0 ≤ s → 0 < t →
    ∀ᵐ ω ∂P, ConfigEq (zipCapUp (Real.sqrt κ) (s + t) (ofFun (h0rev κ) + X ω, drive κ B ω))
      (zipCapUp (Real.sqrt κ) s (zipCapUp (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)))

variable {κ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **Corollary 1.5(b) for `s ≥ 0`, `t = 0`** (unconditional; own elementary argument). -/
theorem theorem1_5b_nonneg_zero (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    {s : ℝ} (hs : 0 ≤ s) :
    ∀ᵐ ω ∂P, ConfigEq
      (zipCap (Real.sqrt κ) (s + 0) (ofFun (h0rev κ) + X ω, drive κ B ω))
      (zipCap (Real.sqrt κ) s (zipCap (Real.sqrt κ) 0 (ofFun (h0rev κ) + X ω, drive κ B ω))) := by
  rw [add_zero, zipCap_of_nonneg (le_refl (0 : ℝ)), zipCap_of_nonneg hs]
  filter_upwards [ae_zipCapUp_zero_eq κ P B X hB hX] with ω ⟨h1, h2⟩
  rw [zipCapUp_congr (γ := Real.sqrt κ) (t := s)
    (x := zipCapUp (Real.sqrt κ) 0 (ofFun (h0rev κ) + X ω, drive κ B ω))
    (x' := (ofFun (h0rev κ) + X ω, drive κ B ω))
    (fun k z => congrFun (congrFun h1 k) z) (fun u _ => congrFun h2 u)]
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- **Corollary 1.5(b) for `s > 0`, `t < 0`**, from Theorem 1.3 and `Cor15ZipUnzipMixStmt`
(the case `s + t = 0` is unconditional given Theorem 1.3). -/
theorem theorem1_5b_pos_neg (h13 : theorem1_3) (hM : Cor15ZipUnzipMixStmt)
    (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) {s t : ℝ} (hs : 0 < s) (ht : t < 0) :
    ∀ᵐ ω ∂P, ConfigEq
      (zipCap (Real.sqrt κ) (s + t) (ofFun (h0rev κ) + X ω, drive κ B ω))
      (zipCap (Real.sqrt κ) s (zipCap (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω))) := by
  by_cases hst : s + t = 0
  · exact theorem1_5b_pos_cancel P B X h13 RS.rohdeSchrammSimple cor15RezipFieldStmt_holds
      hκ hκ4 hB hX hind hs hst
  · have hsa : s ≠ -t := fun h => hst (by linarith)
    have key := hM κ hκ hκ4 P B X hB hX hind s (-t) hs (by linarith) hsa
    rw [zipCap_of_nonneg hs.le, zipCap_of_neg ht, show s + t = s - -t by ring]
    exact key

/-- **Corollary 1.5(b) for `s < 0 < t`**, from `Cor15UnzipZipStmt`. -/
theorem theorem1_5b_neg_pos (hU : Cor15UnzipZipStmt)
    (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) {s t : ℝ} (hs : s < 0) (ht : 0 < t) :
    ∀ᵐ ω ∂P, ConfigEq
      (zipCap (Real.sqrt κ) (s + t) (ofFun (h0rev κ) + X ω, drive κ B ω))
      (zipCap (Real.sqrt κ) s (zipCap (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω))) := by
  have key := hU κ hκ hκ4 P B X hB hX hind (-s) t (by linarith) ht
  rw [zipCap_of_nonneg ht.le, zipCap_of_neg hs, show s + t = t - -s by ring]
  exact key

/-- **Corollary 1.5(b) for `s ≥ 0`, `t > 0`**, from `Cor15ZipZipStmt`. -/
theorem theorem1_5b_nonneg_pos (hZ : Cor15ZipZipStmt)
    (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) :
    ∀ᵐ ω ∂P, ConfigEq
      (zipCap (Real.sqrt κ) (s + t) (ofFun (h0rev κ) + X ω, drive κ B ω))
      (zipCap (Real.sqrt κ) s (zipCap (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω))) := by
  rw [zipCap_of_nonneg ht.le, zipCap_of_nonneg hs, zipCap_of_nonneg (by linarith)]
  exact hZ κ hκ hκ4 P B X hB hX hind s t hs ht

end Cor15Group
end QuantumZipper
