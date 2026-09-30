import QuantumZipper.Proofs.Thm18.R18UpWeld
import QuantumZipper.Proofs.Thm18.R18MuScale
import QuantumZipper.Proofs.Thm18.R18G4Nodes
import QuantumZipper.Proofs.Zipper.LocLenCanonRegMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 T8a (deterministic part): `Z^LEN_{−ℓ₁} ∘ Z^LEN_{−ℓ₂} = Z^LEN_{−(ℓ₁+ℓ₂)}` on area-carrying
configurations

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (2) (p. 26);
the paper gives no separate proof (it follows from additivity of the unzipped length along the
capacity flow, §1.4, and the Brownian/Loewner scaling, §5.1 pp. 60–62). Copy of
`Thm18Asm.unzipTime_add_of` / `Thm18Asm.downDownData_of` (G4GroupNeg.lean) and
`Thm18Asm.unzipFieldRegData_of_cap` (G4UnzipGoodField.lean) under the substitution rule of
`handoff/R18-PLAN.md` §1: open-arc lengths, and the scale (1.8) read from the carried area.

* `lenTimeOpen_add_of`: first passage under the one-step length cocycle (verbatim copy of
  `unzipTime_add_of`);
* `fwdMapInv_capDrv_comp`, `zipCapDownA_zipCapDownA_apply_open`,
  `areaScale_zipCapDownA_zipCapDownA`: the carried area of a twice unzipped configuration is the
  area of the configuration unzipped by the sum of the times (Loewner flow property of the inverse
  maps, `RegUnif.eqOn_fwdMapInv_shift`, `RegCont.fwdMapInv_add`); **own elementary bookkeeping**;
* `configEqOff_zipLenDownA_add_of`: the deterministic group law in the unzipping case.

The area of a zipped field is never read: all scales are `areaScale` of carried areas, identified
with the unzipped field's scale only through the unzipping area rule (T3, `unzipArea_holds`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm LocLen B2

/-! ## First passage under the one-step length cocycle -/

/-- **First passage under the one-step cocycle** (copy of `Thm18Asm.unzipTime_add_of` with
open-arc lengths): `τ(ℓ₁ + ℓ₂, c) = t₂ + a² τ(ℓ₁, c')` when `L'(s) + ℓ₂ = L(t₂ + a² s)`. -/
theorem lenTimeOpen_add_of {γ ℓ₁ ℓ₂ a : ℝ} (h₁ : 0 ≤ ℓ₁) (h₂ : 0 ≤ ℓ₂)
    {c c' : FieldSample × (ℝ → ℝ)} (hpos : 0 < a)
    (hC : ∀ s : ℝ, 0 ≤ s → (unzipLengthsOpen γ c' s).1 + ENNReal.ofReal ℓ₂ =
      (unzipLengthsOpen γ c (lenTimeOpen γ ℓ₂ c + a ^ 2 * s)).1)
    (hne : ∃ t : ℝ, 0 ≤ t ∧ ENNReal.ofReal (ℓ₁ + ℓ₂) ≤ (unzipLengthsOpen γ c t).1) :
    lenTimeOpen γ (ℓ₁ + ℓ₂) c = lenTimeOpen γ ℓ₂ c + a ^ 2 * lenTimeOpen γ ℓ₁ c' := by
  set t₂ := lenTimeOpen γ ℓ₂ c with ht₂
  set L : ℝ → ℝ≥0∞ := fun t => (unzipLengthsOpen γ c t).1 with hL
  set L' : ℝ → ℝ≥0∞ := fun s => (unzipLengthsOpen γ c' s).1 with hL'
  set f : ℝ → ℝ := fun s => t₂ + a ^ 2 * s with hf
  have hadd : ENNReal.ofReal (ℓ₁ + ℓ₂) = ENNReal.ofReal ℓ₁ + ENNReal.ofReal ℓ₂ :=
    ENNReal.ofReal_add h₁ h₂
  have ht₂0 : 0 ≤ t₂ := lenTimeOpen_nonneg γ ℓ₂ c
  have ha2 : a ^ 2 ≠ 0 := by positivity
  have hbelow : ∀ t, 0 ≤ t → ENNReal.ofReal ℓ₂ ≤ L t → t₂ ≤ t := fun t ht hLt =>
    csInf_le ⟨0, fun _ h => h.1⟩ ⟨ht, hLt⟩
  set S₁ : Set ℝ := {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal ℓ₁ ≤ L' s} with hS₁
  have hS : {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal (ℓ₁ + ℓ₂) ≤ L t} = f '' S₁ := by
    ext t
    constructor
    · rintro ⟨ht, hLt⟩
      have hle : t₂ ≤ t := hbelow t ht (le_trans (by rw [hadd]; exact le_add_self) hLt)
      refine ⟨(t - t₂) / a ^ 2, ⟨div_nonneg (by linarith) (sq_nonneg a), ?_⟩, ?_⟩
      · have e := hC ((t - t₂) / a ^ 2) (div_nonneg (by linarith) (sq_nonneg a))
        have hft : t₂ + a ^ 2 * ((t - t₂) / a ^ 2) = t := by field_simp; ring
        rw [hft] at e
        have : ENNReal.ofReal ℓ₁ + ENNReal.ofReal ℓ₂ ≤
            L' ((t - t₂) / a ^ 2) + ENNReal.ofReal ℓ₂ := by
          rw [← hadd]; exact hLt.trans_eq e.symm
        exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 this
      · simp only [hf]; field_simp; ring
    · rintro ⟨s, ⟨hs, hLs⟩, rfl⟩
      have e := hC s hs
      refine ⟨by simp only [hf]; positivity, ?_⟩
      show ENNReal.ofReal (ℓ₁ + ℓ₂) ≤ L (t₂ + a ^ 2 * s)
      rw [hL]
      simp only
      rw [← e, hadd]
      gcongr
  have hmono : Monotone f := fun x y hxy => by
    simp only [hf]; gcongr
  have hne₁ : S₁.Nonempty := by
    obtain ⟨t, ht, hLt⟩ := hne
    have hmem : t ∈ f '' S₁ := hS ▸ ⟨ht, hLt⟩
    obtain ⟨s, hs, -⟩ := hmem
    exact ⟨s, hs⟩
  have hcont : Continuous f := by simp only [hf]; fun_prop
  show sInf {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal (ℓ₁ + ℓ₂) ≤ L t} = f (sInf S₁)
  rw [hS, hmono.map_csInf_of_continuousAt hcont.continuousAt hne₁ ⟨0, fun _ h => h.1⟩]

/-! ## The carried area of a twice unzipped configuration -/

/-- **Flow property of the inverse maps for the driver of `zipCapDown`** (copy of
`F1.fwdMapInv_shiftDrv_comp` with the driver `W(t + max · 0) − W t`). -/
theorem fwdMapInv_capDrv_comp {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t u : ℝ}
    (ht : 0 ≤ t) (hu : 0 ≤ u) {z : ℂ} (hz : z ∈ H) :
    fwdMapInv W t (fwdMapInv (fun r => W (t + max r 0) - W t) u z) = fwdMapInv W (t + u) z := by
  have hE := RegUnif.eqOn_fwdMapInv_shift hW ht hu hz
  rw [hE, RegCont.fwdMapInv_add hW hW0 ht hu hz]
  congr 1
  refine ReverseFlow.revMap_congr_drive z fun q hq => ?_
  rw [vrev_of_mem ⟨hq.1, hq.2.trans (le_add_of_nonneg_left ht)⟩]

/-- **Area of a twice unzipped configuration on open subsets of `ℍ`**: unzipping by `t` and then
by `u` transports the area as unzipping by `t + u`. -/
theorem zipCapDownA_zipCapDownA_apply_open {γ t u : ℝ} {c : AreaConfig} (hc : Continuous c.drv)
    (hc0 : c.drv 0 = 0) (ht : 0 ≤ t) (hu : 0 ≤ u) {S : Set ℂ} (hSo : IsOpen S) (hSH : S ⊆ H) :
    (zipCapDownA γ u (zipCapDownA γ t c)).area S = (zipCapDownA γ (t + u) c).area S := by
  set W₂ : ℝ → ℝ := fun r => c.drv (t + max r 0) - c.drv t with hW₂
  have hW₂c : Continuous W₂ := (F1.zipCapDown_snd_props (γ := γ) (τ := t) (c := c.toPair) hc).1
  have hW₂0 : W₂ 0 = 0 := (F1.zipCapDown_snd_props (γ := γ) (τ := t) (c := c.toPair) hc).2.1
  have hdrv : (zipCapDownA γ t c).drv = W₂ := rfl
  have hSm : MeasurableSet S := hSo.measurableSet
  -- the intermediate image is open and lies in `ℍ`
  have hIo : IsOpen (fwdMapInv W₂ u '' S) := by
    rw [← E6.preimage_fwdMap_inter_eq hW₂c hW₂0 hu hSH, Set.inter_comm]
    exact (E6.continuousOn_fwdMap_compl hW₂c hu).isOpen_inter_preimage
      (FwdHolo.isOpen_compl_fwdHull hW₂c hu) hSo
  have hIH : fwdMapInv W₂ u '' S ⊆ H := by
    rw [← E6.preimage_fwdMap_inter_eq hW₂c hW₂0 hu hSH]
    exact fun z hz => hz.2.1
  have e1 : (zipCapDownA γ u (zipCapDownA γ t c)).area S =
      (zipCapDownA γ t c).area (fwdMapInv W₂ u '' S) := by
    rw [zipCapDownA_area_eq_areaTransport, hdrv]
    exact E6.areaTransport_apply hW₂c hW₂0 hu _ hSm hSH
  have e2 : (zipCapDownA γ t c).area (fwdMapInv W₂ u '' S) =
      c.area (fwdMapInv c.drv t '' (fwdMapInv W₂ u '' S)) := by
    rw [zipCapDownA_area_eq_areaTransport]
    exact E6.areaTransport_apply hc hc0 ht _ hIo.measurableSet hIH
  have e3 : fwdMapInv c.drv t '' (fwdMapInv W₂ u '' S) = fwdMapInv c.drv (t + u) '' S := by
    rw [Set.image_image]
    exact Set.image_congr fun z hz => fwdMapInv_capDrv_comp hc hc0 ht hu (hSH hz)
  have e4 : (zipCapDownA γ (t + u) c).area S = c.area (fwdMapInv c.drv (t + u) '' S) := by
    rw [zipCapDownA_area_eq_areaTransport]
    exact E6.areaTransport_apply hc hc0 (add_nonneg ht hu) _ hSm hSH
  rw [e1, e2, e3, e4]

/-- **Scale (1.8) of a twice unzipped configuration.** -/
theorem areaScale_zipCapDownA_zipCapDownA {γ t u : ℝ} {c : AreaConfig} (hc : Continuous c.drv)
    (hc0 : c.drv 0 = 0) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    areaScale (zipCapDownA γ u (zipCapDownA γ t c)).area =
      areaScale (zipCapDownA γ (t + u) c).area := by
  unfold areaScale
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq]
  rw [zipCapDownA_zipCapDownA_apply_open hc hc0 ht hu (Metric.isOpen_ball.inter isOpen_H)
    inter_subset_right]

/-! ## The deterministic group law, unzipping case -/

/-- **`Z^LEN_{−ℓ₁} ∘ Z^LEN_{−ℓ₂} = Z^LEN_{−(ℓ₁+ℓ₂)}` at a configuration** (copy of
`Thm18Asm.downDownData_of` + `Thm18Asm.configEq_zipLenDown_add_of`, area-carrying maps, open-arc
lengths). Inputs: the unzipping area rule of `c` at all times (T3), the capacity field cocycle,
the regularity package of the canonical rescaling along the flow (`CanonRegArc`, which contains
S2), regularity of the unzipped fields, the capacity cocycle of the left open-arc length, no
overshoot at the length time of `ℓ₂`, and that the level `ℓ₁ + ℓ₂` is reached. -/
theorem configEqOff_zipLenDownA_add_of {γ ℓ₁ ℓ₂ : ℝ} (hγ : 0 < γ) (h₁ : 0 ≤ ℓ₁) (h₂ : 0 ≤ ℓ₂)
    {c : AreaConfig} (hc : Continuous c.drv) (hc0 : c.drv 0 = 0)
    (hA : ∀ t : ℝ, 0 ≤ t → ∀ S : Set ℂ, MeasurableSet S → S ⊆ H →
      qAreaMeasure γ (unzippedField γ c.toPair t) S = c.area (fwdMapInv c.drv t '' S))
    (hcap : UnzipCapRegData γ c.toPair)
    (hcan : ∀ τ r : ℝ, 0 ≤ τ → 0 ≤ r → CanonRegArc γ (zipCapDown γ τ c.toPair) r)
    (hreg : ∀ t : ℝ, 0 ≤ t → IsRegularSample (unzippedField γ c.toPair t))
    (hcoc : ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → (unzipLengthsOpen γ c.toPair (u + s)).1 =
      (unzipLengthsOpen γ c.toPair u).1 + (unzipLengthsOpen γ (zipCapDown γ u c.toPair) s).1)
    (hpass : (unzipLengthsOpen γ c.toPair (lenTimeOpen γ ℓ₂ c.toPair)).1 = ENNReal.ofReal ℓ₂)
    (hne : ∃ t : ℝ, 0 ≤ t ∧ ENNReal.ofReal (ℓ₁ + ℓ₂) ≤ (unzipLengthsOpen γ c.toPair t).1) :
    ConfigEqOff (zipLenDownA γ (ℓ₁ + ℓ₂) c).toPair
      (zipLenDownA γ ℓ₁ (zipLenDownA γ ℓ₂ c)).toPair := by
  set p := c.toPair with hp
  set t₂ := lenTimeOpen γ ℓ₂ p with ht₂def
  set c₂ := zipCapDownA γ t₂ c with hc₂def
  set c' := zipCapDown γ t₂ p with hc'def
  have ht₂ : 0 ≤ t₂ := lenTimeOpen_nonneg _ _ _
  have hσ : ∀ t : ℝ, 0 ≤ t →
      areaScale (zipCapDownA γ t c).area = scaleParam γ (unzippedField γ p t) :=
    fun t ht => areaScale_zipCapDownA_eq hc hc0 ht (hA t ht)
  set a := scaleParam γ c'.1 with hadef
  have ha : 0 < a := (hcan t₂ 0 ht₂ le_rfl).1
  have hc₂a : areaScale c₂.area = a := hσ t₂ ht₂
  have hZ₂ : (zipLenDownA γ ℓ₂ c).toPair = canonConfig γ c' := toPair_canonAConfig hc₂a
  obtain ⟨hW', hW'0, hW'max⟩ := F1.zipCapDown_snd_props (γ := γ) (τ := t₂) (c := p) hc
  -- the one-step length cocycle
  have hL : ∀ s : ℝ, 0 ≤ s → (unzipLengthsOpen γ (canonConfig γ c') s).1 + ENNReal.ofReal ℓ₂ =
      (unzipLengthsOpen γ p (t₂ + a ^ 2 * s)).1 := by
    intro s hs
    have e := unzipLengthsArc_canon_of_reg hγ hW' hW'0 hW'max hs (hcan t₂ s ht₂ hs)
    have hco := hcoc t₂ (a ^ 2 * s) ht₂ (by positivity)
    rw [unzipLengthsOpen_eq] at hco hpass ⊢
    rw [e, hco, hpass, add_comm]
  set τ₁ := lenTimeOpen γ ℓ₁ (zipLenDownA γ ℓ₂ c).toPair with hτ₁def
  have hτ₁ : 0 ≤ τ₁ := lenTimeOpen_nonneg _ _ _
  have hT : lenTimeOpen γ (ℓ₁ + ℓ₂) p = t₂ + a ^ 2 * τ₁ := by
    rw [hτ₁def, hZ₂]
    exact lenTimeOpen_add_of h₁ h₂ ha hL hne
  set T := t₂ + a ^ 2 * τ₁ with hTdef
  have hT0 : 0 ≤ T := by positivity
  set σ := scaleParam γ (unzippedField γ p T) with hσdef
  have hσpos : 0 < σ := (hcan T 0 hT0 le_rfl).1
  -- the scale of the composed map, read from the carried area
  set A₁ := areaScale (zipCapDownA γ τ₁ (zipLenDownA γ ℓ₂ c)).area with hA₁def
  have hc₂c : Continuous c₂.drv := hW'
  have hA₁ : A₁ = σ / a := by
    have e1 := zipCapDownA_canonAConfig_area (γ := γ) (T := a ^ 2 * τ₁) (by positivity)
      (c := c₂) hc₂c (hc₂a ▸ ha)
    rw [hc₂a, show a ^ 2 * τ₁ / a ^ 2 = τ₁ by field_simp] at e1
    show areaScale (zipCapDownA γ τ₁ (canonAConfig γ c₂)).area = σ / a
    rw [e1, areaScale_map_inv_mul _ ha,
      areaScale_zipCapDownA_zipCapDownA hc hc0 ht₂ (by positivity), hσ _ hT0]
  have hA₁pos : 0 < A₁ := by rw [hA₁]; exact div_pos hσpos ha
  have hσA : σ = a * A₁ := by rw [hA₁]; field_simp
  have hA₃ : areaScale (zipCapDownA γ (lenTimeOpen γ (ℓ₁ + ℓ₂) p) c).area = σ := by
    rw [hT]; exact hσ _ hT0
  refine ⟨?_, fun v hv => ?_⟩
  · -- fields
    have hF1 : RegEq (unzippedField γ (canonConfig γ c') τ₁)
        (rescale (unzippedField γ c' (a ^ 2 * τ₁)) (Qc γ) a) :=
      WedgeUnzip.regEq_unzippedField_canonConfig (y := c'.1) (W := c'.2) hW' hW'0 hW'max ha hτ₁
        (hcan t₂ τ₁ ht₂ hτ₁).2.1 (hcan t₂ τ₁ ht₂ hτ₁).2.2.1
    have hF2 : rescale (unzippedField γ c' (a ^ 2 * τ₁)) (Qc γ) a =
        rescale (unzippedField γ p T) (Qc γ) a :=
      Cor15Group.coordChange_congr_regEq (hcap t₂ (a ^ 2 * τ₁) ht₂ (by positivity)) _ _
    have hF3 : rescale (unzippedField γ (canonConfig γ c') τ₁) (Qc γ) A₁ =
        rescale (rescale (unzippedField γ p T) (Qc γ) a) (Qc γ) A₁ := by
      rw [← hF2]
      exact Cor15Group.coordChange_congr_regEq hF1 _ _
    have hF4 := (hreg T hT0).regEq_rescale_rescale (Qc γ) ha hA₁pos
    intro k z _
    show avgReg (rescale (unzippedField γ p (lenTimeOpen γ (ℓ₁ + ℓ₂) p)) (Qc γ)
        (areaScale (zipCapDownA γ (lenTimeOpen γ (ℓ₁ + ℓ₂) p) c).area)) k z =
      avgReg (rescale (unzippedField γ (zipLenDownA γ ℓ₂ c).toPair τ₁) (Qc γ) A₁) k z
    rw [hA₃, hT, hZ₂, hF3, hσA]
    exact (hF4 k z).symm
  · -- drivers
    have hZ2drv : ∀ r : ℝ, (zipLenDownA γ ℓ₂ c).drv r =
        (c.drv (t₂ + max (a ^ 2 * max r 0) 0) - c.drv t₂) / a := fun r => by
      show (c.drv (t₂ + max (areaScale c₂.area ^ 2 * max r 0) 0) - c.drv t₂) / areaScale c₂.area = _
      rw [hc₂a]
    show (c.drv (lenTimeOpen γ (ℓ₁ + ℓ₂) p + max (areaScale (zipCapDownA γ
        (lenTimeOpen γ (ℓ₁ + ℓ₂) p) c).area ^ 2 * max v 0) 0) - c.drv (lenTimeOpen γ (ℓ₁ + ℓ₂) p)) /
        areaScale (zipCapDownA γ (lenTimeOpen γ (ℓ₁ + ℓ₂) p) c).area =
      ((zipLenDownA γ ℓ₂ c).drv (τ₁ + max (A₁ ^ 2 * max v 0) 0) -
        (zipLenDownA γ ℓ₂ c).drv τ₁) / A₁
    rw [hZ2drv, hZ2drv, hA₃, hT, hσA, max_eq_left hv, max_eq_left hτ₁,
      max_eq_left (by positivity : (0 : ℝ) ≤ (a * A₁) ^ 2 * v),
      max_eq_left (by positivity : (0 : ℝ) ≤ A₁ ^ 2 * v),
      max_eq_left (by positivity : (0 : ℝ) ≤ τ₁ + A₁ ^ 2 * v),
      max_eq_left (by positivity : (0 : ℝ) ≤ a ^ 2 * τ₁),
      max_eq_left (by positivity : (0 : ℝ) ≤ a ^ 2 * (τ₁ + A₁ ^ 2 * v)),
      show t₂ + a ^ 2 * (τ₁ + A₁ ^ 2 * v) = t₂ + a ^ 2 * τ₁ + (a * A₁) ^ 2 * v by ring]
    field_simp
    ring

end R18
end QuantumZipper
