import QuantumZipper.Proofs.Zipper.LocLenF2Step4
import QuantumZipper.Proofs.Zipper.LocLenLocalityF1Close
import QuantumZipper.Proofs.Zipper.FSMeasF2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), task R7-S2a: F2 step (2a) with open-arc lengths

Open-arc copy of `FSMeas.f2Unscaled_of_B3d` (FSMeasF2.lean:115): from lengths agreeing for the
`P_*` configuration (`F1StmtArc`) to lengths agreeing for the unscaled wedge configuration, by
the canonical rescaling (Sheffield arXiv:1012.4797 §5.1 pp. 60–62, the scaling rule, and §5.4
p. 70). The global rule `GoodTransforms.qBoundaryMeasure_rescale` of the old proof
(`B3d.unzipLengths_canon`, which needs `IsLQGGood` of the unzipped wedge field, tip and base
included) is replaced by the local rule `LocLen.arcLen_rescale_of_hasBdryLimitOn` for a field
good off `{O⁻, 0, O⁺}` (`unzipLengthsArc_scale_off`). Own bookkeeping as the old files.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- **Scaling of the open-arc lengths for a field good off the tip and the root images** (the
`offSet` analogue of `unzipLengthsArc_scale`). -/
theorem unzipLengthsArc_scale_off {γ : ℝ} {x x' : FieldSample} {W : ℝ → ℝ} {a t : ℝ}
    (hγ : 0 < γ) (ha : 0 < a) (ht : 0 ≤ t)
    (hL : ∃ l, Tendsto (fun r : ℝ => (fwdMap W (a ^ 2 * t) r).re) (𝓝[<] (0 : ℝ)) (𝓝 l))
    (hR : ∃ l, Tendsto (fun r : ℝ => (fwdMap W (a ^ 2 * t) r).re) (𝓝[>] (0 : ℝ)) (𝓝 l))
    (hsign : (sideImages W (a ^ 2 * t)).1 ≤ 0 ∧ 0 ≤ (sideImages W (a ^ 2 * t)).2)
    (hgood : IsLQGGoodOff γ (unzippedField γ (x, W) (a ^ 2 * t)) (offSet W (a ^ 2 * t)))
    (hfield : RegEq (unzippedField γ (x', fun s => W (a ^ 2 * s) / a) t)
      (rescale (unzippedField γ (x, W) (a ^ 2 * t)) (Qc γ) a)) :
    unzipLengthsArc γ (x', fun s => W (a ^ 2 * s) / a) t =
      unzipLengthsArc γ (x, W) (a ^ 2 * t) := by
  obtain ⟨l, hl⟩ := hL
  obtain ⟨m, hm⟩ := hR
  obtain ⟨hreg, ⟨ν, hν⟩, -⟩ := hgood
  have hOl : (sideImages (fun s => W (a ^ 2 * s) / a) t).1 = l / a :=
    B3d.sideImages_fst_scale W ha ht hl
  have hOr : (sideImages (fun s => W (a ^ 2 * s) / a) t).2 = m / a :=
    B3d.sideImages_snd_scale W ha ht hm
  have hRl : (sideImages W (a ^ 2 * t)).1 = l := hl.limUnder_eq
  have hRr : (sideImages W (a ^ 2 * t)).2 = m := hm.limUnder_eq
  have hav := B3d.avgReg_eq_of_regEq hfield
  have hsub₁ : Ioo (sideImages W (a ^ 2 * t)).1 0 ⊆ (offSet W (a ^ 2 * t))ᶜ := fun u hu hu' =>
    disjoint_left.1 (Ioo_left_disjoint_offSet W _ hsign.2) hu hu'
  have hsub₂ : Ioo 0 (sideImages W (a ^ 2 * t)).2 ⊆ (offSet W (a ^ 2 * t))ᶜ := fun u hu hu' =>
    disjoint_left.1 (Ioo_right_disjoint_offSet W _ hsign.1) hu hu'
  have ha' : a ≠ 0 := ha.ne'
  have e1 : a * (l / a) = l := by field_simp
  have e2 : a * (m / a) = m := by field_simp
  rw [hRl] at hsub₁
  rw [hRr] at hsub₂
  simp only [unzipLengthsArc, hOl, hOr, hRl, hRr]
  rw [arcLen_congr hav, arcLen_congr hav,
    arcLen_rescale_of_hasBdryLimitOn hreg hγ ha hν (by rw [e1, mul_zero]; exact hsub₁),
    arcLen_rescale_of_hasBdryLimitOn hreg hγ ha hν (by rw [e2, mul_zero]; exact hsub₂),
    arcLen_eq_of_hasBdryLimitOn hreg hν hsub₁, arcLen_eq_of_hasBdryLimitOn hreg hν hsub₂,
    e1, e2, mul_zero]

/-- **F2 step (2a) with open arcs** (copy of `FSMeas.f2Unscaled_of_B3d`). -/
theorem f2UnscaledArc_of_B3d (hD : UnscaledB3dLocStmt) : F2UnscaledArcStmt := by
  intro hF1 κ hκ hκ4 Ω _ P _ X' A B'' hX hA hI hB hIB
  set γ := Real.sqrt κ with hγdef
  have hγ : 0 < γ := Real.sqrt_pos.2 hκ
  set Z := F2.zU γ X' A with hZ
  obtain ⟨hPS, hcfgae⟩ := FSMeas.pstar_of_unscaled_fs hκ hκ4 hX hA hI hB hIB
  filter_upwards [hF1 κ P _ _ hPS, hcfgae, hD κ hκ hκ4 P X' A B'' hX hA hI hB hIB,
    RS.ae_real_alive hB hκ hκ4.le, B5.ae_forall_sideImages_sign hκ hκ4 hB]
    with ω hFω hcfg hDω halive hsign
  intro t ht
  obtain ⟨ha, hY, hdr⟩ := hcfg
  set a := scaleParam γ (Z ω) with ha_def
  have ha2 : 0 < a ^ 2 := by positivity
  set s := t / a ^ 2 with hs_def
  have hs : 0 ≤ s := div_nonneg ht ha2.le
  have hts : a ^ 2 * s = t := by rw [hs_def]; field_simp
  have hagree := hFω s hs
  have hsf : ∀ (x : FieldSample) (W : ℝ → ℝ) (r : ℝ),
      unzipLengthsArc γ (FSMeas.sfTrunc x, W) r = unzipLengthsArc γ (x, W) r := fun x W r =>
    unzipLengthsArc_congr_avgReg γ (FSMeas.avgReg_sfTrunc x) W r
  have hcc2 : (canonConfig γ (Z ω, drive κ B'' ω)).2 =
      fun r => drive κ B'' ω (a ^ 2 * r) / a :=
    B3d.canonConfig_snd_of_max (F1.drive_max κ B'' ω)
  rw [hY, hdr, hsf, hcc2] at hagree
  obtain ⟨l₁, l₂, hl₁, hl₂⟩ := F1.exists_tendsto_sideImages_of_alive (W := drive κ B'' ω)
    (t := a ^ 2 * s) (by positivity) fun x hx => halive x hx _ (by positivity)
  have hfield := hDω.2 s hs
  have hcc : canonConfig γ (Z ω, drive κ B'' ω) =
      (canonical γ (Z ω), fun r => drive κ B'' ω (a ^ 2 * r) / a) :=
    Prod.ext rfl hcc2
  rw [hcc] at hfield
  have key := unzipLengthsArc_scale_off hγ ha hs ⟨l₁, hl₁⟩ ⟨l₂, hl₂⟩ (hsign _ (by positivity))
    (hDω.1 _ (by positivity)) hfield
  rw [key, hts] at hagree
  exact hagree

end LocLen
end QuantumZipper
