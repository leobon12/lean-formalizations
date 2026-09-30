import QuantumZipper.Proofs.Zipper.LocLenYGood
import QuantumZipper.Proofs.Zipper.LocLenRules
import QuantumZipper.Proofs.Zipper.WedgeXGoodMain
import QuantumZipper.Proofs.Zipper.WedgeTipXReg
import QuantumZipper.Proofs.Zipper.WedgeLogImDom
import QuantumZipper.Proofs.Zipper.WedgeGlobalCara
import QuantumZipper.Proofs.Zipper.WedgeTipXNonvanish

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75 (local lengths), R4a: `XGoodOffAllStmt` from `YGoodOffAllStmt`, without TIP-X

Main results:

* `xGoodOffAll_of_yGoodOff : YGoodOffAllStmt → XGoodOffAllStmt`;
* `xGoodOffAll_of_yMergeOffTip : WedgeUnzip.YMergeOffTipStmt → XGoodOffAllStmt`.

Route: the old `WedgeUnzip.xGoodAll_of_tipX` (WedgeXGoodMain.lean) with the tip tightness
removed, since the boundary limit is now only tested off `offSet W t = {O⁻_t, 0, O⁺_t}`.
A.s., for all `t ≥ 0`: `x_t` and `y_t + ψ_t` have the same countable coordinates
(`WedgeUnzip.coords_unzX_eq`, the paper's step (3)), so `x_t` is good off `offSet` iff
`y_t + ψ_t` is (`isLQGGoodOff_congr_coords`). Regularity: `y_t` is regular, and `ofFun ψ_t` is
regular (`WedgeUnzip.tipXReg_of_logImDomReg`, proved). Boundary: `ψ_t = −γ log‖E_t‖` is continuous
on `ℍ̄` off the root images `O^±_t` (`GlobalCaraStmt`, `ExtNonvanishStmt`, both proved), so the
local rule (5.1) `HasBdryLimitOn.add_ofFun` turns the limit of `y_t` on `{0}ᶜ`, restricted to
`(offSet)ᶜ`, into one for `y_t + ψ_t`. Area: rule (5.1) away from the root images
(`hasAreaLimit_add_far_of`, a copy of `WedgeUnzip.hasAreaLimit_add_far` for an arbitrary area
limit instead of `IsLQGGood`).

Paper: Sheffield, arXiv:1012.4797, p. 70 (the wedge field is the `Γ⁰` field plus a function
continuous away from the root images) and §5.4 rule (5.1); Berestycki–Powell arXiv:2404.16642
Def 6.41 p. 229 (the boundary measure is read where the chart field is GFF + continuous).
Bookkeeping own (as in the old proof).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open GoodSample

/-- `IsLQGGoodOff` only reads the countable coordinates (copy of
`GoodSample.isLQGGood_iff_reconstruct`). -/
theorem isLQGGoodOff_iff_reconstruct (γ : ℝ) (x : FieldSample) (S : Set ℝ) :
    IsLQGGoodOff γ (Factorization.reconstruct (Factorization.coords x)) S ↔
      IsLQGGoodOff γ x S := by
  have he := Factorization.evalReg_congr (Factorization.avgReg_reconstruct_coords x)
  have hb : bdryR γ (Factorization.reconstruct (Factorization.coords x)) = bdryR γ x := by
    funext r; simp only [bdryR, bdryDens, he]
  have ha : areaR γ (Factorization.reconstruct (Factorization.coords x)) = areaR γ x := by
    funext r; simp only [areaR, areaDens, he]
  simp only [IsLQGGoodOff, IsRegularSample, isRegularWith_reconstruct_iff, HasBdryLimitOn,
    HasAreaLimit, hb, ha]

theorem isLQGGoodOff_congr_coords {γ : ℝ} {x y : FieldSample} {S : Set ℝ}
    (h : Factorization.coords x = Factorization.coords y) :
    IsLQGGoodOff γ x S ↔ IsLQGGoodOff γ y S := by
  rw [← isLQGGoodOff_iff_reconstruct γ x, h, isLQGGoodOff_iff_reconstruct]

/-- Copy of `WedgeUnzip.hasAreaLimit_add_far` for a regular `y` with an area limit `μ`. -/
theorem hasAreaLimit_add_far_of {γ : ℝ} {y : FieldSample} (hy : IsRegularSample y)
    {μ : Measure ℂ} (hμ : HasAreaLimit γ y μ) {ψ : ℂ → ℝ}
    {W : Set ℂ} (hW : IsOpen W) (hHW : H ⊆ W) (hψ : ContinuousOn ψ (W ∩ Hbar)) :
    HasAreaLimit γ (y + ofFun ψ) (μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * ψ z))) := by
  have hψH : ContinuousOn ψ H := hψ.mono fun z hz => ⟨hHW hz, le_of_lt (show 0 < z.im from hz)⟩
  refine ⟨withDensity_absolutelyContinuous _ _ hμ.1,
    fun K hK hKH => withDensity_lt_top hK (hμ.2.1 K hK hKH)
      (ContinuousOn.rexp (f := fun z => γ * ψ z) (continuousOn_const.mul (hψH.mono hKH))),
    fun f hf hfc hfH => ?_⟩
  rw [LocalRule.integral_withDensity_exp_of_continuousOn (w := fun z => γ * ψ z) isOpen_H hμ.1
    (continuousOn_const.mul hψH)]
  obtain ⟨δ, hδ, φ', hφ'c, heq⟩ := LocalRule.exists_cutoff hW hψ hfc.isCompact
    (hfH.trans hHW)
  have hlim := (hasAreaLimit_add_ofFun hy hμ hφ'c).2.2 f hf hfc hfH
  have hφf : ContinuousOn (fun z => γ * φ' z) H :=
    continuousOn_const.mul (hφ'c.mono fun z hz => le_of_lt (show 0 < z.im from hz))
  rw [LocalRule.integral_withDensity_exp_of_continuousOn isOpen_H hμ.1 hφf] at hlim
  have htarget : ∫ z, Real.exp (γ * φ' z) * f z ∂μ = ∫ z, Real.exp (γ * ψ z) * f z ∂μ := by
    congr 1
    funext z
    by_cases hz : z ∈ tsupport f
    · rw [heq (Metric.self_subset_cthickening _ hz)]
    · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]
  rw [htarget] at hlim
  refine hlim.congr' ?_
  filter_upwards [tendsto_goodRad.eventually (Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < δ / 4))]
    with i hi
  exact (WedgeUnzip.integral_areaR_cutoff γ y hδ heq subset_rfl hfH hi.1 hi.2.le).symm

/-- **X-G off the root images from the `Γ⁰` goodness off the tip** (no TIP-X). -/
theorem xGoodOffAll_of_yGoodOff (hY : YGoodOffAllStmt) : XGoodOffAllStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  filter_upwards [WedgeUnzip.coords_unzX_eq hκ hκ4 hB hX hind, hY κ hκ hκ4 P B X hB hX hind,
    WedgeUnzip.globalCaraStmt_holds κ hκ hκ4 P B hB,
    WedgeUnzip.extNonvanishStmt_holds κ hκ hκ4 P B hB,
    WedgeUnzip.tipXReg_of_logImDomReg WedgeUnzip.logImDomRegStmt_holds κ hκ hκ4 P B hB]
    with ω hco hyω hCω hNVω hRω t ht
  rw [isLQGGoodOff_congr_coords (hco t ht)]
  have hψ : ContinuousOn (WedgeUnzip.logTipFun κ (drive κ B ω) t)
      ((((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet (drive κ B ω) t)ᶜ ∩ Hbar) := by
    intro u hu
    have hc : ContinuousWithinAt (F2.extInv (drive κ B ω) t)
        ((((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet (drive κ B ω) t)ᶜ ∩ Hbar) u :=
      (hCω t ht u hu.2).mono inter_subset_right
    have hne : F2.extInv (drive κ B ω) t u ≠ 0 := hNVω t ht u hu.2 hu.1
    have hlog : ContinuousWithinAt (fun v => Real.log ‖F2.extInv (drive κ B ω) t v‖)
        ((((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet (drive κ B ω) t)ᶜ ∩ Hbar) u :=
      hc.norm.log (norm_ne_zero_iff.2 hne)
    exact (hlog.const_mul (Real.sqrt κ)).neg
  have hWo : IsOpen ((((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet (drive κ B ω) t)ᶜ) :=
    ((WedgeUnzip.isCompact_tipSet _ t).image Complex.continuous_ofReal).isClosed.isOpen_compl
  have hHW : H ⊆ (((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet (drive κ B ω) t)ᶜ := fun z hz ⟨s, _, hs⟩ => by
    have h0 : (0 : ℝ) < z.im := hz
    rw [← hs, Complex.ofReal_im] at h0
    exact lt_irrefl _ h0
  have hUo : IsOpen (offSet (drive κ B ω) t)ᶜ := (isClosed_offSet _ t).isOpen_compl
  have hUW : ∀ s ∈ (offSet (drive κ B ω) t)ᶜ,
      (s : ℂ) ∈ (((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet (drive κ B ω) t)ᶜ := by
    rintro s hs ⟨u, hu, hus⟩
    obtain rfl := Complex.ofReal_injective hus
    apply hs
    rcases hu with rfl | rfl <;> simp [offSet]
  have hsub : (offSet (drive κ B ω) t)ᶜ ⊆ ({0} : Set ℝ)ᶜ :=
    compl_subset_compl.2 (singleton_subset_iff.2 (by simp [offSet]))
  obtain ⟨⟨F, hF⟩, ⟨ν, hν⟩, ⟨μ, hμ⟩⟩ := hyω t ht
  exact ⟨⟨_, WedgeUnzip.isRegularWith_add hF (hRω t ht)⟩,
    ⟨_, (hν.mono hUo hsub).add_ofFun ⟨F, hF⟩ hUo hWo hUW hψ⟩,
    ⟨_, hasAreaLimit_add_far_of ⟨F, hF⟩ hμ hWo hHW hψ⟩⟩

/-- **X-G off the root images, closed form**: from the offset merging input of Theorem 1.3. -/
theorem xGoodOffAll_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) : XGoodOffAllStmt :=
  xGoodOffAll_of_yGoodOff (yGoodOffAll_of_yMergeOffTip hYO)

end LocLen
end QuantumZipper
