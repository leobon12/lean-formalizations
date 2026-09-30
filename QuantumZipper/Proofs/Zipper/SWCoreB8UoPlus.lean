import QuantumZipper.Proofs.Zipper.SWCoreB8UoMinus
import QuantumZipper.Proofs.Zipper.UnifUOPlus

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B8 (d), part 4: offset merging off the tip, plus side (offset form of `UnifUOPlus`)

The plus side runs through the reflected pair `(−B, X ∘ refl)` as in
`RegUnif.unifOffTipPlusStmt_of_refl`. The dyadic reflection identity
`avgReg_unzippedField_reflRaw_neg_real` (regularized averages at real points and dyadic radii)
is extended here to all points of `Hbar` (`avgReg_unzippedField_reflRaw_neg_Hbar`), hence to the
regularized values at folded circles of **every** radius (`evalReg_unzippedField_reflRaw_neg`), so
that the boundary approximations at the offset radii `c 2^{-k}` reflect too
(`integral_bdryR_neg_off`).

* **`ae_offTip_plus_off`**: a.s., for all `s ∈ [0,T]` and every test function supported in
  `(0, ∞)`, the offset approximations of `h⁰_s` merge with the dyadic ones along `goodFilter`,
  from the offset input for the reflected pair.

Own bookkeeping (same argument as `UnifUOPlusRefl`, at complex points).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set ComplexConjugate
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5 E1 E1.M4

/-- The reflection identity of the regularized averages at every point of `Hbar`. -/
theorem avgReg_unzippedField_reflRaw_neg_Hbar {γ : ℝ} {x : FieldSample} {W : ℝ → ℝ} {t : ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) {Fx : ℂ × ℝ → ℝ} (hx : IsRegularWith x Fx)
    {FY : ℂ × ℝ → ℝ} (hY : IsRegularWith (unzippedField γ (x, W) t) FY)
    (k : ℕ) {w : ℂ} (hw : w ∈ Hbar) :
    avgReg (unzippedField γ (reflRaw x, -W) t) k w =
      avgReg (unzippedField γ (x, W) t) k (-conj w) := by
  have he_mem : ∀ n, -conj (dyadicRoundC n w) ∈ Hbar := fun n =>
    RegClosure.mapsTo_neg_conj (CircleCont.dyadicRoundC_mem_Hbar hw n)
  have he_lpt : ∀ n, ∃ a b : ℤ, -conj (dyadicRoundC n w) = CircleCont.lpt n a b := fun n =>
    ⟨-⌊(2 : ℝ) ^ n * w.re⌋, ⌊(2 : ℝ) ^ n * w.im⌋, by
      rw [CircleCont.dyadicRoundC_eq_lpt, lpt_neg_conj]⟩
  have hlim : Tendsto (fun n => -conj (dyadicRoundC n w)) atTop (𝓝 (-conj w)) :=
    (Complex.continuous_conj.neg.tendsto w).comp (RegClosure.tendsto_dyadicRoundC w)
  have htend := tendsto_lpt_lattice hY k he_mem he_lpt (RegClosure.mapsTo_neg_conj hw) hlim
  have hseq : avgReg (unzippedField γ (reflRaw x, -W) t) k w = limUnder atTop (fun n =>
      unzippedField γ (x, W) t (foldedCircle (-conj (dyadicRoundC n w)) (radius k))) := by
    unfold avgReg
    apply congrArg (limUnder atTop)
    funext n
    exact unzippedField_reflRaw_neg hW hW0 ht hx _ (radius_pos k)
  rw [hseq, htend.limUnder_eq, hY.avgReg_eq k (RegClosure.mapsTo_neg_conj hw)]

/-- The reflection identity of the regularized values at real folded circles of any radius. -/
theorem evalReg_unzippedField_reflRaw_neg {γ : ℝ} {x : FieldSample} {W : ℝ → ℝ} {t : ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) {Fx : ℂ × ℝ → ℝ} (hx : IsRegularWith x Fx)
    {FY : ℂ × ℝ → ℝ} (hY : IsRegularWith (unzippedField γ (x, W) t) FY) (τ r : ℝ) :
    evalReg (unzippedField γ (reflRaw x, -W) t) (foldedCircle (τ : ℂ) r) =
      evalReg (unzippedField γ (x, W) t) (foldedCircle ((-τ : ℝ) : ℂ) r) := by
  unfold evalReg
  congr 1
  funext k
  rw [show ((-τ : ℝ) : ℂ) = -conj ((τ : ℝ) : ℂ) by simp, ← F1.integral_fc_negConj]
  refine integral_congr_ae ?_
  filter_upwards [RegClosure.fc_ae_mem_Hbar (τ : ℂ) r] with w hw
  exact avgReg_unzippedField_reflRaw_neg_Hbar hW hW0 ht hx hY k hw

/-- **Test integrals of `ν_r` under reflection**, any radius `r > 0`. -/
theorem integral_bdryR_neg_off {γ : ℝ} {x x' : FieldSample} {F F' : ℂ × ℝ → ℝ} {r : ℝ}
    (hx : IsRegularWith x F) (hx' : IsRegularWith x' F') (hr : 0 < r)
    (hev : ∀ τ : ℝ, evalReg x' (foldedCircle (τ : ℂ) r) =
      evalReg x (foldedCircle ((-τ : ℝ) : ℂ) r))
    {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ t, g t ∂bdryR γ x r = ∫ t, g (-t) ∂bdryR γ x' r := by
  rw [SWCore.integral_bdryR_eq_dens γ hx r hr, SWCore.integral_bdryR_eq_dens γ hx' r hr]
  have hpt : ∀ t : ℝ, g t * bdryDens γ x r t =
      (fun u : ℝ => g (-u) * bdryDens γ x' r u) (-t) := by
    intro t
    show g t * bdryDens γ x r t = g (-(-t)) * bdryDens γ x' r (-t)
    unfold bdryDens
    rw [hev (-t), neg_neg]
  refine (integral_congr_ae (ae_of_all _ hpt)).trans ?_
  exact integral_neg_eq_self_volume (F := fun u : ℝ => g (-u) * bdryDens γ x' r u)
    ((hg.comp continuous_neg).mul (GoodSample.continuous_bdryDens γ hx' hr)).aestronglyMeasurable

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ T : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **Offset UO, plus side**, from the offset input for the reflected pair. -/
theorem ae_offTip_plus_off (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hF : AnchorUnifFamOffStmt κ T P (negB B) (reflX X)) :
    ∀ᵐ ω ∂P, ∀ s ∈ Icc 0 T, ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g →
      tsupport g ⊆ Ioi 0 →
      Tendsto (WedgeUnzip.bdryMergeDiff (Real.sqrt κ) (h0f κ s B X ω) g) goodFilter (𝓝 0) := by
  have hB' : IsBrownianReal (negB B) P := hB.neg
  have hX' : IsFreeGFFModConstH (reflX X) P := isFreeGFFModConstH_reflRaw hX
  have hind' : IndepFun (pathOf (negB B)) (reflX X) P := indepFun_neg_reflRaw hind
  filter_upwards [ae_offTip_minus_off hκ hκ4 hT hB' hX' hind' hF, hB.cont,
    hB.eval_zero_ae_eq_zero,
    ae_forall_isRegularWith_joint (κ := κ) (γ := Real.sqrt κ) hB hX hind hT,
    ae_forall_isRegularWith_joint (κ := κ) (γ := Real.sqrt κ) hB' hX' hind' hT,
    ae_isRegularSample_ofFun_h0rev hX κ] with ω hoff hcont hB0 hG hG' hbase s hs g hg hgc hgs
  obtain ⟨G, -, hGr⟩ := hG
  obtain ⟨G', -, hGr'⟩ := hG'
  obtain ⟨Fb, hFb⟩ := hbase
  have hWc : Continuous (drive κ B ω) := drive_continuous hcont
  have hW0 : drive κ B ω 0 = 0 := drive_zero hB0
  have hcfg : cfg κ (negB B) (reflX X) ω =
      (reflRaw (ofFun (h0rev κ) + X ω), -drive κ B ω) := by
    simp only [B2.cfg]
    refine Prod.ext ?_ ?_
    · exact (reflRaw_add_ofFun_h0rev κ (X ω)).symm
    · rw [drive_negB κ B ω]
  have hcfgB : cfg κ B X ω = (ofFun (h0rev κ) + X ω, drive κ B ω) := by
    simp only [B2.cfg]
  have hY : IsRegularWith (h0f κ s B X ω) (fun p => G (s, p)) := by
    rw [h0f_eq_unzippedField]; exact hGr s hs
  have hY' : IsRegularWith (h0f κ s (negB B) (reflX X) ω) (fun p => G' (s, p)) := by
    rw [h0f_eq_unzippedField]; exact hGr' s hs
  have hev : ∀ r : ℝ, ∀ τ : ℝ,
      evalReg (h0f κ s (negB B) (reflX X) ω) (foldedCircle (τ : ℂ) r) =
        evalReg (h0f κ s B X ω) (foldedCircle ((-τ : ℝ) : ℂ) r) := by
    intro r τ
    rw [B2.h0f_eq_unzippedField, B2.h0f_eq_unzippedField, hcfg, hcfgB]
    exact evalReg_unzippedField_reflRaw_neg hWc hW0 hs.1 hFb (hGr s hs) τ r
  have hg' : Continuous fun t : ℝ => g (-t) := hg.comp continuous_neg
  have hgc' : HasCompactSupport fun t : ℝ => g (-t) := hgc.comp_homeomorph (Homeomorph.neg ℝ)
  have hgs' : tsupport (fun t : ℝ => g (-t)) ⊆ Iio 0 := by
    intro t ht
    have h1 := hgs (tsupport_comp_neg_subset ht)
    simp only [mem_Ioi, mem_Iio] at h1 ⊢
    linarith
  refine (hoff s hs _ hg' hgc' hgs').congr' ?_
  filter_upwards [GoodSample.eventually_goodRad_pos] with i hi
  simp only [WedgeUnzip.bdryMergeDiff]
  rw [integral_bdryR_neg_off hY hY' hi (hev _) hg,
    integral_bdryR_neg_off hY hY' (radius_pos _) (hev _) hg]

end RegUnif
end QuantumZipper
