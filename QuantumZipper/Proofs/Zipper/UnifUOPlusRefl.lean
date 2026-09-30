import QuantumZipper.Proofs.Zipper.F1ReflReg
import QuantumZipper.Proofs.Zipper.B2Defs
import QuantumZipper.Proofs.LQG.AtomlessUncond
import QuantumZipper.Statements.CouplingFields

/-!
# UNIF-UO (plus side): the raw reflection of a field sample and the unzipped field

Task UO-PLUS (decision D26, `UnifUOMain.lean`). The plus side of `UnifOffTipStmt` is obtained by
reflecting the coupling in the real axis: the reflected driver `B ↦ −B` is again Brownian and the
reflected field `X ↦ X(· ∘ (z ↦ −z̄))` is again a free GFF modulo constants, because `neumannH`
is invariant under `z ↦ −z̄`. The time-`s` picture of the reflected pair is the reflection of the
time-`s` picture of the original pair, so a window on the positive side is the mirror image of a
window on the negative side, where `RegUnif.ae_offTip_minus` applies.

This file contains the **deterministic, pathwise** part. The reflection is taken *raw*,
`reflRaw x μ = x (μ.map (z ↦ −z̄))`, rather than through `RegClosure.reflectH`
(`μ ↦ evalReg x (μ.map (z ↦ −z̄))`), so that it commutes with `ofFun` and with the deterministic
part `𝔥₀(κ)` by a pure `funext` argument (`reflRaw_add_ofFun_h0rev`): this is what makes the
reflection of the configuration `(𝔥₀(κ) + X, W)` the configuration of the reflected pair.

The two reflections agree after regularization: for a **regular** field `x`,
`avgReg (reflRaw x) k w = avgReg x k (−w̄)` on `Hbar` (`avgReg_reflRaw_of_regular`: the folded
circles of `−z̄` are the folded circles of `−z̄`, `F1.fc_map_negConj`, and `−z̄` of a dyadic
lattice point is again a lattice point at the same level, so the raw values are the witness
values, `F1.raw_fc_lpt_eq_evalReg`). Consequently:

* **`unzippedField_reflRaw_neg`** (the analogue of `F1.unzippedField_reflect_fc` for the raw
  reflection): the unzipped field of `(reflRaw x, −W)` at the folded circle `(d, s)` is the
  unzipped field of `(x, W)` at `(−d̄, s)`. Route (own elementary argument): the flow identity
  `fwdMapInv (−W) t = r ∘ fwdMapInv W t ∘ r` with `r z = −z̄` (`F1.fwdMapInv_neg_eq`), the
  `evalReg` terms through `avgReg_reflRaw_of_regular` and `F1.integral_fc_negConj`, the
  derivative terms through `F1.norm_deriv_negConj_conj` and `F1.integral_fc_negConj`;
* **`avgReg_unzippedField_reflRaw_neg_real`**: for a regular base field and a regular unzipped
  field, `avgReg (unzipped (reflRaw x, −W) t) k u = avgReg (unzipped (x, W) t) k (−u)` at real
  `u` — the pathwise identity used for the boundary measures. (The two dyadic sequences differ,
  `dyadicRoundC` being floor rounding, so the comparison is by convergence to the witness,
  `tendsto_lpt_lattice`.)

Sheffield, arXiv:1012.4797, §5.4 p. 72 ("by symmetry") for the reflection dichotomy; the
identifications themselves are own elementary arguments.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate

namespace QuantumZipper
namespace RegUnif

/-- The raw reflection `x ↦ x(· ∘ (z ↦ −z̄))` of a field sample. -/
def reflRaw (x : FieldSample) : FieldSample := fun μ => x (μ.map fun z => -conj z)

theorem measurable_negConj : Measurable fun z : ℂ => -conj z :=
  Complex.continuous_conj.neg.measurable

/-- `reflRaw` is measurable for the Pi-measurable structure on `FieldSample`. -/
theorem measurable_reflRaw : Measurable (reflRaw : FieldSample → FieldSample) :=
  Measurable.of_eval fun μ => measurable_pi_apply (μ.map fun z => -conj z)

/-- Reflection sends the dyadic lattice points of level `n` to lattice points of level `n`. -/
theorem lpt_neg_conj (n : ℕ) (a b : ℤ) :
    -conj (CircleCont.lpt n a b) = CircleCont.lpt n (-a) b := by
  apply Complex.ext <;> simp [CircleCont.lpt, neg_div]

/-- **Regularized averages of the raw reflection**, for a regular field `x`: reflecting the
field reflects the argument. -/
theorem avgReg_reflRaw_of_regular {x : FieldSample} {Fx : ℂ × ℝ → ℝ} (hx : IsRegularWith x Fx)
    (k : ℕ) {w : ℂ} (hw : w ∈ Hbar) :
    avgReg (reflRaw x) k w = avgReg x k (-conj w) := by
  have hpt : ∀ n, ∃ a b : ℤ, -conj (dyadicRoundC n w) = CircleCont.lpt n a b := fun n => by
    refine ⟨-⌊(2 : ℝ) ^ n * w.re⌋, ⌊(2 : ℝ) ^ n * w.im⌋, ?_⟩
    rw [CircleCont.dyadicRoundC_eq_lpt, lpt_neg_conj]
  have hseq : ∀ n, x (foldedCircle (-conj (dyadicRoundC n w)) (radius k)) =
      Fx (-conj (dyadicRoundC n w), radius k) := fun n => by
    obtain ⟨a, b, hab⟩ := hpt n
    rw [hab, F1.raw_fc_lpt_eq_evalReg hx n a b k]
    exact hx.evalReg_fc_of_mem (hab ▸ RegClosure.mapsTo_neg_conj
      (CircleCont.dyadicRoundC_mem_Hbar hw n)) (radius_pos k)
  have hlim : Tendsto (fun n => -conj (dyadicRoundC n w)) atTop (𝓝 (-conj w)) :=
    (Complex.continuous_conj.neg.tendsto w).comp (RegClosure.tendsto_dyadicRoundC w)
  have htend : Tendsto (fun n => Fx (-conj (dyadicRoundC n w), radius k)) atTop
      (𝓝 (Fx (-conj w, radius k))) :=
    Filter.Tendsto.comp (f := fun n => -conj (dyadicRoundC n w))
      (g := fun u : ℂ => Fx (u, radius k))
      (show Tendsto (fun u : ℂ => Fx (u, radius k)) (𝓝[Hbar] (-conj w))
        (𝓝 (Fx (-conj w, radius k))) from
        RegClosure.continuousOn_slice hx.1 (radius_pos k) (-conj w) (RegClosure.mapsTo_neg_conj hw))
      (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n =>
        RegClosure.mapsTo_neg_conj (CircleCont.dyadicRoundC_mem_Hbar hw n)⟩)
  rw [show avgReg (reflRaw x) k w =
      limUnder atTop (fun n => x (foldedCircle (-conj (dyadicRoundC n w)) (radius k))) from ?_,
    show (fun n => x (foldedCircle (-conj (dyadicRoundC n w)) (radius k))) =
      fun n => Fx (-conj (dyadicRoundC n w), radius k) from funext hseq,
    htend.limUnder_eq, hx.avgReg_eq k (RegClosure.mapsTo_neg_conj hw)]
  unfold avgReg reflRaw
  apply congrArg (limUnder atTop)
  funext n
  show x ((foldedCircle (dyadicRoundC n w) (radius k)).map fun z => -conj z) =
    x (foldedCircle (-conj (dyadicRoundC n w)) (radius k))
  rw [F1.fc_map_negConj]

/-- **Raw reflection identity of the unzipped field.** For a continuous driver with `W 0 = 0`,
`t ≥ 0` and a regular field `x`, the unzipped field of the raw-reflected configuration
`(reflRaw x, −W)` at the folded circle `(d, s)` equals the unzipped field of `(x, W)` at the
reflected folded circle `(−d̄, s)`. -/
theorem unzippedField_reflRaw_neg {γ : ℝ} {x : FieldSample} {W : ℝ → ℝ} {t : ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) {Fx : ℂ × ℝ → ℝ} (hx : IsRegularWith x Fx)
    (d : ℂ) {s : ℝ} (hs : 0 < s) :
    unzippedField γ (reflRaw x, -W) t (foldedCircle d s) =
      unzippedField γ (x, W) t (foldedCircle (-conj d) s) := by
  set ψ := fwdMapInv W t with hψ
  have hψ' : fwdMapInv (-W) t = fun u => -conj (ψ (-conj u)) := F1.fwdMapInv_neg_eq W hW ht
  have hWn : Continuous (-W) := hW.neg
  have hWn0 : (-W) 0 = 0 := by simp [hW0]
  simp only [unzippedField, coordChange]
  congr 1
  · -- the regularized evaluation at the pushed circle
    unfold evalReg
    congr 1
    funext j
    rw [integral_map (RegCont.aemeasurable_fwdMapInv hWn hWn0 ht d hs)
      (RegClosure.measurable_avgReg_slice (reflRaw x) j).aestronglyMeasurable]
    rw [show (∫ u, avgReg (reflRaw x) j (fwdMapInv (-W) t u) ∂foldedCircle d s) =
        ∫ u, avgReg x j (ψ (-conj u)) ∂foldedCircle d s from
      integral_congr_ae (ae_of_all _ fun u => by
        show avgReg (reflRaw x) j (fwdMapInv (-W) t u) = avgReg x j (ψ (-conj u))
        rw [avgReg_reflRaw_of_regular hx j (F1.fwdMapInv_mem_Hbar (-W) t u), hψ']
        simp)]
    rw [integral_map (RegCont.aemeasurable_fwdMapInv hW hW0 ht (-conj d) hs)
        (RegClosure.measurable_avgReg_slice x j).aestronglyMeasurable,
      ← F1.integral_fc_negConj (fun v => avgReg x j (ψ v))]
  · -- the derivative term
    congr 1
    rw [hψ', ← F1.integral_fc_negConj (fun v => Real.log ‖deriv ψ v‖)]
    simp only [F1.norm_deriv_negConj_conj]

/-! ## 2. From the raw identity to the regularized averages -/

/-- **Convergence of the raw values at lattice points.** A regular field, read at folded circles
based at lattice points of level `n` converging to `w ∈ Hbar`, converges to the witness at `w`. -/
theorem tendsto_lpt_lattice {y : FieldSample} {F : ℂ × ℝ → ℝ} (hy : IsRegularWith y F) (k : ℕ)
    {e : ℕ → ℂ} (he : ∀ n, e n ∈ Hbar) (hpt : ∀ n, ∃ a b : ℤ, e n = CircleCont.lpt n a b)
    {w : ℂ} (hw : w ∈ Hbar) (hlim : Tendsto e atTop (𝓝 w)) :
    Tendsto (fun n => y (foldedCircle (e n) (radius k))) atTop (𝓝 (F (w, radius k))) := by
  have hseq : ∀ n, y (foldedCircle (e n) (radius k)) = F (e n, radius k) := fun n => by
    obtain ⟨a, b, hab⟩ := hpt n
    rw [hab, F1.raw_fc_lpt_eq_evalReg hy n a b k]
    exact hy.evalReg_fc_of_mem (hab ▸ he n) (radius_pos k)
  rw [show (fun n => y (foldedCircle (e n) (radius k))) = fun n => F (e n, radius k) from
    funext hseq]
  exact Filter.Tendsto.comp (f := e) (g := fun u : ℂ => F (u, radius k))
    (show Tendsto (fun u : ℂ => F (u, radius k)) (𝓝[Hbar] w) (𝓝 (F (w, radius k))) from
      RegClosure.continuousOn_slice hy.1 (radius_pos k) w hw)
    (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall he⟩)

/-- The raw identity, read as the identity of the two `avgReg`-defining dyadic sequences. -/
theorem avgReg_seq_unzippedField_reflRaw {γ : ℝ} {x : FieldSample} {W : ℝ → ℝ} {t : ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) {Fx : ℂ × ℝ → ℝ} (hx : IsRegularWith x Fx)
    (k : ℕ) (u : ℝ) :
    avgReg (unzippedField γ (reflRaw x, -W) t) k (u : ℂ) =
      limUnder atTop (fun n => unzippedField γ (x, W) t
        (foldedCircle (-conj (dyadicRoundC n (u : ℂ))) (radius k))) := by
  unfold avgReg
  apply congrArg (limUnder atTop)
  funext n
  exact unzippedField_reflRaw_neg hW hW0 ht hx _ (radius_pos k)

/-- **The pathwise reflection identity at real points**: for a regular base field and a regular
unzipped field, the regularized averages of the unzipped field of the raw-reflected
configuration at `u` are those of the original at `−u`. -/
theorem avgReg_unzippedField_reflRaw_neg_real {γ : ℝ} {x : FieldSample} {W : ℝ → ℝ} {t : ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) {Fx : ℂ × ℝ → ℝ} (hx : IsRegularWith x Fx)
    {FY : ℂ × ℝ → ℝ} (hY : IsRegularWith (unzippedField γ (x, W) t) FY)
    (k : ℕ) (u : ℝ) :
    avgReg (unzippedField γ (reflRaw x, -W) t) k (u : ℂ) =
      avgReg (unzippedField γ (x, W) t) k ((-u : ℝ) : ℂ) := by
  have hneg : -conj ((u : ℝ) : ℂ) = ((-u : ℝ) : ℂ) := by simp
  have he_mem : ∀ n, -conj (dyadicRoundC n (u : ℂ)) ∈ Hbar := fun n =>
    RegClosure.mapsTo_neg_conj (CircleCont.dyadicRoundC_mem_Hbar (by simp [Hbar]) n)
  have he_lpt : ∀ n, ∃ a b : ℤ, -conj (dyadicRoundC n (u : ℂ)) = CircleCont.lpt n a b := fun n => by
    refine ⟨-⌊(2 : ℝ) ^ n * u⌋, 0, ?_⟩
    rw [CircleCont.dyadicRoundC_eq_lpt, lpt_neg_conj]
    apply Complex.ext <;> simp [CircleCont.lpt, neg_div]
  have hlim : Tendsto (fun n => -conj (dyadicRoundC n (u : ℂ))) atTop (𝓝 (-conj (u : ℂ))) :=
    (Complex.continuous_conj.neg.tendsto (u : ℂ)).comp
      (RegClosure.tendsto_dyadicRoundC (u : ℂ))
  have htend : Tendsto (fun n => unzippedField γ (x, W) t
      (foldedCircle (-conj (dyadicRoundC n (u : ℂ))) (radius k))) atTop
      (𝓝 (FY (((-u : ℝ) : ℂ), radius k))) := by
    have h := tendsto_lpt_lattice hY k he_mem he_lpt
      (RegClosure.mapsTo_neg_conj (show ((u : ℝ) : ℂ) ∈ Hbar by simp [Hbar])) hlim
    simpa only [hneg] using h
  rw [avgReg_seq_unzippedField_reflRaw hW hW0 ht hx k u, htend.limUnder_eq,
    hY.avgReg_eq k (by simp [Hbar])]

/-! ## 3. Reflecting the deterministic part `𝔥₀` -/

/-- `𝔥₀(κ)` is radial, hence invariant under `z ↦ −z̄`. -/
theorem h0rev_neg_conj (κ : ℝ) (z : ℂ) : h0rev κ (-conj z) = h0rev κ z := by
  simp [h0rev]

/-- `ofFun` of the radial potential `𝔥₀(κ)` is unchanged by the raw reflection. -/
theorem ofFun_h0rev_reflRaw (κ : ℝ) (μ : Measure ℂ) :
    ofFun (h0rev κ) (μ.map fun z => -conj z) = ofFun (h0rev κ) μ := by
  unfold ofFun
  rw [integral_map measurable_negConj.aemeasurable
    (UnzipInvariance.measurable_h0rev κ).aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ fun z => h0rev_neg_conj κ z)

/-- **Reflection of the configuration field**: `reflRaw` commutes with adding `𝔥₀(κ)`, because
`𝔥₀(κ)` is radial. -/
theorem reflRaw_add_ofFun_h0rev (κ : ℝ) (x : FieldSample) :
    reflRaw (ofFun (h0rev κ) + x) = ofFun (h0rev κ) + reflRaw x := by
  funext μ
  show (ofFun (h0rev κ) + x) (μ.map fun z => -conj z) =
    ofFun (h0rev κ) μ + x (μ.map fun z => -conj z)
  rw [Pi.add_apply, ofFun_h0rev_reflRaw]

end RegUnif
end QuantumZipper
