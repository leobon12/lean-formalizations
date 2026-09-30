import QuantumZipper.Proofs.Zipper.F1Reflect
import QuantumZipper.Proofs.Zipper.RegContDet
import QuantumZipper.Proofs.LQG.GoodMeasurableReg

/-!
# F1d input (a): the unzipped field of the reflected configuration

Theorem 1.3, node F1d (Sheffield, arXiv:1012.4797, §5.4 p. 72: "by symmetry"). For a
configuration `c = (h, W)` and its reflection `reflectConfig c = (h(−·̄), −W)`, the unzipped field
of the reflection is, after regularization, the reflection of the unzipped field:
`RegEq (unzippedField γ (reflectConfig c) t) (reflectH (unzippedField γ c t))`
(`regEq_unzippedField_reflect`), for a continuous driver with `W 0 = 0`, `t ≥ 0`, `h` regular and
the unzipped field regular.

Route (own elementary argument): `fwdMapInv (−W) t = r ∘ fwdMapInv W t ∘ r` with `r z = −z̄`
(`F1.fwdMapInv_reflect`); the reflection maps folded circles to folded circles
(`fc_map_negConj`); for a regular `h`, `avgReg (reflectH h) j w = avgReg h j (−w̄)` on `Hbar`;
`|(r ∘ ψ ∘ r)'(u)| = |ψ'(r u)|` (`deriv_conj_conj`). This gives the raw identity
`y (fc d s) = x (fc (−d̄) s)` (`unzippedField_reflect_fc`), and the regularity of `x` identifies
its raw values at dyadic folded circles with the regularized ones (`raw_fc_lpt_eq_evalReg`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate

namespace QuantumZipper
namespace F1

/-- The reflection `z ↦ −z̄` as a measurable equivalence. -/
def negConjEquiv : ℂ ≃ᵐ ℂ where
  toFun u := -conj u
  invFun u := -conj u
  left_inv u := by simp
  right_inv u := by simp
  measurable_toFun := (Complex.continuous_conj.neg).measurable
  measurable_invFun := (Complex.continuous_conj.neg).measurable

theorem negConj_emb : MeasurableEmbedding fun u : ℂ => -conj u :=
  negConjEquiv.measurableEmbedding

/-- The reflection maps folded circles to folded circles. -/
theorem fc_map_negConj (c : ℂ) (s : ℝ) :
    (foldedCircle c s).map (fun u => -conj u) = foldedCircle (-conj c) s := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [negConj_emb.integral_map]
  exact RegClosure.integral_fc_comp_neg_conj (g := fun u => f u) f.continuous.continuousOn c s

theorem integral_fc_negConj (g : ℂ → ℝ) (d : ℂ) (s : ℝ) :
    ∫ u, g (-conj u) ∂foldedCircle d s = ∫ v, g v ∂foldedCircle (-conj d) s := by
  rw [← fc_map_negConj, negConj_emb.integral_map]

/-- Values of `fwdMapInv` always lie in `Hbar` (the junk value is `0`). -/
theorem fwdMapInv_mem_Hbar (W : ℝ → ℝ) (t : ℝ) (w : ℂ) : fwdMapInv W t w ∈ Hbar := by
  unfold fwdMapInv
  split_ifs with h
  · exact le_of_lt (show 0 < (h.choose).im from h.choose_spec.1.1.1)
  · show (0 : ℝ) ≤ (0 : ℂ).im; simp

theorem fwdMapInv_neg_eq (W : ℝ → ℝ) (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    fwdMapInv (-W) t = fun u => -conj (fwdMapInv W t (-conj u)) := by
  funext u
  have := fwdMapInv_reflect W hW ht (-conj u)
  simpa using this

/-- `|(r ∘ ψ ∘ r)'(u)| = |ψ'(r u)|` for `r z = −z̄`. -/
theorem norm_deriv_negConj_conj (ψ : ℂ → ℂ) (u : ℂ) :
    ‖deriv (fun v => -conj (ψ (-conj v))) u‖ = ‖deriv ψ (-conj u)‖ := by
  set g : ℂ → ℂ := fun v => -ψ (-v) with hg
  have e : (fun v => -conj (ψ (-conj v))) = conj ∘ g ∘ conj := by
    funext v; simp [hg]
  have hd : ∀ v, deriv g v = deriv ψ (-v) := by
    intro v
    have : g = -(fun v => ψ (-v)) := by funext v; simp [hg]
    rw [this, deriv.neg, deriv_comp_neg, neg_neg]
  rw [e, deriv_conj_conj]
  simp only [Function.comp, hd, Complex.norm_conj]

/-- For a regular `h`, the regularized averages of `reflectH h` are the reflected ones. -/
theorem avgReg_reflectH_eq {h : FieldSample} {F0 : ℂ × ℝ → ℝ} (hh : IsRegularWith h F0)
    (j : ℕ) {w : ℂ} (hw : w ∈ Hbar) :
    avgReg (RegClosure.reflectH h) j w = avgReg h j (-conj w) := by
  rw [hh.reflectH'.avgReg_eq j hw, hh.avgReg_eq j (RegClosure.mapsTo_neg_conj hw)]

/-- **Raw identity.** The unzipped field of the reflected configuration at a folded circle
equals the unzipped field at the reflected folded circle. -/
theorem unzippedField_reflect_fc {γ : ℝ} {c : FieldSample × (ℝ → ℝ)} {t : ℝ}
    (hW : Continuous c.2) (hW0 : c.2 0 = 0) (ht : 0 ≤ t) {F0 : ℂ × ℝ → ℝ}
    (hh : IsRegularWith c.1 F0) (d : ℂ) {s : ℝ} (hs : 0 < s) :
    unzippedField γ (reflectConfig c) t (foldedCircle d s) =
      unzippedField γ c t (foldedCircle (-conj d) s) := by
  set ψ := fwdMapInv c.2 t with hψ
  have hψ' : fwdMapInv (-c.2) t = fun u => -conj (ψ (-conj u)) := fwdMapInv_neg_eq c.2 hW ht
  have hWn : Continuous (-c.2) := hW.neg
  have hWn0 : (-c.2) 0 = 0 := by simp [hW0]
  simp only [unzippedField, reflectConfig, coordChange]
  congr 1
  · -- the regularized evaluation
    unfold evalReg
    congr 1
    funext j
    rw [integral_map (RegCont.aemeasurable_fwdMapInv hWn hWn0 ht d hs)
        (RegClosure.measurable_avgReg_slice _ j).aestronglyMeasurable,
      integral_map (RegCont.aemeasurable_fwdMapInv hW hW0 ht (-conj d) hs)
        (RegClosure.measurable_avgReg_slice _ j).aestronglyMeasurable,
      ← integral_fc_negConj (fun v => avgReg c.1 j (ψ v))]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    show avgReg (RegClosure.reflectH c.1) j (fwdMapInv (-c.2) t u) = avgReg c.1 j (ψ (-conj u))
    rw [avgReg_reflectH_eq hh j (fwdMapInv_mem_Hbar _ _ _), hψ']
    simp
  · -- the derivative term
    congr 1
    rw [hψ', ← integral_fc_negConj (fun v => Real.log ‖deriv ψ v‖)]
    simp only [norm_deriv_negConj_conj]

/-- A dyadic lattice point, folded, is a dyadic lattice point. -/
theorem foldH_lpt (n : ℕ) (a b : ℤ) : ∃ b' : ℤ, foldH (CircleCont.lpt n a b) = CircleCont.lpt n a b' := by
  unfold foldH
  split_ifs
  · exact ⟨b, rfl⟩
  · refine ⟨-b, ?_⟩
    apply Complex.ext <;> simp [CircleCont.lpt, neg_div]

/-- For a regular sample, raw values at dyadic folded circles are the regularized values. -/
theorem raw_fc_lpt_eq_evalReg {x : FieldSample} {F : ℂ × ℝ → ℝ} (hx : IsRegularWith x F)
    (n : ℕ) (a b : ℤ) (k : ℕ) :
    x (foldedCircle (CircleCont.lpt n a b) (radius k)) =
      evalReg x (foldedCircle (CircleCont.lpt n a b) (radius k)) := by
  set e := CircleCont.lpt n a b
  have hfe : foldedCircle (foldH e) (radius k) = foldedCircle e (radius k) :=
    ext_of_forall_integral_eq_of_IsFiniteMeasure fun f =>
      RegClosure.integral_fc_foldH f.continuous.continuousOn e (radius k)
  rw [hx.evalReg_fc e (radius_pos k), ← hfe]
  obtain ⟨b', hb'⟩ := foldH_lpt n a b
  have hmem : foldH e ∈ Hbar := CircleFubini.foldH_mem_Hbar' e
  have htend := hx.2.1 k (foldH e) hmem
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) htend
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [hb', GoodMeas.dyadicRoundC_lpt hm]

/-- **F1d input (a).** For a continuous driver with `W 0 = 0`, `t ≥ 0`, a regular field `h` and a
regular unzipped field, the unzipped field of the reflected configuration is, after
regularization, the reflection of the unzipped field. -/
theorem regEq_unzippedField_reflect {γ : ℝ} {c : FieldSample × (ℝ → ℝ)} {t : ℝ}
    (hW : Continuous c.2) (hW0 : c.2 0 = 0) (ht : 0 ≤ t) {F0 F : ℂ × ℝ → ℝ}
    (hh : IsRegularWith c.1 F0) (hx : IsRegularWith (unzippedField γ c t) F) :
    RegEq (unzippedField γ (reflectConfig c) t)
      (RegClosure.reflectH (unzippedField γ c t)) := by
  intro k z
  unfold avgReg
  congr 1
  funext n
  rw [unzippedField_reflect_fc hW hW0 ht hh _ (radius_pos k)]
  show _ = evalReg _ ((foldedCircle _ _).map fun z => -conj z)
  rw [fc_map_negConj, CircleCont.dyadicRoundC_eq_lpt]
  have e : -conj (CircleCont.lpt n ⌊(2 : ℝ) ^ n * z.re⌋ ⌊(2 : ℝ) ^ n * z.im⌋) =
      CircleCont.lpt n (-⌊(2 : ℝ) ^ n * z.re⌋) ⌊(2 : ℝ) ^ n * z.im⌋ := by
    apply Complex.ext <;> simp [CircleCont.lpt, neg_div]
  rw [e]
  exact raw_fc_lpt_eq_evalReg hx n _ _ k

end F1
end QuantumZipper
