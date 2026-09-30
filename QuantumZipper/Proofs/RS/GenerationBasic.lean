import QuantumZipper.Proofs.RS.TraceHull
import QuantumZipper.Proofs.RS.TraceRadial
import QuantumZipper.Proofs.Complex.CarLengthArea
import QuantumZipper.Proofs.Zipper.RegContDet

/-!
# EXT-RS node GEN, preliminaries: inverse-map facts and the semicircle length bound

Blueprint `blueprint/EXT_RS_BLUEPRINT.md` §3, node **GEN** (task RS-GEN). Notation:
`f_t = fwdMap W t`, `f̂_t = fwdMapInv W t`, `K_t = fwdHull W t`, `H = {z | 0 < z.im}`.

* `fwdMapInv_mem_compl_fwdHull`, `fwdMapInv_fwdMap`, `image_fwdMapInv_H`: `f̂_t` is a bijection
  `H → H \ K_t` inverse to `f_t`.
* `ofReal_norm_sub_le_semicircle`: the distance between two points of the image of the
  semicircle `{r e^{iθ} | 0 < θ < π}` under a holomorphic `g` is at most the length
  `∫_0^π ‖g'(r e^{iθ})‖ r dθ` (lower Lebesgue integral), the form in which Wolff's lemma
  (EXT-CA C2, `Car.exists_short_semicircle_finite`; Pommerenke, *Boundary Behaviour of Conformal
  Maps*, Prop. 2.2, p. 20) bounds it. Own elementary proof (fundamental theorem of calculus
  along the arc).
-/

noncomputable section

open Set Filter Topology Metric Complex MeasureTheory
open scoped ENNReal Real

namespace QuantumZipper
namespace RS

variable {W : ℝ → ℝ}

/-- `f̂_t` maps `H` into `H \ K_t`. -/
theorem fwdMapInv_mem_compl_fwdHull (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {w : ℂ} (hw : w ∈ H) : fwdMapInv W t w ∈ H \ fwdHull W t := by
  refine ⟨fwdMapInv_mem_H hW hW0 ht hw, ?_⟩
  rw [UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht hw]
  set V : ℝ → ℝ := fun r => W (t - r) - W t with hVdef
  have hV : Continuous V := by fun_prop
  have hV0 : V 0 = 0 := by simp [hVdef]
  have hVV : (fun r => V (t - r) - V t) = W := by
    funext r; simp only [hVdef, sub_sub_cancel, sub_self, hW0]; ring
  have h1 := (UnzipInvariance.fwdMap_revMap_timeRev_of_nonneg V hV hV0 ht hw).1
  rw [hVV] at h1
  exact h1

/-- `f̂_t ∘ f_t = id` on `H \ K_t`. -/
theorem fwdMapInv_fwdMap (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ H \ fwdHull W t) : fwdMapInv W t (fwdMap W t z) = z := by
  have hfz : fwdMap W t z ∈ H := FwdHolo.mapsTo_fwdMap hW ht hz
  exact FwdHolo.injOn_fwdMap hW ht (fwdMapInv_mem_compl_fwdHull hW hW0 ht hfz) hz
    (fwdMap_fwdMapInv hW hW0 ht hfz)

/-- `f̂_t (H) = H \ K_t`. -/
theorem image_fwdMapInv_H (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    fwdMapInv W t '' H = H \ fwdHull W t := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact fwdMapInv_mem_compl_fwdHull hW hW0 ht hw
  · intro hz
    exact ⟨_, FwdHolo.mapsTo_fwdMap hW ht hz, fwdMapInv_fwdMap hW hW0 ht hz⟩

/-- `f̂_t` is injective on `H`. -/
theorem injOn_fwdMapInv_H (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    InjOn (fwdMapInv W t) H := fun a ha b hb hab => by
  rw [← fwdMap_fwdMapInv hW hW0 ht ha, hab, fwdMap_fwdMapInv hW hW0 ht hb]

/-- The point `r e^{iθ}` lies in `H` for `r > 0`, `0 < θ < π`. -/
theorem ofReal_mul_exp_mem_H {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioo 0 π) :
    (r : ℂ) * exp (θ * I) ∈ H := by
  show 0 < ((r : ℂ) * exp (θ * I)).im
  simp only [mul_im, ofReal_re, ofReal_im, exp_ofReal_mul_I_im, zero_mul, add_zero]
  exact mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)

/-- **Arc length bound (own elementary proof).** For `g` holomorphic on `H`, `r > 0` and
`0 < a ≤ b < π`, `‖g(r e^{ib}) − g(r e^{ia})‖` is at most the length of the image of the whole
semicircle, `∫⁻_{(0,π)} ‖g'(r e^{iθ})‖ r dθ`. -/
theorem ofReal_norm_sub_le_semicircle {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g H) {r : ℝ}
    (hr : 0 < r) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < π) :
    ENNReal.ofReal ‖g (r * exp (b * I)) - g (r * exp (a * I))‖ ≤
      ∫⁻ θ in Ioo 0 π, ‖deriv g (r * exp (θ * I))‖ₑ * ENNReal.ofReal r := by
  set γ : ℝ → ℂ := fun θ => (r : ℂ) * exp (θ * I) with hγ
  set F' : ℝ → ℂ := fun θ => deriv g (γ θ) * (γ θ * I) with hF'
  have hsub : Icc a b ⊆ Ioo 0 π := fun x hx => ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
  have hγH : ∀ θ ∈ Ioo 0 π, γ θ ∈ H := fun θ hθ => ofReal_mul_exp_mem_H hr hθ
  have hγc : Continuous γ := by fun_prop
  have hγd : ∀ θ : ℝ, HasDerivAt γ (γ θ * I) θ := by
    intro θ
    have h1 : HasDerivAt (fun x : ℝ => ((x : ℂ) * I)) (1 * I) θ :=
      (hasDerivAt_id θ).ofReal_comp.mul_const I
    have h2 := (h1.cexp).const_mul (r : ℂ)
    have he : γ θ * I = (r : ℂ) * (exp (θ * I) * (1 * I)) := by
      show (r : ℂ) * exp (θ * I) * I = _
      ring
    rw [he]
    exact h2
  have hderiv : ∀ θ ∈ uIcc a b, HasDerivAt (fun θ => g (γ θ)) (F' θ) θ := by
    intro θ hθ
    rw [uIcc_of_le hab] at hθ
    have hgd : DifferentiableAt ℂ g (γ θ) :=
      (hg _ (hγH θ (hsub hθ))).differentiableAt (isOpen_H.mem_nhds (hγH θ (hsub hθ)))
    exact hgd.hasDerivAt.comp θ (hγd θ)
  have hcont : ContinuousOn F' (Icc a b) := by
    have hdc : ContinuousOn (deriv g) H := (hg.deriv isOpen_H).continuousOn
    exact (hdc.comp hγc.continuousOn fun θ hθ => hγH θ (hsub hθ)).mul
      (hγc.continuousOn.mul continuousOn_const)
  have hint : IntervalIntegrable F' volume a b :=
    (hcont.mono (by rw [uIcc_of_le hab])).intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hnormF : ∀ θ, ‖F' θ‖ = ‖deriv g (γ θ)‖ * r := by
    intro θ
    simp only [hF', hγ, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
      norm_exp_ofReal_mul_I, abs_of_pos hr]
  have hIoc : IntegrableOn (fun θ => ‖F' θ‖) (Ioc a b) :=
    (hcont.norm.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  calc ENNReal.ofReal ‖g (γ b) - g (γ a)‖
      = ENNReal.ofReal ‖∫ θ in a..b, F' θ‖ := by rw [hFTC]
    _ ≤ ENNReal.ofReal (∫ θ in a..b, ‖F' θ‖) :=
        ENNReal.ofReal_le_ofReal (intervalIntegral.norm_integral_le_integral_norm hab)
    _ = ∫⁻ θ in Ioc a b, ENNReal.ofReal ‖F' θ‖ := by
        rw [intervalIntegral.integral_of_le hab]
        exact ofReal_integral_eq_lintegral_ofReal hIoc
          (Eventually.of_forall fun θ => norm_nonneg _)
    _ ≤ ∫⁻ θ in Ioo 0 π, ENNReal.ofReal ‖F' θ‖ :=
        lintegral_mono_set (Ioc_subset_Icc_self.trans hsub)
    _ = ∫⁻ θ in Ioo 0 π, ‖deriv g (γ θ)‖ₑ * ENNReal.ofReal r := by
        congr 1
        funext θ
        rw [hnormF, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]

end RS
end QuantumZipper
