import QuantumZipper.Proofs.Thm18.R18RTMaskOff

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT2 (D82), deterministic assembly: masked data of the unzipping from off-curve agreement

Sheffield, arXiv:1012.4797, §4.1 p. 48 and Theorem 1.8 (p. 26); Berestycki–Powell,
arXiv:2404.16642, Thm 8.16 and Rem 8.10 (p. 283): the unzipped field is determined by `h` restricted
to `ℍ ∖ η`. Deterministic statement (`offData_zipLenDownA_eq_of_pullOff`): two configurations with
the same driver `W` and carried area, whose fields have the same regularized pairings with every
folded dyadic circle pulled back by `f_s⁻¹ = fwdMapInv W s` **that stays off the unzipped
remaining curve** (`unzCurve W s a`, the curve of the unzipped and rescaled driver, scaled back by
`a`; it is `f_s(η[s,∞))` by `R18T6Curve.mem_curveOf_of_unzip`), have the same masked data after
`Z^LEN_{−ℓ}`, provided the unzipped remaining curves avoid the negative half-line (so that the
lengths of the left open arc `(O⁻_s, 0)` are read off the curve) and the area scale is positive.

Own elementary bookkeeping on top of `R18RTMaskOff.lean`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace R18

/-- The driver of the configuration unzipped by capacity time `s` and rescaled by `a` (the driver
of `canonAConfig γ (zipCapDownA γ s c)` with scale `a`). -/
def outDrv (W : ℝ → ℝ) (s a : ℝ) : ℝ → ℝ := fun r => (W (s + max (a ^ 2 * max r 0) 0) - W s) / a

/-- The remaining curve after unzipping by `s`, in the unzipped (not yet rescaled) picture: the
curve of `outDrv W s a` scaled back by `a` (independent of `a > 0` for a good driver). -/
def unzCurve (W : ℝ → ℝ) (s a : ℝ) : Set ℂ := {w | ((a⁻¹ : ℝ) : ℂ) * w ∈ curveOf (outDrv W s a)}

theorem isClosed_unzCurve (W : ℝ → ℝ) (s a : ℝ) : IsClosed (unzCurve W s a) :=
  isClosed_closure.preimage (continuous_const.mul continuous_id)

/-- **Off-curve pulled-back agreement**: the regularized pairings of `x` and `y` with every folded
dyadic circle that stays off the unzipped remaining curve at time `s ≥ 0`, pulled back by
`fwdMapInv W s`, agree. -/
def PullOffAgree (W : ℝ → ℝ) (x y : FieldSample) : Prop :=
  ∀ s : ℝ, 0 ≤ s → ∀ a : ℝ, 0 < a → ∀ (d : ℂ) (k : ℕ), CircleOff (unzCurve W s a) d (radius k) →
    evalReg x ((foldedCircle d (radius k)).map (fwdMapInv W s)) =
      evalReg y ((foldedCircle d (radius k)).map (fwdMapInv W s))

theorem regEqOff_unzippedField_of_pullOff {γ : ℝ} {W : ℝ → ℝ} {x y : FieldSample}
    (h : PullOffAgree W x y) {s a : ℝ} (hs : 0 ≤ s) (ha : 0 < a) :
    RegEqOff (unzCurve W s a) (unzippedField γ (x, W) s) (unzippedField γ (y, W) s) :=
  regEqOff_coordChange_of_pull _ (h s hs a ha)

theorem zipLenDownA_toPair_eq (γ ℓ : ℝ) (c : AreaConfig) :
    (zipLenDownA γ ℓ c).toPair =
      (rescale (unzippedField γ c.toPair (lenTimeOpen γ ℓ c.toPair)) (Qc γ)
          (areaScale (zipCapDownA γ (lenTimeOpen γ ℓ c.toPair) c).area),
        outDrv c.drv (lenTimeOpen γ ℓ c.toPair)
          (areaScale (zipCapDownA γ (lenTimeOpen γ ℓ c.toPair) c).area)) := rfl

/-- **Deterministic reduction of RT2 (full masked data).** -/
theorem offData_zipLenDownA_eq_of_pullOff {γ ℓ : ℝ} {c c' : AreaConfig} (hW : c.drv = c'.drv)
    (hμ : c.area = c'.area) (hpull : PullOffAgree c.drv c.fld c'.fld)
    (hG1 : ∀ s : ℝ, 0 ≤ s → ∀ t : ℝ, t < 0 → (t : ℂ) ∉ curveOf (outDrv c.drv s 1))
    (ha : 0 < areaScale (zipCapDownA γ (lenTimeOpen γ ℓ c.toPair) c).area) :
    offData (zipLenDownA γ ℓ c).toPair = offData (zipLenDownA γ ℓ c').toPair := by
  obtain ⟨x, W, μ⟩ := c
  obtain ⟨x', W', μ'⟩ := c'
  subst hW hμ
  have hlen : ∀ s : ℝ, 0 ≤ s →
      (unzipLengthsOpen γ (x, W) s).1 = (unzipLengthsOpen γ (x', W) s).1 := by
    intro s hs
    simp only [unzipLengthsOpen, openArcLen]
    rw [qBoundaryMeasureOn_congr_off (isClosed_unzCurve W s 1)
      (regEqOff_unzippedField_of_pullOff hpull hs one_pos) γ (fun t ht => ?_)]
    have h1 := hG1 s hs t ht.2
    simpa [unzCurve] using h1
  have ht : lenTimeOpen γ ℓ (x', W) = lenTimeOpen γ ℓ (x, W) := by
    have hset : {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal ℓ ≤ (unzipLengthsOpen γ (x', W) s).1} =
        {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal ℓ ≤ (unzipLengthsOpen γ (x, W) s).1} := by
      ext s
      exact and_congr_right fun hs => by rw [hlen s hs]
    unfold lenTimeOpen
    rw [hset]
  have hT0 : 0 ≤ lenTimeOpen γ ℓ (x, W) := lenTimeOpen_nonneg _ _ _
  have harea : (zipCapDownA γ (lenTimeOpen γ ℓ (x, W)) ⟨x', W, μ⟩).area =
      (zipCapDownA γ (lenTimeOpen γ ℓ (x, W)) ⟨x, W, μ⟩).area := rfl
  have hreg := regEqOff_unzippedField_of_pullOff (γ := γ) hpull hT0 ha
  rw [zipLenDownA_toPair_eq, zipLenDownA_toPair_eq]
  simp only [AreaConfig.toPair]
  rw [ht, harea]
  unfold offData lawDataOff
  refine Prod.ext (Prod.ext (funext fun i => ?_) (funext fun ρ => ?_)) rfl
  · simp only
    split_ifs with hc
    · exact rescale_foldedCircle_congr_off ha hreg _
        (by unfold CoordsFull.fullIndex; positivity) hc
    · rfl
  · simp only
    split_ifs with hc
    · exact pairRaw_rescale_congr_off (isClosed_closure) ha hreg _ ρ hc
    · rfl

end R18
end QuantumZipper
