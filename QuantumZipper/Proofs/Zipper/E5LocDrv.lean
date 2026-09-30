import QuantumZipper.Proofs.Zipper.E5Model2
import QuantumZipper.Proofs.Zipper.ESMInst

/-!
# E5-LOC, driver part: the driver of the canonicalized collision configuration

Blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4 E5, step (1); Sheffield, arXiv:1012.4797, §5.4
(pp. 66–72, proof of Lemma 5.6). Companion of `E5Model2.locG_canonConfig_targetColl_eq_zLoc`,
which identifies the *field* part (level `C`) of the canonicalized collision configuration with
the D3⁺ model field `zoomModel …`: here we identify its *driver* part with the driver read by a
zoom model, `drvWin κ R (rescale R a D)` (`E5Model1.ZoomModel.data`).

`canonConfig γ (y, d) = (canonical γ y, fun u ↦ d (scaleParam γ y ^ 2 * max u 0) / scaleParam γ y)`
rescales the driver by the local scale `a = scaleParam γ y` (Brownian scaling, `s ↦ a²s` on
times and `1/a` on values; below `0` the `max · 0` normalizes to `d 0 / a`). On the model side,
`ZoomModel.data C` reads the driver

  `drvWin κ R (rescale R a D)`,  `rescale R a D t = a⁻¹ D (a² t)`,  `drvWin κ R f s = √κ f (min s R)`

where `D` is the germ (a `ℝ≥0`-parametrized path, `smPath B (tᴸ ℓ)` in the intended
construction) and `√κ` is put back by `drvWin` (the driving function of the quantum zipper is
`drive κ B = √κ B`). Hence the deterministic identity

  `(canonConfig (√κ) (y, d)).2 (min s R) = √κ · a⁻¹ · D (a² min s R)`

holds as soon as

* the local scale is `a ≥ 0`: `scaleParam (√κ) y = a` (for the collision field this is the
  field-part identity, `E5Model2.locG_canonConfig_targetColl_eq_zLoc`), and
* the configuration's driver `d` agrees with `√κ · D` on the window `[0, a² R]` in which the
  rescaled germ is evaluated: `d u = √κ · D u.toNNReal` for `0 ≤ u ≤ a² R`
  (the argument of `rescale` is `a² · min s R ≤ a² R`).

So the pair `(canonical data, driver)` of the canonicalized collision field is the model data
`(zLoc …, drvWin κ R (rescale R (zScale …).toNNReal D))` of `E5Model1.ZoomModel.data`
(`ZoomModel.data_eq`), which is the `Z C = M.data C` clause of `E5Model1.E5ReprG`. For the
collision configuration of `E5Model2` the driver hypothesis is discharged by
`collided_snd_eq_drvMap`: on `{τ_x ≤ T}` its driver is `ESM.drvMap κ (smPath B (T − τ_x))`.

Own elementary proof (algebra of `canonConfig`, `drvWin`, `rescale` and the `ℝ≥0`/`ℝ`
coercions); the blueprint's route reads the driver through Girsanov/Williams time reversal
instead, and this file is only the deterministic bookkeeping that both routes need.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace E5

open D3Plus E1 B2

/-! ## The two evaluation lemmas (definitional) -/

/-- Evaluation of `pathExt` (definitional). -/
theorem drvWin_pathExt_apply (c : ℝ≥0) (x : Set.Iic c → ℝ) (s : ℝ≥0) :
    LengthMarkov.GermDensity.pathExt c x s =
      x ⟨min s c, Set.mem_Iic.2 (min_le_right _ _)⟩ := rfl

/-- Evaluation of `rescale` (definitional). -/
theorem drvWin_rescale_apply (S a : ℝ≥0) (b : ℝ≥0 → ℝ) (t : Set.Iic S) :
    LengthMarkov.GermDensity.rescale S a b t = (a : ℝ)⁻¹ * b (a ^ 2 * (t : ℝ≥0)) := rfl

/-! ## The driver identity -/

/-- **The deterministic driver identity.** If the configuration `(y, d)` has local scale `a`
(`scaleParam (√κ) y = a`, i.e. its canonicalization `canonConfig (√κ) (y, d)` uses the scale
`a`), and its driver `d` agrees with `√κ · D` on the window `[0, a ^ 2 * R]`, then the driver of
the canonicalized configuration on `[0, R]` is the rescaled germ with `√κ` put back,
`drvWin κ R (rescale R a D)`. -/
theorem canonConfig_snd_eq_drvWin {κ : ℝ} {y : FieldSample} {d : ℝ → ℝ} (a : ℝ≥0)
    (D : ℝ≥0 → ℝ) (hsc : scaleParam (Real.sqrt κ) y = (a : ℝ)) (R : ℕ)
    (hd : ∀ u : ℝ, 0 ≤ u → u ≤ (a : ℝ) ^ 2 * (R : ℝ) → d u = Real.sqrt κ * D u.toNNReal)
    (s : ℝ≥0) :
    (canonConfig (Real.sqrt κ) (y, d)).2 (min (s : ℝ) (R : ℝ)) =
      drvWin κ R (LengthMarkov.GermDensity.rescale (R : ℝ≥0) a D) s := by
  have hR : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
  have hs : (0 : ℝ) ≤ (s : ℝ) := s.2
  have hmin0 : (0 : ℝ) ≤ min (s : ℝ) (R : ℝ) := le_min hs hR
  have hminR : min (s : ℝ) (R : ℝ) ≤ (R : ℝ) := min_le_right _ _
  set A : ℝ := (a : ℝ) ^ 2 * min (s : ℝ) (R : ℝ) with hA
  have hA0 : 0 ≤ A := by rw [hA]; exact mul_nonneg (sq_nonneg _) hmin0
  have hAR : A ≤ (a : ℝ) ^ 2 * (R : ℝ) := by
    rw [hA]
    exact mul_le_mul_of_nonneg_left hminR (sq_nonneg _)
  have hcoe : A = ((a ^ 2 * min s (R : ℝ≥0) : ℝ≥0) : ℝ) := by
    simp only [hA, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_min, NNReal.coe_natCast]
  have harg : A.toNNReal = a ^ 2 * min s (R : ℝ≥0) := by
    refine NNReal.coe_injective ?_
    rw [Real.coe_toNNReal A hA0]
    exact hcoe
  have hL : (canonConfig (Real.sqrt κ) (y, d)).2 (min (s : ℝ) (R : ℝ)) =
      d A / scaleParam (Real.sqrt κ) y := by
    show d (scaleParam (Real.sqrt κ) y ^ 2 * max (min (s : ℝ) (R : ℝ)) 0) /
      scaleParam (Real.sqrt κ) y = d A / scaleParam (Real.sqrt κ) y
    rw [max_eq_left hmin0, hsc, ← hA]
  have hD : drvWin κ R (LengthMarkov.GermDensity.rescale (R : ℝ≥0) a D) s =
      Real.sqrt κ * ((a : ℝ)⁻¹ * D A.toNNReal) := by
    show Real.sqrt κ * LengthMarkov.GermDensity.pathExt (R : ℝ≥0)
      (LengthMarkov.GermDensity.rescale (R : ℝ≥0) a D) s = _
    rw [drvWin_pathExt_apply, drvWin_rescale_apply, ← harg]
  rw [hL, hsc, hd A hA0 hAR, hD]
  ring

/-! ## The collision configuration of E5-LOC -/

/-! ## The germ of the collided configuration

The driver of the collided configuration `𝒞_{τ_x}` is `√κ` times the Brownian path restarted at
the remaining capacity time `T − τ_x` (`ESM.drvMap`, `ESM.zipCapDown_cfg_snd`), which is the germ
`D = smPath B (t)` of the E-SM(b) description of the model. This discharges the window hypothesis
`hd` of `canonConfig_snd_eq_drvWin` with no window restriction. -/

/-- **The model data of a zoom model** is the pair `(zLoc …, drvWin κ R (rescale R (zScale ….toNNReal) D))`
(definitional; the shape matched by the three lemmas above). -/
theorem ZoomModel.data_eq {F : Type} [MeasurableSpace F] {fr : ℕ → FieldSample → F} {κ : ℝ}
    {R : ℕ} {W : Measure (ℝ≥0 → ℝ)} (M : ZoomModel fr κ R W) (C : ℝ) (ω : M.Ω₁) :
    M.data C ω =
      (zLoc fr (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) M.r M.ρ₀ R C (M.X' ω) (M.g ω),
        drvWin κ R (LengthMarkov.GermDensity.rescale (R : ℝ≥0)
          (zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) M.r M.ρ₀ C (M.X' ω)
            (M.g ω)).toNNReal (M.D ω))) := rfl

end E5
end QuantumZipper
