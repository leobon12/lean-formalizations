import QuantumZipper.Proofs.Zipper.WedgeUnzipCore
import QuantumZipper.Proofs.Zipper.FSMeasF2
import QuantumZipper.Proofs.Wire2b
import QuantumZipper.Proofs.NonVacuity

/-!
# D29 (wedge unzipping), part 8: realization of `P_*` samples (core P)

`WedgeUnzip.PStarRealizeStmt` (core P, `WedgeUnzipCore.lean`) says that every `P_*` sample
`(Y, B')` is, on a product extension `Ω' × Ω₂`, the canonicalization `canonConfig γ (Z, √κ B'')`
of an *unscaled* wedge configuration `Z = zU γ X' A`, with `(X', A)` a free field modulo constants
and a wedge process, independent of the fresh driver `B''`; the field part is required to agree
with `Y` only through `avgReg` (`(6)(i)`), because `unzippedField` reads the field through
`avgReg` alone (`FSMeas.coordChange_congr_avgReg`, `FSMeas.unzipLengths_congr_avgReg`).

Source of the statement: Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797,
§5.1 (pp. 60–62, B3(d): the canonical description is the unscaled one rescaled by the random
scale `a = scaleParam`) and §5.4 (pp. 70–72).

## What the statement really forces (and why it is not a law-level statement)

`canonConfig γ (y, W) = (canonical γ y, fun s => W (a² max s 0)/a)` with `a = scaleParam γ y`; by
`F2.canonConfig_eq_drive` its second component is `drive κ (rscale (a²) B'')`. Hence the a.s.
identity `(6)(ii)` *forces* `B''` to be the inverse Brownian rescaling of `B'` by `a`:
`B'' = rscale (a⁻²) B'` (`F2.rscale_mul`, `rscale_one`, `rscale_inv_apply`). So `B''` is *not* a
free random variable on `Ω₂`: it is a function of the witness `(X', A)` (through `a`) and of `B'`.
Likewise `(6)(i)` makes `Y(ω.1)` (through `avgReg`) a function of the witness. Consequently the
pair `(X', A)` cannot be taken to be independent of `ω.1`: an a.s. identity between a function of
`ω.1` and a function of `ω.2` alone under `P' ⊗ Q` forces both to be a.s. constant. The witness
must instead be realised *conditionally on the sample* — as a regular conditional version of the
unscaled configuration given `Y` (Kallenberg, *Foundations of Modern Probability*, 2nd ed.,
Thm. 6.10 (transfer) and Lemma 4.22: a kernel into a standard Borel space is the image of the
uniform law under a jointly measurable map, `ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval`),
realised on `Ω' × I` with `Q` the uniform law on `I = [0,1]`.

## What is proved here

* `F2.rscale_mul`, `F2.rscale_one`, `rscale_inv_apply`: the rescaling algebra.
* `PStarWitnessRealizeStmt`: the witness core (core P with `B''` eliminated), stated exactly.
* `pStarRealizeStmt_of_witness`: **core P from the witness core** — the bookkeeping which
  constructs `B'' = rscale (invCanScale γ ∘ (X',A)) (liftPath B')` and derives all six
  requirements, using `F2.randScale_of_aemeasurable` (the random Brownian rescaling is a Brownian
  motion independent of the *whole* witness, not merely of the scale), `FSMeas.xiU_spec` (the
  measurable canonical data as a function of the witness) and `Wire2.ae_wedge_canonical_spec`
  (positivity of the canonical scale).

Own bookkeeping (independence and rescaling identities); no literature source applies beyond the
cited §5.1/§5.4 of the paper.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper

namespace F2

end F2

namespace WedgeUnzip

/-! ## 1. Rescaling algebra used in the construction -/

/-- The unscaled wedge configuration's witness `(X', A)` as one random element. -/
def witPair {Ω : Type*} (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) : Ω → FieldSample × (ℝ → ℝ) :=
  fun ω => (X' ω, fun t => A t ω)

/-- The driving Brownian motion of a sample, lifted to a product extension. -/
def liftPath {Ω Ω₂ : Type*} (B : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω × Ω₂ → ℝ := fun t ω => B t ω.1

/-- The inverse square canonical scale, as a *measurable* function of the witness data: the
coordinates of the unscaled field are read through `FSMeas.wedgeCoordsM`, and the canonical
scale through the measurable version `FSMeas.canonVer` (D27). -/
def invCanScale (γ : ℝ) (q : FieldSample × (ℝ → ℝ)) : ℝ≥0 :=
  (F2.sqScale (FSMeas.canonVer γ (FSMeas.wedgeCoordsM (Qc γ) q)))⁻¹

theorem measurable_invCanScale (γ : ℝ) : Measurable (invCanScale γ) :=
  measurable_inv.comp (F2.measurable_sqScale.comp ((FSMeas.measurable_canonVer γ).comp
    (FSMeas.measurable_wedgeCoordsM (Qc γ))))

theorem invCanScale_ne_zero (γ : ℝ) (q : FieldSample × (ℝ → ℝ)) : invCanScale γ q ≠ 0 :=
  inv_ne_zero (F2.sqScale_ne_zero (FSMeas.canonVer γ (FSMeas.wedgeCoordsM (Qc γ) q)))

/-! ## 2. The witness core -/

/-- **(Core P-witness)** On a product extension, an unscaled wedge configuration realizing a
`P_*` sample: a free field modulo constants `X'` and a wedge process `A`, mutually independent
and independent of the lifted driving path of `B'`, whose canonicalization is `avgReg`-equal to
`Y`. This is core P with `B''` eliminated: `B''` is then *forced* to be
`rscale (invCanScale γ ∘ (X', A)) (liftPath B')` (see `pStarRealizeStmt_of_witness`).

Provable in principle by the transfer theorem (Kallenberg, *Foundations of Modern Probability*,
2nd ed., Thm. 6.10 and Lemma 4.22): the `IsQuantumWedge` witness `(X, A)` of `Y`'s law, encoded
by the jointly measurable coordinates of its unscaled field (`FSMeas.wedgeCoordsM`, whose law is
the unscaled-configuration law), disintegrated over the sample coordinate with
`Measure.condKernel`, and realised on `Ω' × I` with `Q = ` Lebesgue via
`ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval`; the fiber property
`avgReg (canonical γ (zU γ X' A ω)) = avgReg (Y ω.1)` is the defining property of the regular
conditional distribution (the a.s. identity holds by `IsQuantumWedge` + `FSMeas.xiU_spec`). Not
proved here: it is the transfer/measurability core, isolated deliberately. -/
def PStarWitnessRealizeStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∃ (Ω₂ : Type) (_ : MeasurableSpace Ω₂) (Q : Measure Ω₂) (_ : IsProbabilityMeasure Q)
      (X' : Ω' × Ω₂ → FieldSample) (A : ℝ → Ω' × Ω₂ → ℝ),
      IsFreeGFFModConstH X' (P'.prod Q) ∧
      IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A (P'.prod Q) ∧
      IndepFun X' (fun ω t => A t ω) (P'.prod Q) ∧
      IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf (liftPath B')) (P'.prod Q) ∧
      ∀ᵐ ω ∂(P'.prod Q),
        avgReg (Y ω.1) = avgReg (canonical (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω))

/-! ## 3. Core P from the witness core -/

/-- **Core P (`PStarRealizeStmt`) from the witness core.** Given `(X', A)` as in
`PStarWitnessRealizeStmt`, put `B'' = rscale (invCanScale γ ∘ (X', A)) (liftPath B')`: the
inverse Brownian rescaling of `B'` by the canonical scale `a = scaleParam γ (zU γ X' A)` of the
realized unscaled field. Then

* `B''` is a Brownian motion and independent of the *whole* witness `(X', A)`
  (`F2.randScale_of_aemeasurable`, applied with `ξ = (X', A)`);
* `canonConfig γ (Z, √κ B'') = (canonical γ Z, √κ B')` a.s., because rescaling by `a²` undoes the
  inverse rescaling (`F2.rscale_mul`, `rscale_inv_apply`) and `canonConfig`'s driver is exactly
  `drive κ (rscale (a²) ·)` (`F2.canonConfig_eq_drive`);
* the field identity `(6)(i)` is the hypothesis.

The canonical data of `Z` is the *measurable* version `FSMeas.xiU` (`FSMeas.xiU_spec`), so
`invCanScale γ ∘ (X', A)` is a.e. the honest inverse square scale `((scaleParam γ Z)²)⁻¹`. -/
theorem pStarRealizeStmt_of_witness
    (h : ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
      ∃ (Ω₂ : Type) (_ : MeasurableSpace Ω₂) (Q : Measure Ω₂) (_ : IsProbabilityMeasure Q)
        (X' : Ω' × Ω₂ → FieldSample) (A : ℝ → Ω' × Ω₂ → ℝ),
        IsFreeGFFModConstH X' (P'.prod Q) ∧
        IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A (P'.prod Q) ∧
        IndepFun X' (fun ω t => A t ω) (P'.prod Q) ∧
        IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf (liftPath B')) (P'.prod Q) ∧
        ∀ᵐ ω ∂(P'.prod Q),
          avgReg (Y ω.1) = avgReg (canonical (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω))) :
    PStarRealizeStmt := by
  intro κ Ω' _ P' _ Y B' hPS
  obtain ⟨hκ, hκ4, -, hB', -⟩ := id hPS
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  have hα : Real.sqrt κ - 2 / Real.sqrt κ < Qc (Real.sqrt κ) := F2.alpha_lt_Qc' hγ hγ2
  obtain ⟨Ω₂, instΩ₂, Q, instQ, X', A, hX, hA, hI, hIV, havg⟩ := h κ P' Y B' hPS
  -- the witness as a measurable random element, and its measurable canonical data
  have hwm : AEMeasurable (witPair X' A) (P'.prod Q) :=
    (WedgeTK.measurable_X_pi hX).aemeasurable.prodMk (ZoomRadial.aemeasurable_wedgePath hA)
  have hind : IndepFun (witPair X' A) (pathOf (liftPath B')) (P'.prod Q) := hIV
  obtain ⟨-, -, hξ⟩ := FSMeas.xiU_spec hγ hγ2 hα hX hA hI hind
  have hspec := Wire2.ae_wedge_canonical_spec hγ hγ2 hα hX hA hI
  -- the lifted driver is Brownian, and `B''` is its inverse rescaling by the canonical scale
  have hBlift : IsBrownianReal (liftPath B') (P'.prod Q) :=
    NonVacuity.nv_isBrownianReal measurePreserving_fst hB'
  obtain ⟨hB'', hI''⟩ := F2.randScale_of_aemeasurable hBlift hwm
    (measurable_invCanScale (Real.sqrt κ)) (invCanScale_ne_zero (Real.sqrt κ)) hind
  refine ⟨Ω₂, inferInstance, Q, inferInstance, X', A,
    F2.rscale (invCanScale (Real.sqrt κ) ∘ witPair X' A) (liftPath B'),
    hX, hA, hI, hB'', hI'', ?_⟩
  filter_upwards [havg, hξ, hspec] with ω h5 hξω hspecω
  refine ⟨h5, ?_⟩
  have ha : 0 < scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) := hspecω.1
  -- the measurable canonical data at `ω`, in unfolded form
  have hξ' : FSMeas.canonVer (Real.sqrt κ)
      (FSMeas.wedgeCoordsM (Qc (Real.sqrt κ)) (X' ω, fun t => A t ω)) =
      (FSMeas.sfTrunc (canonical (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω)),
        scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω)) := hξω
  -- `invCanScale` is the honest inverse square scale
  have hsq : F2.sqScale (FSMeas.canonVer (Real.sqrt κ)
      (FSMeas.wedgeCoordsM (Qc (Real.sqrt κ)) (X' ω, fun t => A t ω))) =
      (scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) ^ 2).toNNReal := by
    rw [hξ']
    simp only [F2.sqScale, ha, ↓reduceIte]
  have hval : (invCanScale (Real.sqrt κ) ∘ witPair X' A) ω =
      ((scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) ^ 2).toNNReal)⁻¹ := by
    show (F2.sqScale (FSMeas.canonVer (Real.sqrt κ)
      (FSMeas.wedgeCoordsM (Qc (Real.sqrt κ)) (X' ω, fun t => A t ω))))⁻¹ = _
    rw [hsq]
  have hd : ((scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) ^ 2).toNNReal) ≠ 0 := by
    simp only [ne_eq, Real.toNNReal_eq_zero]
    exact fun h => pow_ne_zero 2 ha.ne' (h.antisymm (sq_nonneg _))
  -- the driver of the canonicalized configuration is `√κ B'`
  rw [F2.canonConfig_eq_drive (Real.sqrt κ) κ (F2.zU (Real.sqrt κ) X' A ω) _ ω ha]
  refine Prod.ext rfl (funext fun u => ?_)
  simp only [drive, F2.rscale, hval, liftPath, NNReal.coe_inv]
  have hc0 : (0 : ℝ) < ((scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) ^ 2).toNNReal : ℝ) := by
    rw [Real.coe_toNNReal _ (sq_nonneg _)]
    exact pow_pos ha 2
  have harg : ((scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) ^ 2).toNNReal)⁻¹ *
      ((scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) ^ 2).toNNReal * u.toNNReal) =
      u.toNNReal := by
    rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]
  have hs : (Real.sqrt (((scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) ^ 2).toNNReal : ℝ)⁻¹))⁻¹ =
      Real.sqrt ((scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) ^ 2).toNNReal : ℝ) := by
    rw [Real.sqrt_inv, inv_inv]
  rw [harg, hs]
  set Y₀ := B' u.toNNReal ω.1 with hY₀def
  rw [← mul_assoc ((Real.sqrt ((scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) ^ 2).toNNReal : ℝ))⁻¹)
      (Real.sqrt ((scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) ^ 2).toNNReal : ℝ)) Y₀,
    inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 hc0)), one_mul]

/-- **Core P from the named witness core** (`PStarWitnessRealizeStmt`, the `def` form). -/
theorem pStarRealizeStmt_of_witnessStmt (h : PStarWitnessRealizeStmt) : PStarRealizeStmt :=
  pStarRealizeStmt_of_witness h

end WedgeUnzip
end QuantumZipper
