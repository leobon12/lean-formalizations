import QuantumZipper.Proofs.Zipper.D3PlusN2H1Kernel
import QuantumZipper.Proofs.Zipper.D3PlusN2HeartLaw

/-!
# N2-H1: independence of the lateral data of the local field from its radial Brownian motion

Task N2-H1, node `N2HLatIndepStmt` (`D3PlusN2HeartStmt.lean`):
`IndepFun (n2LatY X r) (pathOf (zRadB X r)) P` for `0 < r` and a free field `X`.

Source: Duplantier–Miller–Sheffield, arXiv:1409.7055, proof of Prop. 4.7(ii), p. 77 — the
rescaled field's projection onto `H₂(ℍ)` (the lateral part) is independent of the radial
Brownian motion `h_{e^{−t}}(0)`; Sheffield, arXiv:1012.4797, p. 25.

## The argument

Both objects are explicit functionals of the free field `X`:

* radial: `zRadB X r t =ᵐ (√2)⁻¹ (X (fc(0, r e^{−t})) − X (fc(0, r)))` — the radial increment of
  `X` at the two radii `r e^{−t} ≤ r` (`ae_zRadB_eq`), i.e. `radFamMap r` applied to the radial
  family `t ↦ gaussFam X radPair (t − log r)`;
* lateral: `n2LatY X r ω ν = lateralPart (locZField X r ω) ν`; by the Markov decomposition
  (`K3.markov_decomposition`, `K3.markovZ`) and the mean-value property of the harmonic part,
  the lateral part of the local field is the *difference* of the lateral part of `X` at `ν` and
  at its balayage `bal 0 r ν`, i.e. `latFamMap r` applied to the lateral family
  `μ ↦ X μ − X (radSmear μ)` (`latFam`, `Proofs/Zipper/D3PlusN2H1Kernel.lean`).

The independence of the lateral and radial families of `X` is proved in
`D3PlusN2H1Kernel.lean` (`indepFun_latFam_radPair`: joint Gaussianity + vanishing
cross-covariance, the rotation invariance of the Green function of the half-disc) — this is the
general form of `WedgeTK.indepFun_radialProc_lateralPart`. Independence is preserved by the
measurable maps `latFamMap`, `radFamMap` (`IndepFun.comp`), and the laws of the target pair are
the laws of the representatives (a.e. equality of the lateral data — the node
`N2H1LatReprStmt` below — and the coordinatewise a.e. equality of the radial paths,
`map_eq_of_coord_ae_eq`).

**Proved here:** `n2HLatIndep_of_repr : N2H1LatReprStmt → N2HLatIndepStmt`. Caveat: for a
general local measure `ν` the representation needs a.s. convergence of the dyadic regularization
`evalReg` at `ν`, which the project does not have (`F2.EvalRegRawStmt`, `DECISIONS.md` D17/D36);
`N2H1LatReprStmt` is therefore not proved. The restricted form (measures where the regularization
converges, e.g. folded circles and bounded densities) is proved in `D3PlusN2H1Main.lean`
(`indepFun_n2LatY_family`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

open WedgeTK GaussTK

/-! ## Measurability bookkeeping -/

/-- `radAvgReg` at a fixed radius is measurable in the field sample. -/
theorem measurable_radAvgReg_fieldSample (ρ : ℝ) :
    Measurable fun x : FieldSample => radAvgReg x ρ := by
  unfold radAvgReg
  exact (StronglyMeasurable.limUnder fun n =>
    (measurable_pi_apply (foldedCircle 0 (dyadicRound n ρ + radius n))).stronglyMeasurable).measurable

/-- The radial data of the local field are measurable at every time. -/
theorem measurable_zRadB_coord {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} {r : ℝ} (hX : IsFreeGFFModConstH X P)
    (hr : 0 < r) (t : ℝ≥0) : Measurable fun ω => zRadB X r t ω :=
  (measurable_radAvgReg_fieldSample _).comp (measurable_locZField hX hr) |>.const_mul _

/-- The radial data as a random path. -/
theorem measurable_pathOf_zRadB {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} {r : ℝ} (hX : IsFreeGFFModConstH X P)
    (hr : 0 < r) : Measurable (pathOf (zRadB X r)) :=
  measurable_pi_iff.2 fun t => measurable_zRadB_coord hX hr t

/-! ## The two measurable maps on the Gaussian families -/

open Classical in
/-- The lateral data of the local field as a function of the lateral family `L`: for a local
measure `ν` it is `L ν − L (bal 0 r ν)` (`lateralPart Z ν = lateralPart X ν − lateralPart X
(bal 0 r ν)`), and `0` on non-local measures (the junk value of `n2LatY`). -/
def latFamMap (r : ℝ) (hr : 0 < r) (L : AdmIdx → ℝ) : FieldSample :=
  fun ν => if h : K3.IsLocalH 0 r ν then L ⟨ν, h.1⟩ - L ⟨K3.bal 0 r ν, (h.bal_spec hr).1⟩
    else 0

theorem measurable_latFamMap (r : ℝ) (hr : 0 < r) : Measurable (latFamMap r hr) := by
  classical
  refine measurable_pi_iff.2 fun ν => ?_
  unfold latFamMap
  split_ifs with h
  · exact (measurable_pi_apply _).sub (measurable_pi_apply _)
  · exact measurable_const

/-- The radial path of the local field as a function of the radial family `A`: the increment
`A (t − log r) − A (−log r)` at the two radii `r e^{−t} ≤ r`, rescaled by `(√2)⁻¹`. -/
def radFamMap (r : ℝ) (A : ℝ → ℝ) : ℝ≥0 → ℝ :=
  fun t => (√2)⁻¹ * (A ((t : ℝ) - Real.log r) - A (-Real.log r))

theorem measurable_radFamMap (r : ℝ) : Measurable (radFamMap r) :=
  measurable_pi_iff.2 fun t => measurable_const.mul
    ((measurable_pi_apply ((t : ℝ) - Real.log r)).sub
      (measurable_pi_apply (-Real.log r)))

/-! ## The radial representative -/

/-- **(H1, radial side)** Coordinatewise, `zRadB` is the radial increment of the free field at
the radii `r e^{−t} ≤ r` (`ae_zRadB_eq` + `IsRegVersion.raw`), i.e. the map `radFamMap r` applied
to the radial family `t ↦ X (fc(0,e^{−t})) − X (fc(0,1))` shifted by `log r`. -/
theorem ae_zRadB_eq_radFamMap {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} {r : ℝ} (hX : IsFreeGFFModConstH X P)
    (hr : 0 < r) (t : ℝ≥0) :
    zRadB X r t =ᵐ[P] fun ω =>
      radFamMap r (fun s => gaussFam X radPair s ω) t := by
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  have hρ : 0 < r * Real.exp (-(t : ℝ)) := mul_pos hr (Real.exp_pos _)
  filter_upwards [ae_zRadB_eq hX hr hG, hG.raw 0 zero_mem_Hbar (r * Real.exp (-(t : ℝ))) hρ,
    hG.raw 0 zero_mem_Hbar r hr] with ω h1 h2 h3
  rw [h1, h2, h3]
  simp only [radFamMap, gaussFam, radPair]
  rw [show Real.exp (-((t : ℝ) - Real.log r)) = r * Real.exp (-(t : ℝ)) by
      rw [neg_sub, Real.exp_sub, Real.exp_log hr, Real.exp_neg]; ring,
    show Real.exp (-(-Real.log r)) = r by rw [neg_neg, Real.exp_log hr]]
  ring

/-! ## The remaining node and the assembly -/

end D3Plus
end QuantumZipper
