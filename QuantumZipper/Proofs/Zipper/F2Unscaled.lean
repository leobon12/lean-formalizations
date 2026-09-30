import QuantumZipper.Proofs.Zipper.F2UnscaledScale
import QuantumZipper.Proofs.Zipper.F2Reduce
import QuantumZipper.Proofs.Zipper.B3dLen
import QuantumZipper.Proofs.Zipper.F1Side3
import QuantumZipper.Proofs.Wire2b

/-!
# F2 step (2a): F1 transfers to the unscaled wedge configuration (random rescaling B3(d))

Theorem 1.3, node F2, input 2 (`F2.F2UnscaledStmt := F1Stmt → UnscaledLenAgree`).
Source: Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.1 (pp. 60–62:
quantum surfaces modulo `z ↦ a z`, `h ↦ h(a·) + Q log a`; Brownian scaling of the driver) and
§5.4 (proof of Theorem 1.3, pp. 70–72), where the passage between the canonical and the unscaled
embedding is tacit.

Argument (own bookkeeping around the cited scaling): let `Z` be the unscaled wedge field,
`a = scaleParam γ Z > 0` a.s. (`Wire2.ae_wedge_canonical_spec`) and `B'` the Brownian
rescaling of the driver by the random factor `a` (`rscale`). Then
* `(canonical γ Z, √κ B') = canonConfig γ (Z, √κ B'')` pointwise (`canonConfig_eq_drive`);
* `B'` is a Brownian motion independent of `canonical γ Z`: `randScale_isBrownian_indep`
  (F2UnscaledScale.lean), because `(canonical γ Z, a)` is independent of `B''`;
* `canonical γ Z` is a quantum wedge by definition (`IsQuantumWedge`, same reference space);
so F1 applies to the `P_*` sample `(canonical γ Z, B')`, and `B3d.lenAgree_canon_iff` transfers
`L⁻ = L⁺` from canonical time `s` to unscaled time `a² s`; `t ↦ t / a²` covers `[0, ∞)`.
The side images exist by `RS.ae_real_alive` (Rohde–Schramm Lemma 6.2) and
`F1.exists_tendsto_sideImages_of_alive`.

## Open inputs (exact statements below)
* `UnscaledCanonIndepStmt`: the pair `(canonical γ Z, scaleParam γ Z)` is an a.e.-measurable
  random variable independent of the driver path `B''` (it is a function of `(X', A)`, which is
  independent of `B''`; the missing part is the measurability of that function).
* `UnscaledB3dStmt`: a.s., the fields unzipped from the unscaled configuration are good
  (`IsLQGGood`) at all times, and B3(d) at the field level holds at all times.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

/-- The unscaled wedge field `wedgeField (lateralPart X') A Q`. -/
abbrev zU (γ : ℝ) {Ω : Type*} (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (ω : Ω) : FieldSample :=
  wedgeField (lateralPart (X' ω)) (fun t => A t ω) (Qc γ)

/-! ## Deterministic identities -/

theorem drive_max {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (s : ℝ) :
    drive κ B ω (max s 0) = drive κ B ω s := by
  rcases le_total s 0 with h | h
  · simp [drive, max_eq_right h, Real.toNNReal_of_nonpos h]
  · simp [drive, max_eq_left h]

/-- The driver of the canonicalized configuration is the Brownian rescaling by `a`. -/
theorem canonConfig_eq_drive {Ω : Type*} (γ κ : ℝ) (y : FieldSample) (B : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (ha : 0 < scaleParam γ y) :
    canonConfig γ (y, drive κ B ω) =
      (canonical γ y, drive κ (rscale (fun _ => (scaleParam γ y ^ 2).toNNReal) B) ω) := by
  set a := scaleParam γ y with ha_def
  refine Prod.ext rfl (funext fun r => ?_)
  simp only [canonConfig, drive, rscale]
  have hc : ((a ^ 2).toNNReal : ℝ) = a ^ 2 := Real.coe_toNNReal _ (sq_nonneg a)
  have hsq : √((a ^ 2).toNNReal : ℝ) = a := by rw [hc, Real.sqrt_sq ha.le]
  have hmul : (a ^ 2).toNNReal * r.toNNReal = (a ^ 2 * max r 0).toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_mul, hc, Real.coe_toNNReal', Real.coe_toNNReal _
      (mul_nonneg (sq_nonneg a) (le_max_right r 0))]
  rw [hsq, hmul, ← ha_def]
  field_simp

/-! ## The transfer -/

/-- The measurable nowhere-zero scale function `(y, a) ↦ a²` (junk `1` for `a ≤ 0`). -/
def sqScale (p : FieldSample × ℝ) : ℝ≥0 := if 0 < p.2 then (p.2 ^ 2).toNNReal else 1

theorem measurable_sqScale : Measurable sqScale :=
  Measurable.ite (measurableSet_lt measurable_const measurable_snd)
    (measurable_snd.pow_const 2).real_toNNReal measurable_const

theorem sqScale_ne_zero (p : FieldSample × ℝ) : sqScale p ≠ 0 := by
  unfold sqScale
  split_ifs with h
  · exact (Real.toNNReal_pos.2 (by positivity)).ne'
  · exact one_ne_zero

/-- **Random rescaling of a Brownian motion** (non-regularized form): if `ξ` is a.e.-measurable
and independent of `B`, then `rscale (c ∘ ξ) B` is a Brownian motion independent of `ξ`, for
measurable nowhere-zero `c`. -/
theorem randScale_of_aemeasurable {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {ξ : Ω → β} (hξ : AEMeasurable ξ P) {c : β → ℝ≥0} (hcm : Measurable c)
    (hc0 : ∀ b, c b ≠ 0) (hind : IndepFun ξ (pathOf B) P) :
    IsBrownianReal (rscale (c ∘ ξ) B) P ∧ IndepFun ξ (pathOf (rscale (c ∘ ξ) B)) P := by
  obtain ⟨B₁, hB₁m, hB₁c, -, hB₁, hB₁eq⟩ := RS.exists_good_version0 hB
  have hpath : pathOf B =ᵐ[P] pathOf B₁ := by
    filter_upwards [hB₁eq] with ω h
    funext t; exact (h t).symm
  have hind' : IndepFun (hξ.mk ξ) (pathOf B₁) P := hind.congr hξ.ae_eq_mk hpath
  obtain ⟨hBr, hI⟩ := randScale_isBrownian_indep hξ.measurable_mk hcm hc0
    hB₁.toIsPreBrownianReal hB₁m hB₁c hind'
  have heq : ∀ᵐ ω ∂P, pathOf (rscale (c ∘ hξ.mk ξ) B₁) ω = pathOf (rscale (c ∘ ξ) B) ω := by
    filter_upwards [hB₁eq, hξ.ae_eq_mk] with ω h1 h2
    funext t
    simp only [pathOf, rscale, Function.comp, h2, h1]
  refine ⟨⟨hBr.toIsPreBrownianReal.congr fun t => heq.mono fun ω h => congrFun h t, ?_⟩,
    hI.congr hξ.ae_eq_mk.symm heq⟩
  filter_upwards [hBr.cont, heq] with ω h1 h2
  exact (congrArg (fun f : ℝ≥0 → ℝ => Continuous f) h2).mp h1

theorem sqrt_lt_two_of' {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) : Real.sqrt κ < 2 := by
  rw [show (2 : ℝ) = Real.sqrt 4 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt hκ.le hκ4

theorem alpha_lt_Qc' {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : γ - 2 / γ < Qc γ := by
  unfold Qc
  have h : 1 < 2 / γ := (one_lt_div hγ).2 hγ2
  linarith

end F2
end QuantumZipper
