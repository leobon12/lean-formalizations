import QuantumZipper.Proofs.Zipper.F1Germ
import QuantumZipper.Proofs.GFF.LateralGerm
import QuantumZipper.Proofs.Probability.TailTrivial

/-!
# F1c: the three germ families of the unscaled wedge embedding

Theorem 1.3, node F1c (`blueprint/E_BRANCH_BLUEPRINT.md` §F1; Sheffield, arXiv:1012.4797, §5.4,
pp. 70–72). On a space carrying a free field `X`, a wedge radial process `A` and a Brownian
motion `B`, the unscaled wedge configuration is
`unscaledConfig γ κ X A B ω = (wedgeField (lateralPart (X ω)) (A · ω) Q, √κ B ω)`.
The level-`n` data are
* the lateral germ `lateralGerm X P 2⁻ⁿ` (lateral part near `0`; E-L11),
* the radial tail `radTail A n = σ(A_t : t ≥ n)` (the radial part on `ball 0 e⁻ⁿ`),
* the driver germ `bmPast B (1/(n+1))`.
This file proves the structural hypotheses of `f1cd_lengths_agree_local` for these families:
`germFam_le`, `germFam_anti`, `germFam_indep` (from the independence of `X`, `A`, `B`), and
`germFam_triv` (E-L11 `isTrivialSigma_lateralGerm`, the large-time tail of Brownian motion with
drift `TailTrivial.isTrivialSigma_tailFar_drift`, Blumenthal `isTrivialSigma_iInf_bmPast`).
The locality input is the open statement `F1LocalityStmt` (B5 locality: at small times, on
events that eventually occur, the lengths are measurable for the level-`n` data), and
`f1cd_lengths_agree_unscaled` is F1c + F1d for the unscaled configuration given it.
Own elementary arguments (bookkeeping around the cited 0-1 laws).
-/

noncomputable section

set_option warn.classDefReducibility false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace F1

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The radial tail `σ(A_t : t ≥ n)`. -/
def radTail (A : ℝ → Ω → ℝ) (n : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (u : Set.Ici (n : ℝ≥0)) => A ((u : ℝ≥0) : ℝ) ω) inferInstance

/-- The three germ families: lateral germ, radial tail, driver germ. -/
def germFam (X : Ω → FieldSample) (P : Measure Ω) (A : ℝ → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) :
    Fin 3 → ℕ → MeasurableSpace Ω :=
  ![fun n => LateralGerm.lateralGerm X P ((2 : ℝ)⁻¹ ^ n), radTail A,
    fun n => GermZeroOne.bmPast B (GermZeroOne.epsSeq n)]

/-- The σ-algebras of the three sources. -/
def srcSigma (X : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) : Fin 3 → MeasurableSpace Ω :=
  ![MeasurableSpace.comap X inferInstance, MeasurableSpace.comap (fun ω t => A t ω) inferInstance,
    MeasurableSpace.comap (pathOf B) inferInstance]

/-- The unscaled wedge configuration. -/
def unscaledConfig (γ κ : ℝ) (X : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    FieldSample × (ℝ → ℝ) :=
  (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ), drive κ B ω)

theorem lateralGerm_mono (X : Ω → FieldSample) (P : Measure Ω) {r r' : ℝ} (h : r ≤ r') :
    LateralGerm.lateralGerm X P r ≤ LateralGerm.lateralGerm X P r' :=
  iSup₂_le fun μ hμ => le_iSup₂_of_le (f := fun (μ : Measure ℂ) (_ : IsAdmissibleH μ ∧
      μ (Metric.closedBall 0 r' ∩ Hbar)ᶜ = 0 ∧ ∀ᵐ ω ∂P, evalReg (X ω) μ = X ω μ) =>
      MeasurableSpace.comap (fun ω => lateralPart (X ω) μ) inferInstance) μ
    ⟨hμ.1, measure_mono_null (compl_subset_compl.2 (inter_subset_inter_left _
      (Metric.closedBall_subset_closedBall h))) hμ.2.1, hμ.2.2⟩ le_rfl

theorem lateralGerm_le_comap (X : Ω → FieldSample) (P : Measure Ω) (r : ℝ) :
    LateralGerm.lateralGerm X P r ≤ MeasurableSpace.comap X inferInstance :=
  iSup₂_le fun μ h => by
    have := h.1.1
    exact measurable_iff_comap_le.1
      ((WedgeTK.measurable_lateralPart_apply μ).comp (comap_measurable X))

omit mΩ in
theorem radTail_le_comap (A : ℝ → Ω → ℝ) (n : ℕ) :
    radTail A n ≤ MeasurableSpace.comap (fun ω t => A t ω) inferInstance :=
  Measurable.comap_le (GermZeroOne.measurable_pi_of fun _ =>
    GermZeroOne.measurable_comap_coord (fun ω t => A t ω) _)

omit mΩ in
theorem radTail_anti (A : ℝ → Ω → ℝ) : Antitone (radTail A) := fun a b hab =>
  Measurable.comap_le (GermZeroOne.measurable_pi_of fun u =>
    GermZeroOne.measurable_comap_coord (fun ω (u : Set.Ici (a : ℝ≥0)) => A ((u : ℝ≥0) : ℝ) ω)
      ⟨u, le_trans (show (a : ℝ≥0) ≤ b by exact_mod_cast hab) u.2⟩)

omit mΩ in
theorem bmPast_le_comap (B : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) :
    GermZeroOne.bmPast B u ≤ MeasurableSpace.comap (pathOf B) inferInstance :=
  Measurable.comap_le (GermZeroOne.measurable_pi_of fun t =>
    GermZeroOne.measurable_comap_coord (pathOf B) (t : ℝ≥0))

theorem germFam_le_src (X : Ω → FieldSample) (P : Measure Ω) (A : ℝ → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (i : Fin 3) (n : ℕ) : germFam X P A B i n ≤ srcSigma X A B i := by
  fin_cases i
  · exact lateralGerm_le_comap X P _
  · exact radTail_le_comap A n
  · exact bmPast_le_comap B _

theorem srcSigma_le {X : Ω → FieldSample} {A : ℝ → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hX : Measurable X) (hA : ∀ t, Measurable (A t)) (hB : ∀ t, Measurable (B t)) (i : Fin 3) :
    srcSigma X A B i ≤ mΩ := by
  fin_cases i
  · exact hX.comap_le
  · exact (measurable_pi_iff.2 hA).comap_le
  · exact (measurable_pi_iff.2 hB).comap_le

theorem germFam_le {X : Ω → FieldSample} {A : ℝ → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hX : Measurable X) (hA : ∀ t, Measurable (A t)) (hB : ∀ t, Measurable (B t)) (i : Fin 3)
    (n : ℕ) : germFam X P A B i n ≤ mΩ :=
  (germFam_le_src X P A B i n).trans (srcSigma_le hX hA hB i)

theorem germFam_anti (X : Ω → FieldSample) (P : Measure Ω) (A : ℝ → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (i : Fin 3) : Antitone (germFam X P A B i) := by
  fin_cases i
  · exact fun a b hab => lateralGerm_mono X P
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hab)
  · exact radTail_anti A
  · exact fun a b hab => GermZeroOne.bmPast_mono (GermZeroOne.epsSeq_antitone hab)

theorem germFam_indep {X : Ω → FieldSample} {A : ℝ → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hind : iIndep (srcSigma X A B) P) : iIndep (fun i => germFam X P A B i 0) P :=
  iIndep_of_iIndep_of_le hind fun i => germFam_le_src X P A B i 0

/-- Large-time tail triviality of the wedge radial process. -/
theorem isTrivialSigma_radTail {α Q : ℝ} {A : ℝ → Ω → ℝ} (hA : IsWedgeProcess α Q A P)
    (hAm : ∀ t, Measurable (A t)) : GermZeroOne.IsTrivialSigma (⨅ n, radTail A n) P := by
  obtain ⟨b, b', hb, -, -, hAb⟩ := hA
  have hAu : ∀ (u : ℝ≥0) ω, A u ω = Real.sqrt 2 * b u ω + (α - Q) * (u : ℝ) := fun u ω => by
    rw [hAb ω u]
    simp [wedgePath]
  have hbm : ∀ u, Measurable (b u) := fun u => by
    have e : b u = fun ω => (A u ω - (α - Q) * (u : ℝ)) / Real.sqrt 2 := by
      funext ω
      rw [hAu u ω]
      field_simp
      ring
    rw [e]
    exact ((hAm _).sub_const _).div_const _
  refine (TailTrivial.isTrivialSigma_tailFar_drift hb.toIsPreBrownianReal hbm (Real.sqrt 2)
    (α - Q)).mono (le_iInf fun t => (iInf_le _ ⌈t⌉₊).trans ?_)
  refine Measurable.comap_le (GermZeroOne.measurable_pi_of fun u => ?_)
  have htu : t ≤ (u : ℝ≥0) := (Nat.le_ceil t).trans u.2
  have e : (fun ω => A ((u : ℝ≥0) : ℝ) ω) =
      fun ω => Real.sqrt 2 * b (u : ℝ≥0) ω + (α - Q) * ((u : ℝ≥0) : ℝ) :=
    funext fun ω => hAu u ω
  rw [e]
  exact GermZeroOne.measurable_comap_coord
    (fun ω (v : Set.Ici t) => Real.sqrt 2 * b (v : ℝ≥0) ω + (α - Q) * ((v : ℝ≥0) : ℝ))
    ⟨u, htu⟩

/-- **Trivial germs** of the three families: E-L11 (lateral), large-time tail of Brownian motion
with drift (radial), Blumenthal (driver). -/
theorem germFam_triv [IsProbabilityMeasure P] {α Q : ℝ} {X : Ω → FieldSample}
    {A : ℝ → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} (hX : IsFreeGFFModConstH X P)
    (hA : IsWedgeProcess α Q A P) (hAm : ∀ t, Measurable (A t)) (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (i : Fin 3) :
    GermZeroOne.IsTrivialSigma (⨅ n, germFam X P A B i n) P := by
  fin_cases i
  · exact LateralGerm.isTrivialSigma_lateralGerm hX
  · exact isTrivialSigma_radTail hA hAm
  · exact GermZeroOne.isTrivialSigma_iInf_bmPast hB hBm

end F1
end QuantumZipper
