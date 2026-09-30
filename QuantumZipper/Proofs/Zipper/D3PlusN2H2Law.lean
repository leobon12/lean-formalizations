import QuantumZipper.Proofs.Zipper.D3PlusN2HeartStmt
import QuantumZipper.Proofs.LQG.WedgeRestriction
import QuantumZipper.Proofs.Zipper.UnzipInvariance

/-!
# N2-H2 on a regular window family: the free-field lateral window has a scale-free law

Task N2-H2, restricted per Decision D36 (window index = folded circles and bounded compactly
supported densities, where the dyadic regularization converges). This file proves the free-field
half of H2 (`N2H2ScaleStmt` + `N2H2InvStmt` of `D3PlusN2H2Basic.lean`) for **any** index family
`ι : I → Measure ℂ` of admissible measures at which the regularized evaluation of a free field is
a.s. exact after every dilation (`WinRegFam ι`):

* `map_latWinFreeI_eq`: for `a > 0`, the law of the rescaled lateral window
  `i ↦ evalReg (X ω) (ι i ∘ (a·)⁻¹) − ∫ radAvgReg (X ω) (a‖z‖) dι i` of a free field `X`
  equals the law of the plain lateral window `i ↦ lateralPart (X'' ω) (ι i)` of **any** free
  field `X''`.
* `winRegFam_foldedCircle`: folded circles form such a family.

Route (DMS arXiv:1409.7055, proof of Prop. 4.7(ii), p. 78: "the rescaling procedure does not
affect the projection of `h` onto `H₂(ℍ)`"): both windows are a.s. coordinatewise the Gaussian
pair differences `X(μ) − X(radSmear μ)` (`WedgeTK.ae_integral_radial`, `WedgeTK.ae_lateral_X`),
whose law depends only on the Neumann covariance (`WedgeTK.map_gaussFam_eq`,
`WedgeRes.map_gaussFam_eq₂`), and the covariance is dilation invariant on balanced pairs
(`WedgeTK.kernelCov2_map_mul`, `WedgeTK.radSmear_map_mul`). Own assembly of these in-project
facts, following the proof of `WedgeTK.fieldLawFull_lateralPart_rescale`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus
namespace N2H2Law

open WedgeTK

variable {I : Type*} (ι : I → Measure ℂ)

/-- The rescaled free-field lateral window on the index family `ι` (the `evalReg` form of
`lateralPart (rescale X Q a)`; at `LocIdx` this is `n2LatWinFree`). -/
def latWinFreeI (a : ℝ) {Ω : Type*} (X : Ω → FieldSample) (ω : Ω) (i : I) : ℝ :=
  evalReg (X ω) ((ι i).map fun z => (a : ℂ) * z) - ∫ z, radAvgReg (X ω) (a * ‖z‖) ∂(ι i)

/-- The plain lateral window on the index family `ι` (at `LocIdx` this is `latY''`). -/
def latFreeI {Ω : Type*} (X : Ω → FieldSample) (ω : Ω) (i : I) : ℝ := lateralPart (X ω) (ι i)

/-- A regular window family: admissible measures at which the regularized evaluation of every
free field is a.s. exact after every dilation `z ↦ b z`, `b > 0`. -/
def WinRegFam : Prop :=
  (∀ i, IsAdmissibleH (ι i)) ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Ω → FieldSample), IsFreeGFFModConstH X P → ∀ b : ℝ, 0 < b → ∀ i,
      ∀ᵐ ω ∂P, evalReg (X ω) ((ι i).map fun z => (b : ℂ) * z) =
        X ω ((ι i).map fun z => (b : ℂ) * z)

variable {ι}

/-- The dilated balanced pairs `(μ_b, radSmear μ_b)`, `μ_b = ι i ∘ (b·)⁻¹`. -/
def pairMul (hι : ∀ i, IsAdmissibleH (ι i)) {b : ℝ} (hb : 0 < b) (i : I) : BPair :=
  ⟨((ι i).map fun u => (b : ℂ) * u, radSmear ((ι i).map fun u => (b : ℂ) * u)),
    isAdmissibleH_map_mul hb (hι i), isAdmissibleH_radSmear (isAdmissibleH_map_mul hb (hι i)),
    (radSmear_univ _).symm⟩

/-- The undilated balanced pairs `(ι i, radSmear (ι i))`. -/
def pairId (hι : ∀ i, IsAdmissibleH (ι i)) (i : I) : BPair :=
  ⟨(ι i, radSmear (ι i)), hι i, isAdmissibleH_radSmear (hι i), (radSmear_univ _).symm⟩

theorem kernelCov2_pairMul (hι : ∀ i, IsAdmissibleH (ι i)) {b : ℝ} (hb : 0 < b) (i j : I) :
    kernelCov2 neumannH (pairMul hι hb i).1 (pairMul hι hb j).1 =
      kernelCov2 neumannH (pairId hι i).1 (pairId hι j).1 := by
  show kernelCov2 neumannH ((ι i).map _, radSmear ((ι i).map _))
      ((ι j).map _, radSmear ((ι j).map _)) = _
  rw [radSmear_map_mul hb, radSmear_map_mul hb]
  exact kernelCov2_map_mul hb (pairId hι i) (pairId hι j)

theorem measurable_latWinFreeI (hι : ∀ i, IsAdmissibleH (ι i)) {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → FieldSample} (hX : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ) (a : ℝ) :
    Measurable (latWinFreeI ι a X) := by
  refine measurable_pi_iff.2 fun i => ?_
  have : IsFiniteMeasure (ι i) := (hι i).1
  have hXm : Measurable X := measurable_pi_iff.2 hX
  have h1 : Measurable fun ω => evalReg (X ω) ((ι i).map fun z => (a : ℂ) * z) :=
    (measurable_evalReg (ν := (ι i).map fun z => (a : ℂ) * z)).comp hXm
  have hf : StronglyMeasurable fun p : Ω × ℂ => radAvgReg (X p.1) (a * ‖p.2‖) := by
    have hm : Measurable fun p : Ω × ℂ => (X p.1, a * ‖p.2‖) :=
      (hXm.comp measurable_fst).prodMk (measurable_const.mul (measurable_norm.comp measurable_snd))
    exact (measurable_radAvgReg₂.comp hm).stronglyMeasurable
  exact h1.sub (StronglyMeasurable.integral_prod_right' (ν := ι i) hf).measurable

theorem measurable_latFreeI (hι : ∀ i, IsAdmissibleH (ι i)) {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → FieldSample} (hX : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ) :
    Measurable (latFreeI ι X) := by
  refine measurable_pi_iff.2 fun i => ?_
  have : IsFiniteMeasure (ι i) := (hι i).1
  exact (measurable_lateralPart_apply (ι i)).comp (measurable_pi_iff.2 hX)

/-- Model-side window: a.s. the Gaussian pair difference at the dilated pair. -/
theorem ae_latWinFreeI_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    (hι : ∀ i, IsAdmissibleH (ι i)) {a : ℝ} (ha : 0 < a) (i : I)
    (hE : ∀ᵐ ω ∂P, evalReg (X ω) ((ι i).map fun z => (a : ℂ) * z) =
      X ω ((ι i).map fun z => (a : ℂ) * z)) :
    ∀ᵐ ω ∂P, latWinFreeI ι a X ω i = gaussFam X (pairMul hι ha) i ω := by
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  have hμ := hι i
  have : IsFiniteMeasure (ι i) := hμ.1
  have hne : ∀ᵐ z ∂(ι i), z ≠ 0 := by
    rw [ae_iff]; simpa using noAtoms_of_isAdmissibleH hμ 0
  filter_upwards [hG.ae_good, hE, ae_integral_radial hX hG (isAdmissibleH_map_mul ha hμ)]
    with ω hg h1 h2
  have hrad : ∫ z, radAvgReg (X ω) (a * ‖z‖) ∂(ι i) =
      X ω (radSmear ((ι i).map fun u => (a : ℂ) * u)) := by
    rw [integral_congr_ae (hne.mono fun z hz =>
      hg.radAvgReg_eq (mul_pos ha (norm_pos_iff.2 hz))), ← h2.2,
      integral_map (measurable_mul_left' a).aemeasurable h2.1.aestronglyMeasurable]
    congr 1
    funext z
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
  simp only [latWinFreeI, gaussFam, pairMul]
  rw [h1, hrad]

/-- Wedge-side window: a.s. the Gaussian pair difference at the undilated pair. -/
theorem ae_latFreeI_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    (hι : ∀ i, IsAdmissibleH (ι i)) (i : I)
    (hE : ∀ᵐ ω ∂P, evalReg (X ω) (ι i) = X ω (ι i)) :
    ∀ᵐ ω ∂P, latFreeI ι X ω i = gaussFam X (pairId hι) i ω := by
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  exact ae_lateral_X hX hG (hι i) hE

/-- **Free-field half of N2-H2 on a regular window family**: for every `a > 0`, the rescaled
lateral window of a free field `X` has the law of the plain lateral window of any free field
`X''`. -/
theorem map_latWinFreeI_eq (hι : WinRegFam ι) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    {Ω'' : Type} [MeasurableSpace Ω''] {P'' : Measure Ω''} [IsProbabilityMeasure P'']
    {X'' : Ω'' → FieldSample} (hX'' : IsFreeGFFModConstH X'' P'') {a : ℝ} (ha : 0 < a) :
    P.map (latWinFreeI ι a X) = P''.map (latFreeI ι X'') := by
  have hE'' : ∀ i, ∀ᵐ ω ∂P'', evalReg (X'' ω) (ι i) = X'' ω (ι i) := by
    intro i
    have h := hι.2 P'' X'' hX'' 1 one_pos i
    have e : ((ι i).map fun z => ((1 : ℝ) : ℂ) * z) = ι i := by
      have h1 : (fun z : ℂ => ((1 : ℝ) : ℂ) * z) = id := by funext z; simp
      rw [h1, Measure.map_id]
    rwa [e] at h
  calc P.map (latWinFreeI ι a X)
      = P.map (fun ω i => gaussFam X (pairMul hι.1 ha) i ω) :=
        UnzipInvariance.map_eq_of_forall_ae_eq (measurable_latWinFreeI hι.1 hX.measurable_coord a)
          (measurable_gaussFam_pi hX _)
          (fun i => ae_latWinFreeI_eq hX hι.1 ha i (hι.2 P X hX a ha i))
    _ = P.map (fun ω i => gaussFam X (pairId hι.1) i ω) :=
        map_gaussFam_eq hX _ _ (kernelCov2_pairMul hι.1 ha)
    _ = P''.map (fun ω i => gaussFam X'' (pairId hι.1) i ω) :=
        WedgeRes.map_gaussFam_eq₂ hX hX'' _
    _ = P''.map (latFreeI ι X'') :=
        (UnzipInvariance.map_eq_of_forall_ae_eq (measurable_latFreeI hι.1 hX''.measurable_coord)
          (measurable_gaussFam_pi hX'' _) fun i => ae_latFreeI_eq hX'' hι.1 i (hE'' i)).symm

/-- Folded circles `foldedCircle d s` (`s > 0`) form a regular window family. -/
theorem winRegFam_foldedCircle :
    WinRegFam (fun p : {p : ℂ × ℝ // 0 < p.2} => foldedCircle p.1.1 p.1.2) := by
  refine ⟨fun p => isAdmissibleH_foldedCircle' _ p.2, ?_⟩
  intro Ω _ P _ X hX b hb p
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  rw [fc_map_mul _ _ hb]
  exact ae_evalReg_fc hG _ (mul_pos hb p.2)

/-- Bounded continuous densities with compact support off the real line (`CharFun.Dens`) form a
regular window family (`WedgeTK.isGoodSC_map_mul`, `Regularization.ae_evalReg_eq_of_good`). -/
theorem winRegFam_tdens :
    WinRegFam (fun a : {a : ℂ → ℝ // ∃ K M δ, CharFun.Dens a K M δ} => CharFun.tdens a.1) := by
  refine ⟨fun a => ?_, ?_⟩
  · obtain ⟨K, M, δ, hd⟩ := a.2
    exact hd.admissible
  intro Ω _ P _ X hX b hb a
  obtain ⟨K, M, δ, hd⟩ := a.2
  obtain ⟨M', R', δ', hδ', hgood, him⟩ := isGoodSC_map_mul hd hb
  exact Regularization.ae_evalReg_eq_of_good hX hδ' hgood him

/-- Regular window families are stable under reindexing (e.g. restriction to the window). -/
theorem WinRegFam.comp {J : Type*} (hι : WinRegFam ι) (f : J → I) : WinRegFam (ι ∘ f) :=
  ⟨fun j => hι.1 (f j), fun P _ X hX b hb j => hι.2 P X hX b hb (f j)⟩

/-- Regular window families are stable under disjoint unions (circles ⊔ densities). -/
theorem WinRegFam.sum {J : Type*} {κ : J → Measure ℂ} (hι : WinRegFam ι) (hκ : WinRegFam κ) :
    WinRegFam (Sum.elim ι κ) := by
  refine ⟨fun i => ?_, fun P _ X hX b hb i => ?_⟩
  · rcases i with i | j
    · exact hι.1 i
    · exact hκ.1 j
  · rcases i with i | j
    · exact hι.2 P X hX b hb i
    · exact hκ.2 P X hX b hb j

end N2H2Law
end D3Plus
end QuantumZipper
