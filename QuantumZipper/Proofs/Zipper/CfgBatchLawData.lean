import QuantumZipper.Proofs.LQG.WedgeRestriction
import QuantumZipper.Proofs.Zipper.F1EmbedBasic
import QuantumZipper.Proofs.Zipper.F1Read
import QuantumZipper.Proofs.Zipper.B2Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CFG-BATCH-LAW, part 1: the configuration law of a normalized `Γ⁰` sample is universal

Theorem 1.3, node E6/LEN-INF (`E6.CfgNormLenLawStmt`, `LenInfCore.lean`); Sheffield,
arXiv:1012.4797, §5.1 (pp. 60–62) and §5.4 (pp. 70–72). The paper uses without proof that the law
of `(𝔥₀ + X, √κ B)` does not depend on the probability space. Here: for a free boundary GFF `X`
(modulo constants, `IsFreeGFFModConstH`) **normalized** by `X(ρ₁) = 0` (`ρ₁ = foldedCircle 0 1`),
independent of a standard Brownian motion `B`, the data law `configLawFull (cfg κ B X) P` is the
same on every probability space (`configLawFull_cfg_eq_of_normalized`).

Argument (own bookkeeping; no published proof — the paper states it implicitly):
* every coordinate read by `fieldLawFull H` (values at the dyadic folded circles and raw test
  pairings) is a.s. a balanced pair difference of `X` (`ae_ncoord_eq_gaussFam`): at a circle,
  `X(fcN n) = X(fcN n) − X(ρ₁)` by normalization; for a test function `ρ = ρ⁺ − ρ⁻` with masses
  `m±`, linearity gives `⟨X, ρ⟩ = X(ρ⁺ + m₋ ρ₁) − X(ρ⁻ + m₊ ρ₁)` (balanced, mass `m₊ + m₋`);
* the law of a Gaussian family of balanced differences depends only on the covariances
  (`WedgeRes.map_gaussFam_eq₂`), hence `fieldLawFull H X P` is universal;
* the deterministic `𝔥₀` shift, independence and the uniqueness of the Brownian path law
  (`F1.isProjectiveLimit_map_pathOf`) give the configuration law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace QuantumZipper.E6

open WedgeTK CharFun

/-- Mass of a test density part, as an `ℝ≥0`. -/
def tmass (a : ℂ → ℝ) : ℝ≥0 := (tdens a Set.univ).toNNReal

theorem admissible_fc01 : IsAdmissibleH (foldedCircle 0 1) :=
  isAdmissibleH_foldedCircle (by simp [Hbar]) one_pos

theorem admissible_tdens_pos (ρ : TestFun H) : IsAdmissibleH (tdens ρ.1) := by
  obtain ⟨M, δ, hd⟩ := CharFun.exists_dens ρ
  exact hd.admissible

theorem admissible_tdens_neg (ρ : TestFun H) : IsAdmissibleH (tdens fun z => -ρ.1 z) := by
  obtain ⟨M, δ, hd⟩ := CharFun.exists_dens ρ
  exact hd.neg.admissible

theorem tdens_univ_eq_tmass {a : ℂ → ℝ} (h : IsAdmissibleH (tdens a)) :
    tdens a Set.univ = (tmass a : ℝ≥0∞) := by
  have := h.1
  exact (ENNReal.coe_toNNReal (measure_ne_top _ _)).symm

theorem mass_add_smul_fc01 {a : ℂ → ℝ} (h : IsAdmissibleH (tdens a)) (m : ℝ≥0) :
    (tdens a + m • foldedCircle 0 1) Set.univ = (tmass a : ℝ≥0∞) + m := by
  rw [Measure.add_apply, Measure.smul_apply, tdens_univ_eq_tmass h,
    measure_univ (μ := foldedCircle 0 1)]
  simp

/-- The balanced pairs representing the normalized coordinates. -/
def normPair : LatIdx → BPair
  | .inl n => ⟨(fcN n, foldedCircle 0 1), fcN_admissible n, admissible_fc01, by
      simp only [fcN, measure_univ]⟩
  | .inr ρ => ⟨(tdens ρ.1 + tmass (fun z => -ρ.1 z) • foldedCircle 0 1,
      tdens (fun z => -ρ.1 z) + tmass ρ.1 • foldedCircle 0 1),
      isAdmissibleH_add (admissible_tdens_pos ρ)
        (isAdmissibleH_smul_nnreal' admissible_fc01 _),
      isAdmissibleH_add (admissible_tdens_neg ρ)
        (isAdmissibleH_smul_nnreal' admissible_fc01 _), by
      rw [mass_add_smul_fc01 (admissible_tdens_pos ρ), mass_add_smul_fc01 (admissible_tdens_neg ρ),
        add_comm]⟩
where
  isAdmissibleH_smul_nnreal' {μ : Measure ℂ} (hμ : IsAdmissibleH μ) (c : ℝ≥0) :
      IsAdmissibleH (c • μ) :=
    isAdmissibleH_smul (c := (c : ℝ≥0∞)) hμ ENNReal.coe_lt_top

/-- The coordinates read by `fieldLawFull H`, as one family over `LatIdx`. -/
def ncF (x : FieldSample) : LatIdx → ℝ :=
  Sum.elim (fun n => x (fcN n)) (fun ρ => pairRaw x ρ.1)

theorem measurable_ncF : Measurable ncF := by
  refine measurable_pi_iff.2 fun i => ?_
  rcases i with n | ρ
  · exact measurable_pi_apply _
  · exact (measurable_pi_apply _).sub (measurable_pi_apply _)

section Law

theorem measurable_ncF_comp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) : Measurable fun ω => ncF (X ω) :=
  measurable_ncF.comp (measurable_X_pi hX)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

omit [IsProbabilityMeasure P] in
/-- **Normalized coordinates are balanced pair differences** (a.s., coordinatewise). -/
theorem ae_ncF_eq_gaussFam (hX : IsFreeGFFModConstH X P)
    (hn : ∀ᵐ ω ∂P, X ω (foldedCircle 0 1) = 0) (i : LatIdx) :
    ∀ᵐ ω ∂P, ncF (X ω) i = gaussFam X normPair i ω := by
  rcases i with n | ρ
  · filter_upwards [hn] with ω h
    simp only [ncF, Sum.elim_inl, gaussFam, normPair, h, sub_zero]
  · have h1 := hX.linear _ _ (admissible_tdens_pos ρ) admissible_fc01 1
      (tmass fun z => -ρ.1 z)
    have h2 := hX.linear _ _ (admissible_tdens_neg ρ) admissible_fc01 1 (tmass ρ.1)
    filter_upwards [hn, h1, h2] with ω h h1 h2
    rw [one_smul] at h1 h2
    simp only [ncF, Sum.elim_inr, gaussFam, normPair]
    rw [h1, h2, h, pairRaw_eq_tdens]
    simp

theorem fieldLawFull_eq_map_ncF (hX : IsFreeGFFModConstH X P) :
    fieldLawFull H X P =
      (P.map fun ω => ncF (X ω)).map (MeasurableEquiv.sumPiEquivProdPi fun _ : LatIdx => ℝ) := by
  rw [Measure.map_map (MeasurableEquiv.sumPiEquivProdPi fun _ : LatIdx => ℝ).measurable
    (measurable_ncF_comp hX)]
  rfl

end Law

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {P₁ : Measure Ω₁}
  {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
  {X₁ : Ω₁ → FieldSample} {X₂ : Ω₂ → FieldSample}

/-- **The coordinate law of a normalized free field is universal.** -/
theorem map_ncF_eq_of_normalized (hX₁ : IsFreeGFFModConstH X₁ P₁)
    (hn₁ : ∀ᵐ ω ∂P₁, X₁ ω (foldedCircle 0 1) = 0) (hX₂ : IsFreeGFFModConstH X₂ P₂)
    (hn₂ : ∀ᵐ ω ∂P₂, X₂ ω (foldedCircle 0 1) = 0) :
    P₁.map (fun ω => ncF (X₁ ω)) = P₂.map (fun ω => ncF (X₂ ω)) := by
  rw [UnzipInvariance.map_eq_of_forall_ae_eq (measurable_ncF_comp hX₁)
      (measurable_gaussFam_pi hX₁ normPair) (ae_ncF_eq_gaussFam hX₁ hn₁),
    UnzipInvariance.map_eq_of_forall_ae_eq (measurable_ncF_comp hX₂)
      (measurable_gaussFam_pi hX₂ normPair) (ae_ncF_eq_gaussFam hX₂ hn₂)]
  exact WedgeRes.map_gaussFam_eq₂ hX₁ hX₂ normPair

/-- **The full field law of a normalized free field is universal.** -/
theorem fieldLawFull_eq_of_normalized (hX₁ : IsFreeGFFModConstH X₁ P₁)
    (hn₁ : ∀ᵐ ω ∂P₁, X₁ ω (foldedCircle 0 1) = 0) (hX₂ : IsFreeGFFModConstH X₂ P₂)
    (hn₂ : ∀ᵐ ω ∂P₂, X₂ ω (foldedCircle 0 1) = 0) :
    fieldLawFull H X₁ P₁ = fieldLawFull H X₂ P₂ := by
  rw [fieldLawFull_eq_map_ncF hX₁, fieldLawFull_eq_map_ncF hX₂,
    map_ncF_eq_of_normalized hX₁ hn₁ hX₂ hn₂]

/-! ## The configuration law -/

/-- The data of `cfg κ B X` rebuilt from the coordinates of `X` and the driving path: add the
deterministic coordinates of `𝔥₀`. -/
def shiftData (κ : ℝ) (q : (LatIdx → ℝ) × (ℝ≥0 → ℝ)) :
    ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) :=
  ((fun n => ofFun (h0rev κ) (fcN n) + q.1 (.inl n),
    fun ρ => pairRaw (ofFun (h0rev κ)) ρ.1 + q.1 (.inr ρ)), q.2)

theorem measurable_shiftData (κ : ℝ) : Measurable (shiftData κ) := by
  refine Measurable.prodMk (Measurable.prodMk ?_ ?_) measurable_snd
  · exact measurable_pi_iff.2 fun n =>
      measurable_const.add ((measurable_pi_apply _).comp measurable_fst)
  · exact measurable_pi_iff.2 fun ρ =>
      measurable_const.add ((measurable_pi_apply _).comp measurable_fst)

theorem cfgData_cfg_eq {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ω : Ω) :
    F1.cfgData (B2.cfg κ B X ω) = shiftData κ (ncF (X ω), F1.drivePath κ (pathOf B ω)) := by
  refine Prod.ext (Prod.ext (funext fun n => rfl) (funext fun ρ => ?_))
    (F1.drive_nnreal κ B ω)
  simp only [F1.cfgData, shiftData, B2.cfg, ncF, Sum.elim_inr, pairRaw, Pi.add_apply]
  ring

theorem configLawFull_cfg_eq_prod {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (κ : ℝ) {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    configLawFull (B2.cfg κ B X) P =
      ((P.map fun ω => ncF (X ω)).prod ((P.map (pathOf B)).map (F1.drivePath κ))).map
        (shiftData κ) := by
  have hBm := IsBrownianReal.aemeasurable_pathOf hB
  have hN : AEMeasurable (fun ω => ncF (X ω)) P :=
    (measurable_ncF_comp hX).aemeasurable
  have hD : AEMeasurable (fun ω => F1.drivePath κ (pathOf B ω)) P :=
    (F1.measurable_drivePath κ).comp_aemeasurable hBm
  have hI : IndepFun (fun ω => ncF (X ω)) (fun ω => F1.drivePath κ (pathOf B ω)) P :=
    hind.symm.comp measurable_ncF (F1.measurable_drivePath κ)
  have e : configLawFull (B2.cfg κ B X) P =
      (P.map fun ω => (ncF (X ω), F1.drivePath κ (pathOf B ω))).map (shiftData κ) := by
    rw [AEMeasurable.map_map_of_aemeasurable (measurable_shiftData κ).aemeasurable
      (hN.prodMk hD)]
    show P.map _ = _
    congr 1
    funext ω
    exact cfgData_cfg_eq κ B X ω
  rw [e, (indepFun_iff_map_prod_eq_prod_map_map hN hD).1 hI,
    AEMeasurable.map_map_of_aemeasurable (F1.measurable_drivePath κ).aemeasurable hBm]
  rfl

/-- **The configuration law of a normalized `Γ⁰` sample is universal.** -/
theorem configLawFull_cfg_eq_of_normalized (κ : ℝ) {B₁ : ℝ≥0 → Ω₁ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
    (hB₁ : IsBrownianReal B₁ P₁) (hX₁ : IsFreeGFFModConstH X₁ P₁)
    (hi₁ : IndepFun (pathOf B₁) X₁ P₁) (hn₁ : ∀ᵐ ω ∂P₁, X₁ ω (foldedCircle 0 1) = 0)
    (hB₂ : IsBrownianReal B₂ P₂) (hX₂ : IsFreeGFFModConstH X₂ P₂)
    (hi₂ : IndepFun (pathOf B₂) X₂ P₂) (hn₂ : ∀ᵐ ω ∂P₂, X₂ ω (foldedCircle 0 1) = 0) :
    configLawFull (B2.cfg κ B₁ X₁) P₁ = configLawFull (B2.cfg κ B₂ X₂) P₂ := by
  rw [configLawFull_cfg_eq_prod κ hB₁ hX₁ hi₁, configLawFull_cfg_eq_prod κ hB₂ hX₂ hi₂,
    map_ncF_eq_of_normalized hX₁ hn₁ hX₂ hn₂,
    (F1.isProjectiveLimit_map_pathOf hB₁.toIsPreBrownianReal
      (IsBrownianReal.aemeasurable_pathOf hB₁)).unique
    (F1.isProjectiveLimit_map_pathOf hB₂.toIsPreBrownianReal
      (IsBrownianReal.aemeasurable_pathOf hB₂))]

end QuantumZipper.E6
