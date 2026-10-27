import MatedCRTHarmonic.GMS4b.L46TShift
import MatedCRTHarmonic.GMS4b.L46TPhase
import MatedCRTHarmonic.GMS4c.Transfer

/-!
# Hölder transfer of localized bad events

The gamma-cone estimate is transferred only through events reconstructed
from the restricted field pair and the common imaginary-geometry phase.
The source and target event identities are
The missing measurable conclusion of [18, Lemma 4.3].
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4b

/-- The localized inner-degree failure on a spatial test region. -/
def l46tInnerBad {Ω : Type*} (c : Ω → ℝ → ℂ) (S : Set ℂ)
    (ε : ℝ) (k : ℕ) (ζ : ℝ) : Set Ω :=
  {ω | ∃ z ∈ S,
    ENNReal.ofReal (Real.log ε⁻¹ ^ ((k : ℝ) * (1 + ζ) + 1)) <
      ((degreeIn ε (c ω) z : ℕ∞) : ℝ≥0∞)}

/-- Failure of the localization event for the degree ball. -/
def l46tEscapeBad {Ω : Type*} (c : Ω → ℝ → ℂ) (S U : Set ℂ)
    (ε : ℝ) : Set Ω :=
  {ω | ∃ t : ℝ, c ω t ∈ S ∧ ¬ locBall ε (c ω) t ⊆ U}

/-- The still-open measurable part of [18, Lemma 4.3], in the exact form
needed by the two applications of `local_configuration_badEvent_le_holder`.
It reconstructs the escape event and the inner-degree failure on its
complement, under both specified field laws. -/
structure L46TLocalReconstruction {Ωγ Ω₀ : Type*}
    [MeasurableSpace Ωγ] [MeasurableSpace Ω₀]
    (V U : TopologicalSpace.Opens ℂ)
    (Pγ : Measure Ωγ) (P₀ : Measure Ω₀)
    (hγ hIGγ : Ωγ → LQGMetric.DistC) (uγ : Ωγ → ℝ)
    (h₀ hIG₀ : Ω₀ → LQGMetric.DistC) (u₀ : Ω₀ → ℝ)
    (cγ : Ωγ → ℝ → ℂ) (c₀ : Ω₀ → ℝ → ℂ)
    (S : Set ℂ) (ε : ℝ) (k : ℕ) (ζ : ℝ) : Type where
  reconstruct : L46TLocalFieldPhase V → GMS4c.LocalConfiguration U
  reconstruct_measurable : Measurable reconstruct
  escapeBad : Set (GMS4c.LocalConfiguration U)
  escapeBad_measurable : MeasurableSet escapeBad
  innerBad : Set (GMS4c.LocalConfiguration U)
  innerBad_measurable : MeasurableSet innerBad
  gamma_escape : l46tEscapeBad cγ S U ε =ᵐ[Pγ]
    {ω | reconstruct (l46tLocalFieldPhase V hγ hIGγ uγ ω) ∈ escapeBad}
  target_escape : l46tEscapeBad c₀ S U ε =ᵐ[P₀]
    {ω | reconstruct (l46tLocalFieldPhase V h₀ hIG₀ u₀ ω) ∈ escapeBad}
  gamma_inner : (l46tInnerBad cγ S ε k ζ ∩ (l46tEscapeBad cγ S U ε)ᶜ) =ᵐ[Pγ]
    {ω | reconstruct (l46tLocalFieldPhase V hγ hIGγ uγ ω) ∈ innerBad}
  target_inner : (l46tInnerBad c₀ S ε k ζ ∩ (l46tEscapeBad c₀ S U ε)ᶜ) =ᵐ[P₀]
    {ω | reconstruct (l46tLocalFieldPhase V h₀ hIG₀ u₀ ω) ∈ innerBad}

/-- The same local configuration and bad-event sets apply after replacing
either field/phase observation by an a.e.-equal representative. -/
def l46t_localReconstruction_congr
    {Ωγ Ω₀ : Type*} [MeasurableSpace Ωγ] [MeasurableSpace Ω₀]
    {V U : TopologicalSpace.Opens ℂ}
    {Pγ : Measure Ωγ} {P₀ : Measure Ω₀}
    {hγ hIGγ : Ωγ → LQGMetric.DistC} {uγ : Ωγ → ℝ}
    {h₀ hIG₀ : Ω₀ → LQGMetric.DistC} {u₀ : Ω₀ → ℝ}
    {hγ' hIGγ' : Ωγ → LQGMetric.DistC} {uγ' : Ωγ → ℝ}
    {h₀' hIG₀' : Ω₀ → LQGMetric.DistC} {u₀' : Ω₀ → ℝ}
    {cγ : Ωγ → ℝ → ℂ} {c₀ : Ω₀ → ℝ → ℂ}
    {S : Set ℂ} {ε : ℝ} {k : ℕ} {ζ : ℝ}
    (hlocal : L46TLocalReconstruction V U Pγ P₀
      hγ hIGγ uγ h₀ hIG₀ u₀ cγ c₀ S ε k ζ)
    (hs : l46tLocalFieldPhase V hγ' hIGγ' uγ' =ᵐ[Pγ]
      l46tLocalFieldPhase V hγ hIGγ uγ)
    (ht : l46tLocalFieldPhase V h₀' hIG₀' u₀' =ᵐ[P₀]
      l46tLocalFieldPhase V h₀ hIG₀ u₀) :
    L46TLocalReconstruction V U Pγ P₀
      hγ' hIGγ' uγ' h₀' hIG₀' u₀' cγ c₀ S ε k ζ := by
  refine ⟨hlocal.reconstruct, hlocal.reconstruct_measurable,
    hlocal.escapeBad, hlocal.escapeBad_measurable,
    hlocal.innerBad, hlocal.innerBad_measurable, ?_, ?_, ?_, ?_⟩
  · refine hlocal.gamma_escape.trans ?_
    filter_upwards [hs] with ω hω
    simpa only [hω]
  · refine hlocal.target_escape.trans ?_
    filter_upwards [ht] with ω hω
    simpa only [hω]
  · refine hlocal.gamma_inner.trans ?_
    filter_upwards [hs] with ω hω
    simpa only [hω]
  · refine hlocal.target_inner.trans ?_
    filter_upwards [ht] with ω hω
    simpa only [hω]

/-- The two applications of (4.16): one for localization and one for the
inner-degree failure where localization holds. -/
theorem l46t_innerBad_le_holder {Ωγ Ω₀ : Type*}
    [MeasurableSpace Ωγ] [MeasurableSpace Ω₀]
    {V U : TopologicalSpace.Opens ℂ}
    {Pγ : Measure Ωγ} {P₀ : Measure Ω₀}
    {hγ hIGγ : Ωγ → LQGMetric.DistC} {uγ : Ωγ → ℝ}
    {h₀ hIG₀ : Ω₀ → LQGMetric.DistC} {u₀ : Ω₀ → ℝ}
    {cγ : Ωγ → ℝ → ℂ} {c₀ : Ω₀ → ℝ → ℂ}
    {S : Set ℂ} {ε : ℝ} {k : ℕ} {ζ : ℝ} {p q : ℝ}
    (hcmp : L46TPhaseLawComparison V Pγ P₀ hγ hIGγ uγ h₀ hIG₀ u₀ p q)
    (hlocal : L46TLocalReconstruction V U Pγ P₀ hγ hIGγ uγ h₀ hIG₀ u₀
      cγ c₀ S ε k ζ) :
    P₀ (l46tInnerBad c₀ S ε k ζ) ≤
      (∫⁻ x, hcmp.density x ^ p
        ∂(Pγ.map (l46tLocalFieldPhase V hγ hIGγ uγ))) ^ (1 / p) *
        (Pγ (l46tEscapeBad cγ S U ε)) ^ (1 / q) +
      (∫⁻ x, hcmp.density x ^ p
        ∂(Pγ.map (l46tLocalFieldPhase V hγ hIGγ uγ))) ^ (1 / p) *
        (Pγ (l46tInnerBad cγ S ε k ζ)) ^ (1 / q) := by
  let K : ℝ≥0∞ :=
    (∫⁻ x, hcmp.density x ^ p
      ∂(Pγ.map (l46tLocalFieldPhase V hγ hIGγ uγ))) ^ (1 / p)
  have hesc := l46t_phase_badEvent_le_holder hcmp
    (hlocal.reconstruct_measurable hlocal.escapeBad_measurable)
  have hinn := l46t_phase_badEvent_le_holder hcmp
    (hlocal.reconstruct_measurable hlocal.innerBad_measurable)
  have hesc' : P₀ (l46tEscapeBad c₀ S U ε) ≤
      K * (Pγ (l46tEscapeBad cγ S U ε)) ^ (1 / q) := by
    rw [measure_congr hlocal.target_escape, measure_congr hlocal.gamma_escape]
    exact hesc
  have hinn' : P₀ (l46tInnerBad c₀ S ε k ζ ∩ (l46tEscapeBad c₀ S U ε)ᶜ) ≤
      K * (Pγ (l46tInnerBad cγ S ε k ζ)) ^ (1 / q) := by
    rw [measure_congr hlocal.target_inner]
    exact hinn.trans (by
      change K * (Pγ {ω | hlocal.reconstruct
        (l46tLocalFieldPhase V hγ hIGγ uγ ω) ∈ hlocal.innerBad}) ^ (1 / q) ≤
        K * (Pγ (l46tInnerBad cγ S ε k ζ)) ^ (1 / q)
      rw [← measure_congr hlocal.gamma_inner]
      gcongr
      · exact one_div_nonneg.mpr hcmp.conjugate.symm.pos.le
      · exact inter_subset_left)
  calc
    P₀ (l46tInnerBad c₀ S ε k ζ) ≤
        P₀ (l46tEscapeBad c₀ S U ε ∪
          (l46tInnerBad c₀ S ε k ζ ∩ (l46tEscapeBad c₀ S U ε)ᶜ)) :=
      measure_mono (by intro ω hω; by_cases he : ω ∈ l46tEscapeBad c₀ S U ε <;> simp [he, hω])
    _ ≤ P₀ (l46tEscapeBad c₀ S U ε) +
        P₀ (l46tInnerBad c₀ S ε k ζ ∩ (l46tEscapeBad c₀ S U ε)ᶜ) :=
      measure_union_le _ _
    _ ≤ K * (Pγ (l46tEscapeBad cγ S U ε)) ^ (1 / q) +
        K * (Pγ (l46tInnerBad cγ S ε k ζ)) ^ (1 / q) :=
      add_le_add hesc' hinn'

/-- A finite Hölder factor preserves a polynomial probability bound, dividing
The source exponent by its conjugate `q`. -/
theorem l46t_holder_power_bound (K : ℝ≥0∞) (hK : K < ⊤)
    (q C ε s : ℝ) (hq : 0 < q) (hε : 0 < ε) :
    K * (ENNReal.ofReal (C * ε ^ (q * s))) ^ (1 / q) ≤
      ENNReal.ofReal (K.toReal * (max C 0) ^ (1 / q) * ε ^ s) := by
  have hεpow : 0 ≤ ε ^ (q * s) := (Real.rpow_pos_of_pos hε _).le
  have hC : 0 ≤ max C 0 := le_max_right _ _
  have hmono : C * ε ^ (q * s) ≤ max C 0 * ε ^ (q * s) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hεpow
  have hreal : (max C 0 * ε ^ (q * s)) ^ (1 / q) =
      (max C 0) ^ (1 / q) * ε ^ s := by
    rw [Real.mul_rpow hC hεpow, ← Real.rpow_mul hε.le]
    congr 1
    field_simp
  calc
    K * (ENNReal.ofReal (C * ε ^ (q * s))) ^ (1 / q) ≤
        K * (ENNReal.ofReal (max C 0 * ε ^ (q * s))) ^ (1 / q) := by
          gcongr
    _ = ENNReal.ofReal (K.toReal * (max C 0) ^ (1 / q) * ε ^ s) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC hεpow) (one_div_nonneg.mpr hq.le), hreal]
      conv_lhs => rw [← ENNReal.ofReal_toReal hK.ne]
      rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      congr 1
      ring

/-- Pull back a field under the translation sending `z₀` to the cone root. -/
def l46tTranslatedField {Ω : Type*} (z₀ : ℂ)
    (h : Ω → LQGMetric.DistC) : Ω → LQGMetric.DistC :=
  fun ω => LQGMetric.affineComp 1 (-z₀) (h ω)

/-- Transferred Lemma 4.6 on one disk whose observation neighborhood
avoids the translated gamma-cone singularity. The only open inputs are
The actual local field comparison and the measurable Lemma 4.3
reconstruction. -/
theorem l46t_innerDegreeBound_disk_of_coupled_bound
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hS : Ω → LQGMetric.DistC) (uS : Ω → ℝ)
    (k : ℕ)
    (hpoly : InnerDegreeBoundPolylog (MoTInput.cellModelOfCoupling D hγ) (2 * k))
    (M₀ : GMSLemma27.CellModel γ) (hIGtarget : M₀.Ω → LQGMetric.DistC)
    (u₀ : M₀.Ω → ℝ)
    (z₀ w : ℂ) {ρ r R : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (hsub : ball w r ⊆ ball z₀ ρ) (hrR : r < R)
    (V : TopologicalSpace.Opens ℂ) {p q : ℝ}
    (hcmp : L46TPhaseLawComparison V P M₀.P
      (l46tTranslatedField z₀ hS) (l46tTranslatedField z₀ hIG₀) uS
      M₀.field hIGtarget u₀ p q)
    (hlocal : ∀ (k : ℕ) (ζ ε : ℝ), ε ∈ Ioo (0 : ℝ) 1 →
      L46TLocalReconstruction V ⟨ball w R, isOpen_ball⟩ P M₀.P
        (l46tTranslatedField z₀ hS) (l46tTranslatedField z₀ hIG₀) uS
        M₀.field hIGtarget u₀
        (fun ω => l46tTranslateCurve z₀ (η ω)) M₀.curve
        (ball w r) ε k ζ) :
    ∀ ζ ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
      ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
        M₀.P (l46tInnerBad M₀.curve (ball w r) ε (2 * k) ζ) ≤
          ENNReal.ofReal (C * ε ^ s) := by
  let Mγ := MoTInput.cellModelOfCoupling D hγ
  let _ : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hSLE : GMSLemma27.SegmentsContainBalls Mγ :=
    MoTInput.segmentsContainBalls_of_coupling D hγ
  have hGMC : GMSLemma27.GMCLowerTail γ :=
    GMCFacts.gmcLowerTail_holds hγ.1 hγ.2
  have hcone : GMCFacts.ConeAreaExists γ P X B B' :=
    GMCFacts.coneAreaExists_holds hγ.1 hγ.2 D.gff D.bm_B D.bm_B' D.indep_cone
  have hdom : GMSLemma27.AreaDominatesWholePlaneGFF Mγ :=
    MoTInput.areaDominatesWholePlaneGFF_of_coupling D hγ hcone
  intro ζ hζ s
  obtain ⟨Cdeg, hdeg⟩ := l46t_innerDegreeBoundPolylog_translate Mγ (2 * k)
    hpoly z₀ hρ hζ (q * s)
  obtain ⟨Cloc, hloc⟩ := l46t_localization_shifted_disk Mγ hγ.1
    hSLE hGMC hdom z₀ w hρ hsub hrR (q * s)
  let K : ℝ≥0∞ :=
    (∫⁻ x, hcmp.density x ^ p
      ∂(P.map (l46tLocalFieldPhase V (l46tTranslatedField z₀ hS)
        (l46tTranslatedField z₀ hIG₀) uS))) ^ (1 / p)
  have hK : K < ⊤ := l46t_phase_holder_constant_finite hcmp
  have hq : 0 < q := hcmp.conjugate.symm.pos
  let C : ℝ := K.toReal * (max Cloc 0) ^ (1 / q) +
    K.toReal * (max Cdeg 0) ^ (1 / q)
  refine ⟨C, fun ε hε => ?_⟩
  have hlocγ : P (l46tEscapeBad
      (fun ω => l46tTranslateCurve z₀ (η ω)) (ball w r) (ball w R) ε) ≤
      ENNReal.ofReal (Cloc * ε ^ (q * s)) := hloc ε hε
  have hdegγ : P (l46tInnerBad
      (fun ω => l46tTranslateCurve z₀ (η ω)) (ball w r) ε (2 * k) ζ) ≤
      ENNReal.ofReal (Cdeg * ε ^ (q * s)) := by
    refine (measure_mono ?_).trans (hdeg ε hε)
    rintro ω ⟨z, hz, hbad⟩
    exact ⟨z, hsub hz, hbad⟩
  have hholder := l46t_innerBad_le_holder hcmp (hlocal (2 * k) ζ ε hε)
  change M₀.P (l46tInnerBad M₀.curve (ball w r) ε (2 * k) ζ) ≤
    K * (P (l46tEscapeBad
      (fun ω => l46tTranslateCurve z₀ (η ω)) (ball w r) (ball w R) ε)) ^ (1 / q) +
    K * (P (l46tInnerBad
      (fun ω => l46tTranslateCurve z₀ (η ω)) (ball w r) ε (2 * k) ζ)) ^ (1 / q)
    at hholder
  calc
    M₀.P (l46tInnerBad M₀.curve (ball w r) ε (2 * k) ζ) ≤
        K * (P (l46tEscapeBad
          (fun ω => l46tTranslateCurve z₀ (η ω)) (ball w r) (ball w R) ε)) ^ (1 / q) +
        K * (P (l46tInnerBad
          (fun ω => l46tTranslateCurve z₀ (η ω)) (ball w r) ε (2 * k) ζ)) ^ (1 / q) := hholder
    _ ≤ K * (ENNReal.ofReal (Cloc * ε ^ (q * s))) ^ (1 / q) +
        K * (ENNReal.ofReal (Cdeg * ε ^ (q * s))) ^ (1 / q) := by
          gcongr
    _ ≤ ENNReal.ofReal (K.toReal * (max Cloc 0) ^ (1 / q) * ε ^ s) +
        ENNReal.ofReal (K.toReal * (max Cdeg 0) ^ (1 / q) * ε ^ s) :=
      add_le_add (l46t_holder_power_bound K hK q Cloc ε s hq hε.1)
        (l46t_holder_power_bound K hK q Cdeg ε s hq hε.1)
    _ = ENNReal.ofReal (C * ε ^ s) := by
      have h₁ : 0 ≤ K.toReal * (max Cloc 0) ^ (1 / q) * ε ^ s :=
        mul_nonneg (mul_nonneg ENNReal.toReal_nonneg
          (Real.rpow_nonneg (le_max_right _ _) _)) (Real.rpow_nonneg hε.1.le _)
      have h₂ : 0 ≤ K.toReal * (max Cdeg 0) ^ (1 / q) * ε ^ s :=
        mul_nonneg (mul_nonneg ENNReal.toReal_nonneg
          (Real.rpow_nonneg (le_max_right _ _) _)) (Real.rpow_nonneg hε.1.le _)
      rw [← ENNReal.ofReal_add h₁ h₂]
      congr 1
      dsimp [C]
      ring

/-- Each test disk lies inside the disk where L46S controls the translated
gamma-cone degree. The radii shrink near the unit-disk boundary. -/
private theorem l46t_testDisk_subset_sourceDisk {ρ : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (w : ℂ) :
    ball w ((1 - ρ) / 16) ⊆
      ball (w + ((1 - ρ) / 2 : ℝ)) (3 / 4 : ℝ) := by
  intro z hz
  have hzw : dist z w < (1 - ρ) / 16 := hz
  have hone : 0 ≤ 1 - ρ := by linarith [hρ.2]
  have hhalf : 0 ≤ (1 - ρ) / 2 := by linarith [hρ.2]
  have hw : dist w (w + ((1 - ρ) / 2 : ℝ)) = (1 - ρ) / 2 := by
    simp [dist_eq_norm]
    change ‖((1 : ℝ) : ℂ) - (ρ : ℂ)‖ = 1 - ρ
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hone]
  have htri := dist_triangle z w (w + ((1 - ρ) / 2 : ℝ))
  rw [Metric.mem_ball, hw] at *
  linarith [hρ.1]

/-- The actual source comparison disk lies a positive distance from the
translated gamma-cone singularity. -/
def l46tObservation (ρ : ℝ) (w : ℂ) : TopologicalSpace.Opens ℂ :=
  ⟨ball w ((1 - ρ) / 4), isOpen_ball⟩

/-- The disk in which Lemma 4.3 reconstructs localized degree data. -/
def l46tLocalRegion (ρ : ℝ) (w : ℂ) : TopologicalSpace.Opens ℂ :=
  ⟨ball w ((1 - ρ) / 8), isOpen_ball⟩

end MatedCRTHarmonic.GMS4b
