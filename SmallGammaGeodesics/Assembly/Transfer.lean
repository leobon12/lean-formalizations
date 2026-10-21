import SmallGammaGeodesics.Core.Setup
import SmallGammaGeodesics.Core.PathFunctionals
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Transfer of the main conclusions between realizations (final assembly, packet F1)

The conclusions of Theorems 1.1 and 1.2 for a random family of paths `η` depend, for each `γ`, only on
the law of `η γ`. For a strong γ-LQG metric family and the normalized whole-plane GFF, that law is
the same for every realization of the field (`map_geod_eq`), and a strong family has a.s. the same
geodesics as a canonical one (`exists_canonical_family`). Hence the frozen statements follow from the
internal ones, proved for the canonical family on GaussianLQG's coordinate space (`GSetup`).

`DevConcl` and `TightConcl` are, verbatim, the conclusions of the frozen anchors `deviation_scale`
and `functional_tightness`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

open LQGMetric GaussianLQG

/-- The conclusion of Theorem 1.1, (1.4)–(1.9), for a random family of paths `η` (verbatim the
conclusion of the frozen `deviation_scale`). -/
def DevConcl {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (η : ℝ → Ω → C(unitInterval, ℂ)) :
    Prop :=
  ∃ C γ₀ : ℝ, 0 < γ₀ ∧
      -- (1.4)
      (∀ γ ∈ Ioo (0 : ℝ) γ₀,
        ∫⁻ ω, ENNReal.ofReal (maxDev (η γ ω)) ∂P ≤ ENNReal.ofReal (C * γ ^ (2 / 3 : ℝ))) ∧
      -- (1.5)
      (∀ A : ℝ, 1 ≤ A → ∀ ε : ℝ, 0 < ε → ∀ᶠ γ in 𝓝[>] (0 : ℝ),
        P {ω | A * γ ^ (2 / 3 : ℝ) < maxDev (η γ ω)} ≤
          ENNReal.ofReal (C * (A ^ (-3 : ℝ) + A ^ (-4 : ℝ)) + ε)) ∧
      -- (1.6)
      (∀ γ ∈ Ioo (0 : ℝ) γ₀, ∀ a ∈ Ioc (0 : ℝ) 1,
        P {ω | maxDev (η γ ω) ≤ a * γ ^ (2 / 3 : ℝ)} ≤ ENNReal.ofReal (C * a ^ (3 / 5 : ℝ))) ∧
      -- (1.7)
      (∀ ε : ℝ, 0 < ε → ∃ a A : ℝ, 0 < a ∧ ∀ᶠ γ in 𝓝[>] (0 : ℝ),
        P {ω | ¬ (a ≤ maxDev (η γ ω) / γ ^ (2 / 3 : ℝ) ∧
          maxDev (η γ ω) / γ ^ (2 / 3 : ℝ) ≤ A)} ≤ ENNReal.ofReal ε) ∧
      -- (1.8)
      (∀ r ∈ Ioo (0 : ℝ) (3 / 5), ∃ K : ℝ, ∀ γ ∈ Ioo (0 : ℝ) γ₀,
        ∫⁻ ω, ENNReal.ofReal (maxDev (η γ ω) / γ ^ (2 / 3 : ℝ)) ^ (-r) ∂P ≤ ENNReal.ofReal K) ∧
      -- (1.9)
      (∀ ε : ℝ, 0 < ε → Tendsto (fun γ : ℝ => P {ω | ¬ (γ ^ (2 / 3 + ε) ≤ maxDev (η γ ω) ∧
          maxDev (η γ ω) ≤ γ ^ (2 / 3 - ε))}) (𝓝[>] 0) (𝓝 0))

/-- The conclusion of Theorem 1.2 for a random family of paths `η` (verbatim the conclusion of the
frozen `functional_tightness`). -/
def TightConcl {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (η : ℝ → Ω → C(unitInterval, ℂ)) :
    Prop :=
  (∀ γ, 0 < γ → γ < 2 →
      AEMeasurable (fun ω => rescaledPath (γ ^ (2 / 3 : ℝ)) (η γ ω)) P) ∧
    (∀ ε : ℝ, 0 < ε → ∃ K : Set C(unitInterval, ℂ), IsCompact K ∧ ∀ᶠ γ in 𝓝[>] (0 : ℝ),
      P {ω | rescaledPath (γ ^ (2 / 3 : ℝ)) (η γ ω) ∉ K} ≤ ENNReal.ofReal ε) ∧
    TendstoInMeasure P (fun γ ω => horizDev (γ ^ (2 / 3 : ℝ)) (η γ ω)) (𝓝[>] 0) (fun _ => 0)

/-! ### Path functionals: continuity -/

theorem bddAbove_horiz (η : C(unitInterval, ℂ)) :
    BddAbove (range fun t : unitInterval => |(η t).re - (t : ℝ)|) :=
  (isCompact_range (by fun_prop : Continuous fun t : unitInterval => |(η t).re - (t : ℝ)|)).bddAbove

/-- `sup_t |Re η(t) − t|` is 1-Lipschitz in `η`. -/
theorem iSup_horiz_le_add (η η' : C(unitInterval, ℂ)) :
    (⨆ t : unitInterval, |(η t).re - (t : ℝ)|) ≤
      (⨆ t : unitInterval, |(η' t).re - (t : ℝ)|) + dist η η' := by
  refine ciSup_le fun t => ?_
  have h1 : |(η t).re - (t : ℝ)| ≤ |(η' t).re - (t : ℝ)| + dist (η t) (η' t) := by
    have hre : |(η t).re - (η' t).re| ≤ dist (η t) (η' t) := by
      rw [Complex.dist_eq, ← Complex.sub_re]; exact Complex.abs_re_le_norm _
    calc |(η t).re - (t : ℝ)| = |((η t).re - (η' t).re) + ((η' t).re - (t : ℝ))| := by ring_nf
      _ ≤ |(η t).re - (η' t).re| + |(η' t).re - (t : ℝ)| := abs_add_le _ _
      _ ≤ _ := by linarith
  calc |(η t).re - (t : ℝ)| ≤ |(η' t).re - (t : ℝ)| + dist (η t) (η' t) := h1
    _ ≤ _ := add_le_add (le_ciSup (bddAbove_horiz η') t) (ContinuousMap.dist_apply_le_dist t)

theorem continuous_iSup_horiz :
    Continuous fun η : C(unitInterval, ℂ) => ⨆ t : unitInterval, |(η t).re - (t : ℝ)| :=
  (LipschitzWith.of_le_add iSup_horiz_le_add).continuous

theorem horizDev_eq_div {s : ℝ} (hs : 0 < s) (η : C(unitInterval, ℂ)) :
    horizDev s η = (⨆ t : unitInterval, |(η t).re - (t : ℝ)|) / s := by
  unfold horizDev
  simp_rw [div_eq_mul_inv]
  exact (Real.iSup_mul_of_nonneg (inv_nonneg.2 hs.le) _).symm

theorem continuous_horizDev {s : ℝ} (hs : 0 < s) : Continuous (horizDev s) := by
  have : horizDev s = fun η => (⨆ t : unitInterval, |(η t).re - (t : ℝ)|) / s :=
    funext (horizDev_eq_div hs)
  rw [this]
  exact continuous_iSup_horiz.div_const s

/-! ### Law transfer -/

section Law

variable {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
  {f : Ω → C(unitInterval, ℂ)} {f' : Ω' → C(unitInterval, ℂ)}

theorem measure_preimage_eq_of_map_eq (hf : AEMeasurable f P) (hf' : AEMeasurable f' P')
    (hmap : P.map f = P'.map f') {B : Set C(unitInterval, ℂ)} (hB : MeasurableSet B) :
    P (f ⁻¹' B) = P' (f' ⁻¹' B) := by
  rw [← Measure.map_apply_of_aemeasurable hf hB, ← Measure.map_apply_of_aemeasurable hf' hB, hmap]

theorem lintegral_comp_eq_of_map_eq (hf : AEMeasurable f P) (hf' : AEMeasurable f' P')
    (hmap : P.map f = P'.map f') {F : C(unitInterval, ℂ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (f ω) ∂P = ∫⁻ ω, F (f' ω) ∂P' := by
  rw [← lintegral_map' hF.aemeasurable hf, ← lintegral_map' hF.aemeasurable hf', hmap]

end Law

/-- Shrinking `γ₀` preserves the clauses of `DevConcl`; we only use the law of `η γ` for
`γ ∈ (0, 1)`. -/
theorem devConcl_of_map_eq {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {η : ℝ → Ω → C(unitInterval, ℂ)} {η' : ℝ → Ω' → C(unitInterval, ℂ)}
    (hη : ∀ γ, 0 < γ → γ < 2 → AEMeasurable (η γ) P)
    (hη' : ∀ γ, 0 < γ → γ < 2 → AEMeasurable (η' γ) P')
    (hmap : ∀ γ, 0 < γ → γ < 2 → P.map (η γ) = P'.map (η' γ)) :
    DevConcl P' η' → DevConcl P η := by
  rintro ⟨C, γ₀, hγ₀, h14, h15, h16, h17, h18, h19⟩
  have hsmall : ∀ γ ∈ Ioo (0 : ℝ) (min γ₀ 1), 0 < γ ∧ γ < 2 ∧ γ ∈ Ioo (0 : ℝ) γ₀ := by
    intro γ hγ
    exact ⟨hγ.1, by linarith [hγ.2.trans_le (min_le_right _ _)],
      ⟨hγ.1, hγ.2.trans_le (min_le_left _ _)⟩⟩
  have hev : ∀ᶠ γ in 𝓝[>] (0 : ℝ), 0 < γ ∧ γ < 2 :=
    Filter.eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 2)) fun γ hγ => ⟨hγ.1, hγ.2⟩
  have hM : Continuous maxDev := lipschitzWith_maxDev.continuous
  -- the probability of `{maxDev ∈ S}` for a Borel `S ⊆ ℝ` is a function of the law
  have hP : ∀ γ, 0 < γ → γ < 2 → ∀ S : Set ℝ, MeasurableSet S →
      P {ω | maxDev (η γ ω) ∈ S} = P' {ω | maxDev (η' γ ω) ∈ S} := fun γ h0 h2 S hS =>
    measure_preimage_eq_of_map_eq (hη γ h0 h2) (hη' γ h0 h2) (hmap γ h0 h2)
      (hM.measurable hS)
  refine ⟨C, min γ₀ 1, lt_min hγ₀ one_pos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1.4)
    intro γ hγ
    obtain ⟨h0, h2, hγ'⟩ := hsmall γ hγ
    rw [lintegral_comp_eq_of_map_eq (F := fun x => ENNReal.ofReal (maxDev x)) (hη γ h0 h2)
      (hη' γ h0 h2) (hmap γ h0 h2) (ENNReal.measurable_ofReal.comp hM.measurable)]
    exact h14 γ hγ'
  · -- (1.5)
    intro A hA ε hε
    filter_upwards [h15 A hA ε hε, hev] with γ hγ hγ2
    rw [show {ω | A * γ ^ (2 / 3 : ℝ) < maxDev (η γ ω)} =
        {ω | maxDev (η γ ω) ∈ Ioi (A * γ ^ (2 / 3 : ℝ))} from rfl,
      hP γ hγ2.1 hγ2.2 _ measurableSet_Ioi]
    exact hγ
  · -- (1.6)
    intro γ hγ a ha
    obtain ⟨h0, h2, hγ'⟩ := hsmall γ hγ
    rw [show {ω | maxDev (η γ ω) ≤ a * γ ^ (2 / 3 : ℝ)} =
        {ω | maxDev (η γ ω) ∈ Iic (a * γ ^ (2 / 3 : ℝ))} from rfl,
      hP γ h0 h2 _ measurableSet_Iic]
    exact h16 γ hγ' a ha
  · -- (1.7)
    intro ε hε
    obtain ⟨a, A, ha, hev'⟩ := h17 ε hε
    refine ⟨a, A, ha, ?_⟩
    filter_upwards [hev', hev] with γ hγ hγ2
    have hS : MeasurableSet {x : ℝ | ¬ (a ≤ x / γ ^ (2 / 3 : ℝ) ∧ x / γ ^ (2 / 3 : ℝ) ≤ A)} :=
      (measurableSet_le measurable_const (measurable_id.div_const _)).inter
        (measurableSet_le (measurable_id.div_const _) measurable_const) |>.compl
    rw [show {ω | ¬ (a ≤ maxDev (η γ ω) / γ ^ (2 / 3 : ℝ) ∧
        maxDev (η γ ω) / γ ^ (2 / 3 : ℝ) ≤ A)} =
        {ω | maxDev (η γ ω) ∈ {x : ℝ | ¬ (a ≤ x / γ ^ (2 / 3 : ℝ) ∧ x / γ ^ (2 / 3 : ℝ) ≤ A)}}
        from rfl, hP γ hγ2.1 hγ2.2 _ hS]
    exact hγ
  · -- (1.8)
    intro r hr
    obtain ⟨K, hK⟩ := h18 r hr
    refine ⟨K, fun γ hγ => ?_⟩
    obtain ⟨h0, h2, hγ'⟩ := hsmall γ hγ
    have hF : Measurable fun x : C(unitInterval, ℂ) =>
        ENNReal.ofReal (maxDev x / γ ^ (2 / 3 : ℝ)) ^ (-r) :=
      (ENNReal.measurable_ofReal.comp (hM.measurable.div_const _)).pow_const _
    rw [lintegral_comp_eq_of_map_eq (hη γ h0 h2) (hη' γ h0 h2) (hmap γ h0 h2) hF]
    exact hK γ hγ'
  · -- (1.9)
    intro ε hε
    refine (h19 ε hε).congr' ?_
    filter_upwards [hev] with γ hγ2
    have hS : MeasurableSet {x : ℝ | ¬ (γ ^ (2 / 3 + ε) ≤ x ∧ x ≤ γ ^ (2 / 3 - ε))} :=
      (measurableSet_Ici.inter measurableSet_Iic).compl
    exact (hP γ hγ2.1 hγ2.2 _ hS).symm

theorem tightConcl_of_map_eq {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {η : ℝ → Ω → C(unitInterval, ℂ)} {η' : ℝ → Ω' → C(unitInterval, ℂ)}
    (hη : ∀ γ, 0 < γ → γ < 2 → AEMeasurable (η γ) P)
    (hη' : ∀ γ, 0 < γ → γ < 2 → AEMeasurable (η' γ) P')
    (hmap : ∀ γ, 0 < γ → γ < 2 → P.map (η γ) = P'.map (η' γ)) :
    TightConcl P' η' → TightConcl P η := by
  rintro ⟨-, hK, hT⟩
  have hev : ∀ᶠ γ in 𝓝[>] (0 : ℝ), 0 < γ ∧ γ < 2 :=
    Filter.eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 2)) fun γ hγ => ⟨hγ.1, hγ.2⟩
  refine ⟨fun γ h0 h2 => (continuous_rescaledPath _).measurable.comp_aemeasurable (hη γ h0 h2),
    fun ε hε => ?_, fun ε hε => ?_⟩
  · obtain ⟨K, hKc, hev'⟩ := hK ε hε
    refine ⟨K, hKc, ?_⟩
    filter_upwards [hev', hev] with γ hγ hγ2
    have hB : MeasurableSet ((rescaledPath (γ ^ (2 / 3 : ℝ))) ⁻¹' Kᶜ) :=
      (continuous_rescaledPath _).measurable hKc.isClosed.measurableSet.compl
    rw [show {ω | rescaledPath (γ ^ (2 / 3 : ℝ)) (η γ ω) ∉ K} =
        η γ ⁻¹' ((rescaledPath (γ ^ (2 / 3 : ℝ))) ⁻¹' Kᶜ) from rfl,
      measure_preimage_eq_of_map_eq (hη γ hγ2.1 hγ2.2) (hη' γ hγ2.1 hγ2.2) (hmap γ hγ2.1 hγ2.2) hB]
    exact hγ
  · refine (hT ε hε).congr' ?_
    filter_upwards [hev] with γ hγ2
    have hs : 0 < γ ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hγ2.1 _
    have hB : MeasurableSet ((fun x => horizDev (γ ^ (2 / 3 : ℝ)) x) ⁻¹' {y : ℝ | ε ≤ edist y 0}) :=
      (continuous_horizDev hs).measurable (measurableSet_le measurable_const
        (measurable_id.edist measurable_const))
    exact (measure_preimage_eq_of_map_eq (hη γ hγ2.1 hγ2.2) (hη' γ hγ2.1 hγ2.2)
      (hmap γ hγ2.1 hγ2.2) hB).symm

end SmallGammaGeodesics
