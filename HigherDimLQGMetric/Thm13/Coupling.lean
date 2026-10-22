import HigherDimLQGMetric.Thm13.GoodEvent
import HigherDimLQGMetric.Sphere.Conv
import HigherDimLQGMetric.Field.Version
import HigherDimLQGMetric.LfppTight.LawInput
import LQGMetric.Papers.DFGPS.L2_17CoreC
import LQGMetric.Papers.DFGPS.L2_17CoreFM
import LQGMetric.Prob.PolishContinuousMap
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! A fixed-field-marginal subsequential coupling for MA5 A21(1). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal BoundedContinuousFunction

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The normalized LGF property transfers across equality of full field laws. -/
theorem l8_isNormalizedLGF_of_map_eq {d : ℕ}
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {h : Ω → DistRd d} {h' : Ω' → DistRd d}
    (hm : Measurable h) (hh' : IsNormalizedLGF h' P')
    (e : P.map h = P'.map h') : IsNormalizedLGF h P := by
  have hid : IsWholeSpaceLGF (id : DistRd d → DistRd d) (P.map h) := by
    rw [e]
    exact hh'.1.map_id
  refine ⟨⟨hm, ⟨fun I => ?_⟩, fun φ => ?_, fun φ ψ => ?_⟩, ?_⟩
  · have hF : Measurable fun g : DistRd d => I.restrict fun φ : TestRd0 d => g φ.1 :=
      measurable_pi_iff.2 fun _ => measurable_distOn_apply _
    refine ⟨(hF.comp hm).aemeasurable, ?_⟩
    have h1 : IsGaussian ((P.map h).map fun g : DistRd d =>
        I.restrict fun φ : TestRd0 d => g φ.1) :=
      (hid.gaussian.hasGaussianLaw I).isGaussian_map
    rw [Measure.map_map hF hm] at h1
    exact h1
  · have h1 : ∫ g, g φ.1 ∂(P.map h) = 0 := hid.centered φ
    rw [integral_map hm.aemeasurable
      (measurable_distOn_apply φ.1).aestronglyMeasurable] at h1
    exact h1
  · have h1 : cov[fun g : DistRd d => g φ.1,
        fun g : DistRd d => g ψ.1; P.map h] = logCovRd φ.1 ψ.1 :=
      hid.covariance_eq φ ψ
    rw [covariance_map (measurable_distOn_apply φ.1).aestronglyMeasurable
      (measurable_distOn_apply ψ.1).aestronglyMeasurable hm.aemeasurable] at h1
    exact h1
  · have hs : MeasurableSet {g : DistRd d | sphereAvg g 1 0 = 0} :=
      measurableSet_eq_fun (measurable_sphereAvg_left 1 0) measurable_const
    have h1 : ∀ᵐ g ∂(P.map h), sphereAvg g 1 0 = 0 := by
      rw [e]
      exact (ae_map_iff hh'.1.measurable.aemeasurable hs).2 hh'.2
    exact (ae_map_iff hm.aemeasurable hs).1 h1

/-- The fixed-marginal Prokhorov coupling, with the proper length support of
Lemma 3.1 taken in its current exact form until L6c's handoff is available. -/
theorem l8_exists_limit_coupling
    (hL6a : ∀ d ξ κ, L6a_tight d ξ κ)
    (hLen : (∀ d ξ κ, L6a_tight d ξ κ) → ∀ {d : ℕ} (ξ : ℝ) (κ : Rd d → ℝ)
      (_hB2 : ∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧
        DGZ.RealEpsAdapterShape d κ ξ Q)
      {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d),
      IsNormalizedLGF h P →
      ∀ μ : ProbabilityMeasure C(Rd d × Rd d, ℝ),
        μ ∈ closure {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
          ∃ ε ∈ Ioo (0 : ℝ) 1,
            (ν : Measure C(Rd d × Rd d, ℝ)) =
              P.map (fun ω => toCMapRd ((aEps κ ξ ε)⁻¹ •
                lfppDist κ ξ ε (h ω)))} →
        ∀ᵐ E ∂(μ : Measure C(Rd d × Rd d, ℝ)), IsContLengthFn E)
    {d : ℕ} (hd : 2 ≤ d) (ξ : ℝ) (κ : Rd d → ℝ)
    (hB2 : ∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (_ : IsProbabilityMeasure P) (h : Ω → DistRd d)
        (Dh : Ω → ContMetric d),
        IsNormalizedLGF h P ∧ Measurable Dh ∧
          (∀ᵐ ω ∂P, (Dh ω).IsLength ∧ IsProperFn (Dh ω).1) ∧
          StablyTendstoLU P h
            (fun n ω => lfppSeq κ ξ (εs ∘ φ) (h ω) n)
            (fun ω => (Dh ω).1) := by
  let μ : Measure (DistRd d) := normLGFLaw d
  letI : IsProbabilityMeasure μ := (normLGFLaw_spec_holds d hd).1
  have hhμ : IsNormalizedLGF (id : DistRd d → DistRd d) μ :=
    (normLGFLaw_spec_holds d hd).2.1
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    (hεt.eventually (gt_mem_nhds one_pos))
  have hεI (n : ℕ) : εs (n + N₀) ∈ Ioo (0 : ℝ) 1 :=
    ⟨hεs _, hN₀ _ (by omega)⟩
  have hAm (n : ℕ) : AEMeasurable
      (fun g : DistRd d => lfppSeq κ ξ εs g (n + N₀)) μ :=
    l6a_aemeasurable_normalized_lfpp hd κ
      (Classical.choose_spec hB2).1.kernel ξ (hεs _) μ id
      hhμ.1.isLGFPlusBddCont
  let Y : ℕ → DistRd d → C(Rd d × Rd d, ℝ) :=
    fun n => (hAm n).mk _
  have hYm : ∀ n, Measurable (Y n) := fun n => (hAm n).measurable_mk
  have hYe : ∀ n, (fun g : DistRd d => lfppSeq κ ξ εs g (n + N₀)) =ᵐ[μ] Y n :=
    fun n => (hAm n).ae_eq_mk
  have hAt : TightFamily μ
      (fun ε g => toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε g))
      (Ioo (0 : ℝ) 1) := (hL6a d ξ κ) hB2 μ id
        hhμ.1.isLGFPlusBddCont |>.2
  have hYt : IsTightMeasureSet (range fun n => μ.map (Y n)) := by
    refine hAt.2.1.subset ?_
    rintro ν ⟨n, rfl⟩
    exact ⟨εs (n + N₀), hεI n, (Measure.map_congr (hYe n)).symm⟩
  let X : DistRd d → CoordJ → ℝ := pairJ ⊤
  have hXm : Measurable X := measurable_pairJ ⊤
  letI : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable C(Rd d × Rd d, ℝ)
  letI : TopologicalSpace
      (ProbabilityMeasure C(Rd d × Rd d, ℝ)) := inferInstance
  obtain ⟨ψ, hψ, ρ, hlim, hmarg⟩ :=
    LQGMetric.DFGPS.L217.exists_limit_coupling (P := μ) hXm hYm hYt
  let S : Type := (CoordJ → ℝ) × C(Rd d × Rd d, ℝ)
  let H : S → DistRd d := fun q => pairJInv ⊤ q.1
  have hHm : Measurable H := (measurable_pairJInv ⊤).comp measurable_fst
  have hlawH : (ρ : Measure S).map H = μ := by
    rw [show H = pairJInv ⊤ ∘ Prod.fst from rfl,
      ← Measure.map_map (measurable_pairJInv ⊤) measurable_fst,
      hmarg, Measure.map_map (measurable_pairJInv ⊤) hXm]
    have heq : pairJInv ⊤ ∘ X = id := funext fun g => pairJInv_pairJ ⊤ g
    rw [heq, Measure.map_id]
  have hran : ∀ᵐ q ∂(ρ : Measure S), pairJ ⊤ (H q) = q.1 := by
    have hrs : MeasurableSet (range (pairJ (⊤ : TopologicalSpace.Opens (Rd d)))) :=
      measurableSet_range_pairJ ⊤
    have h1 : ∀ᵐ s ∂((ρ : Measure S).map Prod.fst),
        s ∈ range (pairJ (⊤ : TopologicalSpace.Opens (Rd d))) := by
      rw [hmarg]
      exact (ae_map_iff hXm.aemeasurable hrs).2
        (Eventually.of_forall fun g => ⟨g, rfl⟩)
    filter_upwards [ae_of_ae_map measurable_fst.aemeasurable h1] with q hq
    obtain ⟨T, hT⟩ := hq
    simp only [H, ← hT, pairJInv_pairJ]
  let νlim : ProbabilityMeasure C(Rd d × Rd d, ℝ) := ρ.map Prod.snd
  let νn : ℕ → ProbabilityMeasure C(Rd d × Rd d, ℝ) :=
    fun n => ⟨μ.map (Y (ψ n)), inferInstance⟩
  have hνlim : Tendsto
      νn atTop (𝓝 νlim) := by
    have ht := ((ProbabilityMeasure.continuous_map continuous_snd).tendsto ρ).comp hlim
    have heq : (fun n => ProbabilityMeasure.map
        (⟨μ.map (fun g => (X g, Y (ψ n) g)),
          inferInstance⟩ : ProbabilityMeasure S) (Prod.snd : S → _)) = νn := by
      funext n
      apply Subtype.ext
      change (μ.map (fun g => (X g, Y (ψ n) g))).snd = μ.map (Y (ψ n))
      exact Measure.snd_map_prodMk hXm (hYm (ψ n))
    exact heq ▸ ht
  have hνmem : νlim ∈ closure
      {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
        ∃ ε ∈ Ioo (0 : ℝ) 1,
          (ν : Measure C(Rd d × Rd d, ℝ)) =
            μ.map (fun g => toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε g))} := by
    apply mem_closure_of_tendsto hνlim
    exact Eventually.of_forall fun n =>
      ⟨εs (ψ n + N₀), hεI (ψ n), by
        change μ.map (Y (ψ n)) = μ.map (fun g => lfppSeq κ ξ εs g (ψ n + N₀))
        exact (Measure.map_congr (hYe (ψ n))).symm⟩
  have hproper : ∀ᵐ q ∂(ρ : Measure S),
      IsContinuousMetric q.2 ∧ IsProperFn q.2 := by
    have ha := hAt.2.2 νlim hνmem
    exact ae_of_ae_map measurable_snd.aemeasurable ha
  have hlength : ∀ᵐ q ∂(ρ : Measure S), IsContLengthFn q.2 := by
    have ha := hLen hL6a ξ κ hB2 μ id hhμ νlim hνmem
    exact ae_of_ae_map measurable_snd.aemeasurable ha
  let Dh : S → ContMetric d := fun q => l8_toContMetric q.2
  have hDhm : Measurable Dh := l8_measurable_toContMetric.comp measurable_snd
  have hgood : ∀ᵐ q ∂(ρ : Measure S),
      (Dh q).IsLength ∧ IsProperFn (Dh q).1 := by
    filter_upwards [hproper, hlength] with q hp hl
    have hDq : Dh q = ⟨q.2, hp.1⟩ := by
      apply Subtype.ext
      simp [Dh, l8_toContMetric, hp.1]
    rw [hDq]
    exact ⟨hl.choose_spec, hp.2⟩
  have hnorm : IsNormalizedLGF H (ρ : Measure S) :=
    l8_isNormalizedLGF_of_map_eq hHm hhμ (by rw [hlawH, Measure.map_id])
  refine ⟨fun n => ψ n + N₀, fun a b hab => by simpa using hψ hab,
    S, inferInstance, (ρ : Measure S), inferInstance, H, Dh,
    hnorm, hDhm, hgood, ?_⟩
  intro g hg hgb φ hφ hφb
  -- Fixed-marginal convergence of the joint laws upgrades continuous field
  -- tests to bounded measurable field tests.
  let Yc : ℕ → S → C(Rd d × Rd d, ℝ) := fun n q => Y (ψ n) (H q)
  have hYcm (n : ℕ) : Measurable (Yc n) := (hYm (ψ n)).comp hHm
  have hpre (n : ℕ) :
      (ρ : Measure S).map (fun q => (q.1, Yc n q)) =
        μ.map (fun k => (X k, Y (ψ n) k)) := by
    calc
      (ρ : Measure S).map (fun q => (q.1, Yc n q)) =
          (ρ : Measure S).map ((fun k => (X k, Y (ψ n) k)) ∘ H) := by
            apply Measure.map_congr
            filter_upwards [hran] with q hq
            exact Prod.ext hq.symm rfl
      _ = ((ρ : Measure S).map H).map (fun k => (X k, Y (ψ n) k)) :=
        (Measure.map_map (hXm.prodMk (hYm (ψ n))) hHm).symm
      _ = μ.map (fun k => (X k, Y (ψ n) k)) := by rw [hlawH]
  have hconv : ∀ F : S → ℝ, Continuous F → (∃ C, ∀ x, |F x| ≤ C) →
      Tendsto (fun n => ∫ q, F (q.1, Yc n q) ∂(ρ : Measure S)) atTop
        (𝓝 (∫ q, F q ∂(ρ : Measure S))) := by
    intro F hF ⟨C, hC⟩
    let F' : S →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfBound ⟨F, hF⟩ (2 * C) (fun x y => by
        rw [Real.dist_eq]
        change |F x - F y| ≤ 2 * C
        linarith [abs_sub (F x) (F y), hC x, hC y])
    have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim) F'
    have hFn (n : ℕ) : ∫ q, F (q.1, Yc n q) ∂(ρ : Measure S) =
        ∫ k, F k ∂(μ.map (fun a => (X a, Y (ψ n) a))) := by
      rw [← hpre n, integral_map
        (measurable_fst.prodMk (hYcm n)).aemeasurable
        hF.measurable.aestronglyMeasurable]
    change Tendsto (fun n => ∫ k, F k ∂(μ.map (fun a => (X a, Y (ψ n) a))))
      atTop (𝓝 (∫ q, F q ∂(ρ : Measure S))) at ht
    exact ht.congr' (Eventually.of_forall fun n => (hFn n).symm)
  have hfixed := LQGMetric.DFGPS.L217.tendsto_integral_mul_of_fixed_marginal
    (P := (ρ : Measure S)) (X := (Prod.fst : S → CoordJ → ℝ))
    measurable_fst hYcm measurable_snd hconv
    ((hg.comp (measurable_pairJInv ⊤)))
    (fun q => hgb.choose_spec (pairJInv ⊤ q)) hφ hφb.choose_spec
  have hYeρ (n : ℕ) :
      (fun q : S => lfppSeq κ ξ εs (H q) (ψ n + N₀)) =ᵐ[(ρ : Measure S)] Yc n := by
    have hmu : ∀ᵐ k ∂((ρ : Measure S).map H),
        lfppSeq κ ξ εs k (ψ n + N₀) = Y (ψ n) k := by
      rw [hlawH]
      exact hYe (ψ n)
    exact ae_of_ae_map hHm.aemeasurable hmu
  have hDq : ∀ᵐ q ∂(ρ : Measure S), (Dh q).1 = q.2 := by
    filter_upwards [hproper] with q hq
    simp [Dh, l8_toContMetric, hq.1]
  have eL (n : ℕ) :
      (∫ q, g (H q) * φ (lfppSeq κ ξ (εs ∘ fun n => ψ n + N₀) (H q) n)
        ∂(ρ : Measure S)) =
      ∫ q, g (H q) * φ (Yc n q) ∂(ρ : Measure S) := by
    apply integral_congr_ae
    filter_upwards [hYeρ n] with q hq
    rw [show lfppSeq κ ξ (εs ∘ fun n => ψ n + N₀) (H q) n =
      lfppSeq κ ξ εs (H q) (ψ n + N₀) from rfl, hq]
  have eR : (∫ q, g (H q) * φ ((Dh q).1) ∂(ρ : Measure S)) =
      ∫ q, g (H q) * φ q.2 ∂(ρ : Measure S) := by
    apply integral_congr_ae
    filter_upwards [hDq] with q hq
    rw [hq]
  change Tendsto (fun n => ∫ q, g (H q) * φ (Yc n q) ∂(ρ : Measure S))
    atTop (𝓝 (∫ q, g (H q) * φ q.2 ∂(ρ : Measure S))) at hfixed
  rw [eR]
  exact hfixed.congr' (Eventually.of_forall fun n => (eL n).symm)

end HigherDimLQGMetric
