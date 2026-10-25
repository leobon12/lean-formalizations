import SupercriticalLQGUniqueness.B2.Median.GoodLoopsEvent
import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Site
import SupercriticalLQGUniqueness.B2.DG20Lim.SparseDyadicRadius

 













set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

open SupercriticalLQGUniqueness.Uniqueness
open LQGMetric (addConst restrictTo DistOn)

 
def loopScale (j : ℕ) : ℝ := (B2.DG20Lim.ratRad64 1 j : ℝ)

theorem loopScale_pos (j : ℕ) : 0 < loopScale j := by
  unfold loopScale
  exact_mod_cast B2.DG20Lim.ratRad64_pos (by norm_num) j

theorem loopScale_eq (j : ℕ) : loopScale j = 1 / (2 : ℝ) ^ (6 * j) := by
  unfold loopScale
  rw [B2.DG20Lim.ratRad64_one_eq_dyadic]
  push_cast
  ring

 
theorem canonical_loopGood_local {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Set.Ioi (0 : ℝ)) (D : LQGMetric.DistC → LSCMetric)
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hweak : B2.Iface.IsPfeWeakMetric ξ D c)
    (C : ℝ) (w : ℂ) (t : ℝ) (ht : 0 < t)
    (U : TopologicalSpace.Opens ℂ)
    (hU : Toolkit.AnnulusIteration.closedAnnulus w t (2 * t) ⊆ (U : Set ℂ)) :
    ∃ S : Set (DistOn U), MeasurableSet S ∧
      {g | LoopGood C (D g) w t ht} =ᵐ[TwoScale.S36.muH P h] restrictTo U ⁻¹' S := by
  have hprob := TwoScale.S36.muH_isProb P h hh.1
  have hμ : LQGMetric.IsGFFPlusCont (id : LQGMetric.DistC → LQGMetric.DistC)
      (TwoScale.S36.muH P h) :=
    BiLipschitz.OneScale.canonical_gaussianShift_isGFFPlusCont P h hh.1
  set E := {g : LQGMetric.DistC | LoopGood C (D g) w t ht} with hEdef
  obtain ⟨hDm, hlen, hloc, _, _, _, _⟩ := hweak
  obtain ⟨FD, -, hlocD⟩ := hloc (TwoScale.S36.muH P h) id hμ U
  have hGood : ∀ᵐ g ∂(TwoScale.S36.muH P h),
      (D g).internal U = FD (restrictTo U g) := hlocD
  obtain ⟨W, hWae, hWm, hWsub⟩ := hGood.exists_measurable_mem
  let R : LQGMetric.DistC → LQGMetric.CoordJ → ℝ := fun g => LQGMetric.pairJ U (restrictTo U g)
  have hR : Measurable R :=
    (LQGMetric.measurable_pairJ U).comp (LQGMetric.measurable_restrictTo U)
  have hV : Measurable[LQGMetric.Blueprint.fieldSigma id U] R :=
    (LQGMetric.measurable_pairJ U).comp (Measurable.of_comap_le le_rfl)
  have hsat : ∀ g₁ ∈ W, ∀ g₂ ∈ W, R g₁ = R g₂ → g₁ ∈ E → g₂ ∈ E := by
    intro g₁ hg₁ g₂ hg₂ he hE₁
    have hres : restrictTo U g₁ = restrictTo U g₂ := LQGMetric.injective_pairJ U he
    have hi₁ := hWsub g₁ hg₁
    have hi₂ := hWsub g₂ hg₂
    have hId : ∀ u v, TwoScale.S36.intExt (D g₁) U u v = TwoScale.S36.intExt (D g₂) U u v :=
      TwoScale.S36.intExt_eq_of_internal_eq (by rw [hi₁, hi₂, hres])
    exact (loopGood_iff_of_intExt_eq hId C w t ht hU).mp hE₁
  have hB : NullMeasurableSet E ((TwoScale.S36.muH P h).map id) :=
    (hDm (measurableSet_loopGood C w t ht)).nullMeasurableSet
  have hLocal := LQGMetric.LocalEvent.aeEventIn_of_saturated
    (Y := id) (R := R) (V := R) (B := E) (W := W)
    measurable_id hR hV (Filter.Eventually.of_forall fun _ => rfl) hWm hB hWae hsat
  obtain ⟨F, hFm, hFe⟩ := hLocal
  obtain ⟨S, hS, hF⟩ := MeasurableSpace.measurableSet_comap.mp hFm
  refine ⟨S, hS, ?_⟩
  rw [← hF] at hFe
  exact hFe

 

theorem loopGood_centered_local {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Set.Ioi (0 : ℝ)) (D : LQGMetric.DistC → LSCMetric)
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hweak : B2.Iface.IsPfeWeakMetric ξ D c)
    (C : ℝ) (w : ℂ) (t : ℝ) (ht : 0 < t)
    (U : TopologicalSpace.Opens ℂ)
    (hU : Toolkit.AnnulusIteration.closedAnnulus w t (2 * t) ⊆ (U : Set ℂ)) (Rr : ℝ) :
    LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma
        (fun ω => addConst (h ω) (-LQGMetric.circleAvg (h ω) Rr w)) U)
      {ω | h ω ∈ {g | LoopGood C (D g) w t ht}} := by
  set E := {g : LQGMetric.DistC | LoopGood C (D g) w t ht} with hEdef
  let q' : Ω → DistOn U := fun ω => restrictTo U (addConst (h ω) (-LQGMetric.circleAvg (h ω) Rr w))
  obtain ⟨S, hS, hLocal⟩ := canonical_loopGood_local P h hh ξ D c hweak C w t ht U hU
  have hmeasH := (BiLipschitz.OneScale.gff_gaussianShift P h hh.1).measurable
  have hLocalProd : {y : Ω × ℝ | BiLipschitz.OneScale.gaussianShift h y ∈ E}
      =ᵐ[P.prod BiLipschitz.OneScale.standardGaussian]
      {y : Ω × ℝ | restrictTo U (BiLipschitz.OneScale.gaussianShift h y) ∈ S} :=
    ae_of_ae_map hmeasH.aemeasurable hLocal
  have hprodW : LQGMetric.IsWholePlaneGFF (fun y : Ω × ℝ => h y.1)
      (P.prod BiLipschitz.OneScale.standardGaussian) :=
    BiLipschitz.OneScale.gff_prod_fst P BiLipschitz.OneScale.standardGaussian h hh.1
  have hprod : LQGMetric.IsGFFPlusCont (fun y : Ω × ℝ => h y.1)
      (P.prod BiLipschitz.OneScale.standardGaussian) :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hprodW
  have hsc := ae_addConst_eq_mul_of_pfe (P.prod BiLipschitz.OneScale.standardGaussian)
    (fun y => h y.1) hprod ξ D c hweak (fun y => y.2)
  have hInv : ∀ᵐ y ∂P.prod BiLipschitz.OneScale.standardGaussian,
      (addConst (h y.1) y.2 ∈ E ↔ h y.1 ∈ E) := by
    filter_upwards [hsc] with y hy
    exact loopGood_iff_of_dist_scale _ (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
      ENNReal.ofReal_ne_top (fun x z => hy (x, z)) C w t ht
  have hAE : ∀ᵐ y ∂P.prod BiLipschitz.OneScale.standardGaussian,
      (h y.1 ∈ E ↔
        BiLipschitz.OneScale.localShift U (q' y.1) (LQGMetric.circleAvg (h y.1) Rr w + y.2) ∈ S) := by
    filter_upwards [hInv, hLocalProd] with y hi hl
    have hShift : BiLipschitz.OneScale.localShift U (q' y.1)
        (LQGMetric.circleAvg (h y.1) Rr w + y.2) =
        restrictTo U (BiLipschitz.OneScale.gaussianShift h y) := by
      calc
        BiLipschitz.OneScale.localShift U (q' y.1) (LQGMetric.circleAvg (h y.1) Rr w + y.2) =
            restrictTo U (addConst (addConst (h y.1) (-LQGMetric.circleAvg (h y.1) Rr w))
              (LQGMetric.circleAvg (h y.1) Rr w + y.2)) :=
          BiLipschitz.OneScale.localShift_restrictTo U _ _
        _ = restrictTo U (addConst (h y.1) y.2) := by
          rw [LQGMetric.GFFLaw.addConst_addConst]
          congr 2
          ring
        _ = restrictTo U (BiLipschitz.OneScale.gaussianShift h y) := rfl
    rw [hShift]
    exact hi.symm.trans (Iff.of_eq hl)
  have hSmooth := BiLipschitz.OneScale.gaussian_smoothing_event P U q'
    (fun ω => LQGMetric.circleAvg (h ω) Rr w) {ω | h ω ∈ E} S hS hAE
  refine ⟨{ω | BiLipschitz.OneScale.gaussianSmooth U S (q' ω) > 1 / 2}, ?_, ?_⟩
  · have hB : MeasurableSet {v : DistOn U | BiLipschitz.OneScale.gaussianSmooth U S v > 1 / 2} :=
      measurableSet_lt measurable_const (BiLipschitz.OneScale.measurable_gaussianSmooth U hS)
    exact hB.preimage (Measurable.of_comap_le le_rfl)
  · filter_upwards [hSmooth] with ω hω
    exact propext hω

theorem closedAnnulus_subset_iterAnnulus (w : ℂ) (t : ℝ) (ht : 0 < t) :
    Toolkit.AnnulusIteration.closedAnnulus w t (2 * t) ⊆
      (LQGMetric.Blueprint.annulus w ((1 / 4 : ℝ) * (3 * t)) ((3 / 4 : ℝ) * (3 * t)) : Set ℂ) := by
  intro x hx
  change (1 / 4 : ℝ) * (3 * t) < ‖x - w‖ ∧ ‖x - w‖ < (3 / 4 : ℝ) * (3 * t)
  obtain ⟨h1, h2⟩ := hx
  constructor <;> linarith

 

theorem loopGood_site_iteration (a : ℝ) (ha : 0 < a) :
    ∃ p c₀ : ℝ, 0 < p ∧ p < 1 ∧ 0 < c₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → LQGMetric.DistC), IsNormalizedWholePlaneGFF h P →
        ∀ (ξ : Set.Ioi (0 : ℝ)) (D : LQGMetric.DistC → LSCMetric)
          (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)), B2.Iface.IsPfeWeakMetric ξ D c →
        ∀ (C : ℝ) (w : ℂ) (R : Finset ℕ), R.Nonempty → (∀ j ∈ R, 1 ≤ j) →
        (∀ j ∈ R, ENNReal.ofReal p ≤
          P {ω | LoopGood C (D (h ω)) w (loopScale j) (loopScale_pos j)}) →
        P {ω | ∀ j ∈ R, ¬ LoopGood C (D (h ω)) w (loopScale j) (loopScale_pos j)} ≤
          ENNReal.ofReal (c₀ * Real.exp (-a * R.card)) := by
  obtain ⟨p, c₀, hp0, hp1, hc0, hmain⟩ :=
    Toolkit.AnnulusIteration.annulus_iteration_ae_translated_open
    (1 / 4) (3 / 4) (by norm_num) (by norm_num) (by norm_num) a ha (1 / 2)
    (by norm_num) (by norm_num)
  refine ⟨p, c₀, hp0, hp1, hc0, ?_⟩
  intro Ω _ P _ h hh ξ D c hweak C w R hRne hR1 hprob
  set N := R.card with hNdef
  have hN : 1 ≤ N := Finset.card_pos.mpr hRne
  let js : ℕ → ℕ := Objects.AnnulusTails.extEnum R
  have hjs : StrictMono js := Objects.AnnulusTails.extEnum_strictMono R hR1
  let Att : ℕ → Set Ω := fun j =>
    {ω | h ω ∈ {g | LoopGood C (D g) w (loopScale j) (loopScale_pos j)}}
  let rad : ℕ → ℝ := fun k => 3 * loopScale (js k)
  have hradpos : ∀ k, 0 < rad k := fun k => by
    have := loopScale_pos (js k); simp only [rad]; positivity
  have hanti : Antitone rad := by
    intro k k' hkk'
    simp only [rad]
    have hle : js k ≤ js k' := hjs.monotone hkk'
    rw [loopScale_eq, loopScale_eq]
    have hp1' : (2 : ℝ) ^ (6 * js k) ≤ (2 : ℝ) ^ (6 * js k') :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have := one_div_le_one_div_of_le (by positivity) hp1'
    linarith
  have hratio : ∀ k, rad (k + 1) / rad k ≤ 1 / 4 := by
    intro k
    rw [div_le_iff₀ (hradpos k)]
    simp only [rad]
    rw [loopScale_eq, loopScale_eq]
    have hlt : js k + 1 ≤ js (k + 1) := hjs (Nat.lt_succ_self k)
    have hpow : (2 : ℝ) ^ (6 * js k) * 64 ≤ (2 : ℝ) ^ (6 * js (k + 1)) := by
      have : (2 : ℝ) ^ (6 * js k) * 64 = (2 : ℝ) ^ (6 * js k + 6) := by
        rw [pow_add]; norm_num
      rw [this]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hpos : 0 < (2 : ℝ) ^ (6 * js k) := by positivity
    have hpos' : 0 < (2 : ℝ) ^ (6 * js (k + 1)) := by positivity
    have h1 : 1 / (2 : ℝ) ^ (6 * js (k + 1)) ≤ 1 / ((2 : ℝ) ^ (6 * js k) * 64) :=
      one_div_le_one_div_of_le (by positivity) hpow
    have h2 : 1 / ((2 : ℝ) ^ (6 * js k) * 64) = (1 / (2 : ℝ) ^ (6 * js k)) / 64 := by
      field_simp
    rw [h2] at h1
    have h3 : 0 < 1 / (2 : ℝ) ^ (6 * js k) := by positivity
    linarith
  let E : ℕ → Set Ω := fun k => if 1 ≤ k ∧ k ≤ N then Att (js k) else univ
  have hEloc : ∀ k, LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma
        (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) (rad k) w))
        (LQGMetric.Blueprint.annulus w ((1 / 4 : ℝ) * rad k) ((3 / 4 : ℝ) * rad k))) (E k) := by
    intro k
    by_cases hk : 1 ≤ k ∧ k ≤ N
    · have hEk : E k = Att (js k) := ite_eq_left hk
      rw [hEk]
      exact loopGood_centered_local P h hh ξ D c hweak C w (loopScale (js k))
        (loopScale_pos (js k)) _
        (closedAnnulus_subset_iterAnnulus w (loopScale (js k)) (loopScale_pos (js k))) (rad k)
    · have hEk : E k = univ := ite_eq_right hk
      rw [hEk]
      exact ⟨univ, MeasurableSet.univ, ae_eq_refl _⟩
  have hEprob : ∀ k, ENNReal.ofReal p ≤ P (E k) := by
    intro k
    by_cases hk : 1 ≤ k ∧ k ≤ N
    · have hEk : E k = Att (js k) := ite_eq_left hk
      rw [hEk]
      exact hprob (js k) (Objects.AnnulusTails.extEnum_mem R hk.1 hk.2)
    · have hEk : E k = univ := ite_eq_right hk
      rw [hEk, measure_univ]
      exact ENNReal.ofReal_le_one.mpr hp1.le
  have hiter := hmain P h hh.1 w rad E hradpos hanti hratio hEloc hEprob N
  refine (measure_mono ?_).trans hiter
  intro ω hω
  have hzero : LQGMetric.Blueprint.countOcc E N ω = 0 := by
    classical
    unfold LQGMetric.Blueprint.countOcc
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro k hk hkE
    have hk' : 1 ≤ k ∧ k ≤ N := Finset.mem_Icc.mp hk
    have hEk : E k = Att (js k) := ite_eq_left hk'
    rw [hEk] at hkE
    exact hω (js k) (Objects.AnnulusTails.extEnum_mem R hk'.1 hk'.2) hkE
  change (LQGMetric.Blueprint.countOcc E N ω : ℝ) < 1 / 2 * N
  rw [hzero, Nat.cast_zero]
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

end SupercriticalLQGUniqueness.B2.Median
