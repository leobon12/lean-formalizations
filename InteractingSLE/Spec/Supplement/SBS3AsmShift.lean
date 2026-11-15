/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3AssemblyData
import InteractingSLE.Spec.Supplement.SB2FinCompP38
import InteractingSLE.Spec.Exist.FlowField
import InteractingSLE.Spec.Restart.ChartMeasLift
import InteractingSLE.Spec.Restart.ClockTrace
import InteractingSLE.Foundations.Loewner.ConformalImageFull

/-!
# Lemma S3 in shifted coordinates: real translations of hulls, charts and protected means

Worker PROVE-R6-CORNER (Theorem 1.4, Lemma S3 in SB2(1)'s configuration, specification pp. 579–580, 632). SB2(1)'s
second history starts at the seed `u ≤ 0`; S3's comparison is made in coordinates shifted by `u`. Deterministic:

* `isHPHull_image_sub`, `isMapOut_image_sub`, `fillH_image_sub`: hulls, map-outs and fillings under `z ↦ z − u`;
* **`canonDerivLog_image_sub`**: the canonical logarithm is translation covariant (uniqueness
  `IsCanonicalDerivLog.eqOn`);
* **`image_sub_freeNear`**: free-near components are translation covariant (`Homeomorph.image_connectedComponentIn`);
* **`MarkedUnionMeans.image_sub`**: the protected union means are translation covariant (distributions
  `Exist.flowField u 0 G`, densities `v(· + u)`, Lebesgue translation invariance).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Complex Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.SB.S3.Asm

open Restart ConformalImageFull

/-- The real translation `z ↦ z − u` is the affine homeomorphism `affHomeo 1 (−u)`. -/
theorem image_sub_eq_affHomeo (u : ℝ) (S : Set ℂ) :
    (fun z : ℂ => z - (u : ℂ)) '' S = affHomeo 1 one_pos (-u) '' S := by
  congr 1
  funext z
  rw [affHomeo_one_apply]
  push_cast
  ring

theorem mem_image_sub_iff {u : ℝ} {S : Set ℂ} {z : ℂ} : z ∈ (fun z : ℂ => z - (u : ℂ)) '' S ↔ z + u ∈ S := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro h
    exact ⟨z + u, h, by ring⟩

theorem add_real_mem_H_iff' {z : ℂ} (u : ℝ) : z + (u : ℂ) ∈ H ↔ z ∈ H := by
  show (0 : ℝ) < (z + (u : ℂ)).im ↔ (0 : ℝ) < z.im
  simp

theorem sub_real_mem_H_iff {z : ℂ} (u : ℝ) : z - (u : ℂ) ∈ H ↔ z ∈ H := by
  show (0 : ℝ) < (z - (u : ℂ)).im ↔ (0 : ℝ) < z.im
  simp

theorem isHPHull_image_sub {A : Set ℂ} (hA : IsHPHull A) (u : ℝ) :
    IsHPHull ((fun z : ℂ => z - (u : ℂ)) '' A) := by
  rw [image_sub_eq_affHomeo]
  exact hA.image_affHomeo one_pos

theorem isMapOut_image_sub {A : Set ℂ} {g : ℂ → ℂ} (hg : IsMapOut A g) (u : ℝ) :
    IsMapOut ((fun z : ℂ => z - (u : ℂ)) '' A) (fun w => g (w + u) - u) := by
  have h := hg.comp_affHomeo (x := -u) one_pos
  rw [← image_sub_eq_affHomeo] at h
  convert h using 1
  funext w
  rw [affHomeo_one_apply, affHomeo_one_symm_apply]
  push_cast
  ring_nf

theorem fillH_image_sub (A : Set ℂ) (u : ℝ) :
    fillH ((fun z : ℂ => z - (u : ℂ)) '' A) = (fun z : ℂ => z - (u : ℂ)) '' fillH A := by
  have h := fillH_image_add_real A (-u)
  have e : (fun z : ℂ => z + ((-u : ℝ) : ℂ)) = fun z : ℂ => z - (u : ℂ) := by
    funext z; push_cast; ring
  rw [e] at h
  exact h

/-- **The canonical logarithm is translation covariant.** -/
theorem canonDerivLog_image_sub {A : Set ℂ} (hA : IsHPHull A) (u : ℝ) :
    EqOn (canonDerivLog ((fun z : ℂ => z - (u : ℂ)) '' A)) (fun z => canonDerivLog A (z + u))
      (H \ (fun z : ℂ => z - (u : ℂ)) '' A) := by
  set A' := (fun z : ℂ => z - (u : ℂ)) '' A with hA'def
  have hA' : IsHPHull A' := isHPHull_image_sub hA u
  set g := ConformalImage.mapOut A with hgdef
  have hg : IsMapOut A g := ConformalImage.isMapOut_mapOut hA
  set g' : ℂ → ℂ := fun w => g (w + u) - u with hg'def
  have hg' : IsMapOut A' g' := isMapOut_image_sub hg u
  have hL := isCanonicalDerivLog_canonDerivLog hA
  have hderiv : ∀ w : ℂ, deriv g' w = deriv g (w + u) := fun w => by
    rw [hg'def, deriv_sub_const, deriv_comp_add_const]
  have hmemA : ∀ z, z ∈ H \ A' → z + (u : ℂ) ∈ H \ A := fun z hz =>
    ⟨(add_real_mem_H_iff' u).2 hz.1, fun h => hz.2 (mem_image_sub_iff.2 h)⟩
  -- the translated logarithm is canonical for `g'`
  have h₂ : IsCanonicalDerivLog A' g' (fun z => canonDerivLog A (z + u)) := by
    refine ⟨⟨?_, fun z hz => ?_⟩, ?_⟩
    · exact hL.1.1.comp (differentiableOn_id.add_const _) fun z hz => hmemA z hz
    · rw [hderiv]
      exact hL.1.2 _ (hmemA z hz)
    · obtain ⟨Y, hY⟩ := hL.2
      refine ⟨Y, fun w hw => ?_⟩
      show canonDerivLog A (w + u) = log (deriv g' w)
      rw [hderiv, hY (w + u) (by simpa using hw)]
  -- `canonDerivLog A'` is canonical for `g'` as well
  have h₁ : IsCanonicalDerivLog A' g' (canonDerivLog A') := by
    have hL' := isCanonicalDerivLog_canonDerivLog hA'
    have hgg := (ConformalImage.isMapOut_mapOut hA').eqOn hA' hg'
    have hdd : ∀ z ∈ H \ A', deriv (ConformalImage.mapOut A') z = deriv g' z := fun z hz =>
      Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (hA'.isOpen.mem_nhds hz) hgg)
    refine ⟨⟨hL'.1.1, fun z hz => by rw [← hdd z hz]; exact hL'.1.2 z hz⟩, ?_⟩
    obtain ⟨Y, hY⟩ := hL'.2
    obtain ⟨R, hR, hAR⟩ := hA'.exists_subset_ball
    refine ⟨max Y R, fun w hw => ?_⟩
    have hwY : Y < w.im := lt_of_le_of_lt (le_max_left _ _) hw
    have hwR : R < w.im := lt_of_le_of_lt (le_max_right _ _) hw
    have hwH : w ∈ H \ A' := by
      refine ⟨show (0 : ℝ) < w.im from lt_trans hR hwR, fun hwA => ?_⟩
      have h1 := hAR hwA
      rw [mem_ball, dist_zero_right] at h1
      have h2 : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
      linarith [le_abs_self w.im]
    rw [hY w hwY, hdd w hwH]
  exact h₁.eqOn h₂ hA' hg'

/-- **Free-near components are translation covariant.** -/
theorem image_sub_freeNear (A₁ A₂ : Set ℂ) (z₀ : ℂ) (r u : ℝ) :
    (fun z : ℂ => z - (u : ℂ)) '' FinRel.freeNear A₁ A₂ z₀ r =
      FinRel.freeNear ((fun z : ℂ => z - (u : ℂ)) '' A₁) ((fun z : ℂ => z - (u : ℂ)) '' A₂) (z₀ - u) r := by
  set e : ℂ ≃ₜ ℂ := Homeomorph.addRight (-(u : ℂ)) with hedef
  have he : ∀ z, e z = z - (u : ℂ) := fun z => by simp [hedef, sub_eq_add_neg]
  have hfun : (fun z : ℂ => z - (u : ℂ)) = ⇑e := funext fun z => (he z).symm
  have hS : ⇑e '' ((H \ A₂) ∩ ball z₀ r) = (H \ ⇑e '' A₂) ∩ ball (z₀ - u) r := by
    ext w
    constructor
    · rintro ⟨z, ⟨⟨hzH, hzA⟩, hzb⟩, rfl⟩
      refine ⟨⟨by rw [he]; exact (sub_real_mem_H_iff u).2 hzH, fun ⟨z', hz', hzz⟩ => hzA ?_⟩, ?_⟩
      · rw [e.injective hzz] at hz'; exact hz'
      · rw [he, mem_ball, dist_eq_norm, sub_sub_sub_cancel_right, ← dist_eq_norm]; exact hzb
    · rintro ⟨⟨hwH, hwA⟩, hwb⟩
      refine ⟨w + u, ⟨⟨(add_real_mem_H_iff' u).2 hwH, fun h => hwA ⟨w + u, h, by rw [he]; ring⟩⟩, ?_⟩,
        by rw [he]; ring⟩
      rw [mem_ball, dist_eq_norm] at hwb ⊢
      convert hwb using 2
      ring
  rw [hfun]
  ext w
  constructor
  · rintro ⟨z, ⟨hz, hdisj⟩, rfl⟩
    refine ⟨hS ▸ mem_image_of_mem _ hz, ?_⟩
    rw [← hS, ← e.image_connectedComponentIn hz]
    exact (disjoint_image_iff e.injective).2 hdisj
  · rintro ⟨hw, hdisj⟩
    rw [← hS] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    refine ⟨z, ⟨hz, ?_⟩, rfl⟩
    rw [← hS, ← e.image_connectedComponentIn hz] at hdisj
    exact (disjoint_image_iff e.injective).1 hdisj

theorem mem_tsupport_pushTest_shift {φ : TestOn upperHalfPlaneOpens} {u : ℝ} {z : ℂ} :
    z ∈ tsupport (Chart.pushTest (Exist.isConformal_shiftChart u) φ) ↔ z - (u : ℂ) ∈ tsupport φ := by
  set e : ℂ ≃ₜ ℂ := Homeomorph.addRight (-(u : ℂ)) with hedef
  have hez : ∀ w, e w = w - (u : ℂ) := fun w => by simp [hedef, sub_eq_add_neg]
  have hf : ⇑(Chart.pushTest (Exist.isConformal_shiftChart u) φ) = ⇑φ ∘ ⇑e := funext fun w => by
    rw [Exist.pushTest_shiftChart_apply, Function.comp_apply, hez]
  rw [hf, tsupport_comp_eq_preimage, mem_preimage, hez]

theorem tsupport_pushTest_shift_subset {φ : TestOn upperHalfPlaneOpens} {u : ℝ} {S : Set ℂ}
    (hφ : tsupport φ ⊆ (fun z : ℂ => z - (u : ℂ)) '' S) :
    tsupport (Chart.pushTest (Exist.isConformal_shiftChart u) φ) ⊆ S := fun z hz => by
  have h := hφ (mem_tsupport_pushTest_shift.1 hz)
  rw [mem_image_sub_iff, sub_add_cancel] at h
  exact h

theorem diff_H_image_sub (S : Set ℂ) (u : ℝ) :
    H \ (fun z : ℂ => z - (u : ℂ)) '' S = (fun z : ℂ => z - (u : ℂ)) '' (H \ S) := by
  ext z
  rw [mem_image_sub_iff, mem_diff, mem_diff, mem_image_sub_iff, add_real_mem_H_iff']

theorem integral_mul_pushTest_shift (v : ℂ → ℝ) (φ : TestOn upperHalfPlaneOpens) (u : ℝ) :
    ∫ z, v z * Chart.pushTest (Exist.isConformal_shiftChart u) φ z = ∫ w, v (w + u) * φ w := by
  simp_rw [Exist.pushTest_shiftChart_apply]
  rw [← integral_add_right_eq_self (fun z => v z * φ (z - (u : ℂ))) (u : ℂ)]
  simp only [add_sub_cancel_right]

/-- **The protected union means are translation covariant** (densities `v(· + u)`, distributions
`flowField u 0 G`). -/
theorem MarkedUnionMeans.image_sub {A₁ A₂ O : Set ℂ} {p : ℂ} {v₁ v₂ : ℂ → ℝ}
    (h : MarkedUnionMeans A₁ A₂ O p v₁ v₂) (u : ℝ) :
    MarkedUnionMeans ((fun z : ℂ => z - (u : ℂ)) '' A₁) ((fun z : ℂ => z - (u : ℂ)) '' A₂)
      ((fun z : ℂ => z - (u : ℂ)) '' O) (p - u) (fun z => v₁ (z + u)) (fun z => v₂ (z + u)) := by
  obtain ⟨hO, hO₁, hO₂, G, G₁, G₂, ua, ub, hv₁, hr₁, hv₂, hr₂, hua, hra, hub, hrb, ha, hb⟩ := h
  have himg : ∀ {S T : Set ℂ}, S ⊆ T →
      (fun z : ℂ => z - (u : ℂ)) '' S ⊆ (fun z : ℂ => z - (u : ℂ)) '' T := fun hST => image_mono hST
  have hharm : ∀ {v : ℂ → ℝ} {S : Set ℂ}, InnerProductSpace.HarmonicOnNhd v S →
      InnerProductSpace.HarmonicOnNhd (fun z => v (z + u)) ((fun z : ℂ => z - (u : ℂ)) '' S) :=
    fun hv z hz => Exist.harmonicAt_comp_add_const (hv _ (mem_image_sub_iff.1 hz))
  have hO' : IsOpen ((fun z : ℂ => z - (u : ℂ)) '' O) := by
    have e : (fun z : ℂ => z - (u : ℂ)) = ⇑(Homeomorph.addRight (-(u : ℂ))) := funext fun z => by
      simp [sub_eq_add_neg]
    rw [e]
    exact (Homeomorph.addRight _).isOpenMap _ hO
  have htend : Tendsto (fun z => z + (u : ℂ)) (𝓝[(fun z : ℂ => z - (u : ℂ)) '' O] (p - u)) (𝓝[O] p) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => mem_image_sub_iff.1 hz⟩
    have hc : Continuous fun z : ℂ => z + (u : ℂ) := continuous_id.add continuous_const
    have := (hc.tendsto (p - (u : ℂ))).mono_left
      (nhdsWithin_le_nhds (s := (fun z : ℂ => z - (u : ℂ)) '' O))
    simpa using this
  refine ⟨hO', fun z hz => ?_, fun z hz => ?_, Exist.flowField u 0 G, Exist.flowField u 0 G₁,
    Exist.flowField u 0 G₂, fun z => ua (z + u), fun z => ub (z + u), ?_, fun φ hφ => ?_, ?_, fun φ hφ => ?_,
    hharm hua, fun φ hφ => ?_, hharm hub, fun φ hφ => ?_, ha.comp htend, hb.comp htend⟩
  · rw [diff_H_image_sub]; exact himg hO₁ hz
  · rw [diff_H_image_sub]; exact himg hO₂ hz
  · rw [diff_H_image_sub]; exact hharm hv₁
  · rw [diff_H_image_sub] at hφ
    rw [Exist.flowField_apply, hr₁ _ (tsupport_pushTest_shift_subset hφ), integral_mul_pushTest_shift]
    ring
  · rw [diff_H_image_sub]; exact hharm hv₂
  · rw [diff_H_image_sub] at hφ
    rw [Exist.flowField_apply, hr₂ _ (tsupport_pushTest_shift_subset hφ), integral_mul_pushTest_shift]
    ring
  · rw [Exist.flowField_apply, Exist.flowField_apply]
    have := hra _ (tsupport_pushTest_shift_subset hφ)
    rw [← integral_mul_pushTest_shift, ← this]
    ring
  · rw [Exist.flowField_apply, Exist.flowField_apply]
    have := hrb _ (tsupport_pushTest_shift_subset hφ)
    rw [← integral_mul_pushTest_shift, ← this]
    ring

end InteractingSLE.Theorem14.SB.S3.Asm
