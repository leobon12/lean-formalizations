/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetNHGap
import InteractingSLE.Foundations.Loewner.ConformalImageFull

/-!
# G8: Aux. 8's relative hulls, clock and mapping-out factorization

Packet PROVE-G8-DET. This file applies Aux. 8 to a fixed obstacle and proves
the mapping-out factorization for a larger physical hull. The driver may have
an arbitrary initial value; its centered normalization is handled explicitly.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMap)

namespace InteractingSLE.RLC.G8Det

/-- The uncentered Loewner map is hydrodynamically normalized for an arbitrary
initial driver value. This is the translated version of `isMapOut_fwdMap`. -/
theorem isMapOut_fwdMap_any {V : ℝ → ℝ} (hV : Continuous V) {t : ℝ} (ht : 0 ≤ t) :
    IsMapOut (fwdHull V t) (fun z => fwdMap V t z + V t) := by
  let U : ℝ → ℝ := fun s => V s - V 0
  have hU : Continuous U := hV.sub continuous_const
  have hU0 : U 0 = 0 := sub_self _
  have hVeq : V = fun s => U s + V 0 := funext fun s => (sub_add_cancel _ _).symm
  have h := (isMapOut_fwdMap hU hU0 ht).comp_affHomeo (x := V 0) one_pos
  rw [hVeq, ConformalImageFull.fwdHull_add_const]
  convert h using 1
  · exact image_congr fun z _ => (ConformalImageFull.affHomeo_one_apply _ z).symm
  · funext z
    rw [ConformalImageFull.fwdMap_add_const,
      ConformalImageFull.affHomeo_one_apply, ConformalImageFull.affHomeo_one_symm_apply]
    push_cast
    ring

/-- The actual output of Aux. 8, with its capacity identity and boundary
intertwining retained. No estimate is part of this structure. -/
structure RelativeImage (V : ℝ → ℝ) (A : Set ℂ) (φ : ℂ → ℂ) (T : ℝ) where
  clock : ℝ → ℝ
  driver : ℝ → ℝ
  continuous_driver : Continuous driver
  clock_zero : clock 0 = 0
  strictMono_clock : StrictMonoOn clock (Icc 0 T)
  continuous_clock : ContinuousOn clock (Icc 0 T)
  capacity : ∀ t ∈ Icc 0 T,
    ∃ hK : IsHPHull (φ '' fwdHull V t), clock t = HPHull.hcap ⟨_, hK⟩ / 2
  hull_eq : ∀ t ∈ Icc 0 T, fwdHull driver (clock t) = φ '' fwdHull V t
  intertwine : ∀ t ∈ Icc 0 T, ∀ R : ℂ → ℂ,
    IsMapOut ((fun z => fwdMap V t z + V t) '' A) R →
      (∀ z ∈ H \ (A ∪ fwdHull V t),
        fwdMap driver (clock t) (φ z) + driver (clock t) = R (fwdMap V t z + V t)) ∧
      Tendsto R (𝓝[H] (V t : ℂ)) (𝓝 (driver (clock t) : ℂ))

/-- Construct the relative continuous driver and capacity clock by Aux. 8. -/
theorem exists_relativeImage {V : ℝ → ℝ} (hV : Continuous V) {T : ℝ} (hT : 0 < T)
    {A : Set ℂ} (hA : IsHPHull A) {φ : ℂ → ℂ} (hφ : IsMapOut A φ)
    (hd : Disjoint (closure A) (closure (fwdHull V T))) :
    Nonempty (RelativeImage V A φ T) := by
  obtain ⟨a, W, hW, ha0, ham, hac, h⟩ :=
    ConformalImageFull.exists_loewner_image_of_pos hV hT hA hφ hd
  exact ⟨⟨a, W, hW, ha0, ham, hac, fun t ht => (h t ht).1,
    fun t ht => (h t ht).2.1, fun t ht => (h t ht).2.2⟩⟩

namespace RelativeImage

variable {V : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ}
variable (d : RelativeImage V A φ T)

theorem clock_nonneg {t : ℝ} (ht : t ∈ Icc 0 T) : 0 ≤ d.clock t := by
  rw [← d.clock_zero]
  exact d.strictMono_clock.monotoneOn ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1

theorem clock_pos (hT : 0 < T) : 0 < d.clock T := by
  rw [← d.clock_zero]
  exact d.strictMono_clock ⟨le_rfl, hT.le⟩ ⟨hT.le, le_rfl⟩ hT

/-- Every relative time before the terminal time is attained before `T`. -/
theorem clock_surj (hT : 0 < T) {s : ℝ} (hs : s ∈ Ico 0 (d.clock T)) :
    ∃ t ∈ Ico 0 T, d.clock t = s := by
  obtain ⟨t, ht, he⟩ := d.continuous_clock.surjOn_Icc
    (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT.le⟩) ⟨hT.le, le_rfl⟩
    (show s ∈ Icc (d.clock 0) (d.clock T) by rw [d.clock_zero]; exact ⟨hs.1, hs.2.le⟩)
  refine ⟨t, ⟨ht.1, lt_of_le_of_ne ht.2 ?_⟩, he⟩
  intro h
  exact hs.2.ne (h ▸ he.symm)

/-- The relative driver starts at the obstacle map's boundary value at the
old driver. This identifies the constant used to center the relative chain. -/
theorem driver_zero (hV : Continuous V) (hT : 0 ≤ T) (hA : IsHPHull A)
    {c : ℝ} (hc : Tendsto φ (𝓝[H] (V 0 : ℂ)) (𝓝 (c : ℂ)))
    (hφ : IsMapOut A φ) : d.driver 0 = c := by
  have hg0 := isMapOut_fwdMap_any hV (le_refl 0)
  rw [QuantumZipper.RS.fwdHull_zero_eq_empty hV] at hg0
  have he0 := hg0.eqOn isHPHull_empty isMapOut_empty_id
  have hA0 : (fun z => fwdMap V 0 z + V 0) '' A = A := by
    rw [show (fun z => fwdMap V 0 z + V 0) '' A = id '' A from
      image_congr fun z hz => he0 ⟨hA.1 hz, Set.notMem_empty z⟩, image_id]
  have hφ0 : IsMapOut ((fun z => fwdMap V 0 z + V 0) '' A) φ := by rw [hA0]; exact hφ
  have hlim := (d.intertwine 0 ⟨le_rfl, hT⟩ φ hφ0).2
  rw [d.clock_zero] at hlim
  have : (𝓝[H] (V 0 : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, QuantumZipper.CA.Car.closure_H_eq_Hbar]
    show 0 ≤ (V 0 : ℂ).im
    simp only [ofReal_im, le_refl]
  exact_mod_cast tendsto_nhds_unique hlim hc

/-- The relative clock approaches its terminal value from below. -/
theorem tendsto_clock (hT : 0 < T) :
    Tendsto d.clock (𝓝[<] T) (𝓝[<] (d.clock T)) := by
  have hc : Tendsto d.clock (𝓝[<] T) (𝓝 (d.clock T)) :=
    (d.continuous_clock T ⟨hT.le, le_rfl⟩).tendsto.mono_left
      (nhdsWithin_mono _ Ico_subset_Icc_self |>.trans' (nhdsWithin_le_of_mem (Ico_mem_nhdsLT hT)))
  refine tendsto_nhdsWithin_iff.2 ⟨hc, ?_⟩
  filter_upwards [Ico_mem_nhdsLT hT] with t ht
  exact d.strictMono_clock ⟨ht.1, ht.2.le⟩ ⟨hT.le, le_rfl⟩ ht.2

/-- The image Loewner map composed with the obstacle map maps out `A ∪ K_t`. -/
theorem isMapOut_union (hV : Continuous V) (hA : IsHPHull A) (hφ : IsMapOut A φ)
    (hd : Disjoint (closure A) (closure (fwdHull V T))) {t : ℝ} (ht : t ∈ Icc 0 T) :
    IsMapOut (A ∪ fwdHull V t)
      ((fun z => fwdMap d.driver (d.clock t) z + d.driver (d.clock t)) ∘ φ) := by
  have hdt : Disjoint (closure A) (closure (fwdHull V t)) :=
    hd.mono_right (closure_mono ((QuantumZipper.fwdHull_mono (W := V)).1 ht.2))
  have hg := isMapOut_fwdMap_any d.continuous_driver (d.clock_nonneg ht)
  rw [d.hull_eq t ht] at hg
  exact hφ.comp_of_disjoint_closure hA (isHPHull_fwdHull hV ht.1) hdt hg

/-- Factorization of the canonical map of a physical joint hull. The hypothesis
is the hull identity in the original cut chart, rather than a map identity. -/
theorem mapOut_eq (hV : Continuous V) (hA : IsHPHull A) (hφ : IsMapOut A φ)
    (hd : Disjoint (closure A) (closure (fwdHull V T)))
    {K B : Set ℂ} (hK : IsHPHull K) (hB : IsHPHull B) (hKB : K ⊆ B)
    {g : ℂ → ℂ} (hg : IsMapOut K g) {t : ℝ} (ht : t ∈ Icc 0 T)
    (heq : g '' (B \ K) = A ∪ fwdHull V t) :
    EqOn (ConformalImage.mapOut B)
      (fun z => fwdMap d.driver (d.clock t) (φ (g z)) + d.driver (d.clock t)) (H \ B) := by
  have hcomp := d.isMapOut_union hV hA hφ hd ht
  rw [← heq] at hcomp
  exact (ConformalImage.isMapOut_mapOut hB).eqOn hB (hg.comp hK hB hKB hcomp)

end RelativeImage
end InteractingSLE.RLC.G8Det
