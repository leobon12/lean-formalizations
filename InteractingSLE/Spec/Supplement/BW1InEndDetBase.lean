/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1InEnd
import InteractingSLE.Spec.Supplement.GB6LifeBase
import InteractingSLE.Spec.Supplement.GB6LifeEnd
import InteractingSLE.Spec.Sec5.Prop49QExitMainNR
import InteractingSLE.Foundations.Loewner.HullFilling
import InteractingSLE.Spec.Supplement.BW1PropContact
import InteractingSLE.Spec.Supplement.GW4LeafClock

/-!
# BW1's endpoint, deterministic half: the boundary correspondence, the clock and the contact

Packet PROVE-BW1-INPUTS. Deterministic tools for `BW1EndpointDetStatement`:

* `isGeneratingTrace_of_isLoewnerTrace`: a continuous Loewner trace on `[0, ∞)` is a generating trace with infinite
  horizon (for drivers that only see `[0, ∞)`);
* **`mem_base_of_mem_trace`** (the boundary correspondence of the state chart `g_A − W`): if the boundary extension
  `f` of `f_ζ⁻¹` sends a point `p ∈ ℍ̄` into the trace range `α([0, ζ])`, then `p` is real and lies in the filled base
  `[V̂^{0,L}_ζ, V̂^{0,R}_ζ]` (interior points go to `ℍ \ K_ζ`; real points outside the base by GB6's base statement
  `Supp8.GB6.gb6BaseStatement`);
* `tendsto_clock`: a strictly increasing clock onto `[0, T)` tends to `T` at the end of its interval;
* `contact_of_firstContactTime_eq`: at a finite first contact of the physical counterflow with a compact set, the
  counterflow chart trace is nonzero and its inversion lies in the set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.BW1In

open Supp8.GB6

/-- A continuous Loewner trace of a driver that only sees `[0, ∞)` is a generating trace on `[0, ∞)`. -/
theorem isGeneratingTrace_of_isLoewnerTrace {U : ℝ → ℝ} (hUnn : ∀ x : ℝ, U (x.toNNReal : ℝ) = U x)
    {η : ℝ → ℂ} (hη : IsLoewnerTrace U η) :
    IsGeneratingTrace (fun s : ℝ≥0 => U s) ⊤ (fun s : ℝ≥0 => η s) := by
  have hc : Continuous fun s : ℝ≥0 => η s :=
    hη.2.1.comp_continuous continuous_subtype_val fun s => s.2
  refine ⟨by simpa using hη.1, hc.continuousOn, fun t _ => ?_⟩
  have he : (fun s : ℝ => (fun s : ℝ≥0 => U s) s.toNNReal) = U := funext fun x => hUnn x
  rw [he, hη.2.2 t t.2]
  have himg : (fun s : ℝ≥0 => η s) '' Icc 0 t = η '' Icc (0 : ℝ) t := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, ⟨s.2, NNReal.coe_le_coe.2 hs.2⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.toNNReal, ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hx.2⟩, ?_⟩
      simp only [Real.coe_toNNReal _ hx.1]
  rw [himg]
  exact isFilling_fillH (isCompact_Icc.image_of_continuousOn (hη.2.1.mono Icc_subset_Ici_self))

/-- The points `y + i/(n+1)` of `ℍ` tend to `y`. -/
theorem tendsto_real_add_I (y : ℝ) :
    Tendsto (fun n : ℕ => (y : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) atTop (𝓝[H] (y : ℂ)) := by
  have h1 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun n : ℕ => (y : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) atTop
      (𝓝 ((y : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) :=
    tendsto_const_nhds.add (((Complex.continuous_ofReal.tendsto 0).comp h1).mul tendsto_const_nhds)
  rw [Complex.ofReal_zero, zero_mul, add_zero] at h2
  refine tendsto_nhdsWithin_iff.2 ⟨h2, Eventually.of_forall fun n => ?_⟩
  show 0 < ((y : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I).im
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.I_im, mul_one, zero_add]
  positivity

/-- **The boundary correspondence of the state chart**: if the boundary extension `f` of `f_ζ⁻¹` sends `p ∈ ℍ̄` into
the trace range `η([0, ζ])`, then `p` is real and lies in the filled base `[V̂^{0,L}_ζ, V̂^{0,R}_ζ]`. -/
theorem mem_base_of_mem_trace {U : ℝ → ℝ} (hUc : Continuous U) (hU0 : U 0 = 0)
    (hUnn : ∀ x : ℝ, U (x.toNNReal : ℝ) = U x) {η : ℝ → ℂ} (hη : IsLoewnerTrace U η) {ζ : ℝ≥0} {f : ℂ → ℂ}
    (hf : ∀ p ∈ QuantumZipper.Hbar, Tendsto (fwdMapInv U ζ) (𝓝[H] p) (𝓝 (f p))) {p : ℂ}
    (hp : p ∈ QuantumZipper.Hbar) (hfp : f p ∈ (fun s : ℝ≥0 => η s) '' Icc 0 ζ) :
    p.im = 0 ∧ baseL U ζ ≤ p.re ∧ p.re ≤ baseR U ζ := by
  obtain ⟨u, hu, hfu⟩ := hfp
  have hζ : (0 : ℝ) ≤ (ζ : ℝ) := NNReal.coe_nonneg ζ
  rcases (show (0 : ℝ) ≤ p.im from hp).lt_or_eq with hpos | hzero
  · exfalso
    have hpH : p ∈ H := hpos
    have heq : fwdMapInv U ζ p = f p :=
      tendsto_nhds_unique (tendsto_pure_nhds _ p) ((hf p hp).mono_left (pure_le_nhdsWithin hpH))
    have hmem := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hUc hU0 hζ hpH
    rw [heq, ← hfu] at hmem
    exact hmem.2 (Sec5.Prop49Exit.trace_mem_fwdHull hη hζ ⟨u.2, NNReal.coe_le_coe.2 hu.2⟩ hmem.1)
  · obtain ⟨y, rfl⟩ : ∃ y : ℝ, p = (y : ℂ) := ⟨p.re, Complex.ext rfl (by simp [← hzero])⟩
    have he : (fun r : ℝ => (fun s : ℝ≥0 => U s) r.toNNReal) = U := funext hUnn
    set q : ℕ → ℂ := fun n => (y : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I with hqdef
    have hqH : ∀ n, q n ∈ H := fun n => by
      show 0 < (q n).im
      simp only [hqdef, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
        mul_zero, Complex.I_im, mul_one, zero_add]
      positivity
    have hz : ∀ n, fwdMapInv U ζ (q n) ∈ H \ fwdHull (fun r : ℝ => (fun s : ℝ≥0 => U s) r.toNNReal) ζ := by
      intro n
      rw [he]
      exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hUc hU0 hζ (hqH n)
    have hlim : Tendsto (fun n => fwdMapInv U ζ (q n)) atTop (𝓝 (f y)) :=
      (hf _ hp).comp (tendsto_real_add_I y)
    have hmap : Tendsto (fun n => fwdMap (fun r : ℝ => (fun s : ℝ≥0 => U s) r.toNNReal) ζ (fwdMapInv U ζ (q n)))
        atTop (𝓝 (y : ℂ)) := by
      rw [he]
      have e : (fun n => fwdMap U ζ (fwdMapInv U ζ (q n))) = q :=
        funext fun n => QuantumZipper.RS.fwdMap_fwdMapInv hUc hU0 hζ (hqH n)
      rw [e]
      exact (tendsto_real_add_I y).mono_right nhdsWithin_le_nhds
    have hB := gb6BaseStatement (fun s : ℝ≥0 => U s) ⊤ (fun s => η s) ζ (isGeneratingTrace_of_isLoewnerTrace hUnn hη)
      (hUc.comp continuous_subtype_val).continuousOn (by simpa using hU0) ENNReal.coe_lt_top
      (fun n => fwdMapInv U ζ (q n)) (f y) y hz hlim ⟨u, hu, hfu⟩ hmap
    rw [he] at hB
    exact ⟨hzero.symm, by simpa using hB⟩

/-- **A strictly increasing clock onto `[0, T)` tends to `T`** at the end of its interval (along any filter that is
eventually in the interval and eventually beyond each of its points). -/
theorem tendsto_clock {ℓ : ℝ≥0 → ℝ≥0} {I : Set ℝ≥0} {T : ℝ≥0∞} {F : Filter ℝ≥0}
    (hmono : StrictMonoOn ℓ I) (himg : ℓ '' I = {u : ℝ≥0 | (u : ℝ≥0∞) < T}) (hFI : ∀ᶠ s in F, s ∈ I)
    (hF : ∀ s₀ ∈ I, ∀ᶠ s in F, s₀ < s) :
    (T = ⊤ → Tendsto ℓ F atTop) ∧ ∀ T₀ : ℝ≥0, T = T₀ → Tendsto ℓ F (𝓝 T₀) := by
  refine ⟨fun hT => tendsto_atTop.2 fun b => ?_, fun T₀ hT => tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩⟩
  · have hb : b ∈ ℓ '' I := by rw [himg, hT]; exact ENNReal.coe_lt_top
    obtain ⟨s₀, hs₀, rfl⟩ := hb
    filter_upwards [hFI, hF s₀ hs₀] with s hs hlt
    exact (hmono hs₀ hs hlt).le
  · have ha' : a ∈ ℓ '' I := by
      rw [himg, hT]
      show (a : ℝ≥0∞) < T₀
      exact_mod_cast ha
    obtain ⟨s₀, hs₀, rfl⟩ := ha'
    filter_upwards [hFI, hF s₀ hs₀] with s hs hlt
    exact hmono hs₀ hs hlt
  · filter_upwards [hFI] with s hs
    have hm : ℓ s ∈ ℓ '' I := ⟨s, hs, rfl⟩
    rw [himg, hT] at hm
    have hm' : ℓ s < T₀ := by exact_mod_cast hm
    exact hm'.trans ha

/-- **A finite first contact with a compact set is attained by a finite physical point**: the counterflow chart trace
is nonzero there and its inversion lies in the set. -/
theorem contact_of_firstContactTime_eq {γ : ℝ≥0 → ℂ} (hγc : Continuous γ) {A : Set ℂ} (hA : IsCompact A)
    {T₀ : ℝ≥0}
    (hT : firstContactTime (fun s => sphereInv (γ s : OnePoint ℂ)) ((fun z : ℂ => (z : OnePoint ℂ)) '' A) = T₀) :
    γ T₀ ≠ 0 ∧ -(γ T₀)⁻¹ ∈ A := by
  have hcl : IsClosed ((fun z : ℂ => (z : OnePoint ℂ)) '' A) := (hA.image OnePoint.continuous_coe).isClosed
  have hmem := firstContactTime_mem (continuous_sphereInv.comp (OnePoint.continuous_coe.comp hγc)) hcl hT
  obtain ⟨z, hz, hze⟩ := hmem
  by_cases h0 : γ T₀ = 0
  · simp only [Function.comp_apply, h0, sphereInv_coe, ↓reduceIte] at hze
    exact absurd hze (OnePoint.coe_ne_infty z)
  · simp only [Function.comp_apply] at hze
    rw [sphereInv_coe_of_ne h0] at hze
    exact ⟨h0, OnePoint.coe_injective hze ▸ hz⟩

end InteractingSLE.Theorem14.BW1In
