/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFusedSource
import InteractingSLE.Spec.ZhanGT4.DualSeedAccessField

/-!
# Adaptedness of the opposite-view fused field

Packet PROVE-ZHAN-GT4-A22. Fixed alive accesses in the frozen chart may
be seed coordinates of the first curve. Measurability follows from the
landed reflected-map observables and the source variational integral.
-/

set_option autoImplicit false
noncomputable section
open Set Complex MeasureTheory
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol)
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The raw log-density and its first two spatial derivatives along an
arbitrary adapted driver, with arbitrary fixed alive chart accesses. -/
theorem measurable_frzAccess_log_jet {n : ℕ} {d : Ω → FrzData n}
    {A : Set ℂ} {φ : ℂ → ℂ} {T : Ω → ℝ} {G : Set Ω} {t κ ζ₀ : ℝ}
    {rr : Fin n → ℝ} {ζ : Fin n → ℝ}
    (hφ : ∀ ω, (d ω).φ = φ) (hκ : ∀ ω, (d ω).κ = κ) (hr : ∀ ω, (d ω).r = rr)
    (hζ₀ : ∀ ω, (d ω).ζ₀ = ζ₀) (hζ : ∀ ω, (d ω).ζ = ζ) (ht : 0 ≤ t)
    (hFM : ∀ u ∈ Icc (0 : ℝ) t,
      FrzMeas (fun ω => (d ω).W) (fun ω => (d ω).W') (fun ω => (d ω).a) A φ T G u)
    (hq₀ : ∀ ω ∈ G, ∃ q, IsForwardSol (d ω).W' (ζ₀ : ℂ) ((d ω).a (T ω)) q)
    (hq : ∀ m ω, ω ∈ G → ∃ q, IsForwardSol (d ω).W' (ζ m : ℂ) ((d ω).a (T ω)) q) :
    Measurable (G.indicator fun ω => (d ω).ell t ((d ω).W t)) ∧
    Measurable (G.indicator fun ω => (d ω).LSX t ((d ω).W t)) ∧
    Measurable (G.indicator fun ω => (d ω).LSXX t ((d ω).W t)) := by
  have hM := hFM t ⟨ht, le_rfl⟩
  have hA (k : ℕ) : Measurable (G.indicator fun ω => (d ω).A k t) := by
    simpa only [FrzData.A, hφ] using hM.measurable_frzA k
  have h20 : Measurable (G.indicator fun ω => (d ω).A20 t) := by
    simpa only [FrzData.A20, hζ₀] using hM.measurable_frzImg hq₀
  have h21 : Measurable (G.indicator fun ω => (d ω).A21 t) := by
    simpa only [FrzData.A21, hζ₀] using hM.measurable_frzImgD hq₀
  have hB0 (m : Fin n) : Measurable (G.indicator fun ω => (d ω).B0 t m) := by
    simpa only [FrzData.B0, hζ] using hM.measurable_frzImg (hq m)
  have hB1 (m : Fin n) : Measurable (G.indicator fun ω => (d ω).B1 t m) := by
    simpa only [FrzData.B1, hζ] using hM.measurable_frzImgD (hq m)
  have hLF : Measurable (G.indicator fun ω =>
      frzLogF (d ω).W (d ω).W' (d ω).a (d ω).φ t) := by
    simpa only [hφ] using measurable_frzLogF ht hFM
  have h0 := (measurable_dualLogTime κ rr h21 hLF h20 hB0 hB1).add
    (measurable_dualLogSpace κ rr (hA 0) (hA 1) h20 hB0)
  have h1 := measurable_dualLogSpaceX κ rr (hA 0) (hA 1) (hA 2) h20 hB0
  have h2 := measurable_dualLogSpaceXX κ rr (hA 0) (hA 1) (hA 2) (hA 3) h20 hB0
  have he (ω : Ω) (k : ℕ) : (d ω).F k t ((d ω).W t) = (d ω).A k t := rfl
  refine ⟨?_, ?_, ?_⟩
  · convert h0.indicator hM.meas using 1
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω, FrzData.ell, FrzData.LT, FrzData.LS, hκ, hr, he, Pi.add_apply]
    · simp only [indicator_of_notMem hω]
  · convert h1.indicator hM.meas using 1
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω, FrzData.LSX, hκ, hr, he]
    · simp only [indicator_of_notMem hω]
  · convert h2.indicator hM.meas using 1
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω, FrzData.LSXX, hκ, hr, he]
    · simp only [indicator_of_notMem hω]

/-- The fused log-density and its first two spatial derivatives are
measurable on the alive event. The original force coordinate supplies the
reference logarithm through its actual variational integral. -/
theorem measurable_seedAccess_log_jet {n : ℕ} {d : Ω → FrzData n}
    {A : Set ℂ} {φ : ℂ → ℂ} {T : Ω → ℝ} {G : Set Ω} {t κ ζ₀ p : ℝ}
    {rr : Fin n → ℝ} {ζ : Fin n → ℝ} {V : Ω → ℝ → ℝ}
    (hφ : ∀ ω, (d ω).φ = φ) (hκ : ∀ ω, (d ω).κ = κ) (hr : ∀ ω, (d ω).r = rr)
    (hζ₀ : ∀ ω, (d ω).ζ₀ = ζ₀) (hζ : ∀ ω, (d ω).ζ = ζ) (ht : 0 ≤ t)
    (hFM : ∀ u ∈ Icc (0 : ℝ) t,
      FrzMeas (fun ω => (d ω).W) (fun ω => (d ω).W') (fun ω => (d ω).a) A φ T G u)
    (hq₀ : ∀ ω ∈ G, ∃ q, IsForwardSol (d ω).W' (ζ₀ : ℂ) ((d ω).a (T ω)) q)
    (hq : ∀ m ω, ω ∈ G → ∃ q, IsForwardSol (d ω).W' (ζ m : ℂ) ((d ω).a (T ω)) q)
    (hqS : ∀ ω ∈ G, ∃ q, IsForwardSol (d ω).W (p : ℂ) (T ω) q)
    (hV : ∀ ω ∈ G, ∀ u ∈ Icc (0 : ℝ) t, V ω u = (d ω).seedAccessSource p u)
    (hVm : ∀ u ∈ Icc (0 : ℝ) t, Measurable (G.indicator fun ω => V ω u)) :
    Measurable (G.indicator fun ω => (d ω).seedAccessEll p t ((d ω).W t)) ∧
    Measurable (G.indicator fun ω => (d ω).seedAccessX p t ((d ω).W t)) ∧
    Measurable (G.indicator fun ω => (d ω).seedAccessXX p t ((d ω).W t)) := by
  have htt : t ∈ Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
  have hM := hFM t htt
  have hWm := fun u hu => ((hFM u hu).drv).indicator hM.meas
  have hG := measurable_log_source_deriv hM.meas ht
    (fun ω hω => (hM.own ω hω).cont) (fun ω hω => (hM.mem ω hω).2) hqS hV hWm hVm
  obtain ⟨h0, h1, h2⟩ := measurable_frzAccess_log_jet hφ hκ hr hζ₀ hζ ht hFM hq₀ hq
  let R : ℝ := -1 / 2 + ∑ m, rr m
  have hE := (hWm t htt).sub (hVm t htt)
  have h0' := (h0.sub (hG.const_mul (dualGamma κ R))).sub (hE.log.const_mul R)
  have h1' := h1.sub ((measurable_const (a := R)).div hE)
  have h2' := h2.add ((measurable_const (a := R)).div (hE.pow_const 2))
  have he (ω : Ω) (hω : ω ∈ G) : V ω t = (d ω).seedAccessSource p t := hV ω hω t htt
  refine ⟨?_, ?_, ?_⟩
  · convert h0'.indicator hM.meas using 1
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω, FrzData.seedAccessEll, FrzData.seedAccessExponent,
        hκ, hr, he ω hω, Pi.sub_apply, R]
    · simp only [indicator_of_notMem hω]
  · convert h1'.indicator hM.meas using 1
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω, FrzData.seedAccessX, FrzData.seedAccessExponent,
        hr, he ω hω, Pi.div_apply, Pi.sub_apply, R]
    · simp only [indicator_of_notMem hω]
  · convert h2'.indicator hM.meas using 1
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω, FrzData.seedAccessXX, FrzData.seedAccessExponent,
        hr, he ω hω, Pi.div_apply, Pi.sub_apply, Pi.add_apply, R]
    · simp only [indicator_of_notMem hω]

end InteractingSLE.ZhanGT4
