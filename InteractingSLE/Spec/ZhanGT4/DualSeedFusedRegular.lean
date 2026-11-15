/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFusedBound

/-!
# Local regularity of the fused opposite-view logarithm

Packet PROVE-ZHAN-GT4-A22. The original source is separated from the
growing hull. The raw reflected field and the actual source equations
give the regular log-field required by the stopped random-field Itô API.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap)
namespace FrzData
variable {n : ℕ} (d : FrzData n)

/-- Normalize a regular raw field by the actual fused-source partition
function. All constants are uniform on the protected box. -/
theorem isLogField_seedAccess {A : Set ℂ} {T p b c y rb ρ K L c₀ : ℝ}
    (h : OwnData d.W A d.φ T d.a d.W')
    {q₀ : ℝ → ℂ} (hq₀ : IsForwardSol d.W' d.ζ₀ (d.a T) q₀)
    {q : Fin n → ℝ → ℂ} (hq : ∀ m, IsForwardSol d.W' (d.ζ m) (d.a T) (q m))
    (hζ₀ : ∀ m, d.ζ m ≠ d.ζ₀) (hζ : Function.Injective d.ζ)
    {qS : ℝ → ℂ} (hqS : IsForwardSol d.W (p : ℂ) T qS)
    (hJ : Icc b c ⊆ Icc 0 T)
    (hd : ∀ t ∈ Icc b c, Disjoint (ball (y : ℂ) (2 * rb))
      ((fun z => fwdMap d.W t z + d.W t) '' A))
    (hw : ∀ t ∈ Icc b c, (d.W t : ℂ) ∈ ball (y : ℂ) rb)
    (hn : ∀ t ∈ Icc b c, ∀ z ∈ ball (y : ℂ) rb,
      dslope (ownExt d.W d.W' d.a d.φ t) (d.W t) z ≠ 0)
    (h3 : 3 * ρ ≤ rb)
    (hnd : ∀ t ∈ Icc b c, ∀ x : ℝ, |x - y| < 3 * ρ →
      d.F 1 t x ≠ 0 ∧ d.F 0 t x - d.A20 t ≠ 0 ∧ ∀ m, d.F 0 t x - d.B0 t m ≠ 0)
    (hraw : IsLogField d.ell d.LSX d.LSXX d.LSXXX d.ellT b c y ρ K)
    (hL : 0 ≤ L) (hc : 0 < c₀) (hGL : 2 * T / c₀ ^ 2 ≤ L)
    (hgap : ∀ t ∈ Icc (0 : ℝ) T, c₀ ≤ |(fwdMap d.W t p).re|)
    (hx : ∀ t ∈ Icc b c, ∀ x : ℝ, |x - y| < 3 * ρ →
      c₀ ≤ |x - d.seedAccessSource p t| ∧ InScale L (x - d.seedAccessSource p t)) :
    IsLogField (d.seedAccessEll p) (d.seedAccessX p) (d.seedAccessXX p)
      (d.seedAccessXXX p) (d.seedAccessT p) b c y ρ
      (seedAccessBound d.κ d.seedAccessExponent K L c₀) := by
  let R := Icc b c ×ˢ {x : ℝ | |x - y| < 3 * ρ}
  have hfst : MapsTo Prod.fst R (Icc 0 T) := fun _ hp => hJ hp.1
  have cV : ContinuousOn (fun z : ℝ × ℝ => d.seedAccessSource p z.1) R :=
    (show ContinuousOn (d.seedAccessSource p) (Icc 0 T) from
      fun t ht => ((source_gmap_rates h.cont hqS ht).1).continuousWithinAt).comp continuousOn_fst hfst
  have cG : ContinuousOn (fun z : ℝ × ℝ => Real.log (deriv (fwdMap d.W z.1) p).re) R :=
    (show ContinuousOn (fun t => Real.log (deriv (fwdMap d.W t) p).re) (Icc 0 T) from
      fun t ht => (OwnData.hasDerivWithinAt_log_source_deriv h.cont hqS ht).continuousWithinAt).comp
        continuousOn_fst hfst
  have cE := cV.sub (h.cont.continuousOn.comp continuousOn_fst hfst)
  have cX := continuousOn_snd.sub cV
  have nE : ∀ z ∈ R, d.seedAccessSource p z.1 - d.W z.1 ≠ 0 := by
    intro z hz
    apply SeedData.ne_zero_of_le_abs hc
    simpa only [seedAccessSource, add_sub_cancel_right] using hgap z.1 (hJ hz.1)
  have nX : ∀ z ∈ R, z.2 - d.seedAccessSource p z.1 ≠ 0 :=
    fun z hz => SeedData.ne_zero_of_le_abs hc (hx z.1 hz.1 z.2 hz.2).1
  have spatial : ∀ t ∈ Icc b c, ∀ x : ℝ, |x - y| < 3 * ρ →
      HasDerivAt (d.seedAccessEll p t) (d.seedAccessX p t x) x ∧
      HasDerivAt (d.seedAccessX p t) (d.seedAccessXX p t x) x ∧
      HasDerivAt (d.seedAccessXX p t) (d.seedAccessXXX p t x) x := by
    intro t ht x hx'
    have hxb := mem_ball_of_near h3 hx'
    have hrb : 0 < rb := pos_of_mem_ball hxb
    have hclr : Disjoint (ball (x : ℂ) rb) ((fun z => fwdMap d.W t z + d.W t) '' A) := by
      apply (hd t ht).mono_left
      intro z hz
      have hh := dist_triangle z (x : ℂ) (y : ℂ)
      rw [mem_ball] at hz hxb ⊢
      linarith
    obtain ⟨h1, h0, hm⟩ := hnd t ht x hx'
    exact d.seedAccess_space_derivatives h (hJ ht) hrb hclr h1 h0 hm (nX (t, x) ⟨ht, hx'⟩)
  refine ⟨hraw.pos, seedAccessBound_nonneg hraw.Knonneg hL hc,
    fun t ht x hx' => (spatial t ht x hx').1,
    fun t ht x hx' => (spatial t ht x hx').2.1,
    fun t ht x hx' => (spatial t ht x hx').2.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht x hx'
    obtain ⟨h1, h0, hm⟩ := hnd t ht x hx'
    exact d.hasDerivWithinAt_seedAccessEll h hq₀ hq hζ₀ hζ hqS hJ hd hw hn ht
      (mem_ball_of_near h3 hx') h1 h0 hm (nX (t, x) ⟨ht, hx'⟩)
  · exact (hraw.cont.sub (continuousOn_const.mul cG)).sub (continuousOn_const.mul (cX.log nX))
  · exact hraw.contX.sub (continuousOn_const.div cX nX)
  · exact hraw.contXX.add (continuousOn_const.div (cX.pow 2) fun z hz => pow_ne_zero 2 (nX z hz))
  · exact (hraw.contT.add (continuousOn_const.div (cE.pow 2) fun z hz => pow_ne_zero 2 (nE z hz))).add
      ((continuousOn_const.mul (continuousOn_const.div cE nE)).div cX nX)
  · intro t ht x hx'
    exact d.seedAccess_bounds hL hc (hraw.bound t ht x hx')
      ((abs_log_source_deriv_le h.cont hqS hc hgap (hJ ht)).trans hGL)
      (abs_log_le_of_inScale (hx t ht x hx').2) (hx t ht x hx').1
      (by simpa only [seedAccessSource, add_sub_cancel_right] using hgap t (hJ ht))

end FrzData
end InteractingSLE.ZhanGT4
