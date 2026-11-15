/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedAccessFusion
import InteractingSLE.Spec.ZhanGT4.DualSeedImageAmalgam

/-!
# The opposite-view log field with an amalgamated original source

Packet PROVE-ZHAN-GT4-A22. `FrzData` records marks in the frozen chart;
they may be boundary accesses of the frozen first hull. Its numerator is
normalized by the one-source reference partition function, rather than by
separate coincident ordinary-mark partition functions.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap)
namespace FrzData
variable {n : ℕ} (d : FrzData n)

/-- The original second marginal's total reduced charge at the first source. -/
def seedAccessExponent : ℝ := -1 / 2 + ∑ m, d.r m

/-- The first source through the original second curve's hydrodynamic map. -/
def seedAccessSource (p t : ℝ) : ℝ := (fwdMap d.W t p).re + d.W t

/-- The opposite-view log density with all original marks fused at `p`.
A constant depending only on the frozen first prefix can normalize its entrance. -/
def seedAccessEll (p t x : ℝ) : ℝ := d.ell t x -
  dualGamma d.κ d.seedAccessExponent * Real.log (deriv (fwdMap d.W t) p).re -
    d.seedAccessExponent * Real.log (x - d.seedAccessSource p t)

/-- First spatial derivative of the fused log density. -/
def seedAccessX (p t x : ℝ) : ℝ := d.LSX t x - d.seedAccessExponent / (x - d.seedAccessSource p t)

/-- Second spatial derivative of the fused log density. -/
def seedAccessXX (p t x : ℝ) : ℝ := d.LSXX t x + d.seedAccessExponent / (x - d.seedAccessSource p t) ^ 2

/-- Third spatial derivative of the fused log density. -/
def seedAccessXXX (p t x : ℝ) : ℝ := d.LSXXX t x - 2 * d.seedAccessExponent /
  (x - d.seedAccessSource p t) ^ 3

/-- Time derivative at a fixed spatial coordinate, using the original
source's Loewner and variational equations. -/
def seedAccessT (p t x : ℝ) : ℝ := d.ellT t x +
  2 * dualGamma d.κ d.seedAccessExponent / (d.seedAccessSource p t - d.W t) ^ 2 +
    d.seedAccessExponent * (2 / (d.seedAccessSource p t - d.W t)) / (x - d.seedAccessSource p t)

/-- The numerator's zero-generator identity holds for arbitrary distinct
alive chart accesses, without identifying them with physical ordinary marks. -/
theorem gen_eq_zero_of_accesses {A : Set ℂ} {T : ℝ}
    (h : OwnData d.W A d.φ T d.a d.W') (hκ : d.κ ≠ 0)
    {q₀ : ℝ → ℂ} (hq₀ : IsForwardSol d.W' d.ζ₀ (d.a T) q₀)
    {q : Fin n → ℝ → ℂ} (hq : ∀ m, IsForwardSol d.W' (d.ζ m) (d.a T) (q m))
    (hζ₀ : ∀ m, d.ζ m ≠ d.ζ₀) (hζ : Function.Injective d.ζ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    d.ellT t (d.W t) + d.κ / 2 * (d.LSXX t (d.W t) + d.LSX t (d.W t) ^ 2) = 0 := by
  obtain ⟨η, hη, r, _, hd, hw, hn⟩ := h.exists_box ht
  have hJ : Icc (max 0 (t - η)) (min T (t + η)) ⊆ Icc 0 T :=
    fun u hu => (OwnData.mem_box_of_abs_lt hu).1
  have hg := h.frzGen_eq_zero hJ hd hw hn hκ d.r hq₀ hq hζ₀ hζ (OwnData.mem_box_self hη ht)
  convert hg using 1
  rfl

/-- The actual force drift of the original marginal in the fused normalization. -/
theorem seedAccess_drift_eq_mirror {κ : ℝ} (hκ : κ ≠ 0)
    (hdκ : d.κ = 16 / κ) (rr : Fin n → ℝ)
    (hdr : d.r = fun m => -(κ / 4) * rr m) (w v : ℝ) :
    d.κ * d.seedAccessExponent / (w - v) = mirrorSourceCharge κ rr / (w - v) := by
  rw [seedAccessExponent, hdκ, hdr, mul_add, Finset.mul_sum]
  have he := mirrorSourceCharge_eq hκ rr
  have hc : (16 / κ) * (-1 / 2) = -(16 / κ) / 2 := by ring
  rw [hc, he]

/-- The fused log density has zero exponential generator under the
amalgamated original force drift. The source may be the first curve's seed;
only its separation from the growing second curve is used. -/
theorem seedAccess_gen_eq_zero {A : Set ℂ} {T p : ℝ}
    (h : OwnData d.W A d.φ T d.a d.W') (hκ : d.κ ≠ 0)
    {q₀ : ℝ → ℂ} (hq₀ : IsForwardSol d.W' d.ζ₀ (d.a T) q₀)
    {q : Fin n → ℝ → ℂ} (hq : ∀ m, IsForwardSol d.W' (d.ζ m) (d.a T) (q m))
    (hζ₀ : ∀ m, d.ζ m ≠ d.ζ₀) (hζ : Function.Injective d.ζ)
    {qS : ℝ → ℂ} (hqS : IsForwardSol d.W (p : ℂ) T qS)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    d.seedAccessT p t (d.W t) +
      (d.κ * d.seedAccessExponent / (d.W t - d.seedAccessSource p t)) *
        d.seedAccessX p t (d.W t) +
      d.κ / 2 * (d.seedAccessXX p t (d.W t) + d.seedAccessX p t (d.W t) ^ 2) = 0 := by
  have hg := d.gen_eq_zero_of_accesses h hκ hq₀ hq hζ₀ hζ ht
  have hE : d.W t - d.seedAccessSource p t ≠ 0 := by
    have hn := (hqS.2 t ht).1
    have hi := im_eq_zero_of_isForwardSol_real h.cont hqS ht
    have he := fwdMap_eq_of_isForwardSol h.cont hqS ht
    simp only [seedAccessSource, sub_add_eq_sub_sub_swap, sub_self, zero_sub]
    exact neg_ne_zero.2 (he ▸ re_ne_zero_of_im_eq_zero hn hi)
  have heT : d.seedAccessT p t (d.W t) = d.ellT t (d.W t) -
      (-2 * dualGamma d.κ d.seedAccessExponent + 2 * d.seedAccessExponent) /
        (d.W t - d.seedAccessSource p t) ^ 2 := by
    unfold seedAccessT
    have hn : d.seedAccessSource p t - d.W t ≠ 0 := sub_ne_zero.2 (sub_ne_zero.1 hE).symm
    field_simp [hE, hn]
    ring
  rw [heT, seedAccessX, seedAccessXX]
  exact fused_quotient_gen_eq_zero hg

end FrzData
end InteractingSLE.ZhanGT4
