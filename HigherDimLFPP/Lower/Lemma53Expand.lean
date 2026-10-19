import HigherDimLFPP.Lower.Lemma52Riemann

/-!
# Lemma 5.3: the exponential expansion of the tilted replacement (source §5.2, Steps 2 and 4)

Packet P-L3, target T3, deterministic part (audit HA4, "Details for later use" D6, Steps 2
and 4; findings HA4-4, HA4-5).

For P-L2a's construction `P` (any `LParams`), a finitely supported `μ = Σ_{z ∈ Sμ} w z δ_z` and
a weight `h : ℝ^d → ℝ` (`h = 1` for the total mass, `h = 1_{z₁ ≤ x}` for the prefix `{z₁ ≤ x}`),
write `rv Y j i z = Y(ρq, ρ, T_i^j z)` for the root-band value at `T_i^j z` and

* `cdfW h j = K⁻¹ Σ_{i,z} w z h(T_i^j z)` (for `h = 1_{z₁ ≤ x}`: P-L1's `replCDF`, the horizontal
  distribution function of `ν_{j,μ}`),
* `linW h j Y = K⁻¹ Σ_{i,z} w z h(T_i^j z) rv Y j i z` (the pairing `⟨H, h ν_{j,μ}⟩`),
* `remW h j Y = K⁻¹ Σ_{i,z} w z h(T_i^j z) R(ζ rv Y j i z)`, `R(t) = eᵗ - 1 - t ≥ 0`,
* `tiltH h Y = K⁻¹ Σ_{i,z} w z h(T_i^I z) e^{ζ rv Y I i z}`, `I = sel Y` (the weighted prefix of the
  tilted replacement).

`tiltH_eq`: `tiltH h = cdfW h I + ζ linW h I + remW h I` (`eᵗ = 1 + t + R(t)`).  For `h = 1` this
is the expansion of `∫ e^{ζH} dν_{I,μ}` (`tiltH_one`, `cdfW_one`), and for `h = 1_{z₁ ≤ x}` the
weighted prefix is the prefix mass of P-L2a's `tiltW` (`tiltH_prefix`, `cdfW_prefix`).
The remainders are nonnegative and dominated by the total ones (`remW_nonneg`,
`remW_le_remW_one`), hence by `Σ_j remW 1 j` whatever the selected index.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Lower

variable {d : ℕ}

/-- The exponential remainder `R(t) = eᵗ - 1 - t`. -/
def expRem (t : ℝ) : ℝ := Real.exp t - 1 - t

theorem expRem_nonneg (t : ℝ) : 0 ≤ expRem t := by
  unfold expRem
  linarith [Real.add_one_le_exp t]

namespace LParams

variable (P : LParams d) (Sμ : Finset (Rd d)) (w : Rd d → ℝ)

/-- The root-band value `Y(ρq, ρ, T_i^j z)`. -/
def rv (Y : TriD d → ℝ) (j : Fin (P.J + 1)) (i : ℕ) (z : Rd d) : ℝ :=
  Y (P.ρ * P.q, P.ρ, (P.T j i).app z)

/-- `K⁻¹ Σ_{i,z} w z h(T_i^j z)`. -/
def cdfW (h : Rd d → ℝ) (j : Fin (P.J + 1)) : ℝ :=
  (1 / (P.K : ℝ)) * ∑ i ∈ Finset.range P.K, ∑ z ∈ Sμ, w z * h ((P.T j i).app z)

/-- `⟨H, h ν_{j,μ}⟩ = K⁻¹ Σ_{i,z} w z h(T_i^j z) Y(ρq, ρ, T_i^j z)`. -/
def linW (h : Rd d → ℝ) (j : Fin (P.J + 1)) (Y : TriD d → ℝ) : ℝ :=
  (1 / (P.K : ℝ)) * ∑ i ∈ Finset.range P.K, ∑ z ∈ Sμ, w z * h ((P.T j i).app z) * P.rv Y j i z

/-- `K⁻¹ Σ_{i,z} w z h(T_i^j z) R(ζ Y(ρq, ρ, T_i^j z))`. -/
def remW (h : Rd d → ℝ) (j : Fin (P.J + 1)) (Y : TriD d → ℝ) : ℝ :=
  (1 / (P.K : ℝ)) * ∑ i ∈ Finset.range P.K, ∑ z ∈ Sμ,
    w z * h ((P.T j i).app z) * expRem (P.ζ * P.rv Y j i z)

/-- The `h`-weighted tilted replacement `∫ h e^{ζH} dν_{I,μ}`, `I = sel Y`. -/
def tiltH (h : Rd d → ℝ) (Y : TriD d → ℝ) : ℝ :=
  (1 / (P.K : ℝ)) * ∑ i ∈ Finset.range P.K, ∑ z ∈ Sμ,
    w z * h ((P.T (P.sel Y) i).app z) * Real.exp (P.ζ * P.rv Y (P.sel Y) i z)

/-- **The exponential expansion**: `∫ h e^{ζH} dν_{I,μ} = ν_{I,μ}(h) + ζ ⟨H, h ν_{I,μ}⟩ +
∫ h R(ζH) dν_{I,μ}`. -/
theorem tiltH_eq (h : Rd d → ℝ) (Y : TriD d → ℝ) :
    P.tiltH Sμ w h Y = P.cdfW Sμ w h (P.sel Y) + P.ζ * P.linW Sμ w h (P.sel Y) Y +
      P.remW Sμ w h (P.sel Y) Y := by
  unfold tiltH cdfW linW remW
  have e : ∀ i ∈ Finset.range P.K, ∀ z ∈ Sμ,
      w z * h ((P.T (P.sel Y) i).app z) * Real.exp (P.ζ * P.rv Y (P.sel Y) i z) =
        w z * h ((P.T (P.sel Y) i).app z) +
          P.ζ * (w z * h ((P.T (P.sel Y) i).app z) * P.rv Y (P.sel Y) i z) +
          w z * h ((P.T (P.sel Y) i).app z) * expRem (P.ζ * P.rv Y (P.sel Y) i z) := by
    intro i _ z _
    unfold expRem
    ring
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun z hz => e i hi z hz]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem tiltH_one (Y : TriD d → ℝ) : P.tiltH Sμ w (fun _ => 1) Y = P.tiltMass Sμ w Y := by
  unfold tiltH tiltMass rv
  simp only [mul_one]

theorem cdfW_one {Sμ : Finset (Rd d)} {w : Rd d → ℝ} (hμ : IsFinProb Sμ w) (hK : 0 < P.K)
    (j : Fin (P.J + 1)) : P.cdfW Sμ w (fun _ => 1) j = 1 := by
  have hK' : (0 : ℝ) < P.K := by exact_mod_cast hK
  unfold cdfW
  simp only [mul_one, hμ.2, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

theorem remW_nonneg {Sμ : Finset (Rd d)} {w : Rd d → ℝ} (hw : ∀ z ∈ Sμ, 0 ≤ w z)
    {h : Rd d → ℝ} (hh : ∀ p, 0 ≤ h p) (j : Fin (P.J + 1)) (Y : TriD d → ℝ) :
    0 ≤ P.remW Sμ w h j Y := by
  unfold remW
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun z hz => ?_)
  exact mul_nonneg (mul_nonneg (hw z hz) (hh _)) (expRem_nonneg _)

theorem remW_le_remW_one {Sμ : Finset (Rd d)} {w : Rd d → ℝ} (hw : ∀ z ∈ Sμ, 0 ≤ w z)
    {h : Rd d → ℝ} (hh1 : ∀ p, h p ≤ 1) (j : Fin (P.J + 1)) (Y : TriD d → ℝ) :
    P.remW Sμ w h j Y ≤ P.remW Sμ w (fun _ => 1) j Y := by
  unfold remW
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun z hz => ?_)
    (by positivity)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hh1 _) (hw z hz))
    (expRem_nonneg _)

/-- The selected remainder is dominated by the sum of the remainders of all profiles. -/
theorem remW_sel_le {Sμ : Finset (Rd d)} {w : Rd d → ℝ} (hw : ∀ z ∈ Sμ, 0 ≤ w z)
    {h : Rd d → ℝ} (hh1 : ∀ p, h p ≤ 1) (Y : TriD d → ℝ) :
    P.remW Sμ w h (P.sel Y) Y ≤ ∑ j, P.remW Sμ w (fun _ => 1) j Y :=
  (P.remW_le_remW_one hw hh1 _ Y).trans (Finset.single_le_sum
    (f := fun j => P.remW Sμ w (fun _ => 1) j Y)
    (fun j _ => P.remW_nonneg hw (fun _ => zero_le_one) j Y) (Finset.mem_univ _))

/-! ## The prefix weight `h = 1_{z₁ ≤ x}` -/

/-- The prefix weight `1_{z₁ ≤ x}`. -/
def preW (x : ℝ) (p : Rd d) : ℝ := if horiz p ≤ x then 1 else 0

theorem preW_nonneg (x : ℝ) (p : Rd d) : 0 ≤ preW x p := by
  unfold preW
  split_ifs <;> norm_num

theorem preW_le_one (x : ℝ) (p : Rd d) : preW x p ≤ 1 := by
  unfold preW
  split_ifs <;> norm_num

/-- For the prefix weight, `cdfW` is P-L1's horizontal distribution function `replCDF` of
`ν_{j,μ}`. -/
theorem cdfW_prefix (x : ℝ) (j : Fin (P.J + 1)) :
    P.cdfW Sμ w (preW x) j = replCDF P.K P.q (P.v j) Sμ w x := by
  unfold cdfW replCDF
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pushCDF_eq_sum_ite]
  refine Finset.sum_congr rfl fun z _ => ?_
  show w z * preW x ((edgeSim P.q (P.v j) i).app z) = _
  unfold preW
  split_ifs <;> ring

/-- For the prefix weight, `tiltH` is the prefix mass of P-L2a's tilted weights `tiltW`. -/
theorem tiltH_prefix (x : ℝ) (Y : TriD d → ℝ) :
    P.tiltH Sμ w (preW x) Y =
      ∑ p ∈ (P.stepPts Sμ).filter (fun p => horiz p ≤ x), P.tiltW Sμ w Y p := by
  classical
  symm
  unfold tiltH tiltW
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Finset.sum_ite_eq]
  have hmem : (P.T (P.sel Y) i).app z ∈ P.stepPts Sμ :=
    mem_stepPts _ (Finset.mem_range.1 hi) hz
  unfold preW rv
  simp only [Finset.mem_filter, hmem, true_and]
  split_ifs <;> ring

end LParams

end HigherDimLFPP.Lower
