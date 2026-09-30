import QuantumZipper.Proofs.Zipper.BdryAllMapsWin
import QuantumZipper.Proofs.Zipper.AreaWinDense
import QuantumZipper.Proofs.LQG.AllOffsets

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-THM43 (4): the boundary window node from SW's `L¹ + L²` window estimate

Source: S. Sheffield, M. Wang, arXiv:1605.06171 (literature/1605.06171.pdf), proof of
**Theorem 4.2**, pp. 18–19: "`E(A_k^y − B_k^y)² ≍ 2^{-k(1−γ²/2)}` … The case `√2 ≤ γ < 2` can be
proved using an argument similar to the proof of Lemma 3.1 by breaking the sum over `z ∈ S_k^y`
into two parts", and "by considering the random measures `C(N) sup_{ε∈[2^{-(k+1)/N},2^{-k/N}]}
e^{h̄_ε(z)} dz` and `C̲(N) inf … e^{h̄_ε(z)} dz` as in the proof of Theorem 1.1".

Boundary port of the area chain `AreaWinSplit.lean` / `AreaWinDense.lean` (reusing `WinSplit`,
`ae_tendsto_of_winSplit`, `tendsto_goodFilter_winHi`):

* `SWBdryWindowSplitStmt γ c c'`: SW's window estimate for the boundary measure (the `L¹ + L²`
  split `WinSplit` of the normalized window integrals against the reference `∫ φ dν_{2^{-j/N}}`),
  for the free field normalized by `X(fc(0,1)) = 0`, per `N ≥ 1` and per test function `φ ≥ 0`;
* `tendsto_bWinRef`: SW's Lemma 3.1 (boundary: Theorem 4.2, "for each integer `N ≥ 1`, the random
  measures `µ^B_{2^{-k/N}}` a.s. converge to `µ^B`") along `2^{-j/N}` from the offset-uniform
  boundary limit M4-B4 (`AllOffsets.ae_hasBdryLimit`);
* the dense-family step (`BoundaryVague.testFam`, `bump`) and the additive-constant scaling;
* **`bdryWindowStmt_of_split`** and **`bdryAllMapsStmt_of_split_distortion`**.

Own elementary bookkeeping (cost rule), as in the area chain.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology ENNReal

namespace QuantumZipper
namespace F1

open E6 GoodSample BdryVague

/-- The reference integral `∫ φ dν_{2^{-j/N}}` (in `ℝ≥0∞`). -/
def bWinRef (γ : ℝ) (x : FieldSample) (N j : ℕ) (φ : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ u, ENNReal.ofReal (bdryDens γ x (winHi N j) u * φ u)

/-- The normalized window integral `c ∫ D φ`. -/
def bWinInt (c : ℝ) (D : ℝ → ℝ≥0∞) (φ : ℝ → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal c * ∫⁻ u, D u * ENNReal.ofReal (φ u)

/-- SW Lemma 3.1 / Thm 4.2 along `2^{-j/N}`, from the offset-uniform boundary limit. -/
theorem tendsto_bWinRef {γ : ℝ} {x : FieldSample} (hx : IsRegularSample x) {ν : Measure ℝ}
    (hν : HasBdryLimit γ x ν) {N : ℕ} (hN : 1 ≤ N) {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hφ0 : ∀ u, 0 ≤ φ u) :
    Tendsto (fun j => bWinRef γ x N j φ) atTop (𝓝 (ENNReal.ofReal (∫ u, φ u ∂ν))) := by
  obtain ⟨F, hF⟩ := hx
  obtain ⟨i, hi, hrad⟩ := tendsto_goodFilter_winHi hN
  have h1 := (hν.2 φ hφc hφs).comp hi
  have h2 := (ENNReal.continuous_ofReal.tendsto _).comp h1
  refine h2.congr fun j => ?_
  simp only [Function.comp_apply, hrad]
  have hr : 0 < winHi N j := Real.rpow_pos_of_pos (by norm_num) _
  rw [bWinRef, bdryR, integral_withDensity_ofReal (continuous_bdryDens γ hF hr).measurable
    (fun t => bdryDens_nonneg γ x hr t)]
  refine ofReal_integral_eq_lintegral_ofReal ?_ (Eventually.of_forall fun t =>
    mul_nonneg (bdryDens_nonneg γ x hr t) (hφ0 t))
  exact ((continuous_bdryDens γ hF hr).mul hφc).integrable_of_hasCompactSupport hφs.mul_left

theorem measurable_bSupWin {x : FieldSample} (hx : IsRegularSample x) (γ : ℝ) (N j : ℕ) :
    Measurable (bSupWin γ x N j) := by
  obtain ⟨F, hF⟩ := hx
  refine LowerSemicontinuous.measurable ?_
  refine lowerSemicontinuous_biSup fun ρ hρ => ?_
  exact (ENNReal.continuous_ofReal.comp
    (continuous_bdryDens γ hF ((winLo_pos N j).trans_le hρ.1))).lowerSemicontinuous

theorem measurable_bInfWin {x : FieldSample} (hx : IsRegularSample x) (γ : ℝ) (N j : ℕ) :
    Measurable (bInfWin γ x N j) := by
  obtain ⟨F, hF⟩ := hx
  refine UpperSemicontinuous.measurable ?_
  refine upperSemicontinuous_biInf fun ρ hρ => ?_
  exact (ENNReal.continuous_ofReal.comp
    (continuous_bdryDens γ hF ((winLo_pos N j).trans_le hρ.1))).upperSemicontinuous

theorem bWinInt_le_add {c : ℝ} {D : ℝ → ℝ≥0∞} (hD : Measurable D) {f g χ : ℝ → ℝ}
    (hg : Continuous g) (hχ : Continuous χ) (hg0 : ∀ z, 0 ≤ g z) (hχ0 : ∀ z, 0 ≤ χ z)
    {η : ℝ} (hη : 0 ≤ η) (hle : ∀ z, f z ≤ g z + η * χ z) :
    bWinInt c D f ≤ bWinInt c D g + ENNReal.ofReal η * bWinInt c D χ := by
  unfold bWinInt
  have hpt : ∀ w, D w * ENNReal.ofReal (f w) ≤
      D w * ENNReal.ofReal (g w) + ENNReal.ofReal η * (D w * ENNReal.ofReal (χ w)) := by
    intro w
    calc D w * ENNReal.ofReal (f w) ≤ D w * ENNReal.ofReal (g w + η * χ w) :=
          mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (hle w)) zero_le
      _ = D w * ENNReal.ofReal (g w) + ENNReal.ofReal η * (D w * ENNReal.ofReal (χ w)) := by
          rw [ENNReal.ofReal_add (hg0 w) (mul_nonneg hη (hχ0 w)), ENNReal.ofReal_mul hη,
            mul_add]
          ring
  have hm1 : Measurable fun w => D w * ENNReal.ofReal (g w) :=
    hD.mul (ENNReal.measurable_ofReal.comp hg.measurable)
  have hm2 : Measurable fun w => D w * ENNReal.ofReal (χ w) :=
    hD.mul (ENNReal.measurable_ofReal.comp hχ.measurable)
  calc ENNReal.ofReal c * ∫⁻ w, D w * ENNReal.ofReal (f w)
      ≤ ENNReal.ofReal c * ∫⁻ w, (D w * ENNReal.ofReal (g w) +
          ENNReal.ofReal η * (D w * ENNReal.ofReal (χ w))) :=
        mul_le_mul_of_nonneg_left (lintegral_mono hpt) zero_le
    _ = ENNReal.ofReal c * (∫⁻ w, D w * ENNReal.ofReal (g w)) +
          ENNReal.ofReal η * (ENNReal.ofReal c * ∫⁻ w, D w * ENNReal.ofReal (χ w)) := by
        rw [lintegral_add_left hm1, lintegral_const_mul _ hm2]
        ring

/-- Positive part of a function on `ℝ`. -/
def posR (g : ℝ → ℝ) : ℝ → ℝ := fun z => max (g z) 0

theorem posR_test {g : ℝ → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) :
    Continuous (posR g) ∧ HasCompactSupport (posR g) :=
  ⟨hg.max continuous_const, hgs.comp_left (g := fun y => max y 0) (by simp)⟩

/-- **Dense-family reduction** on `ℝ` (family: positive parts of `testFam N m`, and `bump N`). -/
theorem tendsto_bWinInt_of_dense {c : ℝ} {D : ℕ → ℝ → ℝ≥0∞} (hD : ∀ j, Measurable (D j))
    {μ : Measure ℝ} [IsFiniteMeasureOnCompacts μ]
    (hconv : ∀ N m : ℕ, Tendsto (fun j => bWinInt c (D j) (posR (testFam N m))) atTop
      (𝓝 (ENNReal.ofReal (∫ z, posR (testFam N m) z ∂μ))))
    (hbump : ∀ N : ℕ, Tendsto (fun j => bWinInt c (D j) (bump N)) atTop
      (𝓝 (ENNReal.ofReal (∫ z, bump N z ∂μ))))
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (hψ0 : ∀ z, 0 ≤ ψ z) :
    Tendsto (fun j => bWinInt c (D j) ψ) atTop (𝓝 (ENNReal.ofReal (∫ z, ψ z ∂μ))) := by
  obtain ⟨N, happrox⟩ := exists_testFam_approx hψc hψs
  set χ := bump N with hχdef
  have hχc : Continuous χ := continuous_bump N
  have hχ0 : ∀ z, 0 ≤ χ z := bump_nonneg N
  have hχconv := hbump N
  have hint : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → Integrable f μ :=
    fun f hf hfs => hf.integrable_of_hasCompactSupport hfs
  have hχi : Integrable χ μ := hint χ hχc (hasCompactSupport_bump N)
  set Lχ := ∫ z, χ z ∂μ with hLχ
  have hLχ0 : 0 ≤ Lχ := integral_nonneg hχ0
  set I := ∫ z, ψ z ∂μ with hI
  have key : ∀ δ : ℝ, 0 < δ →
      limsup (fun j => bWinInt c (D j) ψ) atTop ≤ ENNReal.ofReal I + ENNReal.ofReal δ ∧
      ENNReal.ofReal I ≤ liminf (fun j => bWinInt c (D j) ψ) atTop + ENNReal.ofReal δ := by
    intro δ hδ
    set η := δ / (2 * (Lχ + 1)) with hη
    have hη0 : 0 < η := by positivity
    have hηL : 2 * (η * Lχ) ≤ δ := by
      rw [hη]
      have h1 : δ / (2 * (Lχ + 1)) * Lχ ≤ δ / (2 * (Lχ + 1)) * (Lχ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hη0.le
      have h2 : δ / (2 * (Lχ + 1)) * (Lχ + 1) = δ / 2 := by field_simp
      linarith
    obtain ⟨m, hm⟩ := happrox η hη0
    set g := posR (testFam N m) with hgdef
    have hgT := posR_test (continuous_testFam N m) (hasCompactSupport_testFam N m)
    have hgp0 : ∀ z, 0 ≤ g z := fun z => le_max_right _ _
    have hpt : ∀ z, |ψ z - g z| ≤ η * χ z := by
      intro z
      have e : ψ z = max (ψ z) 0 := (max_eq_left (hψ0 z)).symm
      calc |ψ z - g z| = |max (ψ z) 0 - max (testFam N m z) 0| := by rw [← e]; rfl
        _ ≤ |ψ z - testFam N m z| := abs_max_sub_max_le_abs _ _ _
        _ ≤ η * χ z := hm z
    have hup : ∀ z, ψ z ≤ g z + η * χ z := fun z => by
      linarith [le_abs_self (ψ z - g z), hpt z]
    have hdn : ∀ z, g z ≤ ψ z + η * χ z := fun z => by
      linarith [neg_abs_le (ψ z - g z), hpt z]
    have hψi := hint ψ hψc hψs
    have hgi := hint g hgT.1 hgT.2
    have hIg1 : I ≤ ∫ z, g z ∂μ + η * Lχ := by
      rw [hI, hLχ, ← integral_const_mul, ← integral_add hgi (hχi.const_mul η)]
      exact integral_mono hψi (hgi.add (hχi.const_mul η)) hup
    have hIg2 : ∫ z, g z ∂μ ≤ I + η * Lχ := by
      rw [hI, hLχ, ← integral_const_mul, ← integral_add hψi (hχi.const_mul η)]
      exact integral_mono hgi (hψi.add (hχi.const_mul η)) hdn
    have hgc := hconv N m
    have hχc' : Tendsto (fun j => ENNReal.ofReal η * bWinInt c (D j) χ) atTop
        (𝓝 (ENNReal.ofReal η * ENNReal.ofReal Lχ)) :=
      ENNReal.Tendsto.const_mul hχconv (Or.inr ENNReal.ofReal_ne_top)
    constructor
    · have hT := hgc.add hχc'
      calc limsup (fun j => bWinInt c (D j) ψ) atTop
          ≤ limsup (fun j => bWinInt c (D j) g +
              ENNReal.ofReal η * bWinInt c (D j) χ) atTop :=
            limsup_le_limsup (Eventually.of_forall fun j =>
              bWinInt_le_add (hD j) hgT.1 hχc hgp0 hχ0 hη0.le hup)
        _ = ENNReal.ofReal (∫ z, g z ∂μ) + ENNReal.ofReal η * ENNReal.ofReal Lχ :=
            hT.limsup_eq
        _ = ENNReal.ofReal (∫ z, g z ∂μ + η * Lχ) := by
            rw [← ENNReal.ofReal_mul hη0.le,
              ← ENNReal.ofReal_add (integral_nonneg hgp0) (mul_nonneg hη0.le hLχ0)]
        _ ≤ ENNReal.ofReal (I + δ) := ENNReal.ofReal_le_ofReal (by linarith)
        _ ≤ ENNReal.ofReal I + ENNReal.ofReal δ := ENNReal.ofReal_add_le
    · have hT := ENNReal.Tendsto.sub hgc hχc' (Or.inl ENNReal.ofReal_ne_top)
      have hlow : ENNReal.ofReal (∫ z, g z ∂μ) - ENNReal.ofReal η * ENNReal.ofReal Lχ ≤
          liminf (fun j => bWinInt c (D j) ψ) atTop := by
        rw [← hT.liminf_eq]
        exact liminf_le_liminf (Eventually.of_forall fun j => tsub_le_iff_right.2
          (bWinInt_le_add (hD j) hψc hχc hψ0 hχ0 hη0.le hdn))
      calc ENNReal.ofReal I ≤ ENNReal.ofReal (∫ z, g z ∂μ - η * Lχ + δ) :=
            ENNReal.ofReal_le_ofReal (by linarith)
        _ ≤ ENNReal.ofReal (∫ z, g z ∂μ - η * Lχ) + ENNReal.ofReal δ :=
            ENNReal.ofReal_add_le
        _ = (ENNReal.ofReal (∫ z, g z ∂μ) - ENNReal.ofReal η * ENNReal.ofReal Lχ) +
              ENNReal.ofReal δ := by
            rw [← ENNReal.ofReal_mul hη0.le, ENNReal.ofReal_sub _ (mul_nonneg hη0.le hLχ0)]
        _ ≤ liminf (fun j => bWinInt c (D j) ψ) atTop + ENNReal.ofReal δ := by gcongr
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have := (key ε (by exact_mod_cast hε)).2
    rwa [ENNReal.ofReal_coe_nnreal] at this
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have := (key ε (by exact_mod_cast hε)).1
    rwa [ENNReal.ofReal_coe_nnreal] at this

end F1
end QuantumZipper
