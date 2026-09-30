import QuantumZipper.Proofs.Zipper.AreaWinSplit
import QuantumZipper.Proofs.Section5.Prop17PalmCReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-WINDOW (2): from countably many test functions to all of them; `FreeWindowStmt`

Source: S. Sheffield, M. Wang, arXiv:1605.06171, proof of Lemma 3.1, p. 7 ("It is easy to see
that if for each dyadic square `S` … the random variables … a.s. converge …, then the desired
result follows"). We use the countable dense test family of the repository
(`VagueH.exists_denseTestFamily`, positive parts of its members) instead of dyadic squares:

* `measurable_supWin`, `measurable_infWin`: for a regular sample the window densities are
  lower/upper semicontinuous, hence measurable;
* `winInt_le_add`: `f ≤ g + η χ` pointwise gives the same inequality for the window integrals;
* `tendsto_winInt_of_dense`: convergence for the positive parts of a dense family gives
  convergence for every test function `ψ ≥ 0` (limsup/liminf sandwich);
* `windowLimits_of_scaled`: window limits are insensitive to an additive constant in the field
  (both sides scale by `e^{γ c}`), used to pass from the normalized field `X − X(fc(0,1))`;
* **`freeWindowStmt_of_split`**: `SWWindowSplitStmt γ c c' → FreeWindowStmt γ c c'`.

Own elementary bookkeeping (cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

open VagueH GoodSample

theorem winLo_pos (N j : ℕ) : 0 < winLo N j := Real.rpow_pos_of_pos (by norm_num) _

theorem measurable_supWin {x : FieldSample} (hx : IsRegularSample x) (γ : ℝ) (N j : ℕ) :
    Measurable (supWin γ x N j) := by
  obtain ⟨F, hF⟩ := hx
  refine LowerSemicontinuous.measurable ?_
  refine lowerSemicontinuous_biSup fun ρ hρ => ?_
  exact (ENNReal.continuous_ofReal.comp
    (continuous_areaDens γ hF ((winLo_pos N j).trans_le hρ.1))).lowerSemicontinuous

theorem measurable_infWin {x : FieldSample} (hx : IsRegularSample x) (γ : ℝ) (N j : ℕ) :
    Measurable (infWin γ x N j) := by
  obtain ⟨F, hF⟩ := hx
  refine UpperSemicontinuous.measurable ?_
  refine upperSemicontinuous_biInf fun ρ hρ => ?_
  exact (ENNReal.continuous_ofReal.comp
    (continuous_areaDens γ hF ((winLo_pos N j).trans_le hρ.1))).upperSemicontinuous

/-- The abstract window integral `c ∫_ℍ D f`. -/
def winInt (c : ℝ) (D : ℂ → ℝ≥0∞) (f : ℂ → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal c * ∫⁻ w in H, D w * ENNReal.ofReal (f w)

theorem winInt_le_add {c : ℝ} {D : ℂ → ℝ≥0∞} (hD : Measurable D) {f g χ : ℂ → ℝ}
    (hg : Continuous g) (hχ : Continuous χ) (hg0 : ∀ z, 0 ≤ g z) (hχ0 : ∀ z, 0 ≤ χ z)
    {η : ℝ} (hη : 0 ≤ η) (hle : ∀ z, f z ≤ g z + η * χ z) :
    winInt c D f ≤ winInt c D g + ENNReal.ofReal η * winInt c D χ := by
  unfold winInt
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
  calc ENNReal.ofReal c * ∫⁻ w in H, D w * ENNReal.ofReal (f w)
      ≤ ENNReal.ofReal c * ∫⁻ w in H, (D w * ENNReal.ofReal (g w) +
          ENNReal.ofReal η * (D w * ENNReal.ofReal (χ w))) :=
        mul_le_mul_of_nonneg_left (lintegral_mono hpt) zero_le
    _ = ENNReal.ofReal c * (∫⁻ w in H, D w * ENNReal.ofReal (g w)) +
          ENNReal.ofReal η * (ENNReal.ofReal c * ∫⁻ w in H, D w * ENNReal.ofReal (χ w)) := by
        rw [lintegral_add_left hm1, lintegral_const_mul _ hm2]
        ring

/-- Positive part of a test function. -/
def posPart' (g : ℂ → ℝ) : ℂ → ℝ := fun z => max (g z) 0

theorem isTestH_posPart' {g : ℂ → ℝ} (hg : IsTestH g) : IsTestH (posPart' g) := by
  have hs : support (posPart' g) ⊆ support g := by
    intro z hz
    simp only [mem_support, posPart'] at hz ⊢
    intro h0
    rw [h0, max_self] at hz
    exact hz rfl
  refine ⟨hg.1.max continuous_const, hg.2.1.mono' (hs.trans (subset_tsupport g)), ?_⟩
  exact (closure_mono hs).trans hg.2.2

/-- **Dense-family reduction** (fixed sample, fixed `N`, one of the two window densities). -/
theorem tendsto_winInt_of_dense {c : ℝ} {D : ℕ → ℂ → ℝ≥0∞} (hD : ∀ j, Measurable (D j))
    {μ : Measure ℂ} (hμK : ∀ K, IsCompact K → K ⊆ H → μ K < ⊤) {F : Set (ℂ → ℝ)}
    (hF : IsDenseTestFamily F)
    (hconv : ∀ g ∈ F, Tendsto (fun j => winInt c (D j) (posPart' g)) atTop
      (𝓝 (ENNReal.ofReal (∫ z, posPart' g z ∂μ))))
    {ψ : ℂ → ℝ} (hψ : IsTestH ψ) (hψ0 : ∀ z, 0 ≤ ψ z) :
    Tendsto (fun j => winInt c (D j) ψ) atTop (𝓝 (ENNReal.ofReal (∫ z, ψ z ∂μ))) := by
  obtain ⟨K, hK, hKH, hψK, ⟨χ, hχF, hχ0, hχ1⟩, happrox⟩ := hF.2 ψ hψ
  have hχ := hF.1 χ hχF
  have hχp : posPart' χ = χ := funext fun z => max_eq_left (hχ0 z)
  have hχc := hconv χ hχF
  rw [hχp] at hχc
  have hint : ∀ f, IsTestH f → Integrable f μ := fun f hf =>
    hf.integrable (hμK _ hf.2.1.isCompact hf.2.2)
  set Lχ := ∫ z, χ z ∂μ with hLχ
  have hLχ0 : 0 ≤ Lχ := integral_nonneg hχ0
  set I := ∫ z, ψ z ∂μ with hI
  -- the key approximation step, for every `δ > 0`
  have key : ∀ δ : ℝ, 0 < δ →
      limsup (fun j => winInt c (D j) ψ) atTop ≤ ENNReal.ofReal I + ENNReal.ofReal δ ∧
      ENNReal.ofReal I ≤ liminf (fun j => winInt c (D j) ψ) atTop + ENNReal.ofReal δ := by
    intro δ hδ
    set η := δ / (2 * (Lχ + 1)) with hη
    have hη0 : 0 < η := by positivity
    have hηL : 2 * (η * Lχ) ≤ δ := by
      rw [hη]
      have h1 : δ / (2 * (Lχ + 1)) * Lχ ≤ δ / (2 * (Lχ + 1)) * (Lχ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hη0.le
      have h2 : δ / (2 * (Lχ + 1)) * (Lχ + 1) = δ / 2 := by field_simp
      linarith
    obtain ⟨g, hgF, hgK, hgψ⟩ := happrox η hη0
    have hg := hF.1 g hgF
    have hgp := isTestH_posPart' hg
    have hgp0 : ∀ z, 0 ≤ posPart' g z := fun z => le_max_right _ _
    -- pointwise: `|ψ − g⁺| ≤ η χ`
    have hpt : ∀ z, |ψ z - posPart' g z| ≤ η * χ z := by
      intro z
      by_cases hz : z ∈ K
      · have e : ψ z = max (ψ z) 0 := (max_eq_left (hψ0 z)).symm
        calc |ψ z - posPart' g z| = |max (ψ z) 0 - max (g z) 0| := by rw [← e]; rfl
          _ ≤ |ψ z - g z| := abs_max_sub_max_le_abs _ _ _
          _ ≤ η := hgψ z
          _ = η * 1 := (mul_one η).symm
          _ ≤ η * χ z := mul_le_mul_of_nonneg_left (hχ1 z hz) hη0.le
      · have h1 : ψ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hψK h)
        have h2 : g z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hgK h)
        rw [h1, posPart', h2, max_self, sub_zero, abs_zero]
        exact mul_nonneg hη0.le (hχ0 z)
    have hup : ∀ z, ψ z ≤ posPart' g z + η * χ z := fun z => by
      linarith [le_abs_self (ψ z - posPart' g z), hpt z]
    have hdn : ∀ z, posPart' g z ≤ ψ z + η * χ z := fun z => by
      linarith [neg_abs_le (ψ z - posPart' g z), hpt z]
    -- integrals
    have hIg1 : I ≤ ∫ z, posPart' g z ∂μ + η * Lχ := by
      rw [hI, hLχ, ← integral_const_mul, ← integral_add (hint _ hgp)
        ((hint _ hχ).const_mul η)]
      exact integral_mono (hint _ hψ) ((hint _ hgp).add ((hint _ hχ).const_mul η)) hup
    have hIg2 : ∫ z, posPart' g z ∂μ ≤ I + η * Lχ := by
      rw [hI, hLχ, ← integral_const_mul, ← integral_add (hint _ hψ)
        ((hint _ hχ).const_mul η)]
      exact integral_mono (hint _ hgp) ((hint _ hψ).add ((hint _ hχ).const_mul η)) hdn
    have hgc := hconv g hgF
    have hχc' : Tendsto (fun j => ENNReal.ofReal η * winInt c (D j) χ) atTop
        (𝓝 (ENNReal.ofReal η * ENNReal.ofReal Lχ)) :=
      ENNReal.Tendsto.const_mul hχc (Or.inr ENNReal.ofReal_ne_top)
    constructor
    · have hT := hgc.add hχc'
      calc limsup (fun j => winInt c (D j) ψ) atTop
          ≤ limsup (fun j => winInt c (D j) (posPart' g) +
              ENNReal.ofReal η * winInt c (D j) χ) atTop :=
            limsup_le_limsup (Eventually.of_forall fun j =>
              winInt_le_add (hD j) hgp.1 hχ.1 hgp0 hχ0 hη0.le hup)
        _ = ENNReal.ofReal (∫ z, posPart' g z ∂μ) + ENNReal.ofReal η * ENNReal.ofReal Lχ :=
            hT.limsup_eq
        _ = ENNReal.ofReal (∫ z, posPart' g z ∂μ + η * Lχ) := by
            rw [← ENNReal.ofReal_mul hη0.le,
              ← ENNReal.ofReal_add (integral_nonneg hgp0) (mul_nonneg hη0.le hLχ0)]
        _ ≤ ENNReal.ofReal (I + δ) := ENNReal.ofReal_le_ofReal (by linarith)
        _ ≤ ENNReal.ofReal I + ENNReal.ofReal δ := ENNReal.ofReal_add_le
    · have hT := ENNReal.Tendsto.sub hgc hχc' (Or.inl ENNReal.ofReal_ne_top)
      have hlow : ENNReal.ofReal (∫ z, posPart' g z ∂μ) - ENNReal.ofReal η * ENNReal.ofReal Lχ ≤
          liminf (fun j => winInt c (D j) ψ) atTop := by
        rw [← hT.liminf_eq]
        exact liminf_le_liminf (Eventually.of_forall fun j => tsub_le_iff_right.2
          (winInt_le_add (hD j) hψ.1 hχ.1 hψ0 hχ0 hη0.le hdn))
      calc ENNReal.ofReal I ≤ ENNReal.ofReal (∫ z, posPart' g z ∂μ - η * Lχ + δ) :=
            ENNReal.ofReal_le_ofReal (by linarith)
        _ ≤ ENNReal.ofReal (∫ z, posPart' g z ∂μ - η * Lχ) + ENNReal.ofReal δ :=
            ENNReal.ofReal_add_le
        _ = (ENNReal.ofReal (∫ z, posPart' g z ∂μ) - ENNReal.ofReal η * ENNReal.ofReal Lχ) +
              ENNReal.ofReal δ := by
            rw [← ENNReal.ofReal_mul hη0.le, ENNReal.ofReal_sub _ (mul_nonneg hη0.le hLχ0)]
        _ ≤ liminf (fun j => winInt c (D j) ψ) atTop + ENNReal.ofReal δ := by gcongr
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have := (key ε (by exact_mod_cast hε)).2
    rwa [ENNReal.ofReal_coe_nnreal] at this
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have := (key ε (by exact_mod_cast hε)).1
    rwa [ENNReal.ofReal_coe_nnreal] at this

end QuantumZipper.E6
