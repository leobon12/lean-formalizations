import HigherDimLQGMetric.Sharp.W3Det
import HigherDimLQGMetric.Sharp.W3ProbTail
import HigherDimLQGMetric.Sharp.W3Gaussian
import HigherDimLQGMetric.Sharp.W3ShellTail

/-! Probability assembly for sharp normalized diameter tails. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric MeasureTheory
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- Both shell costs are simultaneously small at every point of a dyadic grid,
outside an event with a polynomial tail. -/
theorem w3_shell_allScales (hd : 3 ≤ d) {ξ Q ζ p : ℝ}
    (hξ : 0 < ξ) (hQ : 0 ≤ Q) (hζ : 0 < ζ) (hp : 0 < p)
    (hgap : (d : ℝ) < ζ * p)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    {CG : ℝ} (hCG : 0 ≤ CG) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ {r c : ℝ}, 0 < r → 0 < c → ∀ G : ℕ → Finset (Rd d),
      (∀ n, ((G n).card : ℝ) ≤ CG * 2 ^ (d * n)) →
      ∀ A : ℝ, 1 ≤ A →
      P {ω | ∃ n : ℕ, ∃ w ∈ G n,
        let ρ : ℝ := c * r / 2 ^ n
        let t : ℝ := A * (2 : ℝ) ^ (ζ * n) * ρ ^ (ξ * Q) *
          Real.exp (ξ * sphereAvg (h ω) ρ w)
        ENNReal.ofReal t < setDistIn (D (h ω))
          (ann w (ρ / 16) (2 * ρ)) (Metric.sphere w (ρ / 8)) (Metric.sphere w ρ) ∨
        ENNReal.ofReal t < aroundDist (D (h ω)) w (3 * ρ / 16) (3 * ρ / 8)} ≤
      ENNReal.ofReal (B * A ^ (-p)) := by
  obtain ⟨C₁, hC₁⟩ := w3_across_upper_superpoly hd hξ hQ hD hp
  obtain ⟨C₂, hC₂⟩ := w3_around_upper_superpoly hd hξ hQ hD hp
  let b₁ : ℝ := max 0 C₁
  let b₂ : ℝ := max 0 C₂
  have hb₁ : 0 ≤ b₁ := le_max_left _ _
  have hb₂ : 0 ≤ b₂ := le_max_left _ _
  let b : ℝ := b₁ + b₂
  have hb : 0 ≤ b := add_nonneg hb₁ hb₂
  let ratio : ℝ := (2 : ℝ) ^ ((d : ℝ) - ζ * p)
  have hratio0 : 0 ≤ ratio := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hratio1 : ratio < 1 :=
    (Real.rpow_lt_one_iff (by norm_num : (0 : ℝ) ≤ 2)).2
      (Or.inr (Or.inl ⟨by norm_num, by linarith⟩))
  let B : ℝ := CG * b / (1 - ratio)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro Ω _ P _ h hh r c hr hc G hcard A hA
  let F : ℕ → Rd d → Ω → Prop := fun n w ω =>
    let ρ : ℝ := c * r / 2 ^ n
    let t : ℝ := A * (2 : ℝ) ^ (ζ * n) * ρ ^ (ξ * Q) *
      Real.exp (ξ * sphereAvg (h ω) ρ w)
    ENNReal.ofReal t < setDistIn (D (h ω))
      (ann w (ρ / 16) (2 * ρ)) (Metric.sphere w (ρ / 8)) (Metric.sphere w ρ) ∨
    ENNReal.ofReal t < aroundDist (D (h ω)) w (3 * ρ / 16) (3 * ρ / 8)
  have hpoint : ∀ n, ∀ w ∈ G n,
      P {ω | F n w ω} ≤
        ENNReal.ofReal (b * (A * (2 : ℝ) ^ (ζ * n)) ^ (-p)) := by
    intro n w hw
    let ρ : ℝ := c * r / 2 ^ n
    let T : ℝ := A * (2 : ℝ) ^ (ζ * n)
    have hρ : 0 < ρ := by dsimp [ρ]; positivity
    have hT : 1 ≤ T := by
      have hexp : 0 ≤ ζ * (n : ℝ) := mul_nonneg hζ.le (Nat.cast_nonneg _)
      have hpow : 1 ≤ (2 : ℝ) ^ (ζ * n) :=
        Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) hexp
      dsimp [T]
      nlinarith only [hA, hpow]
    let E₁ : Set Ω := {ω | ENNReal.ofReal (T * ρ ^ (ξ * Q) *
      Real.exp (ξ * sphereAvg (h ω) ρ w)) <
      setDistIn (D (h ω)) (ann w (ρ / 16) (2 * ρ))
        (Metric.sphere w (ρ / 8)) (Metric.sphere w ρ)}
    let E₂ : Set Ω := {ω | ENNReal.ofReal (T * ρ ^ (ξ * Q) *
      Real.exp (ξ * sphereAvg (h ω) ρ w)) <
      aroundDist (D (h ω)) w (3 * ρ / 16) (3 * ρ / 8)}
    have hE₁ : P E₁ ≤ ENNReal.ofReal (C₁ * T ^ (-p)) :=
      hC₁ P h hh ρ hρ w T hT
    have hE₂ : P E₂ ≤ ENNReal.ofReal (C₂ * T ^ (-p)) := by
      simpa only [E₂, T, ρ] using hC₂ P h hh ρ hρ w T hT
    have hpow : 0 ≤ T ^ (-p) := by positivity
    have hE₁' : P E₁ ≤ ENNReal.ofReal (b₁ * T ^ (-p)) :=
      hE₁.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_right 0 C₁) hpow))
    have hE₂' : P E₂ ≤ ENNReal.ofReal (b₂ * T ^ (-p)) :=
      hE₂.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_right 0 C₂) hpow))
    have hF : {ω | F n w ω} = E₁ ∪ E₂ := by
      ext ω
      simp only [F, E₁, E₂, T, ρ, mem_ofPred_eq, mem_union]
    rw [hF]
    calc
      P (E₁ ∪ E₂) ≤ P E₁ + P E₂ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (b₁ * T ^ (-p)) +
          ENNReal.ofReal (b₂ * T ^ (-p)) := add_le_add hE₁' hE₂'
      _ = ENNReal.ofReal (b * T ^ (-p)) := by
        rw [← ENNReal.ofReal_add (mul_nonneg hb₁ hpow) (mul_nonneg hb₂ hpow)]
        congr 1
        dsimp [b]
        ring
  have hbad := w3_dyadic_failure_bound P G hCG hb hA hζ hp hgap hcard F hpoint
  simpa only [F, B, b, ratio] using hbad

/-- Two-parameter sharp diameter tail: the shell costs contribute `A^{-p}`
and the Gaussian field contributes `C^{-a}`. -/
theorem w3_two_parameter_tail (hd : 3 ≤ d) {ξ Q q ζ p a : ℝ}
    (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    (hq0 : Real.sqrt (2 * d) < q) (hqQ : q < Q)
    (hζ : 0 < ζ) (hζsmall : ζ < ξ * (Q - q))
    (hp : 0 < p) (hgap : (d : ℝ) < ζ * p)
    (ha : a < q + Real.sqrt (q ^ 2 - 2 * d))
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    {U K : Set (Rd d)} (hU : IsOpen U) (hK : IsCompact K)
    (hKc : IsConnected K) (hKU : K ⊆ U) :
    ∃ T B J C₀ : ℝ, 0 < T ∧ 0 ≤ B ∧ 0 ≤ J ∧ 1 ≤ C₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ r : ℝ, 0 < r → ∀ z : Rd d, ∀ A : ℝ, 1 ≤ A →
      ∀ C : ℝ, C₀ ≤ C →
      P {ω | ENNReal.ofReal (T * A * C ^ ξ) <
        normDiam ξ Q D (h ω) U K r z} ≤
        ENNReal.ofReal (B * A ^ (-p)) + ENNReal.ofReal (J * C ^ (-a)) := by
  classical
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  let c : ℝ := δ / 4
  have hc : 0 < c := by dsimp [c]; positivity
  have hcδ : 3 * c ≤ δ := by dsimp [c]; linarith only [hδ]
  obtain ⟨CG, hCG, H, hHcard, hHbound, hAff⟩ :=
    w3_affine_grids (by omega : 1 ≤ d) hR hKR hc hcδ hδU
  have hRc : 0 < R + c := add_pos hR hc
  obtain ⟨Cgauss, Kgauss, hGauss⟩ :=
    w3_sphereAvg_allScales_shifted (by omega : 2 ≤ d) hq0 hRc hc hCG ha
  have hQ0 : 0 ≤ Q := le_of_lt ((Real.sqrt_nonneg _).trans_lt hQ)
  obtain ⟨B, hB, hShell⟩ := w3_shell_allScales hd hξ hQ0 hζ hp hgap hD hCG.le
  let ratio : ℝ := (2 : ℝ) ^ (ζ + ξ * q - ξ * Q)
  have hratio1 : ratio < 1 :=
    (Real.rpow_lt_one_iff (by norm_num : (0 : ℝ) ≤ 2)).2
      (Or.inr (Or.inl ⟨by norm_num, by nlinarith only [hζsmall]⟩))
  let T : ℝ := (5 + 2 * (H 0).card) * c ^ (ξ * Q) / (1 - ratio)
  have hT : 0 < T := by dsimp [T]; positivity
  let J : ℝ := max 0 Kgauss
  have hJ : 0 ≤ J := le_max_left _ _
  let C₀ : ℝ := max 2 Cgauss
  have hC₀ : 1 ≤ C₀ := (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)
  refine ⟨T, B, J, C₀, hT, hB, hJ, hC₀, ?_⟩
  intro Ω _ P _ h hh r hr z A hA C hC
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hC₀.trans hC)
  let G : ℕ → Finset (Rd d) := fun n => (H n).image (fun w => z + r • w)
  let Go : ℕ → Finset (Rd d) := fun n => (H n).image (fun w => r • w)
  obtain ⟨hGcard, hGK, hGU⟩ := hAff hr z
  have hGocard : ∀ n, ((Go n).card : ℝ) ≤ CG * 2 ^ (d * n) := by
    intro n
    have hn : (Go n).card ≤ (H n).card := Finset.card_image_le
    exact (by exact_mod_cast hn : ((Go n).card : ℝ) ≤ (H n).card).trans (hHcard n)
  have hGobound : ∀ n, ∀ w ∈ Go n, ‖w‖ ≤ (R + c) * r := by
    intro n w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith only [hHbound n v hv, hr]
  let Fbad : Set Ω := {ω | ∃ n : ℕ, ∃ w ∈ Go n,
    Real.log C + q * n * Real.log 2 <
      |sphereAvg (h ω) (c * r / 2 ^ n) (z + w) - sphereAvg (h ω) r z|}
  have hFbad : P Fbad ≤ ENNReal.ofReal (J * C ^ (-a)) := by
    have hb := hGauss P h hh r hr z Go hGocard hGobound C
      ((le_max_right _ _).trans hC)
    have hpC : 0 ≤ C ^ (-a) := by positivity
    exact hb.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_right 0 Kgauss) hpC))
  let Sbad : Set Ω := {ω | ∃ n : ℕ, ∃ w ∈ G n,
    let ρ : ℝ := c * r / 2 ^ n
    let t : ℝ := A * (2 : ℝ) ^ (ζ * n) * ρ ^ (ξ * Q) *
      Real.exp (ξ * sphereAvg (h ω) ρ w)
    ENNReal.ofReal t < setDistIn (D (h ω))
      (ann w (ρ / 16) (2 * ρ)) (Metric.sphere w (ρ / 8)) (Metric.sphere w ρ) ∨
    ENNReal.ofReal t < aroundDist (D (h ω)) w (3 * ρ / 16) (3 * ρ / 8)}
  have hSbad : P Sbad ≤ ENNReal.ofReal (B * A ^ (-p)) :=
    hShell P h hh hr hc G hGcard A hA
  let Lbad : Set Ω := {ω | ¬ (D (h ω)).IsLength}
  have hLbad : P Lbad = 0 := by
    have hlen := hD.length P h hh.isLGFPlusCont
    exact (ae_iff.mp hlen)
  have hN₀ : (G 0).card ≤ (H 0).card := Finset.card_image_le
  let E : Set Ω := {ω | ENNReal.ofReal (T * A * C ^ ξ) <
    normDiam ξ Q D (h ω) U K r z}
  have hsub : E ⊆ (Sbad ∪ Fbad) ∪ Lbad := by
    intro ω hω
    by_cases hlen : (D (h ω)).IsLength
    · by_cases hs : ω ∈ Sbad
      · exact Or.inl (Or.inl hs)
      by_cases hf : ω ∈ Fbad
      · exact Or.inl (Or.inr hf)
      exfalso
      have hfield : ∀ n, ∀ w ∈ G n,
          sphereAvg (h ω) (c * r / 2 ^ n) w - sphereAvg (h ω) r z ≤
            Real.log C + q * n * Real.log 2 := by
        intro n w hw
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
        have hvo : r • v ∈ Go n := Finset.mem_image.mpr ⟨v, hv, rfl⟩
        have hn : ¬ Real.log C + q * n * Real.log 2 <
            |sphereAvg (h ω) (c * r / 2 ^ n) (z + r • v) - sphereAvg (h ω) r z| := by
          intro hb
          exact hf ⟨n, r • v, hvo, hb⟩
        exact (le_abs_self _).trans (le_of_not_gt hn)
      have hacross : ∀ n, ∀ w ∈ G n,
          setDistIn (D (h ω))
            (ann w ((c * r / 2 ^ n) / 16) (2 * (c * r / 2 ^ n)))
            (Metric.sphere w ((c * r / 2 ^ n) / 8))
            (Metric.sphere w (c * r / 2 ^ n)) ≤
            ENNReal.ofReal (A * (2 : ℝ) ^ (ζ * n) *
              (c * r / 2 ^ n) ^ (ξ * Q) *
              Real.exp (ξ * sphereAvg (h ω) (c * r / 2 ^ n) w)) := by
        intro n w hw
        exact le_of_not_gt (by
          intro hb
          exact hs ⟨n, w, hw, Or.inl hb⟩)
      have haround : ∀ n, ∀ w ∈ G n,
          aroundDist (D (h ω)) w (3 * (c * r / 2 ^ n) / 16)
            (3 * (c * r / 2 ^ n) / 8) ≤
            ENNReal.ofReal (A * (2 : ℝ) ^ (ζ * n) *
              (c * r / 2 ^ n) ^ (ξ * Q) *
              Real.exp (ξ * sphereAvg (h ω) (c * r / 2 ^ n) w)) := by
        intro n w hw
        exact le_of_not_gt (by
          intro hb
          exact hs ⟨n, w, hw, Or.inr hb⟩)
      have hdia := w3_normDiam_good (by omega : 2 ≤ d) hξ hQ0 hqQ
        hζ hζsmall hc hr (by linarith : 0 < A) hCpos
        (D (h ω)) hlen (h ω) hU hK hKc z G (H 0).card hN₀ hGK hGU
        hfield hacross haround
      have he : ((5 + 2 * (H 0).card) * A * c ^ (ξ * Q) * C ^ ξ) /
          (1 - ratio) = T * A * C ^ ξ := by
        dsimp [T]
        ring
      change ENNReal.ofReal (T * A * C ^ ξ) < normDiam ξ Q D (h ω) U K r z at hω
      rw [← he] at hω
      exact (not_lt_of_ge hdia) hω
    · exact Or.inr hlen
  change P E ≤ _
  calc
    P E ≤ P ((Sbad ∪ Fbad) ∪ Lbad) := measure_mono hsub
    _ ≤ P (Sbad ∪ Fbad) + P Lbad := measure_union_le _ _
    _ ≤ (P Sbad + P Fbad) + P Lbad := by gcongr; exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (B * A ^ (-p)) + ENNReal.ofReal (J * C ^ (-a)) := by
      rw [hLbad, add_zero]
      exact add_le_add hSbad hFbad

end HigherDimLQGMetric
