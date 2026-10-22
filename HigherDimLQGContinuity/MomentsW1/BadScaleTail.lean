import HigherDimLQGContinuity.MomentsW1.BadScalePeierls

/-! Quadratic tails for the fine-field bad scales. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLQGMetric.DGZ

/-- A common numerical bound for all three Peierls exponents. -/
private theorem wnBadDiameter_num (d k : ℕ) :
    (d:ℝ)*k - ((wnBadDiameter k / 2:ℕ):ℝ) ≤
      (10000 + 2*(d:ℝ)^2) - (k:ℝ)^2/8 := by
  have hD : k^2 ≤ 2*(wnBadDiameter k/2)+10203 := by
    dsimp [wnBadDiameter]
    omega
  have hDr : (k:ℝ)^2 ≤ 2*((wnBadDiameter k/2:ℕ):ℝ)+10203 := by
    exact_mod_cast hD
  have hsq : 0 ≤ ((k:ℝ)-4*d)^2 := sq_nonneg _
  nlinarith

private theorem wnBadDiameter_prev_num (d k : ℕ) (hk : 110 ≤ k) :
    (d:ℝ)*k - ((wnBadDiameter (k-1) / 2:ℕ):ℝ) ≤
      (10000 + 2*(d:ℝ)^2) - (k:ℝ)^2/8 := by
  have hk1 : k-1+1=k := by omega
  have hD : (k-1)^2 ≤ 2*(wnBadDiameter (k-1)/2)+10203 := by
    dsimp [wnBadDiameter]
    omega
  have hDr : ((k-1:ℕ):ℝ)^2 ≤ 2*((wnBadDiameter (k-1)/2:ℕ):ℝ)+10203 := by
    exact_mod_cast hD
  have hk1r : ((k-1:ℕ):ℝ) + 1 = (k:ℝ) := by exact_mod_cast hk1
  have hJ : (k:ℝ)^2 ≤ 4*((wnBadDiameter (k-1)/2:ℕ):ℝ)+40000 := by
    nlinarith [sq_nonneg ((k:ℝ)-2)]
  have hsq : 0 ≤ ((k:ℝ)-4*d)^2 := sq_nonneg _
  nlinarith

private theorem wnRoughDiameter_num (d k : ℕ) (hk : 110 ≤ k) :
    (d:ℝ)*k - ((wnRoughDiameter k / 2:ℕ):ℝ) ≤
      (10000 + 2*(d:ℝ)^2) - (k:ℝ)^2/8 := by
  have hk2 : 3 ≤ k^2 := by nlinarith
  have hJ : k^2 ≤ 4*(wnRoughDiameter k/2)+8 := by
    dsimp [wnRoughDiameter]
    omega
  have hJreal : (k:ℝ)^2 ≤ 4*((wnRoughDiameter k/2:ℕ):ℝ)+8 := by
    exact_mod_cast hJ
  have hsq : 0 ≤ ((k:ℝ)-4*d)^2 := sq_nonneg _
  nlinarith

private theorem wnPeierls_numeric (d k J N : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (hN : (N : ℝ) ≤ 3 * (R + 4) * (2:ℝ)^k)
    (hnum : (d:ℝ)*k - J ≤ (10000 + 2*(d:ℝ)^2) - (k:ℝ)^2/8) :
    (2 * (N : ℝ≥0∞) + 1)^d * (2⁻¹ : ℝ≥0∞)^J ≤
      (2:ℝ≥0∞) ^ ((11000 + 3*(d:ℝ)^2):ℝ) *
        ENNReal.ofReal ((1+R)^d) * (2:ℝ≥0∞)^(-(k:ℝ)^2/8) := by
  have hpow : 1 ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
  have hbase_real : 2*(N:ℝ)+1 ≤ 32*(1+R)*(2:ℝ)^k := by
    nlinarith [hN, mul_nonneg (show 0 ≤ R-1 by linarith) (show 0 ≤ (2:ℝ)^k by positivity)]
  have hbase : 2*(N:ℝ≥0∞)+1 ≤ (2:ℝ≥0∞)^(k+5) * ENNReal.ofReal (1+R) := by
    calc
      2*(N:ℝ≥0∞)+1 = ENNReal.ofReal (2*(N:ℝ)+1) := by norm_cast
      _ ≤ ENNReal.ofReal (32*(1+R)*(2:ℝ)^k) := ENNReal.ofReal_le_ofReal hbase_real
      _ = (2:ℝ≥0∞)^(k+5) * ENNReal.ofReal (1+R) := by
        have he : 32*(1+R)*(2:ℝ)^k = (2:ℝ)^(k+5)*(1+R) := by
          rw [pow_add]
          norm_num
          ring
        rw [he, ENNReal.ofReal_mul (by positivity : 0 ≤ (2:ℝ)^(k+5)),
          ENNReal.ofReal_pow (by norm_num : 0 ≤ (2:ℝ))]
        norm_num
  have hexp : ((k+5:ℕ):ℝ)*(d:ℝ) - (J:ℝ) ≤
      (11000 + 3*(d:ℝ)^2) - (k:ℝ)^2/8 := by
    push_cast
    nlinarith [sq_nonneg ((d:ℝ)-3)]
  have htwo0 : (2:ℝ≥0∞) ≠ 0 := by norm_num
  have htwot : (2:ℝ≥0∞) ≠ ⊤ := by norm_num
  have hpowcomp : (2:ℝ≥0∞)^(((k+5:ℕ):ℝ)*(d:ℝ)-(J:ℝ)) ≤
      (2:ℝ≥0∞)^((11000 + 3*(d:ℝ)^2)-(k:ℝ)^2/8) :=
    ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  calc
    (2*(N:ℝ≥0∞)+1)^d * (2⁻¹:ℝ≥0∞)^J
        ≤ ((2:ℝ≥0∞)^(k+5) * ENNReal.ofReal (1+R))^d * (2⁻¹:ℝ≥0∞)^J :=
          by gcongr
    _ = (2:ℝ≥0∞)^(((k+5:ℕ):ℝ)*(d:ℝ)-(J:ℝ)) * ENNReal.ofReal ((1+R)^d) := by
      rw [mul_pow, ← ENNReal.ofReal_pow (by linarith : 0 ≤ 1+R), mul_assoc]
      rw [← ENNReal.rpow_natCast ((2:ℝ≥0∞)^(k+5)) d,
        ← ENNReal.rpow_natCast (2:ℝ≥0∞) (k+5), ← ENNReal.rpow_mul]
      rw [show (2⁻¹:ℝ≥0∞)^J = (2:ℝ≥0∞)^(-(J:ℝ)) by
        simpa [ENNReal.rpow_neg, ENNReal.rpow_natCast] using
          (ENNReal.inv_pow (a := (2:ℝ≥0∞)) (n := J)).symm]
      calc
        (2:ℝ≥0∞)^(((k+5:ℕ):ℝ) * (d:ℝ)) *
            (ENNReal.ofReal ((1+R)^d) * (2:ℝ≥0∞)^(-(J:ℝ))) =
          ((2:ℝ≥0∞)^(((k+5:ℕ):ℝ) * (d:ℝ)) * (2:ℝ≥0∞)^(-(J:ℝ))) *
            ENNReal.ofReal ((1+R)^d) := by ac_rfl
        _ = _ := by
          rw [← ENNReal.rpow_add _ _ htwo0 htwot]
          congr 1
    _ ≤ (2:ℝ≥0∞)^((11000 + 3*(d:ℝ)^2)-(k:ℝ)^2/8) *
        ENNReal.ofReal ((1+R)^d) := by gcongr
    _ = (2:ℝ≥0∞)^((11000 + 3*(d:ℝ)^2):ℝ) *
        ENNReal.ofReal ((1+R)^d) * (2:ℝ≥0∞)^(-(k:ℝ)^2/8) := by
      rw [sub_eq_add_neg, ENNReal.rpow_add _ _ htwo0 htwot]
      have he : -((k:ℝ)^2 / 8) = -(k:ℝ)^2 / 8 := by ring
      rw [he]
      ac_rfl

/-- Each of the three fine-field cluster failures has a quadratic tail. -/
theorem wnBadAt_prob {d : ℕ} {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {ρ : ℝ}
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) (ξ : ℝ) {R : ℝ} (hR : 1 ≤ R) {q : ℝ≥0∞}
    (hq0 : 0 < q) (hq1 : q < 1) {k n : ℕ} (hk : 110 ≤ k) (hkn : k < n)
    {θ : ℝ≥0∞} (hθ1 : θ ≤ 1)
    (hεθ : (1 + 3 ^ d) * (2 * (d : ℝ≥0∞) * (1 - q)) ≤
      θ ^ ((⌈2 * (2 + ρ)⌉₊ + 1) ^ d))
    (h3 : (3 : ℝ≥0∞) ^ d * θ ≤ 2⁻¹) :
    P (wnBadAt P H ξ R q k n) ≤
      3 * ((2:ℝ≥0∞) ^ (11000 + 3*(d:ℝ)^2) *
        ENNReal.ofReal ((1+R)^d) * (2:ℝ≥0∞)^(-(k:ℝ)^2/8)) := by
  let A : Set Ω := {ω | ¬ SmallClusters (wnGood P H ξ R q k n ω) (wnBadDiameter k)}
  let B : Set Ω := {ω | ¬ SmallClusters (wnGood P H ξ R q (k-1) n ω)
    (wnBadDiameter (k-1))}
  let C : Set Ω := {ω | ¬ SmallClusters
    (wnNice (wnGood P H ξ R q (k-1) n ω) (wnGood P H ξ R q k n ω))
    (wnRoughDiameter k)}
  have hclosed : 2 * (d:ℝ≥0∞) * (1-q) ≤
      θ ^ ((⌈2 * (2 + ρ)⌉₊ + 1)^d) := by
    have h1 : (1:ℝ≥0∞) ≤ 1 + 3^d := le_add_of_nonneg_right (by positivity)
    calc
      2 * (d:ℝ≥0∞) * (1-q) = 1 * (2 * d * (1-q)) := (one_mul _).symm
      _ ≤ (1+3^d) * (2*d*(1-q)) := by gcongr
      _ ≤ _ := hεθ
  have hk1 : k - 1 ≤ n := (Nat.sub_le k 1).trans hkn.le
  have hpow : (2:ℝ)^(k-1) ≤ (2:ℝ)^k :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le k 1)
  have hR4 : 0 ≤ R+4 := by linarith
  obtain ⟨N₁, hP₁, -, hN₁⟩ := wnGood_smallClusters_prob hκ hH hρ ξ hR
    hq0 hq1 hkn.le hθ1 hclosed (by simpa using h3) (wnBadDiameter k)
  obtain ⟨N₂, hP₂, -, hN₂⟩ := wnGood_smallClusters_prob hκ hH hρ ξ hR
    hq0 hq1 hk1 hθ1 hclosed (by simpa using h3) (wnBadDiameter (k-1))
  obtain ⟨N₃, hP₃, -, hN₃⟩ := wnNice_smallClusters_prob hκ hH hρ ξ hR
    hq0 hq1 (by omega : 1 ≤ k) hkn.le hθ1 hεθ h3 (wnRoughDiameter k)
  have hN₁' : (N₁:ℝ) ≤ 3*(R+4)*(2:ℝ)^k := by
    nlinarith [mul_nonneg hR4 (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k)]
  have hN₂' : (N₂:ℝ) ≤ 3*(R+4)*(2:ℝ)^k := by
    nlinarith [mul_nonneg hR4 (sub_nonneg.mpr hpow),
      mul_nonneg hR4 (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k)]
  have hB₁ := wnPeierls_numeric d k (wnBadDiameter k/2) N₁ R hR hN₁'
    (wnBadDiameter_num d k)
  have hB₂ := wnPeierls_numeric d k (wnBadDiameter (k-1)/2) N₂ R hR hN₂'
    (wnBadDiameter_prev_num d k hk)
  have hB₃ := wnPeierls_numeric d k (wnRoughDiameter k/2) N₃ R hR hN₃
    (wnRoughDiameter_num d k hk)
  have hA : P A ≤ (2:ℝ≥0∞) ^ (11000 + 3*(d:ℝ)^2) *
      ENNReal.ofReal ((1+R)^d) * (2:ℝ≥0∞)^(-(k:ℝ)^2/8) := hP₁.trans hB₁
  have hB : P B ≤ (2:ℝ≥0∞) ^ (11000 + 3*(d:ℝ)^2) *
      ENNReal.ofReal ((1+R)^d) * (2:ℝ≥0∞)^(-(k:ℝ)^2/8) := hP₂.trans hB₂
  have hC : P C ≤ (2:ℝ≥0∞) ^ (11000 + 3*(d:ℝ)^2) *
      ENNReal.ofReal ((1+R)^d) * (2:ℝ≥0∞)^(-(k:ℝ)^2/8) := hP₃.trans hB₃
  have hbad : wnBadAt P H ξ R q k n = A ∪ B ∪ C := by
    ext ω
    simp only [wnBadAt, A, B, C, Set.mem_ofPred_eq, Set.mem_union]
    tauto
  rw [hbad]
  calc
    P (A ∪ B ∪ C) ≤ P A + P B + P C := by
      exact (measure_union_le (A ∪ B) C).trans
        (by simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right (measure_union_le A B) (P C))
    _ ≤ 3 * ((2:ℝ≥0∞) ^ (11000 + 3*(d:ℝ)^2) *
        ENNReal.ofReal ((1+R)^d) * (2:ℝ≥0∞)^(-(k:ℝ)^2/8)) := by
      calc P A + P B + P C ≤
          ((2:ℝ≥0∞) ^ (11000 + 3*(d:ℝ)^2) *
          ENNReal.ofReal ((1+R)^d) * (2:ℝ≥0∞)^(-(k:ℝ)^2/8)) +
          ((2:ℝ≥0∞) ^ (11000 + 3*(d:ℝ)^2) *
          ENNReal.ofReal ((1+R)^d) * (2:ℝ≥0∞)^(-(k:ℝ)^2/8)) +
          ((2:ℝ≥0∞) ^ (11000 + 3*(d:ℝ)^2) *
          ENNReal.ofReal ((1+R)^d) * (2:ℝ≥0∞)^(-(k:ℝ)^2/8)) := by gcongr
        _ = _ := by ring

/-- Quadratic decay dominates a geometric series after any scale at least 110. -/
private theorem wnQuadraticTerm_le (s j : ℕ) (hs : 110 ≤ s) :
    (2:ℝ≥0∞)^(-((s+j:ℕ):ℝ)^2/8) ≤
      (2:ℝ≥0∞)^(-(s:ℝ)^2/8) * (2⁻¹:ℝ≥0∞)^j := by
  have hexp : -((s+j:ℕ):ℝ)^2/8 ≤ -(s:ℝ)^2/8 - (j:ℝ) := by
    push_cast
    have hsj : (0:ℝ) ≤ j := by positivity
    have hs' : (110:ℝ) ≤ s := by exact_mod_cast hs
    nlinarith [mul_nonneg (show 0 ≤ (s:ℝ)-4 by linarith) hsj]
  calc
    _ ≤ (2:ℝ≥0∞)^(-(s:ℝ)^2/8 - (j:ℝ)) :=
      ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = (2:ℝ≥0∞)^(-(s:ℝ)^2/8) * (2⁻¹:ℝ≥0∞)^j := by
      rw [sub_eq_add_neg, ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
      congr 1
      simpa [ENNReal.rpow_neg, ENNReal.rpow_natCast] using
        (ENNReal.inv_pow (a := (2:ℝ≥0∞)) (n := j))

/-- The bad-scale tail above the deterministic floor. -/
theorem wnBadScale_tail_large {d : ℕ} {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {ρ : ℝ}
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) (ξ : ℝ) {R : ℝ} (hR : 1 ≤ R) {q : ℝ≥0∞}
    (hq0 : 0 < q) (hq1 : q < 1) {n s : ℕ} (hs : 110 ≤ s)
    {θ : ℝ≥0∞} (hθ1 : θ ≤ 1)
    (hεθ : (1 + 3 ^ d) * (2 * (d : ℝ≥0∞) * (1 - q)) ≤
      θ ^ ((⌈2 * (2 + ρ)⌉₊ + 1) ^ d))
    (h3 : (3 : ℝ≥0∞) ^ d * θ ≤ 2⁻¹) :
    P {ω | s < wnBadScale P H ξ R q n ω} ≤
      6 * ((2:ℝ≥0∞) ^ (11000 + 3*(d:ℝ)^2) *
        ENNReal.ofReal ((1+R)^d) * (2:ℝ≥0∞)^(-(s:ℝ)^2/8)) := by
  classical
  let E : ℕ → Set Ω := fun j => if 110 ≤ s+j ∧ s+j < n then
    wnBadAt P H ξ R q (s+j) n else ∅
  have hsub : {ω | s < wnBadScale P H ξ R q n ω} ⊆ ⋃ j, E j := by
    intro ω hω
    have hex : ∃ k ∈ Finset.Ico 110 n, ω ∈ wnBadAt P H ξ R q k n ∧ s ≤ k := by
      by_contra hnone
      push Not at hnone
      have hsup : (Finset.Ico 110 n).sup
          (fun k => if ω ∈ wnBadAt P H ξ R q k n then k+1 else 0) ≤ s := by
        apply Finset.sup_le
        intro k hk
        split_ifs with hbad
        · have hks : k < s := hnone k hk hbad
          omega
        · omega
      have hM : wnBadScale P H ξ R q n ω ≤ s := by
        dsimp [wnBadScale]
        exact max_le hs hsup
      exact not_lt_of_ge hM hω
    obtain ⟨k, hk, hbad, hsk⟩ := hex
    have heq : s + (k-s) = k := by omega
    refine Set.mem_iUnion.mpr ⟨k-s, ?_⟩
    dsimp [E]
    rw [heq]
    simp [Finset.mem_Ico.mp hk, hbad]
  let T : ℝ≥0∞ := 3 * ((2:ℝ≥0∞) ^ (11000 + 3*(d:ℝ)^2) *
    ENNReal.ofReal ((1+R)^d) * (2:ℝ≥0∞)^(-(s:ℝ)^2/8))
  have hterm (j : ℕ) : P (E j) ≤ T * (2⁻¹:ℝ≥0∞)^j := by
    by_cases hcase : 110 ≤ s+j ∧ s+j < n
    · have hprob := wnBadAt_prob hκ hH hρ ξ hR hq0 hq1 hcase.1 hcase.2
        hθ1 hεθ h3
      have hquad := wnQuadraticTerm_le s j hs
      have hbound : P (wnBadAt P H ξ R q (s+j) n) ≤ T * (2⁻¹:ℝ≥0∞)^j := calc
        P (wnBadAt P H ξ R q (s+j) n) ≤
            3 * ((2:ℝ≥0∞) ^ (11000 + 3*(d:ℝ)^2) *
              ENNReal.ofReal ((1+R)^d) *
              (2:ℝ≥0∞)^(-((s+j:ℕ):ℝ)^2/8)) := hprob
        _ ≤ 3 * ((2:ℝ≥0∞) ^ (11000 + 3*(d:ℝ)^2) *
              ENNReal.ofReal ((1+R)^d) *
              ((2:ℝ≥0∞)^(-(s:ℝ)^2/8) * (2⁻¹:ℝ≥0∞)^j)) := by gcongr
        _ = T * (2⁻¹:ℝ≥0∞)^j := by dsimp [T]; ring
      simpa [E, hcase] using hbound
    · simp [E, hcase]
  calc
    P {ω | s < wnBadScale P H ξ R q n ω} ≤ P (⋃ j, E j) := measure_mono hsub
    _ ≤ ∑' j, P (E j) := measure_iUnion_le _
    _ ≤ ∑' j, T * (2⁻¹:ℝ≥0∞)^j := ENNReal.tsum_le_tsum hterm
    _ = T * 2 := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
    _ = 6 * ((2:ℝ≥0∞) ^ (11000 + 3*(d:ℝ)^2) *
        ENNReal.ofReal ((1+R)^d) * (2:ℝ≥0∞)^(-(s:ℝ)^2/8)) := by
          dsimp [T]
          ring

/-- The bad-scale cutoff has a quadratic tail, uniformly in the upper level. -/
theorem wnBadScale_tail {d : ℕ} {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {ρ : ℝ}
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) (ξ : ℝ) {R : ℝ} (hR : 1 ≤ R) {q : ℝ≥0∞}
    (hq0 : 0 < q) (hq1 : q < 1) (n s : ℕ)
    {θ : ℝ≥0∞} (hθ1 : θ ≤ 1)
    (hεθ : (1 + 3 ^ d) * (2 * (d : ℝ≥0∞) * (1 - q)) ≤
      θ ^ ((⌈2 * (2 + ρ)⌉₊ + 1) ^ d))
    (h3 : (3 : ℝ≥0∞) ^ d * θ ≤ 2⁻¹) :
    P {ω | s < wnBadScale P H ξ R q n ω} ≤
      6 * ((2:ℝ≥0∞) ^ (11000 + 3*(d:ℝ)^2) *
        ENNReal.ofReal ((1+R)^d) * (2:ℝ≥0∞)^(-(s:ℝ)^2/8)) := by
  by_cases hs : 110 ≤ s
  · exact wnBadScale_tail_large hκ hH hρ ξ hR hq0 hq1 hs hθ1 hεθ h3
  · letI : IsProbabilityMeasure P := hH.whiteNoise.isProbabilityMeasure
    have hs' : s ≤ 109 := by omega
    have hs2 : s^2 ≤ 109^2 := Nat.pow_le_pow_left hs' 2
    have hs2r : (s:ℝ)^2 ≤ 109^2 := by exact_mod_cast hs2
    have hexp : 0 ≤ (11000 + 3*(d:ℝ)^2) - (s:ℝ)^2/8 := by
      nlinarith [sq_nonneg (d:ℝ)]
    have htwo0 : (2:ℝ≥0∞) ≠ 0 := by norm_num
    have htwot : (2:ℝ≥0∞) ≠ ⊤ := by norm_num
    have hcoeff : (1:ℝ≥0∞) ≤ (2:ℝ≥0∞) ^ (11000 + 3*(d:ℝ)^2) *
        (2:ℝ≥0∞)^(-(s:ℝ)^2/8) := by
      rw [← ENNReal.rpow_add _ _ htwo0 htwot]
      have hexp' : 0 ≤ (11000 + 3*(d:ℝ)^2) + (-(s:ℝ)^2/8) := by
        nlinarith [hexp]
      simpa using ENNReal.rpow_le_rpow_of_exponent_le
        (x := (2:ℝ≥0∞)) (by norm_num) hexp'
    have hQ : (1:ℝ≥0∞) ≤ ENNReal.ofReal ((1+R)^d) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by linarith))
    have hfinal : (1:ℝ≥0∞) ≤
        6 * ((2:ℝ≥0∞) ^ (11000 + 3*(d:ℝ)^2) *
        ENNReal.ofReal ((1+R)^d) * (2:ℝ≥0∞)^(-(s:ℝ)^2/8)) := by
      calc
        1 ≤ (2:ℝ≥0∞) ^ (11000 + 3*(d:ℝ)^2) *
            (2:ℝ≥0∞)^(-(s:ℝ)^2/8) := hcoeff
        _ = 1 * ((2:ℝ≥0∞) ^ (11000 + 3*(d:ℝ)^2) * 1 *
            (2:ℝ≥0∞)^(-(s:ℝ)^2/8)) := by ring
        _ ≤ 6 * ((2:ℝ≥0∞) ^ (11000 + 3*(d:ℝ)^2) *
            ENNReal.ofReal ((1+R)^d) * (2:ℝ≥0∞)^(-(s:ℝ)^2/8)) := by
              gcongr
              norm_num
    have hmeasure : P {ω | s < wnBadScale P H ξ R q n ω} ≤ 1 := by
      calc
        P {ω | s < wnBadScale P H ξ R q n ω} ≤ P Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    exact hmeasure.trans hfinal

end HigherDimLQGContinuity
