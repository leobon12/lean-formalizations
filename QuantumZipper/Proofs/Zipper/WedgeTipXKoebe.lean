import QuantumZipper.Proofs.RS.KoebeLoewnerTime
import QuantumZipper.Proofs.RS.TraceShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# TIP-X, part (1), analytic input: a polynomial lower bound for univalent maps omitting `0`

For `f` injective and holomorphic on `ℍ` with `0 ∉ f(ℍ)` and `Y, R > 0` there are `c > 0` and
`N : ℕ` with `c · (Im u)^N ≤ ‖f u‖` for all `u ∈ ℍ` with `Im u ≤ Y`, `|Re u| ≤ R`
(`WedgeUnzip.exists_pow_le_norm_of_univalent`). Applied to `E_t = f_t⁻¹` (`fwdMapInv`, which maps
`ℍ` into `ℍ`) this gives `log ‖E_t u‖ ≥ log c − N |log Im u|` on bounded sets: the function
`ψ_t = −γ log ‖E_t‖` of TIP-X has at worst a `|log Im u|` singularity at `ℝ`, for **every**
`t ≥ 0` and without any SLE-specific input.

Proof. Koebe's estimate (Garnett–Marshall, *Harmonic Measure*, Ch. I, Thm 4.3 (4.13), p. 20:
`c₁ · Im u · ‖f'(u)‖ ≤ dist(f u, ∂f(ℍ)) ≤ ‖f u‖`, the last since `0 ∉ f(ℍ)`; repo
`CA.Koebe.infDist_compl_image_ge`) and the distortion chain KD(a) (Kemppainen, *Schramm–Loewner
Evolution*, Lemma 6.6, repo `RS.kd_distortion`): `‖f'(iY)‖ ≤ C^{n+1} ‖f'(iy)‖` along the
`n ≈ log₂(Y/y)` dyadic vertical steps, and `‖f'(iy)‖ ≤ C (1 + x²)^C ‖f'(y(x + i))‖`. Hence
`‖f'(u)‖ ≳ (Im u)^{m + 2m'}` and `‖f u‖ ≳ (Im u)^{1 + m + 2m'}`. Standard (Pommerenke,
*Univalent Functions*, 1975, Thm 1.3 / Cor 1.4 in disc form: `|f(z)| ≥ |f'(0)|(1 − |z|)²/…` for
univalent `f` omitting `0`); the half-plane chaining with non-sharp constants is our own.
-/

noncomputable section

open Set Metric Filter Complex
open scoped Topology

namespace QuantumZipper
namespace WedgeUnzip

/-- Vertical dyadic chain: `‖f'(iY)‖ ≤ C^n ‖f'(i 2^{-n} Y)‖`. -/
theorem norm_deriv_le_pow_vertical {f : ℂ → ℂ} {C : ℝ} (hC : 1 ≤ C)
    (hkd : ∀ y : ℝ, 0 < y → ∀ s ∈ Icc (1 / 2 : ℝ) 2,
      ‖deriv f ((y : ℂ) * I)‖ ≤ C * ‖deriv f ((s * y : ℝ) * I)‖)
    {Y : ℝ} (hY : 0 < Y) (n : ℕ) :
    ‖deriv f ((Y : ℂ) * I)‖ ≤ C ^ n * ‖deriv f ((((2 : ℝ) ^ n)⁻¹ * Y : ℝ) * I)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hy : 0 < ((2 : ℝ) ^ n)⁻¹ * Y := by positivity
    have h := hkd _ hy (1 / 2) ⟨le_rfl, by norm_num⟩
    have e : (1 / 2 : ℝ) * (((2 : ℝ) ^ n)⁻¹ * Y) = ((2 : ℝ) ^ (n + 1))⁻¹ * Y := by
      rw [pow_succ]; ring
    rw [e] at h
    calc ‖deriv f ((Y : ℂ) * I)‖ ≤ C ^ n * ‖deriv f ((((2 : ℝ) ^ n)⁻¹ * Y : ℝ) * I)‖ := ih
      _ ≤ C ^ n * (C * ‖deriv f ((((2 : ℝ) ^ (n + 1))⁻¹ * Y : ℝ) * I)‖) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = C ^ (n + 1) * ‖deriv f ((((2 : ℝ) ^ (n + 1))⁻¹ * Y : ℝ) * I)‖ := by ring

/-- **Polynomial lower bound for a univalent map of `ℍ` omitting `0`.** -/
theorem exists_pow_le_norm_of_univalent {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im}) (hinj : InjOn f {z : ℂ | 0 < z.im})
    (h0 : ∀ z : ℂ, 0 < z.im → f z ≠ 0) {Y R : ℝ} (hY : 0 < Y) (hR : 0 ≤ R) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ u : ℂ, 0 < u.im → u.im ≤ Y → |u.re| ≤ R →
      c * u.im ^ N ≤ ‖f u‖ := by
  obtain ⟨C, hC1, hkd⟩ := RS.kd_distortion
  have hC0 : 0 < C := by linarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, C ≤ 2 ^ m := pow_unbounded_of_one_lt C (by norm_num) |>.imp
    fun _ h => h.le
  obtain ⟨m', hm'⟩ : ∃ m' : ℕ, C ≤ m' := exists_nat_ge C
  have hYI : 0 < ((Y : ℂ) * I).im := by simpa using hY
  set D := ‖deriv f ((Y : ℂ) * I)‖ with hD
  have hDpos : 0 < D := norm_pos_iff.2
    (CA.Koebe.deriv_ne_zero_of_injOn CA.Koebe.isOpen_upperHalfPlaneSet hd hinj hYI)
  set K : ℝ := Y ^ 2 + R ^ 2 with hK
  have hK1 : 0 < K := by positivity
  refine ⟨CA.Koebe.koebeCovConst * D / (C ^ 2 * K ^ m' * Y ^ m), by
    have := CA.Koebe.koebeCovConst_pos; positivity, 1 + m + 2 * m', fun u hu huY huR => ?_⟩
  set y := u.im with hydef
  set x := u.re / y with hxdef
  have hux : u = (y : ℂ) * ((x : ℂ) + I) := by
    have hu0 : u.im ≠ 0 := ne_of_gt hu
    apply Complex.ext <;> simp [hxdef, hydef] <;> field_simp [hu0]
  -- vertical chain down to height `y`
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := Y / y) (y := 2)
    ((one_le_div hu).2 huY) (by norm_num)
  have hvert := norm_deriv_le_pow_vertical hC1 (fun y hy s hs => ((hkd f hd hinj y hy 0).1 s hs).2)
    hY n
  set y' := ((2 : ℝ) ^ n)⁻¹ * Y with hy'
  have hy'pos : 0 < y' := by positivity
  set s := y / y' with hs
  have hsy : s * y' = y := by rw [hs]; field_simp
  have hs1 : 1 / 2 ≤ s := by
    rw [hs, hy', le_div_iff₀ (by positivity)]
    rw [div_lt_iff₀ hu] at hn2
    have : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
    rw [this] at hn2
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    calc 1 / 2 * (((2 : ℝ) ^ n)⁻¹ * Y) = Y / (2 * 2 ^ n) := by field_simp
      _ ≤ y := by rw [div_le_iff₀ (by positivity)]; linarith
  have hs2 : s ≤ 2 := by
    rw [hs, hy', div_le_iff₀ (by positivity)]
    rw [le_div_iff₀ hu] at hn1
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    calc y ≤ Y / 2 ^ n := by rw [le_div_iff₀ h2n]; linarith
      _ ≤ 2 * (((2 : ℝ) ^ n)⁻¹ * Y) := by
          rw [div_eq_mul_inv, mul_comm Y]; nlinarith [inv_pos.2 h2n]
  have hstep := ((hkd f hd hinj y' hy'pos 0).1 s ⟨hs1, hs2⟩).2
  rw [hsy] at hstep
  have hhor := (hkd f hd hinj y hu x).2.2
  rw [← hux] at hhor
  -- the numeric factors
  have hCn : C ^ n ≤ (Y / y) ^ m := by
    calc C ^ n ≤ ((2 : ℝ) ^ m) ^ n := pow_le_pow_left₀ hC0.le hm n
      _ = ((2 : ℝ) ^ n) ^ m := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (Y / y) ^ m := pow_le_pow_left₀ (by positivity) hn1 m
  have hx2 : 1 + x ^ 2 ≤ K / y ^ 2 := by
    rw [le_div_iff₀ (by positivity), hxdef, hK]
    have hre : u.re ^ 2 ≤ R ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) huR 2
    have hy2 : y ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ hu.le huY 2
    have : (1 + (u.re / y) ^ 2) * y ^ 2 = y ^ 2 + u.re ^ 2 := by field_simp
    rw [this]; linarith
  have hxC : (1 + x ^ 2) ^ C ≤ (K / y ^ 2) ^ m' := by
    calc (1 + x ^ 2) ^ C ≤ (1 + x ^ 2) ^ (m' : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by nlinarith) hm'
      _ = (1 + x ^ 2) ^ m' := Real.rpow_natCast _ _
      _ ≤ (K / y ^ 2) ^ m' := pow_le_pow_left₀ (by positivity) hx2 m'
  -- `D ≤ C^{n+2} (1+x²)^C ‖f' u‖`
  have hDu : D ≤ C ^ 2 * (Y / y) ^ m * (K / y ^ 2) ^ m' * ‖deriv f u‖ := by
    have hfu := norm_nonneg (deriv f u)
    have h1 : D ≤ C ^ n * (C * (C * (1 + x ^ 2) ^ C * ‖deriv f u‖)) :=
      hvert.trans (mul_le_mul_of_nonneg_left (hstep.trans
        (mul_le_mul_of_nonneg_left hhor hC0.le)) (by positivity))
    calc D ≤ C ^ n * (C * (C * (1 + x ^ 2) ^ C * ‖deriv f u‖)) := h1
      _ = C ^ 2 * C ^ n * (1 + x ^ 2) ^ C * ‖deriv f u‖ := by ring
      _ ≤ C ^ 2 * (Y / y) ^ m * (K / y ^ 2) ^ m' * ‖deriv f u‖ := by gcongr
  -- Koebe: `c₁ y ‖f' u‖ ≤ ‖f u‖`
  have hkoebe := CA.Koebe.infDist_compl_image_ge hd hinj (z := u) hu
  have h0mem : (0 : ℂ) ∈ (f '' {z : ℂ | 0 < z.im})ᶜ := by
    rintro ⟨z, hz, hfz⟩; exact h0 z hz hfz
  have hdist : infDist (f u) (f '' {z : ℂ | 0 < z.im})ᶜ ≤ ‖f u‖ := by
    simpa using infDist_le_dist_of_mem h0mem (x := f u)
  have hfu : CA.Koebe.koebeCovConst * y * ‖deriv f u‖ ≤ ‖f u‖ := hkoebe.trans hdist
  have hc1 := CA.Koebe.koebeCovConst_pos
  have hyN : y ^ (1 + m + 2 * m') * (C ^ 2 * (Y / y) ^ m * (K / y ^ 2) ^ m') =
      y * (C ^ 2 * K ^ m' * Y ^ m) := by
    rw [div_pow, div_pow, ← pow_mul]
    field_simp
    ring
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  calc CA.Koebe.koebeCovConst * D * y ^ (1 + m + 2 * m')
      ≤ CA.Koebe.koebeCovConst * (C ^ 2 * (Y / y) ^ m * (K / y ^ 2) ^ m' * ‖deriv f u‖) *
          y ^ (1 + m + 2 * m') := by gcongr
    _ = CA.Koebe.koebeCovConst * y * ‖deriv f u‖ * (C ^ 2 * K ^ m' * Y ^ m) := by
        linear_combination (CA.Koebe.koebeCovConst * ‖deriv f u‖) * hyN
    _ ≤ ‖f u‖ * (C ^ 2 * K ^ m' * Y ^ m) := by gcongr

/-- **The lower bound for `E_t = f_t⁻¹`.** -/
theorem exists_pow_le_norm_fwdMapInv {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {Y R : ℝ} (hY : 0 < Y) (hR : 0 ≤ R) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ u : ℂ, 0 < u.im → u.im ≤ Y → |u.re| ≤ R →
      c * u.im ^ N ≤ ‖fwdMapInv W t u‖ :=
  exists_pow_le_norm_of_univalent (RS.differentiableOn_fwdMapInv hW hW0 ht)
    (RS.injOn_fwdMapInv hW hW0 ht)
    (fun z hz h => by
      have := RS.fwdMapInv_mem_H hW hW0 ht (w := z) hz
      rw [h] at this; simp [H] at this) hY hR

end WedgeUnzip
end QuantumZipper
