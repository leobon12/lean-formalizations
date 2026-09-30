import QuantumZipper.Proofs.GFF.CoordRegKolm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-FIRSTMODE, step 2: a quantitative sup tail from the dyadic Kolmogorov chaining

Task N2Z-FIRSTMODE. For a process `Z` on `ℝ^d` (`d ≤ 4`) with continuous paths, the increment
moment bound `MomentBoundG Z P p a K (R+1)` of `KolmG` and pointwise moments `E|Z q|^p ≤ K` on
the box `boxD R`, we prove the tail bound (`kolm_sup_tail`)

`P(∃ q ∈ [-R,R]^d, (d/(1-θ) + 1) λ < |Z q|) ≤ (K/λ^p) ((2R+1)^d + d (2R+1)^d / (1 - ρ))`,

`ρ = 16 (1/2)^a / θ^p < 1`. Proof: apply the chaining of `KolmG` (`telescope_G'`,
`measure_badSetG_le`) to `Z/λ` from level `0`, plus Markov at the `(2R+1)^d` lattice points of
level `0`. This is the quantitative form of the Kolmogorov–Čentsov criterion (Revuz–Yor,
*Continuous Martingales and Brownian Motion*, 3rd ed., Ch. I, Thm (2.1), pp. 26–27, whose proof
bounds the Hölder constant on the complement of the bad events); the bookkeeping is own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace QuantumZipper
namespace D3Plus

open KolmD KolmG

variable {d : ℕ} {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- On all-good levels, the value at `q` is within `d/(1-θ)` of the level-0 rounding. -/
theorem abs_sub_rndD_zero_le_of_good (hθ0 : 0 < θ) (hθ1 : θ < 1) {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) {R : ℕ} (hg : ∀ j ≥ 0, GoodG θ f R j) {q : Fin d → ℝ}
    (hq : q ∈ boxD R) : |f q - f (rndD 0 q)| ≤ d / (1 - θ) := by
  have ht : Tendsto (fun M => rndD M q) atTop (𝓝 q) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun M => norm_rndD_sub_le M q) ?_
    simp_rw [one_div]
    exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hlim : Tendsto (fun M => |f (rndD M q) - f (rndD 0 q)|) atTop
      (𝓝 |f q - f (rndD 0 q)|) :=
    (((hf.tendsto q).comp ht).sub tendsto_const_nhds).abs
  refine le_of_tendsto hlim (Eventually.of_forall fun M => ?_)
  have h := telescope_G' hθ0 hθ1 hq hg le_rfl (Nat.zero_le M)
  simpa using h

/-- Scaling the moment bound. -/
theorem momentBoundG_div {Z : (Fin d → ℝ) → Ω → ℝ} {p : ℕ} {a K : ℝ} {R : ℕ}
    (hmom : MomentBoundG Z P p a K R) {c : ℝ} (hc : 0 < c) (hK : 0 ≤ K) :
    MomentBoundG (fun q ω => Z q ω / c) P p a (K / c ^ p) R := by
  intro q hq q' hq'
  have e : ∀ ω, ENNReal.ofReal (|Z q ω / c - Z q' ω / c| ^ p) =
      ENNReal.ofReal (|Z q ω - Z q' ω| ^ p) * ENNReal.ofReal ((c ^ p)⁻¹) := by
    intro ω
    rw [← ENNReal.ofReal_mul (by positivity), ← sub_div, abs_div, abs_of_pos hc,
      div_pow, div_eq_mul_inv]
  simp_rw [e]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  calc _ ≤ ENNReal.ofReal (K * ‖q - q'‖ ^ a) * ENNReal.ofReal ((c ^ p)⁻¹) := by
        gcongr; exact hmom q hq q' hq'
    _ = ENNReal.ofReal (K / c ^ p * ‖q - q'‖ ^ a) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

/-- The level-0 lattice of the box `R` has `(2R+1)^d` points. -/
theorem card_lattice0 (R : ℕ) :
    ((Fintype.piFinset fun _ : Fin d => Finset.Icc (-(R : ℤ)) R).card : ℝ) =
      (2 * (R : ℝ) + 1) ^ d := by
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Int.card_Icc]
  have h1 : (0 : ℤ) ≤ (R : ℤ) + 1 - -(R : ℤ) := by omega
  push_cast
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h1]; push_cast; ring

/-- **Quantitative sup tail** from the dyadic Kolmogorov chaining. -/
theorem kolm_sup_tail (hd : d ≤ 4) (hθ0 : 0 < θ) (hθ1 : θ < 1) {Z : (Fin d → ℝ) → Ω → ℝ}
    (hZc : ∀ ω, Continuous fun q => Z q ω) (hZ : ∀ q, AEMeasurable (Z q) P) {p : ℕ} {a K : ℝ}
    (ha : 0 ≤ a) (hK : 0 ≤ K) (hρ : 16 * ((1 / 2 : ℝ) ^ a / θ ^ p) < 1) {R : ℕ}
    (hmom : MomentBoundG Z P p a K (R + 1))
    (hpt : ∀ q ∈ boxD (d := d) R, ∫⁻ ω, ENNReal.ofReal (|Z q ω| ^ p) ∂P ≤ ENNReal.ofReal K)
    {l : ℝ} (hl : 0 < l) :
    P {ω | ∃ q ∈ boxD (d := d) R, (d / (1 - θ) + 1) * l < |Z q ω|} ≤
      ENNReal.ofReal (K / l ^ p * ((2 * R + 1) ^ d +
        d * (2 * R + 1) ^ d / (1 - 16 * ((1 / 2 : ℝ) ^ a / θ ^ p)))) := by
  classical
  set ρ : ℝ := 16 * ((1 / 2 : ℝ) ^ a / θ ^ p) with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have h1ρ : 0 < 1 - ρ := by linarith
  set Z' : (Fin d → ℝ) → Ω → ℝ := fun q ω => Z q ω / l with hZ'
  set K' : ℝ := K / l ^ p with hK'
  have hK'0 : 0 ≤ K' := by positivity
  have hmom' : MomentBoundG Z' P p a K' (R + 1) := momentBoundG_div hmom hl hK
  have hZ'm : ∀ q, AEMeasurable (Z' q) P := fun q => (hZ q).div_const l
  set S : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(R : ℤ)) R with hS
  set B : Set Ω := (⋃ j, badSetG Z' θ R j) ∪
    ⋃ b ∈ S, {ω | 1 < |Z' (lptD 0 b) ω - 0|} with hB
  have hsub : {ω | ∃ q ∈ boxD (d := d) R, (d / (1 - θ) + 1) * l < |Z q ω|} ⊆ B := by
    intro ω hω
    by_contra hnot
    simp only [hB, mem_union, mem_iUnion, not_or, not_exists, badSetG, mem_ofPred_eq,
      not_not, sub_zero, not_lt] at hnot
    obtain ⟨hgood, hlat⟩ := hnot
    obtain ⟨q, hq, hbig⟩ := hω
    have h1 := abs_sub_rndD_zero_le_of_good hθ0 hθ1 ((hZc ω).div_const l)
      (fun j _ => hgood j) hq
    have hmem : flr 0 q ∈ S := Fintype.mem_piFinset.2 fun i =>
      Finset.mem_Icc.2 (abs_le.1 (by simpa using inRange_flr hq 0 i))
    have h2 := hlat _ hmem
    have h3 : |Z' q ω| ≤ d / (1 - θ) + 1 := by
      have := abs_sub_abs_le_abs_sub (Z' q ω) (Z' (rndD 0 q) ω)
      simp only [rndD] at this h1
      simp only [hZ'] at *
      linarith
    have h4 : |Z q ω| ≤ (d / (1 - θ) + 1) * l := by
      simp only [hZ', abs_div, abs_of_pos hl] at h3
      rwa [div_le_iff₀ hl] at h3
    linarith
  have hbad : ∀ j, P (badSetG Z' θ R j) ≤ ENNReal.ofReal (d * (2 * R + 1) ^ d * K' * ρ ^ j) :=
    fun j => measure_badSetG_le hd hθ0 hZ'm ha hK'0 hmom' j
  have hlatb : ∀ b ∈ S, P {ω | 1 < |Z' (lptD 0 b) ω - 0|} ≤ ENNReal.ofReal K' := by
    intro b hb
    have hbR : lptD 0 b ∈ boxD (d := d) R := fun i => by
      have := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hb i)
      simp only [lptD, pow_zero, div_one]
      rw [abs_le]; constructor <;> exact_mod_cast (by omega : _)
    have hm : ∫⁻ ω, ENNReal.ofReal (|Z' (lptD 0 b) ω - 0| ^ p) ∂P ≤ ENNReal.ofReal K' := by
      have e : ∀ ω, ENNReal.ofReal (|Z' (lptD 0 b) ω - 0| ^ p) =
          ENNReal.ofReal (|Z (lptD 0 b) ω| ^ p) * ENNReal.ofReal ((l ^ p)⁻¹) := by
        intro ω
        rw [← ENNReal.ofReal_mul (by positivity), sub_zero, hZ', abs_div, abs_of_pos hl,
          div_pow, div_eq_mul_inv]
      simp_rw [e]
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hK', div_eq_mul_inv,
        ENNReal.ofReal_mul hK]
      gcongr; exact hpt _ hbR
    simpa using meas_gt_le_of_moment_G (hZ'm _) aemeasurable_const one_pos hm
  have hgeom : ∑' j, ENNReal.ofReal (d * (2 * R + 1) ^ d * K' * ρ ^ j) =
      ENNReal.ofReal (d * (2 * R + 1) ^ d * K' / (1 - ρ)) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
      ((summable_geometric_of_lt_one hρ0 hρ).mul_left _), tsum_mul_left,
      tsum_geometric_of_lt_one hρ0 hρ, div_eq_mul_inv]
  calc P {ω | ∃ q ∈ boxD (d := d) R, (d / (1 - θ) + 1) * l < |Z q ω|}
      ≤ P B := measure_mono hsub
    _ ≤ P (⋃ j, badSetG Z' θ R j) + P (⋃ b ∈ S, {ω | 1 < |Z' (lptD 0 b) ω - 0|}) :=
        measure_union_le _ _
    _ ≤ ∑' j, ENNReal.ofReal (d * (2 * R + 1) ^ d * K' * ρ ^ j) +
          ∑ b ∈ S, ENNReal.ofReal K' :=
        add_le_add ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hbad))
          ((measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum hlatb))
    _ = ENNReal.ofReal (K / l ^ p * ((2 * R + 1) ^ d +
          d * (2 * R + 1) ^ d / (1 - ρ))) := by
        rw [hgeom, Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), card_lattice0,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [hK']; ring

end D3Plus
end QuantumZipper
