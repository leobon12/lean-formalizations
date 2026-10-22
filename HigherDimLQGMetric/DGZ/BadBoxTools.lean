import HigherDimLQGMetric.DGZ.NiceBoxLaw
import HigherDimLQGMetric.DGZ.NiceBoxCert
import HigherDimLQGMetric.DGZ.NiceBoxOscBound

/-!
# DGZ §5.2: tools for the bad-box probabilities (packet L4a2)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), §5.2, Lemmas 5.5–5.9 (TeX l. 2158–2389);
planning audit `planning/audits/MA7-ref2-sections-4-6.md`, Details (a) D-5.5–5.9 and D-OSC;
blueprint Part C (`blueprint/sections/ref2-compare.tex`, `r2:lem:oscconds`,
`r2:lem:55`–`r2:lem:59`).

Generic ingredients of the union bounds and the scaling arguments of Lemmas 5.5–5.9:

* `BadBox.cube c M`: the lattice cube `{v ∈ ℤ^d : |v - c|_∞ ≤ M}` as a `Finset`, with
  `card = (2M + 1)^d` (`BadBox.card_cube`);
* `BadBox.measure_exists_le_sum`, `BadBox.measure_exists_le_card_mul`: union bounds for events
  `{∃ v, A v ∧ E v}` whose index condition `A` confines `v` to a finite set (outer measure: no
  measurability is needed);
* `BadBox.s_eq_pow_mul`: `s_j = 2^{(n-a_i)-(n-a_j)} s_i` with a natural-number factor, and the
  lattice descriptions of the boxes used by the nice-box conditions;
* `BadBox.measure_acrossDist_band_le_eq`: the scaled law of the across distance of a band
  `h_{m,n'}` on a shell of radii `r₁ 2^{-m}, r₂ 2^{-m}` (lower tail, `≤` form), from L3b1's
  `map_acrossDist_sim_eq`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox)

variable {d : ℕ}

namespace BadBox

/-! ## Lattice cubes -/

/-- The lattice cube `{v ∈ ℤ^d : |v_i - c_i| ≤ M for all i}` as a `Finset`. -/
def cube (c : Zd d) (M : ℕ) : Finset (Zd d) :=
  Fintype.piFinset fun i => Finset.Icc (c i - M) (c i + M)

theorem mem_cube {c v : Zd d} {M : ℕ} : v ∈ cube c M ↔ ∀ i, |v i - c i| ≤ M := by
  simp only [cube, Fintype.mem_piFinset, Finset.mem_Icc]
  refine forall_congr' fun i => ?_
  rw [abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem card_cube (c : Zd d) (M : ℕ) : (cube c M).card = (2 * M + 1) ^ d := by
  rw [cube, Fintype.card_piFinset]
  have e : ∀ i : Fin d, (Finset.Icc (c i - M) (c i + M)).card = 2 * M + 1 := by
    intro i
    rw [Int.card_Icc]
    omega
  rw [Finset.prod_congr rfl fun i _ => e i, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-! ## Union bounds -/

/-- **Union bound** over a finite index set: if the index condition `A v` forces `v ∈ F`, then
`P{∃ v, A v ∧ E v} ≤ ∑_{v ∈ F} P{E v}`. -/
theorem measure_exists_le_sum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {ι : Type*}
    (F : Finset ι) (A : ι → Prop) (E : ι → Ω → Prop) (hA : ∀ v, A v → v ∈ F) :
    P {ω | ∃ v, A v ∧ E v ω} ≤ ∑ v ∈ F, P {ω | E v ω} := by
  refine (measure_mono ?_).trans (measure_biUnion_finset_le F fun v => {ω | E v ω})
  rintro ω ⟨v, hv, hE⟩
  exact Set.mem_biUnion (hA v hv) hE

/-- **Union bound with a uniform bound**: `P{∃ v, A v ∧ E v} ≤ #F · b` when `A v → v ∈ F` and
`P{E v} ≤ b` for `v ∈ F`. -/
theorem measure_exists_le_card_mul {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {ι : Type*}
    (F : Finset ι) (A : ι → Prop) (E : ι → Ω → Prop) (hA : ∀ v, A v → v ∈ F) {b : ℝ≥0∞}
    (hb : ∀ v ∈ F, P {ω | E v ω} ≤ b) :
    P {ω | ∃ v, A v ∧ E v ω} ≤ F.card * b := by
  refine (measure_exists_le_sum P F A E hA).trans ?_
  calc ∑ v ∈ F, P {ω | E v ω} ≤ ∑ _v ∈ F, b := Finset.sum_le_sum hb
    _ = F.card * b := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ## Scales -/

/-- `s_j = 2^{(n - a_i) - (n - a_j)} s_i` (natural-number factor) when `n - a_j ≤ n - a_i`. -/
theorem s_eq_pow_mul (p : NiceParams) {i j : ℕ} (h : p.n - p.a j ≤ p.n - p.a i) :
    p.s j = ((2 ^ ((p.n - p.a i) - (p.n - p.a j)) : ℕ) : ℝ) * p.s i := by
  unfold NiceParams.s
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le h
  rw [he, Nat.add_sub_cancel_left, pow_add]
  push_cast
  rw [mul_left_comm, ← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow, mul_one]

/-- `s_i / s_j = 2^{-(a_j - a_i)}` when `a_i ≤ a_j ≤ n`. -/
theorem s_div_s_eq (p : NiceParams) {i j : ℕ} (hij : p.a i ≤ p.a j) (hjn : p.a j ≤ p.n) :
    p.s i / p.s j = (2 : ℝ)⁻¹ ^ (p.a j - p.a i) := by
  have hle : p.n - p.a j ≤ p.n - p.a i := Nat.sub_le_sub_left hij _
  rw [s_eq_pow_mul p hle]
  have hs := p.s_pos i
  have e : (p.n - p.a i) - (p.n - p.a j) = p.a j - p.a i := by omega
  rw [e, Nat.cast_pow, Nat.cast_ofNat, div_mul_cancel_right₀ hs.ne', inv_pow]

/-- `B_{s_i}(s_i v) ⊆ B_{s_j}(s_j u)` (`s_j = N s_i`) iff `v` lies in the lattice cube of radius
`N - 1` around `N u`. -/
theorem obox_subset_iff_mem_cube {s' : ℝ} (hs' : 0 < s') (N : ℕ) (hN : 1 ≤ N) (u v : Zd d) :
    obox (latPt s' v) s' ⊆ obox (latPt (N * s') u) (N * s') ↔ v ∈ cube ((N : ℤ) • u) (N - 1) := by
  rw [obox_latPt_subset_scale_iff hs' N u v, mem_cube]
  refine forall_congr' fun i => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  have : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by omega
  rw [this]

/-- `s_i v ∈ B_{s_j}(s_j u)` (`s_j = N s_i`) iff `v` lies in the lattice cube of radius `N - 1`
around `N u`. -/
theorem latPt_mem_obox_iff_mem_cube {s' : ℝ} (hs' : 0 < s') (N : ℕ) (hN : 1 ≤ N) (u w : Zd d) :
    latPt s' w ∈ obox (latPt (N * s') u) (N * s') ↔ w ∈ cube ((N : ℤ) • u) (N - 1) := by
  rw [latPt_mem_obox_iff hs' N u w, mem_cube]
  refine forall_congr' fun i => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  have : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by omega
  rw [this]
  omega

/-- `B_{s'}(s' v) ⊆ B_{R s'}(s' w)` iff `v` lies in the lattice cube of radius `R - 1` around `w`
(`R ≥ 1`). -/
theorem obox_subset_R_iff_mem_cube {s' : ℝ} (hs' : 0 < s') {R : ℕ} (hR : 1 ≤ R) (v w : Zd d) :
    obox (latPt s' v) s' ⊆ obox (latPt s' w) (R * s') ↔ v ∈ cube w (R - 1) := by
  rw [mul_comm (R : ℝ) s', obox_latPt_subset_iff hs', mem_cube]
  refine forall_congr' fun i => ?_
  have : ((R - 1 : ℕ) : ℤ) = (R : ℤ) - 1 := by omega
  rw [this]

/-- If `s' v ∈ B_{c N s'}(N s' u)` then `v` lies in the lattice cube of radius `c N` around
`N u`. -/
theorem mem_cube_of_latPt_mem_obox {s' : ℝ} (hs' : 0 < s') (N c : ℕ) (u v : Zd d)
    (h : latPt s' v ∈ obox (latPt (N * s') u) (c * (N * s'))) :
    v ∈ cube ((N : ℤ) • u) (c * N) := by
  rw [mem_cube]
  intro i
  have h1 := h i
  rw [latPt_apply, latPt_apply] at h1
  have e : s' * (v i : ℝ) - N * s' * (u i : ℝ) = s' * ((v i : ℝ) - N * u i) := by ring
  rw [e, abs_mul, abs_of_pos hs'] at h1
  have h2 : |(v i : ℝ) - N * u i| < c * N := by
    have : s' * |(v i : ℝ) - N * u i| < s' * (c * N) := by linarith
    exact lt_of_mul_lt_mul_left this hs'.le
  simp only [Pi.smul_apply, smul_eq_mul]
  have h3 : ((|v i - (N : ℤ) * u i| : ℤ) : ℝ) ≤ (((c * N : ℕ) : ℤ) : ℝ) := by
    push_cast
    exact h2.le
  exact_mod_cast h3

/-- If `s v ∈ B_ρ(0)` and `ρ ≤ M s`, then `v` lies in the lattice cube of radius `M` around `0`. -/
theorem mem_cube_zero_of_latPt_mem_obox {s ρ : ℝ} (hs : 0 < s) (M : ℕ) (hρ : ρ ≤ M * s)
    (v : Zd d) (h : latPt s v ∈ obox (0 : Rd d) ρ) : v ∈ cube 0 M := by
  rw [mem_cube]
  intro i
  have h1 := h i
  rw [latPt_apply] at h1
  have e : s * (v i : ℝ) - (0 : Rd d) i = s * (v i : ℝ) := by simp
  rw [e, abs_mul, abs_of_pos hs] at h1
  have h2 : |(v i : ℝ)| < M := by
    have : s * |(v i : ℝ)| < s * M := by linarith
    exact lt_of_mul_lt_mul_left this hs.le
  simp only [Pi.zero_apply, sub_zero]
  have h3 : ((|v i| : ℤ) : ℝ) ≤ ((M : ℤ) : ℝ) := by
    push_cast
    exact h2.le
  exact_mod_cast h3

/-! ## Scaled law of the across distance (lower tail) -/

/-- Two real random variables with the same law have the same lower tails (`≤` form). -/
theorem measure_le_eq_of_map_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ} (hX : Measurable X)
    (hY : Measurable Y) (h : P.map X = P'.map Y) (t : ℝ) :
    P {ω | X ω ≤ t} = P' {ω | Y ω ≤ t} := by
  have e1 : P {ω | X ω ≤ t} = P.map X (Iic t) := (Measure.map_apply hX measurableSet_Iic).symm
  have e2 : P' {ω | Y ω ≤ t} = P'.map Y (Iic t) := (Measure.map_apply hY measurableSet_Iic).symm
  rw [e1, e2, h]

section Scaled

variable {κ : Rd d → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
  {H : ℕ → Rd d → Ω → ℝ}

/-- **Scaled law of the across distance, lower tail** (MA7 D-5.5, D-5.6): for a version `G` of
`h_{m,n} = H_{2^{-n},2^{-m}}` (`m ≤ n`), any centre `w` and radii `r₁ 2^{-m}`, `r₂ 2^{-m}`:
`P[D(G)(across) ≤ t] = P[D_{n-m}(across B_{r₁}(0) \ B_{r₂}(0)) ≤ t / 2^{-m}]`. -/
theorem measure_acrossDist_band_le_eq (hκ : IsLFPPKernel κ) (hH : IsDyadicRealization κ P W H)
    {m n : ℕ} (hmn : m ≤ n) {G : Rd d → Ω → ℝ}
    (hG : IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ m) G) (ξ : ℝ) (w : Rd d)
    (r₁ r₂ t : ℝ) :
    P {ω | acrossDist ξ (fun z => G z ω) w (r₁ * (2 : ℝ)⁻¹ ^ m) (r₂ * (2 : ℝ)⁻¹ ^ m) ≤ t} =
      P {ω | acrossDist ξ (fun z => H (n - m) z ω) 0 r₁ r₂ ≤ t / (2 : ℝ)⁻¹ ^ m} := by
  have hr0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m := by positivity
  have hW := hH.whiteNoise
  have hmap := map_acrossDist_sim_eq hG (isBandVersion_scaled hH hmn) hW hW hκ w hr0
    (by positivity) ξ 0 r₁ r₂
  rw [smul_zero, add_zero, mul_comm ((2 : ℝ)⁻¹ ^ m) r₁, mul_comm ((2 : ℝ)⁻¹ ^ m) r₂] at hmap
  have hF : Measurable fun ω =>
      acrossDist ξ (fun z => G z ω) w (r₁ * (2 : ℝ)⁻¹ ^ m) (r₂ * (2 : ℝ)⁻¹ ^ m) :=
    measurable_acrossDist hG.continuous hG.measurable ξ w _ _
  have hF' : Measurable fun ω => (2 : ℝ)⁻¹ ^ m * acrossDist ξ (fun z => H (n - m) z ω) 0 r₁ r₂ :=
    (measurable_acrossDist (hH.band _).continuous (hH.band _).measurable ξ 0 r₁ r₂).const_mul _
  rw [measure_le_eq_of_map_eq hF hF' hmap t]
  congr 1
  ext ω
  simp only [mem_ofPred_eq]
  rw [le_div_iff₀ hr0, mul_comm]

end Scaled

end BadBox

end DGZ

end HigherDimLQGMetric
