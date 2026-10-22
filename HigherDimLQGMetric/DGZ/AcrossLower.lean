import HigherDimLQGMetric.DGZ.AcrossAroundTools
import HigherDimLQGMetric.DGZ.Lemma36Dyadic

/-!
# DGZ Prop 4.8, lower half (packet L3c3; MA7 D-4.8)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Prop 4.8 (TeX l. 1683–1791, pp. 33–35);
planning audit `planning/audits/MA7-ref2-sections-4-6.md`, §5 row L3c3, gap G8 and Details (a)
D-4.8; the target shape `AcrossLowerShape` is copied **verbatim** from MA7 Details (c) §E (durable
copy `planning/audits/statements/MA7Statements.lean.txt`).

Main results:
* `AcrossLowerShape` (definition, verbatim) and `acrossLowerShape : AcrossLowerShape d κ ξ Q` (for
  all `d, κ, ξ, Q`): under `DGZHyp d κ ξ Q`, for every `δ > 0` there is `C` with
  `P*[D_n(across B₂(0) \ B₁(0)) < 2^{-(1-ξQ+δ)n}] ≤ C e^{-n/C}` for every dyadic realization and
  every `n`;
* the covering inequality `inf'_setDist_le_acrossDist`: for the grid of mesh `s = 2^{-k}`,
  `min_{y,x} D(B̄_s(s y), B̄_s(s x); B₃(0)) ≤ D(across B₂ \ B₁)`, the minimum over the inner sites
  `y` (`|s y|_∞ ≤ 1`) and the outer sites `x` (`2 - s ≤ |s x|_∞ ≤ 2`).

Proof (MA7 D-4.8). `g = ξ(Q - √(2d))/4`, `ε = min(1/2, δ²/(32 d ξ²))`, `m = ⌊ε n⌋`,
`δ' = min(g ε, δ/4)`, grid mesh `s = 2^{-(m+1)}`. For a pair `(a, b) = (s y, s x)`:
`S ≥ D_n(a, b; B₃) - Y_a - Y_b` with `Y_w = selfDiam_n(B_{2s}(w))`. Lemma 3.6 (lower half, `δ'`)
bounds `D_n(a,b;B₃)` below; on `𝒢_m` (`sup_{B̄₃} h_m ≤ m (Q - 3g/ξ) log 2`, L3c1) and with
`h_n = h_m + (h_n - h_m)`, `Y_w ≤ 2^{(ξQ - 3g)m} selfDiam(h_n - h_m)(B_{2^{-m}}(w))`, whose law is
that of `2^{-m} selfDiam_{n-m}(B₁(0))` (scaling) and D-4.7s with `δ'' = g ε` applies. So
`P[S < t₀] ≤ 1/4` with `t₀ = 2^{-(1-ξQ+δ')n}/2`; D-4.6 for `log S` (`K = B̄₃(0)`) gives
`P[S < 2^{-(1-ξQ+δ)n}] ≤ 2 e^{-δ² n log 2/(8ξ²)}`; a union bound over `≤ 2^{2d(m+4)}` pairs gives
`2·2^{8d} e^{-δ² n log 2/(16 ξ²)}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox roundLat convex_obox isOpen_obox
  obox_subset_cbox abs_latPt_roundLat_le abs_latPt_roundLat_sub_lt)
open HigherDimLFPP.Conc (quantileConst)

variable {d : ℕ}

/-! ### The target shape (MA7 Details (c) §E, verbatim) -/

/-- **DGZ Prop 4.8, lower half** (MA7 D-4.8): `D_n(across B₂ \ B₁) ≥ 2^{-(1-ξQ+δ)n}` outside an
exponentially small event -/
def AcrossLowerShape (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) : Prop :=
  DGZHyp d κ ξ Q → ∀ δ > 0, ∃ C > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
      P {ω | acrossDist ξ (fun z => H n z ω) 0 2 1 < (2 : ℝ) ^ (-(1 - ξ * Q + δ) * n)} ≤
        ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C))

/-! ### Grid sites covering the spheres `∂B₁(0)` and `∂B₂(0)` -/

open Classical in
/-- the inner grid sites of mesh `s = 2^{-k}`: `|s y|_∞ ≤ 1` (their closed `s`-boxes cover
`∂B₁(0)`) -/
def innerSites (d k : ℕ) : Finset (Zd d) :=
  (boxF 0 (2 ^ (k + 1))).filter fun y => ∀ i, |latPt ((2 : ℝ)⁻¹ ^ k) y i| ≤ 1

open Classical in
/-- the outer grid sites of mesh `s = 2^{-k}`: `|s x|_∞ ≤ 2` and `|s x_i| ≥ 2 - s` for some `i`
(their closed `s`-boxes cover `∂B₂(0)`) -/
def outerSites (d k : ℕ) : Finset (Zd d) :=
  (boxF 0 (2 ^ (k + 1))).filter fun x =>
    (∀ i, |latPt ((2 : ℝ)⁻¹ ^ k) x i| ≤ 2) ∧ ∃ i, 2 - (2 : ℝ)⁻¹ ^ k ≤ |latPt ((2 : ℝ)⁻¹ ^ k) x i|

lemma mem_innerSites {k : ℕ} {y : Zd d} :
    y ∈ innerSites d k ↔
      WithinInf ((2 ^ (k + 1) : ℕ) : ℤ) y 0 ∧ ∀ i, |latPt ((2 : ℝ)⁻¹ ^ k) y i| ≤ 1 := by
  unfold innerSites
  rw [Finset.mem_filter, mem_boxF]

lemma mem_outerSites {k : ℕ} {x : Zd d} :
    x ∈ outerSites d k ↔ WithinInf ((2 ^ (k + 1) : ℕ) : ℤ) x 0 ∧
      (∀ i, |latPt ((2 : ℝ)⁻¹ ^ k) x i| ≤ 2) ∧
        ∃ i, 2 - (2 : ℝ)⁻¹ ^ k ≤ |latPt ((2 : ℝ)⁻¹ ^ k) x i| := by
  unfold outerSites
  rw [Finset.mem_filter, mem_boxF]

/-- A site with `|2^{-k} x|_∞ ≤ 2` lies in the lattice box of radius `2^{k+1}`. -/
lemma withinInf_of_abs_latPt_le {k : ℕ} {x : Zd d}
    (h : ∀ i, |latPt ((2 : ℝ)⁻¹ ^ k) x i| ≤ 2) : WithinInf ((2 ^ (k + 1) : ℕ) : ℤ) x 0 := by
  intro i
  have h1 := h i
  rw [latPt_apply, abs_mul, abs_of_pos (by positivity)] at h1
  have e : (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ k = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow]
  have h2 : |((x i : ℤ) : ℝ)| ≤ (2 : ℝ) ^ (k + 1) := by
    calc |((x i : ℤ) : ℝ)| = (2 : ℝ) ^ k * ((2 : ℝ)⁻¹ ^ k * |((x i : ℤ) : ℝ)|) := by
          rw [← mul_assoc, e, one_mul]
      _ ≤ (2 : ℝ) ^ k * 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (2 : ℝ) ^ (k + 1) := by ring
  simp only [Pi.zero_apply, sub_zero]
  exact_mod_cast h2

/-- The closed `s`-boxes of the inner sites cover `∂B₁(0)`. -/
lemma lsph_one_subset_iUnion (k : ℕ) :
    lsph (0 : Rd d) 1 ⊆
      ⋃ y ∈ innerSites d k, cbox (latPt ((2 : ℝ)⁻¹ ^ k) y) ((2 : ℝ)⁻¹ ^ k) := by
  intro z hz
  have hs : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  have hz1 : ∀ i, |z i| ≤ 1 := fun i => by
    have := (mem_lsph.1 hz).1 i
    simpa using this
  have hy : ∀ i, |latPt ((2 : ℝ)⁻¹ ^ k) (roundLat ((2 : ℝ)⁻¹ ^ k) z) i| ≤ 1 := fun i =>
    (abs_latPt_roundLat_le hs z i).trans (hz1 i)
  refine mem_iUnion₂.2 ⟨roundLat ((2 : ℝ)⁻¹ ^ k) z, mem_innerSites.2
    ⟨withinInf_of_abs_latPt_le fun i => (hy i).trans one_le_two, hy⟩, fun i => ?_⟩
  rw [abs_sub_comm]
  exact (abs_latPt_roundLat_sub_lt hs z i).le

/-- The closed `s`-boxes of the outer sites cover `∂B₂(0)`. -/
lemma lsph_two_subset_iUnion (k : ℕ) :
    lsph (0 : Rd d) 2 ⊆
      ⋃ x ∈ outerSites d k, cbox (latPt ((2 : ℝ)⁻¹ ^ k) x) ((2 : ℝ)⁻¹ ^ k) := by
  intro z hz
  have hs : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  have hz2 : ∀ i, |z i| ≤ 2 := fun i => by
    have := (mem_lsph.1 hz).1 i
    simpa using this
  obtain ⟨j, hj⟩ : ∃ j, 2 ≤ |z j| := by
    have h := (mem_lsph.1 hz).2
    rw [mem_obox] at h
    push Not at h
    obtain ⟨j, hj⟩ := h
    exact ⟨j, by simpa using hj⟩
  have hx : ∀ i, |latPt ((2 : ℝ)⁻¹ ^ k) (roundLat ((2 : ℝ)⁻¹ ^ k) z) i| ≤ 2 := fun i =>
    (abs_latPt_roundLat_le hs z i).trans (hz2 i)
  have hxj : 2 - (2 : ℝ)⁻¹ ^ k ≤ |latPt ((2 : ℝ)⁻¹ ^ k) (roundLat ((2 : ℝ)⁻¹ ^ k) z) j| := by
    have h1 := abs_latPt_roundLat_sub_lt hs z j
    have h2 := abs_sub_abs_le_abs_sub (z j) (latPt ((2 : ℝ)⁻¹ ^ k) (roundLat ((2 : ℝ)⁻¹ ^ k) z) j)
    rw [abs_sub_comm] at h1
    linarith
  refine mem_iUnion₂.2 ⟨roundLat ((2 : ℝ)⁻¹ ^ k) z, mem_outerSites.2
    ⟨withinInf_of_abs_latPt_le hx, hx, j, hxj⟩, fun i => ?_⟩
  rw [abs_sub_comm]
  exact (abs_latPt_roundLat_sub_lt hs z i).le

/-- The index set of pairs is nonempty (`d ≥ 1`). -/
lemma innerSites_prod_outerSites_nonempty (hd : 1 ≤ d) (k : ℕ) :
    (innerSites d k ×ˢ outerSites d k).Nonempty := by
  obtain ⟨z, hz⟩ := lsph_nonempty (d := d) hd 0 zero_le_two
  obtain ⟨x, hx, -⟩ := mem_iUnion₂.1 (lsph_two_subset_iUnion k hz)
  refine ⟨(0, x), Finset.mem_product.2 ⟨mem_innerSites.2 ⟨fun i => ?_, fun i => ?_⟩, hx⟩⟩
  · simp
  · rw [HigherDimLFPP.DGZ.latPt_zero]
    simp

/-- **The covering inequality** (MA7 D-4.8): minimizing paths for the across distance can be taken
in the closed shell, hence in `B₃(0)`; covering the two spheres by closed `s`-boxes gives
`min_{(y,x)} D(B̄_s(s y), B̄_s(s x); B₃(0)) ≤ D(across B₂(0) \ B₁(0))`. -/
theorem inf'_setDist_le_acrossDist (hd : 1 ≤ d) {ξ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ)
    (k : ℕ) :
    (innerSites d k ×ˢ outerSites d k).inf' (innerSites_prod_outerSites_nonempty hd k)
      (fun p => lfppSetDist ξ φ (obox 0 3) (cbox (latPt ((2 : ℝ)⁻¹ ^ k) p.1) ((2 : ℝ)⁻¹ ^ k))
        (cbox (latPt ((2 : ℝ)⁻¹ ^ k) p.2) ((2 : ℝ)⁻¹ ^ k))) ≤ acrossDist ξ φ 0 2 1 := by
  refine (inf'_le_lfppSetDist_of_subset _ _ _ _ _ (lsph_one_subset_iUnion k)
    (lsph_two_subset_iUnion k) (lsph_nonempty hd 0 zero_le_one)
    (lsph_nonempty hd 0 zero_le_two)).trans ?_
  exact lfppSetDist_lsph_le_acrossDist hφ one_lt_two fun z hz =>
    cbox_subset_obox (by norm_num : (2 : ℝ) < 3) hz.1

/-! ### Geometry of a pair of sites -/

section Pair

variable {k : ℕ} {y x : Zd d}

lemma latPt_inner_mem_cbox (hy : y ∈ innerSites d k) :
    latPt ((2 : ℝ)⁻¹ ^ k) y ∈ cbox (0 : Rd d) 2 := fun i => by
  have := (mem_innerSites.1 hy).2 i
  simp only [PiLp.zero_apply, sub_zero]
  linarith

lemma latPt_outer_mem_cbox (hx : x ∈ outerSites d k) :
    latPt ((2 : ℝ)⁻¹ ^ k) x ∈ cbox (0 : Rd d) 2 := fun i => by
  have := (mem_outerSites.1 hx).2.1 i
  simp only [PiLp.zero_apply, sub_zero]
  exact this

/-- the two points of a pair are `ℓ^∞`-far apart (`s ≤ 1/2`) -/
lemma exists_half_le_abs_sub (hk : 1 ≤ k) (hy : y ∈ innerSites d k) (hx : x ∈ outerSites d k) :
    ∃ i, (1 : ℝ) / 2 ≤ |latPt ((2 : ℝ)⁻¹ ^ k) y i - latPt ((2 : ℝ)⁻¹ ^ k) x i| := by
  obtain ⟨-, -, j, hj⟩ := mem_outerSites.1 hx
  have hyj := (mem_innerSites.1 hy).2 j
  have hs : (2 : ℝ)⁻¹ ^ k ≤ 1 / 2 := by
    calc (2 : ℝ)⁻¹ ^ k ≤ (2 : ℝ)⁻¹ ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      _ = 1 / 2 := by norm_num
  refine ⟨j, ?_⟩
  have := abs_sub_abs_le_abs_sub (latPt ((2 : ℝ)⁻¹ ^ k) x j) (latPt ((2 : ℝ)⁻¹ ^ k) y j)
  rw [abs_sub_comm] at this
  linarith

/-- a box of radius `2s ≤ 1/2` around a point of `B̄₂(0)` lies in `B₃(0)` -/
lemma obox_subset_obox_three {a : Rd d} (ha : a ∈ cbox (0 : Rd d) 2) {r : ℝ} (hr : r ≤ 1 / 2) :
    obox a r ⊆ obox (0 : Rd d) 3 := fun z hz i => by
  have h1 := hz i
  have h2 := ha i
  simp only [PiLp.zero_apply, sub_zero] at h2 ⊢
  have := abs_sub_abs_le_abs_sub (z i) (a i)
  linarith

/-- the closed `s`-boxes of a pair are disjoint (`s ≤ 1/4`) -/
lemma disjoint_cbox_pair (hk : 2 ≤ k) (hy : y ∈ innerSites d k) (hx : x ∈ outerSites d k) :
    Disjoint (cbox (latPt ((2 : ℝ)⁻¹ ^ k) y) ((2 : ℝ)⁻¹ ^ k))
      (cbox (latPt ((2 : ℝ)⁻¹ ^ k) x) ((2 : ℝ)⁻¹ ^ k)) := by
  obtain ⟨-, -, j, hj⟩ := mem_outerSites.1 hx
  have hyj := (mem_innerSites.1 hy).2 j
  have hs : (2 : ℝ)⁻¹ ^ k ≤ 1 / 4 := by
    calc (2 : ℝ)⁻¹ ^ k ≤ (2 : ℝ)⁻¹ ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      _ = 1 / 4 := by norm_num
  refine Set.disjoint_left.2 fun z hz1 hz2 => ?_
  have h1 := hz1 j
  have h2 := hz2 j
  have h3 := abs_sub_abs_le_abs_sub (latPt ((2 : ℝ)⁻¹ ^ k) x j) (latPt ((2 : ℝ)⁻¹ ^ k) y j)
  have h4 := abs_sub_le (latPt ((2 : ℝ)⁻¹ ^ k) x j) (z j) (latPt ((2 : ℝ)⁻¹ ^ k) y j)
  rw [abs_sub_comm (latPt ((2 : ℝ)⁻¹ ^ k) x j) (z j)] at h4
  linarith

end Pair

/-! ### One pair of boxes -/

section PairProb

variable {κ : Rd d → ℝ} {ξ Q : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}

/-- **The bad events of a pair** (MA7 D-4.8 (1)): `S ≥ D_n(a, b; B₃) - Y_a - Y_b`
(`lfppDistOn_le_selfDiam_add_lfppSetDist`) and, on `𝒢_m` (with `h_n = h_m + (h_n - h_m)`),
`Y_w ≤ 2^{(ξQ - 3g) m} selfDiam(h_n - h_m)(B_r(w))`. So `S < Z/2` forces `D_n(a,b;B₃) < Z`, or
`𝒢_mᶜ`, or a self-internal diameter of `h_n - h_m` above `X' = 2^{-(ξQ-3g)m} Z/4`. -/
theorem measure_setDist_lt_half_le (hξ : 0 < ξ) {g : ℝ} (hH : IsDyadicRealization κ P W H)
    {m n : ℕ} {a b : Rd d} {s r : ℝ} (hsr : s < r) (hs0 : 0 ≤ s)
    (haV : obox a r ⊆ obox (0 : Rd d) 3) (hbV : obox b r ⊆ obox (0 : Rd d) 3) {Z X' : ℝ}
    (hX'Z : (2 : ℝ) ^ ((ξ * Q - 3 * g) * m) * X' = Z / 4) :
    P {ω | lfppSetDist ξ (fun z => H n z ω) (obox 0 3) (cbox a s) (cbox b s) < Z / 2} ≤
      P {ω | lfppDistOn ξ (fun z => H n z ω) (obox 0 3) a b < Z} +
        P (eventG ξ Q (3 * g) H m)ᶜ +
        P {ω | X' < selfDiam ξ (fun z => H n z ω - H m z ω) a r} +
        P {ω | X' < selfDiam ξ (fun z => H n z ω - H m z ω) b r} := by
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans (add_le_add
    ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) le_rfl))
  intro ω hω
  by_contra hno
  simp only [mem_union, not_or, mem_ofPred_eq, not_lt, mem_compl_iff, not_not] at hno
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hno
  have hφ := (hH.band n).continuous ω
  have hψ : Continuous fun z => H n z ω - H m z ω :=
    ((hH.band n).continuous ω).sub ((hH.band m).continuous ω)
  have hcmp : ∀ w : Rd d, obox w r ⊆ obox (0 : Rd d) 3 →
      ∀ z ∈ obox w r, Real.exp (ξ * H n z ω) ≤
        (2 : ℝ) ^ ((ξ * Q - 3 * g) * m) * Real.exp (ξ * (H n z ω - H m z ω)) := by
    intro w hwV z hz
    have hz3 : z ∈ cbox (0 : Rd d) 3 := obox_subset_cbox _ _ (hwV hz)
    have hHm : H m z ω ≤ m * (Q - 3 * g / ξ) * Real.log 2 := h2 z hz3
    rw [← exp_eq_two_rpow hξ m, ← Real.exp_add, Real.exp_le_exp]
    have := mul_le_mul_of_nonneg_left hHm hξ.le
    linarith
  have hY : ∀ w : Rd d, obox w r ⊆ obox (0 : Rd d) 3 →
      selfDiam ξ (fun z => H n z ω - H m z ω) w r ≤ X' →
        selfDiam ξ (fun z => H n z ω) w r ≤ Z / 4 := by
    intro w hwV hw
    calc selfDiam ξ (fun z => H n z ω) w r
        ≤ (2 : ℝ) ^ ((ξ * Q - 3 * g) * m) * selfDiam ξ (fun z => H n z ω - H m z ω) w r :=
          selfDiam_le_mul_of_exp_le hφ hψ (by positivity) (hcmp w hwV)
      _ ≤ (2 : ℝ) ^ ((ξ * Q - 3 * g) * m) * X' := mul_le_mul_of_nonneg_left hw (by positivity)
      _ = Z / 4 := hX'Z
  have haA : a ∈ cbox a s := fun i => by rw [sub_self, abs_zero]; exact hs0
  have hbB : b ∈ cbox b s := fun i => by rw [sub_self, abs_zero]; exact hs0
  have htri := lfppDistOn_le_selfDiam_add_lfppSetDist hφ (isOpen_obox 0 3)
    (convex_obox 0 3).isPreconnected (cbox_subset_obox hsr) (cbox_subset_obox hsr) haV hbV
    ⟨a, haA⟩ ⟨b, hbB⟩ (ξ := ξ)
  have hYa := hY a haV h3
  have hYb := hY b hbV h4
  have hω' : lfppSetDist ξ (fun z => H n z ω) (obox 0 3) (cbox a s) (cbox b s) < Z / 2 := hω
  linarith

/-- **Lower tail of a set distance from a lower quantile** (MA7 D-4.6 for `log S`, `K = B̄₃(0)`):
if `P[S < t₀] ≤ 1/4` and `log T + t ≤ log t₀ - ξ √(n log 2) c_{3/4}`, then
`P[S < T] ≤ 2 exp(-t²/(2 ξ² n log 2))`. -/
theorem measure_setDist_lt_le (hκ : IsLFPPKernel κ) (hξ : 0 < ξ)
    (hH : IsDyadicRealization κ P W H) {n : ℕ} (hn : 1 ≤ n) {A B : Set (Rd d)}
    (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsClosed B) (hBne : B.Nonempty)
    (hAB : Disjoint A B) (hA3 : A ⊆ obox (0 : Rd d) 3) (hB3 : B ⊆ obox (0 : Rd d) 3)
    {t₀ T t : ℝ} (ht₀ : 0 < t₀) (ht : 0 ≤ t)
    (hbad : P {ω | lfppSetDist ξ (fun z => H n z ω) (obox 0 3) A B < t₀} ≤
      ENNReal.ofReal (1 / 4))
    (hle : Real.log T + t ≤ Real.log t₀ - ξ * √(n * Real.log 2) * quantileConst (3 / 4)) :
    P {ω | lfppSetDist ξ (fun z => H n z ω) (obox 0 3) A B < T} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ξ ^ 2 * (n * Real.log 2)))) := by
  have hW := hH.whiteNoise
  have := hW.isProbabilityMeasure
  have h34 := three_quarters_le_measure hbad
  have hΦ := isSupLipschitzOn_log_lfppSetDist ξ (obox_subset_cbox (0 : Rd d) 3) A B
  have hpos : ∀ φ : Rd d → ℝ, Continuous φ → 0 < lfppSetDist ξ φ (obox 0 3) A B := fun φ hφ =>
    lfppSetDist_pos hφ hA hAne hB hBne hAB fun x hx y hy =>
      PcwJoined.of_convex (convex_obox 0 3) (hA3 hx) (hB3 hy)
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  have hab : (2 : ℝ)⁻¹ ^ n < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hconc := log_sub_lt_integral_log_of_le_measure_ge
    (Φ := fun φ => lfppSetDist ξ φ (obox 0 3) A B) hκ hW ha hab (hH.band n) (isCompact_cbox 0 3)
    hξ.ne' hΦ hpos (T := t₀) (p := 3 / 4) ht₀ (by norm_num) (by norm_num) h34
  rw [log_one_div_inv_two_pow, abs_of_pos hξ] at hconc
  have hle' : Real.log T + t ≤ ∫ ω, Real.log ((fun φ => lfppSetDist ξ φ (obox 0 3) A B)
      fun z => H n z ω) ∂P := by
    linarith
  have htail := measure_lt_le_of_log_add_le_integral
    (Φ := fun φ => lfppSetDist ξ φ (obox 0 3) A B) hκ hW ha hab.le (hH.band n)
    (isCompact_cbox 0 3) hΦ hpos (T := T) ht hle'
  rw [log_one_div_inv_two_pow] at htail
  exact htail

end PairProb

/-! ### Arithmetic -/

/-- `log 2 + ξ c √(n log 2) ≤ (δ/4) n log 2` once `n log 2 ≥ (8ξc/δ)² + 8 log 2/δ`. -/
lemma log_two_add_le_of_le {ξ c δ : ℝ} (hξ : 0 < ξ) (hc : 0 ≤ c) (hδ : 0 < δ) {n : ℕ}
    (hn : ((8 * ξ * c / δ) ^ 2 + 8 * Real.log 2 / δ) / Real.log 2 ≤ n) :
    Real.log 2 + ξ * √(n * Real.log 2) * c ≤ δ / 4 * (n * Real.log 2) := by
  obtain ⟨hL0, -⟩ := log_two_pos_lt_one
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, √(n * Real.log 2) = u := ⟨_, rfl⟩
  have hu2 : u ^ 2 = n * Real.log 2 := by rw [← hudef]; exact Real.sq_sqrt (by positivity)
  have hu0 : 0 ≤ u := by rw [← hudef]; exact Real.sqrt_nonneg _
  rw [hudef]
  have h7 : (8 * ξ * c / δ) ^ 2 + 8 * Real.log 2 / δ ≤ n * Real.log 2 := by
    rwa [div_le_iff₀ hL0] at hn
  have hA1 : 8 * ξ * c / δ ≤ u := by
    have h0 : 0 ≤ 8 * ξ * c / δ := by positivity
    rw [← Real.sqrt_sq h0, ← Real.sqrt_sq hu0]
    refine Real.sqrt_le_sqrt ?_
    have : 0 ≤ 8 * Real.log 2 / δ := by positivity
    rw [hu2]
    linarith
  have hA2 : 8 * Real.log 2 / δ ≤ u ^ 2 := by
    rw [hu2]
    have : 0 ≤ (8 * ξ * c / δ) ^ 2 := sq_nonneg _
    linarith
  have hB1 : Real.log 2 ≤ δ / 8 * u ^ 2 := by
    rw [div_le_iff₀ hδ] at hA2
    linarith
  have hB2 : ξ * u * c ≤ δ / 8 * u ^ 2 := by
    have h1 : ξ * c ≤ δ / 8 * u := by
      rw [div_le_iff₀ hδ] at hA1
      linarith
    have := mul_le_mul_of_nonneg_right h1 hu0
    nlinarith
  rw [hu2] at hB1 hB2
  linarith

/-- The number of pairs: `≤ 2^{2d(m+4)}`. -/
lemma card_innerSites_prod_le (m : ℕ) :
    ((innerSites d (m + 1) ×ˢ outerSites d (m + 1)).card : ℝ) ≤
      Real.exp (2 * d * (m + 4) * Real.log 2) := by
  have h1 : (innerSites d (m + 1) ×ˢ outerSites d (m + 1)).card ≤
      (2 * 2 ^ (m + 2) + 1) ^ d * (2 * 2 ^ (m + 2) + 1) ^ d := by
    rw [Finset.card_product]
    have hi : (innerSites d (m + 1)).card ≤ (2 * 2 ^ (m + 2) + 1) ^ d := by
      unfold innerSites
      exact (Finset.card_filter_le _ _).trans (card_boxF _ _).le
    have ho : (outerSites d (m + 1)).card ≤ (2 * 2 ^ (m + 2) + 1) ^ d := by
      unfold outerSites
      exact (Finset.card_filter_le _ _).trans (card_boxF _ _).le
    exact Nat.mul_le_mul hi ho
  have h2 : (2 * 2 ^ (m + 2) + 1 : ℕ) ≤ 2 ^ (m + 4) := by
    have : 1 ≤ 2 ^ (m + 2) := Nat.one_le_two_pow
    calc 2 * 2 ^ (m + 2) + 1 ≤ 4 * 2 ^ (m + 2) := by omega
      _ = 2 ^ (m + 4) := by ring
  have h3 : (innerSites d (m + 1) ×ˢ outerSites d (m + 1)).card ≤ 2 ^ ((m + 4) * (2 * d)) := by
    have h5 : (2 * 2 ^ (m + 2) + 1) ^ d ≤ (2 ^ (m + 4)) ^ d := Nat.pow_le_pow_left h2 d
    calc _ ≤ (2 * 2 ^ (m + 2) + 1) ^ d * (2 * 2 ^ (m + 2) + 1) ^ d := h1
      _ ≤ (2 ^ (m + 4)) ^ d * (2 ^ (m + 4)) ^ d := Nat.mul_le_mul h5 h5
      _ = 2 ^ ((m + 4) * (2 * d)) := by
          rw [← pow_mul, ← pow_add]
          congr 1
          ring
  have h4 : ((innerSites d (m + 1) ×ˢ outerSites d (m + 1)).card : ℝ) ≤
      (2 : ℝ) ^ ((m + 4) * (2 * d)) := by exact_mod_cast h3
  refine h4.trans_eq ?_
  rw [show (2 * d * (m + 4) * Real.log 2 : ℝ) = (((m + 4) * (2 * d) : ℕ) : ℝ) * Real.log 2 by
    push_cast; ring, Real.exp_nat_mul, Real.exp_log two_pos]

/-- The final exponent: `2^{2d(m+4)} · 2 e^{-δ² n log 2/(8ξ²)} ≤ 2·2^{8d} e^{-δ² n log 2/(16ξ²)}`
for `m ≤ ε n`, `ε ≤ δ²/(32 d ξ²)`. -/
lemma exp_card_mul_le {ξ δ ε : ℝ} (hξ : 0 < ξ) (hd : 1 ≤ d) (hε : ε ≤ δ ^ 2 / (32 * d * ξ ^ 2))
    {m n : ℕ} (hm : (m : ℝ) ≤ ε * n) :
    Real.exp (2 * d * (m + 4) * Real.log 2) *
        (2 * Real.exp (-(δ ^ 2 * Real.log 2 / (8 * ξ ^ 2) * n))) ≤
      2 * Real.exp (8 * d * Real.log 2) * Real.exp (-(δ ^ 2 * Real.log 2 / (16 * ξ ^ 2) * n)) := by
  obtain ⟨hL0, -⟩ := log_two_pos_lt_one
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have e1 : Real.exp (2 * d * (m + 4) * Real.log 2) *
      (2 * Real.exp (-(δ ^ 2 * Real.log 2 / (8 * ξ ^ 2) * n))) =
      2 * Real.exp (2 * d * (m + 4) * Real.log 2 + -(δ ^ 2 * Real.log 2 / (8 * ξ ^ 2) * n)) := by
    rw [Real.exp_add]
    ring
  have e2 : 2 * Real.exp (8 * d * Real.log 2) *
      Real.exp (-(δ ^ 2 * Real.log 2 / (16 * ξ ^ 2) * n)) =
      2 * Real.exp (8 * d * Real.log 2 + -(δ ^ 2 * Real.log 2 / (16 * ξ ^ 2) * n)) := by
    rw [Real.exp_add]
    ring
  rw [e1, e2]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
  have h1 : 2 * d * ε ≤ δ ^ 2 / (16 * ξ ^ 2) := by
    rw [le_div_iff₀ (by positivity)] at hε ⊢
    nlinarith
  have h2 : 2 * d * (m : ℝ) * Real.log 2 ≤ 2 * d * (ε * n) * Real.log 2 := by
    have : (0 : ℝ) ≤ 2 * d * Real.log 2 := by positivity
    nlinarith
  have h3 : 2 * d * (ε * n) * Real.log 2 ≤ δ ^ 2 / (16 * ξ ^ 2) * n * Real.log 2 := by
    have : (0 : ℝ) ≤ n * Real.log 2 := by positivity
    nlinarith
  have e : δ ^ 2 * Real.log 2 / (16 * ξ ^ 2) * n = δ ^ 2 / (16 * ξ ^ 2) * n * Real.log 2 := by ring
  have e' : δ ^ 2 * Real.log 2 / (8 * ξ ^ 2) * n =
      2 * (δ ^ 2 / (16 * ξ ^ 2) * n * Real.log 2) := by ring
  rw [e, e']
  nlinarith

/-- The threshold comparison of MA7 D-4.8 (1): with `δ' ≤ g ε`, `ε n < m + 1` and
`3g + 2 ≤ g ε n`, `2^{-(1-ξQ-gε)(n-m)} ≤ 2^{-(ξQ-3g)m} 2^{-(1-ξQ+δ')n}/4 / 2^{-m}`. -/
lemma two_rpow_threshold_le {ξ Q g ε δ' : ℝ} {m n : ℕ} (hmn : m ≤ n) (hg : 0 < g) (hε : 0 < ε)
    (hδ' : δ' ≤ g * ε) (hmge : ε * n < m + 1) (h4 : 3 * g + 2 ≤ g * ε * n) :
    (2 : ℝ) ^ (-(1 - ξ * Q - g * ε) * ((n - m : ℕ) : ℝ)) ≤
      (2 : ℝ) ^ (-(1 - ξ * Q + δ') * n) / 4 * (2 : ℝ) ^ (-((ξ * Q - 3 * g) * m)) /
        (2 : ℝ)⁻¹ ^ m := by
  rw [two_rpow_div_four_mul_div]
  refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
  rw [Nat.cast_sub hmn]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : δ' * n ≤ g * ε * n := mul_le_mul_of_nonneg_right hδ' hn0
  have h2 : 0 ≤ g * ε * m := by positivity
  have h3 : 3 * g * (ε * n) ≤ 3 * g * (m + 1) := mul_le_mul_of_nonneg_left hmge.le (by positivity)
  linarith only [h1, h2, h3, h4]

/-! ### The tail bound -/

/-- **DGZ Prop 4.8, lower half** (MA7 D-4.8), for the dyadic realizations of `DGZHyp`:
`P[D_n(across B₂(0) \ B₁(0)) < 2^{-(1-ξQ+δ)n}] ≤ C e^{-n/C}`. -/
theorem acrossLower_tail {κ : Rd d → ℝ} {ξ Q : ℝ} (h : DGZHyp d κ ξ Q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
        P {ω | acrossDist ξ (fun z => H n z ω) 0 2 1 < (2 : ℝ) ^ (-(1 - ξ * Q + δ) * n)} ≤
          ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C)) := by
  have hd := h.dim
  have hd1 : 1 ≤ d := by omega
  have hκ := h.kernel
  have hξ := h.xi_pos
  obtain ⟨hL0, -⟩ := log_two_pos_lt_one
  -- the gap `g = ξ(Q - √(2d))/4` and the level `η = 3g` of `𝒢_m`
  obtain ⟨g, hg0, hgdef⟩ : ∃ g : ℝ, 0 < g ∧ ξ * (Q - √(2 * d)) = 4 * g :=
    ⟨ξ * (Q - √(2 * d)) / 4, div_pos (mul_pos hξ (sub_pos.2 h.subcritical)) (by norm_num),
      by ring⟩
  have hη : 3 * g < ξ * (Q - √(2 * d)) := by linarith
  obtain ⟨CG, hCG, hGb⟩ := prob_G_compl_le hκ hξ hη
  -- `ε = min(1/2, δ²/(32 d ξ²))` and `δ' = min(g ε, δ/4)`
  obtain ⟨ε, hε0, hε2, hεδ⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ ε ≤ δ ^ 2 / (32 * d * ξ ^ 2) :=
    ⟨min (1 / 2) (δ ^ 2 / (32 * d * ξ ^ 2)), lt_min (by norm_num) (by positivity),
      min_le_left _ _, min_le_right _ _⟩
  obtain ⟨δ', hδ'0, hδ'g, hδ'δ⟩ : ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ g * ε ∧ δ' ≤ δ / 4 :=
    ⟨min (g * ε) (δ / 4), lt_min (by positivity) (by positivity), min_le_left _ _,
      min_le_right _ _⟩
  obtain ⟨C₃, hC₃, h36⟩ := lemma36_lower_of_dgzHyp h hδ'0
  obtain ⟨Csd, hCsd, hsd⟩ := selfDiamShape d κ ξ Q h (g * ε) (by positivity)
  obtain ⟨k₃, hk₃⟩ := exists_mul_exp_neg_div_le hC₃ (θ := 1 / 16) (by norm_num)
  obtain ⟨kG, hkG⟩ := exists_mul_exp_neg_div_le hCG (θ := 1 / 16) (by norm_num)
  obtain ⟨ksd, hksd⟩ := exists_mul_exp_neg_div_le hCsd (θ := 1 / 16) (by norm_num)
  obtain ⟨c, hc0, hcdef⟩ : ∃ c : ℝ, 0 ≤ c ∧ quantileConst (3 / 4) = c :=
    ⟨_, HigherDimLFPP.Conc.quantileConst_nonneg _, rfl⟩
  -- the threshold `n₀`
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (((((((eventually_ge_atTop 1).and
    (eventually_ge_real (1 / ε))).and (eventually_ge_real ((kG + 1) / ε))).and
    (eventually_ge_atTop (2 * ksd))).and (eventually_ge_atTop k₃)).and
    (eventually_ge_real ((3 * g + 2) / (g * ε)))).and
    (eventually_ge_real (((8 * ξ * c / δ) ^ 2 + 8 * Real.log 2 / δ) / Real.log 2)))
  -- the rate `β = δ² log 2/(16 ξ²)` and the constant `C`
  obtain ⟨β, hβ0, hβdef⟩ : ∃ β : ℝ, 0 < β ∧ δ ^ 2 * Real.log 2 / (16 * ξ ^ 2) = β :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨K₀, hK₀0, hK₀def⟩ : ∃ K₀ : ℝ, 0 < K₀ ∧ 2 * Real.exp (8 * d * Real.log 2) = K₀ :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨C, hCK, hCβ, hCn⟩ : ∃ C : ℝ, K₀ ≤ C ∧ 1 / β ≤ C ∧ (n₀ : ℝ) + 1 ≤ C :=
    ⟨max (max K₀ (1 / β)) (n₀ + 1), (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _), le_max_right _ _⟩
  have hC0 : 0 < C := by linarith
  refine ⟨C, hC0, fun Ω _ P W H hH n => ?_⟩
  have hW := hH.whiteNoise
  have := hW.isProbabilityMeasure
  rcases lt_or_ge n n₀ with hn | hn
  · -- small `n`: the probability is at most `1 ≤ C e^{-n/C}`
    calc _ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal (one_le_mul_exp_neg_div (Nat.cast_nonneg n) ?_)
        have : (n : ℝ) + 1 ≤ n₀ := by exact_mod_cast hn
        linarith
  obtain ⟨⟨⟨⟨⟨⟨hn1, hnε⟩, hnG⟩, hnsd⟩, hn3⟩, hn6⟩, hn7⟩ := hn₀ n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  -- the scale `m = ⌊ε n⌋`
  have hεn : 1 ≤ ε * n := by
    rw [div_le_iff₀ hε0] at hnε
    linarith
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, ⌊ε * n⌋₊ = m := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by
    rw [← hmdef]
    exact Nat.le_floor (by exact_mod_cast hεn)
  have hmle : (m : ℝ) ≤ ε * n := by
    rw [← hmdef]
    exact Nat.floor_le (by positivity)
  have hmge : ε * n < m + 1 := by
    rw [← hmdef]
    exact Nat.lt_floor_add_one _
  have hmn : m ≤ n := by
    have : (m : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have hnm : ((n - m : ℕ) : ℝ) = n - m := Nat.cast_sub hmn
  -- the bad events have probability `≤ 1/16` each
  have hP3 : C₃ * Real.exp (-(n : ℝ) / C₃) ≤ 1 / 16 := hk₃ n hn3
  have hPG : CG * Real.exp (-(m : ℝ) / CG) ≤ 1 / 16 := by
    refine hkG m ?_
    have h1 : (kG : ℝ) + 1 ≤ ε * n := by
      rw [div_le_iff₀ hε0] at hnG
      linarith
    have : (kG : ℝ) < m + 1 := by linarith
    have : kG < m + 1 := by exact_mod_cast this
    omega
  have hPsd : Csd * Real.exp (-((n - m : ℕ) : ℝ) / Csd) ≤ 1 / 16 := by
    refine hksd (n - m) ?_
    have h1 : (2 * ksd : ℝ) ≤ n := by exact_mod_cast hnsd
    have : (ksd : ℝ) ≤ ((n - m : ℕ) : ℝ) := by rw [hnm]; nlinarith
    exact_mod_cast this
  -- the grid `s = 2^{-(m+1)}` and the boxes of radius `r = 2^{-m}`
  have hs0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (m + 1) := by positivity
  have hsr : (2 : ℝ)⁻¹ ^ (m + 1) < (2 : ℝ)⁻¹ ^ m :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (Nat.lt_succ_self m)
  have hr2 : (2 : ℝ)⁻¹ ^ m ≤ 1 / 2 := by
    calc (2 : ℝ)⁻¹ ^ m ≤ (2 : ℝ)⁻¹ ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm1
      _ = 1 / 2 := by norm_num
  have hG := isBandVersion_sub_of_realization hκ hH hmn
  -- thresholds `Z = 2^{-(1-ξQ+δ')n}` and `X' = 2^{-(ξQ-3g)m} Z/4`
  obtain ⟨Z, hZ0, hZdef⟩ : ∃ Z : ℝ, 0 < Z ∧ (2 : ℝ) ^ (-(1 - ξ * Q + δ') * n) = Z :=
    ⟨_, Real.rpow_pos_of_pos two_pos _, rfl⟩
  obtain ⟨X', hX'def⟩ : ∃ X' : ℝ,
      (2 : ℝ) ^ (-(1 - ξ * Q + δ') * n) / 4 * (2 : ℝ) ^ (-((ξ * Q - 3 * g) * m)) = X' :=
    ⟨_, rfl⟩
  have hX'Z : (2 : ℝ) ^ ((ξ * Q - 3 * g) * m) * X' = Z / 4 := by
    rw [← hX'def, two_rpow_mul_div_four_mul, hZdef]
  have hthr : (2 : ℝ) ^ (-(1 - ξ * Q - g * ε) * ((n - m : ℕ) : ℝ)) ≤
      X' / (2 : ℝ)⁻¹ ^ m := by
    rw [← hX'def]
    refine two_rpow_threshold_le hmn hg0 hε0 hδ'g hmge ?_
    rw [div_le_iff₀ (by positivity)] at hn6
    linarith
  have hE3 : ∀ w : Rd d,
      P {ω | X' < selfDiam ξ (fun z => H n z ω - H m z ω) w ((2 : ℝ)⁻¹ ^ m)} ≤
        ENNReal.ofReal (1 / 16) := by
    intro w
    rw [measure_lt_selfDiam_band_eq hκ hH hmn hG ξ w X']
    refine (measure_mono fun ω hω => ?_).trans ((hsd Ω P W H hH (n - m)).trans
      (ENNReal.ofReal_le_ofReal hPsd))
    exact lt_of_le_of_lt hthr hω
  have hbig := log_two_add_le_of_le hξ hc0 hδ hn7
  -- the pair estimate
  have hpair : ∀ p ∈ innerSites d (m + 1) ×ˢ outerSites d (m + 1),
      P {ω | lfppSetDist ξ (fun z => H n z ω) (obox 0 3)
        (cbox (latPt ((2 : ℝ)⁻¹ ^ (m + 1)) p.1) ((2 : ℝ)⁻¹ ^ (m + 1)))
        (cbox (latPt ((2 : ℝ)⁻¹ ^ (m + 1)) p.2) ((2 : ℝ)⁻¹ ^ (m + 1))) <
          (2 : ℝ) ^ (-(1 - ξ * Q + δ) * n)} ≤
        ENNReal.ofReal (2 * Real.exp (-(δ / 2 * (n * Real.log 2)) ^ 2 /
          (2 * ξ ^ 2 * (n * Real.log 2)))) := by
    intro p hp
    obtain ⟨hy, hx⟩ := Finset.mem_product.1 hp
    have ha2 := latPt_inner_mem_cbox hy
    have hb2 := latPt_outer_mem_cbox hx
    have haV := obox_subset_obox_three ha2 hr2
    have hbV := obox_subset_obox_three hb2 hr2
    -- (1) `P[S < Z/2] ≤ 1/4`
    have hE1 : P {ω | lfppDistOn ξ (fun z => H n z ω) (obox 0 3)
        (latPt ((2 : ℝ)⁻¹ ^ (m + 1)) p.1) (latPt ((2 : ℝ)⁻¹ ^ (m + 1)) p.2) < Z} ≤
        ENNReal.ofReal (1 / 16) := by
      rw [← hZdef]
      exact (h36 Ω P W H hH _ _ ha2 hb2 (exists_half_le_abs_sub (by omega) hy hx) n).trans
        (ENNReal.ofReal_le_ofReal hP3)
    have hbad := (measure_setDist_lt_half_le hξ hH (n := n) hsr hs0.le haV hbV hX'Z).trans
      (add_le_add (add_le_add (add_le_add hE1
        ((hGb hH m).trans (ENNReal.ofReal_le_ofReal hPG))) (hE3 _)) (hE3 _))
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)] at hbad
    norm_num at hbad
    -- (2), (3) concentration and the tail at `2^{-(1-ξQ+δ)n}`
    refine measure_setDist_lt_le hκ hξ hH hn1 (isCompact_cbox _ _) ⟨_, fun i => by
      rw [sub_self, abs_zero]; exact hs0.le⟩ (HigherDimLFPP.DGZ.isClosed_cbox _ _) ⟨_, fun i => by
      rw [sub_self, abs_zero]; exact hs0.le⟩ (disjoint_cbox_pair (by omega) hy hx)
      ((cbox_subset_obox hsr).trans haV) ((cbox_subset_obox hsr).trans hbV)
      (div_pos hZ0 two_pos) (by positivity) (by simpa using hbad) ?_
    rw [Real.log_div hZ0.ne' two_ne_zero, ← hZdef, Real.log_rpow two_pos, Real.log_rpow two_pos,
      hcdef]
    have h1 : δ' * (n * Real.log 2) ≤ δ / 4 * (n * Real.log 2) :=
      mul_le_mul_of_nonneg_right hδ'δ (by positivity)
    linarith only [h1, hbig]
  -- (4) the union bound over the pairs
  have hincl : {ω | acrossDist ξ (fun z => H n z ω) 0 2 1 < (2 : ℝ) ^ (-(1 - ξ * Q + δ) * n)} ⊆
      ⋃ p ∈ innerSites d (m + 1) ×ˢ outerSites d (m + 1),
        {ω | lfppSetDist ξ (fun z => H n z ω) (obox 0 3)
          (cbox (latPt ((2 : ℝ)⁻¹ ^ (m + 1)) p.1) ((2 : ℝ)⁻¹ ^ (m + 1)))
          (cbox (latPt ((2 : ℝ)⁻¹ ^ (m + 1)) p.2) ((2 : ℝ)⁻¹ ^ (m + 1))) <
            (2 : ℝ) ^ (-(1 - ξ * Q + δ) * n)} := by
    intro ω hω
    obtain ⟨p, hp, hpeq⟩ := Finset.exists_mem_eq_inf'
      (innerSites_prod_outerSites_nonempty hd1 (m + 1))
      (fun p => lfppSetDist ξ (fun z => H n z ω) (obox 0 3)
        (cbox (latPt ((2 : ℝ)⁻¹ ^ (m + 1)) p.1) ((2 : ℝ)⁻¹ ^ (m + 1)))
        (cbox (latPt ((2 : ℝ)⁻¹ ^ (m + 1)) p.2) ((2 : ℝ)⁻¹ ^ (m + 1))))
    have hle := inf'_setDist_le_acrossDist hd1 ((hH.band n).continuous ω) (m + 1) (ξ := ξ)
    have hlt := lt_of_le_of_lt hle hω
    rw [hpeq] at hlt
    exact mem_iUnion₂.2 ⟨p, hp, hlt⟩
  have hexpo : -(δ / 2 * (n * Real.log 2)) ^ 2 / (2 * ξ ^ 2 * (n * Real.log 2)) =
      -(δ ^ 2 * Real.log 2 / (8 * ξ ^ 2) * n) := by
    field_simp
    ring
  rw [hexpo] at hpair
  refine (measure_mono hincl).trans ((measure_biUnion_finset_le _ _).trans
    ((Finset.sum_le_sum hpair).trans ?_))
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hβC : Real.exp (-(β * n)) ≤ Real.exp (-(n : ℝ) / C) := by
    refine Real.exp_le_exp.2 ?_
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ hC0]
    have h1 : 1 ≤ β * C := by
      rw [div_le_iff₀ hβ0] at hCβ
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith only [h2]
  calc ((innerSites d (m + 1) ×ˢ outerSites d (m + 1)).card : ℝ) *
        (2 * Real.exp (-(δ ^ 2 * Real.log 2 / (8 * ξ ^ 2) * n)))
      ≤ Real.exp (2 * d * (m + 4) * Real.log 2) *
        (2 * Real.exp (-(δ ^ 2 * Real.log 2 / (8 * ξ ^ 2) * n))) :=
        mul_le_mul_of_nonneg_right (card_innerSites_prod_le m) (by positivity)
    _ ≤ K₀ * Real.exp (-(β * n)) := by
        rw [← hK₀def, ← hβdef]
        exact exp_card_mul_le hξ hd1 hεδ hmle
    _ ≤ C * Real.exp (-(n : ℝ) / C) := mul_le_mul hCK hβC (Real.exp_pos _).le hC0.le

/-- **MA7 Details (c) `AcrossLowerShape`** (DGZ Prop 4.8, lower half; MA7 D-4.8), for every
`d, κ, ξ, Q`. -/
theorem acrossLowerShape (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) : AcrossLowerShape d κ ξ Q :=
  fun h _ hδ => acrossLower_tail h hδ

end DGZ

end HigherDimLQGMetric
