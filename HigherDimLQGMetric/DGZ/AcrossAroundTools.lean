import HigherDimLQGMetric.DGZ.SelfDiam
import HigherDimLQGMetric.DGZ.FunctionalsBounds
import HigherDimLQGMetric.DGZ.FunctionalsLaw
import HigherDimLQGMetric.DGZ.FieldTailsMeas

/-!
# Tools for DGZ Prop 4.8 (lower half), Lemma 4.9 (around half) and Lemma 4.10 (across half)

Packet L3c3 (MA7 `planning/audits/MA7-ref2-sections-4-6.md`, Details (a) D-4.8, D-4.9, D-4.10).
Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), §4.3–4.4.

Shared ingredients of the three proofs:

* `isBandVersion_sub_of_realization`: for a dyadic realization and `m ≤ n`, the pointwise difference
  `h_n - h_m` is itself a continuous version of `h_{m,n} = H_{2^{-n}, 2^{-m}}` (so
  `h_n = h_m + h_{m,n}` holds everywhere, not only almost surely);
* scaled laws (`measure_lt_selfDiam_band_eq`, `measure_acrossDist_band_lt_eq`): the self-internal
  diameter and the across distance of `h_{m,n}` on boxes of size `2^{-m}` have the laws of `2^{-m}`
  times those of `h_{n-m}` on the unit boxes (dyadic scaling and translation, L3b1);
* `productBound_of_local`: events that are measurable for the field `h_{m,n}` on the boxes
  `B̄_{R s}(s x)` (`s ≥ 2^{-m}`) satisfy HigherDimLFPP's `ProductBound` with range `⌈2(R + ρ)⌉`;
* `measurableSet_setOf_config`: every event about a site configuration whose closed sites lie in a
  fixed finite set and are measurable events is measurable;
* `measure_not_smallClusters_le`: the Peierls bound `Perc.diameterBound` in the form
  `P[¬ SmallClusters O D] ≤ (2N+1)^d 2^{-⌊D/2⌋}` when all closed sites lie in `B̄_N(0)`;
* the coarse scale `superScale n = 2 ⌊log₂ n⌋ + 2` (`n² < 2^{m} ≤ 4 n²`) used by D-4.9 and D-4.10
  (MA7 uses `⌊n/(log n)²⌋`; any `m = O(log n)` with `2^m ≫ n log n` works) and the asymptotic
  inequalities that make the bounds super-exponential;
* `exists_field_superExp'` (any version `ψ` of `h_{m(n)}`) and `exists_field_superExp` (dyadic
  realizations): `P[sup_{B̄_R(0)} |h_{m(n)}| > c n] ≤ e^{-n log n}` for large `n`;
* `exists_isDyadicRealization`: every white noise carries a dyadic realization.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox abs_apply_le_norm)

variable {d : ℕ}

/-! ### The band `h_{m,n}` as a difference -/

/-- **`h_n - h_m` is a version of `h_{m,n}`**: for a dyadic realization and `m ≤ n`, the pointwise
difference `z ↦ H n z ω - H m z ω` is a continuous version of `H_{2^{-n}, 2^{-m}}` over the same
white noise. -/
theorem isBandVersion_sub_of_realization {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {m n : ℕ} (hmn : m ≤ n) :
    IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ m) (fun z ω => H n z ω - H m z ω) where
  continuous ω := ((hH.band n).continuous ω).sub ((hH.band m).continuous ω)
  measurable z := ((hH.band n).measurable z).sub ((hH.band m).measurable z)
  ae_eq z := by
    obtain ⟨G, hG, hsum⟩ := exists_band_decomp hκ hH hmn
    filter_upwards [hsum, hG.ae_eq z] with ω h1 h2
    show H n z ω - H m z ω = _
    rw [h1 z, add_sub_cancel_left]
    exact h2

/-! ### Laws of real random variables -/

/-- Two real random variables with the same law have the same upper tails. -/
lemma measure_lt_eq_of_map_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ} (hX : Measurable X)
    (hY : Measurable Y) (h : P.map X = P'.map Y) (t : ℝ) :
    P {ω | t < X ω} = P' {ω | t < Y ω} := by
  have e1 : P {ω | t < X ω} = P.map X (Ioi t) := (Measure.map_apply hX measurableSet_Ioi).symm
  have e2 : P' {ω | t < Y ω} = P'.map Y (Ioi t) := (Measure.map_apply hY measurableSet_Ioi).symm
  rw [e1, e2, h]

/-- Two real random variables with the same law have the same lower tails. -/
lemma measure_gt_eq_of_map_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ} (hX : Measurable X)
    (hY : Measurable Y) (h : P.map X = P'.map Y) (t : ℝ) :
    P {ω | X ω < t} = P' {ω | Y ω < t} := by
  have e1 : P {ω | X ω < t} = P.map X (Iio t) := (Measure.map_apply hX measurableSet_Iio).symm
  have e2 : P' {ω | Y ω < t} = P'.map Y (Iio t) := (Measure.map_apply hY measurableSet_Iio).symm
  rw [e1, e2, h]

/-! ### Scaled laws on the boxes of the coarse scale -/

section Scaled

variable {κ : Rd d → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
  {H : ℕ → Rd d → Ω → ℝ}

/-- `h_{n-m}` as a version of `H_{2^{-n}/2^{-m}, 2^{-m}/2^{-m}}`. -/
lemma isBandVersion_scaled (hH : IsDyadicRealization κ P W H) {m n : ℕ} (hmn : m ≤ n) :
    IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n / (2 : ℝ)⁻¹ ^ m) ((2 : ℝ)⁻¹ ^ m / (2 : ℝ)⁻¹ ^ m)
      (H (n - m)) :=
  (hH.band (n - m)).congr_band (inv_two_pow_div_inv_two_pow hmn).symm
    (div_self (by positivity)).symm

/-- **Scaled law of the self-internal diameter** (MA7 D-4.8 (1), D-4.9): for a version `G` of
`h_{m,n}` and any centre `w`,
`P[t < selfDiam(G)(B_{2^{-m}}(w))] = P[t / 2^{-m} < selfDiam_{n-m}(B₁(0))]`. -/
theorem measure_lt_selfDiam_band_eq (hκ : IsLFPPKernel κ) (hH : IsDyadicRealization κ P W H)
    {m n : ℕ} (hmn : m ≤ n) {G : Rd d → Ω → ℝ}
    (hG : IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ m) G) (ξ : ℝ) (w : Rd d) (t : ℝ) :
    P {ω | t < selfDiam ξ (fun z => G z ω) w ((2 : ℝ)⁻¹ ^ m)} =
      P {ω | t / (2 : ℝ)⁻¹ ^ m < selfDiam ξ (fun z => H (n - m) z ω) 0 1} := by
  have hr0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m := by positivity
  have hW := hH.whiteNoise
  have hmap := map_selfDiam_sim_eq hG (isBandVersion_scaled hH hmn) hW hW hκ w hr0
    (by positivity) ξ 0 1
  rw [smul_zero, add_zero, mul_one] at hmap
  have hF : Measurable fun ω => selfDiam ξ (fun z => G z ω) w ((2 : ℝ)⁻¹ ^ m) :=
    measurable_selfDiam hG.continuous hG.measurable ξ w _
  have hF' : Measurable fun ω => (2 : ℝ)⁻¹ ^ m * selfDiam ξ (fun z => H (n - m) z ω) 0 1 :=
    (measurable_selfDiam (hH.band _).continuous (hH.band _).measurable ξ 0 1).const_mul _
  rw [measure_lt_eq_of_map_eq hF hF' hmap t]
  congr 1
  ext ω
  simp only [mem_ofPred_eq]
  rw [div_lt_iff₀ hr0, mul_comm]

/-- **Scaled law of the across distance** (MA7 D-4.10): for a version `G` of `h_{m,n}` and any
centre `w`, `P[D(G)(across B_{2s}(w) \ B_s(w)) < t] = P[D_{n-m}(across B₂(0) \ B₁(0)) < t/s]`,
`s = 2^{-m}`. -/
theorem measure_acrossDist_band_lt_eq (hκ : IsLFPPKernel κ) (hH : IsDyadicRealization κ P W H)
    {m n : ℕ} (hmn : m ≤ n) {G : Rd d → Ω → ℝ}
    (hG : IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ m) G) (ξ : ℝ) (w : Rd d) (t : ℝ) :
    P {ω | acrossDist ξ (fun z => G z ω) w (2 * (2 : ℝ)⁻¹ ^ m) ((2 : ℝ)⁻¹ ^ m) < t} =
      P {ω | acrossDist ξ (fun z => H (n - m) z ω) 0 2 1 < t / (2 : ℝ)⁻¹ ^ m} := by
  have hr0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m := by positivity
  have hW := hH.whiteNoise
  have hmap := map_acrossDist_sim_eq hG (isBandVersion_scaled hH hmn) hW hW hκ w hr0
    (by positivity) ξ 0 2 1
  rw [smul_zero, add_zero, mul_one, mul_comm ((2 : ℝ)⁻¹ ^ m) 2] at hmap
  have hF : Measurable fun ω =>
      acrossDist ξ (fun z => G z ω) w (2 * (2 : ℝ)⁻¹ ^ m) ((2 : ℝ)⁻¹ ^ m) :=
    measurable_acrossDist hG.continuous hG.measurable ξ w _ _
  have hF' : Measurable fun ω => (2 : ℝ)⁻¹ ^ m * acrossDist ξ (fun z => H (n - m) z ω) 0 2 1 :=
    (measurable_acrossDist (hH.band _).continuous (hH.band _).measurable ξ 0 2 1).const_mul _
  rw [measure_gt_eq_of_map_eq hF hF' hmap t]
  congr 1
  ext ω
  simp only [mem_ofPred_eq]
  rw [lt_div_iff₀ hr0, mul_comm]

end Scaled

/-! ### Product bound for local site events -/

/-- **Product bound for local events** (DGZ's finite-range dependence; generalizes HigherDimLFPP
`productBound_closedSite`): let `G` be a version of `H_{a,c}` (`0 < a`, `c ≤ s`), `ρ` a support
radius of `κ`, and let each event `closed x` be measurable for the σ-algebra generated by `G` on
the closed box `B̄_{R s}(s x)`. Then the events satisfy `Perc.ProductBound` with range
`⌈2(R + ρ)⌉`: sites at lattice `ℓ^∞`-distance `> ⌈2(R + ρ)⌉` have boxes at Euclidean distance
`≥ 2 ρ s ≥ 2 ρ c`, so the restricted fields are mutually independent. -/
theorem productBound_of_local {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) {ρ : ℝ}
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {a c : ℝ} (ha : 0 < a) {G : Rd d → Ω → ℝ}
    (hG : IsBandVersion P W κ a c G) {s : ℝ} (hs : 0 < s) (hcs : c ≤ s) {R : ℝ}
    (closed : Zd d → Set Ω)
    (hloc : ∀ x, MeasurableSet[MeasurableSpace.comap
      (fun ω (z : cbox (latPt s x) (R * s)) => G z ω) MeasurableSpace.pi] (closed x)) :
    ProductBound P closed ((⌈2 * (R + ρ)⌉₊ : ℕ) : ℤ) := by
  intro S hS
  set M : ℕ := ⌈2 * (R + ρ)⌉₊ with hMdef
  have hρ0 : 0 < ρ := hκ.radius_pos hρ
  have hM : 2 * (R + ρ) ≤ (M : ℝ) := Nat.le_ceil _
  set A : S → Set (Rd d) := fun x => cbox (latPt s x) (R * s) with hA
  have hfar : ∀ x₁ x₂ : S, x₁ ≠ x₂ → ∀ z ∈ A x₁, ∀ w ∈ A x₂, 2 * ρ * c ≤ ‖z - w‖ := by
    intro x₁ x₂ hne z hz w hw
    have hnot := hS x₁ x₁.2 x₂ x₂.2 fun h => hne (Subtype.ext h)
    simp only [WithinInf, not_forall, not_le] at hnot
    obtain ⟨l, hl⟩ := hnot
    have hl1 : (M : ℤ) + 1 ≤ |(x₁ : Zd d) l - (x₂ : Zd d) l| := hl
    have hl' : (M : ℝ) + 1 ≤ |((x₁ : Zd d) l : ℝ) - ((x₂ : Zd d) l : ℝ)| := by
      exact_mod_cast hl1
    have h1 : |z l - s * ((x₁ : Zd d) l : ℝ)| ≤ R * s := hz l
    have h2 : |w l - s * ((x₂ : Zd d) l : ℝ)| ≤ R * s := hw l
    have h3 : |s * ((x₁ : Zd d) l : ℝ) - s * ((x₂ : Zd d) l : ℝ)| ≤
        |z l - s * ((x₁ : Zd d) l : ℝ)| + |z l - w l| + |w l - s * ((x₂ : Zd d) l : ℝ)| := by
      have e : s * ((x₁ : Zd d) l : ℝ) - s * ((x₂ : Zd d) l : ℝ) =
          -(z l - s * ((x₁ : Zd d) l : ℝ)) + (z l - w l) + (w l - s * ((x₂ : Zd d) l : ℝ)) := by
        ring
      rw [e]
      refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) le_rfl)
      rw [abs_neg]
    have h4 : |s * ((x₁ : Zd d) l : ℝ) - s * ((x₂ : Zd d) l : ℝ)| =
        s * |((x₁ : Zd d) l : ℝ) - ((x₂ : Zd d) l : ℝ)| := by
      rw [← mul_sub, abs_mul, abs_of_pos hs]
    have h5 := abs_apply_le_norm (z - w) l
    rw [PiLp.sub_apply] at h5
    have k1 : s * ((M : ℝ) + 1) ≤ s * |((x₁ : Zd d) l : ℝ) - ((x₂ : Zd d) l : ℝ)| :=
      mul_le_mul_of_nonneg_left hl' hs.le
    have k2 : s * (2 * (R + ρ)) ≤ s * (M : ℝ) := mul_le_mul_of_nonneg_left hM hs.le
    have k3 : 2 * ρ * c ≤ 2 * ρ * s := mul_le_mul_of_nonneg_left hcs (by positivity)
    nlinarith
  have hind := hG.iIndepFun_restrict_of_far hW hκ hρ ha A hfar
  have h := hind.meas_iInter (s := fun x : S => closed x) fun x => hloc x
  have e : (⋂ x ∈ S, closed x) = ⋂ x : S, closed x := by
    ext ω
    simp only [mem_iInter, Subtype.forall]
  rw [e, h, Finset.prod_coe_sort S fun x => P (closed x)]

/-! ### Measurability of configuration events -/

/-- **Events about a finite random configuration are measurable**: if the closed sites `{x | ω ∈
closed x}` always lie in the finite set `F` and each `closed x` is measurable, then for every
property `p` of site sets, `{ω | p {x | ω ∉ closed x}}` is measurable (a finite union over the
possible closed sets). -/
theorem measurableSet_setOf_config {Ω : Type*} [MeasurableSpace Ω] (closed : Zd d → Set Ω)
    (F : Finset (Zd d)) (hF : ∀ x, x ∉ F → closed x = ∅) (hm : ∀ x, MeasurableSet (closed x))
    (p : Set (Zd d) → Prop) : MeasurableSet {ω | p {x | ω ∉ closed x}} := by
  classical
  have key : {ω | p {x | ω ∉ closed x}} =
      ⋃ K ∈ F.powerset.filter (fun K => p {x | x ∉ K}),
        ⋂ x ∈ F, (if x ∈ K then closed x else (closed x)ᶜ) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, Finset.mem_filter, Finset.mem_powerset,
      exists_prop]
    constructor
    · intro h
      refine ⟨F.filter (fun x => ω ∈ closed x), ⟨Finset.filter_subset _ _, ?_⟩, ?_⟩
      · have e : {x | x ∉ F.filter (fun x => ω ∈ closed x)} = {x | ω ∉ closed x} := by
          ext x
          simp only [mem_ofPred_eq, Finset.mem_filter, not_and]
          constructor
          · intro hx hω
            by_cases hxF : x ∈ F
            · exact hx hxF hω
            · rw [hF x hxF] at hω
              exact hω
          · intro hx _ hω
            exact hx hω
        rw [e]
        exact h
      · intro x hx
        split_ifs with hxK
        · exact (Finset.mem_filter.1 hxK).2
        · exact fun hxω => hxK (Finset.mem_filter.2 ⟨hx, hxω⟩)
    · rintro ⟨K, ⟨hKF, hK⟩, hω⟩
      have e : {x | ω ∉ closed x} = {x | x ∉ K} := by
        ext x
        simp only [mem_ofPred_eq]
        by_cases hxF : x ∈ F
        · have h' := hω x hxF
          by_cases hxK : x ∈ K
          · rw [ite_eq_left hxK] at h'
            exact ⟨fun h'' => absurd h' h'', fun h'' => absurd hxK h''⟩
          · rw [ite_eq_right hxK] at h'
            exact ⟨fun _ => hxK, fun _ => h'⟩
        · rw [hF x hxF]
          exact ⟨fun _ hxK => hxF (hKF hxK), fun _ h'' => h''⟩
      rw [e]
      exact hK
  rw [key]
  refine Finset.measurableSet_biUnion _ fun K _ => Finset.measurableSet_biInter _ fun x _ => ?_
  by_cases hxK : x ∈ K
  · rw [ite_eq_left hxK]
    exact hm x
  · rw [ite_eq_right hxK]
    exact (hm x).compl

/-! ### The Peierls bound for `SmallClusters` -/

/-- **Small closed clusters with high probability** (HigherDimLFPP `Perc.diameterBound`): under the
Peierls hypotheses, if every closed site lies in `B̄_N(0)`, then
`P[¬ SmallClusters {x | ω ∉ closed x} D] ≤ (2N+1)^d 2^{-⌊D/2⌋}`. -/
theorem measure_not_smallClusters_le {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (closed : Zd d → Set Ω) (r : ℕ) (ε θ : ℝ≥0∞) (hε : ∀ x, μ (closed x) ≤ ε)
    (hPB : ProductBound μ closed r) (hθ1 : θ ≤ 1) (hεθ : ε ≤ θ ^ ((r + 1) ^ d))
    (h3 : (3 : ℝ≥0∞) ^ d * θ ≤ 2⁻¹) (N D : ℕ)
    (hN : ∀ x ω, ω ∈ closed x → WithinInf (N : ℤ) x 0) :
    μ {ω | ¬ SmallClusters {x | ω ∉ closed x} D} ≤
      (2 * (N : ℝ≥0∞) + 1) ^ d * 2⁻¹ ^ (D / 2) := by
  refine (measure_mono ?_).trans (diameterBound d μ closed r ε θ hε hPB hθ1 hεθ h3 0 N D)
  intro ω hω
  simp only [mem_ofPred_eq] at hω ⊢
  by_contra hne
  apply hω
  intro C hC
  have hCcl : ∀ y ∈ C, ω ∈ closed y := fun y hy => by
    have := hC.2.1 hy
    simpa using this
  refine ⟨⟨N, fun y hy => hN y ω (hCcl y hy)⟩, fun y hy y' hy' => ?_⟩
  by_contra hyy'
  obtain ⟨z, hz⟩ := hC.1
  exact hne ⟨C, hC, ⟨z, hz, hN z ω (hCcl z hz)⟩, y, hy, y', hy', hyy'⟩

/-! ### Small helpers -/

/-- `2^{-m} = 2^{-(m : ℝ)}` (real power). -/
lemma inv_two_pow_eq_rpow (m : ℕ) : (2 : ℝ)⁻¹ ^ m = (2 : ℝ) ^ (-(m : ℝ)) := by
  rw [inv_pow, Real.rpow_neg (by norm_num), Real.rpow_natCast]

/-- `2^e / 4 · 2^{-w} / 2^{-m} = 2^{e - 2 - w + m}` (real powers). -/
lemma two_rpow_div_four_mul_div (e w : ℝ) (m : ℕ) :
    (2 : ℝ) ^ e / 4 * (2 : ℝ) ^ (-w) / (2 : ℝ)⁻¹ ^ m = (2 : ℝ) ^ (e - 2 - w + m) := by
  rw [inv_two_pow_eq_rpow, Real.rpow_add two_pos, Real.rpow_sub two_pos, Real.rpow_sub two_pos,
    Real.rpow_neg two_pos.le, Real.rpow_neg two_pos.le, Real.rpow_two]
  have h1 : (0 : ℝ) < (2 : ℝ) ^ w := Real.rpow_pos_of_pos two_pos w
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (m : ℝ) := Real.rpow_pos_of_pos two_pos _
  field_simp
  ring

/-- `2^e / 2^{-m} = 2^{e + m}` (real powers). -/
lemma two_rpow_div_inv_two_pow (e : ℝ) (m : ℕ) :
    (2 : ℝ) ^ e / (2 : ℝ)⁻¹ ^ m = (2 : ℝ) ^ (e + m) := by
  rw [inv_two_pow_eq_rpow, Real.rpow_add two_pos, Real.rpow_neg two_pos.le]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (m : ℝ) := Real.rpow_pos_of_pos two_pos _
  field_simp

/-- `2^w · (2^e / 4 · 2^{-w}) = 2^e / 4` (real powers). -/
lemma two_rpow_mul_div_four_mul (e w : ℝ) :
    (2 : ℝ) ^ w * ((2 : ℝ) ^ e / 4 * (2 : ℝ) ^ (-w)) = (2 : ℝ) ^ e / 4 := by
  rw [Real.rpow_neg two_pos.le]
  have h1 : (0 : ℝ) < (2 : ℝ) ^ w := Real.rpow_pos_of_pos two_pos w
  field_simp

/-- If `P[f < t] ≤ 1/4` then `P[t ≤ f] ≥ 3/4` (outer measure, `P` a probability measure). -/
lemma three_quarters_le_measure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} {t : ℝ} (h : P {ω | f ω < t} ≤ ENNReal.ofReal (1 / 4)) :
    ENNReal.ofReal (3 / 4) ≤ P {ω | t ≤ f ω} := by
  have h1 : (1 : ℝ≥0∞) ≤ P {ω | t ≤ f ω} + P {ω | f ω < t} := by
    rw [← measure_univ (μ := P)]
    refine (measure_mono fun ω _ => ?_).trans (measure_union_le _ _)
    rcases le_or_gt t (f ω) with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  have h2 : ENNReal.ofReal (3 / 4) + ENNReal.ofReal (1 / 4) = 1 := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  refine ENNReal.le_of_add_le_add_right (a := ENNReal.ofReal (1 / 4)) ENNReal.ofReal_ne_top ?_
  calc ENNReal.ofReal (3 / 4) + ENNReal.ofReal (1 / 4) = 1 := h2
    _ ≤ P {ω | t ≤ f ω} + P {ω | f ω < t} := h1
    _ ≤ P {ω | t ≤ f ω} + ENNReal.ofReal (1 / 4) := add_le_add le_rfl h

/-! ### Elementary asymptotics -/

/-- `0 < log 2 < 1`. -/
lemma log_two_pos_lt_one : 0 < Real.log 2 ∧ Real.log 2 < 1 :=
  ⟨Real.log_pos one_lt_two, by have := Real.log_two_lt_d9; linarith⟩

/-- `(log n)^k ≤ c n` for all large `n` (`c > 0`). -/
lemma eventually_log_pow_le_mul (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log n ^ k ≤ c * n := by
  have h := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero).comp
    tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hc)
  filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  simp only [Function.comp, one_mul, add_zero] at hn
  rw [div_lt_iff₀ hn0] at hn
  linarith

/-- `K ≤ n` for all large `n`. -/
lemma eventually_ge_real (K : ℝ) : ∀ᶠ n : ℕ in atTop, K ≤ n := by
  filter_upwards [eventually_ge_atTop ⌈K⌉₊] with n hn
  exact (Nat.le_ceil K).trans (by exact_mod_cast hn)

/-- For `k ≥ k₀`, `C e^{-k/C} ≤ θ` (`C, θ > 0`). -/
lemma exists_mul_exp_neg_div_le {C θ : ℝ} (hC : 0 < C) (hθ : 0 < θ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → C * Real.exp (-(k : ℝ) / C) ≤ θ := by
  refine ⟨⌈C * Real.log (C / θ)⌉₊, fun k hk => ?_⟩
  have h1 : C * Real.log (C / θ) ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have h2 : -(k : ℝ) / C ≤ -Real.log (C / θ) := by
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ hC]
    linarith
  calc C * Real.exp (-(k : ℝ) / C) ≤ C * Real.exp (-Real.log (C / θ)) := by gcongr
    _ = θ := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp

/-- **Small `n` in a super-exponential bound**: for `n < n₀`, `1 ≤ C e^{-n log n}` with
`C = e^{n₀ log n₀} + 1`. -/
lemma exists_superExp_const (n₀ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n < n₀ → 1 ≤ C * Real.exp (-(n : ℝ) * Real.log n) := by
  refine ⟨Real.exp ((n₀ : ℝ) * Real.log n₀) + 1, by positivity, fun n hn => ?_⟩
  have hmono : (n : ℝ) * Real.log n ≤ (n₀ : ℝ) * Real.log n₀ := by
    have h0 : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    have h1 : (n : ℝ) ≤ n₀ := by exact_mod_cast hn.le
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp only [Nat.cast_zero, zero_mul]
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    · have h2 : Real.log (n : ℝ) ≤ Real.log n₀ :=
        Real.log_le_log (by exact_mod_cast hpos) h1
      calc (n : ℝ) * Real.log n ≤ (n₀ : ℝ) * Real.log n :=
            mul_le_mul_of_nonneg_right h1 h0
        _ ≤ (n₀ : ℝ) * Real.log n₀ := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
  have h3 : 1 ≤ Real.exp ((n₀ : ℝ) * Real.log n₀) * Real.exp (-(n : ℝ) * Real.log n) := by
    rw [← Real.exp_add]
    exact Real.one_le_exp (by linarith)
  have h4 := Real.exp_pos (-(n : ℝ) * Real.log n)
  nlinarith

/-- **Polynomial against a Gaussian factor**: for `A, B ≥ 0`, `b > 0`, any `c` and `k`,
`(A n² + B)^k e^{-(b n² - c)} ≤ e^{-n log n}` for all large `n`. -/
lemma eventually_poly_mul_exp_neg_sq_le (A B c : ℝ) (k : ℕ) {b : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb : 0 < b) : ∀ᶠ n : ℕ in atTop,
      (A * (n : ℝ) ^ 2 + B) ^ k * Real.exp (-(b * (n : ℝ) ^ 2 - c)) ≤
        Real.exp (-(n : ℝ) * Real.log n) := by
  set M : ℝ := A + B + 1 with hM
  have hM1 : 1 ≤ M := by linarith
  set K₀ : ℝ := k * Real.log M + |c| with hK₀
  have hK₀0 : 0 ≤ K₀ := by
    have : 0 ≤ Real.log M := Real.log_nonneg hM1
    positivity
  filter_upwards [eventually_log_pow_le_mul 1 (c := b / 4) (by positivity),
    eventually_ge_real ((2 * k * (b / 4) + K₀) / (3 * b / 4) + 1)] with n hlog hn
  rw [pow_one] at hlog
  have hn1 : (1 : ℝ) ≤ n := by
    have : 0 ≤ (2 * k * (b / 4) + K₀) / (3 * b / 4) := by positivity
    linarith
  have hn0 : (0 : ℝ) < n := by linarith
  -- `(A n² + B)^k ≤ M^k e^{2k log n}`
  have hbase : A * (n : ℝ) ^ 2 + B ≤ M * (n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
    nlinarith
  have hpow : (A * (n : ℝ) ^ 2 + B) ^ k ≤ Real.exp (k * Real.log M + 2 * k * Real.log n) := by
    calc (A * (n : ℝ) ^ 2 + B) ^ k ≤ (M * (n : ℝ) ^ 2) ^ k :=
          pow_le_pow_left₀ (by positivity) hbase k
      _ = Real.exp (k * Real.log M + 2 * k * Real.log n) := by
          rw [show (k : ℝ) * Real.log M + 2 * k * Real.log n =
              k * Real.log (M * (n : ℝ) ^ 2) by
                rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring,
            Real.exp_nat_mul, Real.exp_log (by positivity)]
  -- the exponents
  have hexp : k * Real.log M + 2 * k * Real.log n + -(b * (n : ℝ) ^ 2 - c) ≤
      -(n : ℝ) * Real.log n := by
    have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have h1 : (n : ℝ) * Real.log n ≤ (n : ℝ) * (b / 4 * n) :=
      mul_le_mul_of_nonneg_left hlog hn0.le
    have h2 : 2 * k * Real.log n ≤ 2 * k * (b / 4 * n) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have h3 : (2 * k * (b / 4) + K₀) / (3 * b / 4) ≤ n := by linarith
    rw [div_le_iff₀ (by positivity)] at h3
    have h4 : (2 * k * (b / 4) + K₀) * 1 ≤ (2 * k * (b / 4) + K₀) * n :=
      mul_le_mul_of_nonneg_left hn1 (by positivity)
    have h5 : n * (3 * b / 4) * 1 ≤ n * (3 * b / 4) * n :=
      mul_le_mul_of_nonneg_left hn1 (by positivity)
    have hc : c ≤ |c| := le_abs_self c
    nlinarith
  calc (A * (n : ℝ) ^ 2 + B) ^ k * Real.exp (-(b * (n : ℝ) ^ 2 - c))
      ≤ Real.exp (k * Real.log M + 2 * k * Real.log n) * Real.exp (-(b * (n : ℝ) ^ 2 - c)) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = Real.exp (k * Real.log M + 2 * k * Real.log n + -(b * (n : ℝ) ^ 2 - c)) :=
        (Real.exp_add _ _).symm
    _ ≤ Real.exp (-(n : ℝ) * Real.log n) := Real.exp_le_exp.2 hexp

/-- **Polynomial against an exponential**: for `A, B ≥ 0`, `M ≥ 0`, `b > 0` and any `k`,
`M (A n² + B)^k ≤ e^{b n}` for all large `n`. -/
lemma eventually_mul_poly_le_exp (M A B : ℝ) (k : ℕ) {b : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hb : 0 < b) : ∀ᶠ n : ℕ in atTop,
      M * (A * (n : ℝ) ^ 2 + B) ^ k ≤ Real.exp (b * n) := by
  set M' : ℝ := A + B + 1 with hM'
  have hM'1 : 1 ≤ M' := by linarith
  set K₀ : ℝ := Real.log (M + 1) + k * Real.log M' with hK₀
  have hK₀0 : 0 ≤ K₀ := by
    have : 0 ≤ Real.log M' := Real.log_nonneg hM'1
    have : 0 ≤ Real.log (M + 1) := Real.log_nonneg (by linarith)
    positivity
  filter_upwards [eventually_log_pow_le_mul 1 (c := b / (4 * k + 1)) (by positivity),
    eventually_ge_real (2 * K₀ / b + 1)] with n hlog hn
  rw [pow_one] at hlog
  have hn1 : (1 : ℝ) ≤ n := by
    have : 0 ≤ 2 * K₀ / b := by positivity
    linarith
  have hbase : A * (n : ℝ) ^ 2 + B ≤ M' * (n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
    nlinarith
  have hpow : M * (A * (n : ℝ) ^ 2 + B) ^ k ≤
      Real.exp (Real.log (M + 1) + k * Real.log M' + 2 * k * Real.log n) := by
    calc M * (A * (n : ℝ) ^ 2 + B) ^ k ≤ (M + 1) * (M' * (n : ℝ) ^ 2) ^ k := by
          gcongr
          · linarith
      _ = Real.exp (Real.log (M + 1) + k * Real.log M' + 2 * k * Real.log n) := by
          rw [show Real.log (M + 1) + k * Real.log M' + 2 * k * Real.log n =
              Real.log (M + 1) + k * Real.log (M' * (n : ℝ) ^ 2) by
                rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring,
            Real.exp_add, Real.exp_nat_mul, Real.exp_log (by positivity),
            Real.exp_log (by positivity)]
  refine hpow.trans (Real.exp_le_exp.2 ?_)
  have h1 : 2 * k * Real.log n ≤ 2 * k * (b / (4 * k + 1) * n) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have h2 : 2 * k * (b / (4 * k + 1) * n) ≤ b / 2 * n := by
    have hk : (0 : ℝ) < 4 * k + 1 := by positivity
    rw [show 2 * k * (b / (4 * k + 1) * n) = (2 * k / (4 * k + 1)) * (b * n) by ring]
    have : 2 * (k : ℝ) / (4 * k + 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ hk]
      linarith
    nlinarith [mul_pos hb (by linarith : (0 : ℝ) < n)]
  have h3 : 2 * K₀ / b ≤ n := by linarith
  rw [div_le_iff₀ hb] at h3
  linarith

/-! ### The coarse scale `m(n) = 2 ⌊log₂ n⌋ + 2` -/

/-- **The coarse scale** of the super-exponential bounds (MA7 D-4.9, D-4.10 use
`⌊n/(log n)²⌋`; here `m(n) = 2 ⌊log₂ n⌋ + 2`, so that `n² < 2^{m(n)} ≤ 4 n²`). -/
def superScale (n : ℕ) : ℕ := 2 * Nat.log 2 n + 2

lemma sq_lt_two_pow_superScale (n : ℕ) : n ^ 2 < 2 ^ superScale n := by
  have h := Nat.lt_pow_succ_log_self one_lt_two n
  calc n ^ 2 < (2 ^ (Nat.log 2 n).succ) ^ 2 := Nat.pow_lt_pow_left h two_ne_zero
    _ = 2 ^ superScale n := by
        rw [← pow_mul]
        unfold superScale
        congr 1
        omega

lemma two_pow_superScale_le {n : ℕ} (hn : n ≠ 0) : 2 ^ superScale n ≤ 4 * n ^ 2 := by
  have h := Nat.pow_log_le_self 2 hn
  calc 2 ^ superScale n = 4 * (2 ^ Nat.log 2 n) ^ 2 := by unfold superScale; ring
    _ ≤ 4 * n ^ 2 := by gcongr

lemma sq_lt_two_pow_superScale_real (n : ℕ) : (n : ℝ) ^ 2 < (2 : ℝ) ^ superScale n := by
  exact_mod_cast sq_lt_two_pow_superScale n

lemma two_pow_superScale_le_real {n : ℕ} (hn : n ≠ 0) :
    (2 : ℝ) ^ superScale n ≤ 4 * (n : ℝ) ^ 2 := by
  exact_mod_cast two_pow_superScale_le hn

lemma two_le_superScale (n : ℕ) : 2 ≤ superScale n := by
  unfold superScale
  omega

/-- `m(n) log 2 ≤ 2 log n + 2 log 2`. -/
lemma superScale_mul_log_two_le {n : ℕ} (hn : n ≠ 0) :
    (superScale n : ℝ) * Real.log 2 ≤ 2 * Real.log n + 2 * Real.log 2 := by
  have h := Nat.pow_log_le_self 2 hn
  have h' : (2 : ℝ) ^ Nat.log 2 n ≤ n := by exact_mod_cast h
  have hlog : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h'
  unfold superScale
  push_cast
  linarith

/-- `m(n) ≤ c n` for all large `n` (`c > 0`). -/
lemma eventually_superScale_le_mul {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (superScale n : ℝ) ≤ c * n := by
  obtain ⟨hl0, hl1⟩ := log_two_pos_lt_one
  filter_upwards [eventually_log_pow_le_mul 1 (c := c * Real.log 2 / 4) (by positivity),
    eventually_ge_real (4 / c), eventually_ge_atTop 1] with n hlog hn hn1
  rw [pow_one] at hlog
  have h := superScale_mul_log_two_le (n := n) (by omega)
  have h4 : 4 ≤ c * n := by
    rw [div_le_iff₀ hc] at hn
    linarith
  have key : (superScale n : ℝ) * Real.log 2 ≤ c * n * Real.log 2 := by nlinarith
  exact le_of_mul_le_mul_right key hl0

/-- `K ≤ 2^{m(n)}` for all large `n`. -/
lemma eventually_le_two_pow_superScale (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, K ≤ (2 : ℝ) ^ superScale n := by
  filter_upwards [eventually_ge_real K, eventually_ge_atTop 1] with n hn hn1
  have h1 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    nlinarith
  linarith [sq_lt_two_pow_superScale_real n]

/-- **The Gaussian tail at the coarse scale is super-exponential**: with `L = m(n) log 2` (the
variance of `h_{m(n)}`), for all large `n`: `A L + C √L + C ≤ c n / 2` and
`2 e^{-(c n/2)²/(2 L)} ≤ e^{-n log n}`. -/
lemma eventually_field_superExp (A C c : ℝ) (hc : 0 < c) : ∀ᶠ n : ℕ in atTop,
    A * ((superScale n : ℝ) * Real.log 2) + C * √((superScale n : ℝ) * Real.log 2) + C ≤
      c * n / 2 ∧
    2 * Real.exp (-(c * n / 2) ^ 2 / (2 * ((superScale n : ℝ) * Real.log 2))) ≤
      Real.exp (-(n : ℝ) * Real.log n) := by
  obtain ⟨hl0, hl1⟩ := log_two_pos_lt_one
  set K₁ : ℝ := |A| + |C| with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  set ε : ℝ := c ^ 2 / 256 with hε
  have hε0 : 0 < ε := by positivity
  filter_upwards [eventually_log_pow_le_mul 1 (c := c / (8 * K₁ + 1)) (by positivity),
    eventually_log_pow_le_mul 1 (c := ε) hε0, eventually_log_pow_le_mul 2 (c := ε) hε0,
    eventually_ge_real ((8 * K₁ + 8 * |C|) / c), eventually_ge_real (256 / c ^ 2 + 2),
    eventually_ge_atTop 1] with n hlogA hlogε hlog2 hnA hnB hn1
  rw [pow_one] at hlogA hlogε
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  set L : ℝ := (superScale n : ℝ) * Real.log 2 with hL
  have hL0 : 0 < L := by
    have : (2 : ℝ) ≤ superScale n := by exact_mod_cast two_le_superScale n
    positivity
  have hLle : L ≤ 2 * Real.log n + 2 := by
    have := superScale_mul_log_two_le (n := n) (by omega)
    linarith
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1'
  constructor
  · -- `A L + C √L + C ≤ (|A| + |C|) L + 2|C| ≤ c n / 2`
    have hsq : √L ≤ L + 1 := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    have h1 : A * L ≤ |A| * L := mul_le_mul_of_nonneg_right (le_abs_self A) hL0.le
    have h2 : C * √L ≤ |C| * (L + 1) :=
      (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg L)).trans
        (mul_le_mul_of_nonneg_left hsq (abs_nonneg C))
    have h3 : K₁ * L ≤ K₁ * (2 * Real.log n + 2) := mul_le_mul_of_nonneg_left hLle hK₁0
    have h4 : (8 * K₁ + 1) * Real.log n ≤ c * n := by
      have hpos : (0 : ℝ) < 8 * K₁ + 1 := by positivity
      calc (8 * K₁ + 1) * Real.log n ≤ (8 * K₁ + 1) * (c / (8 * K₁ + 1) * n) :=
            mul_le_mul_of_nonneg_left hlogA hpos.le
        _ = c * n := by field_simp
    have h5 : 8 * K₁ + 8 * |C| ≤ c * n := by
      rw [div_le_iff₀ hc] at hnA
      linarith
    have hC := le_abs_self C
    nlinarith
  · -- `2 e^{-(cn/2)²/(2L)} ≤ e^{-n log n}`
    have hkey : (n * Real.log n + Real.log 2) * (2 * L) ≤ (c * n / 2) ^ 2 := by
      have h1 : (n * Real.log n + Real.log 2) * (2 * L) ≤
          (n * Real.log n + 1) * (2 * (2 * Real.log n + 2)) := by
        have : 0 ≤ n * Real.log n + Real.log 2 := by positivity
        have h' : (n * Real.log n + Real.log 2) * (2 * L) ≤
            (n * Real.log n + Real.log 2) * (2 * (2 * Real.log n + 2)) := by
          nlinarith
        have h'' : (n * Real.log n + Real.log 2) * (2 * (2 * Real.log n + 2)) ≤
            (n * Real.log n + 1) * (2 * (2 * Real.log n + 2)) := by
          have : 0 ≤ 2 * (2 * Real.log n + 2) := by positivity
          nlinarith
        linarith
      have e : (n * Real.log n + 1) * (2 * (2 * Real.log n + 2)) =
          4 * (n * Real.log n ^ 2) + 4 * (n * Real.log n) + 4 * Real.log n + 4 := by ring
      have h2 : n * Real.log n ^ 2 ≤ n * (ε * n) := mul_le_mul_of_nonneg_left hlog2 hnpos.le
      have h3 : n * Real.log n ≤ n * (ε * n) := mul_le_mul_of_nonneg_left hlogε hnpos.le
      have h4 : Real.log n ≤ n := by
        have := Real.log_le_sub_one_of_pos hnpos
        linarith
      have h5 : 256 / c ^ 2 + 2 ≤ n := hnB
      have h6 : 256 ≤ c ^ 2 * (n - 2) := by
        have : 256 / c ^ 2 ≤ n - 2 := by linarith
        rw [div_le_iff₀ (by positivity)] at this
        linarith
      have h7 : 256 * n ≤ c ^ 2 * (n - 2) * n := by nlinarith
      rw [e] at h1
      have hεe : ε * 256 = c ^ 2 := by rw [hε]; field_simp
      nlinarith
    have hexp : Real.log 2 + -(c * n / 2) ^ 2 / (2 * L) ≤ -(n : ℝ) * Real.log n := by
      have h2L : 0 < 2 * L := by positivity
      have : (n * Real.log n + Real.log 2) ≤ (c * n / 2) ^ 2 / (2 * L) := by
        rwa [le_div_iff₀ h2L]
      rw [neg_div]
      linarith
    calc 2 * Real.exp (-(c * n / 2) ^ 2 / (2 * L))
        = Real.exp (Real.log 2 + -(c * n / 2) ^ 2 / (2 * L)) := by
          rw [Real.exp_add, Real.exp_log two_pos]
      _ ≤ Real.exp (-(n : ℝ) * Real.log n) := Real.exp_le_exp.2 hexp

/-- `(1/2)^{⌊D/2⌋} ≤ e^{-(b n² - 2) log 2 / 2}` when `b 2^{m(n)} ≤ D + 1`. -/
lemma inv_two_pow_half_le {n D : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hD : b * (2 : ℝ) ^ superScale n ≤ D + 1) :
    (2⁻¹ : ℝ) ^ (D / 2) ≤ Real.exp (-(b * Real.log 2 / 2 * (n : ℝ) ^ 2 - Real.log 2)) := by
  obtain ⟨hl0, -⟩ := log_two_pos_lt_one
  have hDiv : (D : ℝ) ≤ 2 * ((D / 2 : ℕ) : ℝ) + 1 := by
    have : D ≤ 2 * (D / 2) + 1 := by omega
    exact_mod_cast this
  have hsq : b * (n : ℝ) ^ 2 ≤ b * (2 : ℝ) ^ superScale n :=
    mul_le_mul_of_nonneg_left (sq_lt_two_pow_superScale_real n).le hb
  have hj : b * Real.log 2 / 2 * (n : ℝ) ^ 2 - Real.log 2 ≤ ((D / 2 : ℕ) : ℝ) * Real.log 2 := by
    have : b * (n : ℝ) ^ 2 - 2 ≤ 2 * ((D / 2 : ℕ) : ℝ) := by linarith
    nlinarith
  have e : (2⁻¹ : ℝ) ^ (D / 2) = Real.exp (-(((D / 2 : ℕ) : ℝ) * Real.log 2)) := by
    rw [show -(((D / 2 : ℕ) : ℝ) * Real.log 2) = ((D / 2 : ℕ) : ℝ) * Real.log 2⁻¹ by
      rw [Real.log_inv]; ring, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [e]
  exact Real.exp_le_exp.2 (by linarith)

/-- **The Peierls term at the coarse scale is super-exponential**: if `N ≤ a 2^{m(n)} + 1` and
`b 2^{m(n)} ≤ D + 1` (`a ≥ 0`, `b > 0`), then `(2N+1)^d 2^{-⌊D/2⌋} ≤ e^{-n log n}` for large `n`. -/
lemma eventually_peierls_superExp (d : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop, ∀ N D : ℕ, (N : ℝ) ≤ a * (2 : ℝ) ^ superScale n + 1 →
      b * (2 : ℝ) ^ superScale n ≤ D + 1 →
        (2 * (N : ℝ≥0∞) + 1) ^ d * 2⁻¹ ^ (D / 2) ≤
          ENNReal.ofReal (Real.exp (-(n : ℝ) * Real.log n)) := by
  obtain ⟨hl0, -⟩ := log_two_pos_lt_one
  filter_upwards [eventually_poly_mul_exp_neg_sq_le (8 * a) 3 (Real.log 2) d
    (b := b * Real.log 2 / 2) (by positivity) (by norm_num) (by positivity),
    eventually_ge_atTop 1] with n hn hn1 N D hN hD
  rw [HigherDimLFPP.L33.box_mul_pow_eq_ofReal]
  refine ENNReal.ofReal_le_ofReal (le_trans ?_ hn)
  have h4 := two_pow_superScale_le_real (n := n) (by omega)
  have hbase : 2 * (N : ℝ) + 1 ≤ 8 * a * (n : ℝ) ^ 2 + 3 := by nlinarith
  exact mul_le_mul (pow_le_pow_left₀ (by positivity) hbase d) (inv_two_pow_half_le hb.le hD)
    (by positivity) (by positivity)

/-! ### The field at the coarse scale -/

/-- **Field tail at the coarse scale** (MA7 D-4.9 `𝒢₁`, D-4.10 `𝒢₃`), for any version `ψ` of
`h_{m(n)} = H_{2^{-m(n)}, 1}`: for `R ≥ 0` and `c > 0` there is `n₀` with
`P[∃ z ∈ B̄_R(0), |ψ(z)| > c n] ≤ e^{-n log n}` for every `n ≥ n₀` (`ψ` has variance
`m(n) log 2 = O(log n)`; L3b2's sharp Borell–TIS bound `exists_sup_cbox_gaussian_tail`). -/
theorem exists_field_superExp' {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {R : ℝ} (hR : 0 ≤ R)
    {c : ℝ} (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
      IsWhiteNoise P W → ∀ n : ℕ, n₀ ≤ n → ∀ {ψ : Rd d → Ω → ℝ},
        IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ superScale n) 1 ψ →
          P {ω | ∃ z ∈ cbox (0 : Rd d) R, c * n < |ψ z ω|} ≤
            ENNReal.ofReal (Real.exp (-(n : ℝ) * Real.log n)) := by
  obtain ⟨C, hC0, hC⟩ := exists_sup_cbox_gaussian_tail hκ hR
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (eventually_field_superExp (√(2 * d)) C c hc)
  refine ⟨n₀, fun {Ω} _ {P} {W} hW n hn {ψ} hψ => ?_⟩
  obtain ⟨h1, h2⟩ := hn₀ n hn
  obtain ⟨hl0, -⟩ := log_two_pos_lt_one
  have hL0 : 0 < (superScale n : ℝ) * Real.log 2 := by
    have : (2 : ℝ) ≤ superScale n := by exact_mod_cast two_le_superScale n
    positivity
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, c * n - (√(2 * d) * ((superScale n : ℝ) * Real.log 2) +
      C * √((superScale n : ℝ) * Real.log 2) + C) = u := ⟨_, rfl⟩
  have hu : c * n / 2 ≤ u := by linarith
  have hu0 : 0 ≤ u := by
    have : 0 ≤ c * n := by positivity
    linarith
  have hb := hC hW (a := (2 : ℝ)⁻¹ ^ superScale n) (b := 1) (by positivity)
    (pow_le_one₀ (by norm_num) (by norm_num)) hψ 0 hu0
  rw [log_one_div_inv_two_pow, mul_one] at hb
  have e : √(2 * d) * ((superScale n : ℝ) * Real.log 2) +
      C * √((superScale n : ℝ) * Real.log 2) + C + u = c * n := by
    rw [← hudef]
    ring
  rw [e] at hb
  refine hb.trans (ENNReal.ofReal_le_ofReal (le_trans ?_ h2))
  have hsq : (c * n / 2) ^ 2 ≤ u ^ 2 := by
    have : 0 ≤ c * n / 2 := by positivity
    nlinarith
  have hdiv : (c * n / 2) ^ 2 / (2 * ((superScale n : ℝ) * Real.log 2)) ≤
      u ^ 2 / (2 * ((superScale n : ℝ) * Real.log 2)) :=
    div_le_div_of_nonneg_right hsq (by positivity)
  have : Real.exp (-u ^ 2 / (2 * ((superScale n : ℝ) * Real.log 2))) ≤
      Real.exp (-(c * n / 2) ^ 2 / (2 * ((superScale n : ℝ) * Real.log 2))) := by
    rw [Real.exp_le_exp, neg_div, neg_div, neg_le_neg_iff]
    exact hdiv
  linarith

/-- **Field tail at the coarse scale** for a dyadic realization: `h_{m(n)} = H (m(n))`. -/
theorem exists_field_superExp {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {R : ℝ} (hR : 0 ≤ R)
    {c : ℝ} (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
      {H : ℕ → Rd d → Ω → ℝ}, IsDyadicRealization κ P W H → ∀ n : ℕ, n₀ ≤ n →
        P {ω | ∃ z ∈ cbox (0 : Rd d) R, c * n < |H (superScale n) z ω|} ≤
          ENNReal.ofReal (Real.exp (-(n : ℝ) * Real.log n)) := by
  obtain ⟨n₀, hn₀⟩ := exists_field_superExp' hκ hR hc
  exact ⟨n₀, fun {Ω} _ {P} {W} {H} hH n hn => hn₀ hH.whiteNoise n hn (hH.band (superScale n))⟩

/-- **Every white noise carries a dyadic realization** (HigherDimLFPP `exists_isBandVersion`). -/
theorem exists_isDyadicRealization {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} (hW : IsWhiteNoise P W) :
    ∃ H : ℕ → Rd d → Ω → ℝ, IsDyadicRealization κ P W H := by
  have h : ∀ k : ℕ, ∃ G : Rd d → Ω → ℝ, IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ k) 1 G := fun k =>
    exists_isBandVersion hκ hW (by positivity) 1
  choose H hH using h
  exact ⟨H, ⟨hW, hH⟩⟩

end DGZ

end HigherDimLQGMetric
