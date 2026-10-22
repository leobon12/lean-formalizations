import HigherDimLQGMetric.DGZ.NiceBoxShell

/-!
# DGZ §5.1: independence of nice boxes (packet L4a1)

Source: [2] Remark 5.4 (TeX l. 2137–2148), Lemma 5.7 (l. 2264–2323); planning audit MA7 D-5.3
(Remark 5.4′), G24; blueprint Lemma `r2:lem:54`(ii), (iii).

Setting: a dyadic realization `(P, W, H)` (`H q` a continuous version of `h_q = H_{2^{-q},1}` over
the white noise `W`), so the bands `H q - H p` (`p ≤ q`) are versions of `H_{2^{-q},2^{-p}}`
(`isBandVersion_sub_of_realization`); `ρ` is a support radius of the kernel (`κ y = 0` for `‖y‖ ≥
ρ`; DGZ's `r₀`).

* `indep_bandSigma_of_far`: the band σ-algebras `bandSigma H p₀ A`, `bandSigma H p₀ B` (bands below
  `2^{-p₀}` on `A`, `B`) are independent when `‖z - w‖ ≥ 2ρ 2^{-p₀}` for `z ∈ A`, `w ∈ B` (finite
  range, HigherDimLFPP `IsWhiteNoise.indepFun_of_ae_eq` and
  `inner_bandVec_eq_zero_of_two_mul_min_le`).
* `indep_niceBox_of_far` (**target**; MA7 Remark 5.4′, G24): the statuses of two `a_j`-boxes whose
  centres `s_j u`, `s_j u'` are at `ℓ^∞`-distance `≥ R s_j` (`R ≤ |u_i - u'_i|` for some `i`) are
  independent, for `R ≥ 2ρ + 10` (DGZ: `R = ⌊100 r₀⌋ + 100 ≥ 2(5 + r₀)`); σ-algebra form
  `indep_bandSigma_niceBox_of_far` (so families of statuses in far sets are independent as well) and
  the product form `measure_bad_inter_bad_eq`.
* `indep_niceCEvent_fine` (MA7 Remark 5.4′: "`𝒞(x,z)` is independent of the fine fields on
  `B_{(R+5)s_{j-1}}(z)`"; blueprint `r2:lem:54`(iii)): the σ-algebra `cSigma` of the fields used by
  `𝒞(x,z)` (`x = s_j u`, `z = s_{j-1} w ∈ B_{s_j}(x)`) — the band `h_{n-a_j,n}` on the closed shell
  `B̄_{4s_j}(x) \ B_{2s_j}(x)`, the two certificate bands on the closed shell `B̄_{4Rs_{j-1}}(z) \
  B_{2Rs_{j-1}}(z)` and `h_{n-a_j,n-a_{j-1}}` on `B̄_{4Rs_{j-1}}(z)` — is independent of the bands
  below `s_{j-1}` on `B̄_{(R+4)s_{j-1}}(z)`, provided `(2ρ + R + 4) s_{j-1} ≤ s_j` and `R ≥ 2ρ + 4`;
  with `measurableSet_niceCEvent_cSigma` and `measurableSet_exists_bad_fine` this gives
  `indepSet_niceCEvent_exists_bad`: `𝒞(x,z)` is independent of `{some a_{j-1}-box contained in B_{R
  s_{j-1}}(z) is bad}` (DGZ Lemma 5.7, the event `ℬ₂`), and the product form
  `measure_not_niceCEvent_inter_exists_bad_eq`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox obox_subset_cbox)

variable {d : ℕ}

/-! ## Geometry -/

/-- A coordinate gap bounds the Euclidean distance. -/
theorem abs_sub_le_norm_sub (z w : Rd d) (i : Fin d) : |z i - w i| ≤ ‖z - w‖ := by
  have h := PiLp.norm_apply_le (z - w) i
  rwa [PiLp.sub_apply, Real.norm_eq_abs] at h

/-- Points of the boxes `B̄_{5s}(s u)`, `B̄_{5s}(s u')` with `R ≤ |u_i - u'_i|` are at Euclidean
distance `≥ (R - 10) s`. -/
theorem le_norm_sub_of_far {s : ℝ} (hs : 0 < s) {u u' : Zd d} {R : ℝ} {i : Fin d}
    (hi : R ≤ |((u i - u' i : ℤ) : ℝ)|) {z w : Rd d} (hz : z ∈ cbox (latPt s u) (5 * s))
    (hw : w ∈ cbox (latPt s u') (5 * s)) : (R - 10) * s ≤ ‖z - w‖ := by
  refine le_trans ?_ (abs_sub_le_norm_sub z w i)
  have h1 : |z i - s * (u i : ℝ)| ≤ 5 * s := by have := hz i; rwa [latPt_apply] at this
  have h2 : |w i - s * (u' i : ℝ)| ≤ 5 * s := by have := hw i; rwa [latPt_apply] at this
  have h3 : R * s ≤ |s * (u i : ℝ) - s * (u' i : ℝ)| := by
    rw [← mul_sub, abs_mul, abs_of_pos hs]
    push_cast at hi
    have := mul_le_mul_of_nonneg_left hi hs.le
    linarith
  have h4 := abs_sub_abs_le_abs_sub (s * (u i : ℝ) - s * (u' i : ℝ)) (z i - w i)
  have h5 : |(s * (u i : ℝ) - s * (u' i : ℝ)) - (z i - w i)| ≤ 10 * s := by
    calc |(s * (u i : ℝ) - s * (u' i : ℝ)) - (z i - w i)|
        = |(s * (u i : ℝ) - z i) + (w i - s * (u' i : ℝ))| := by ring_nf
      _ ≤ |s * (u i : ℝ) - z i| + |w i - s * (u' i : ℝ)| := abs_add_le _ _
      _ ≤ 10 * s := by rw [abs_sub_comm] at h1; linarith
  linarith

/-! ## Independence of band σ-algebras on far sets -/

section Indep

variable {κ : Rd d → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
  {H : ℕ → Rd d → Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- `bandSigma H p₀ A` is below the σ-algebra of the whole family of bands `(q, z) ↦ H (p₀+q) z -
H p₀ z` on `A`. -/
theorem bandSigma_le_comap_family (p₀ : ℕ) (A : Set (Rd d)) :
    bandSigma H p₀ A ≤ MeasurableSpace.comap
      (fun ω (s : ℕ × A) => H (p₀ + s.1) s.2 ω - H p₀ s.2 ω) MeasurableSpace.pi := by
  refine bandSigma_le_of_measurable fun q hq z hz => ?_
  have h := (measurable_pi_apply ((q - p₀, ⟨z, hz⟩) : ℕ × A)).comp
    (comap_measurable (fun ω (s : ℕ × A) => H (p₀ + s.1) s.2 ω - H p₀ s.2 ω))
  have e : p₀ + (q - p₀) = q := Nat.add_sub_cancel' hq
  simp only [Function.comp_def, e] at h
  exact h

/-- **Finite range for the band σ-algebras**: if `2ρ 2^{-p₀} ≤ ‖z - w‖` for `z ∈ A`, `w ∈ B`, the
bands below `2^{-p₀}` on `A` and on `B` are independent. -/
theorem indep_bandSigma_of_far (hκ : IsLFPPKernel κ) (hH : IsDyadicRealization κ P W H)
    {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {p₀ : ℕ} {A B : Set (Rd d)}
    (hAB : ∀ z ∈ A, ∀ w ∈ B, 2 * ρ * (2 : ℝ)⁻¹ ^ p₀ ≤ ‖z - w‖) :
    Indep (bandSigma H p₀ A) (bandSigma H p₀ B) P := by
  have hind := hH.whiteNoise.indepFun_of_ae_eq
    (fun s : ℕ × A => bandVec κ ((2 : ℝ)⁻¹ ^ (p₀ + s.1)) ((2 : ℝ)⁻¹ ^ p₀) s.2)
    (fun t : ℕ × B => bandVec κ ((2 : ℝ)⁻¹ ^ (p₀ + t.1)) ((2 : ℝ)⁻¹ ^ p₀) t.2)
    (fun s t => inner_bandVec_eq_zero_of_two_mul_min_le hκ hρ (by positivity) (by positivity)
      (by rw [min_self]; exact hAB s.2 s.2.2 t.2 t.2.2))
    (X := fun s ω => H (p₀ + s.1) s.2 ω - H p₀ s.2 ω)
    (Y := fun t ω => H (p₀ + t.1) t.2 ω - H p₀ t.2 ω)
    (fun s => (isBandVersion_sub_of_realization hκ hH (Nat.le_add_right p₀ s.1)).ae_eq s.2)
    (fun t => (isBandVersion_sub_of_realization hκ hH (Nat.le_add_right p₀ t.1)).ae_eq t.2)
  exact indep_of_indep_of_le_left (indep_of_indep_of_le_right hind
    (bandSigma_le_comap_family p₀ B)) (bandSigma_le_comap_family p₀ A)

/-- **Statuses of far boxes are independent**, σ-algebra form (MA7 D-5.3, Remark 5.4′, G24): the
band σ-algebras below `s_j` on `B̄_{5s_j}(s_j u)` and `B̄_{5s_j}(s_j u')` are independent when
`R ≤ |u_i - u'_i|` for some `i` and `2ρ + 10 ≤ R`. -/
theorem indep_bandSigma_niceBox_of_far (hκ : IsLFPPKernel κ) (hH : IsDyadicRealization κ P W H)
    {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) (p : NiceParams) (hR : 2 * ρ + 10 ≤ (p.R : ℝ))
    (j : ℕ) {u u' : Zd d} (hfar : ∃ i, (p.R : ℤ) ≤ |u i - u' i|) :
    Indep (bandSigma H (p.n - p.a j) (cbox (latPt (p.s j) u) (5 * p.s j)))
      (bandSigma H (p.n - p.a j) (cbox (latPt (p.s j) u') (5 * p.s j))) P := by
  obtain ⟨i, hi⟩ := hfar
  have hρ0 := hκ.radius_pos hρ
  refine indep_bandSigma_of_far hκ hH hρ fun z hz w hw => ?_
  have hi' : (p.R : ℝ) ≤ |((u i - u' i : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast hi
  have h := le_norm_sub_of_far (p.s_pos j) hi' hz hw
  have hs := p.s_pos j
  have e : (2 : ℝ)⁻¹ ^ (p.n - p.a j) = p.s j := rfl
  rw [e]
  nlinarith

/-- **Statuses of far boxes are independent** (target `indep_niceBox_of_far`; MA7 D-5.3,
Remark 5.4′, G24; blueprint `r2:lem:54`(ii)): for a dyadic realization, two `a_j`-boxes whose
centres are at `ℓ^∞`-distance `≥ R s_j` have independent statuses (`2ρ + 10 ≤ R`, `a` monotone,
`R ≥ 4`, `8 s_{i-1} ≤ s_i` and `R s_{i-1} ≤ s_i` for `2 ≤ i ≤ j`). -/
theorem indep_niceBox_of_far (hκ : IsLFPPKernel κ) (hH : IsDyadicRealization κ P W H)
    {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) (p : NiceParams) (hmono : Monotone p.a)
    (hR4 : 4 ≤ (p.R : ℝ)) (hR : 2 * ρ + 10 ≤ (p.R : ℝ)) {j : ℕ}
    (hgap : ∀ i, 2 ≤ i → i ≤ j → 8 * p.s (i - 1) ≤ p.s i ∧ (p.R : ℝ) * p.s (i - 1) ≤ p.s i)
    {u u' : Zd d} (hfar : ∃ i, (p.R : ℤ) ≤ |u i - u' i|) :
    IndepSet {ω | NiceBox p (fun q z => H q z ω) j u}
      {ω | NiceBox p (fun q z => H q z ω) j u'} P := by
  have hc : ∀ q ω, Continuous fun z => H q z ω := fun q => (hH.band q).continuous
  exact (indep_bandSigma_niceBox_of_far hκ hH hρ p hR j hfar).indepSet_of_measurableSet
    (niceBox_local hc p hmono hR4 hgap u) (niceBox_local hc p hmono hR4 hgap u')

/-- **The product formula for two far bad boxes** (DGZ Lemma 5.7, the event `ℬ₁`). -/
theorem measure_bad_inter_bad_eq (hκ : IsLFPPKernel κ) (hH : IsDyadicRealization κ P W H)
    {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) (p : NiceParams) (hmono : Monotone p.a)
    (hR4 : 4 ≤ (p.R : ℝ)) (hR : 2 * ρ + 10 ≤ (p.R : ℝ)) {j : ℕ}
    (hgap : ∀ i, 2 ≤ i → i ≤ j → 8 * p.s (i - 1) ≤ p.s i ∧ (p.R : ℝ) * p.s (i - 1) ≤ p.s i)
    {u u' : Zd d} (hfar : ∃ i, (p.R : ℤ) ≤ |u i - u' i|) :
    P ({ω | ¬ NiceBox p (fun q z => H q z ω) j u} ∩ {ω | ¬ NiceBox p (fun q z => H q z ω) j u'}) =
      P {ω | ¬ NiceBox p (fun q z => H q z ω) j u} *
        P {ω | ¬ NiceBox p (fun q z => H q z ω) j u'} := by
  have hc : ∀ q ω, Continuous fun z => H q z ω := fun q => (hH.band q).continuous
  have hind := indep_bandSigma_niceBox_of_far hκ hH hρ p hR j hfar
  rw [Indep_iff] at hind
  exact hind _ _ (niceBox_local hc p hmono hR4 hgap u).compl
    (niceBox_local hc p hmono hR4 hgap u').compl

end Indep

/-! ## Independence of `𝒞(x,z)` from the fine fields near `z` -/

section CEvent

variable {Ω : Type*}

/-- `comap (Φ ∘ g) ≤ comap g` for a measurable `Φ` (no measurable structure on `Ω` is involved). -/
theorem comap_comp_le_comap {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    (g : Ω → α) {Φ : α → β} (hΦ : Measurable Φ) :
    MeasurableSpace.comap (Φ ∘ g) mβ ≤ MeasurableSpace.comap g mα := by
  rw [← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hΦ.comap_le

/-- Restricting a field to `A` after a map `T : A → B` gives a smaller σ-algebra than restricting it
to `B`. -/
theorem comap_restrict_comp_le (X : Rd d → Ω → ℝ) {A B : Set (Rd d)} (T : Rd d → Rd d)
    (hT : ∀ z ∈ A, T z ∈ B) :
    MeasurableSpace.comap (fun ω (z : A) => X (T z) ω) MeasurableSpace.pi ≤
      MeasurableSpace.comap (fun ω (z : B) => X z ω) MeasurableSpace.pi :=
  comap_comp_le_comap (fun ω (z : B) => X z ω)
    (Φ := fun (F : B → ℝ) (z : A) => F ⟨T z, hT z z.2⟩)
    (measurable_pi_iff.2 fun _z => measurable_pi_apply _)

set_option warn.classDefReducibility false in
/-- The σ-algebra of the fields used by `𝒞(x,z)` (`x = s_j u`, `z = s_{j-1} w`): the band
`h_{n-a_j,n}` on the closed shell `B̄_{4s_j}(x) \ B_{2s_j}(x)`, the coarse and fine certificate
bands on the closed shell `B̄_{4Rs_{j-1}}(z) \ B_{2Rs_{j-1}}(z)`, and `h_{n-a_j,n-a_{j-1}}` on
`B̄_{4Rs_{j-1}}(z)`. -/
def cSigma (H : ℕ → Rd d → Ω → ℝ) (p : NiceParams) (j : ℕ) (u w : Zd d) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (z : (cbox (latPt (p.s j) u) (4 * p.s j) \
      obox (latPt (p.s j) u) (2 * p.s j) : Set (Rd d))) =>
      H p.n z ω - H (p.n - p.a j) z ω) MeasurableSpace.pi ⊔
    (MeasurableSpace.comap (fun ω (z : (cbox (latPt (p.s (j - 1)) w) (4 * p.R * p.s (j - 1)) \
        obox (latPt (p.s (j - 1)) w) (2 * p.R * p.s (j - 1)) : Set (Rd d))) =>
        H (p.certIdx (j - 1)) z ω - H (p.n - p.a (j - 1)) z ω) MeasurableSpace.pi ⊔
      (MeasurableSpace.comap (fun ω (z : (cbox (latPt (p.s (j - 1)) w) (4 * p.R * p.s (j - 1)) \
          obox (latPt (p.s (j - 1)) w) (2 * p.R * p.s (j - 1)) : Set (Rd d))) =>
          H p.n z ω - H (p.certIdx (j - 1)) z ω) MeasurableSpace.pi ⊔
        MeasurableSpace.comap (fun ω (z : cbox (latPt (p.s (j - 1)) w) (4 * p.R * p.s (j - 1))) =>
          H (p.n - p.a (j - 1)) z ω - H (p.n - p.a j) z ω) MeasurableSpace.pi))

/-- The rescaled certificate shell lies in the certificate shell around `z`. -/
theorem smul_add_mem_shell {z w : Rd d} {s r₁ r₂ : ℝ} (hs : 0 < s)
    (hw : w ∈ cbox (0 : Rd d) r₁ \ obox (0 : Rd d) r₂) :
    z + s • w ∈ cbox z (r₁ * s) \ obox z (r₂ * s) := by
  have e : ∀ i, |(z + s • w) i - z i| = s * |w i - (0 : Rd d) i| := fun i => by
    rw [smul_add_apply, add_sub_cancel_left, PiLp.zero_apply, sub_zero, abs_mul, abs_of_pos hs]
  refine ⟨fun i => ?_, fun h => hw.2 fun i => ?_⟩
  · rw [e, mul_comm r₁]
    exact mul_le_mul_of_nonneg_left (hw.1 i) hs.le
  · have := h i
    rw [e, mul_comm r₂] at this
    exact lt_of_mul_lt_mul_left this hs.le

/-- **`𝒞(x,z)` is measurable for `cSigma`** (its locality; MA7 D-5.3 Remark 5.4′). -/
theorem measurableSet_niceCEvent_cSigma {H : ℕ → Rd d → Ω → ℝ}
    (hc : ∀ q ω, Continuous fun z => H q z ω) (p : NiceParams) (hR : 4 ≤ (p.R : ℝ)) (j : ℕ)
    (u w : Zd d) :
    MeasurableSet[cSigma H p j u w] {ω | NiceCEvent p (fun q z => H q z ω) j u w} := by
  set s := p.s j with hs
  set s' := p.s (j - 1) with hs'
  have hs0 : 0 < s := p.s_pos j
  have hs'0 : 0 < s' := p.s_pos (j - 1)
  set x := latPt s u with hx
  set z₀ := latPt s' w with hz₀
  -- the four σ-algebras
  set m₁ : MeasurableSpace Ω := MeasurableSpace.comap (fun ω (z : (cbox x (4 * s) \
      obox x (2 * s) : Set (Rd d))) => H p.n z ω - H (p.n - p.a j) z ω) MeasurableSpace.pi
    with hm₁
  set m₂ : MeasurableSpace Ω := MeasurableSpace.comap (fun ω (z : (cbox z₀ (4 * p.R * s') \
      obox z₀ (2 * p.R * s') : Set (Rd d))) =>
      H (p.certIdx (j - 1)) z ω - H (p.n - p.a (j - 1)) z ω) MeasurableSpace.pi with hm₂
  set m₃ : MeasurableSpace Ω := MeasurableSpace.comap (fun ω (z : (cbox z₀ (4 * p.R * s') \
      obox z₀ (2 * p.R * s') : Set (Rd d))) =>
      H p.n z ω - H (p.certIdx (j - 1)) z ω) MeasurableSpace.pi with hm₃
  set m₄ : MeasurableSpace Ω := MeasurableSpace.comap (fun ω (z : cbox z₀ (4 * p.R * s')) =>
      H (p.n - p.a (j - 1)) z ω - H (p.n - p.a j) z ω) MeasurableSpace.pi with hm₄
  have hσ : cSigma H p j u w = m₁ ⊔ (m₂ ⊔ (m₃ ⊔ m₄)) := rfl
  rw [hσ]
  have h1 : m₁ ≤ m₁ ⊔ (m₂ ⊔ (m₃ ⊔ m₄)) := le_sup_left
  have h2 : m₂ ⊔ m₃ ≤ m₁ ⊔ (m₂ ⊔ (m₃ ⊔ m₄)) :=
    sup_le (le_sup_left.trans le_sup_right)
      ((le_sup_left.trans le_sup_right).trans le_sup_right)
  have h4 : m₄ ≤ m₁ ⊔ (m₂ ⊔ (m₃ ⊔ m₄)) := (le_sup_right.trans le_sup_right).trans le_sup_right
  -- the across term
  have hA : MeasurableSet[m₁] {ω | (2 : ℝ) ^ (-(p.n : ℝ) + (p.ξ * p.Q - p.θ) * p.a j) <
      acrossDist p.ξ (fun z => H p.n z ω - H (p.n - p.a j) z ω) x (4 * s) (2 * s)} := by
    have hf := measurable_acrossDist_comap_shell
      (H := fun z ω => H p.n z ω - H (p.n - p.a j) z ω) (fun ω => (hc _ ω).sub (hc _ ω)) p.ξ x
      (r₁ := 4 * s) (r₂ := 2 * s) (by linarith) (by linarith)
    exact measurableSet_lt measurable_const hf
  -- the certificate
  have hC : MeasurableSet[m₂ ⊔ m₃] {ω | NiceCert p (fun q z => H q z ω) (j - 1) z₀} := by
    have hsS : (0 : ℝ) < (2 : ℝ)⁻¹ ^ superScale (p.a (j - 1)) := by positivity
    have hsϱ : 2 * (2 : ℝ)⁻¹ ^ superScale (p.a (j - 1)) ≤
        min (2 * (p.R : ℝ)) (4 * p.R - 2 * p.R) / 16 := by
      have h2 : (2 : ℝ)⁻¹ ^ superScale (p.a (j - 1)) ≤ (2 : ℝ)⁻¹ ^ 2 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by unfold superScale; omega)
      have e : min (2 * (p.R : ℝ)) (4 * p.R - 2 * p.R) = 2 * p.R := by
        rw [show (4 : ℝ) * p.R - 2 * p.R = 2 * p.R by ring, min_self]
      rw [e]
      norm_num at h2
      linarith
    have hcont : ∀ q ω, Continuous fun v : Rd d => H q (z₀ + s' • v) ω := fun q ω =>
      (hc q ω).comp (continuous_const.add (continuous_const_smul _))
    have hloc := measurableSet_aroundCert_comap
      (ψ := fun v ω => H (p.certIdx (j - 1)) (z₀ + s' • v) ω -
        H (p.n - p.a (j - 1)) (z₀ + s' • v) ω)
      (g := fun v ω => H p.n (z₀ + s' • v) ω - H (p.certIdx (j - 1)) (z₀ + s' • v) ω)
      (fun ω => (hcont _ ω).sub (hcont _ ω)) (fun ω => (hcont _ ω).sub (hcont _ ω)) p.ξ
      (4 * (p.R : ℝ)) (2 * p.R) _ hsS hsϱ ((2 : ℝ) ^ (-(1 - p.ξ * p.Q) * p.a (j - 1) +
        p.θ * p.a (j - 1) / 3)) (p.θ * Real.log 2 / (3 * p.ξ) * p.a (j - 1))
    have hmem : ∀ v ∈ cbox (0 : Rd d) (4 * (p.R : ℝ)) \ obox (0 : Rd d) (2 * p.R),
        z₀ + s' • v ∈ cbox z₀ (4 * p.R * s') \ obox z₀ (2 * p.R * s') :=
      fun v hv => smul_add_mem_shell hs'0 hv
    have hle₂ := comap_restrict_comp_le (A := cbox (0 : Rd d) (4 * (p.R : ℝ)) \
        obox (0 : Rd d) (2 * p.R)) (B := cbox z₀ (4 * p.R * s') \ obox z₀ (2 * p.R * s'))
      (fun z ω => H (p.certIdx (j - 1)) z ω - H (p.n - p.a (j - 1)) z ω)
      (fun v => z₀ + s' • v) hmem
    have hle₃ := comap_restrict_comp_le (A := cbox (0 : Rd d) (4 * (p.R : ℝ)) \
        obox (0 : Rd d) (2 * p.R)) (B := cbox z₀ (4 * p.R * s') \ obox z₀ (2 * p.R * s'))
      (fun z ω => H p.n z ω - H (p.certIdx (j - 1)) z ω) (fun v => z₀ + s' • v) hmem
    exact sup_le_sup hle₂ hle₃ _ hloc
  -- the supremum term
  have hS : MeasurableSet[m₄] {ω | ∀ z ∈ cbox z₀ (4 * p.R * s'),
      H (p.n - p.a (j - 1)) z ω - H (p.n - p.a j) z ω ≤ p.supLevel j} := by
    have h := (measurableSet_exists_lt_comap
      (X := fun z ω => H (p.n - p.a (j - 1)) z ω - H (p.n - p.a j) z ω)
      (fun ω => (hc _ ω).sub (hc _ ω)) (subset_refl (cbox z₀ (4 * p.R * s')))
      (p.supLevel j)).1.compl
    convert h using 1
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, not_exists, not_and, not_lt]
  have e : {ω | NiceCEvent p (fun q z => H q z ω) j u w} =
      {ω | (2 : ℝ) ^ (-(p.n : ℝ) + (p.ξ * p.Q - p.θ) * p.a j) <
        acrossDist p.ξ (fun z => H p.n z ω - H (p.n - p.a j) z ω) x (4 * s) (2 * s)} ∩
      ({ω | NiceCert p (fun q z => H q z ω) (j - 1) z₀} ∩
        {ω | ∀ z ∈ cbox z₀ (4 * p.R * s'),
          H (p.n - p.a (j - 1)) z ω - H (p.n - p.a j) z ω ≤ p.supLevel j}) := by
    ext ω
    rfl
  rw [e]
  exact (h1 _ hA).inter ((h2 _ hC).inter (h4 _ hS))

/-- **The bad boxes near `z` form an event of the fine fields**: `{some a_{j-1}-box contained in
B_{R s_{j-1}}(z) is bad}` is measurable for the bands below `s_{j-1}` on `B̄_{(R+4)s_{j-1}}(z)`. -/
theorem measurableSet_exists_bad_fine {H : ℕ → Rd d → Ω → ℝ}
    (hc : ∀ q ω, Continuous fun z => H q z ω) (p : NiceParams) (hmono : Monotone p.a)
    (hR : 4 ≤ (p.R : ℝ)) {j : ℕ}
    (hgap : ∀ i, 2 ≤ i → i ≤ j - 1 → 8 * p.s (i - 1) ≤ p.s i ∧ (p.R : ℝ) * p.s (i - 1) ≤ p.s i)
    (w : Zd d) :
    MeasurableSet[bandSigma H (p.n - p.a (j - 1))
        (cbox (latPt (p.s (j - 1)) w) ((p.R + 4) * p.s (j - 1)))]
      {ω | ∃ v : Zd d, obox (latPt (p.s (j - 1)) v) (p.s (j - 1)) ⊆
          obox (latPt (p.s (j - 1)) w) (p.R * p.s (j - 1)) ∧
        ¬ NiceBox p (fun q z => H q z ω) (j - 1) v} := by
  set m := bandSigma H (p.n - p.a (j - 1))
    (cbox (latPt (p.s (j - 1)) w) ((p.R + 4) * p.s (j - 1))) with hm
  have hs' := p.s_pos (j - 1)
  have e : {ω | ∃ v : Zd d, obox (latPt (p.s (j - 1)) v) (p.s (j - 1)) ⊆
        obox (latPt (p.s (j - 1)) w) (p.R * p.s (j - 1)) ∧
        ¬ NiceBox p (fun q z => H q z ω) (j - 1) v} =
      ⋃ v : {v : Zd d // obox (latPt (p.s (j - 1)) v) (p.s (j - 1)) ⊆
        obox (latPt (p.s (j - 1)) w) (p.R * p.s (j - 1))},
        {ω | NiceBox p (fun q z => H q z ω) (j - 1) v.1}ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_compl_iff, Subtype.exists, exists_prop]
  rw [e]
  refine @MeasurableSet.iUnion Ω _ m _ _ fun v => ?_
  have hle : bandSigma H (p.n - p.a (j - 1)) (cbox (latPt (p.s (j - 1)) v.1) (5 * p.s (j - 1))) ≤
      m := by
    refine bandSigma_mono_set ((cbox_subset_of_obox_subset hs' v.2 _).trans fun z hz i =>
      (hz i).trans (le_of_eq ?_))
    ring
  exact (hle _ (niceBox_local hc p hmono hR hgap v.1)).compl

variable [MeasurableSpace Ω] {κ : Rd d → ℝ} {P : Measure Ω} {W : WN d → Ω → ℝ}
  {H : ℕ → Rd d → Ω → ℝ}

/-- **`𝒞(x,z)` is independent of the fine fields near `z`** (MA7 D-5.3 Remark 5.4′; blueprint
`r2:lem:54`(iii)): for `x = s_j u`, `z = s_{j-1} w ∈ B_{s_j}(x)`, the σ-algebra of the fields used
by `𝒞(x,z)` is independent of the bands below `s_{j-1}` on `B̄_{(R+4)s_{j-1}}(z)`, provided `a_{j-1}
≤ a_j ≤ n`, `m(a_{j-1}) ≤ a_{j-1}`, `R ≥ 2ρ + 4` and `(2ρ + R + 4) s_{j-1} ≤ s_j`. -/
theorem indep_niceCEvent_fine (hκ : IsLFPPKernel κ) (hH : IsDyadicRealization κ P W H)
    {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) (p : NiceParams) {j : ℕ}
    (haj : p.a (j - 1) ≤ p.a j) (hjn : p.a j ≤ p.n)
    (hsS : superScale (p.a (j - 1)) ≤ p.a (j - 1)) (hR : 2 * ρ + 4 ≤ (p.R : ℝ))
    (hgap : (2 * ρ + p.R + 4) * p.s (j - 1) ≤ p.s j) {u w : Zd d}
    (hw : latPt (p.s (j - 1)) w ∈ obox (latPt (p.s j) u) (p.s j)) :
    Indep (cSigma H p j u w)
      (bandSigma H (p.n - p.a (j - 1)) (cbox (latPt (p.s (j - 1)) w) ((p.R + 4) * p.s (j - 1))))
      P := by
  have hρ0 := hκ.radius_pos hρ
  set s := p.s j with hs
  set s' := p.s (j - 1) with hs'
  have hs0 : 0 < s := p.s_pos j
  have hs'0 : 0 < s' := p.s_pos (j - 1)
  set x := latPt s u with hx
  set z₀ := latPt s' w with hz₀
  set p₁ := p.n - p.a (j - 1) with hp₁
  set p₂ := p.n - p.a j with hp₂
  set ci := p.certIdx (j - 1) with hci
  have hp₂₁ : p₂ ≤ p₁ := Nat.sub_le_sub_left haj _
  have hp₁ci : p₁ ≤ ci := Nat.le_add_right _ _
  have hcin : ci ≤ p.n := by
    have h1 : p.a (j - 1) ≤ p.n := haj.trans hjn
    have h2 : ci = p.n - p.a (j - 1) + superScale (p.a (j - 1)) := rfl
    omega
  -- index types
  let SX := (cbox x (4 * s) \ obox x (2 * s) : Set (Rd d))
  let SZ := (cbox z₀ (4 * p.R * s') \ obox z₀ (2 * p.R * s') : Set (Rd d))
  let BZ := cbox z₀ (4 * p.R * s')
  let BF := cbox z₀ ((p.R + 4) * s')
  let F₁ : SX ⊕ (SZ ⊕ (SZ ⊕ BZ)) → WN d :=
    Sum.elim (fun z => bandVec κ ((2 : ℝ)⁻¹ ^ p.n) ((2 : ℝ)⁻¹ ^ p₂) z)
      (Sum.elim (fun z => bandVec κ ((2 : ℝ)⁻¹ ^ ci) ((2 : ℝ)⁻¹ ^ p₁) z)
        (Sum.elim (fun z => bandVec κ ((2 : ℝ)⁻¹ ^ p.n) ((2 : ℝ)⁻¹ ^ ci) z)
          (fun z => bandVec κ ((2 : ℝ)⁻¹ ^ p₁) ((2 : ℝ)⁻¹ ^ p₂) z)))
  let X : SX ⊕ (SZ ⊕ (SZ ⊕ BZ)) → Ω → ℝ :=
    Sum.elim (fun z ω => H p.n z ω - H p₂ z ω)
      (Sum.elim (fun z ω => H ci z ω - H p₁ z ω)
        (Sum.elim (fun z ω => H p.n z ω - H ci z ω) (fun z ω => H p₁ z ω - H p₂ z ω)))
  let F₂ : ℕ × BF → WN d := fun t => bandVec κ ((2 : ℝ)⁻¹ ^ (p₁ + t.1)) ((2 : ℝ)⁻¹ ^ p₁) t.2
  let Y : ℕ × BF → Ω → ℝ := fun t ω => H (p₁ + t.1) t.2 ω - H p₁ t.2 ω
  -- geometry: the far parts
  have hfarX : ∀ z ∈ cbox x (4 * s) \ obox x (2 * s), ∀ y ∈ BF, 2 * ρ * s' ≤ ‖z - y‖ := by
    intro z hz y hy
    obtain ⟨i, hi⟩ : ∃ i, 2 * s ≤ |z i - x i| := by
      by_contra hcon
      push Not at hcon
      exact hz.2 hcon
    refine le_trans ?_ (abs_sub_le_norm_sub z y i)
    have h1 : |y i - z₀ i| ≤ (p.R + 4) * s' := hy i
    have h2 : |z₀ i - x i| < s := hw i
    have h3 := abs_sub_abs_le_abs_sub (z i - x i) (y i - x i)
    have h4 : |y i - x i| ≤ |y i - z₀ i| + |z₀ i - x i| := by
      calc |y i - x i| = |(y i - z₀ i) + (z₀ i - x i)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have h5 : |(z i - x i) - (y i - x i)| = |z i - y i| := by ring_nf
    rw [h5] at h3
    linarith
  have hfarZ : ∀ z ∈ cbox z₀ (4 * p.R * s') \ obox z₀ (2 * p.R * s'), ∀ y ∈ BF,
      2 * ρ * s' ≤ ‖z - y‖ := by
    intro z hz y hy
    obtain ⟨i, hi⟩ : ∃ i, 2 * p.R * s' ≤ |z i - z₀ i| := by
      by_contra hcon
      push Not at hcon
      exact hz.2 hcon
    refine le_trans ?_ (abs_sub_le_norm_sub z y i)
    have h1 : |y i - z₀ i| ≤ (p.R + 4) * s' := hy i
    have h3 := abs_sub_abs_le_abs_sub (z i - z₀ i) (y i - z₀ i)
    have h5 : |(z i - z₀ i) - (y i - z₀ i)| = |z i - y i| := by ring_nf
    rw [h5] at h3
    have h6 := mul_le_mul_of_nonneg_right hR hs'0.le
    linarith
  have hsp : ∀ q : ℕ, (0 : ℝ) < (2 : ℝ)⁻¹ ^ q := fun q => by positivity
  have hmin : ∀ b : ℝ, b ≤ s' → 2 * ρ * min b s' ≤ 2 * ρ * s' := fun b _ =>
    mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
  have hci_le : (2 : ℝ)⁻¹ ^ ci ≤ s' :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hp₁ci
  -- orthogonality
  have horth : ∀ (a : SX ⊕ (SZ ⊕ (SZ ⊕ BZ))) (t : ℕ × BF), inner ℝ (F₁ a) (F₂ t) = 0 := by
    rintro (z | z | z | z) ⟨q, y⟩
    · refine inner_bandVec_eq_zero_of_two_mul_min_le hκ hρ (hsp _) (hsp _) ?_
      refine le_trans ?_ (hfarX z z.2 y y.2)
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
    · exact inner_bandVec_eq_zero_of_two_mul_min_le hκ hρ (hsp _) (hsp _)
        ((hmin _ le_rfl).trans (hfarZ z z.2 y y.2))
    · exact inner_bandVec_eq_zero_of_two_mul_min_le hκ hρ (hsp _) (hsp _)
        ((hmin _ hci_le).trans (hfarZ z z.2 y y.2))
    · exact inner_bandVec_eq_zero_of_le hκ (hsp _) (hsp _)
        ((min_le_right _ _).trans (le_max_left _ _)) z y
  -- versions
  have hX : ∀ a, X a =ᵐ[P] W (F₁ a) := by
    rintro (z | z | z | z)
    · exact (isBandVersion_sub_of_realization hκ hH (Nat.sub_le p.n (p.a j))).ae_eq z
    · exact (isBandVersion_sub_of_realization hκ hH hp₁ci).ae_eq z
    · exact (isBandVersion_sub_of_realization hκ hH hcin).ae_eq z
    · exact (isBandVersion_sub_of_realization hκ hH hp₂₁).ae_eq z
  have hY : ∀ t, Y t =ᵐ[P] W (F₂ t) := fun t =>
    (isBandVersion_sub_of_realization hκ hH (Nat.le_add_right p₁ t.1)).ae_eq t.2
  have hind := hH.whiteNoise.indepFun_of_ae_eq F₁ F₂ horth hX hY
  refine indep_of_indep_of_le_left (indep_of_indep_of_le_right hind
    (bandSigma_le_comap_family p₁ BF)) ?_
  unfold cSigma
  refine sup_le ?_ (sup_le ?_ (sup_le ?_ ?_))
  · exact comap_comp_le_comap (fun ω a => X a ω)
      (Φ := fun (F : SX ⊕ (SZ ⊕ (SZ ⊕ BZ)) → ℝ) (z : SX) => F (Sum.inl z))
      (measurable_pi_iff.2 fun z => measurable_pi_apply _)
  · exact comap_comp_le_comap (fun ω a => X a ω)
      (Φ := fun (F : SX ⊕ (SZ ⊕ (SZ ⊕ BZ)) → ℝ) (z : SZ) => F (Sum.inr (Sum.inl z)))
      (measurable_pi_iff.2 fun z => measurable_pi_apply _)
  · exact comap_comp_le_comap (fun ω a => X a ω)
      (Φ := fun (F : SX ⊕ (SZ ⊕ (SZ ⊕ BZ)) → ℝ) (z : SZ) => F (Sum.inr (Sum.inr (Sum.inl z))))
      (measurable_pi_iff.2 fun z => measurable_pi_apply _)
  · exact comap_comp_le_comap (fun ω a => X a ω)
      (Φ := fun (F : SX ⊕ (SZ ⊕ (SZ ⊕ BZ)) → ℝ) (z : BZ) => F (Sum.inr (Sum.inr (Sum.inr z))))
      (measurable_pi_iff.2 fun z => measurable_pi_apply _)

/-- **`𝒞(x,z)` is independent of the badness of the `a_{j-1}`-boxes near `z`** (DGZ Lemma 5.7, the
event `ℬ₂`; MA7 D-5.3 Remark 5.4′; blueprint `r2:lem:54`(iii)). -/
theorem indepSet_niceCEvent_exists_bad (hκ : IsLFPPKernel κ) (hH : IsDyadicRealization κ P W H)
    {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) (p : NiceParams) (hmono : Monotone p.a)
    (hR4 : 4 ≤ (p.R : ℝ)) {j : ℕ} (hjn : p.a j ≤ p.n)
    (hsS : superScale (p.a (j - 1)) ≤ p.a (j - 1)) (hR : 2 * ρ + 4 ≤ (p.R : ℝ))
    (hgapj : (2 * ρ + p.R + 4) * p.s (j - 1) ≤ p.s j)
    (hgap : ∀ i, 2 ≤ i → i ≤ j - 1 → 8 * p.s (i - 1) ≤ p.s i ∧ (p.R : ℝ) * p.s (i - 1) ≤ p.s i)
    {u w : Zd d} (hw : latPt (p.s (j - 1)) w ∈ obox (latPt (p.s j) u) (p.s j)) :
    IndepSet {ω | NiceCEvent p (fun q z => H q z ω) j u w}
      {ω | ∃ v : Zd d, obox (latPt (p.s (j - 1)) v) (p.s (j - 1)) ⊆
          obox (latPt (p.s (j - 1)) w) (p.R * p.s (j - 1)) ∧
        ¬ NiceBox p (fun q z => H q z ω) (j - 1) v} P := by
  have hc : ∀ q ω, Continuous fun z => H q z ω := fun q => (hH.band q).continuous
  exact (indep_niceCEvent_fine hκ hH hρ p (hmono (Nat.sub_le j 1)) hjn hsS hR hgapj
    hw).indepSet_of_measurableSet (measurableSet_niceCEvent_cSigma hc p hR4 j u w)
    (measurableSet_exists_bad_fine hc p hmono hR4 hgap w)

/-- **The product formula for `ℬ₂`** (DGZ Lemma 5.7, (5.18)): `P[𝒞(x,z)ᶜ ∩ {some a_{j-1}-box in
B_{R s_{j-1}}(z) is bad}] = P[𝒞(x,z)ᶜ] · P[some a_{j-1}-box in B_{R s_{j-1}}(z) is bad]`. -/
theorem measure_not_niceCEvent_inter_exists_bad_eq (hκ : IsLFPPKernel κ)
    (hH : IsDyadicRealization κ P W H) {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) (p : NiceParams)
    (hmono : Monotone p.a) (hR4 : 4 ≤ (p.R : ℝ)) {j : ℕ} (hjn : p.a j ≤ p.n)
    (hsS : superScale (p.a (j - 1)) ≤ p.a (j - 1)) (hR : 2 * ρ + 4 ≤ (p.R : ℝ))
    (hgapj : (2 * ρ + p.R + 4) * p.s (j - 1) ≤ p.s j)
    (hgap : ∀ i, 2 ≤ i → i ≤ j - 1 → 8 * p.s (i - 1) ≤ p.s i ∧ (p.R : ℝ) * p.s (i - 1) ≤ p.s i)
    {u w : Zd d} (hw : latPt (p.s (j - 1)) w ∈ obox (latPt (p.s j) u) (p.s j)) :
    P ({ω | ¬ NiceCEvent p (fun q z => H q z ω) j u w} ∩
        {ω | ∃ v : Zd d, obox (latPt (p.s (j - 1)) v) (p.s (j - 1)) ⊆
          obox (latPt (p.s (j - 1)) w) (p.R * p.s (j - 1)) ∧
          ¬ NiceBox p (fun q z => H q z ω) (j - 1) v}) =
      P {ω | ¬ NiceCEvent p (fun q z => H q z ω) j u w} *
        P {ω | ∃ v : Zd d, obox (latPt (p.s (j - 1)) v) (p.s (j - 1)) ⊆
          obox (latPt (p.s (j - 1)) w) (p.R * p.s (j - 1)) ∧
          ¬ NiceBox p (fun q z => H q z ω) (j - 1) v} := by
  have hc : ∀ q ω, Continuous fun z => H q z ω := fun q => (hH.band q).continuous
  have hind := indep_niceCEvent_fine hκ hH hρ p (hmono (Nat.sub_le j 1)) hjn hsS hR hgapj hw
  rw [Indep_iff] at hind
  exact hind _ _ (measurableSet_niceCEvent_cSigma hc p hR4 j u w).compl
    (measurableSet_exists_bad_fine hc p hmono hR4 hgap w)

end CEvent

end DGZ

end HigherDimLQGMetric
