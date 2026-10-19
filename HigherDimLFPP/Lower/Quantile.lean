import HigherDimLFPP.Lower.EqualEdgePath
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The quantile coupling for finitely supported measures (source §5.2, Lemma 5.3, Step 1)

Packet P-L1, supplement to target T3 (audit HA4, "Details for later use" D3(e), finding HA4-3).
All statements are deterministic.

For `μ = Σ_{z∈S} w z δ_z` with `μ_x ∈ W(r)` (`HorizW S w r`), list the atoms by increasing
horizontal coordinate (ties broken by an enumeration of `S`) and let `(c⁻(z), c⁺(z)]` be the
consecutive intervals of lengths `w z` (`qLow`). Then (`exists_quantile_coupling`):

* the intervals are pairwise disjoint subsets of `(0,1]` that tile it up to a null set, so
  `∫_{(0,1]} g = Σ_z ∫_{(c⁻(z), c⁺(z)]} g` for every integrable `g`: the measure
  `π = Σ_z δ_z ⊗ 𝓛|_{(c⁻(z), c⁺(z)]}` couples `μ` with `𝓛` (Lebesgue measure on `[0,1] e₁`);
* `|z₁ - t| ≤ r` for `t ∈ (c⁻(z), c⁺(z)]`.

The key inequality is the left-limit form of the sandwich, `μ{z₁ < x} ≥ clamp(x - r)`
(`clamp01_sub_le_sum_lt`). Lifting (`norm_sub_smul_e₁_le`) and pushing forward by a similarity of
ratio `q` (`norm_app_sub_app_smul_e₁_le`) gives the displacement `q(r + m)` of (5.17)
(`r = Bδ²`, `m = Mδ`: `u = qδ(M + Bδ)`); for an edge similarity of a polygon the partner of
`T_i z` is the polygon point at parameter `(i + t)/K` (`edgeSim_app_smul_e₁_eq_polyPath`).

2D source: none (the 2D proof does not use couplings).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLFPP.Lower

variable {d : ℕ}

/-! ## The left limit of the horizontal distribution function -/

/-- `clamp` is `1`-Lipschitz. -/
theorem clamp01_sub_clamp01_le (a b : ℝ) : clamp01 a - clamp01 b ≤ |a - b| := by
  unfold clamp01
  have h1 : |max 0 (min 1 a) - max 0 (min 1 b)| ≤ |min 1 a - min 1 b| := by
    rw [max_comm 0 (min 1 a), max_comm 0 (min 1 b)]
    exact abs_max_sub_max_le_abs _ _ _
  have h2 : |min 1 a - min 1 b| ≤ max |1 - 1| |a - b| := abs_min_sub_min_le_max _ _ _ _
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)] at h2
  exact (le_abs_self _).trans (h1.trans h2)

/-- **Left limit of the sandwich**: if `μ_x ∈ W(r)`, then `μ{z₁ < x} ≥ clamp(x - r)`. -/
theorem clamp01_sub_le_sum_lt {S : Finset (Rd d)} {w : Rd d → ℝ} {r : ℝ} (hW : HorizW S w r)
    (x : ℝ) : clamp01 (x - r) ≤ ∑ z ∈ S.filter (fun z => horiz z < x), w z := by
  set Fm := ∑ z ∈ S.filter (fun z => horiz z < x), w z with hFm
  -- a point `y₀ < x` with no atom in `(y₀, x)`
  obtain ⟨y₀, hy₀x, hy₀⟩ : ∃ y₀ < x, ∀ z ∈ S, horiz z < x → horiz z ≤ y₀ := by
    set A := (S.filter (fun z => horiz z < x)).image horiz with hA_def
    by_cases hA : A.Nonempty
    · refine ⟨A.max' hA, ?_, fun z hz hzx => A.le_max' _
        (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hz, hzx⟩))⟩
      obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.1 (A.max'_mem hA)
      rw [← hzeq]
      exact (Finset.mem_filter.1 hz).2
    · refine ⟨x - 1, by linarith, fun z hz hzx => absurd ⟨horiz z,
        Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hz, hzx⟩)⟩ hA⟩
  have hconst : ∀ y, y₀ ≤ y → y < x → hCDF S w y = Fm := by
    intro y hy1 hy2
    unfold hCDF
    rw [hFm]
    congr 1
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hz, hzy⟩
      exact ⟨hz, lt_of_le_of_lt hzy hy2⟩
    · rintro ⟨hz, hzx⟩
      exact ⟨hz, (hy₀ z hz hzx).trans hy1⟩
  by_contra hcon
  push Not at hcon
  set ε := clamp01 (x - r) - Fm with hε_def
  have hε : 0 < ε := by linarith
  set y := max y₀ (x - ε / 2) with hy_def
  have hy1 : y₀ ≤ y := le_max_left _ _
  have hy2 : y < x := max_lt hy₀x (by linarith)
  have hxy : x - y ≤ ε / 2 := by
    have := le_max_right y₀ (x - ε / 2)
    linarith
  have hlip : clamp01 (x - r) - clamp01 (y - r) ≤ x - y := by
    have := clamp01_sub_clamp01_le (x - r) (y - r)
    rwa [show x - r - (y - r) = x - y by ring, abs_of_nonneg (by linarith)] at this
  have h1 := (hW y).1
  rw [hconst y hy1 hy2] at h1
  linarith

/-! ## The quantile intervals -/

/-- Rank of an atom in a fixed enumeration of `S` (tie-break). -/
def atomRank (S : Finset (Rd d)) (z : Rd d) : ℕ :=
  if h : z ∈ S then ((S.equivFin ⟨z, h⟩ : Fin S.card) : ℕ) else 0

theorem atomRank_inj {S : Finset (Rd d)} {z z' : Rd d} (hz : z ∈ S) (hz' : z' ∈ S)
    (h : atomRank S z = atomRank S z') : z = z' := by
  simp only [atomRank, hz, hz', dite_true] at h
  have := S.equivFin.injective (Fin.ext h)
  exact congrArg Subtype.val this

/-- The strict lexicographic order `(z₁, rank)` on atoms. -/
def lexLT (S : Finset (Rd d)) (z' z : Rd d) : Prop :=
  horiz z' < horiz z ∨ (horiz z' = horiz z ∧ atomRank S z' < atomRank S z)

instance (S : Finset (Rd d)) (z : Rd d) : DecidablePred fun z' => lexLT S z' z :=
  fun _ => by unfold lexLT; infer_instance

theorem lexLT_irrefl (S : Finset (Rd d)) (z : Rd d) : ¬ lexLT S z z := by
  rintro (h | ⟨-, h⟩) <;> exact lt_irrefl _ h

theorem lexLT_trans {S : Finset (Rd d)} {a b c : Rd d} (hab : lexLT S a b) (hbc : lexLT S b c) :
    lexLT S a c := by
  rcases hab with h1 | ⟨h1, h1'⟩ <;> rcases hbc with h2 | ⟨h2, h2'⟩
  · exact Or.inl (h1.trans h2)
  · exact Or.inl (h2 ▸ h1)
  · exact Or.inl (h1 ▸ h2)
  · exact Or.inr ⟨h1.trans h2, h1'.trans h2'⟩

theorem lexLT_trichotomy {S : Finset (Rd d)} {z z' : Rd d} (hz : z ∈ S) (hz' : z' ∈ S)
    (hne : z ≠ z') : lexLT S z z' ∨ lexLT S z' z := by
  rcases lt_trichotomy (horiz z) (horiz z') with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy (atomRank S z) (atomRank S z') with h' | h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact absurd (atomRank_inj hz hz' h') hne
    · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
  · exact Or.inr (Or.inl h)

/-- Lower endpoint `c⁻(z) = μ{z' ≺ z}` of the quantile interval of the atom `z`. -/
def qLow (S : Finset (Rd d)) (w : Rd d → ℝ) (z : Rd d) : ℝ :=
  ∑ z' ∈ S.filter (fun z' => lexLT S z' z), w z'

theorem qLow_nonneg {S : Finset (Rd d)} {w : Rd d → ℝ} (hw : ∀ z ∈ S, 0 ≤ w z) (z : Rd d) :
    0 ≤ qLow S w z :=
  Finset.sum_nonneg fun z' hz' => hw z' (Finset.mem_filter.1 hz').1

/-- `c⁺(z) = c⁻(z) + w z` is a sum over `insert z {z' ≺ z}`. -/
theorem qLow_add_eq {S : Finset (Rd d)} {w : Rd d → ℝ} {z : Rd d} :
    qLow S w z + w z = ∑ z' ∈ insert z (S.filter (fun z' => lexLT S z' z)), w z' := by
  rw [Finset.sum_insert, add_comm]
  · rfl
  · intro h
    exact lexLT_irrefl S z (Finset.mem_filter.1 h).2

theorem qLow_add_le_of_subset {S : Finset (Rd d)} {w : Rd d → ℝ} (hw : ∀ z ∈ S, 0 ≤ w z)
    {z : Rd d} {T : Finset (Rd d)} (hT : T ⊆ S)
    (hsub : insert z (S.filter (fun z' => lexLT S z' z)) ⊆ T) :
    qLow S w z + w z ≤ ∑ z' ∈ T, w z' := by
  rw [qLow_add_eq]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun z' hz' _ => hw z' (hT hz')

/-- **The quantile coupling** (HA4 D3(e)). For a finitely supported probability measure `μ` with
`μ_x ∈ W(r)` there are lower endpoints `c⁻(z)` such that the intervals `(c⁻(z), c⁻(z) + w z]`,
`z ∈ S`, are pairwise disjoint subsets of `(0,1]`, tile `(0,1]` for integration, and
`|z₁ - t| ≤ r` on the interval of `z`. -/
theorem exists_quantile_coupling {S : Finset (Rd d)} {w : Rd d → ℝ} (hμ : IsFinProb S w)
    {r : ℝ} (hW : HorizW S w r) :
    ∃ cl : Rd d → ℝ,
      (∀ z ∈ S, 0 ≤ cl z ∧ cl z + w z ≤ 1) ∧
      (↑S : Set (Rd d)).PairwiseDisjoint (fun z => Ioc (cl z) (cl z + w z)) ∧
      (∀ z ∈ S, ∀ t ∈ Ioc (cl z) (cl z + w z), |horiz z - t| ≤ r) ∧
      ∀ g : ℝ → ℝ, IntegrableOn g (Ioc 0 1) →
        ∫ t in Ioc (0 : ℝ) 1, g t = ∑ z ∈ S, ∫ t in Ioc (cl z) (cl z + w z), g t := by
  obtain ⟨hw, hsum⟩ := hμ
  refine ⟨qLow S w, ?_, ?_, ?_, ?_⟩
  · -- endpoints in `[0,1]`
    intro z hz
    refine ⟨qLow_nonneg hw z, ?_⟩
    rw [← hsum]
    refine qLow_add_le_of_subset hw (Finset.Subset.refl S) ?_
    exact Finset.insert_subset hz (Finset.filter_subset _ _)
  · -- disjointness
    have key : ∀ z ∈ S, ∀ z' ∈ S, lexLT S z z' → qLow S w z + w z ≤ qLow S w z' := by
      intro z hz z' _ hzz'
      refine qLow_add_le_of_subset hw (Finset.filter_subset _ _) ?_
      refine Finset.insert_subset (Finset.mem_filter.2 ⟨hz, hzz'⟩) ?_
      intro z'' hz''
      rw [Finset.mem_filter] at hz'' ⊢
      exact ⟨hz''.1, lexLT_trans hz''.2 hzz'⟩
    intro z hz z' hz' hne
    simp only [Function.onFun]
    rw [Set.Ioc_disjoint_Ioc]
    rcases lexLT_trichotomy hz hz' hne with h | h
    · have := key z hz z' hz' h
      exact (min_le_left _ _).trans (this.trans (le_max_right _ _))
    · have := key z' hz' z hz h
      exact (min_le_right _ _).trans (this.trans (le_max_left _ _))
  · -- displacement
    intro z hz t ht
    have hcl0 := qLow_nonneg hw z
    have hcl1 : qLow S w z + w z ≤ 1 := by
      rw [← hsum]
      exact qLow_add_le_of_subset hw (Finset.Subset.refl S)
        (Finset.insert_subset hz (Finset.filter_subset _ _))
    -- upper: `c⁺(z) ≤ F(z₁) ≤ clamp(z₁ + r)`
    have hup : qLow S w z + w z ≤ hCDF S w (horiz z) := by
      refine qLow_add_le_of_subset hw (Finset.filter_subset _ _) ?_
      refine Finset.insert_subset (Finset.mem_filter.2 ⟨hz, le_rfl⟩) ?_
      intro z'' hz''
      rw [Finset.mem_filter] at hz'' ⊢
      refine ⟨hz''.1, ?_⟩
      rcases hz''.2 with h | ⟨h, -⟩
      · exact h.le
      · exact h.le
    have hup' := hup.trans (hW (horiz z)).2
    -- lower: `c⁻(z) ≥ μ{z₁' < z₁} ≥ clamp(z₁ - r)`
    have hlow : ∑ z' ∈ S.filter (fun z' => horiz z' < horiz z), w z' ≤ qLow S w z := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun z' hz' _ =>
        hw z' (Finset.mem_filter.1 hz').1
      intro z' hz'
      rw [Finset.mem_filter] at hz' ⊢
      exact ⟨hz'.1, Or.inl hz'.2⟩
    have hlow' := (clamp01_sub_le_sum_lt hW (horiz z)).trans hlow
    have ht0 : 0 < t := lt_of_le_of_lt hcl0 ht.1
    have ht1 : t ≤ 1 := ht.2.trans hcl1
    rw [abs_le]
    constructor
    · -- `t ≤ z₁ + r`
      have h1 : t ≤ clamp01 (horiz z + r) := ht.2.trans hup'
      rcases le_or_gt (horiz z + r) 0 with h | h
      · rw [clamp01_of_nonpos h] at h1
        linarith
      · have : clamp01 (horiz z + r) ≤ horiz z + r :=
          max_le h.le (min_le_right _ _)
        linarith
    · -- `z₁ - r < t`
      have h1 : clamp01 (horiz z - r) < t := lt_of_le_of_lt hlow' ht.1
      rcases le_or_gt 1 (horiz z - r) with h | h
      · rw [clamp01_of_one_le h] at h1
        linarith
      · have : horiz z - r ≤ clamp01 (horiz z - r) := by
          unfold clamp01
          rw [min_eq_right h.le]
          exact le_max_right _ _
        linarith
  · -- integral decomposition
    intro g hg
    have hcl : ∀ z ∈ S, 0 ≤ qLow S w z ∧ qLow S w z + w z ≤ 1 := fun z hz =>
      ⟨qLow_nonneg hw z, by
        rw [← hsum]
        exact qLow_add_le_of_subset hw (Finset.Subset.refl S)
          (Finset.insert_subset hz (Finset.filter_subset _ _))⟩
    have hdisj : (↑S : Set (Rd d)).PairwiseDisjoint
        (fun z => Ioc (qLow S w z) (qLow S w z + w z)) := by
      intro z hz z' hz' hne
      simp only [Function.onFun]
      rw [Set.Ioc_disjoint_Ioc]
      have key : ∀ a ∈ S, ∀ b ∈ S, lexLT S a b → qLow S w a + w a ≤ qLow S w b := by
        intro a ha b _ hab
        refine qLow_add_le_of_subset hw (Finset.filter_subset _ _) ?_
        refine Finset.insert_subset (Finset.mem_filter.2 ⟨ha, hab⟩) ?_
        intro c hc
        rw [Finset.mem_filter] at hc ⊢
        exact ⟨hc.1, lexLT_trans hc.2 hab⟩
      rcases lexLT_trichotomy hz hz' hne with h | h
      · exact (min_le_left _ _).trans ((key z hz z' hz' h).trans (le_max_right _ _))
      · exact (min_le_right _ _).trans ((key z' hz' z hz h).trans (le_max_left _ _))
    have hsub : (⋃ z ∈ S, Ioc (qLow S w z) (qLow S w z + w z)) ⊆ Ioc (0 : ℝ) 1 := by
      intro t ht
      simp only [mem_iUnion] at ht
      obtain ⟨z, hz, ht⟩ := ht
      exact ⟨lt_of_le_of_lt (hcl z hz).1 ht.1, ht.2.trans (hcl z hz).2⟩
    have hmeas : volume (⋃ z ∈ S, Ioc (qLow S w z) (qLow S w z + w z)) =
        volume (Ioc (0 : ℝ) 1) := by
      rw [measure_biUnion_finset hdisj (fun z _ => measurableSet_Ioc)]
      simp_rw [Real.volume_Ioc, add_sub_cancel_left]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun z hz => hw z hz), hsum, sub_zero]
    have hae : (⋃ z ∈ S, Ioc (qLow S w z) (qLow S w z + w z)) =ᵐ[volume] Ioc (0 : ℝ) 1 :=
      ae_eq_of_subset_of_measure_ge hsub hmeas.ge
        (Finset.measurableSet_biUnion S fun z _ => measurableSet_Ioc).nullMeasurableSet
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    rw [← setIntegral_congr_set hae,
      integral_biUnion_finset S (fun z _ => measurableSet_Ioc) hdisj
        (fun z hz => hg.mono_set fun t ht => hsub (mem_biUnion hz ht))]

/-! ## Lifting and pushing forward: the displacement (5.17) -/

/-- Lift of the horizontal coupling: `‖z - t e₁‖ ≤ |z₁ - t| + ‖z_⊥‖`. -/
theorem norm_sub_smul_e₁_le (hd : 0 < d) {z : Rd d} {t r m : ℝ} (h1 : |horiz z - t| ≤ r)
    (h2 : ‖transv z‖ ≤ m) : ‖z - t • e₁ d‖ ≤ r + m := by
  have e : z - t • e₁ d = (horiz z - t) • e₁ d + transv z := by
    conv_lhs => rw [← horiz_add_transv z]
    rw [sub_smul]
    abel
  rw [e]
  calc ‖(horiz z - t) • e₁ d + transv z‖ ≤ ‖(horiz z - t) • e₁ d‖ + ‖transv z‖ :=
        norm_add_le _ _
    _ = |horiz z - t| + ‖transv z‖ := by rw [norm_smul, norm_e₁ hd, mul_one, Real.norm_eq_abs]
    _ ≤ r + m := add_le_add h1 h2

/-- **(5.17)**: pushed forward by a similarity of ratio `q`, the coupled pair `(z, t e₁)` has
displacement `≤ |q| (r + m)`. -/
theorem norm_app_sub_app_smul_e₁_le (hd : 0 < d) (T : SimD d) {z : Rd d} {t r m : ℝ}
    (h1 : |horiz z - t| ≤ r) (h2 : ‖transv z‖ ≤ m) :
    ‖T.app z - T.app (t • e₁ d)‖ ≤ |T.r| * (r + m) := by
  rw [SimD.norm_app_sub]
  exact mul_le_mul_of_nonneg_left (norm_sub_smul_e₁_le hd h1 h2) (abs_nonneg _)

/-- The partner `T_i(t e₁)` of `T_i z` is the polygon point at parameter `(i + t)/K`. -/
theorem edgeSim_app_smul_e₁_eq_polyPath (hd : 0 < d) {K : ℕ} {δ q E₀ M₀ c : ℝ}
    {v : ℕ → Rd d} (hE : EqualEdgeData K δ q E₀ M₀ c v) (hq : 0 < q) {i : ℕ} (hi : i < K)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (edgeSim q v i).app (t • e₁ d) = polyPath v K (((i : ℝ) + t) / K) := by
  have hKpos : 0 < K := lt_of_le_of_lt (Nat.zero_le i) hi
  have hK' : (0 : ℝ) < K := by exact_mod_cast hKpos
  rw [edgeSim_app_smul_e₁ hd hq (hE.edge_len i hi),
    polyPath_eq_edgeAff v K hKpos i hi _ ⟨?_, ?_⟩]
  · unfold edgeAff
    congr 2
    field_simp
    ring
  · rw [div_le_div_iff_of_pos_right hK']
    linarith [ht.1]
  · rw [div_le_div_iff_of_pos_right hK']
    linarith [ht.2]

end HigherDimLFPP.Lower
