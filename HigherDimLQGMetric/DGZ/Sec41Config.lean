import HigherDimLQGMetric.DGZ.Sec41Lemma41
import HigherDimLQGMetric.DGZ.Fold
import HigherDimLFPP.Paths.Compare

/-!
# DGZ §4.1: deterministic relations between the configurations (packet L3c1; MA7 D-4.2)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), proof of Lemma 4.2(1) (TeX l. 1405–1450):
(4.11) `ℰ_{m,n} ⊇ 𝒢_m ∩ ℰ̂_{m,n}` and (4.14)
`ℱ_{m,n} ⊇ ℰ_{m,n} ∩ ℰ_{m-1,n} ∩ 𝒢_m ∩ 𝒢_{m-1} ∩ ℰ̃_{m,n}`;
planning audit `planning/audits/MA7-ref2-sections-4-6.md`, Details (a) D-4.2 (third clause, with
the repairs of G2 at l. 1444 and G25). Everything here is deterministic: `φ` stands for `h_n`,
`ψ` for `h_m` (or `h_{m-1}`) and `g` for `h_{m,n}` (or `h_{m-1,n}`), with `φ = ψ + g`.

* `smallClusters_of_subset`: `SmallClusters` is inherited by configurations with more open sites;
* `mGood_subset_mOpen` (DGZ l. 1411–1416): if `φ = ψ + g` and `ψ ≤ m (Q - η/ξ) log 2` on `B̄₃(0)`
  (the event `𝒢_m`), every `m`-good site of `g` is `m`-open for `φ`
  (`D_φ ≤ 2^{(ξQ - η)m} D_g` on `B_{2^{1-m}}(x) ⊆ B̄₃(0)`); hence `smallClusters_mOpen_of_mGood`
  (4.11);
* `mNice_subset_mOpen`: on `𝒢_{m-1}`, nice sites are `(m-1)`-open;
* `reflTransGen_two_smul`: an L-path `y₀, …, y_k` of coarse sites refines to the fine L-path
  `2y₀, y₀ + y₁, 2y₁, …, 2y_k`;
* `add_not_mem_latRegion` (MA7 G25): if `y, y'` are L-adjacent coarse sites outside `𝓛_{m-1}`,
  their midpoint `y + y'` (a fine site) lies outside `𝓛_m`;
* **`exists_free_of_smallClusters_mNice`** (MA7 D-4.2, third clause): if the rough (non-nice)
  clusters are small (`SmallClusters` of `mNice` with `2D' + 3 ≤ m²`) and `𝒢_m`, `𝒢_{m-1}` hold,
  then
  every fine site `x` is within `ℓ^∞`-distance `m²` (fine units) of a coarse site `y` with `2y`
  free for `O_m` and `y` free for `O_{m-1}`.

Proof of the third clause (MA7 D-4.2). Let `x' = ⌊x/2⌋` (coordinatewise), so `|x - 2x'|_∞ ≤ 1`. The
hole lemma (D-F3) for the nice configuration gives a nice-free `y` with `|y - x'|_∞ ≤ D' + 1`, so
`|x - 2y|_∞ ≤ 2D' + 3 ≤ m²`. Free sites reach infinity (D-FS(ii)): there is a nice L-path from `y`
to `v = (2^m + 1, …)`, outside `𝓛_{m-1}`. Nice sites are `(m-1)`-open, so the path is
`(m-1)`-open and `y` is free for `O_{m-1}` (D-FS(iii)). The refined path `2y → … → 2v` is `m`-open:
`2y'` is `m`-good if `y' ∈ 𝓛_{m-1}` (niceness) and lies outside `𝓛_m` otherwise; the midpoint
`y' + y''` of a step is within `ℓ^∞`-distance `1` of `2y'` and of `2y''`, so it is `m`-good if one
of
`y', y''` lies in `𝓛_{m-1}`, and lies outside `𝓛_m` otherwise (G25); `m`-good sites are `m`-open on
`𝒢_m`. As `2v` lies outside `𝓛_m`, `2y` is free for `O_m` (D-FS(iii)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Relation

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox SiteClosed)

variable {d : ℕ}

/-! ### Monotonicity of `SmallClusters` -/

/-- `SmallClusters` passes to configurations with more open sites: a closed cluster of `O'` is a
`*`-connected set of closed sites of `O`, hence lies in a closed cluster of `O`. -/
theorem smallClusters_of_subset {O O' : Set (Zd d)} {D : ℕ} (h : SmallClusters O D)
    (hOO' : O ⊆ O') : SmallClusters O' D := by
  intro C hC
  obtain ⟨c, hc⟩ := hC.1
  have hCO : C ⊆ Oᶜ := fun y hy hyO => hC.2.1 hy (hOO' hyO)
  obtain ⟨C₀, hC₀, hCC₀⟩ := exists_isClosedCluster_superset hC.2.2.1 hCO hc
  obtain ⟨⟨R, hR⟩, hD⟩ := h C₀ hC₀
  exact ⟨⟨R, fun y hy => hR y (hCC₀ hy)⟩, fun y hy y' hy' => hD y (hCC₀ hy) y' (hCC₀ hy')⟩

/-! ### Good sites are open on `𝒢_m` -/

/-- For `x ∈ 𝓛_m`, the box `B_{2^{1-m}}(2^{-m} x)` lies in `B̄₃(0)`. -/
lemma obox_subset_cbox_three {m : ℕ} {x : Zd d} (hx : x ∈ latRegion m) :
    obox (latPt ((2 : ℝ)⁻¹ ^ m) x) (2 * (2 : ℝ)⁻¹ ^ m) ⊆ cbox (0 : Rd d) 3 := by
  intro z hz i
  have hs1 : (2 : ℝ)⁻¹ ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h1 : |latPt ((2 : ℝ)⁻¹ ^ m) x i| ≤ 2 - (2 : ℝ)⁻¹ ^ m := (abs_latPt_le_iff m x i).2 (hx i)
  have h2 : |z i - latPt ((2 : ℝ)⁻¹ ^ m) x i| < 2 * (2 : ℝ)⁻¹ ^ m := hz i
  rw [PiLp.zero_apply, sub_zero]
  calc |z i| = |(z i - latPt ((2 : ℝ)⁻¹ ^ m) x i) + latPt ((2 : ℝ)⁻¹ ^ m) x i| := by ring_nf
    _ ≤ |z i - latPt ((2 : ℝ)⁻¹ ^ m) x i| + |latPt ((2 : ℝ)⁻¹ ^ m) x i| := abs_add_le _ _
    _ ≤ 3 := by linarith

/-- `e^{ξ m (Q - η/ξ) log 2} = 2^{(ξQ - η) m}`. -/
lemma exp_eq_two_rpow {ξ Q η : ℝ} (hξ : 0 < ξ) (m : ℕ) :
    Real.exp (ξ * (m * (Q - η / ξ) * Real.log 2)) = (2 : ℝ) ^ ((ξ * Q - η) * m) := by
  rw [Real.rpow_def_of_pos two_pos]
  congr 1
  field_simp

/-- **Good implies open on `𝒢_m`** (DGZ l. 1411–1416): if `φ = ψ + g` and
`ψ ≤ m (Q - η/ξ) log 2` on `B̄₃(0)`, then every `m`-good site of `g` is `m`-open for `φ`. -/
theorem mGood_subset_mOpen {ξ Q η : ℝ} (hξ : 0 < ξ) {φ ψ g : Rd d → ℝ} (hφ : Continuous φ)
    (hg : Continuous g) (hsum : ∀ z, φ z = ψ z + g z) {m : ℕ}
    (hG : ∀ z ∈ cbox (0 : Rd d) 3, ψ z ≤ m * (Q - η / ξ) * Real.log 2) (a : ℝ) :
    mGood ξ g m a ⊆ mOpen ξ Q η φ m a := by
  intro x hx
  rw [mem_mGood_iff] at hx
  rw [mOpen_eq_mGood, mem_mGood_iff]
  intro hreg x' hxx'
  have h1 := hx hreg x' hxx'
  have hC : (0 : ℝ) ≤ (2 : ℝ) ^ ((ξ * Q - η) * m) := by positivity
  have hcomp : lfppDistOn ξ φ (obox (latPt ((2 : ℝ)⁻¹ ^ m) x) (2 * (2 : ℝ)⁻¹ ^ m))
      (latPt ((2 : ℝ)⁻¹ ^ m) x) (latPt ((2 : ℝ)⁻¹ ^ m) x') ≤
      (2 : ℝ) ^ ((ξ * Q - η) * m) * lfppDistOn ξ g
        (obox (latPt ((2 : ℝ)⁻¹ ^ m) x) (2 * (2 : ℝ)⁻¹ ^ m))
        (latPt ((2 : ℝ)⁻¹ ^ m) x) (latPt ((2 : ℝ)⁻¹ ^ m) x') := by
    refine lfppDistOn_le_mul_of_exp_le hφ hg hC fun z hz => ?_
    rw [hsum z, mul_add, Real.exp_add, ← exp_eq_two_rpow hξ m]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    rw [Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left (hG z (obox_subset_cbox_three hreg hz)) hξ.le
  calc _ ≤ _ := hcomp
    _ ≤ (2 : ℝ) ^ ((ξ * Q - η) * m) * ((2 : ℝ)⁻¹ ^ m * a) := mul_le_mul_of_nonneg_left h1 hC
    _ = (2 : ℝ)⁻¹ ^ m * ((2 : ℝ) ^ ((ξ * Q - η) * m) * a) := by ring

/-- **DGZ (4.11)**: on `𝒢_m` (`φ = ψ + g`, `ψ ≤ m (Q - η/ξ) log 2` on `B̄₃(0)`), small clusters of
`m`-bad sites give small clusters of `m`-closed sites. -/
theorem smallClusters_mOpen_of_mGood {ξ Q η : ℝ} (hξ : 0 < ξ) {φ ψ g : Rd d → ℝ}
    (hφ : Continuous φ) (hg : Continuous g) (hsum : ∀ z, φ z = ψ z + g z) {m : ℕ}
    (hG : ∀ z ∈ cbox (0 : Rd d) 3, ψ z ≤ m * (Q - η / ξ) * Real.log 2) {a : ℝ} {D : ℕ}
    (h : SmallClusters (mGood ξ g m a) D) : SmallClusters (mOpen ξ Q η φ m a) D :=
  smallClusters_of_subset h (mGood_subset_mOpen hξ hφ hg hsum hG a)

/-! ### Coarse and fine lattices -/

lemma mem_latRegion_pred_iff {m : ℕ} (hm : 1 ≤ m) {y : Zd d} :
    y ∈ latRegion (m - 1) ↔ ∀ i, |y i| < 2 ^ m := by
  simp only [latRegion, mem_ofPred_eq, Nat.sub_add_cancel hm]

/-- A coarse site outside `𝓛_{m-1}` is a fine site outside `𝓛_m`. -/
lemma two_smul_not_mem_latRegion {m : ℕ} (hm : 1 ≤ m) {y : Zd d} (hy : y ∉ latRegion (m - 1)) :
    2 • y ∉ latRegion m := by
  rw [mem_latRegion_pred_iff hm] at hy
  intro h
  refine hy fun i => ?_
  have := h i
  rw [two_smul_apply, abs_mul, pow_succ] at this
  norm_num at this
  omega

/-- **MA7 G25**: the midpoint `y + y'` of two L-adjacent coarse sites outside `𝓛_{m-1}` is a
fine site outside `𝓛_m`. -/
lemma add_not_mem_latRegion {m : ℕ} (hm : 1 ≤ m) {y y' : Zd d} (hy : y ∉ latRegion (m - 1))
    (hy' : y' ∉ latRegion (m - 1)) (hyy' : LAdj y y') : y + y' ∉ latRegion m := by
  rw [mem_latRegion_pred_iff hm] at hy hy'
  push Not at hy hy'
  obtain ⟨i, hi⟩ := hy
  obtain ⟨i', hi'⟩ := hy'
  obtain ⟨j, hj, hj1⟩ := exists_coord_of_lAdj hyy'
  have hK : (1 : ℤ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  intro h
  by_cases hij : i = j
  · subst hij
    by_cases hi'i : i' = i
    · subst hi'i
      have := h i'
      rw [Pi.add_apply, pow_succ] at this
      rw [abs_lt] at this
      rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at hj1
      rcases le_abs'.1 hi with h1 | h1 <;> rcases le_abs'.1 hi' with h2 | h2 <;> omega
    · have := h i'
      rw [Pi.add_apply, ← hj i' hi'i, pow_succ] at this
      rw [← hj i' hi'i] at hi'
      rw [abs_lt] at this
      rcases le_abs'.1 hi' with h2 | h2 <;> omega
  · have := h i
    rw [Pi.add_apply, hj i hij, pow_succ] at this
    rw [hj i hij] at hi
    rw [abs_lt] at this
    rcases le_abs'.1 hi with h2 | h2 <;> omega

/-- **Refinement of coarse paths**: an L-path `y₀, …, y_k` in `S` gives the fine L-path
`2y₀, y₀ + y₁, 2y₁, …, 2y_k` in `T`, if `2y ∈ T` for `y ∈ S` and the midpoints of the steps lie in
`T`. -/
lemma reflTransGen_two_smul {S T : Set (Zd d)} (hS : ∀ y ∈ S, 2 • y ∈ T)
    (hmid : ∀ y y', y ∈ S → y' ∈ S → LAdj y y' → y + y' ∈ T) {u v : Zd d}
    (h : ReflTransGen (StepIn S LAdj) u v) : ReflTransGen (StepIn T LAdj) (2 • u) (2 • v) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih =>
    obtain ⟨hb, hc, hbc'⟩ := hbc
    rename_i b c _
    have e1 : LAdj (2 • b) (b + c) := by
      unfold LAdj at hbc' ⊢
      simp only [two_smul_apply, Pi.add_apply]
      rw [← hbc']
      exact Finset.sum_congr rfl fun i _ => by ring_nf
    have e2 : LAdj (b + c) (2 • c) := by
      unfold LAdj at hbc' ⊢
      simp only [two_smul_apply, Pi.add_apply]
      rw [← hbc']
      exact Finset.sum_congr rfl fun i _ => by ring_nf
    exact (ih.tail ⟨hS _ hb, hmid _ _ hb hc hbc', e1⟩).tail ⟨hmid _ _ hb hc hbc', hS _ hc, e2⟩

/-- On `𝒢_{m-1}`, nice sites are `(m-1)`-open. -/
theorem mNice_subset_mOpen {ξ Q η : ℝ} (hξ : 0 < ξ) {φ ψ₁ g₁ g₂ : Rd d → ℝ}
    (hφ : Continuous φ) (hg₁ : Continuous g₁) (hsum₁ : ∀ z, φ z = ψ₁ z + g₁ z) {m : ℕ}
    (hG₁ : ∀ z ∈ cbox (0 : Rd d) 3, ψ₁ z ≤ ((m - 1 : ℕ) : ℝ) * (Q - η / ξ) * Real.log 2)
    (a₁ a₂ : ℝ) : mNice ξ g₁ g₂ m a₁ a₂ ⊆ mOpen ξ Q η φ (m - 1) a₁ := by
  intro y hy
  by_cases hreg : y ∈ latRegion (m - 1)
  · exact mGood_subset_mOpen hξ hφ hg₁ hsum₁ hG₁ a₁ (hy hreg).1
  · exact mem_mOpen_of_not_mem_latRegion hreg

/-- On `𝒢_m`, the fine site `2y` of a nice coarse site is `m`-open. -/
lemma two_smul_mem_mOpen_of_mem_mNice {ξ Q η : ℝ} (hξ : 0 < ξ) {φ ψ₂ g₁ g₂ : Rd d → ℝ}
    (hφ : Continuous φ) (hg₂ : Continuous g₂) (hsum₂ : ∀ z, φ z = ψ₂ z + g₂ z) {m : ℕ}
    (hm : 1 ≤ m) (hG₂ : ∀ z ∈ cbox (0 : Rd d) 3, ψ₂ z ≤ m * (Q - η / ξ) * Real.log 2)
    {a₁ a₂ : ℝ} {y : Zd d} (hy : y ∈ mNice ξ g₁ g₂ m a₁ a₂) : 2 • y ∈ mOpen ξ Q η φ m a₂ := by
  by_cases hreg : y ∈ latRegion (m - 1)
  · exact mGood_subset_mOpen hξ hφ hg₂ hsum₂ hG₂ a₂ ((hy hreg).2 _ (withinInf_refl (by norm_num) _))
  · exact mem_mOpen_of_not_mem_latRegion (two_smul_not_mem_latRegion hm hreg)

/-- **MA7 D-4.2, third clause of `ℱ_{m,n}`** (deterministic; repairs DGZ l. 1444, gap G2, and
G25): suppose `φ = ψ₁ + g₁ = ψ₂ + g₂` (`h_n = h_{m-1} + h_{m-1,n} = h_m + h_{m,n}`),
`𝒢_{m-1}` and `𝒢_m` hold for `ψ₁`, `ψ₂`, and the closed (rough) clusters of the nice configuration
are bounded with diameter `≤ D'`, `2D' + 3 ≤ m²`. Then every fine site `x` is within `ℓ^∞`-distance
`m²` of `2 • y` for a coarse site `y` such that `2 • y` is free for the `m`-open configuration of
`φ` and `y` is free for the `(m-1)`-open configuration of `φ`. -/
theorem exists_free_of_smallClusters_mNice (hd : 2 ≤ d) {ξ Q η : ℝ} (hξ : 0 < ξ) {m : ℕ}
    (hm : 1 ≤ m) {φ ψ₁ ψ₂ g₁ g₂ : Rd d → ℝ} (hφ : Continuous φ) (hg₁ : Continuous g₁)
    (hg₂ : Continuous g₂) (hsum₁ : ∀ z, φ z = ψ₁ z + g₁ z) (hsum₂ : ∀ z, φ z = ψ₂ z + g₂ z)
    (hG₁ : ∀ z ∈ cbox (0 : Rd d) 3, ψ₁ z ≤ ((m - 1 : ℕ) : ℝ) * (Q - η / ξ) * Real.log 2)
    (hG₂ : ∀ z ∈ cbox (0 : Rd d) 3, ψ₂ z ≤ m * (Q - η / ξ) * Real.log 2) {a₁ a₂ : ℝ} {D' : ℕ}
    (hN : SmallClusters (mNice ξ g₁ g₂ m a₁ a₂) D') (hD' : 2 * D' + 3 ≤ m ^ 2) (x : Zd d) :
    ∃ y : Zd d, WithinInf ((m : ℤ) ^ 2) x (2 • y) ∧ FreeSite (mOpen ξ Q η φ m a₂) (2 • y) ∧
      FreeSite (mOpen ξ Q η φ (m - 1) a₁) y := by
  set N := mNice ξ g₁ g₂ m a₁ a₂ with hNdef
  -- the coarse site below `x`, and a nice-free coarse site near it (hole lemma)
  set x' : Zd d := fun i => x i / 2 with hx'
  obtain ⟨y, hyx', hyN⟩ := holeLemma d hd N D' hN x'
  -- a far coarse site and a nice path to it (free sites reach infinity)
  have hd1 : 1 ≤ d := by omega
  set v : Zd d := fun _ => 2 ^ m + 1 with hv
  have hRN : ∀ z, z ∉ N → WithinInf (2 ^ m) z 0 := by
    intro z hz
    have hreg : z ∈ latRegion (m - 1) := by
      by_contra hreg
      exact hz fun h => absurd h hreg
    intro i
    rw [Pi.zero_apply, sub_zero]
    exact ((mem_latRegion_pred_iff hm).1 hreg i).le
  have hvN : ¬ WithinInf (2 ^ m) v 0 := not_withinInf_const hd1 (by omega)
  have hpath : ReflTransGen (StepIn N LAdj) y v :=
    freeToInfinity d hd N D' hN _ hRN y v hyN hvN
  refine ⟨y, fun i => ?_, ?_, ?_⟩
  · -- `|x - 2y|_∞ ≤ 1 + 2 (D' + 1) ≤ m²`
    have h1 := hyx' i
    rw [two_smul_apply]
    have hD'z : 2 * (D' : ℤ) + 3 ≤ (m : ℤ) ^ 2 := by exact_mod_cast hD'
    simp only [hx'] at h1
    rw [abs_le] at h1 ⊢
    omega
  · -- `2y` is free for `O_m`: the refined path is `m`-open
    have hS : ∀ y' ∈ N, 2 • y' ∈ mOpen ξ Q η φ m a₂ := fun y' hy' =>
      two_smul_mem_mOpen_of_mem_mNice hξ hφ hg₂ hsum₂ hm hG₂ hy'
    have hmid : ∀ y' y'', y' ∈ N → y'' ∈ N → LAdj y' y'' → y' + y'' ∈ mOpen ξ Q η φ m a₂ := by
      intro y' y'' hy' hy'' h
      have hw := h.withinInf
      by_cases h1 : y' ∈ latRegion (m - 1)
      · refine mGood_subset_mOpen hξ hφ hg₂ hsum₂ hG₂ a₂ ((hy' h1).2 _ fun i => ?_)
        have := hw i
        rw [Pi.add_apply, two_smul_apply]
        rw [abs_le] at this ⊢
        omega
      · by_cases h2 : y'' ∈ latRegion (m - 1)
        · refine mGood_subset_mOpen hξ hφ hg₂ hsum₂ hG₂ a₂ ((hy'' h2).2 _ fun i => ?_)
          have := hw i
          rw [Pi.add_apply, two_smul_apply]
          rw [abs_le] at this ⊢
          omega
        · exact mem_mOpen_of_not_mem_latRegion (add_not_mem_latRegion hm h1 h2 h)
    have hpath' := reflTransGen_two_smul hS hmid hpath
    refine freeSite_of_reflTransGen hd (R := 2 ^ (m + 1))
      (fun z hz => withinInf_of_not_mem_mOpen hz) ?_ hpath'
    intro hw
    have := hw ⟨0, by omega⟩
    rw [two_smul_apply, Pi.zero_apply, sub_zero, pow_succ] at this
    simp only [hv] at this
    rw [abs_le] at this
    omega
  · -- `y` is free for `O_{m-1}`: nice sites are `(m-1)`-open
    have hpath1 := reflTransGen_stepIn_mono (mNice_subset_mOpen hξ hφ hg₁ hsum₁ hG₁ a₁ a₂) hpath
    refine freeSite_of_reflTransGen hd (R := 2 ^ m) (fun z hz => ?_) hvN hpath1
    have := withinInf_of_not_mem_mOpen hz
    rwa [Nat.sub_add_cancel hm] at this

end DGZ

end HigherDimLQGMetric
