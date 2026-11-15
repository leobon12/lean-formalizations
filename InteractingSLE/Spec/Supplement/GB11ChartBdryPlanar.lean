/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11ConnGrowth
import QuantumZipper.Proofs.Complex.TopoJaniszewski
import QuantumZipper.Proofs.Complex.TopoSep

/-!
# Lemma GB11's pocket charts: the two walls of a pocket meet only at its ends

Packet PROVE-T14-GW4T5, item (1a), planar part. For a shaped pocket `C` between two complete simple flows `α_R`, `α_L`
whose common contacts have the same order along both curves (GB11's barrier input), the two boundary arcs of `C` —
`α_R([s₁, s₂])` and `α_L([t₁, t₂])` for a bounded pocket, `α_R([s₁, ∞))` and `α_L([t₁, ∞))` for the unbounded one —
meet only at the exit `α_R(s₁) = α_L(t₁)` (and the entry `α_R(s₂) = α_L(t₂)`). So the frontier of `C` is a Jordan
curve (through `∞` for the unbounded pocket), which is what Carathéodory's boundary correspondence needs.

## The argument

An intermediate contact `X = α_R(m) = α_L(m')` splits the walls into a part `F₁` before `X` and a part `F₂` after `X`,
with `F₁ ∩ F₂ = {X}` (same contact order). The pocket `C` is a bounded component of the complement of `F₁ ∪ F₂`, and its
closure contains a point (the entry) off `F₁` that escapes to `∞` off `F₁` (along `α_R` beyond the entry), and a point
(the exit) off `F₂` that escapes to `∞` off `F₂` (back along `α_R` to `0`, then down the negative imaginary axis). Then
neither `F₁` nor `F₂` separates a point of `C` from `∞`, so by Janiszewski's theorem
(`QuantumZipper.CA.Topo.janiszewski`) neither does `F₁ ∪ F₂` — contradicting the boundedness of `C`
(`false_of_escaping_ends`). The unbounded pocket is first sent to a bounded one by `μ(z) = −1/(z + i)`.

## Main results

* `eq_connectedComponentIn_of_frontier_subset`, `false_of_escaping_ends` (planar);
* **`inter_subset_of_boundedPocket`**: the two arcs of a bounded pocket meet only at its ends;
* **`inter_subset_of_unboundedPocket`**: the two arcs of the unbounded pocket meet only at the exit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Theorem14

namespace GB11Chart

/-! ### Planar lemmas -/

/-- An open preconnected set disjoint from a set `F` that contains its frontier is a component of `Fᶜ`. -/
theorem eq_connectedComponentIn_of_frontier_subset {C F : Set ℂ} (hCo : IsOpen C) (hCc : IsPreconnected C)
    {y : ℂ} (hy : y ∈ C) (hCF : ∀ z ∈ C, z ∉ F) (hfr : frontier C ⊆ F) :
    connectedComponentIn Fᶜ y = C := by
  refine Subset.antisymm ?_ (hCc.subset_connectedComponentIn hy fun z hz => hCF z hz)
  have hD : IsPreconnected (connectedComponentIn Fᶜ y) := isPreconnected_connectedComponentIn
  refine hD.subset_left_of_subset_union hCo isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_right (compl_subset_compl.2 subset_closure)) (fun z hz => ?_)
    ⟨y, mem_connectedComponentIn (hCF y hy), hy⟩
  by_cases hzC : z ∈ C
  · exact Or.inl hzC
  · refine Or.inr fun hcl => ?_
    have hzF : z ∈ Fᶜ := connectedComponentIn_subset _ _ hz
    exact hzF (hfr ⟨hcl, by rwa [hCo.interior_eq]⟩)

/-- A point of `C̄` off `F` escaping to infinity off `F` lies in the unbounded part of the complement: every point of
norm `> R` is in the component of `Fᶜ` through `C` (`C ∩ F = ∅`, `C` preconnected, `F ⊆ ball 0 R`). -/
theorem mem_connectedComponentIn_of_escape {C F S : Set ℂ} (hCc : IsPreconnected C) {y : ℂ} (hy : y ∈ C)
    (hCF : ∀ z ∈ C, z ∉ F) {R : ℝ} (hFR : F ⊆ ball 0 R) {q : ℂ} (hq : q ∈ closure C) (hqF : q ∉ F)
    (hS : IsPreconnected S) (hqS : q ∈ S) (hSF : ∀ z ∈ S, z ∉ F) (hSu : ¬ IsBounded S) {z : ℂ}
    (hz : R < ‖z‖) : z ∈ connectedComponentIn Fᶜ y := by
  set D := connectedComponentIn Fᶜ y with hDdef
  have hCD : C ⊆ D := hCc.subset_connectedComponentIn hy fun w hw => hCF w hw
  have hqD : q ∈ D := GB11Conn.mem_connectedComponentIn_of_mem_closure (closure_mono hCD hq) hqF
  have hSD : S ⊆ D := by
    rw [hDdef, connectedComponentIn_eq hqD]
    exact hS.subset_connectedComponentIn hqS fun w hw => hSF w hw
  obtain ⟨w, hwS, hwR⟩ : ∃ w ∈ S, R < ‖w‖ := by
    by_contra h
    push Not at h
    exact hSu ((isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset fun w hw =>
      mem_closedBall_zero_iff.2 (h w hw))
  have hOF : ∀ v ∈ {v : ℂ | R < ‖v‖}, v ∉ F := fun v hv hvF =>
    absurd (mem_ball_zero_iff.1 (hFR hvF)) (not_lt.2 (le_of_lt hv))
  have hwD : w ∈ D := hSD hwS
  have hOD : {v : ℂ | R < ‖v‖} ⊆ D := by
    rw [hDdef, connectedComponentIn_eq hwD]
    exact (QuantumZipper.CA.Topo.isPreconnected_setOf_lt_norm R).subset_connectedComponentIn hwR hOF
  exact hOD hz

/-- **Escaping ends (Janiszewski).** Let `F₁, F₂` be compact with `F₁ ∩ F₂` preconnected, and `C` a bounded open
preconnected set off `F₁ ∪ F₂` whose frontier lies in `F₁ ∪ F₂`. Then `C̄` cannot contain both a point `q ∉ F₁` that
escapes to infinity along a preconnected set off `F₁` and a point `p ∉ F₂` that escapes to infinity off `F₂`. -/
theorem false_of_escaping_ends {F₁ F₂ C : Set ℂ} (hF₁ : IsCompact F₁) (hF₂ : IsCompact F₂)
    (hF₁₂ : IsPreconnected (F₁ ∩ F₂)) (hCo : IsOpen C) (hCc : IsPreconnected C) (hCb : IsBounded C) {y : ℂ}
    (hy : y ∈ C) (hCF : ∀ z ∈ C, z ∉ F₁ ∪ F₂) (hfr : frontier C ⊆ F₁ ∪ F₂)
    {q : ℂ} (hq : q ∈ closure C) (hqF : q ∉ F₁) {Sq : Set ℂ} (hSq : IsPreconnected Sq) (hqS : q ∈ Sq)
    (hSqF : ∀ z ∈ Sq, z ∉ F₁) (hSqu : ¬ IsBounded Sq)
    {p : ℂ} (hp : p ∈ closure C) (hpF : p ∉ F₂) {Sp : Set ℂ} (hSp : IsPreconnected Sp) (hpS : p ∈ Sp)
    (hSpF : ∀ z ∈ Sp, z ∉ F₂) (hSpu : ¬ IsBounded Sp) : False := by
  obtain ⟨R, -, hR⟩ := (hCb.union (hF₁.isBounded.union hF₂.isBounded)).subset_ball_lt 0 0
  set z : ℂ := ((R + 1 : ℝ) : ℂ) with hzdef
  have hzR : R < ‖z‖ := by
    rw [hzdef, Complex.norm_real, Real.norm_eq_abs]
    exact lt_of_lt_of_le (lt_add_one R) (le_abs_self _)
  have hF₁R : F₁ ⊆ ball 0 R := fun w hw => hR (Or.inr (Or.inl hw))
  have hF₂R : F₂ ⊆ ball 0 R := fun w hw => hR (Or.inr (Or.inr hw))
  have hzF : z ∉ F₁ ∪ F₂ := by
    rintro (h | h)
    · exact absurd (mem_ball_zero_iff.1 (hF₁R h)) (not_lt.2 hzR.le)
    · exact absurd (mem_ball_zero_iff.1 (hF₂R h)) (not_lt.2 hzR.le)
  have h₁ : z ∈ connectedComponentIn F₁ᶜ y :=
    mem_connectedComponentIn_of_escape hCc hy (fun w hw h => hCF w hw (Or.inl h)) hF₁R hq hqF hSq hqS hSqF hSqu hzR
  have h₂ : z ∈ connectedComponentIn F₂ᶜ y :=
    mem_connectedComponentIn_of_escape hCc hy (fun w hw h => hCF w hw (Or.inr h)) hF₂R hp hpF hSp hpS hSpF hSpu hzR
  have hj := QuantumZipper.CA.Topo.janiszewski hF₁ hF₂ hF₁₂ (hCF y hy) hzF h₁ h₂
  rw [eq_connectedComponentIn_of_frontier_subset hCo hCc hy hCF hfr] at hj
  exact absurd (mem_ball_zero_iff.1 (hR (Or.inl hj))) (not_lt.2 hzR.le)

/-! ### The inversion `μ(z) = −1/(z + i)` -/

section Mu

/-- The inversion `μ(z) = −1/(z + i)`, a bijection of `ℂ` (junk value `μ(−i) = 0`) sending `ℍ̄` into the closed unit
disc and `∞` to `0`. -/
def mu (z : ℂ) : ℂ := -(z + Complex.I)⁻¹

/-- The inverse of `mu`. -/
def muInv (ζ : ℂ) : ℂ := -ζ⁻¹ - Complex.I

@[simp] theorem mu_muInv (ζ : ℂ) : mu (muInv ζ) = ζ := by
  simp only [mu, muInv, sub_add_cancel, inv_neg, inv_inv, neg_neg]

@[simp] theorem muInv_mu (z : ℂ) : muInv (mu z) = z := by
  simp only [mu, muInv, inv_neg, inv_inv, neg_neg, add_sub_cancel_right]

theorem mu_injective : Function.Injective mu := fun z w h => by
  rw [← muInv_mu z, h, muInv_mu]

theorem mu_eq_zero_iff {z : ℂ} : mu z = 0 ↔ z = -Complex.I := by
  simp only [mu, neg_eq_zero, inv_eq_zero]
  constructor
  · intro h; linear_combination h
  · intro h; rw [h]; ring

theorem neg_I_notMem_Hbar : -Complex.I ∉ Hbar := fun h => by
  have : (0 : ℝ) ≤ (-Complex.I).im := h
  norm_num at this

theorem mem_Hbar_of_mem_H {z : ℂ} (hz : z ∈ H) : z ∈ Hbar := le_of_lt (show (0 : ℝ) < z.im from hz)

theorem mu_ne_zero_of_mem_Hbar {z : ℂ} (hz : z ∈ Hbar) : mu z ≠ 0 := fun h =>
  neg_I_notMem_Hbar (mu_eq_zero_iff.1 h ▸ hz)

theorem continuousAt_mu {z : ℂ} (hz : z ≠ -Complex.I) : ContinuousAt mu z := by
  have h : z + Complex.I ≠ 0 := fun h => hz (by linear_combination h)
  exact ((continuousAt_id.add continuousAt_const).inv₀ h).neg

theorem continuousOn_mu_Hbar : ContinuousOn mu Hbar := fun _ hz =>
  (continuousAt_mu fun h => neg_I_notMem_Hbar (h ▸ hz)).continuousWithinAt

theorem continuousOn_muInv : ContinuousOn muInv {0}ᶜ := fun _ hζ =>
  ((continuousAt_id.inv₀ hζ).neg.sub continuousAt_const).continuousWithinAt

theorem muInv_im (ζ : ℂ) : (muInv ζ).im = ζ.im / Complex.normSq ζ - 1 := by
  simp only [muInv, Complex.sub_im, Complex.neg_im, Complex.inv_im, Complex.I_im]
  ring

theorem norm_mu_le_one {z : ℂ} (hz : z ∈ Hbar) : ‖mu z‖ ≤ 1 := by
  have hz' : (0 : ℝ) ≤ z.im := hz
  have h1 : 1 ≤ ‖z + Complex.I‖ := by
    have := Complex.abs_im_le_norm (z + Complex.I)
    simp only [Complex.add_im, Complex.I_im] at this
    rw [abs_of_nonneg (by linarith)] at this
    linarith
  rw [mu, norm_neg, norm_inv]
  exact inv_le_one_of_one_le₀ h1

theorem tendsto_mu_cobounded : Tendsto mu (cobounded ℂ) (𝓝 0) := by
  have h1 : Tendsto (fun z : ℂ => z + Complex.I) (cobounded ℂ) (cobounded ℂ) :=
    tendsto_add_const_cobounded _
  have h2 := (tendsto_inv₀_cobounded.comp h1).neg
  have he : mu = fun z => -(z + Complex.I)⁻¹ := rfl
  rw [he]
  simpa [Function.comp_def] using h2

/-- The closure of the `μ`-image of a closed set `S ⊆ ℍ̄` adds at most `0`. -/
theorem closure_mu_image_subset {S : Set ℂ} (hS : IsClosed S) :
    closure (mu '' S) ⊆ mu '' S ∪ {0} := by
  intro ζ hζ
  by_cases h0 : ζ = 0
  · exact Or.inr h0
  · left
    have hc : ContinuousWithinAt muInv (mu '' S) ζ := (continuousOn_muInv ζ h0).mono_of_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds h0))
    have hmem := hc.mem_closure_image hζ
    rw [image_image] at hmem
    simp only [muInv_mu, image_id'] at hmem
    exact ⟨muInv ζ, hS.closure_eq ▸ hmem, mu_muInv ζ⟩

/-- `μ(S) ∪ {0}` is compact for a closed `S ⊆ ℍ̄`. -/
theorem isCompact_mu_image_union_zero {S : Set ℂ} (hS : IsClosed S) (hSH : S ⊆ Hbar) :
    IsCompact (mu '' S ∪ {0}) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · refine closure_subset_iff_isClosed.1 ?_
    rw [closure_union, closure_singleton]
    exact union_subset (closure_mu_image_subset hS) subset_union_right
  · refine (isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset ?_
    rintro _ (⟨z, hz, rfl⟩ | h)
    · exact mem_closedBall_zero_iff.2 (norm_mu_le_one (hSH hz))
    · rw [mem_singleton_iff.1 h]; exact mem_closedBall_self zero_le_one

/-- `μ` of an open set `C ⊆ ℍ` is open. -/
theorem isOpen_mu_image {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H) : IsOpen (mu '' C) := by
  have he : mu '' C = {0}ᶜ ∩ muInv ⁻¹' C := by
    ext ζ
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨mu_ne_zero_of_mem_Hbar (mem_Hbar_of_mem_H (hCH hz)), by simpa using hz⟩
    · rintro ⟨-, hζ⟩
      exact ⟨muInv ζ, hζ, mu_muInv ζ⟩
  rw [he]
  exact continuousOn_muInv.isOpen_inter_preimage isOpen_compl_singleton hCo

/-- The frontier of `μ(C)` (`C ⊆ ℍ` open) lies in `μ(∂C) ∪ {0}`. -/
theorem frontier_mu_image_subset {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H) :
    frontier (mu '' C) ⊆ mu '' frontier C ∪ {0} := by
  intro ζ hζ
  by_cases h0 : ζ = 0
  · exact Or.inr h0
  · left
    have hc : ContinuousWithinAt muInv (mu '' C) ζ := (continuousOn_muInv ζ h0).mono_of_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds h0))
    have hmem := hc.mem_closure_image hζ.1
    rw [image_image] at hmem
    simp only [muInv_mu, image_id'] at hmem
    refine ⟨muInv ζ, ⟨hmem, ?_⟩, mu_muInv ζ⟩
    rw [hCo.interior_eq]
    intro hC
    have : ζ ∈ interior (mu '' C) := by
      rw [(isOpen_mu_image hCo hCH).interior_eq]; exact ⟨muInv ζ, hC, mu_muInv ζ⟩
    exact hζ.2 this

/-- A point `−u i`, `u > 0`, of the negative imaginary axis is `μ` of a point below `ℝ`. -/
theorem muInv_negImag_notMem_Hbar {u : ℝ} (hu : 0 < u) : muInv (-((u : ℂ) * Complex.I)) ∉ Hbar := by
  intro h
  have h' : (0 : ℝ) ≤ (muInv (-((u : ℂ) * Complex.I))).im := h
  rw [muInv_im] at h'
  simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
    Complex.I_re, mul_zero, add_zero, Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_I] at h'
  have : -u / (u * u) < 0 := div_neg_of_neg_of_pos (neg_lt_zero.2 hu) (by positivity)
  linarith

/-- A point `u i`, `u > 1`, of the imaginary axis is `μ` of a point below `ℝ`. -/
theorem muInv_posImag_notMem_Hbar {u : ℝ} (hu : 1 < u) : muInv ((u : ℂ) * Complex.I) ∉ Hbar := by
  intro h
  have h' : (0 : ℝ) ≤ (muInv ((u : ℂ) * Complex.I)).im := h
  rw [muInv_im] at h'
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
    Complex.I_re, mul_zero, add_zero, Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_I] at h'
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have : u / (u * u) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  linarith

theorem muInv_I : muInv Complex.I = 0 := by simp [muInv]

theorem mu_zero : mu 0 = Complex.I := by simp [mu]

end Mu

/-! ### Walls -/

section Walls

variable {αR αL : ℝ≥0 → ℂ}

/-- A proper curve leaves every bounded set: its image of a half-line is unbounded. -/
theorem not_isBounded_image_Ici (hα : GB11.IsCompleteSimpleFlow αR) (s : ℝ≥0) : ¬ IsBounded (αR '' Ici s) := by
  intro hb
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hb
  obtain ⟨r, hr⟩ := (hα.2.2.2.2.eventually_gt_atTop M).exists_forall_of_atTop
  exact absurd (hM _ ⟨max r s, le_max_right r s, rfl⟩) (not_le.2 (hr _ (le_max_left r s)))

/-- The negative imaginary axis `{−u i : u ≥ 0}` is preconnected and unbounded. -/
theorem isPreconnected_negImagRay : IsPreconnected ((fun u : ℝ => -((u : ℂ) * Complex.I)) '' Ici 0) :=
  isPreconnected_Ici.image _ (by fun_prop)

theorem not_isBounded_negImagRay : ¬ IsBounded ((fun u : ℝ => -((u : ℂ) * Complex.I)) '' Ici 0) := by
  intro hb
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hb
  have h := hM _ ⟨|M| + 1, le_trans (abs_nonneg M) (le_add_of_nonneg_right zero_le_one), rfl⟩
  rw [norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)] at h
  linarith [le_abs_self M]

/-- A point of the negative imaginary axis in `ℍ̄` is `0`. -/
theorem eq_zero_of_negImagRay_mem_Hbar {u : ℝ} (hu : 0 ≤ u) (h : -((u : ℂ) * Complex.I) ∈ Hbar) :
    -((u : ℂ) * Complex.I) = 0 := by
  have him : 0 ≤ (-((u : ℂ) * Complex.I)).im := h
  simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
    Complex.I_re, mul_zero, add_zero] at him
  have : u = 0 := le_antisymm (by linarith) hu
  simp [this]

variable (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
  (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
include hR hL hord

/-- **The two arcs of a bounded pocket meet only at its ends** (GB11's barrier input: same contact order). -/
theorem inter_subset_of_boundedPocket {s₁ s₂ t₁ t₂ : ℝ≥0} (h1 : αR s₁ = αL t₁) (h2 : αR s₂ = αL t₂)
    {C : Set ℂ} (hCo : IsOpen C) (hCc : IsPreconnected C) (hCb : IsBounded C) {y : ℂ} (hy : y ∈ C)
    (hCF : ∀ z ∈ C, z ∉ range αR ∪ range αL) (hfr : frontier C ⊆ αR '' Icc s₁ s₂ ∪ αL '' Icc t₁ t₂)
    (hP : αR s₁ ∈ closure C) (hQ : αR s₂ ∈ closure C) :
    αR '' Icc s₁ s₂ ∩ αL '' Icc t₁ t₂ ⊆ {αR s₁, αR s₂} := by
  rintro X ⟨⟨m, hm, rfl⟩, ⟨m', hm', hX⟩⟩
  rcases eq_or_lt_of_le hm.1 with hm1 | hm1
  · exact Or.inl (congrArg αR hm1.symm)
  rcases eq_or_lt_of_le hm.2 with hm2 | hm2
  · exact Or.inr (congrArg αR hm2)
  exfalso
  have hX' : αR m = αL m' := hX.symm
  have hm'1 : t₁ < m' := (hord s₁ m t₁ m' h1 hX').1 hm1
  have hm'2 : m' < t₂ := (hord m s₂ m' t₂ hX' h2).1 hm2
  have hRi := hR.2.1
  have hLi := hL.2.1
  set F₁ := αR '' Icc s₁ m ∪ αL '' Icc t₁ m' with hF₁
  set F₂ := αR '' Icc m s₂ ∪ αL '' Icc m' t₂ with hF₂
  have hF₁c : IsCompact F₁ := (isCompact_Icc.image hR.1).union (isCompact_Icc.image hL.1)
  have hF₂c : IsCompact F₂ := (isCompact_Icc.image hR.1).union (isCompact_Icc.image hL.1)
  have hF₁₂ : F₁ ∩ F₂ ⊆ {αR m} := by
    rintro w ⟨hw1, hw2⟩
    rcases hw1 with ⟨a, ha, rfl⟩ | ⟨a', ha', rfl⟩ <;> rcases hw2 with ⟨b, hb, hb'⟩ | ⟨b', hb', hb''⟩
    · have hab : b = a := hRi hb'
      have : a = m := le_antisymm ha.2 (hab ▸ hb.1)
      rw [this]; rfl
    · have hc := hord a m b' m' hb''.symm hX'
      rcases eq_or_lt_of_le ha.2 with h | h
      · rw [h]; rfl
      · exact absurd (hc.1 h) (not_lt.2 hb'.1)
    · have hc := hord m b m' a' hX' hb'
      rcases eq_or_lt_of_le hb.1 with h | h
      · rw [← hb', ← h]; rfl
      · exact absurd (hc.1 h) (not_lt.2 ha'.2)
    · have hab : b' = a' := hLi hb''
      have : a' = m' := le_antisymm ha'.2 (hab ▸ hb'.1)
      rw [this, ← hX']; rfl
  have hpre : IsPreconnected (F₁ ∩ F₂) :=
    (subsingleton_singleton.anti hF₁₂).isPreconnected
  have hCF' : ∀ z ∈ C, z ∉ F₁ ∪ F₂ := by
    intro z hz hzF
    refine hCF z hz ?_
    rcases hzF with (⟨a, -, rfl⟩ | ⟨a, -, rfl⟩) | (⟨a, -, rfl⟩ | ⟨a, -, rfl⟩)
    exacts [Or.inl ⟨a, rfl⟩, Or.inr ⟨a, rfl⟩, Or.inl ⟨a, rfl⟩, Or.inr ⟨a, rfl⟩]
  have hfr' : frontier C ⊆ F₁ ∪ F₂ := by
    refine hfr.trans ?_
    rintro w (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · rcases le_total a m with h | h
      · exact Or.inl (Or.inl ⟨a, ⟨ha.1, h⟩, rfl⟩)
      · exact Or.inr (Or.inl ⟨a, ⟨h, ha.2⟩, rfl⟩)
    · rcases le_total a m' with h | h
      · exact Or.inl (Or.inr ⟨a, ⟨ha.1, h⟩, rfl⟩)
      · exact Or.inr (Or.inr ⟨a, ⟨h, ha.2⟩, rfl⟩)
  -- the entry escapes along `α_R` beyond it, off `F₁`
  have hSqF : ∀ z ∈ αR '' Ici s₂, z ∉ F₁ := by
    rintro _ ⟨r, hr, rfl⟩ (⟨a, ha, he⟩ | ⟨a', ha', he⟩)
    · have : a = r := hRi he
      exact absurd (lt_of_lt_of_le hm2 hr) (not_lt.2 (this ▸ ha.2))
    · exact absurd ((hord m r m' a' hX' he.symm).1 (lt_of_lt_of_le hm2 hr)) (not_lt.2 ha'.2)
  -- the exit escapes back along `α_R` to `0` and down the negative imaginary axis, off `F₂`
  set ray := (fun u : ℝ => -((u : ℂ) * Complex.I)) '' Ici 0 with hray
  have h0ray : (0 : ℂ) ∈ ray := ⟨0, (mem_Ici.2 le_rfl), by simp⟩
  have h0F₂ : (0 : ℂ) ∉ F₂ := by
    rintro (⟨a, ha, he⟩ | ⟨a', ha', he⟩)
    · have : a = 0 := hRi (he.trans hR.2.2.1.symm)
      exact absurd (lt_of_le_of_lt ((zero_le : (0 : ℝ≥0) ≤ s₁)) (lt_of_lt_of_le hm1 (this ▸ ha.1))) (lt_irrefl 0)
    · have : a' = 0 := hLi (he.trans hL.2.2.1.symm)
      exact absurd (lt_of_le_of_lt ((zero_le : (0 : ℝ≥0) ≤ t₁)) (lt_of_lt_of_le hm'1 (this ▸ ha'.1))) (lt_irrefl 0)
  have hF₂H : F₂ ⊆ Hbar := by
    rintro _ (⟨a, -, rfl⟩ | ⟨a, -, rfl⟩)
    exacts [hR.2.2.2.1 a, hL.2.2.2.1 a]
  have hSpF : ∀ z ∈ αR '' Icc 0 s₁ ∪ ray, z ∉ F₂ := by
    rintro _ (⟨r, hr, rfl⟩ | ⟨u, hu, rfl⟩) hzF
    · rcases hzF with ⟨b, hb, he⟩ | ⟨b', hb', he⟩
      · have : b = r := hRi he
        exact absurd (lt_of_le_of_lt hr.2 (lt_of_lt_of_le hm1 (this ▸ hb.1))) (lt_irrefl _)
      · exact absurd ((hord r m b' m' he.symm hX').1 (lt_of_le_of_lt hr.2 hm1)) (not_lt.2 hb'.1)
    · have h0 := eq_zero_of_negImagRay_mem_Hbar hu (hF₂H hzF)
      exact h0F₂ (h0 ▸ hzF)
  have hSp : IsPreconnected (αR '' Icc 0 s₁ ∪ ray) :=
    (isPreconnected_Icc.image _ hR.1.continuousOn).union 0
      ⟨0, left_mem_Icc.2 ((zero_le : (0 : ℝ≥0) ≤ s₁)), hR.2.2.1⟩ h0ray isPreconnected_negImagRay
  have hPmem : αR s₁ ∈ αR '' Icc 0 s₁ ∪ ray := Or.inl ⟨s₁, ⟨(zero_le : (0 : ℝ≥0) ≤ s₁), le_rfl⟩, rfl⟩
  exact false_of_escaping_ends hF₁c hF₂c hpre hCo hCc hCb hy hCF' hfr' hQ (hSqF _ ⟨s₂, (mem_Ici.2 le_rfl), rfl⟩)
    (isPreconnected_Ici.image _ hR.1.continuousOn) ⟨s₂, (mem_Ici.2 le_rfl), rfl⟩ hSqF (not_isBounded_image_Ici hR s₂)
    hP (hSpF _ hPmem) hSp hPmem hSpF (fun hb => not_isBounded_negImagRay (hb.subset subset_union_right))

/-- **The two arcs of the unbounded pocket meet only at the exit** (GB11's barrier input: same contact order). The
pocket is sent to a bounded one by `μ(z) = −1/(z + i)` (`∞ ↦ 0`) and `false_of_escaping_ends` applies. -/
theorem inter_subset_of_unboundedPocket {s₁ t₁ : ℝ≥0} (h1 : αR s₁ = αL t₁) {C : Set ℂ} (hCo : IsOpen C)
    (hCc : IsPreconnected C) (hCH : C ⊆ H) (hCu : ¬ IsBounded C) {y : ℂ} (hy : y ∈ C)
    (hCF : ∀ z ∈ C, z ∉ range αR ∪ range αL) (hfr : frontier C ⊆ αR '' Ici s₁ ∪ αL '' Ici t₁)
    (hP : αR s₁ ∈ closure C) :
    αR '' Ici s₁ ∩ αL '' Ici t₁ ⊆ {αR s₁} := by
  rintro X ⟨⟨m, hm, rfl⟩, ⟨m', hm', hX⟩⟩
  rcases eq_or_lt_of_le (mem_Ici.1 hm) with hm1 | hm1
  · exact congrArg αR hm1.symm
  exfalso
  have hX' : αR m = αL m' := hX.symm
  have hm'1 : t₁ < m' := (hord s₁ m t₁ m' h1 hX').1 hm1
  have hRi := hR.2.1
  have hLi := hL.2.1
  set F₁ := αR '' Icc s₁ m ∪ αL '' Icc t₁ m' with hF₁
  set F₂ := αR '' Ici m ∪ αL '' Ici m' with hF₂
  have hF₁H : F₁ ⊆ Hbar := by
    rintro _ (⟨a, -, rfl⟩ | ⟨a, -, rfl⟩)
    exacts [hR.2.2.2.1 a, hL.2.2.2.1 a]
  have hF₂H : F₂ ⊆ Hbar := by
    rintro _ (⟨a, -, rfl⟩ | ⟨a, -, rfl⟩)
    exacts [hR.2.2.2.1 a, hL.2.2.2.1 a]
  have hF₁c : IsCompact F₁ := (isCompact_Icc.image hR.1).union (isCompact_Icc.image hL.1)
  have hF₂cl : IsClosed F₂ := (Supp9B.isClosed_image ⟨hR.1, hR.2.1, hR.2.2.2.1, hR.2.2.2.2⟩ isClosed_Ici).union
    (Supp9B.isClosed_image ⟨hL.1, hL.2.1, hL.2.2.2.1, hL.2.2.2.2⟩ isClosed_Ici)
  have hF₁₂ : F₁ ∩ F₂ ⊆ {αR m} := by
    rintro w ⟨hw1, hw2⟩
    rcases hw1 with ⟨a, ha, rfl⟩ | ⟨a', ha', rfl⟩ <;> rcases hw2 with ⟨b, hb, hb'⟩ | ⟨b', hb', hb''⟩
    · have hab : b = a := hRi hb'
      have : a = m := le_antisymm ha.2 (hab ▸ hb)
      rw [this]; rfl
    · have hc := hord a m b' m' hb''.symm hX'
      rcases eq_or_lt_of_le ha.2 with h | h
      · rw [h]; rfl
      · exact absurd (hc.1 h) (not_lt.2 hb')
    · have hc := hord m b m' a' hX' hb'
      rcases eq_or_lt_of_le (mem_Ici.1 hb) with h | h
      · rw [← hb', ← h]; rfl
      · exact absurd (hc.1 h) (not_lt.2 ha'.2)
    · have hab : b' = a' := hLi hb''
      have : a' = m' := le_antisymm ha'.2 (hab ▸ hb')
      rw [this, ← hX']; rfl
  -- the configuration after `μ`
  set F₁' := mu '' F₁ with hF₁'
  set F₂' := mu '' F₂ ∪ {0} with hF₂'
  have hF₁'c : IsCompact F₁' := hF₁c.image_of_continuousOn (continuousOn_mu_Hbar.mono hF₁H)
  have hF₂'c : IsCompact F₂' := isCompact_mu_image_union_zero hF₂cl hF₂H
  have h0F₁' : (0 : ℂ) ∉ F₁' := by
    rintro ⟨z, hz, h⟩
    exact mu_ne_zero_of_mem_Hbar (hF₁H hz) h
  have hF₁₂' : F₁' ∩ F₂' ⊆ {mu (αR m)} := by
    rintro w ⟨⟨a, ha, rfl⟩, hw2⟩
    rcases hw2 with ⟨b, hb, he⟩ | h0
    · have hab : b = a := mu_injective he
      rw [mem_singleton_iff.1 (hF₁₂ ⟨ha, hab ▸ hb⟩)]
      rfl
    · exact absurd (mem_singleton_iff.1 h0) (mu_ne_zero_of_mem_Hbar (hF₁H ha))
  have hpre : IsPreconnected (F₁' ∩ F₂') := (subsingleton_singleton.anti hF₁₂').isPreconnected
  set C' := mu '' C with hC'
  have hC'o : IsOpen C' := isOpen_mu_image hCo hCH
  have hCH' : C ⊆ Hbar := fun z hz => mem_Hbar_of_mem_H (hCH hz)
  have hC'c : IsPreconnected C' := hCc.image _ (continuousOn_mu_Hbar.mono hCH')
  have hC'b : IsBounded C' := by
    refine (isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset ?_
    rintro _ ⟨z, hz, rfl⟩
    exact mem_closedBall_zero_iff.2 (norm_mu_le_one (hCH' hz))
  have hFsub : F₁ ∪ F₂ ⊆ range αR ∪ range αL := by
    rintro _ ((⟨a, -, rfl⟩ | ⟨a, -, rfl⟩) | (⟨a, -, rfl⟩ | ⟨a, -, rfl⟩))
    exacts [Or.inl ⟨a, rfl⟩, Or.inr ⟨a, rfl⟩, Or.inl ⟨a, rfl⟩, Or.inr ⟨a, rfl⟩]
  have hCF' : ∀ z ∈ C', z ∉ F₁' ∪ F₂' := by
    rintro _ ⟨c, hc, rfl⟩ ((⟨w, hw, he⟩) | (⟨w, hw, he⟩ | h0))
    · exact hCF c hc (hFsub (Or.inl (mu_injective he ▸ hw)))
    · exact hCF c hc (hFsub (Or.inr (mu_injective he ▸ hw)))
    · exact mu_ne_zero_of_mem_Hbar (hCH' hc) (mem_singleton_iff.1 h0)
  have hfr' : frontier C' ⊆ F₁' ∪ F₂' := by
    refine (frontier_mu_image_subset hCo hCH).trans ?_
    rintro _ (⟨z, hz, rfl⟩ | h0)
    · rcases hfr hz with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
      · rcases le_total a m with h | h
        · exact Or.inl ⟨αR a, Or.inl ⟨a, ⟨ha, h⟩, rfl⟩, rfl⟩
        · exact Or.inr (Or.inl ⟨αR a, Or.inl ⟨a, h, rfl⟩, rfl⟩)
      · rcases le_total a m' with h | h
        · exact Or.inl ⟨αL a, Or.inr ⟨a, ⟨ha, h⟩, rfl⟩, rfl⟩
        · exact Or.inr (Or.inl ⟨αL a, Or.inr ⟨a, h, rfl⟩, rfl⟩)
    · exact Or.inr (Or.inr h0)
  -- the entry `0 = μ(∞)` escapes down the negative imaginary axis, off `F₁'`
  have h0cl : (0 : ℂ) ∈ closure C' := by
    have hne : (cobounded ℂ ⊓ 𝓟 C).NeBot := by
      refine Filter.inf_principal_neBot_iff.2 fun U hU => ?_
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      have hUb : IsBounded Uᶜ := isBounded_def.2 (by rwa [compl_compl])
      refine hCu (hUb.subset fun z hz hzU => ?_)
      have : z ∈ U ∩ C := ⟨hzU, hz⟩
      rw [h] at this
      exact this
    exact mem_closure_of_tendsto (tendsto_mu_cobounded.mono_left inf_le_left)
      (eventually_inf_principal.2 (Eventually.of_forall fun z hz => mem_image_of_mem _ hz))
  have hSqF : ∀ z ∈ (fun u : ℝ => -((u : ℂ) * Complex.I)) '' Ici 0, z ∉ F₁' := by
    rintro _ ⟨u, hu, rfl⟩ ⟨w, hw, he⟩
    have he : mu w = -((u : ℂ) * Complex.I) := he
    rcases eq_or_lt_of_le (mem_Ici.1 hu) with h | h
    · rw [← h] at he
      exact mu_ne_zero_of_mem_Hbar (hF₁H hw) (by rw [he]; simp)
    · refine muInv_negImag_notMem_Hbar h ?_
      rw [← he, muInv_mu]
      exact hF₁H hw
  -- the exit escapes back along `μ ∘ α_R` to `μ(0) = i` and up the imaginary axis, off `F₂'`
  have h0F₂ : (0 : ℂ) ∉ F₂ := by
    rintro (⟨a, ha, he⟩ | ⟨a', ha', he⟩)
    · have : a = 0 := hRi (he.trans hR.2.2.1.symm)
      exact absurd (lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ s₁) (lt_of_lt_of_le hm1 (this ▸ ha)))
        (lt_irrefl 0)
    · have : a' = 0 := hLi (he.trans hL.2.2.1.symm)
      exact absurd (lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ t₁) (lt_of_lt_of_le hm'1 (this ▸ ha')))
        (lt_irrefl 0)
  set up := (fun u : ℝ => (u : ℂ) * Complex.I) '' Ici 1 with hup
  have hSpF : ∀ z ∈ mu '' (αR '' Icc 0 s₁) ∪ up, z ∉ F₂' := by
    rintro _ (⟨_, ⟨r, hr, rfl⟩, rfl⟩ | ⟨u, hu, rfl⟩) hzF
    · rcases hzF with ⟨w, hw, he⟩ | h0
      · have hw' : w = αR r := mu_injective he
        rw [hw'] at hw
        rcases hw with ⟨b, hb, he'⟩ | ⟨b', hb', he'⟩
        · have : b = r := hRi he'
          exact absurd (lt_of_le_of_lt hr.2 (lt_of_lt_of_le hm1 (this ▸ hb))) (lt_irrefl _)
        · exact absurd ((hord r m b' m' he'.symm hX').1 (lt_of_le_of_lt hr.2 hm1)) (not_lt.2 hb')
      · exact mu_ne_zero_of_mem_Hbar (hR.2.2.2.1 r) (mem_singleton_iff.1 h0)
    · rcases hzF with ⟨w, hw, he⟩ | h0
      · have he : mu w = (u : ℂ) * Complex.I := he
        rcases eq_or_lt_of_le (mem_Ici.1 hu) with h | h
        · have : w = 0 := by rw [← muInv_mu w, he, ← h]; simpa using muInv_I
          exact h0F₂ (this ▸ hw)
        · refine muInv_posImag_notMem_Hbar h ?_
          rw [← he, muInv_mu]
          exact hF₂H hw
      · have h0' := mem_singleton_iff.1 h0
        have hu1 : (1 : ℝ) ≤ u := hu
        have : (u : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 (by linarith)) Complex.I_ne_zero
        exact this h0'
  have hSp : IsPreconnected (mu '' (αR '' Icc 0 s₁) ∪ up) := by
    refine IsPreconnected.union Complex.I ⟨αR 0, ⟨0, left_mem_Icc.2 (zero_le : (0 : ℝ≥0) ≤ s₁), rfl⟩,
      by rw [hR.2.2.1, mu_zero]⟩ ⟨1, mem_Ici.2 le_rfl, by simp⟩ ?_ (isPreconnected_Ici.image _ (by fun_prop))
    exact (isPreconnected_Icc.image _ hR.1.continuousOn).image _
      (continuousOn_mu_Hbar.mono fun _ ⟨r, _, he⟩ => he ▸ hR.2.2.2.1 r)
  have hupu : ¬ IsBounded up := by
    intro hb
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hb
    have h := hM _ ⟨|M| + 1, mem_Ici.2 (le_add_of_nonneg_left (abs_nonneg M)), rfl⟩
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)] at h
    linarith [le_abs_self M]
  have hPcl : mu (αR s₁) ∈ closure C' :=
    (continuousAt_mu fun h => neg_I_notMem_Hbar (h ▸ hR.2.2.2.1 s₁)).continuousWithinAt.mem_closure_image hP
  have hPmem : mu (αR s₁) ∈ mu '' (αR '' Icc 0 s₁) ∪ up :=
    Or.inl ⟨αR s₁, ⟨s₁, ⟨zero_le, le_rfl⟩, rfl⟩, rfl⟩
  exact false_of_escaping_ends hF₁'c hF₂'c hpre hC'o hC'c hC'b (mem_image_of_mem mu hy) hCF' hfr' h0cl h0F₁'
    isPreconnected_negImagRay ⟨0, mem_Ici.2 le_rfl, by simp⟩ hSqF not_isBounded_negImagRay
    hPcl (hSpF _ hPmem) hSp hPmem hSpF (fun hb => hupu (hb.subset subset_union_right))

end Walls

end GB11Chart

end Theorem14

end InteractingSLE
