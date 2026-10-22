import HigherDimLQGMetric.DGZ.LengthIn

/-!
# Crossings of shells, across distances, exits from open sets (packet L3b1)

Source: MA7 (`planning/audits/MA7-ref2-sections-4-6.md`) §5 row L3b1 and Details (a): D-4.6
("`acrossDist` (minimizing paths can be taken inside the closed shell `K`)"), D-4.8 ("minimizing
paths for the across distance can be taken in the closed shell"), D-4.10, D-5.11 ("it contains a
crossing of `A′_z` and `across(x_z) ≤ ℓ_{A′_z}(γ′)`"), D-5.12 (d), D-5.14 (iii), D-6.4, D-6.7,
D-6.9 (μ3) and D-ADP (Euclidean spheres).

**Shell configurations.** `IsShellPair F₂ G₂ F₁ G₁`: closed `F₂, F₁`, open `G₂, G₁` with
`G₂ ⊆ F₂ ⊆ G₁ ⊆ F₁`; inner sphere `F₂ \ G₂`, outer sphere `F₁ \ G₁`, closed shell `F₁ \ G₂`.
Instances: `ℓ^∞` boxes (`isShellPair_box`: `cbox c r₂ ⊆ obox c r₁`, spheres `lsph`) and Euclidean
balls (`isShellPair_ball`, spheres `Metric.sphere`).

* `IsShellPair.exists_crossing_of_le`, `IsShellPair.exists_crossing`: a path continuous on `[0,1]`
  from `F₂` to the complement of `G₁` contains a sub-crossing `[u, v]` of the closed shell from one
  sphere to the other (first exit from `G₁`, then last visit of `F₂`);
* `IsShellPair.lfppSetDist_le_integral`, `IsShellPair.lfppSetDist_le_lfppLengthIn`,
  `IsShellPair.lfppSetDist_le_lfppDistOn`: the sphere-to-sphere distance (in any domain containing
  the closed shell) is at most the length of the sub-crossing;
* `IsShellPair.lfppSetDist_le_mul_of_exp_le`: **the across distance only sees the field on the
  closed shell** (field comparison on `F₁ \ G₂`).

**Across distances** (`ℓ^∞` shells, `r₂ < r₁`): **`acrossDist_le_of_crossing`** (target:
`across ≤ len(γ|_{closed shell})` for every path from `cbox c r₂` to the complement of
`obox c r₁`), `acrossDist_le_integral`, `acrossDist_le_lfppLength_of_crossing`,
`acrossDist_le_lfppDistOn`, `IsShellCrossing.acrossDist_le`; field comparison
`acrossDist_le_mul_of_exp_le`, `acrossDist_le_exp_mul`, `abs_log_acrossDist_sub_le`,
`acrossDist_mono_field`, `acrossDist_congr`; bounds `exp_mul_le_acrossDist`, `acrossDist_pos`,
`acrossDist_le_exp_mul_sub`. Euclidean spheres: `lfppSetDist_sphere_le_lfppDistOn`,
`lfppSetDist_sphere_le_mul_of_exp_le`, `abs_log_lfppSetDist_sphere_sub_le`.

**Set distances in a fixed domain**: `lfppSetDist_le_mul_of_exp_le`, `lfppSetDist_le_exp_mul`,
`abs_log_lfppSetDist_sub_le`, `lfppSetDist_mono_field`, `lfppSetDist_congr`.

**Exits from open sets** (MA7 D-6.9 (μ3), prelimit): `exists_last_exit`,
**`lfppMetric_ge_min`** (target: `D(x, A) ≥ min(D(x, A; U), D(∂U, A))` for `x ∈ U ⊇ A`),
`lfppSetDist_frontier_le` (`x ∉ U`), and the collar bound `lfppSetDist_level_le`
(`D(∂U, A) ≥ D({g = ρ} ∩ U, A; U)` for a continuous `g ≤ 0` off `U`, `g ≥ ρ > 0` on `A`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ}

/-! ## Two helpers: lower bounds with a multiplicative constant -/

section Helpers

variable {ξ : ℝ} {φ ψ : Rd d → ℝ} {V A B : Set (Rd d)} {x y : Rd d}

/-- If `a ≤ C · len_ψ(γ)` for every path from `x` to `y` in `V` (`C ≥ 0`), then
`a ≤ C · D_V(x, y)(ψ)`. -/
theorem le_mul_lfppDistOn_of_forall (hj : PcwJoined V x y) {a C : ℝ} (hC : 0 ≤ C)
    (h : ∀ γ : ℝ → Rd d, IsPcwC1Path γ x y → MapsTo γ (Icc 0 1) V →
      a ≤ C * lfppLength ξ ψ γ) :
    a ≤ C * lfppDistOn ξ ψ V x y := by
  rcases hC.lt_or_eq with hC' | hC'
  · rw [← div_le_iff₀' hC']
    exact le_lfppDistOn hj fun γ hγ hV => by
      rw [div_le_iff₀' hC']
      exact h γ hγ hV
  · obtain ⟨γ, hγ, hV⟩ := hj
    have := h γ hγ hV
    rw [← hC', zero_mul] at this ⊢
    exact this

/-- If `a ≤ C · D_V(x, y)(ψ)` for all `x ∈ A`, `y ∈ B` (nonempty, `C ≥ 0`), then
`a ≤ C · D(A, B; V)(ψ)`. -/
theorem le_mul_lfppSetDist_of_forall (hA : A.Nonempty) (hB : B.Nonempty) {a C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ A, ∀ y ∈ B, a ≤ C * lfppDistOn ξ ψ V x y) :
    a ≤ C * lfppSetDist ξ ψ V A B := by
  rcases hC.lt_or_eq with hC' | hC'
  · rw [← div_le_iff₀' hC']
    exact le_lfppSetDist hA hB fun x hx y hy => by
      rw [div_le_iff₀' hC']
      exact h x hx y hy
  · obtain ⟨x, hx⟩ := hA
    obtain ⟨y, hy⟩ := hB
    have := h x hx y hy
    rw [← hC', zero_mul] at this ⊢
    exact this

/-- An empty side makes the set distance vanish. -/
theorem lfppSetDist_of_not_nonempty (h : ¬ (A.Nonempty ∧ B.Nonempty)) :
    lfppSetDist ξ φ V A B = 0 := by
  have he : A ×ˢ B = ∅ := by
    by_contra hne
    have hne' := nonempty_iff_ne_empty.2 hne
    exact h ⟨hne'.fst, hne'.snd⟩
  rw [lfppSetDist, he, image_empty, Real.sInf_empty]

end Helpers

/-! ## Set distances in a fixed domain: field comparison -/

section SetDistField

variable {ξ : ℝ} {φ ψ : Rd d → ℝ} {V A B : Set (Rd d)}

/-- **Field comparison for set distances**: if `e^{ξ φ} ≤ C e^{ξ ψ}` on `V` (`C ≥ 0`), then
`D(A, B; V)(φ) ≤ C D(A, B; V)(ψ)`. -/
theorem lfppSetDist_le_mul_of_exp_le (hφ : Continuous φ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ z ∈ V, Real.exp (ξ * φ z) ≤ C * Real.exp (ξ * ψ z)) :
    lfppSetDist ξ φ V A B ≤ C * lfppSetDist ξ ψ V A B := by
  by_cases hAB : A.Nonempty ∧ B.Nonempty
  · exact le_mul_lfppSetDist_of_forall hAB.1 hAB.2 hC fun x hx y hy =>
      (lfppSetDist_le hx hy).trans (lfppDistOn_le_mul_of_exp_le hφ hψ hC h)
  · rw [lfppSetDist_of_not_nonempty hAB, lfppSetDist_of_not_nonempty hAB, mul_zero]

theorem lfppSetDist_le_exp_mul (hφ : Continuous φ) (hψ : Continuous ψ) {M : ℝ}
    (hM : ∀ z ∈ V, |φ z - ψ z| ≤ M) :
    lfppSetDist ξ φ V A B ≤ Real.exp (|ξ| * M) * lfppSetDist ξ ψ V A B :=
  lfppSetDist_le_mul_of_exp_le hφ hψ (Real.exp_pos _).le fun z hz =>
    exp_mul_le_exp_abs_mul (hM z hz)

/-- **Log-Lipschitz bound for set distances** (MA7 D-4.6): if `|φ - ψ| ≤ M` on `V` (`M ≥ 0`), then
`|log D(A, B; V)(φ) - log D(A, B; V)(ψ)| ≤ |ξ| M`. -/
theorem abs_log_lfppSetDist_sub_le (hφ : Continuous φ) (hψ : Continuous ψ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ V, |φ z - ψ z| ≤ M) :
    |Real.log (lfppSetDist ξ φ V A B) - Real.log (lfppSetDist ξ ψ V A B)| ≤ |ξ| * M :=
  abs_log_sub_le_of_le_exp_mul (lfppSetDist_nonneg ξ φ V A B) (lfppSetDist_nonneg ξ ψ V A B)
    (mul_nonneg (abs_nonneg ξ) hM0) (lfppSetDist_le_exp_mul hφ hψ hM)
    (lfppSetDist_le_exp_mul hψ hφ fun z hz => by rw [abs_sub_comm]; exact hM z hz)

/-- **Monotonicity in the field** (`ξ ≥ 0`). -/
theorem lfppSetDist_mono_field (hξ : 0 ≤ ξ) (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : ∀ z ∈ V, φ z ≤ ψ z) : lfppSetDist ξ φ V A B ≤ lfppSetDist ξ ψ V A B := by
  have := lfppSetDist_le_mul_of_exp_le (ξ := ξ) (V := V) (A := A) (B := B) hφ hψ zero_le_one
    fun z hz => by
      rw [one_mul, Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left (h z hz) hξ
  rwa [one_mul] at this

/-- **Locality**: `D(A, B; V)` only depends on the field on `V`. -/
theorem lfppSetDist_congr (h : ∀ z ∈ V, φ z = ψ z) :
    lfppSetDist ξ φ V A B = lfppSetDist ξ ψ V A B := by
  unfold lfppSetDist
  congr 1
  exact image_congr fun p _ => HigherDimLFPP.DGZ.lfppDistOn_congr h p.1 p.2

end SetDistField

/-! ## Sub-paths -/

section SubPaths

variable {ξ : ℝ} {φ : Rd d → ℝ} {γ : ℝ → Rd d} {x y : Rd d} {W : Set (Rd d)}

/-- The sub-path of `γ` on `[u, v] ⊆ [0,1]` bounds the internal distance between its endpoints in any
domain containing it. -/
theorem lfppDistOn_le_integral (hγ : IsPcwC1Path γ x y) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hv : v ≤ 1) (hW : ∀ t ∈ Icc u v, γ t ∈ W) :
    lfppDistOn ξ φ W (γ u) (γ v) ≤ ∫ t in u..v, lfppIntegrand ξ φ γ t := by
  rw [← lfppLength_subPath ξ φ γ huv]
  exact lfppDistOn_le_lfppLength (hγ.subPath hu huv hv) fun s hs => hW _ (affine_mem_Icc huv hs)

/-- The integral over a parameter sub-interval is at most the length. -/
theorem integral_le_lfppLength (hφ : Continuous φ) (hγ : IsPcwC1Path γ x y) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    ∫ t in u..v, lfppIntegrand ξ φ γ t ≤ lfppLength ξ φ γ := by
  have h := integral_le_lfppLengthIn (ξ := ξ) (S := univ) hφ hγ hu huv hv fun _ _ => mem_univ _
  rwa [lfppLengthIn_univ] at h

end SubPaths

/-! ## Shell configurations and sub-crossings -/

/-- A *shell configuration*: closed sets `F₂, F₁` and open sets `G₂, G₁` with
`G₂ ⊆ F₂ ⊆ G₁ ⊆ F₁`. The inner sphere is `F₂ \ G₂`, the outer sphere `F₁ \ G₁`, the closed shell
`F₁ \ G₂`. -/
structure IsShellPair (F₂ G₂ F₁ G₁ : Set (Rd d)) : Prop where
  isClosed_inner : IsClosed F₂
  isOpen_inner : IsOpen G₂
  isClosed_outer : IsClosed F₁
  isOpen_outer : IsOpen G₁
  inner_subset : G₂ ⊆ F₂
  inner_subset_outer : F₂ ⊆ G₁
  outer_subset : G₁ ⊆ F₁

/-- `ℓ^∞` boxes: `cbox c r₂ ⊆ obox c r₁` for `r₂ < r₁`; spheres `lsph c r₂`, `lsph c r₁`. -/
theorem isShellPair_box (c : Rd d) {r₁ r₂ : ℝ} (hr : r₂ < r₁) :
    IsShellPair (cbox c r₂) (obox c r₂) (cbox c r₁) (obox c r₁) :=
  ⟨HigherDimLFPP.DGZ.isClosed_cbox c r₂, HigherDimLFPP.DGZ.isOpen_obox c r₂,
    HigherDimLFPP.DGZ.isClosed_cbox c r₁, HigherDimLFPP.DGZ.isOpen_obox c r₁,
    HigherDimLFPP.DGZ.obox_subset_cbox c r₂, cbox_subset_obox hr,
    HigherDimLFPP.DGZ.obox_subset_cbox c r₁⟩

/-- Euclidean balls: `closedBall c r₂ ⊆ ball c r₁` for `r₂ < r₁`; spheres `Metric.sphere`. -/
theorem isShellPair_ball (c : Rd d) {r₁ r₂ : ℝ} (hr : r₂ < r₁) :
    IsShellPair (Metric.closedBall c r₂) (Metric.ball c r₂) (Metric.closedBall c r₁)
      (Metric.ball c r₁) :=
  ⟨Metric.isClosed_closedBall, Metric.isOpen_ball, Metric.isClosed_closedBall, Metric.isOpen_ball,
    Metric.ball_subset_closedBall, Metric.closedBall_subset_ball hr, Metric.ball_subset_closedBall⟩

namespace IsShellPair

variable {F₂ G₂ F₁ G₁ : Set (Rd d)}

/-- **Sub-crossing on `[a, b]`**: if `γ` is continuous on `[a, b]`, `γ a ∈ F₂` and `γ b ∉ G₁`, then
for the first exit time `t₁` from `G₁` and the last visit `t₀ ≤ t₁` of `F₂`, `γ t₀` lies on the
inner sphere, `γ t₁` on the outer sphere, `γ [t₀, t₁]` in the closed shell and `γ (t₀, t₁)` in
`G₁ \ F₂`. -/
theorem exists_crossing_of_le (hsh : IsShellPair F₂ G₂ F₁ G₁) {γ : ℝ → Rd d} {a b : ℝ}
    (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b)) (ha : γ a ∈ F₂) (hb : γ b ∉ G₁) :
    ∃ t₀ t₁, a ≤ t₀ ∧ t₀ < t₁ ∧ t₁ ≤ b ∧ γ t₀ ∈ F₂ \ G₂ ∧ γ t₁ ∈ F₁ \ G₁ ∧
      (∀ t ∈ Icc t₀ t₁, γ t ∈ F₁ \ G₂) ∧ (∀ t ∈ Ioo t₀ t₁, γ t ∈ G₁ \ F₂) := by
  -- the first exit time `t₁` from `G₁`
  set S₁ : Set ℝ := Icc a b ∩ γ ⁻¹' G₁ᶜ with hS₁
  have hS₁c : IsClosed S₁ :=
    hγ.preimage_isClosed_of_isClosed isClosed_Icc hsh.isOpen_outer.isClosed_compl
  have hbS₁ : b ∈ S₁ := ⟨⟨hab, le_rfl⟩, hb⟩
  have hS₁b : BddBelow S₁ := ⟨a, fun t ht => ht.1.1⟩
  set t₁ := sInf S₁ with ht₁
  have ht₁S : t₁ ∈ S₁ := hS₁c.csInf_mem ⟨b, hbS₁⟩ hS₁b
  have hat₁ : a ≤ t₁ := ht₁S.1.1
  have ht₁b : t₁ ≤ b := ht₁S.1.2
  have hbefore : ∀ t ∈ Ico a t₁, γ t ∈ G₁ := by
    intro t ht
    by_contra hcon
    have htS : t ∈ S₁ := ⟨⟨ht.1, ht.2.le.trans ht₁b⟩, hcon⟩
    exact absurd (csInf_le hS₁b htS) (not_le.2 ht.2)
  have hat₁' : a < t₁ := by
    rcases hat₁.lt_or_eq with h | h
    · exact h
    · exfalso
      have h' := ht₁S.2
      rw [← h] at h'
      exact h' (hsh.inner_subset_outer ha)
  have ht₁F₁ : γ t₁ ∈ F₁ := by
    have hcw : ContinuousWithinAt γ (Ico a t₁) t₁ :=
      (hγ t₁ ⟨hat₁, ht₁b⟩).mono (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht₁b))
    have hmem := hcw.mem_closure_image (by rw [closure_Ico hat₁'.ne]; exact right_mem_Icc.2 hat₁)
    have hsub : γ '' Ico a t₁ ⊆ F₁ := by
      rintro _ ⟨u, hu, rfl⟩
      exact hsh.outer_subset (hbefore u hu)
    exact (hsh.isClosed_outer.closure_subset_iff.2 hsub) hmem
  -- the last visit `t₀ ≤ t₁` of `F₂`
  set S₀ : Set ℝ := Icc a t₁ ∩ γ ⁻¹' F₂ with hS₀
  have hS₀c : IsClosed S₀ :=
    (hγ.mono (Icc_subset_Icc le_rfl ht₁b)).preimage_isClosed_of_isClosed isClosed_Icc
      hsh.isClosed_inner
  have haS₀ : a ∈ S₀ := ⟨⟨le_rfl, hat₁⟩, ha⟩
  have hS₀b : BddAbove S₀ := ⟨t₁, fun t ht => ht.1.2⟩
  set t₀ := sSup S₀ with ht₀
  have ht₀S : t₀ ∈ S₀ := hS₀c.csSup_mem ⟨a, haS₀⟩ hS₀b
  have hat₀ : a ≤ t₀ := le_csSup hS₀b haS₀
  have ht₀t₁ : t₀ < t₁ := by
    rcases ht₀S.1.2.lt_or_eq with h | h
    · exact h
    · exfalso
      have h' := ht₀S.2
      rw [mem_preimage, h] at h'
      exact ht₁S.2 (hsh.inner_subset_outer h')
  have hafter : ∀ t ∈ Ioc t₀ t₁, γ t ∉ F₂ := by
    intro t ht hF
    have htS : t ∈ S₀ := ⟨⟨hat₀.trans ht.1.le, ht.2⟩, hF⟩
    exact absurd (le_csSup hS₀b htS) (not_le.2 ht.1)
  have ht₀G₂ : γ t₀ ∉ G₂ := by
    have hcw : ContinuousWithinAt γ (Ioc t₀ t₁) t₀ :=
      (hγ t₀ ⟨hat₀, ht₀t₁.le.trans ht₁b⟩).mono fun t ht =>
        ⟨hat₀.trans ht.1.le, ht.2.trans ht₁b⟩
    have hmem := hcw.mem_closure_image (by rw [closure_Ioc ht₀t₁.ne]; exact left_mem_Icc.2 ht₀t₁.le)
    have hsub : γ '' Ioc t₀ t₁ ⊆ G₂ᶜ := by
      rintro _ ⟨u, hu, rfl⟩
      exact fun h => hafter u hu (hsh.inner_subset h)
    exact (hsh.isOpen_inner.isClosed_compl.closure_subset_iff.2 hsub) hmem
  refine ⟨t₀, t₁, hat₀, ht₀t₁, ht₁b, ⟨ht₀S.2, ht₀G₂⟩, ⟨ht₁F₁, ht₁S.2⟩, fun t ht => ⟨?_, ?_⟩,
    fun t ht => ⟨hbefore t ⟨hat₀.trans ht.1.le, ht.2⟩, hafter t ⟨ht.1, ht.2.le⟩⟩⟩
  · rcases ht.2.lt_or_eq with h | h
    · exact hsh.outer_subset (hbefore t ⟨hat₀.trans ht.1, h⟩)
    · rw [h]
      exact ht₁F₁
  · rcases ht.1.lt_or_eq with h | h
    · exact fun hG => hafter t ⟨h, ht.2⟩ (hsh.inner_subset hG)
    · rw [← h]
      exact ht₀G₂

/-- **Sub-crossing, both orientations**: if `γ` is continuous on `[0,1]`, `γ a ∈ F₂` and
`γ b ∉ G₁` (`a, b ∈ [0,1]`), there are `u < v` between `a` and `b` such that `γ [u, v]` lies in the
closed shell, `γ (u, v)` in `G₁ \ F₂`, and the endpoints lie on the two spheres. -/
theorem exists_crossing (hsh : IsShellPair F₂ G₂ F₁ G₁) {γ : ℝ → Rd d}
    (hγ : ContinuousOn γ (Icc 0 1)) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hin : γ a ∈ F₂) (hout : γ b ∉ G₁) :
    ∃ u v, min a b ≤ u ∧ u < v ∧ v ≤ max a b ∧ (∀ t ∈ Icc u v, γ t ∈ F₁ \ G₂) ∧
      (∀ t ∈ Ioo u v, γ t ∈ G₁ \ F₂) ∧
      ((γ u ∈ F₂ \ G₂ ∧ γ v ∈ F₁ \ G₁) ∨ (γ u ∈ F₁ \ G₁ ∧ γ v ∈ F₂ \ G₂)) := by
  rcases le_total a b with hab | hba
  · obtain ⟨t₀, t₁, h₀, h₀₁, h₁, hs₀, hs₁, hsh', hin'⟩ := hsh.exists_crossing_of_le hab
      (hγ.mono (Icc_subset_Icc ha.1 hb.2)) hin hout
    exact ⟨t₀, t₁, (min_le_left a b).trans h₀, h₀₁, h₁.trans (le_max_right a b), hsh', hin',
      Or.inl ⟨hs₀, hs₁⟩⟩
  · -- reverse time
    set γ' : ℝ → Rd d := fun t => γ (-t) with hγ'
    have hγ'c : ContinuousOn γ' (Icc (-a) (-b)) :=
      hγ.comp continuous_neg.continuousOn fun t ht =>
        ⟨by linarith [ht.2, hb.1], by linarith [ht.1, ha.2]⟩
    obtain ⟨t₀, t₁, h₀, h₀₁, h₁, hs₀, hs₁, hsh', hin'⟩ := hsh.exists_crossing_of_le
      (neg_le_neg hba) hγ'c (by simpa only [hγ', neg_neg] using hin)
      (by simpa only [hγ', neg_neg] using hout)
    refine ⟨-t₁, -t₀, ?_, neg_lt_neg h₀₁, ?_, fun t ht => ?_, fun t ht => ?_, Or.inr ⟨?_, ?_⟩⟩
    · rw [min_eq_right hba]; linarith
    · rw [max_eq_left hba]; linarith
    · have := hsh' (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
      simpa only [hγ', neg_neg] using this
    · have := hin' (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
      simpa only [hγ', neg_neg] using this
    · simpa only [hγ', neg_neg] using hs₁
    · simpa only [hγ', neg_neg] using hs₀

/-- **Sub-crossing on `[a, b]`, reverse orientation**: if `γ a ∉ G₁` and `γ b ∈ F₂`, there are
`a ≤ t₀ < t₁ ≤ b` with `γ t₀` on the outer sphere, `γ t₁` on the inner sphere, `γ [t₀, t₁]` in the
closed shell and `γ (t₀, t₁)` in `G₁ \ F₂`. -/
theorem exists_crossing_of_le_rev (hsh : IsShellPair F₂ G₂ F₁ G₁) {γ : ℝ → Rd d} {a b : ℝ}
    (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b)) (ha : γ a ∉ G₁) (hb : γ b ∈ F₂) :
    ∃ t₀ t₁, a ≤ t₀ ∧ t₀ < t₁ ∧ t₁ ≤ b ∧ γ t₀ ∈ F₁ \ G₁ ∧ γ t₁ ∈ F₂ \ G₂ ∧
      (∀ t ∈ Icc t₀ t₁, γ t ∈ F₁ \ G₂) ∧ (∀ t ∈ Ioo t₀ t₁, γ t ∈ G₁ \ F₂) := by
  set γ' : ℝ → Rd d := fun t => γ (-t) with hγ'
  have hγ'c : ContinuousOn γ' (Icc (-b) (-a)) :=
    hγ.comp continuous_neg.continuousOn fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
  obtain ⟨s₀, s₁, h₀, h₀₁, h₁, hs₀, hs₁, hsh', hin'⟩ := hsh.exists_crossing_of_le
    (neg_le_neg hab) hγ'c (by simpa only [hγ', neg_neg] using hb)
    (by simpa only [hγ', neg_neg] using ha)
  refine ⟨-s₁, -s₀, by linarith, neg_lt_neg h₀₁, by linarith, ?_, ?_, fun t ht => ?_,
    fun t ht => ?_⟩
  · simpa only [hγ', neg_neg] using hs₁
  · simpa only [hγ', neg_neg] using hs₀
  · have := hsh' (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa only [hγ', neg_neg] using this
  · have := hin' (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa only [hγ', neg_neg] using this

variable {ξ : ℝ} {φ ψ : Rd d → ℝ} {V W : Set (Rd d)} {γ : ℝ → Rd d} {x y : Rd d}

/-- **Crossing bound, interval form**: if `γ` goes, on the parameter interval `[a, b]`, from `F₂`
to the complement of `G₁` (either orientation), the sphere-to-sphere distance in any domain
containing the closed shell is at most `∫_a^b e^{ξ φ(γ)} |γ'|`. -/
theorem lfppSetDist_le_integral (hsh : IsShellPair F₂ G₂ F₁ G₁) (hφ : Continuous φ)
    (hV : F₁ \ G₂ ⊆ V) (hγ : IsPcwC1Path γ x y) {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hb1 : b ≤ 1) (h : (γ a ∈ F₂ ∧ γ b ∉ G₁) ∨ (γ b ∈ F₂ ∧ γ a ∉ G₁)) :
    lfppSetDist ξ φ V (F₂ \ G₂) (F₁ \ G₁) ≤ ∫ t in a..b, lfppIntegrand ξ φ γ t := by
  have ha : a ∈ Icc (0 : ℝ) 1 := ⟨ha0, hab.trans hb1⟩
  have hb : b ∈ Icc (0 : ℝ) 1 := ⟨ha0.trans hab, hb1⟩
  have key : ∀ a' b', a' ∈ Icc (0 : ℝ) 1 → b' ∈ Icc (0 : ℝ) 1 → γ a' ∈ F₂ → γ b' ∉ G₁ →
      min a' b' = a → max a' b' = b →
      lfppSetDist ξ φ V (F₂ \ G₂) (F₁ \ G₁) ≤ ∫ t in a..b, lfppIntegrand ξ φ γ t := by
    intro a' b' ha' hb' hin hout hmin hmax
    obtain ⟨u, v, hu, huv, hv, hshell, -, hends⟩ :=
      hsh.exists_crossing hγ.continuousOn ha' hb' hin hout
    rw [hmin] at hu
    rw [hmax] at hv
    have hu0 : 0 ≤ u := ha0.trans hu
    have hv1 : v ≤ 1 := hv.trans hb1
    have hD : lfppDistOn ξ φ V (γ u) (γ v) ≤ ∫ t in u..v, lfppIntegrand ξ φ γ t :=
      lfppDistOn_le_integral hγ hu0 huv.le hv1 fun t ht => hV (hshell t ht)
    have hI : ∫ t in u..v, lfppIntegrand ξ φ γ t ≤ ∫ t in a..b, lfppIntegrand ξ φ γ t :=
      intervalIntegral.integral_mono_interval hu huv.le hv
        (ae_of_all _ fun t => lfppIntegrand_nonneg ξ φ γ t)
        (intervalIntegrable_of_sub (hγ.intervalIntegrable_lfppIntegrand hφ ξ) ha0 hab hb1)
    rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact (lfppSetDist_le h₁ h₂).trans (hD.trans hI)
    · refine (lfppSetDist_le h₂ h₁).trans ?_
      rw [lfppDistOn_comm]
      exact hD.trans hI
  rcases h with ⟨hin, hout⟩ | ⟨hin, hout⟩
  · exact key a b ha hb hin hout (min_eq_left hab) (max_eq_right hab)
  · exact key b a hb ha hin hout (min_eq_right hab) (max_eq_left hab)

/-- **Crossing bound, restricted-length form**: if `γ` meets `F₂` and the complement of `G₁`, the
sphere-to-sphere distance in any domain containing the closed shell is at most the length of the
part of `γ` inside the closed shell. -/
theorem lfppSetDist_le_lfppLengthIn (hsh : IsShellPair F₂ G₂ F₁ G₁) (hφ : Continuous φ)
    (hV : F₁ \ G₂ ⊆ V) (hγ : IsPcwC1Path γ x y) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) (hin : γ a ∈ F₂) (hout : γ b ∉ G₁) :
    lfppSetDist ξ φ V (F₂ \ G₂) (F₁ \ G₁) ≤ lfppLengthIn ξ φ γ (F₁ \ G₂) := by
  obtain ⟨u, v, hu, huv, hv, hshell, -, hends⟩ := hsh.exists_crossing hγ.continuousOn ha hb hin hout
  have hu0 : 0 ≤ u := (le_min ha.1 hb.1).trans hu
  have hv1 : v ≤ 1 := hv.trans (max_le ha.2 hb.2)
  have hD : lfppDistOn ξ φ V (γ u) (γ v) ≤ ∫ t in u..v, lfppIntegrand ξ φ γ t :=
    lfppDistOn_le_integral hγ hu0 huv.le hv1 fun t ht => hV (hshell t ht)
  have hI := integral_le_lfppLengthIn (ξ := ξ) hφ hγ hu0 huv.le hv1 hshell
  rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact (lfppSetDist_le h₁ h₂).trans (hD.trans hI)
  · refine (lfppSetDist_le h₂ h₁).trans ?_
    rw [lfppDistOn_comm]
    exact hD.trans hI

/-- **Crossing bound, two-point form**: for `x ∈ F₂`, `y ∉ G₁` joined in some domain `W`, the
sphere-to-sphere distance in any domain containing the closed shell is at most `D_W(x, y)`. -/
theorem lfppSetDist_le_lfppDistOn (hsh : IsShellPair F₂ G₂ F₁ G₁) (hφ : Continuous φ)
    (hV : F₁ \ G₂ ⊆ V) (hx : x ∈ F₂) (hy : y ∉ G₁) (hj : PcwJoined W x y) :
    lfppSetDist ξ φ V (F₂ \ G₂) (F₁ \ G₁) ≤ lfppDistOn ξ φ W x y :=
  le_lfppDistOn hj fun γ hγ _ =>
    (hsh.lfppSetDist_le_lfppLengthIn hφ hV hγ (left_mem_Icc.2 zero_le_one)
      (right_mem_Icc.2 zero_le_one) (by rw [hγ.source]; exact hx)
      (by rw [hγ.target]; exact hy)).trans (lfppLengthIn_le_lfppLength hφ hγ)

/-- **The sphere-to-sphere distance only sees the field on the closed shell**: if
`e^{ξ φ} ≤ C e^{ξ ψ}` on `F₁ \ G₂` (`C ≥ 0`), then
`D(F₂ \ G₂, F₁ \ G₁)(φ) ≤ C D(F₂ \ G₂, F₁ \ G₁)(ψ)` (whole-space metric). -/
theorem lfppSetDist_le_mul_of_exp_le (hsh : IsShellPair F₂ G₂ F₁ G₁) (hφ : Continuous φ)
    (hψ : Continuous ψ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ z ∈ F₁ \ G₂, Real.exp (ξ * φ z) ≤ C * Real.exp (ξ * ψ z)) :
    lfppSetDist ξ φ univ (F₂ \ G₂) (F₁ \ G₁) ≤ C * lfppSetDist ξ ψ univ (F₂ \ G₂) (F₁ \ G₁) := by
  by_cases hAB : (F₂ \ G₂).Nonempty ∧ (F₁ \ G₁).Nonempty
  · refine le_mul_lfppSetDist_of_forall hAB.1 hAB.2 hC fun x hx y hy => ?_
    refine le_mul_lfppDistOn_of_forall (pcwJoined_univ x y) hC fun γ hγ _ => ?_
    obtain ⟨u, v, hu, huv, hv, hshell, -, hends⟩ := hsh.exists_crossing hγ.continuousOn
      (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
      (by rw [hγ.source]; exact hx.1) (by rw [hγ.target]; exact hy.2)
    rw [min_eq_left zero_le_one] at hu
    rw [max_eq_right zero_le_one] at hv
    have hD : lfppDistOn ξ φ univ (γ u) (γ v) ≤ ∫ t in u..v, lfppIntegrand ξ φ γ t :=
      lfppDistOn_le_integral hγ hu huv.le hv fun _ _ => mem_univ _
    have hcomp : ∫ t in u..v, lfppIntegrand ξ φ γ t ≤
        C * ∫ t in u..v, lfppIntegrand ξ ψ γ t := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on huv.le
        (intervalIntegrable_of_sub (hγ.intervalIntegrable_lfppIntegrand hφ ξ) hu huv.le hv)
        ((intervalIntegrable_of_sub (hγ.intervalIntegrable_lfppIntegrand hψ ξ) hu huv.le
          hv).const_mul C) fun t ht => ?_
      unfold lfppIntegrand
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (h _ (hshell t ht)) (norm_nonneg _)
    have hlen : C * ∫ t in u..v, lfppIntegrand ξ ψ γ t ≤ C * lfppLength ξ ψ γ :=
      mul_le_mul_of_nonneg_left (integral_le_lfppLength hψ hγ hu huv.le hv) hC
    rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact (lfppSetDist_le h₁ h₂).trans (hD.trans (hcomp.trans hlen))
    · refine (lfppSetDist_le h₂ h₁).trans ?_
      rw [lfppDistOn_comm]
      exact hD.trans (hcomp.trans hlen)
  · rw [lfppSetDist_of_not_nonempty hAB, lfppSetDist_of_not_nonempty hAB, mul_zero]

end IsShellPair

/-! ## Across distances of `ℓ^∞` shells -/

section Across

variable {ξ : ℝ} {φ ψ : Rd d → ℝ} {c : Rd d} {r₁ r₂ : ℝ} {V W B : Set (Rd d)} {γ : ℝ → Rd d}
  {x y : Rd d}

theorem acrossDist_eq (ξ : ℝ) (φ : Rd d → ℝ) (c : Rd d) (r₁ r₂ : ℝ) :
    acrossDist ξ φ c r₁ r₂ =
      lfppSetDist ξ φ univ (cbox c r₂ \ obox c r₂) (cbox c r₁ \ obox c r₁) := rfl

theorem acrossDist_nonneg (ξ : ℝ) (φ : Rd d → ℝ) (c : Rd d) (r₁ r₂ : ℝ) :
    0 ≤ acrossDist ξ φ c r₁ r₂ :=
  lfppSetDist_nonneg ξ φ univ _ _

/-- The across distance is at most the whole-space distance of any pair of points on the two
spheres. -/
theorem acrossDist_le_lfppMetric (hx : x ∈ lsph c r₂) (hy : y ∈ lsph c r₁) :
    acrossDist ξ φ c r₁ r₂ ≤ lfppMetric ξ φ x y :=
  lfppSetDist_le hx hy

/-- **Across bound for a crossing path** (MA7 §5 row L3b1, D-5.11, D-5.12): if a piecewise `C¹` path
`γ` meets the closed inner box `cbox c r₂` and the complement of the open outer box `obox c r₁`
(`r₂ < r₁`), then `D(across) ≤ len(γ|_{cbox c r₁ \ obox c r₂})`. -/
theorem acrossDist_le_of_crossing (hφ : Continuous φ) (hr : r₂ < r₁) (hγ : IsPcwC1Path γ x y)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hin : γ a ∈ cbox c r₂)
    (hout : γ b ∉ obox c r₁) :
    acrossDist ξ φ c r₁ r₂ ≤ lfppLengthIn ξ φ γ (cbox c r₁ \ obox c r₂) :=
  (isShellPair_box c hr).lfppSetDist_le_lfppLengthIn hφ (subset_univ _) hγ ha hb hin hout

/-- **Across bound, interval form**: if on the parameter interval `[a, b]` the path goes from
`cbox c r₂` to the complement of `obox c r₁` (either orientation), `D(across) ≤ ∫_a^b`. -/
theorem acrossDist_le_integral (hφ : Continuous φ) (hr : r₂ < r₁) (hγ : IsPcwC1Path γ x y)
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (h : (γ a ∈ cbox c r₂ ∧ γ b ∉ obox c r₁) ∨ (γ b ∈ cbox c r₂ ∧ γ a ∉ obox c r₁)) :
    acrossDist ξ φ c r₁ r₂ ≤ ∫ t in a..b, lfppIntegrand ξ φ γ t :=
  (isShellPair_box c hr).lfppSetDist_le_integral hφ (subset_univ _) hγ ha0 hab hb1 h

theorem acrossDist_le_lfppLength_of_crossing (hφ : Continuous φ) (hr : r₂ < r₁)
    (hγ : IsPcwC1Path γ x y) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hin : γ a ∈ cbox c r₂) (hout : γ b ∉ obox c r₁) :
    acrossDist ξ φ c r₁ r₂ ≤ lfppLength ξ φ γ :=
  (acrossDist_le_of_crossing hφ hr hγ ha hb hin hout).trans (lfppLengthIn_le_lfppLength hφ hγ)

/-- **Across bound, two-point form** (MA7 D-5.14 (iii), D-6.4, D-6.7): for `x ∈ cbox c r₂` and
`y ∉ obox c r₁` joined in `W`, `D(across) ≤ D_W(x, y)`. -/
theorem acrossDist_le_lfppDistOn (hφ : Continuous φ) (hr : r₂ < r₁) (hx : x ∈ cbox c r₂)
    (hy : y ∉ obox c r₁) (hj : PcwJoined W x y) : acrossDist ξ φ c r₁ r₂ ≤ lfppDistOn ξ φ W x y :=
  (isShellPair_box c hr).lfppSetDist_le_lfppDistOn hφ (subset_univ _) hx hy hj

theorem acrossDist_le_lfppMetric_of_mem (hφ : Continuous φ) (hr : r₂ < r₁) (hx : x ∈ cbox c r₂)
    (hy : y ∉ obox c r₁) : acrossDist ξ φ c r₁ r₂ ≤ lfppMetric ξ φ x y :=
  acrossDist_le_lfppDistOn hφ hr hx hy (pcwJoined_univ x y)

/-- **A shell crossing is at least the across distance.** -/
theorem IsShellCrossing.acrossDist_le (h : IsShellCrossing c r₁ r₂ B γ) :
    acrossDist ξ φ c r₁ r₂ ≤ lfppLength ξ φ γ :=
  (acrossDist_le_lfppMetric h.start h.stop).trans (lfppMetric_le_lfppLength h.pcw)

/-- **The across distance only sees the field on the closed shell** (MA7 D-4.6, D-4.8):
if `e^{ξ φ} ≤ C e^{ξ ψ}` on `cbox c r₁ \ obox c r₂` (`C ≥ 0`, `r₂ < r₁`), then
`D(across)(φ) ≤ C D(across)(ψ)`. -/
theorem acrossDist_le_mul_of_exp_le (hφ : Continuous φ) (hψ : Continuous ψ) (hr : r₂ < r₁)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ z ∈ cbox c r₁ \ obox c r₂, Real.exp (ξ * φ z) ≤ C * Real.exp (ξ * ψ z)) :
    acrossDist ξ φ c r₁ r₂ ≤ C * acrossDist ξ ψ c r₁ r₂ :=
  (isShellPair_box c hr).lfppSetDist_le_mul_of_exp_le hφ hψ hC h

theorem acrossDist_le_exp_mul (hφ : Continuous φ) (hψ : Continuous ψ) (hr : r₂ < r₁) {M : ℝ}
    (hM : ∀ z ∈ cbox c r₁ \ obox c r₂, |φ z - ψ z| ≤ M) :
    acrossDist ξ φ c r₁ r₂ ≤ Real.exp (|ξ| * M) * acrossDist ξ ψ c r₁ r₂ :=
  acrossDist_le_mul_of_exp_le hφ hψ hr (Real.exp_pos _).le fun z hz =>
    exp_mul_le_exp_abs_mul (hM z hz)

/-- **Log-Lipschitz bound for the across distance** (MA7 D-4.6): if `|φ - ψ| ≤ M` on the closed
shell (`M ≥ 0`, `r₂ < r₁`), then `|log across(φ) - log across(ψ)| ≤ |ξ| M`. -/
theorem abs_log_acrossDist_sub_le (hφ : Continuous φ) (hψ : Continuous ψ) (hr : r₂ < r₁)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z ∈ cbox c r₁ \ obox c r₂, |φ z - ψ z| ≤ M) :
    |Real.log (acrossDist ξ φ c r₁ r₂) - Real.log (acrossDist ξ ψ c r₁ r₂)| ≤ |ξ| * M :=
  abs_log_sub_le_of_le_exp_mul (acrossDist_nonneg ξ φ c r₁ r₂) (acrossDist_nonneg ξ ψ c r₁ r₂)
    (mul_nonneg (abs_nonneg ξ) hM0) (acrossDist_le_exp_mul hφ hψ hr hM)
    (acrossDist_le_exp_mul hψ hφ hr fun z hz => by rw [abs_sub_comm]; exact hM z hz)

/-- **Monotonicity in the field** (`ξ ≥ 0`). -/
theorem acrossDist_mono_field (hξ : 0 ≤ ξ) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hr : r₂ < r₁) (h : ∀ z ∈ cbox c r₁ \ obox c r₂, φ z ≤ ψ z) :
    acrossDist ξ φ c r₁ r₂ ≤ acrossDist ξ ψ c r₁ r₂ := by
  have := acrossDist_le_mul_of_exp_le (ξ := ξ) hφ hψ hr zero_le_one fun z hz => by
    rw [one_mul, Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left (h z hz) hξ
  rwa [one_mul] at this

/-- **Locality**: the across distance only depends on the field on the closed shell. -/
theorem acrossDist_congr (hφ : Continuous φ) (hψ : Continuous ψ) (hr : r₂ < r₁)
    (h : ∀ z ∈ cbox c r₁ \ obox c r₂, φ z = ψ z) :
    acrossDist ξ φ c r₁ r₂ = acrossDist ξ ψ c r₁ r₂ := by
  have h1 := acrossDist_le_mul_of_exp_le (ξ := ξ) hφ hψ hr zero_le_one fun z hz => by
    rw [one_mul, h z hz]
  have h2 := acrossDist_le_mul_of_exp_le (ξ := ξ) hψ hφ hr zero_le_one fun z hz => by
    rw [one_mul, h z hz]
  rw [one_mul] at h1 h2
  exact le_antisymm h1 h2

/-- The point `c + r e₁` lies on `lsph c r` (`d ≥ 1`, `r ≥ 0`). -/
theorem add_smul_e₁_mem_lsph (hd : 0 < d) (c : Rd d) {r : ℝ} (hr : 0 ≤ r) :
    c + r • e₁ d ∈ lsph c r := by
  refine ⟨fun i => ?_, fun h => ?_⟩
  · rw [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, add_sub_cancel_left, abs_mul,
      abs_of_nonneg hr, e₁_ofLp]
    split_ifs <;> norm_num [hr]
  · have h0 := h ⟨0, hd⟩
    rw [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, add_sub_cancel_left, abs_mul,
      abs_of_nonneg hr, e₁_ofLp] at h0
    simp at h0

/-- **Lower bound** (exit-time argument on the sub-crossing): if `ξ φ ≥ m` on the closed shell,
then `D(across) ≥ e^m (r₁ - r₂)` (`d ≥ 1`, `0 ≤ r₂ < r₁`). -/
theorem exp_mul_le_acrossDist (hd : 0 < d) (hφ : Continuous φ) (hr₂ : 0 ≤ r₂) (hr : r₂ < r₁)
    {m : ℝ} (hm : ∀ z ∈ cbox c r₁ \ obox c r₂, m ≤ ξ * φ z) :
    Real.exp m * (r₁ - r₂) ≤ acrossDist ξ φ c r₁ r₂ := by
  refine le_lfppSetDist ⟨_, add_smul_e₁_mem_lsph hd c hr₂⟩
    ⟨_, add_smul_e₁_mem_lsph hd c (hr₂.trans hr.le)⟩ fun x hx y hy => ?_
  refine le_lfppDistOn (pcwJoined_univ x y) fun γ hγ _ => ?_
  obtain ⟨u, v, hu, huv, hv, hshell, -, hends⟩ := (isShellPair_box c hr).exists_crossing
    hγ.continuousOn (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
    (by rw [hγ.source]; exact hx.1) (by rw [hγ.target]; exact hy.2)
  rw [min_eq_left zero_le_one] at hu
  rw [max_eq_right zero_le_one] at hv
  have hint := hγ.exp_mul_norm_sub_le_integral (ζ := ξ) hφ hu huv.le hv fun t ht => hm _ (hshell t ht)
  have hchord : r₁ - r₂ ≤ ‖γ v - γ u‖ := by
    -- the outer endpoint has a coordinate at distance `≥ r₁` from `c`, the inner one `≤ r₂`
    have hcoord : ∀ p q : Rd d, p ∈ lsph c r₁ → q ∈ lsph c r₂ → r₁ - r₂ ≤ ‖p - q‖ := by
      intro p q hp hq
      have hpo : ¬ ∀ i, |p i - c i| < r₁ := hp.2
      push Not at hpo
      obtain ⟨i, hi⟩ := hpo
      have hqi := hq.1 i
      have h1 : r₁ - r₂ ≤ |p i - q i| := by
        have := abs_sub_abs_le_abs_sub (p i - c i) (q i - c i)
        rw [sub_sub_sub_cancel_right] at this
        linarith
      have h2 := HigherDimLFPP.DGZ.abs_apply_le_norm (p - q) i
      rw [PiLp.sub_apply] at h2
      linarith
    rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact hcoord _ _ h₂ h₁
    · rw [norm_sub_rev]; exact hcoord _ _ h₁ h₂
  calc Real.exp m * (r₁ - r₂) ≤ Real.exp m * ‖γ v - γ u‖ :=
        mul_le_mul_of_nonneg_left hchord (Real.exp_pos m).le
    _ ≤ ∫ t in u..v, lfppIntegrand ξ φ γ t := hint
    _ ≤ lfppLength ξ φ γ := integral_le_lfppLength hφ hγ hu huv.le hv

/-- **Positivity of the across distance** (`d ≥ 1`, `0 ≤ r₂ < r₁`, continuous field). -/
theorem acrossDist_pos (hd : 0 < d) (hφ : Continuous φ) (hr₂ : 0 ≤ r₂) (hr : r₂ < r₁) :
    0 < acrossDist ξ φ c r₁ r₂ := by
  obtain ⟨m, hm⟩ := (isCompact_cbox c r₁).bddBelow_image (continuous_const.mul hφ).continuousOn
  exact (mul_pos (Real.exp_pos m) (sub_pos.2 hr)).trans_le
    (exp_mul_le_acrossDist hd hφ hr₂ hr fun z hz => hm ⟨z, hz.1, rfl⟩)

/-- **Upper bound** along the segment `[c + r₂ e₁, c + r₁ e₁]`: if `ξ φ ≤ M` on `cbox c r₁`, then
`D(across) ≤ e^M (r₁ - r₂)` (`d ≥ 1`, `0 ≤ r₂ ≤ r₁`). -/
theorem acrossDist_le_exp_mul_sub (hd : 0 < d) (hφ : Continuous φ) (hr₂ : 0 ≤ r₂) (hr : r₂ ≤ r₁)
    {M : ℝ} (hM : ∀ z ∈ cbox c r₁, ξ * φ z ≤ M) :
    acrossDist ξ φ c r₁ r₂ ≤ Real.exp M * (r₁ - r₂) := by
  have hx := add_smul_e₁_mem_lsph hd c hr₂
  have hy := add_smul_e₁_mem_lsph hd c (hr₂.trans hr)
  refine (acrossDist_le_lfppMetric hx hy).trans ?_
  have hseg : ∀ u ∈ Icc (0 : ℝ) 1, segPath (c + r₂ • e₁ d) (c + r₁ • e₁ d) u ∈ cbox c r₁ := by
    intro u hu i
    have e : segPath (c + r₂ • e₁ d) (c + r₁ • e₁ d) u = c + (r₂ + u * (r₁ - r₂)) • e₁ d := by
      simp only [segPath]
      rw [add_sub_add_left_eq_sub, ← sub_smul, smul_smul, add_assoc, ← add_smul]
    rw [e, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, add_sub_cancel_left, abs_mul, e₁_ofLp]
    have h0 : 0 ≤ r₂ + u * (r₁ - r₂) := by nlinarith [hu.1]
    have h1 : r₂ + u * (r₁ - r₂) ≤ r₁ := by nlinarith [hu.2]
    rw [abs_of_nonneg h0]
    split_ifs <;> norm_num <;> linarith
  have hb := lfppDistOn_le_of_segment (ζ := ξ) (V := univ) hφ (mapsTo_univ _ _)
    (B := Real.exp M) fun u hu => Real.exp_le_exp.2 (hM _ (hseg u hu))
  have hn : ‖c + r₁ • e₁ d - (c + r₂ • e₁ d)‖ = r₁ - r₂ := by
    rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, norm_e₁ hd, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.2 hr)]
  rw [hn] at hb
  exact hb

end Across

/-! ## Shell crossings as sub-paths (MA7 D-5.11) -/

section ShellCrossing

variable {c : Rd d} {r₁ r₂ : ℝ} {B : Set (Rd d)} {γ : ℝ → Rd d} {x y : Rd d}

/-- A sub-path from the inner sphere to the outer sphere, inside the closed shell and `B`, is a
shell crossing. -/
theorem isShellCrossing_subPath (hγ : IsPcwC1Path γ x y) {t₀ t₁ : ℝ} (h0 : 0 ≤ t₀)
    (h01 : t₀ ≤ t₁) (h1 : t₁ ≤ 1) (hs : γ t₀ ∈ lsph c r₂) (he : γ t₁ ∈ lsph c r₁)
    (hshell : ∀ t ∈ Icc t₀ t₁, γ t ∈ cbox c r₁ \ obox c r₂) (hB : ∀ t ∈ Icc t₀ t₁, γ t ∈ B) :
    IsShellCrossing c r₁ r₂ B (subPath γ t₀ t₁) where
  pcw := by
    rw [subPath_zero, subPath_one]
    exact hγ.subPath h0 h01 h1
  start := by rw [subPath_zero]; exact hs
  stop := by rw [subPath_one]; exact he
  inShell := fun _ hs' => hshell _ (affine_mem_Icc h01 hs')
  inB := fun _ hs' => hB _ (affine_mem_Icc h01 hs')

/-- A sub-path from the outer sphere to the inner sphere, inside the closed shell and `B`,
traversed backwards, is a shell crossing. -/
theorem isShellCrossing_revPath_subPath (hγ : IsPcwC1Path γ x y) {t₀ t₁ : ℝ} (h0 : 0 ≤ t₀)
    (h01 : t₀ ≤ t₁) (h1 : t₁ ≤ 1) (hs : γ t₀ ∈ lsph c r₁) (he : γ t₁ ∈ lsph c r₂)
    (hshell : ∀ t ∈ Icc t₀ t₁, γ t ∈ cbox c r₁ \ obox c r₂) (hB : ∀ t ∈ Icc t₀ t₁, γ t ∈ B) :
    IsShellCrossing c r₁ r₂ B (revPath (subPath γ t₀ t₁)) where
  pcw := by
    have e0 : revPath (subPath γ t₀ t₁) 0 = γ t₁ := by
      simp only [revPath, sub_zero, subPath_one]
    have e1 : revPath (subPath γ t₀ t₁) 1 = γ t₀ := by
      simp only [revPath, sub_self, subPath_zero]
    rw [e0, e1]
    exact (hγ.subPath h0 h01 h1).revPath
  start := by simp only [revPath, sub_zero, subPath_one]; exact he
  stop := by simp only [revPath, sub_self, subPath_zero]; exact hs
  inShell := mapsTo_revPath fun _ hs' => hshell _ (affine_mem_Icc h01 hs')
  inB := mapsTo_revPath fun _ hs' => hB _ (affine_mem_Icc h01 hs')

/-- **Existence of a shell crossing inside a path** (inner box at `a`, outside the outer box at
`b ≥ a`, the path in `B` on `[a, b]`). -/
theorem exists_isShellCrossing_subPath (hr : r₂ < r₁) (hγ : IsPcwC1Path γ x y) {a b : ℝ}
    (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) (hin : γ a ∈ cbox c r₂) (hout : γ b ∉ obox c r₁)
    (hB : ∀ t ∈ Icc a b, γ t ∈ B) :
    ∃ t₀ t₁, a ≤ t₀ ∧ t₀ < t₁ ∧ t₁ ≤ b ∧ IsShellCrossing c r₁ r₂ B (subPath γ t₀ t₁) := by
  obtain ⟨t₀, t₁, h₀, h₀₁, h₁, hs₀, hs₁, hshell, -⟩ := (isShellPair_box c hr).exists_crossing_of_le
    hab (hγ.continuousOn.mono (Icc_subset_Icc ha0 hb1)) hin hout
  exact ⟨t₀, t₁, h₀, h₀₁, h₁, isShellCrossing_subPath hγ (ha0.trans h₀) h₀₁.le (h₁.trans hb1)
    hs₀ hs₁ hshell fun t ht => hB t ⟨h₀.trans ht.1, ht.2.trans h₁⟩⟩

/-- **Existence of a shell crossing inside a path, reverse orientation** (outside the outer box at
`a`, inner box at `b ≥ a`, the path in `B` on `[a, b]`): the reversed sub-path is a crossing. -/
theorem exists_isShellCrossing_revPath (hr : r₂ < r₁) (hγ : IsPcwC1Path γ x y) {a b : ℝ}
    (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) (hout : γ a ∉ obox c r₁) (hin : γ b ∈ cbox c r₂)
    (hB : ∀ t ∈ Icc a b, γ t ∈ B) :
    ∃ t₀ t₁, a ≤ t₀ ∧ t₀ < t₁ ∧ t₁ ≤ b ∧
      IsShellCrossing c r₁ r₂ B (revPath (subPath γ t₀ t₁)) := by
  obtain ⟨t₀, t₁, h₀, h₀₁, h₁, hs₀, hs₁, hshell, -⟩ :=
    (isShellPair_box c hr).exists_crossing_of_le_rev hab
      (hγ.continuousOn.mono (Icc_subset_Icc ha0 hb1)) hout hin
  exact ⟨t₀, t₁, h₀, h₀₁, h₁, isShellCrossing_revPath_subPath hγ (ha0.trans h₀) h₀₁.le
    (h₁.trans hb1) hs₀ hs₁ hshell fun t ht => hB t ⟨h₀.trans ht.1, ht.2.trans h₁⟩⟩

end ShellCrossing

/-! ## Euclidean spheres (for the adapter D-ADP) -/

section Sphere

variable {ξ : ℝ} {φ ψ : Rd d → ℝ} {c x y : Rd d} {r₁ r₂ : ℝ} {W : Set (Rd d)}

theorem closedBall_sdiff_ball_eq (c : Rd d) (r : ℝ) :
    Metric.closedBall c r \ Metric.ball c r = Metric.sphere c r :=
  Metric.closedBall_sdiff_ball

/-- Euclidean crossing bound: for `x ∈ B̄(c, r₂)` and `y ∉ B(c, r₁)` joined in `W`,
`D(∂B(c, r₂), ∂B(c, r₁)) ≤ D_W(x, y)`. -/
theorem lfppSetDist_sphere_le_lfppDistOn (hφ : Continuous φ) (hr : r₂ < r₁)
    (hx : x ∈ Metric.closedBall c r₂) (hy : y ∉ Metric.ball c r₁) (hj : PcwJoined W x y) :
    lfppSetDist ξ φ univ (Metric.sphere c r₂) (Metric.sphere c r₁) ≤ lfppDistOn ξ φ W x y := by
  rw [← closedBall_sdiff_ball_eq c r₂, ← closedBall_sdiff_ball_eq c r₁]
  exact (isShellPair_ball c hr).lfppSetDist_le_lfppDistOn hφ (subset_univ _) hx hy hj

/-- The Euclidean sphere-to-sphere distance only sees the field on the closed Euclidean shell. -/
theorem lfppSetDist_sphere_le_mul_of_exp_le (hφ : Continuous φ) (hψ : Continuous ψ)
    (hr : r₂ < r₁) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ z ∈ Metric.closedBall c r₁ \ Metric.ball c r₂,
      Real.exp (ξ * φ z) ≤ C * Real.exp (ξ * ψ z)) :
    lfppSetDist ξ φ univ (Metric.sphere c r₂) (Metric.sphere c r₁) ≤
      C * lfppSetDist ξ ψ univ (Metric.sphere c r₂) (Metric.sphere c r₁) := by
  rw [← closedBall_sdiff_ball_eq c r₂, ← closedBall_sdiff_ball_eq c r₁]
  exact (isShellPair_ball c hr).lfppSetDist_le_mul_of_exp_le hφ hψ hC h

theorem abs_log_lfppSetDist_sphere_sub_le (hφ : Continuous φ) (hψ : Continuous ψ)
    (hr : r₂ < r₁) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ Metric.closedBall c r₁ \ Metric.ball c r₂, |φ z - ψ z| ≤ M) :
    |Real.log (lfppSetDist ξ φ univ (Metric.sphere c r₂) (Metric.sphere c r₁)) -
      Real.log (lfppSetDist ξ ψ univ (Metric.sphere c r₂) (Metric.sphere c r₁))| ≤ |ξ| * M :=
  abs_log_sub_le_of_le_exp_mul (lfppSetDist_nonneg _ _ _ _ _) (lfppSetDist_nonneg _ _ _ _ _)
    (mul_nonneg (abs_nonneg ξ) hM0)
    (lfppSetDist_sphere_le_mul_of_exp_le hφ hψ hr (Real.exp_pos _).le fun z hz =>
      exp_mul_le_exp_abs_mul (hM z hz))
    (lfppSetDist_sphere_le_mul_of_exp_le hψ hφ hr (Real.exp_pos _).le fun z hz =>
      exp_mul_le_exp_abs_mul (by rw [abs_sub_comm]; exact hM z hz))

end Sphere

/-! ## Exits from open sets (MA7 D-6.9 (μ3)) -/

section Exit

variable {ξ : ℝ} {φ : Rd d → ℝ} {U A F : Set (Rd d)} {x : Rd d}

/-- **Last exit**: if `γ` is continuous on `[0,1]`, `γ 1 ∈ U` (open) and `γ t₀ ∉ U`, then at the
last time `s ≥ t₀` outside `U`, `γ s ∈ ∂U`, and `γ (s, 1] ⊆ U`. -/
theorem exists_last_exit (hU : IsOpen U) {γ : ℝ → Rd d} (hγ : ContinuousOn γ (Icc 0 1))
    (h1 : γ 1 ∈ U) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (hout : γ t₀ ∉ U) :
    ∃ s, t₀ ≤ s ∧ s < 1 ∧ γ s ∈ frontier U ∧ ∀ t ∈ Ioc s 1, γ t ∈ U := by
  set S : Set ℝ := Icc t₀ 1 ∩ γ ⁻¹' Uᶜ with hS
  have hSc : IsClosed S :=
    (hγ.mono (Icc_subset_Icc ht₀.1 le_rfl)).preimage_isClosed_of_isClosed isClosed_Icc
      hU.isClosed_compl
  have ht₀S : t₀ ∈ S := ⟨⟨le_rfl, ht₀.2⟩, hout⟩
  have hSb : BddAbove S := ⟨1, fun t ht => ht.1.2⟩
  set s := sSup S with hs
  have hsS : s ∈ S := hSc.csSup_mem ⟨t₀, ht₀S⟩ hSb
  have hts : t₀ ≤ s := le_csSup hSb ht₀S
  have hs1 : s < 1 := by
    rcases hsS.1.2.lt_or_eq with h | h
    · exact h
    · exfalso
      have h' := hsS.2
      rw [mem_preimage, h] at h'
      exact h' h1
  have hafter : ∀ t ∈ Ioc s 1, γ t ∈ U := by
    intro t ht
    by_contra hcon
    have htS : t ∈ S := ⟨⟨hts.trans ht.1.le, ht.2⟩, hcon⟩
    exact absurd (le_csSup hSb htS) (not_le.2 ht.1)
  have hcl : γ s ∈ closure U := by
    have hcw : ContinuousWithinAt γ (Ioc s 1) s :=
      (hγ s ⟨ht₀.1.trans hts, hs1.le⟩).mono fun t ht => ⟨(ht₀.1.trans hts).trans ht.1.le, ht.2⟩
    have hmem := hcw.mem_closure_image (by rw [closure_Ioc hs1.ne]; exact left_mem_Icc.2 hs1.le)
    exact closure_mono (by rintro _ ⟨u, hu, rfl⟩; exact hafter u hu) hmem
  refine ⟨s, hts, hs1, ?_, hafter⟩
  rw [hU.frontier_eq]
  exact ⟨hcl, hsS.2⟩

/-- A path from outside `U` (or from `∂U`) to `A ⊆ U` contains a sub-path from `∂U` to its end. -/
theorem lfppSetDist_frontier_le_lfppLength (hφ : Continuous φ) (hU : IsOpen U) {γ : ℝ → Rd d}
    {y : Rd d} (hγ : IsPcwC1Path γ x y) (hy : y ∈ A) (hyU : y ∈ U) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (hout : γ t₀ ∉ U) :
    lfppSetDist ξ φ univ (frontier U) A ≤ lfppLength ξ φ γ := by
  obtain ⟨s, hts, hs1, hsF, -⟩ := exists_last_exit hU hγ.continuousOn
    (by rw [hγ.target]; exact hyU) ht₀ hout
  have hs0 : 0 ≤ s := ht₀.1.trans hts
  have hD := lfppDistOn_le_integral (ξ := ξ) (φ := φ) (W := univ) hγ hs0 hs1.le le_rfl
    fun _ _ => mem_univ _
  rw [hγ.target] at hD
  exact (lfppSetDist_le hsF hy).trans (hD.trans (integral_le_lfppLength hφ hγ hs0 hs1.le le_rfl))

/-- **Exit decomposition** (MA7 §5 row L3b1, D-6.9 (μ3), prelimit): for an open set `U` containing
the nonempty set `A` and `x ∈ U`,
`D(x, A) ≥ min(D(x, A; U), D(∂U, A))` (whole-space metric, internal metric of `U`). -/
theorem lfppMetric_ge_min (hφ : Continuous φ) (hU : IsOpen U) (hAU : A ⊆ U) (hA : A.Nonempty)
    (hx : x ∈ U) :
    min (lfppSetDist ξ φ U {x} A) (lfppSetDist ξ φ univ (frontier U) A) ≤
      lfppSetDist ξ φ univ {x} A := by
  refine le_lfppSetDist (singleton_nonempty x) hA fun x' hx' y hy => ?_
  rw [mem_singleton_iff] at hx'
  subst hx'
  refine le_lfppDistOn (pcwJoined_univ x' y) fun γ hγ _ => ?_
  by_cases hin : MapsTo γ (Icc 0 1) U
  · exact (min_le_left _ _).trans ((lfppSetDist_le (mem_singleton x') hy).trans
      (lfppDistOn_le_lfppLength hγ hin))
  · rw [MapsTo] at hin
    push Not at hin
    obtain ⟨t₀, ht₀, hout⟩ := hin
    exact (min_le_right _ _).trans
      (lfppSetDist_frontier_le_lfppLength hφ hU hγ hy (hAU hy) ht₀ hout)

/-- **Exit decomposition, outside point** (MA7 D-6.9 (μ3)): for `x ∉ U ⊇ A`,
`D(x, A) ≥ D(∂U, A)`. -/
theorem lfppSetDist_frontier_le (hφ : Continuous φ) (hU : IsOpen U) (hAU : A ⊆ U)
    (hA : A.Nonempty) (hx : x ∉ U) :
    lfppSetDist ξ φ univ (frontier U) A ≤ lfppSetDist ξ φ univ {x} A := by
  refine le_lfppSetDist (singleton_nonempty x) hA fun x' hx' y hy => ?_
  rw [mem_singleton_iff] at hx'
  subst hx'
  refine le_lfppDistOn (pcwJoined_univ x' y) fun γ hγ _ => ?_
  exact lfppSetDist_frontier_le_lfppLength hφ hU hγ hy (hAU hy) (left_mem_Icc.2 zero_le_one)
    (by rw [hγ.source]; exact hx)

/-- **Collar bound** (MA7 D-6.9 (μ3), prelimit): let `g` be continuous with `g ≤ 0` off `U`,
`g ≤ ρ` on `F` and `g ≥ ρ > 0` on `A` (both nonempty). Then every path from `F` to `A` meets the
level set `K = {z ∈ U | g z = ρ}` and stays in `U` afterwards, so `D(K, A; U) ≤ D(F, A)`.
(With `g = dist(·, Uᶜ)` and `F = ∂U` this is MA7's collar inequality.) -/
theorem lfppSetDist_level_le (hφ : Continuous φ) {g : Rd d → ℝ} (hg : Continuous g) {ρ : ℝ}
    (hρ : 0 < ρ) (hgU : ∀ z, z ∉ U → g z ≤ 0) (hgF : ∀ p ∈ F, g p ≤ ρ) (hgA : ∀ a ∈ A, ρ ≤ g a)
    (hF : F.Nonempty) (hA : A.Nonempty) :
    lfppSetDist ξ φ U {z | z ∈ U ∧ g z = ρ} A ≤ lfppSetDist ξ φ univ F A := by
  refine le_lfppSetDist hF hA fun p hp a ha => ?_
  refine le_lfppDistOn (pcwJoined_univ p a) fun γ hγ _ => ?_
  have hgγ : ContinuousOn (fun t => g (γ t)) (Icc 0 1) := hg.comp_continuousOn hγ.continuousOn
  set T : Set ℝ := Icc (0 : ℝ) 1 ∩ (fun t => g (γ t)) ⁻¹' Iic ρ with hT
  have hTc : IsClosed T := hgγ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have h0T : (0 : ℝ) ∈ T := ⟨left_mem_Icc.2 zero_le_one, by
    show g (γ 0) ≤ ρ
    rw [hγ.source]; exact hgF p hp⟩
  have hTb : BddAbove T := ⟨1, fun t ht => ht.1.2⟩
  set t₀ := sSup T with ht₀
  have ht₀T : t₀ ∈ T := hTc.csSup_mem ⟨0, h0T⟩ hTb
  have ht₀0 : 0 ≤ t₀ := ht₀T.1.1
  have ht₀1 : t₀ ≤ 1 := ht₀T.1.2
  have hafter : ∀ t ∈ Ioc t₀ 1, ρ < g (γ t) := by
    intro t ht
    by_contra hcon
    have htT : t ∈ T := ⟨⟨ht₀0.trans ht.1.le, ht.2⟩, not_lt.1 hcon⟩
    exact absurd (le_csSup hTb htT) (not_le.2 ht.1)
  have hge : ρ ≤ g (γ t₀) := by
    rcases ht₀1.lt_or_eq with h | h
    · have hcw : ContinuousWithinAt (fun t => g (γ t)) (Ioc t₀ 1) t₀ :=
        (hgγ t₀ ⟨ht₀0, ht₀1⟩).mono fun t ht => ⟨ht₀0.trans ht.1.le, ht.2⟩
      have hmem := hcw.mem_closure_image (by rw [closure_Ioc h.ne]; exact left_mem_Icc.2 h.le)
      have hsub : (fun t => g (γ t)) '' Ioc t₀ 1 ⊆ Ici ρ := by
        rintro _ ⟨u, hu, rfl⟩
        exact (hafter u hu).le
      exact (isClosed_Ici.closure_subset_iff.2 hsub) hmem
    · rw [h, hγ.target]; exact hgA a ha
  have heq : g (γ t₀) = ρ := le_antisymm ht₀T.2 hge
  have hinU : ∀ t ∈ Icc t₀ 1, γ t ∈ U := by
    intro t ht
    by_contra hcon
    have h1 := hgU _ hcon
    rcases ht.1.lt_or_eq with h | h
    · linarith [hafter t ⟨h, ht.2⟩]
    · rw [← h, heq] at h1; linarith
  have hK : γ t₀ ∈ {z | z ∈ U ∧ g z = ρ} := ⟨hinU t₀ ⟨le_rfl, ht₀1⟩, heq⟩
  have hD := lfppDistOn_le_integral (ξ := ξ) (φ := φ) hγ ht₀0 ht₀1 le_rfl hinU
  rw [hγ.target] at hD
  exact (lfppSetDist_le hK ha).trans (hD.trans (integral_le_lfppLength hφ hγ ht₀0 ht₀1 le_rfl))

end Exit

end HigherDimLQGMetric.DGZ
