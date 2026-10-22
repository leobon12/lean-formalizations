import HigherDimLQGMetric.DGZ.Continuity
import HigherDimLQGMetric.DGZ.Crossing

/-!
# Bounds for internal diameters and set distances (packet L3b1)

Source: MA7 (`planning/audits/MA7-ref2-sections-4-6.md`) Details (a): D-4.6 (the concentration
lemma needs `Φ > 0` and log-Lipschitz functionals: set distances between compact sets,
`lfppDiam`), D-4.8 (`across ≥ min_{i,j} S_{ij}` and `S_{ij} ≥ D_n(x_i, y_j; B₃) - Y_{x_i} - Y_{y_j}`
with `Y_w = selfDiam`), D-5.14 (iii) (`D_n(0, e₁) ≤ 2 diam + D_n(boxes)`).

* Internal diameters: `bddAbove_lfppDiam_of_isCompact` (`U ⊆ K` compact `⊆ V` open preconnected),
  `lfppDiam_pos`, field comparison `lfppDiam_le_mul_of_exp_le`, `lfppDiam_le_exp_mul`,
  `abs_log_lfppDiam_sub_le`, `lfppDiam_mono_field`.
* Set distances: the lower bound `exp_mul_le_lfppSetDist` (exit time from balls of radius `δ`
  around `A`), positivity `lfppSetDist_pos` (`A` compact, `B` closed, disjoint, nonempty, all
  pairs joined), and `inf'_le_lfppSetDist_of_subset` (finite covers of the two sets).
* Across distances versus set distances: `acrossDist_le_lfppSetDist` (every path between two sets
  separated by the shell crosses it), `lfppSetDist_lsph_le_acrossDist` (the sphere-to-sphere
  distance in any domain containing the closed shell is at most the across distance; with
  `IsShellPair.lfppSetDist_le_lfppDistOn` the two agree when the domain is `univ`).
* Triangle-type bounds: `lfppDistOn_le_lfppDiam_add_lfppSetDist` and its box form
  `lfppDistOn_le_selfDiam_add_lfppSetDist`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ}

/-! ## Internal diameters -/

section Diam

variable {ξ : ℝ} {φ ψ : Rd d → ℝ} {U V : Set (Rd d)} {x y : Rd d}

/-- For a continuous field and `U ⊆ K` with `K` compact inside an open preconnected `V`, the family
defining `Diam(U; V)` is bounded above. -/
theorem bddAbove_lfppDiam_of_isCompact (hV : IsOpen V) (hVc : IsPreconnected V)
    (hφ : Continuous φ) (ξ : ℝ) {K : Set (Rd d)} (hK : IsCompact K) (hKV : K ⊆ V)
    (hUK : U ⊆ K) :
    BddAbove ((fun p : Rd d × Rd d => lfppDistOn ξ φ V p.1 p.2) '' (U ×ˢ U)) :=
  ((hK.prod hK).bddAbove_image ((continuousOn_lfppDistOn hV hVc hφ ξ).mono
    (prod_mono hKV hKV))).mono (image_mono (prod_mono hUK hUK))

/-- **Positivity of internal diameters**: two distinct points of `U` joined in `V`. -/
theorem lfppDiam_pos (hφ : Continuous φ)
    (hbdd : BddAbove ((fun p : Rd d × Rd d => lfppDistOn ξ φ V p.1 p.2) '' (U ×ˢ U)))
    (hx : x ∈ U) (hy : y ∈ U) (hxy : x ≠ y) (hj : PcwJoined V x y) : 0 < lfppDiam ξ φ U V :=
  (lfppDistOn_pos hφ hxy hj).trans_le (lfppDistOn_le_lfppDiam hbdd hx hy)

/-- **Field comparison for internal diameters**: if `e^{ξ φ} ≤ C e^{ξ ψ}` on `V` (`C ≥ 0`) and the
family of `ψ` is bounded above, then `Diam(U; V)(φ) ≤ C Diam(U; V)(ψ)`. -/
theorem lfppDiam_le_mul_of_exp_le (hφ : Continuous φ) (hψ : Continuous ψ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ z ∈ V, Real.exp (ξ * φ z) ≤ C * Real.exp (ξ * ψ z))
    (hbdd : BddAbove ((fun p : Rd d × Rd d => lfppDistOn ξ ψ V p.1 p.2) '' (U ×ˢ U))) :
    lfppDiam ξ φ U V ≤ C * lfppDiam ξ ψ U V :=
  lfppDiam_le (mul_nonneg hC (lfppDiam_nonneg ξ ψ U V)) fun _ hx _ hy =>
    (lfppDistOn_le_mul_of_exp_le hφ hψ hC h).trans
      (mul_le_mul_of_nonneg_left (lfppDistOn_le_lfppDiam hbdd hx hy) hC)

theorem lfppDiam_le_exp_mul (hφ : Continuous φ) (hψ : Continuous ψ) {M : ℝ}
    (hM : ∀ z ∈ V, |φ z - ψ z| ≤ M)
    (hbdd : BddAbove ((fun p : Rd d × Rd d => lfppDistOn ξ ψ V p.1 p.2) '' (U ×ˢ U))) :
    lfppDiam ξ φ U V ≤ Real.exp (|ξ| * M) * lfppDiam ξ ψ U V :=
  lfppDiam_le_mul_of_exp_le hφ hψ (Real.exp_pos _).le
    (fun z hz => exp_mul_le_exp_abs_mul (hM z hz)) hbdd

/-- **Log-Lipschitz bound for internal diameters** (MA7 D-4.6): if `|φ - ψ| ≤ M` on `V` (`M ≥ 0`)
and both families are bounded above, `|log Diam(U; V)(φ) - log Diam(U; V)(ψ)| ≤ |ξ| M`. -/
theorem abs_log_lfppDiam_sub_le (hφ : Continuous φ) (hψ : Continuous ψ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ V, |φ z - ψ z| ≤ M)
    (hbddφ : BddAbove ((fun p : Rd d × Rd d => lfppDistOn ξ φ V p.1 p.2) '' (U ×ˢ U)))
    (hbddψ : BddAbove ((fun p : Rd d × Rd d => lfppDistOn ξ ψ V p.1 p.2) '' (U ×ˢ U))) :
    |Real.log (lfppDiam ξ φ U V) - Real.log (lfppDiam ξ ψ U V)| ≤ |ξ| * M :=
  abs_log_sub_le_of_le_exp_mul (lfppDiam_nonneg ξ φ U V) (lfppDiam_nonneg ξ ψ U V)
    (mul_nonneg (abs_nonneg ξ) hM0) (lfppDiam_le_exp_mul hφ hψ hM hbddψ)
    (lfppDiam_le_exp_mul hψ hφ (fun z hz => by rw [abs_sub_comm]; exact hM z hz) hbddφ)

/-- **Monotonicity of internal diameters in the field** (`ξ ≥ 0`). -/
theorem lfppDiam_mono_field (hξ : 0 ≤ ξ) (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : ∀ z ∈ V, φ z ≤ ψ z)
    (hbdd : BddAbove ((fun p : Rd d × Rd d => lfppDistOn ξ ψ V p.1 p.2) '' (U ×ˢ U))) :
    lfppDiam ξ φ U V ≤ lfppDiam ξ ψ U V := by
  have := lfppDiam_le_mul_of_exp_le (ξ := ξ) (U := U) hφ hψ zero_le_one (fun z hz => by
    rw [one_mul, Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left (h z hz) hξ) hbdd
  rwa [one_mul] at this

end Diam

/-! ## Set distances: lower bounds and covers -/

section SetDist

variable {ξ : ℝ} {φ : Rd d → ℝ} {V A B : Set (Rd d)}

/-- **Lower bound for set distances** (exit time from the balls `B̄(x, δ)`, `x ∈ A`): if all pairs
are at distance `≥ δ`, joined in `V`, and `ξ φ ≥ m` on the `δ`-balls around `A`, then
`D(A, B; V) ≥ e^m δ`. -/
theorem exp_mul_le_lfppSetDist (hφ : Continuous φ) (hA : A.Nonempty) (hB : B.Nonempty) {δ m : ℝ}
    (hδ : ∀ x ∈ A, ∀ y ∈ B, δ ≤ ‖y - x‖)
    (hm : ∀ x ∈ A, ∀ z ∈ Metric.closedBall x δ, m ≤ ξ * φ z)
    (hj : ∀ x ∈ A, ∀ y ∈ B, PcwJoined V x y) : Real.exp m * δ ≤ lfppSetDist ξ φ V A B :=
  le_lfppSetDist hA hB fun x hx y hy =>
    exp_mul_le_lfppDistOn hφ (hj x hx y hy) (hδ x hx y hy) (hm x hx)

/-- **Positivity of set distances**: `A` compact, `B` closed, both nonempty and disjoint, all pairs
joined in `V`, continuous field. -/
theorem lfppSetDist_pos (hφ : Continuous φ) (hA : IsCompact A) (hAne : A.Nonempty)
    (hB : IsClosed B) (hBne : B.Nonempty) (hAB : Disjoint A B)
    (hj : ∀ x ∈ A, ∀ y ∈ B, PcwJoined V x y) : 0 < lfppSetDist ξ φ V A B := by
  obtain ⟨δ, hδ, hdisj⟩ := hAB.exists_cthickenings hA hB
  obtain ⟨m, hm⟩ := (hA.cthickening (r := δ)).bddBelow_image
    (continuous_const.mul hφ).continuousOn
  have hsep : ∀ x ∈ A, ∀ y ∈ B, δ ≤ ‖y - x‖ := by
    intro x hx y hy
    by_contra hlt
    rw [not_le] at hlt
    have hyA : y ∈ Metric.cthickening δ A :=
      Metric.closedBall_subset_cthickening hx δ
        (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hlt.le)
    exact Set.disjoint_left.1 hdisj hyA (Metric.self_subset_cthickening B hy)
  exact (mul_pos (Real.exp_pos m) hδ).trans_le (exp_mul_le_lfppSetDist hφ hAne hBne hsep
    (fun x hx z hz => hm ⟨z, Metric.closedBall_subset_cthickening hx δ hz, rfl⟩) hj)

/-- **Finite covers**: if `A ⊆ ⋃_{i ∈ I} A i` and `B ⊆ ⋃_{j ∈ J} B j` (`A`, `B` nonempty), then
`D(A, B; V) ≥ min_{i,j} D(A i, B j; V)`. -/
theorem inf'_le_lfppSetDist_of_subset {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (hIJ : (I ×ˢ J).Nonempty) (Ai : ι → Set (Rd d)) (Bj : κ → Set (Rd d))
    (hAcov : A ⊆ ⋃ i ∈ I, Ai i) (hBcov : B ⊆ ⋃ j ∈ J, Bj j) (hA : A.Nonempty)
    (hB : B.Nonempty) :
    (I ×ˢ J).inf' hIJ (fun p => lfppSetDist ξ φ V (Ai p.1) (Bj p.2)) ≤
      lfppSetDist ξ φ V A B := by
  refine le_lfppSetDist hA hB fun x hx y hy => ?_
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (hAcov hx)
  obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.1 (hBcov hy)
  have hmem : (i, j) ∈ I ×ˢ J := Finset.mem_product.2 ⟨hi, hj⟩
  exact (Finset.inf'_le (fun p : ι × κ => lfppSetDist ξ φ V (Ai p.1) (Bj p.2)) hmem).trans
    (lfppSetDist_le hxi hyj)

end SetDist

/-! ## Across distances versus set distances in a domain -/

section Across

variable {ξ : ℝ} {φ : Rd d → ℝ} {c : Rd d} {r₁ r₂ : ℝ} {V : Set (Rd d)}

/-- **Across distance versus the sphere-to-sphere distance in a domain** (MA7 D-4.8): for any
domain `V` containing the closed shell, `D(∂B_{r₂}(c), ∂B_{r₁}(c); V) ≤ D(across)`. -/
theorem lfppSetDist_lsph_le_acrossDist (hφ : Continuous φ) (hr : r₂ < r₁)
    (hV : cbox c r₁ \ obox c r₂ ⊆ V) :
    lfppSetDist ξ φ V (lsph c r₂) (lsph c r₁) ≤ acrossDist ξ φ c r₁ r₂ := by
  by_cases hne : (lsph c r₂).Nonempty ∧ (lsph c r₁).Nonempty
  · exact le_lfppSetDist hne.1 hne.2 fun x hx y hy =>
      (isShellPair_box c hr).lfppSetDist_le_lfppDistOn hφ hV hx.1 hy.2 (pcwJoined_univ x y)
  · rw [lfppSetDist_of_not_nonempty hne]
    exact acrossDist_nonneg ξ φ c r₁ r₂

/-- **Every path between the two sets crosses the shell** (MA7 D-5.14 (iii)): if
`A ⊆ cbox c r₂`, `B` misses `obox c r₁` (`r₂ < r₁`), both are nonempty and all pairs are joined in
`V`, then `D(across) ≤ D(A, B; V)`. -/
theorem acrossDist_le_lfppSetDist (hφ : Continuous φ) (hr : r₂ < r₁) {A B : Set (Rd d)}
    (hA : A ⊆ cbox c r₂) (hB : ∀ y ∈ B, y ∉ obox c r₁) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hj : ∀ x ∈ A, ∀ y ∈ B, PcwJoined V x y) :
    acrossDist ξ φ c r₁ r₂ ≤ lfppSetDist ξ φ V A B :=
  le_lfppSetDist hAne hBne fun x hx y hy =>
    acrossDist_le_lfppDistOn hφ hr (hA hx) (hB y hy) (hj x hx y hy)

end Across

/-! ## Triangle-type bounds -/

section Triangle

variable {ξ : ℝ} {φ : Rd d → ℝ} {V A B WA WB : Set (Rd d)} {a b : Rd d}

/-- **Triangle bound through two sets** (MA7 D-5.14 (iii)): for `a ∈ A`, `b ∈ B`, an open
preconnected `V ⊇ A ∪ B ∪ WA ∪ WB`, and points of `A` (resp. `B`) joined in `WA` (resp. `WB`)
with bounded families,
`D_V(a, b) ≤ Diam(A; WA) + D(A, B; V) + Diam(B; WB)`. -/
theorem lfppDistOn_le_lfppDiam_add_lfppSetDist (hφ : Continuous φ) (hV : IsOpen V)
    (hVc : IsPreconnected V) (ha : a ∈ A) (hb : b ∈ B) (hAV : A ⊆ V) (hBV : B ⊆ V)
    (hWA : WA ⊆ V) (hWB : WB ⊆ V) (hjA : ∀ x ∈ A, ∀ y ∈ A, PcwJoined WA x y)
    (hjB : ∀ x ∈ B, ∀ y ∈ B, PcwJoined WB x y)
    (hbddA : BddAbove ((fun p : Rd d × Rd d => lfppDistOn ξ φ WA p.1 p.2) '' (A ×ˢ A)))
    (hbddB : BddAbove ((fun p : Rd d × Rd d => lfppDistOn ξ φ WB p.1 p.2) '' (B ×ˢ B))) :
    lfppDistOn ξ φ V a b ≤ lfppDiam ξ φ A WA + lfppSetDist ξ φ V A B + lfppDiam ξ φ B WB := by
  have key : ∀ x ∈ A, ∀ y ∈ B,
      lfppDistOn ξ φ V a b - lfppDiam ξ φ A WA - lfppDiam ξ φ B WB ≤ lfppDistOn ξ φ V x y := by
    intro x hx y hy
    have j := fun p q (hp : p ∈ V) (hq : q ∈ V) => pcwJoined_of_isPreconnected hV hVc hp hq
    have h1 : lfppDistOn ξ φ V a b ≤
        lfppDistOn ξ φ V a x + lfppDistOn ξ φ V x y + lfppDistOn ξ φ V y b := by
      calc lfppDistOn ξ φ V a b ≤ lfppDistOn ξ φ V a y + lfppDistOn ξ φ V y b :=
            lfppDistOn_triangle hφ (j a y (hAV ha) (hBV hy)) (j y b (hBV hy) (hBV hb))
        _ ≤ (lfppDistOn ξ φ V a x + lfppDistOn ξ φ V x y) + lfppDistOn ξ φ V y b := by
            gcongr
            exact lfppDistOn_triangle hφ (j a x (hAV ha) (hAV hx)) (j x y (hAV hx) (hBV hy))
    have h2 : lfppDistOn ξ φ V a x ≤ lfppDiam ξ φ A WA :=
      (lfppDistOn_mono hWA (hjA a ha x hx)).trans (lfppDistOn_le_lfppDiam hbddA ha hx)
    have h3 : lfppDistOn ξ φ V y b ≤ lfppDiam ξ φ B WB :=
      (lfppDistOn_mono hWB (hjB y hy b hb)).trans (lfppDistOn_le_lfppDiam hbddB hy hb)
    linarith
  have h := le_lfppSetDist (V := V) ⟨a, ha⟩ ⟨b, hb⟩ key
  linarith

/-- **Triangle bound through two boxes** (MA7 D-4.8 (1): `S ≥ D(x, y; B₃) - Y_x - Y_y`): for
`A ⊆ B_{ρa}(a)`, `B ⊆ B_{ρb}(b)` nonempty, both boxes inside an open preconnected `V`,
`D_V(a, b) ≤ selfDiam(B_{ρa}(a)) + D(A, B; V) + selfDiam(B_{ρb}(b))`. -/
theorem lfppDistOn_le_selfDiam_add_lfppSetDist (hφ : Continuous φ) (hV : IsOpen V)
    (hVc : IsPreconnected V) {ρa ρb : ℝ} (hA : A ⊆ obox a ρa) (hB : B ⊆ obox b ρb)
    (haV : obox a ρa ⊆ V) (hbV : obox b ρb ⊆ V) (hAne : A.Nonempty) (hBne : B.Nonempty) :
    lfppDistOn ξ φ V a b ≤ selfDiam ξ φ a ρa + lfppSetDist ξ φ V A B + selfDiam ξ φ b ρb := by
  obtain ⟨x₀, hx₀⟩ := hAne
  obtain ⟨y₀, hy₀⟩ := hBne
  -- the centres lie in their boxes (coordinatewise, from a point of `A`, resp. `B`)
  have hamem : a ∈ obox a ρa := fun i => by
    rw [sub_self, abs_zero]
    exact (abs_nonneg _).trans_lt (hA hx₀ i)
  have hbmem : b ∈ obox b ρb := fun i => by
    rw [sub_self, abs_zero]
    exact (abs_nonneg _).trans_lt (hB hy₀ i)
  have key : ∀ x ∈ A, ∀ y ∈ B,
      lfppDistOn ξ φ V a b - selfDiam ξ φ a ρa - selfDiam ξ φ b ρb ≤ lfppDistOn ξ φ V x y := by
    intro x hx y hy
    have j := fun p q (hp : p ∈ V) (hq : q ∈ V) => pcwJoined_of_isPreconnected hV hVc hp hq
    have hxV : x ∈ V := haV (hA hx)
    have hyV : y ∈ V := hbV (hB hy)
    have h1 : lfppDistOn ξ φ V a b ≤
        lfppDistOn ξ φ V a x + lfppDistOn ξ φ V x y + lfppDistOn ξ φ V y b := by
      calc lfppDistOn ξ φ V a b ≤ lfppDistOn ξ φ V a y + lfppDistOn ξ φ V y b :=
            lfppDistOn_triangle hφ (j a y (haV hamem) hyV) (j y b hyV (hbV hbmem))
        _ ≤ (lfppDistOn ξ φ V a x + lfppDistOn ξ φ V x y) + lfppDistOn ξ φ V y b := by
            gcongr
            exact lfppDistOn_triangle hφ (j a x (haV hamem) hxV) (j x y hxV hyV)
    have h2 : lfppDistOn ξ φ V a x ≤ selfDiam ξ φ a ρa :=
      lfppDistOn_le_selfDiam_of_subset hφ haV hamem (hA hx)
    have h3 : lfppDistOn ξ φ V y b ≤ selfDiam ξ φ b ρb :=
      lfppDistOn_le_selfDiam_of_subset hφ hbV (hB hy) hbmem
    linarith
  have h := le_lfppSetDist (V := V) ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩ key
  linarith

end Triangle

end HigherDimLQGMetric.DGZ
