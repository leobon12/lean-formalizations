import HigherDimLFPP.Frozen.Rd
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Arc moduli and the junction sets of the bisection (Lemma 4.1′)

Packet Q1 (ruling N9). Source: planning audit `planning/audits/NA2-section-4.md`, Details (c) **R1**
("Junction sets" and the splitting identity); [C] (4.1), p. 10.

* `ArcModuli γ A α β`: the two-sided moduli (4.1) of `γ` on `[0, 1]`,
  `|γ s - γ t| ≤ A |s - t|^α` and `|s - t| ≤ A |γ s - γ t|^β`.
* `junctionSet γ m r ρ a b` (`S_{[a,b]}`): the closed `r`-thickening of `γ([a, b])` together with
  the closed `ρ`-balls `B̄(γ(j 2^{-m}), ρ)` at the dyadic junction points `j 2^{-m} ∈ [a, b]`.
* `junctionSet_inter` (**splitting identity**): at a dyadic point `t = j 2^{-m} ∈ [a, b]`,
  `S_{[a,t]} ∩ S_{[t,b]} = B̄(γ(t), ρ)` when `ρ = r + A^{1+α}(2r)^{αβ}` and
  `A(2ρ + r)^β < 2^{-m}`. Cases: two arc points near `x` on both sides of `t` are at parameter
  distance `≤ A(2r)^β`, so `x` is within `r + A^{1+α}(2r)^{αβ}` of `γ(t)`; an arc point and a
  different junction ball, or two different junction balls, would force two parameters at least
  `2^{-m}` apart to have images within `ρ + r` (resp. `2ρ`), contradicting the inverse modulus.

Auxiliary facts for the bisection: `isClosed_junctionSet`, `junctionSet_subset_union`,
`junctionSet_subset_closedBall` (the leaves) and `exists_dist_le_of_mem_junctionSet`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity.Topology

variable {d : ℕ}

/-- The two-sided arc moduli (4.1) of `γ` on `[0, 1]`. -/
def ArcModuli (γ : ℝ → Rd d) (A α β : ℝ) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
    ‖γ s - γ t‖ ≤ A * |s - t| ^ α ∧ |s - t| ≤ A * ‖γ s - γ t‖ ^ β

/-- The set `S_I` of the bisection: the closed `r`-thickening of `γ([a, b])` together with the
closed `ρ`-balls at the dyadic junction points of level `≤ m` in `[a, b]`. -/
def junctionSet (γ : ℝ → Rd d) (m : ℕ) (r ρ a b : ℝ) : Set (Rd d) :=
  cthickening r (γ '' Icc a b) ∪
    ⋃ j ∈ Finset.range (2 ^ m + 1),
      {x | a ≤ (j : ℝ) / 2 ^ m ∧ (j : ℝ) / 2 ^ m ≤ b ∧ x ∈ closedBall (γ ((j : ℝ) / 2 ^ m)) ρ}

/-! ### Consequences of the arc moduli -/

section ArcModuli

variable {γ : ℝ → Rd d} {A α β : ℝ}

/-- An arc with a Hölder modulus of positive exponent is continuous on `[0, 1]`. -/
lemma ArcModuli.continuousOn (hγ : ArcModuli γ A α β) (hα : 0 < α) :
    ContinuousOn γ (Icc 0 1) := by
  intro s hs
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hg : Tendsto (fun s' : ℝ => A * |s' - s| ^ α) (𝓝[Icc 0 1] s) (𝓝 0) := by
    have hc : Continuous fun s' : ℝ => A * |s' - s| ^ α :=
      continuous_const.mul ((Real.continuous_rpow_const hα.le).comp
        (continuous_abs.comp (continuous_id.sub continuous_const)))
    have h0 : A * |s - s| ^ α = 0 := by
      rw [sub_self, abs_zero, Real.zero_rpow hα.ne', mul_zero]
    have := hc.continuousAt (x := s)
    rw [ContinuousAt, h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hg
  filter_upwards [self_mem_nhdsWithin] with s' hs'
  exact (hγ s' hs' s hs).1

lemma ArcModuli.norm_sub_le (hγ : ArcModuli γ A α β) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) : ‖γ s - γ t‖ ≤ A * |s - t| ^ α :=
  (hγ s hs t ht).1

/-- The inverse modulus with a bound on the distance of the images. -/
lemma ArcModuli.abs_sub_le (hγ : ArcModuli γ A α β) (hA : 0 ≤ A) (hβ : 0 ≤ β) {s t D : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hD : ‖γ s - γ t‖ ≤ D) :
    |s - t| ≤ A * D ^ β :=
  (hγ s hs t ht).2.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hD hβ) hA)

/-- A point of the closed `r`-thickening of `γ([a, b]) ⊆ γ([0, 1])` is within `r` of some arc
point `γ(s)`, `s ∈ [a, b]` (compactness). -/
lemma ArcModuli.exists_dist_le_of_mem_cthickening (hγ : ArcModuli γ A α β) (hα : 0 < α)
    {r a b : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) (hb : b ≤ 1) {x : Rd d}
    (hx : x ∈ cthickening r (γ '' Icc a b)) : ∃ s ∈ Icc a b, dist x (γ s) ≤ r := by
  have hK : IsCompact (γ '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn
      ((hγ.continuousOn hα).mono (Icc_subset_Icc ha hb))
  rw [hK.cthickening_eq_biUnion_closedBall hr] at hx
  obtain ⟨z, ⟨s, hs, rfl⟩, hxz⟩ := mem_iUnion₂.1 hx
  exact ⟨s, hs, hxz⟩

end ArcModuli

/-! ### Dyadic points -/

/-- Two different dyadic points of level `m` are at least `2^{-m}` apart. -/
lemma dyadic_gap {m j j' : ℕ} (h : (j : ℝ) / 2 ^ m < (j' : ℝ) / 2 ^ m) :
    (2 : ℝ)⁻¹ ^ m ≤ (j' : ℝ) / 2 ^ m - (j : ℝ) / 2 ^ m := by
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  have hjj : (j : ℝ) < j' := (div_lt_div_iff_of_pos_right h2).1 h
  have hjj' : j + 1 ≤ j' := by exact_mod_cast hjj
  have hjj'' : (j : ℝ) + 1 ≤ j' := by exact_mod_cast hjj'
  rw [div_sub_div_same, inv_pow, le_div_iff₀ h2, inv_mul_cancel₀ h2.ne']
  linarith

/-! ### Elementary properties of the junction sets -/

section JunctionSet

variable {γ : ℝ → Rd d} {m : ℕ} {r ρ : ℝ}

lemma mem_junctionSet_iff {a b : ℝ} {x : Rd d} :
    x ∈ junctionSet γ m r ρ a b ↔ x ∈ cthickening r (γ '' Icc a b) ∨
      ∃ j : ℕ, j ≤ 2 ^ m ∧ a ≤ (j : ℝ) / 2 ^ m ∧ (j : ℝ) / 2 ^ m ≤ b ∧
        x ∈ closedBall (γ ((j : ℝ) / 2 ^ m)) ρ := by
  simp only [junctionSet, mem_union, mem_iUnion, Finset.mem_range, mem_ofPred_eq, exists_prop,
    Nat.lt_succ_iff]

lemma isClosed_junctionSet (a b : ℝ) : IsClosed (junctionSet γ m r ρ a b) := by
  refine isClosed_cthickening.union (isClosed_biUnion_finset fun j _ => ?_)
  by_cases h : a ≤ (j : ℝ) / 2 ^ m ∧ (j : ℝ) / 2 ^ m ≤ b
  · have : {x | a ≤ (j : ℝ) / 2 ^ m ∧ (j : ℝ) / 2 ^ m ≤ b ∧
        x ∈ closedBall (γ ((j : ℝ) / 2 ^ m)) ρ} = closedBall (γ ((j : ℝ) / 2 ^ m)) ρ := by
      ext x
      simp only [mem_ofPred_eq, h, true_and]
    rw [this]
    exact isClosed_closedBall
  · have : {x | a ≤ (j : ℝ) / 2 ^ m ∧ (j : ℝ) / 2 ^ m ≤ b ∧
        x ∈ closedBall (γ ((j : ℝ) / 2 ^ m)) ρ} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ h
    rw [this]
    exact isClosed_empty

/-- `S_{[a,b]} ⊆ S_{[a,t]} ∪ S_{[t,b]}` for `a ≤ t ≤ b` (in fact equality). -/
lemma junctionSet_subset_union {a t b : ℝ} (hat : a ≤ t) (htb : t ≤ b) :
    junctionSet γ m r ρ a b ⊆ junctionSet γ m r ρ a t ∪ junctionSet γ m r ρ t b := by
  intro x hx
  rcases mem_junctionSet_iff.1 hx with h | ⟨j, hj, h1, h2, h3⟩
  · rw [← Icc_union_Icc_eq_Icc hat htb, image_union, cthickening_union] at h
    rcases h with h | h
    · exact Or.inl (mem_junctionSet_iff.2 (Or.inl h))
    · exact Or.inr (mem_junctionSet_iff.2 (Or.inl h))
  · rcases le_total ((j : ℝ) / 2 ^ m) t with h4 | h4
    · exact Or.inl (mem_junctionSet_iff.2 (Or.inr ⟨j, hj, h1, h4, h3⟩))
    · exact Or.inr (mem_junctionSet_iff.2 (Or.inr ⟨j, hj, h4, h2, h3⟩))

/-- Every point of `S_{[a,b]}`, `[a, b] ⊆ [0, 1]`, is within `max r ρ` of an arc point. -/
lemma exists_dist_le_of_mem_junctionSet {A α β : ℝ} (hγ : ArcModuli γ A α β) (hα : 0 < α)
    (hr : 0 ≤ r) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) {x : Rd d}
    (hx : x ∈ junctionSet γ m r ρ a b) : ∃ s ∈ Icc (0 : ℝ) 1, dist x (γ s) ≤ max r ρ := by
  rcases mem_junctionSet_iff.1 hx with h | ⟨j, -, h1, h2, h3⟩
  · obtain ⟨s, hs, hxs⟩ := hγ.exists_dist_le_of_mem_cthickening hα hr ha hb h
    exact ⟨s, ⟨ha.trans hs.1, hs.2.trans hb⟩, hxs.trans (le_max_left _ _)⟩
  · exact ⟨_, ⟨ha.trans h1, h2.trans hb⟩, (mem_closedBall.1 h3).trans (le_max_right _ _)⟩

/-- The leaves: `S_{[a,b]} ⊆ B̄(γ(a), A (b - a)^α + ρ)` when `[a, b] ⊆ [0, 1]` and `r ≤ ρ`. -/
lemma junctionSet_subset_closedBall {A α β : ℝ} (hγ : ArcModuli γ A α β) (hA : 0 ≤ A)
    (hα : 0 < α) (hr : 0 ≤ r) (hrρ : r ≤ ρ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    junctionSet γ m r ρ a b ⊆ closedBall (γ a) (A * (b - a) ^ α + ρ) := by
  have haI : a ∈ Icc (0 : ℝ) 1 := ⟨ha, hab.trans hb⟩
  have key : ∀ s ∈ Icc a b, ‖γ s - γ a‖ ≤ A * (b - a) ^ α := by
    intro s hs
    have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hs.1, hs.2.trans hb⟩
    refine (hγ.norm_sub_le hsI haI).trans (mul_le_mul_of_nonneg_left ?_ hA)
    rw [abs_of_nonneg (by linarith [hs.1])]
    exact Real.rpow_le_rpow (by linarith [hs.1]) (by linarith [hs.2]) hα.le
  intro x hx
  rw [mem_closedBall, dist_eq_norm]
  rcases mem_junctionSet_iff.1 hx with h | ⟨j, -, h1, h2, h3⟩
  · obtain ⟨s, hs, hxs⟩ := hγ.exists_dist_le_of_mem_cthickening hα hr ha hb h
    rw [dist_eq_norm] at hxs
    calc ‖x - γ a‖ = ‖(x - γ s) + (γ s - γ a)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖x - γ s‖ + ‖γ s - γ a‖ := norm_add_le _ _
      _ ≤ r + A * (b - a) ^ α := add_le_add hxs (key s hs)
      _ ≤ A * (b - a) ^ α + ρ := by linarith
  · rw [mem_closedBall, dist_eq_norm] at h3
    calc ‖x - γ a‖ = ‖(x - γ ((j : ℝ) / 2 ^ m)) + (γ ((j : ℝ) / 2 ^ m) - γ a)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ ‖x - γ ((j : ℝ) / 2 ^ m)‖ + ‖γ ((j : ℝ) / 2 ^ m) - γ a‖ := norm_add_le _ _
      _ ≤ ρ + A * (b - a) ^ α := add_le_add h3 (key _ ⟨h1, h2⟩)
      _ = A * (b - a) ^ α + ρ := add_comm _ _

end JunctionSet

/-! ### The splitting identity -/

/-- The splitting identity of the bisection: at a dyadic split point `t` of level `≤ m`,
`S_{[a,t]} ∩ S_{[t,b]} = B̄(γ(t), ρ)` when `ρ = r + A^{1+α}(2r)^{αβ}` and `A(2ρ + r)^β < 2^{-m}`. -/
theorem junctionSet_inter {γ : ℝ → Rd d} {A α β r ρ : ℝ} (hγ : ArcModuli γ A α β) (hA : 1 ≤ A)
    (hα : 0 < α) (hβ : 0 < β) (hr : 0 ≤ r) (hρ : ρ = r + A ^ (1 + α) * (2 * r) ^ (α * β))
    {m : ℕ} (hsep : A * (2 * ρ + r) ^ β < (2 : ℝ)⁻¹ ^ m) {a t b : ℝ} (ha : 0 ≤ a) (hat : a ≤ t)
    (htb : t ≤ b) (hb : b ≤ 1) (htj : ∃ j : ℕ, j ≤ 2 ^ m ∧ t = (j : ℝ) / 2 ^ m) :
    junctionSet γ m r ρ a t ∩ junctionSet γ m r ρ t b = closedBall (γ t) ρ := by
  obtain ⟨j, hj, htj⟩ := htj
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hrρ : r ≤ ρ := by
    have : 0 ≤ A ^ (1 + α) * (2 * r) ^ (α * β) := by positivity
    rw [hρ]
    linarith
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hat, htb.trans hb⟩
  -- a parameter gap of at least `2^{-m}` is incompatible with images within `2ρ + r`
  have hfar : ∀ s s' : ℝ, s ∈ Icc (0 : ℝ) 1 → s' ∈ Icc (0 : ℝ) 1 →
      ‖γ s - γ s'‖ ≤ 2 * ρ + r → (2 : ℝ)⁻¹ ^ m ≤ |s - s'| → False := by
    intro s s' hs hs' hD hgap
    have := hγ.abs_sub_le hA0 hβ.le hs hs' hD
    linarith
  -- two points within `D₁`, `D₂` of `x` are within `D₁ + D₂` of each other
  have htri : ∀ (x z z' : Rd d) (D₁ D₂ : ℝ), ‖x - z‖ ≤ D₁ → ‖x - z'‖ ≤ D₂ → ‖z - z'‖ ≤ D₁ + D₂ := by
    intro x z z' D₁ D₂ h₁ h₂
    calc ‖z - z'‖ = ‖(x - z') - (x - z)‖ := by congr 1; abel
      _ ≤ ‖x - z'‖ + ‖x - z‖ := norm_sub_le _ _
      _ ≤ D₁ + D₂ := by linarith
  apply Subset.antisymm
  · rintro x ⟨hx₁, hx₂⟩
    rw [mem_closedBall, dist_eq_norm]
    rcases mem_junctionSet_iff.1 hx₁ with h₁ | ⟨j₁, -, h₁a, h₁t, h₁x⟩ <;>
      rcases mem_junctionSet_iff.1 hx₂ with h₂ | ⟨j₂, -, h₂t, h₂b, h₂x⟩
    · -- arc–arc: both arc points are within `A(2r)^β` of `t` in parameter
      obtain ⟨s₁, hs₁, hxs₁⟩ := hγ.exists_dist_le_of_mem_cthickening hα hr ha (htb.trans hb) h₁
      obtain ⟨s₂, hs₂, hxs₂⟩ :=
        hγ.exists_dist_le_of_mem_cthickening hα hr (ha.trans hat) hb h₂
      have hs₁I : s₁ ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hs₁.1, hs₁.2.trans (htb.trans hb)⟩
      have hs₂I : s₂ ∈ Icc (0 : ℝ) 1 := ⟨(ha.trans hat).trans hs₂.1, hs₂.2.trans hb⟩
      rw [dist_eq_norm] at hxs₁ hxs₂
      have hD : ‖γ s₁ - γ s₂‖ ≤ 2 * r := by
        have := htri x (γ s₁) (γ s₂) r r hxs₁ hxs₂
        linarith
      have hpar := hγ.abs_sub_le hA0 hβ.le hs₁I hs₂I hD
      rw [abs_of_nonpos (by linarith [hs₁.2, hs₂.1])] at hpar
      have hts : |s₁ - t| ≤ A * (2 * r) ^ β := by
        rw [abs_of_nonpos (by linarith [hs₁.2])]
        linarith [hs₂.1]
      have himg : ‖γ s₁ - γ t‖ ≤ A ^ (1 + α) * (2 * r) ^ (α * β) := by
        calc ‖γ s₁ - γ t‖ ≤ A * |s₁ - t| ^ α := hγ.norm_sub_le hs₁I htI
          _ ≤ A * (A * (2 * r) ^ β) ^ α :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hts hα.le) hA0
          _ = A ^ (1 + α) * (2 * r) ^ (α * β) := by
            rw [Real.mul_rpow hA0 (by positivity), ← Real.rpow_mul (by positivity),
              Real.rpow_add hApos, Real.rpow_one, mul_comm β α]
            ring
      calc ‖x - γ t‖ = ‖(x - γ s₁) + (γ s₁ - γ t)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖x - γ s₁‖ + ‖γ s₁ - γ t‖ := norm_add_le _ _
        _ ≤ ρ := by rw [hρ]; linarith
    · -- arc–ball: the ball must be the one at `t`
      by_cases hjt : (j₂ : ℝ) / 2 ^ m = t
      · rw [hjt, mem_closedBall, dist_eq_norm] at h₂x
        exact h₂x
      · exfalso
        have hlt : t < (j₂ : ℝ) / 2 ^ m := lt_of_le_of_ne h₂t (Ne.symm hjt)
        have hgap := dyadic_gap (m := m) (j := j) (j' := j₂) (by rw [← htj]; exact hlt)
        rw [← htj] at hgap
        obtain ⟨s₁, hs₁, hxs₁⟩ :=
          hγ.exists_dist_le_of_mem_cthickening hα hr ha (htb.trans hb) h₁
        have hs₁I : s₁ ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hs₁.1, hs₁.2.trans (htb.trans hb)⟩
        have hj₂I : (j₂ : ℝ) / 2 ^ m ∈ Icc (0 : ℝ) 1 := ⟨(ha.trans hat).trans h₂t, h₂b.trans hb⟩
        rw [mem_closedBall, dist_eq_norm] at h₂x
        rw [dist_eq_norm] at hxs₁
        refine hfar s₁ _ hs₁I hj₂I ?_ ?_
        · have := htri x _ _ r ρ hxs₁ h₂x
          linarith
        · rw [abs_of_nonpos (by linarith [hs₁.2])]
          linarith [hs₁.2]
    · -- ball–arc: symmetric
      by_cases hjt : (j₁ : ℝ) / 2 ^ m = t
      · rw [hjt, mem_closedBall, dist_eq_norm] at h₁x
        exact h₁x
      · exfalso
        have hlt : (j₁ : ℝ) / 2 ^ m < t := lt_of_le_of_ne h₁t hjt
        have hgap := dyadic_gap (m := m) (j := j₁) (j' := j) (by rw [← htj]; exact hlt)
        rw [← htj] at hgap
        obtain ⟨s₂, hs₂, hxs₂⟩ :=
          hγ.exists_dist_le_of_mem_cthickening hα hr (ha.trans hat) hb h₂
        have hs₂I : s₂ ∈ Icc (0 : ℝ) 1 := ⟨(ha.trans hat).trans hs₂.1, hs₂.2.trans hb⟩
        have hj₁I : (j₁ : ℝ) / 2 ^ m ∈ Icc (0 : ℝ) 1 := ⟨ha.trans h₁a, h₁t.trans (htb.trans hb)⟩
        rw [mem_closedBall, dist_eq_norm] at h₁x
        rw [dist_eq_norm] at hxs₂
        refine hfar _ s₂ hj₁I hs₂I ?_ ?_
        · have := htri x _ _ ρ r h₁x hxs₂
          linarith
        · rw [abs_of_nonpos (by linarith [hs₂.1])]
          linarith [hs₂.1]
    · -- ball–ball: one of the two balls is the one at `t`
      by_cases hjt₁ : (j₁ : ℝ) / 2 ^ m = t
      · rw [hjt₁, mem_closedBall, dist_eq_norm] at h₁x
        exact h₁x
      by_cases hjt₂ : (j₂ : ℝ) / 2 ^ m = t
      · rw [hjt₂, mem_closedBall, dist_eq_norm] at h₂x
        exact h₂x
      exfalso
      have hlt : (j₁ : ℝ) / 2 ^ m < (j₂ : ℝ) / 2 ^ m :=
        (lt_of_le_of_ne h₁t hjt₁).trans (lt_of_le_of_ne h₂t (Ne.symm hjt₂))
      have hgap := dyadic_gap hlt
      have hj₁I : (j₁ : ℝ) / 2 ^ m ∈ Icc (0 : ℝ) 1 := ⟨ha.trans h₁a, h₁t.trans (htb.trans hb)⟩
      have hj₂I : (j₂ : ℝ) / 2 ^ m ∈ Icc (0 : ℝ) 1 := ⟨(ha.trans hat).trans h₂t, h₂b.trans hb⟩
      rw [mem_closedBall, dist_eq_norm] at h₁x h₂x
      refine hfar _ _ hj₁I hj₂I ?_ ?_
      · have := htri x _ _ ρ ρ h₁x h₂x
        linarith
      · rw [abs_of_nonpos (by linarith)]
        linarith
  · intro x hx
    have hx' : x ∈ closedBall (γ ((j : ℝ) / 2 ^ m)) ρ := by rwa [← htj]
    exact ⟨mem_junctionSet_iff.2 (Or.inr ⟨j, hj, htj ▸ hat, htj ▸ le_rfl, hx'⟩),
      mem_junctionSet_iff.2 (Or.inr ⟨j, hj, htj ▸ le_rfl, htj ▸ htb, hx'⟩)⟩

end HigherDimLQGContinuity.Topology

end
