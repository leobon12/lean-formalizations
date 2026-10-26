import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.Complex.Basic

/-!
# First and last hitting times along a source geodesic (Lemma 4.1, SB2 D6 steps 2–3)

Generic first/last hitting times of a closed set by a continuous real function on a compact interval (SB2 D2, T5),
and the two time constructions of the proof of Lemma 4.1 (paper l. 408–420):
* `l41_J_exists`: the segment `J = [a₀, b₀]` (`b₀` the first hit of `B̄_ρ(w)`, `a₀` the last visit to `B̄_ρ(z)`
  before `b₀`), on which the path stays at distance `≥ ρ` from both endpoints;
* `l41_excursion`: the excursion `I = [α, β]` from the last visit of `∂B_{6r}(c)` before `τ` to the first visit after
  `τ`, and its annular crossing `G = [s, t] ⊂ I` (`t` the first hit of `∂B_{2r}(c)` after `τ`, `s` the last visit to
  `∂B_r(c)` before `t`).
-/

set_option autoImplicit false
noncomputable section

open Set

namespace SupercriticalLFPPAS.Contraction

/-- The last time in `[a, b]` at which a continuous function takes a value in a closed set. -/
theorem l41_exists_last {f : ℝ → ℝ} {a b : ℝ} {F : Set ℝ} (hF : IsClosed F)
    (hf : ContinuousOn f (Icc a b)) {t₁ : ℝ} (ht₁ : t₁ ∈ Icc a b) (hft₁ : f t₁ ∈ F) :
    ∃ t₀ ∈ Icc a b, f t₀ ∈ F ∧ ∀ t ∈ Ioc t₀ b, f t ∉ F := by
  have hcl : IsClosed (Icc a b ∩ f ⁻¹' F) := hf.preimage_isClosed_of_isClosed isClosed_Icc hF
  have hcpt : IsCompact (Icc a b ∩ f ⁻¹' F) :=
    isCompact_Icc.of_isClosed_subset hcl inter_subset_left
  obtain ⟨t₀, ⟨ht₀, hft₀⟩, hmax⟩ := hcpt.exists_isGreatest ⟨t₁, ht₁, hft₁⟩
  refine ⟨t₀, ht₀, hft₀, fun t ht hft => ?_⟩
  have hle : t ≤ t₀ := hmax ⟨⟨ht₀.1.trans ht.1.le, ht.2⟩, hft⟩
  exact absurd ht.1 (not_lt.mpr hle)

/-- The first time in `[a, b]` at which a continuous function takes a value in a closed set. -/
theorem l41_exists_first {f : ℝ → ℝ} {a b : ℝ} {F : Set ℝ} (hF : IsClosed F)
    (hf : ContinuousOn f (Icc a b)) {t₁ : ℝ} (ht₁ : t₁ ∈ Icc a b) (hft₁ : f t₁ ∈ F) :
    ∃ t₀ ∈ Icc a b, f t₀ ∈ F ∧ ∀ t ∈ Ico a t₀, f t ∉ F := by
  have hcl : IsClosed (Icc a b ∩ f ⁻¹' F) := hf.preimage_isClosed_of_isClosed isClosed_Icc hF
  have hcpt : IsCompact (Icc a b ∩ f ⁻¹' F) :=
    isCompact_Icc.of_isClosed_subset hcl inter_subset_left
  obtain ⟨t₀, ⟨ht₀, hft₀⟩, hmin⟩ := hcpt.exists_isLeast ⟨t₁, ht₁, hft₁⟩
  refine ⟨t₀, ht₀, hft₀, fun t ht hft => ?_⟩
  have hle : t₀ ≤ t := hmin ⟨⟨ht.1, ht.2.le.trans ht₀.2⟩, hft⟩
  exact absurd ht.2 (not_lt.mpr hle)

/-- A closed condition holding on `(a, b]` holds at `a` (continuity from the right). -/
theorem l41_mem_of_Ioc {f : ℝ → ℝ} {a b : ℝ} {F : Set ℝ} (hF : IsClosed F) (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (h : ∀ t ∈ Ioc a b, f t ∈ F) : f a ∈ F := by
  have hcw : ContinuousWithinAt f (Ioc a b) a :=
    (hf a ⟨le_rfl, hab.le⟩).mono Ioc_subset_Icc_self
  have hcl : a ∈ closure (Ioc a b) := by
    rw [closure_Ioc hab.ne]
    exact ⟨le_rfl, hab.le⟩
  have h2 : f '' Ioc a b ⊆ F := by
    rintro _ ⟨t, ht, rfl⟩
    exact h t ht
  exact (hF.closure_subset_iff.mpr h2) (hcw.mem_closure_image hcl)

/-- A closed condition holding on `[a, b)` holds at `b` (continuity from the left). -/
theorem l41_mem_of_Ico {f : ℝ → ℝ} {a b : ℝ} {F : Set ℝ} (hF : IsClosed F) (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (h : ∀ t ∈ Ico a b, f t ∈ F) : f b ∈ F := by
  have hcw : ContinuousWithinAt f (Ico a b) b :=
    (hf b ⟨hab.le, le_rfl⟩).mono Ico_subset_Icc_self
  have hcl : b ∈ closure (Ico a b) := by
    rw [closure_Ico hab.ne]
    exact ⟨hab.le, le_rfl⟩
  have h2 : f '' Ico a b ⊆ F := by
    rintro _ ⟨t, ht, rfl⟩
    exact h t ht
  exact (hF.closure_subset_iff.mpr h2) (hcw.mem_closure_image hcl)

/-- The distance of a Euclidean-continuous path to a fixed point is continuous. -/
theorem l41_continuousOn_dist {P : ℝ → ℂ} {a b : ℝ} (hP : ContinuousOn P (Icc a b)) (c : ℂ) :
    ContinuousOn (fun t => dist (P t) c) (Icc a b) :=
  continuous_dist.comp_continuousOn (hP.prodMk continuousOn_const)

/-- **The segment `J` of Lemma 4.1** (paper l. 410–413, SB2 D6 step 2): if the endpoints `z = P 0`, `w = P L` are at
distance `> 2ρ`, there are `0 < a₀ < b₀ ≤ L` with `|P a₀ − z| ≤ ρ`, `|P b₀ − w| ≤ ρ`, and `P` at distance `≥ ρ` from
both endpoints on `[a₀, b₀]`. -/
theorem l41_J_exists {P : ℝ → ℂ} {L ρ : ℝ} (hP : ContinuousOn P (Icc 0 L)) (hL : 0 ≤ L)
    (hρ : 0 < ρ) (hfar : 2 * ρ < dist (P 0) (P L)) :
    ∃ a₀ b₀ : ℝ, 0 < a₀ ∧ a₀ < b₀ ∧ b₀ ≤ L ∧ dist (P a₀) (P 0) ≤ ρ ∧ dist (P b₀) (P L) ≤ ρ ∧
      ∀ t ∈ Icc a₀ b₀, ρ ≤ dist (P t) (P 0) ∧ ρ ≤ dist (P t) (P L) := by
  -- `b₀`: the first hit of the closed ball of radius `ρ` around `w`
  obtain ⟨b₀, hb₀, hfb₀, hbefore⟩ := l41_exists_first (F := Iic ρ) isClosed_Iic
    (l41_continuousOn_dist hP (P L)) ⟨hL, le_rfl⟩ (by simp [hρ.le])
  have hb₀le : dist (P b₀) (P L) ≤ ρ := hfb₀
  have hbefore' : ∀ t ∈ Ico 0 b₀, ρ < dist (P t) (P L) := fun t ht =>
    lt_of_not_ge (hbefore t ht)
  have hb₀pos : 0 < b₀ := by
    rcases eq_or_lt_of_le hb₀.1 with h | h
    · rw [← h] at hb₀le
      linarith
    · exact h
  have hb₀ge : ρ ≤ dist (P b₀) (P L) := l41_mem_of_Ico (f := fun t => dist (P t) (P L))
    (F := Ici ρ) isClosed_Ici hb₀pos
    (l41_continuousOn_dist (hP.mono (Icc_subset_Icc le_rfl hb₀.2)) (P L))
    (fun t ht => (hbefore' t ht).le)
  -- `a₀`: the last visit to the closed ball of radius `ρ` around `z` before `b₀`
  have hPb : ContinuousOn P (Icc 0 b₀) := hP.mono (Icc_subset_Icc le_rfl hb₀.2)
  obtain ⟨a₀, ha₀, hga₀, hafter⟩ := l41_exists_last (F := Iic ρ) isClosed_Iic
    (l41_continuousOn_dist hPb (P 0)) ⟨le_rfl, hb₀pos.le⟩ (by simp [hρ.le])
  have ha₀le : dist (P a₀) (P 0) ≤ ρ := hga₀
  have hafter' : ∀ t ∈ Ioc a₀ b₀, ρ < dist (P t) (P 0) := fun t ht => lt_of_not_ge (hafter t ht)
  have hb₀z : ρ < dist (P b₀) (P 0) := by
    have htri := dist_triangle (P 0) (P b₀) (P L)
    rw [dist_comm (P 0) (P b₀)] at htri
    linarith
  have ha₀b₀ : a₀ < b₀ := by
    rcases eq_or_lt_of_le ha₀.2 with h | h
    · rw [h] at ha₀le
      linarith
    · exact h
  have ha₀ge : ρ ≤ dist (P a₀) (P 0) := l41_mem_of_Ioc (f := fun t => dist (P t) (P 0))
    (F := Ici ρ) isClosed_Ici ha₀b₀
    (l41_continuousOn_dist (hPb.mono (Icc_subset_Icc ha₀.1 le_rfl)) (P 0))
    (fun t ht => (hafter' t ht).le)
  have ha₀pos : 0 < a₀ := by
    rcases eq_or_lt_of_le ha₀.1 with h | h
    · rw [← h, dist_self] at ha₀ge
      linarith
    · exact h
  refine ⟨a₀, b₀, ha₀pos, ha₀b₀, hb₀.2, ha₀le, hb₀le, fun t ht => ⟨?_, ?_⟩⟩
  · rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]
      exact ha₀ge
    · exact (hafter' t ⟨h, ht.2⟩).le
  · rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h]
      exact hb₀ge
    · exact (hbefore' t ⟨ha₀pos.le.trans ht.1, h⟩).le

/-- **The excursion `I_τ` and the crossing `G_τ`** (paper l. 414–420, SB2 D6 steps 3 and 5). Let `|P τ − c| < r`, and
let both endpoints of the path be at distance `≥ 8r` from `c`. Then there are times
`0 < α < τ ≤ s < t < β < L` with `|P α − c| = |P β − c| = 6r`, `P([α, β]) ⊆ B̄_{6r}(c)`, `|P s − c| = r`,
`|P t − c| = 2r` and `P([s, t]) ⊆ Ā_{r,2r}(c)`. -/
theorem l41_excursion {P : ℝ → ℂ} {L τ r : ℝ} {c : ℂ} (hP : ContinuousOn P (Icc 0 L))
    (hr : 0 < r) (hτ : τ ∈ Icc 0 L) (hτc : dist (P τ) c < r) (h0 : 8 * r ≤ dist (P 0) c)
    (hLc : 8 * r ≤ dist (P L) c) :
    ∃ α β s t : ℝ, 0 < α ∧ α < τ ∧ τ ≤ s ∧ s < t ∧ t < β ∧ β < L ∧
      dist (P α) c = 6 * r ∧ dist (P β) c = 6 * r ∧ dist (P s) c = r ∧ dist (P t) c = 2 * r ∧
      (∀ u ∈ Icc α β, dist (P u) c ≤ 6 * r) ∧
      (∀ u ∈ Icc s t, r ≤ dist (P u) c ∧ dist (P u) c ≤ 2 * r) := by
  have hf : ContinuousOn (fun u => dist (P u) c) (Icc 0 L) := l41_continuousOn_dist hP c
  have hsub : ∀ {x y : ℝ}, 0 ≤ x → y ≤ L → ContinuousOn (fun u => dist (P u) c) (Icc x y) :=
    fun hx hy => hf.mono (Icc_subset_Icc hx hy)
  -- `α`: the last time before `τ` at distance `≥ 6r`
  obtain ⟨α, hα, hfα, hαafter⟩ := l41_exists_last (F := Ici (6 * r)) isClosed_Ici
    (hsub le_rfl hτ.2) ⟨le_rfl, hτ.1⟩ (show 6 * r ≤ dist (P 0) c by linarith)
  have hαafter' : ∀ u ∈ Ioc α τ, dist (P u) c < 6 * r := fun u hu =>
    lt_of_not_ge (hαafter u hu)
  have hατ : α < τ := by
    rcases eq_or_lt_of_le hα.2 with h | h
    · have hfα' : 6 * r ≤ dist (P α) c := hfα
      rw [h] at hfα'
      linarith
    · exact h
  have hαle : dist (P α) c ≤ 6 * r := l41_mem_of_Ioc (f := fun u => dist (P u) c)
    (F := Iic (6 * r)) isClosed_Iic hατ
    (hsub hα.1 hτ.2) (fun u hu => (hαafter' u hu).le)
  have hαeq : dist (P α) c = 6 * r := le_antisymm hαle hfα
  have hαpos : 0 < α := by
    rcases eq_or_lt_of_le hα.1 with h | h
    · rw [← h] at hαeq
      linarith
    · exact h
  -- `β`: the first time after `τ` at distance `≥ 6r`
  obtain ⟨β, hβ, hfβ, hβbefore⟩ := l41_exists_first (F := Ici (6 * r)) isClosed_Ici
    (hsub hτ.1 le_rfl) ⟨hτ.2, le_rfl⟩ (show 6 * r ≤ dist (P L) c by linarith)
  have hβbefore' : ∀ u ∈ Ico τ β, dist (P u) c < 6 * r := fun u hu =>
    lt_of_not_ge (hβbefore u hu)
  have hτβ : τ < β := by
    rcases eq_or_lt_of_le hβ.1 with h | h
    · have hfβ' : 6 * r ≤ dist (P β) c := hfβ
      rw [← h] at hfβ'
      linarith
    · exact h
  have hβle : dist (P β) c ≤ 6 * r := l41_mem_of_Ico (f := fun u => dist (P u) c)
    (F := Iic (6 * r)) isClosed_Iic hτβ
    (hsub hτ.1 hβ.2) (fun u hu => (hβbefore' u hu).le)
  have hβeq : dist (P β) c = 6 * r := le_antisymm hβle hfβ
  have hβL : β < L := by
    rcases eq_or_lt_of_le hβ.2 with h | h
    · rw [h] at hβeq
      linarith
    · exact h
  -- `t`: the first time after `τ` at distance `≥ 2r`
  obtain ⟨t, ht, hft, htbefore⟩ := l41_exists_first (F := Ici (2 * r)) isClosed_Ici
    (hsub hτ.1 hβ.2) ⟨hτβ.le, le_rfl⟩ (show 2 * r ≤ dist (P β) c by linarith)
  have htbefore' : ∀ u ∈ Ico τ t, dist (P u) c < 2 * r := fun u hu =>
    lt_of_not_ge (htbefore u hu)
  have hτt : τ < t := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · have hft' : 2 * r ≤ dist (P t) c := hft
      rw [← h] at hft'
      linarith
    · exact h
  have htle : dist (P t) c ≤ 2 * r := l41_mem_of_Ico (f := fun u => dist (P u) c)
    (F := Iic (2 * r)) isClosed_Iic hτt
    (hsub hτ.1 (ht.2.trans hβ.2)) (fun u hu => (htbefore' u hu).le)
  have hteq : dist (P t) c = 2 * r := le_antisymm htle hft
  have htβ : t < β := by
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h] at hteq
      linarith
    · exact h
  -- `s`: the last time before `t` at distance `≤ r`
  obtain ⟨s, hs, hfs, hsafter⟩ := l41_exists_last (F := Iic r) isClosed_Iic
    (hsub hτ.1 (ht.2.trans hβ.2)) ⟨le_rfl, hτt.le⟩ (show dist (P τ) c ≤ r from hτc.le)
  have hsafter' : ∀ u ∈ Ioc s t, r < dist (P u) c := fun u hu => lt_of_not_ge (hsafter u hu)
  have hst : s < t := by
    rcases eq_or_lt_of_le hs.2 with h | h
    · have hfs' : dist (P s) c ≤ r := hfs
      rw [h] at hfs'
      linarith
    · exact h
  have hsge : r ≤ dist (P s) c := l41_mem_of_Ioc (f := fun u => dist (P u) c)
    (F := Ici r) isClosed_Ici hst
    (hsub (hτ.1.trans hs.1) (ht.2.trans hβ.2)) (fun u hu => (hsafter' u hu).le)
  have hseq : dist (P s) c = r := le_antisymm hfs hsge
  refine ⟨α, β, s, t, hαpos, hατ, hs.1, hst, htβ, hβL, hαeq, hβeq, hseq, hteq, ?_, ?_⟩
  · intro u hu
    by_cases huτ : u ≤ τ
    · rcases eq_or_lt_of_le hu.1 with h | h
      · rw [← h, hαeq]
      · exact (hαafter' u ⟨h, huτ⟩).le
    · rcases eq_or_lt_of_le hu.2 with h | h
      · rw [h, hβeq]
      · exact (hβbefore' u ⟨(lt_of_not_ge huτ).le, h⟩).le
  · intro u hu
    constructor
    · rcases eq_or_lt_of_le hu.1 with h | h
      · rw [← h, hseq]
      · exact (hsafter' u ⟨h, hu.2⟩).le
    · rcases eq_or_lt_of_le hu.2 with h | h
      · rw [h, hteq]
      · exact (htbefore' u ⟨hs.1.trans hu.1, h⟩).le

end SupercriticalLFPPAS.Contraction
