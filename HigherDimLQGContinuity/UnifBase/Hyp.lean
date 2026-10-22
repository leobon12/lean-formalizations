import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Param.Lipschitz
import HigherDimLQGMetric.Main.ExponentBridge
import HigherDimLQGMetric.DGZ.TightBasics

/-!
# The uniform hypothesis, the parameter sets `S(b, μ)` and compact subcritical sets (packet U0)

Blueprint Part D, `d:def-param`, `d:lem-uhyp`, `d:lem-reduce` (NA3 R2(g), R3, ROUTE-4; rulings N3, N8). With
`Q = distExp d`, `ϕ = phiXi d` (PAR) and the gap `gapXi d ξ = ϕ(ξ) - √(2d) ξ`:

* `uSbm d b μ = S(b, μ) = {ξ ∈ (0, b] : ξ (Q(ξ) - √(2d)) ≥ μ}` (`mem_uSbm_iff_gapXi`: the gap form);
* `IsSubcritCompact d J` (NA3 Details (d), verbatim): `J` compact, `J ⊆ [0, ∞)`, every positive point subcritical;
* `uHyp_iff` (`d:lem-uhyp`(a)): for `d ≥ 2`, an admissible kernel and `μ > 0`, `UHyp d κ b μ ξ ↔ ξ ∈ S(b, μ)`;
* `UHyp.distExp_ge_qStar`, `UHyp.mu_le_one`, `UHyp.mu_le_phi`, `UHyp.phi_le` (`d:lem-uhyp`(b), and the upper bound
  `ϕ ≤ 1 + √(2d) b` from PAR's `phiXi_le_one_add_sqrt_mul`, ruling N8: `L_ϕ = √(2d)`);
* `exists_bMu_of_isSubcritCompact` (`d:lem-reduce`): `J ∩ (0, ∞) ⊆ S(b, μ)` with `b = max 1 (sup J)` and
  `μ = min 1 (gap(sup J))` — the gap is antitone (PAR's `gapXi_antitone`), so its minimum on `J` is at `sup J`; and
  `mu_le_gap_of_le_small`: `(0, b'] ⊆ S(b', μ')` for `0 < μ' < 1`, `b' ≤ (1 - μ')/(2√(2d))`.

`uQstar d b μ = √(2d) + μ/b` (the `Q_*` of (A.7)) is defined here because `d:lem-uhyp`(b) uses it; the rest of the
constant package is in `UnifBase/Consts.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd IsLFPPKernel)

variable {d : ℕ}

/-! ### Definitions -/

/-- The parameter set `S(b, μ) = {ξ ∈ (0, b] : ξ (Q(ξ) - √(2d)) ≥ μ}` of Part D (`d:def-param`, NA3 ROUTE-4). -/
def uSbm (d : ℕ) (b μ : ℝ) : Set ℝ :=
  {ξ | 0 < ξ ∧ ξ ≤ b ∧ μ ≤ ξ * (distExp d ξ - Real.sqrt (2 * d))}

/-- A compact subcritical parameter set (`d:def-param`; NA3 Details (d) verbatim): `J` is compact, `J ⊆ [0, ∞)`, and
`√(2d) < Q(ξ)` at every positive `ξ ∈ J`. No interval structure of the subcritical set is assumed (ED4). -/
def IsSubcritCompact (d : ℕ) (J : Set ℝ) : Prop :=
  IsCompact J ∧ (∀ ξ ∈ J, 0 ≤ ξ) ∧ ∀ ξ ∈ J, 0 < ξ → Real.sqrt (2 * d) < distExp d ξ

/-- `Q_* = √(2d) + μ/b`, the lower bound of `Q` on `S(b, μ)` ((A.7), `d:lem-uhyp`(b), `d:lem-consts`). -/
def uQstar (d : ℕ) (b μ : ℝ) : ℝ := Real.sqrt (2 * d) + μ / b

/-! ### `S(b, μ)` -/

theorem mem_uSbm {b μ ξ : ℝ} :
    ξ ∈ uSbm d b μ ↔ 0 < ξ ∧ ξ ≤ b ∧ μ ≤ ξ * (distExp d ξ - Real.sqrt (2 * d)) :=
  Iff.rfl

/-- The gap form of `S(b, μ)`: `{ξ ∈ (0, b] : gap(ξ) ≥ μ}`. -/
theorem mem_uSbm_iff_gapXi {b μ ξ : ℝ} : ξ ∈ uSbm d b μ ↔ 0 < ξ ∧ ξ ≤ b ∧ μ ≤ gapXi d ξ := by
  constructor
  · rintro ⟨hξ, hb, hg⟩
    exact ⟨hξ, hb, by rwa [gapXi_of_pos hξ]⟩
  · rintro ⟨hξ, hb, hg⟩
    exact ⟨hξ, hb, by rwa [gapXi_of_pos hξ] at hg⟩

/-- Points of `S(b, μ)` with `μ > 0` are subcritical. -/
theorem sqrt_lt_distExp_of_mem_uSbm {b μ ξ : ℝ} (hμ : 0 < μ) (h : ξ ∈ uSbm d b μ) :
    Real.sqrt (2 * d) < distExp d ξ := by
  obtain ⟨hξ, -, hg⟩ := h
  have hpos : 0 < ξ * (distExp d ξ - Real.sqrt (2 * d)) := hμ.trans_le hg
  have := (mul_pos_iff_of_pos_left hξ).1 hpos
  linarith

/-! ### `d:lem-uhyp` -/

/-- **`d:lem-uhyp`(a)**: for `d ≥ 2`, an admissible kernel and `μ > 0`, the uniform hypothesis is membership in
`S(b, μ)` (`l10a_dgzHyp` supplies `DGZHyp` at `Q(ξ)` for every positive subcritical `ξ`). -/
theorem uHyp_iff (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ ξ : ℝ} (hμ : 0 < μ) :
    UHyp d κ b μ ξ ↔ ξ ∈ uSbm d b μ := by
  constructor
  · intro h
    exact ⟨h.base.xi_pos, h.le_b, h.gap⟩
  · intro h
    exact ⟨l10a_dgzHyp hd hκ h.1 (sqrt_lt_distExp_of_mem_uSbm hμ h), h.2.1, h.2.2⟩

theorem UHyp.xi_pos {κ : Rd d → ℝ} {b μ ξ : ℝ} (h : UHyp d κ b μ ξ) : 0 < ξ :=
  h.base.xi_pos

theorem UHyp.dim {κ : Rd d → ℝ} {b μ ξ : ℝ} (h : UHyp d κ b μ ξ) : 2 ≤ d :=
  h.base.dim

theorem UHyp.b_pos {κ : Rd d → ℝ} {b μ ξ : ℝ} (h : UHyp d κ b μ ξ) : 0 < b :=
  h.xi_pos.trans_le h.le_b

theorem UHyp.mem_uSbm {κ : Rd d → ℝ} {b μ ξ : ℝ} (h : UHyp d κ b μ ξ) : ξ ∈ uSbm d b μ :=
  ⟨h.xi_pos, h.le_b, h.gap⟩

/-- **`d:lem-uhyp`(b)**, first claim: `Q(ξ) ≥ Q_* = √(2d) + μ/b` on `S(b, μ)` (no sign condition on `μ` is needed:
`Q(ξ) > √(2d)` is part of `DGZHyp`). -/
theorem UHyp.distExp_ge_qStar {κ : Rd d → ℝ} {b μ ξ : ℝ} (h : UHyp d κ b μ ξ) :
    uQstar d b μ ≤ distExp d ξ := by
  have hξ := h.xi_pos
  have hb := h.b_pos
  have hsub := h.base.subcritical
  unfold uQstar
  rcases le_or_gt μ 0 with hμ | hμ
  · have : μ / b ≤ 0 := div_nonpos_of_nonpos_of_nonneg hμ hb.le
    linarith
  · have h1 : μ / b ≤ μ / ξ := div_le_div_of_nonneg_left hμ.le hξ h.le_b
    have h2 : μ / ξ ≤ distExp d ξ - Real.sqrt (2 * d) := by
      rw [div_le_iff₀ hξ]
      linarith [h.gap]
    linarith

/-- **`d:lem-uhyp`(b)**, last claim: `μ ≤ ξ (Q(ξ) - √(2d)) ≤ 1` (`DGZ.xi_mul_sub_sqrt_le_one`); in particular
`S(b, μ) = ∅` for `μ > 1`. -/
theorem UHyp.mu_le_one {κ : Rd d → ℝ} {b μ ξ : ℝ} (h : UHyp d κ b μ ξ) : μ ≤ 1 :=
  h.gap.trans (DGZ.xi_mul_sub_sqrt_le_one h.base)

/-- `ξ (Q(ξ) - √(2d)) ≤ 1` under the uniform hypothesis. -/
theorem UHyp.gap_le_one {κ : Rd d → ℝ} {b μ ξ : ℝ} (h : UHyp d κ b μ ξ) :
    ξ * (distExp d ξ - Real.sqrt (2 * d)) ≤ 1 :=
  DGZ.xi_mul_sub_sqrt_le_one h.base

/-- **`d:lem-uhyp`(b)**, second claim: `ϕ(ξ) = ξ Q(ξ) ≥ μ`. -/
theorem UHyp.mu_le_phi {κ : Rd d → ℝ} {b μ ξ : ℝ} (h : UHyp d κ b μ ξ) : μ ≤ ξ * distExp d ξ := by
  have hξ := h.xi_pos
  have h0 : 0 ≤ ξ * Real.sqrt (2 * d) := mul_nonneg hξ.le (Real.sqrt_nonneg _)
  have e : ξ * distExp d ξ = ξ * (distExp d ξ - Real.sqrt (2 * d)) + ξ * Real.sqrt (2 * d) := by ring
  rw [e]
  linarith [h.gap]

/-- `ϕ(ξ) ≤ 1 + √(2d) b` on `S(b, μ)` (PAR's `phiXi_le_one_add_sqrt_mul`; ruling N8, `L_ϕ = √(2d)`). -/
theorem UHyp.phi_le {κ : Rd d → ℝ} {b μ ξ : ℝ} (h : UHyp d κ b μ ξ) :
    ξ * distExp d ξ ≤ 1 + Real.sqrt (2 * d) * b := by
  have hξ := h.xi_pos
  have h1 := phiXi_le_one_add_sqrt_mul h.dim hξ.le
  rw [phiXi_of_pos hξ] at h1
  have h2 : Real.sqrt (2 * d) * ξ ≤ Real.sqrt (2 * d) * b :=
    mul_le_mul_of_nonneg_left h.le_b (Real.sqrt_nonneg _)
  linarith

/-- `ξ (Q(ξ) - √(2d)) ≤ 1` for every `ξ > 0` (`d ≥ 2`): the gap is antitone with `gap(0) = 1` (PAR's
`gapXi_antitone`); no kernel and no subcriticality are needed (compare `DGZ.xi_mul_sub_sqrt_le_one`). -/
theorem xi_mul_sub_sqrt_le_one_of_pos (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) :
    ξ * (distExp d ξ - Real.sqrt (2 * d)) ≤ 1 := by
  rw [← gapXi_of_pos hξ]
  calc gapXi d ξ ≤ gapXi d 0 := gapXi_antitone hd hξ.le
    _ = 1 := gapXi_zero d

/-- `μ ≤ 1` on `S(b, μ)` (`d:lem-uhyp`(b), set form). -/
theorem mu_le_one_of_mem_uSbm (hd : 2 ≤ d) {b μ ξ : ℝ} (h : ξ ∈ uSbm d b μ) : μ ≤ 1 :=
  h.2.2.trans (xi_mul_sub_sqrt_le_one_of_pos hd h.1)

/-- **`d:lem-uhyp`**, last sentence: `S(b, μ) = ∅` if `μ > 1`. -/
theorem uSbm_eq_empty_of_one_lt (hd : 2 ≤ d) {b μ : ℝ} (hμ : 1 < μ) : uSbm d b μ = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ h => absurd (mu_le_one_of_mem_uSbm hd h) (not_le.2 hμ)

/-! ### `d:lem-reduce` -/

/-- **`d:lem-reduce`** (NA3 R2(g), R3): every compact subcritical set reduces to `S(b, μ)`. With `b = max 1 (sup J)`
and `μ = min 1 (gap(sup J))` (`gap` is antitone, so its minimum on `J` is at `sup J`, and it is positive there:
`gap(0) = 1`, and `gap > 0` at positive subcritical points): `1 ≤ b`, `0 < μ ≤ 1`, every `ξ ∈ J` has `ξ ≤ b` and
`μ ≤ gap(ξ)`, and `J ∩ (0, ∞) ⊆ S(b, μ)`. -/
theorem exists_bMu_of_isSubcritCompact (hd : 2 ≤ d) {J : Set ℝ} (hJ : IsSubcritCompact d J) :
    ∃ b μ : ℝ, 1 ≤ b ∧ 0 < μ ∧ μ ≤ 1 ∧ (∀ ξ ∈ J, ξ ≤ b ∧ μ ≤ gapXi d ξ) ∧
      ∀ ξ ∈ J, 0 < ξ → ξ ∈ uSbm d b μ := by
  obtain ⟨hcpt, hnn, hsub⟩ := hJ
  set m : ℝ := sSup J with hm
  -- the gap is positive at `m = sup J`
  have hgm : 0 < gapXi d m := by
    rcases J.eq_empty_or_nonempty with hJe | hJne
    · rw [hm, hJe, Real.sSup_empty, gapXi_zero]
      exact one_pos
    · have hmJ : m ∈ J := hcpt.sSup_mem hJne
      rcases (hnn m hmJ).lt_or_eq with hm0 | hm0
      · rw [gapXi_of_pos hm0]
        exact mul_pos hm0 (by linarith [hsub m hmJ hm0])
      · rw [← hm0, gapXi_zero]
        exact one_pos
  have hle : ∀ ξ ∈ J, ξ ≤ m := fun ξ hξ => le_csSup hcpt.bddAbove hξ
  refine ⟨max 1 m, min 1 (gapXi d m), le_max_left _ _, lt_min one_pos hgm, min_le_left _ _, ?_, ?_⟩
  · intro ξ hξ
    exact ⟨(hle ξ hξ).trans (le_max_right _ _),
      (min_le_right _ _).trans (gapXi_antitone hd (hle ξ hξ))⟩
  · intro ξ hξ hξ0
    refine mem_uSbm_iff_gapXi.2 ⟨hξ0, (hle ξ hξ).trans (le_max_right _ _), ?_⟩
    exact (min_le_right _ _).trans (gapXi_antitone hd (hle ξ hξ))

/-- **`d:lem-reduce`**, last claim (with `L_ϕ = √(2d)`, ruling N8): if `b' ≤ (1 - μ')/(2√(2d))` (the claim is about
`μ' ∈ (0, 1)` and `b' > 0`; otherwise `(0, b']` is empty), every `ξ ∈ (0, b']` has gap `≥ μ'`, so
`(0, b'] ⊆ S(b', μ')` (`gap(ξ) ≥ 1 - 2√(2d) ξ`: PAR's `one_sub_sqrt_mul_le_phiXi`). -/
theorem mu_le_gap_of_le_small (hd : 2 ≤ d) {b' μ' ξ : ℝ}
    (hb' : b' ≤ (1 - μ') / (2 * Real.sqrt (2 * d))) (hξ : 0 < ξ) (hξb : ξ ≤ b') :
    ξ ∈ uSbm d b' μ' := by
  have hs : 0 < Real.sqrt (2 * d) := Real.sqrt_pos.2 (by positivity)
  refine mem_uSbm_iff_gapXi.2 ⟨hξ, hξb, ?_⟩
  have h1 := one_sub_sqrt_mul_le_phiXi hd hξ.le
  have h2 : 2 * Real.sqrt (2 * d) * b' ≤ 1 - μ' := by
    rw [le_div_iff₀ (by positivity)] at hb'
    linarith
  have h3 : Real.sqrt (2 * d) * ξ ≤ Real.sqrt (2 * d) * b' := mul_le_mul_of_nonneg_left hξb hs.le
  unfold gapXi
  linarith

/-- `(0, b'] ⊆ S(b', μ')` in set form (`d:lem-reduce`, last claim). -/
theorem Ioc_subset_uSbm (hd : 2 ≤ d) {b' μ' : ℝ} (hb' : b' ≤ (1 - μ') / (2 * Real.sqrt (2 * d))) :
    Ioc 0 b' ⊆ uSbm d b' μ' :=
  fun _ hξ => mu_le_gap_of_le_small hd hb' hξ.1 hξ.2

/-- NA3's `PhiFacts d` (Details (d)), written out (no `PhiFacts` definition is frozen; ruling N8: the Lipschitz half
is PAR's `phiXi_lipschitz` with `L = √(2d)`, the gap half is `exists_bMu_of_isSubcritCompact`): `ϕ` is Lipschitz on
`[0, ∞)`, and the gap is bounded below by a positive constant on every compact subcritical set. -/
theorem phiFacts (hd : 2 ≤ d) :
    (∃ L : ℝ, 0 ≤ L ∧ ∀ ξ η : ℝ, 0 ≤ ξ → 0 ≤ η → |phiXi d ξ - phiXi d η| ≤ L * |ξ - η|) ∧
      ∀ J : Set ℝ, IsSubcritCompact d J → ∃ μ : ℝ, 0 < μ ∧ ∀ ξ ∈ J, μ ≤ gapXi d ξ := by
  refine ⟨⟨Real.sqrt (2 * d), Real.sqrt_nonneg _, fun ξ η _ _ => phiXi_lipschitz hd ξ η⟩,
    fun J hJ => ?_⟩
  obtain ⟨b, μ, -, hμ, -, hJ', -⟩ := exists_bMu_of_isSubcritCompact hd hJ
  exact ⟨μ, hμ, fun ξ hξ => (hJ' ξ hξ).2⟩

/-- The uniform hypothesis on a compact subcritical set (`d:lem-reduce` + `d:lem-uhyp`(a)): one pair `(b, μ)` with
`1 ≤ b` and `0 < μ ≤ 1` such that `UHyp d κ b μ ξ` at every positive `ξ ∈ J`, for every admissible kernel. -/
theorem exists_uHyp_of_isSubcritCompact (hd : 2 ≤ d) {J : Set ℝ} (hJ : IsSubcritCompact d J) :
    ∃ b μ : ℝ, 1 ≤ b ∧ 0 < μ ∧ μ ≤ 1 ∧ ∀ κ : Rd d → ℝ, IsLFPPKernel κ →
      ∀ ξ ∈ J, 0 < ξ → UHyp d κ b μ ξ := by
  obtain ⟨b, μ, hb, hμ, hμ1, -, hJS⟩ := exists_bMu_of_isSubcritCompact hd hJ
  exact ⟨b, μ, hb, hμ, hμ1, fun κ hκ ξ hξ hξ0 => (uHyp_iff hd hκ hμ).2 (hJS ξ hξ hξ0)⟩

end HigherDimLQGContinuity
