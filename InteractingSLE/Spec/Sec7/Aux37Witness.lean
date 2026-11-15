/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripPocketPathFinal

/-!
# Aux. lemma 37 at one rational witness: the deterministic part

Packet PROVE-STRIPSYS34 (first part). Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md` L80–L136,
pp. 197–200) in the repaired form of ruling R41 (`source/external/AstraIG1/ig1_ztip_elimination.txt` L185–L207), and
Aux. lemma 43 (L284–L296, pp. 207–208).

PROVE-STRIPSYS31 reduced the attachment constancy of the strip pocket to the exclusion of every rational witness
(`hwit`/`hwitI`, `StripPocketPath.IsPocketWitness`/`…Inf`). The source excludes a witness by a field comparison: at the
witness, "the compact arc `J = α_i([v₁, v₂])` is disjoint from `R_r`, is contained in `R_{T_v}`, and never loses its
incident `C`-side collar to new range"; the unchanged central mean has the flow-side germ `ελ − θχ + 2πk_fχ` and the
counterflow-side germ `ελ′ − πχ + 2πk_cχ` on that collar ((PFI2)–(PFI3)); the two cannot agree ((PFI4)).

This file proves the deterministic content of that argument:

* **The phase contradiction with the side sign** (`phase_ne_of_side`, `false_of_side_germs_of_side`): the germs differ
  for `ε = 1` (the collar on the right of the oriented incoming arc) whenever `θ ∈ (−π/2, π/2]`, and for `ε = −1` (on
  the left) whenever `θ ∈ [−π/2, π/2)`. The landed `Aux37Attach.false_of_side_germs` needs `θ ∈ (−π/2, π/2)`; with the
  side known, the extremal angle on the far side is excluded as well. In the strip pocket the pocket lies on the left
  of the right wall `α` (`ε = −1`; angles `−π/2`, `θ₁`) and on the right of the left wall `β^{(q)}` (`ε = 1`; angles
  `π/2`, `θ₂`), so the phase comparison excludes witnesses on **every** angle piece, including the extremal initial
  pieces, as soon as `θ₂ ≠ −π/2` (`strip_side_phase_ne`). The source treats extremal pieces by Aux. lemma 43 (global
  frontier confinement plus Aux. lemma 42); with the side signs of this configuration that detour is not needed.
* **The witness collar** (`IsAttachWitness.collar`): in a reverse-contained pocket, at a witness `(r, s, v, v₁, v₂)` on
  the side `α`, the first visit `T ∈ (r, s]` of `α(v)` is fresh, every `α(x)`, `x ∈ [v, 1]`, is visited by `T`, the arc
  `α([v, v₂])` keeps a positive distance `δ` from the range `R_r`, the visited part of the pocket does not change on
  `[r, s]` (`C ∩ R_t = C ∩ R_r`), and every point of `α([v, v₂])` has a ball whose pocket part is not visited by time
  `s` — the source's three collar properties. The same at the junction `∞` (`IsAttachWitnessInf.collar`: arms from
  `y₀`, last-visit attachments, the fresh point `α(v₂)`).
* **One angle piece** (`IsPocketWitness.disc_lt_or_gt`): the disc parameters of a strip-pocket witness lie on one side
  of the change point of its wall.

What remains for `hwit`/`hwitI` is the field statement (the flat clock of the central mean on `[r, s]` and the two germ
identifications, Aux. lemmas 34–36); see the handoff `planning/handoffs/PROVE-STRIPSYS34.md`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped NNReal

namespace InteractingSLE.Sec7.Aux37Witness

open Sec6 Aux37Attach

/-! ### The phase contradiction with the side sign -/

section Phase

/-- **(PFI4) with the side sign** (p. 200): for `χ > 0`, `λ − λ' = πχ/2`, the flow-side germ `ελ − θχ + 2πk_fχ` and
the counterflow-side germ `ελ' − πχ + 2πk_cχ` differ when `ε = 1` and `θ ∈ (−π/2, π/2]`, or `ε = −1` and
`θ ∈ [−π/2, π/2)`. -/
theorem phase_ne_of_side {χ lam lam' ε θ : ℝ} (hχ : 0 < χ) (hlam : lam - lam' = π * χ / 2)
    (hside : (ε = 1 ∧ θ ∈ Ioc (-(π / 2)) (π / 2)) ∨ (ε = -1 ∧ θ ∈ Ico (-(π / 2)) (π / 2))) (kf kc : ℤ) :
    ε * lam - θ * χ + 2 * π * kf * χ ≠ ε * lam' - π * χ + 2 * π * kc * χ := by
  intro heq
  have hπ := Real.pi_pos
  have hdiff : χ * (ε * (π / 2) + π - θ + 2 * π * ((kf : ℝ) - kc)) = 0 := by
    have : ε * lam = ε * lam' + ε * (π * χ / 2) := by rw [← hlam]; ring
    linear_combination heq + (-1 : ℝ) * this
  have hzero : ε * (π / 2) + π - θ + 2 * π * ((kf : ℝ) - kc) = 0 :=
    (mul_eq_zero.1 hdiff).resolve_left hχ.ne'
  set k : ℤ := kf - kc with hk
  have hkR : ((kf : ℝ) - kc) = (k : ℝ) := by rw [hk]; push_cast; ring
  rw [hkR] at hzero
  rcases hside with ⟨rfl, hθ⟩ | ⟨rfl, hθ⟩
  · -- `θ = 3π/2 + 2πk ∈ (−π/2, π/2]` forces `−1 < k ≤ −1/2`
    have h1 : (k : ℝ) ≤ -1 / 2 := by nlinarith [hθ.2]
    have h2 : (-1 : ℝ) < k := by nlinarith [hθ.1]
    have h1' : k < 0 := by exact_mod_cast (show (k : ℝ) < 0 by linarith)
    have h2' : -1 < k := by exact_mod_cast h2
    omega
  · -- `θ = π/2 + 2πk ∈ [−π/2, π/2)` forces `−1/2 ≤ k < 0`
    have h1 : (k : ℝ) < 0 := by nlinarith [hθ.2]
    have h2 : (-1 / 2 : ℝ) ≤ k := by nlinarith [hθ.1]
    have h1' : k < 0 := by exact_mod_cast h1
    have h2' : -1 < k := by exact_mod_cast (show (-1 : ℝ) < k by linarith)
    omega

/-- **The contradiction of (PFI2)–(PFI4) with the side sign**, along one approach filter `F` to the collar: as
`Aux37Attach.false_of_side_germs`, with `θ` allowed to be the extremal angle on the far side of the collar. -/
theorem false_of_side_germs_of_side {F : Filter ℂ} [F.NeBot] {M Lf Lc : ℂ → ℝ} {χ lam lam' ε θ : ℝ} {k : ℤ}
    (hχ : 0 < χ) (hlam : lam - lam' = π * χ / 2)
    (hside : (ε = 1 ∧ θ ∈ Ioc (-(π / 2)) (π / 2)) ∨ (ε = -1 ∧ θ ∈ Ico (-(π / 2)) (π / 2)))
    (hf : Tendsto (fun z => M z + χ * Lf z) F (𝓝 (ε * lam - θ * χ)))
    (hc : Tendsto (fun z => M z + χ * Lc z) F (𝓝 (ε * lam' - π * χ)))
    (hk : Tendsto (fun z => Lf z - Lc z) F (𝓝 (2 * π * k))) : False := by
  have h1 : Tendsto (fun z => χ * (Lf z - Lc z)) F (𝓝 ((ε * lam - θ * χ) - (ε * lam' - π * χ))) :=
    (hf.sub hc).congr fun z => by ring
  have h2 : Tendsto (fun z => χ * (Lf z - Lc z)) F (𝓝 (χ * (2 * π * k))) := hk.const_mul χ
  have heq := tendsto_nhds_unique h1 h2
  refine phase_ne_of_side hχ hlam hside 0 k ?_
  push_cast
  linarith

/-- **The strip pocket's four angle pieces are all excluded by the phase comparison**: on the right wall (the pocket on
its left, `ε = −1`) the angles `−π/2` and `θ₁ ∈ (−π/2, π/2)`, on the left wall (the pocket on its right, `ε = 1`) the
angles `π/2` and `θ₂ ∈ (−π/2, π/2]`. -/
theorem strip_side_phase_ne {χ lam lam' θ₁ θ₂ : ℝ} (hχ : 0 < χ) (hlam : lam - lam' = π * χ / 2)
    (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2)) (kf kc : ℤ) :
    (∀ θ ∈ ({-(π / 2), θ₁} : Set ℝ), -1 * lam - θ * χ + 2 * π * kf * χ ≠ -1 * lam' - π * χ + 2 * π * kc * χ) ∧
      ∀ θ ∈ ({π / 2, θ₂} : Set ℝ), 1 * lam - θ * χ + 2 * π * kf * χ ≠ 1 * lam' - π * χ + 2 * π * kc * χ := by
  have hπ := Real.pi_pos
  refine ⟨fun θ hθ => phase_ne_of_side hχ hlam (Or.inr ⟨rfl, ?_⟩) kf kc,
    fun θ hθ => phase_ne_of_side hχ hlam (Or.inl ⟨rfl, ?_⟩) kf kc⟩
  · rcases hθ with rfl | rfl
    · exact ⟨le_rfl, by linarith⟩
    · exact ⟨hθ₁.1.le, hθ₁.2⟩
  · rcases hθ with rfl | rfl
    · exact ⟨by linarith, le_rfl⟩
    · exact hθ₂

end Phase

/-! ### The collar of the newly exposed arc at a witness -/

section Collar

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ β α : ℝ → ℂ} {τ σ r s v v₁ v₂ : ℝ}

/-- The visited parts of the pocket do not change while the counterflow avoids it: `C ∩ R_t = C ∩ R_r` for
`t ∈ [r, s]` when `η([r, s]) ∩ C = ∅` (Aux. lemma 37, p. 198: "If `η′([a, b])` avoids `C`, the open set `C ∖ R_t` is
the same for all `t ∈ [a, b]`"). -/
theorem inter_image_eq_of_avoid (havoid : ∀ t ∈ Icc r s, η t ∉ C) {t : ℝ} (ht : t ∈ Icc r s) :
    C ∩ η '' Icc 0 t = C ∩ η '' Icc 0 r := by
  ext z
  refine ⟨fun ⟨hzC, u, hu, hue⟩ => ⟨hzC, ?_⟩, fun ⟨hzC, u, hu, hue⟩ => ⟨hzC, u, ⟨hu.1, hu.2.trans ht.1⟩, hue⟩⟩
  rcases le_or_gt u r with hur | hur
  · exact ⟨u, ⟨hu.1, hur⟩, hue⟩
  · exact absurd (hue ▸ hzC) (havoid u ⟨hur.le, hu.2.trans ht.2⟩)

/-- **The collar of the newly exposed arc at a rational witness** (Aux. lemma 37, p. 199: "Let `T_v` be the first
counterflow visit to `α_i(v)`. […] On (PFI1), `r < T_v < s`. The compact arc `J = α_i([v₁, v₂])` is disjoint from
`R_r`, is contained in `R_{T_v}`, and never loses its incident `C`-side collar to new range, because the new range
avoids `C`"). In a reverse-contained pocket, at a witness on the side `α`:

1. the first visit `T ∈ (r, s]` of `α(v)` is fresh and every `α(x)`, `x ∈ [v, 1]`, is visited by `T`;
2. the arc `α([v, v₂])` keeps a positive distance `δ` from the range `R_r`;
3. the visited part of the pocket is unchanged on `[r, s]`;
4. every point of `α([v, v₂])` has a ball whose pocket part is not visited by time `s`. -/
theorem _root_.InteractingSLE.Sec7.Aux37Attach.IsAttachWitness.collar
    (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hα : α = α₁ ∨ α = α₂)
    (hw : IsAttachWitness η C α τ σ r s v v₁ v₂) :
    (∃ T ∈ Ioc r s, η T = α v ∧ α v ∉ η '' Ico 0 T ∧ ∀ x ∈ Icc v 1, α x ∈ η '' Icc 0 T) ∧
      (∃ δ > 0, ∀ x ∈ Icc v v₂, ∀ y ∈ η '' Icc 0 r, δ ≤ dist (α x) y) ∧
      (∀ t ∈ Icc r s, C ∩ η '' Icc 0 t = C ∩ η '' Icc 0 r) ∧
      ∀ x ∈ Icc v v₂, ∃ ε > 0, ball (α x) ε ∩ C ∩ η '' Icc 0 s = ∅ := by
  obtain ⟨hτr, hrs, hsσ, havoid, hsv, hvv₁, hv₁v₂, hv₂r⟩ := hw
  have hr0 : 0 ≤ r := hP.nonneg.trans hτr
  obtain ⟨hpos_s, -, -, -, -⟩ := hP.chart (hτr.trans hrs.le) hsσ hα
  obtain ⟨-, hle_r, -, -, -⟩ := hP.chart hτr (hrs.trans hsσ) hα
  have hv01 : v ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hηc : ContinuousOn η (Ici 0) := hP.trace.2.1
  have hαc : ContinuousOn α (Icc 0 1) := (hP.arm hα).1
  -- 1. the first visit and the visited suffix
  have h1 : ∃ T ∈ Ioc r s, η T = α v ∧ α v ∉ η '' Ico 0 T ∧ ∀ x ∈ Icc v 1, α x ∈ η '' Icc 0 T := by
    obtain ⟨T, hT, hTe, hfresh⟩ := IsAttachWitness.exists_firstVisitTime hP hα
      ⟨hτr, hrs, hsσ, havoid, hsv, hvv₁, hv₁v₂, hv₂r⟩
    refine ⟨T, hT, hTe, hfresh, fun x hx => ?_⟩
    obtain ⟨-, -, -, hsuf, -⟩ := hP.chart (hτr.trans hT.1.le) (hT.2.trans_lt hsσ) hα
    have hvT : α v ∈ η '' Icc 0 T := ⟨T, ⟨hr0.trans hT.1.le, le_rfl⟩, hTe⟩
    have hu : firstVisit (fun t => η '' Icc 0 t) α T ≤ v := firstVisit_le hv01 hvT
    exact hsuf x ⟨hu.trans hx.1, hx.2⟩
  -- 2. the positive distance from `R_r`
  have hK : IsCompact (η '' Icc 0 r) := isCompact_Icc.image_of_continuousOn (hηc.mono fun _ h => h.1)
  have hKne : (η '' Icc 0 r).Nonempty := ⟨η 0, 0, ⟨le_rfl, hr0⟩, rfl⟩
  have hdisj : ∀ x ∈ Icc v v₂, α x ∉ η '' Icc 0 r := fun x hx =>
    IsAttachWitness.arc_disjoint hP hα ⟨hτr, hrs, hsσ, havoid, hsv, hvv₁, hv₁v₂, hv₂r⟩ x hx
  have h2 : ∃ δ > 0, ∀ x ∈ Icc v v₂, ∀ y ∈ η '' Icc 0 r, δ ≤ dist (α x) y := by
    have hfc : ContinuousOn (fun x => infDist (α x) (η '' Icc 0 r)) (Icc v v₂) :=
      (continuous_infDist_pt _).comp_continuousOn (hαc.mono fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (by linarith)) hfc
    have hpos : 0 < infDist (α x₀) (η '' Icc 0 r) :=
      (infDist_pos_iff_notMem_closure hKne).1 (by rw [hK.isClosed.closure_eq]; exact hdisj x₀ hx₀)
    exact ⟨_, hpos, fun x hx y hy => (hmin hx).trans (infDist_le_dist_of_mem hy)⟩
  -- 3. the unchanged visited part of the pocket
  have h3 : ∀ t ∈ Icc r s, C ∩ η '' Icc 0 t = C ∩ η '' Icc 0 r := fun t ht =>
    inter_image_eq_of_avoid havoid ht
  -- 4. the unvisited collar
  refine ⟨h1, h2, h3, fun x hx => ?_⟩
  obtain ⟨δ, hδ, hsep⟩ := h2
  refine ⟨δ, hδ, eq_empty_of_forall_notMem fun z ⟨⟨hzb, hzC⟩, hzs⟩ => ?_⟩
  have hzr : z ∈ C ∩ η '' Icc 0 r := by
    rw [← h3 s ⟨hrs.le, le_rfl⟩]
    exact ⟨hzC, hzs⟩
  have := hsep x hx z hzr.2
  rw [mem_ball, dist_comm] at hzb
  linarith

/-- **The collar of the newly exposed arc at a rational witness at infinity** (the pocket opening at the flow seed,
arms parametrized from `y₀` towards `∞`, last-visit attachments): at a witness `(r, s, v, v₁, v₂)` on the arm `α`,

1. the first visit `T ∈ (r, s]` of `α(v₂)` is fresh and every `α(x)`, `x ∈ [0, v₂]`, is visited by `T`;
2. the arc `α([v, v₂])` keeps a positive distance `δ` from the range `R_r`;
3. the visited part of the pocket is unchanged on `[r, s]`;
4. every point of `α([v, v₂])` has a ball whose pocket part is not visited by time `s`. -/
theorem _root_.InteractingSLE.Sec7.Aux37Attach.IsAttachWitnessInf.collar
    (hP : IsReversePocketInf W η C α₁ α₂ τ) (hα : α = α₁ ∨ α = α₂)
    (hw : IsAttachWitnessInf η C α τ r s v v₁ v₂) :
    (∃ T ∈ Ioc r s, η T = α v₂ ∧ α v₂ ∉ η '' Ico 0 T ∧ ∀ x ∈ Icc 0 v₂, α x ∈ η '' Icc 0 T) ∧
      (∃ δ > 0, ∀ x ∈ Icc v v₂, ∀ y ∈ η '' Icc 0 r, δ ≤ dist (α x) y) ∧
      (∀ t ∈ Icc r s, C ∩ η '' Icc 0 t = C ∩ η '' Icc 0 r) ∧
      ∀ x ∈ Icc v v₂, ∃ ε > 0, ball (α x) ε ∩ C ∩ η '' Icc 0 s = ∅ := by
  obtain ⟨hτr, hrs, havoid, hrv, hvv₁, hv₁v₂, hv₂s⟩ := hw
  have hr0 : 0 ≤ r := hP.nonneg.trans hτr
  have hηc : ContinuousOn η (Ici 0) := hP.trace.2.1
  obtain ⟨hαc, -, hαt, -, -, -, -⟩ := hP.arm hα
  have hbdd : ∀ t, Bornology.IsBounded (η '' Icc 0 t) := fun t =>
    (isCompact_Icc.image_of_continuousOn (hηc.mono fun _ h => h.1)).isBounded
  obtain ⟨hur0, -, -, -⟩ := hP.chart hτr hα
  have hdisj : ∀ x ∈ Icc v v₂, α x ∉ η '' Icc 0 r := fun x hx hxR => by
    have := le_lastVisit (R := fun t => η '' Icc 0 t) hαt (hbdd r)
      (show x ∈ Ici (0 : ℝ) by simp only [mem_Ici]; linarith [hx.1]) hxR
    linarith [hx.1]
  obtain ⟨-, hsuf_s, -, -⟩ := hP.chart (hτr.trans hrs.le) hα
  have hv₂R : α v₂ ∈ η '' Icc 0 s := hsuf_s v₂ ⟨by linarith, hv₂s.le⟩
  -- 1. the first visit of `α(v₂)` and the visited prefix
  have h1 : ∃ T ∈ Ioc r s, η T = α v₂ ∧ α v₂ ∉ η '' Ico 0 T ∧ ∀ x ∈ Icc 0 v₂, α x ∈ η '' Icc 0 T := by
    obtain ⟨hT0, hTe, hfresh⟩ := PocketJordan.firstHit_spec hηc ⟨s, hv₂R⟩
    set T := PocketJordan.firstHit η (α v₂)
    have hTs : T ≤ s := by
      by_contra hTs
      obtain ⟨t, ht, hte⟩ := hv₂R
      exact hfresh ⟨t, ⟨ht.1, ht.2.trans_lt (not_le.1 hTs)⟩, hte⟩
    have hrT : r < T := by
      by_contra hrT
      exact hdisj v₂ ⟨by linarith, le_rfl⟩ ⟨T, ⟨hT0, not_lt.1 hrT⟩, hTe⟩
    refine ⟨T, ⟨hrT, hTs⟩, hTe, hfresh, fun x hx => ?_⟩
    obtain ⟨-, hsuf, -, -⟩ := hP.chart (hτr.trans hrT.le) hα
    have hu : v₂ ≤ lastVisit (fun t => η '' Icc 0 t) α T :=
      le_lastVisit (R := fun t => η '' Icc 0 t) hαt (hbdd T)
        (show v₂ ∈ Ici (0 : ℝ) by simp only [mem_Ici]; linarith)
        ⟨T, ⟨hT0, le_rfl⟩, hTe⟩
    exact hsuf x ⟨hx.1, hx.2.trans hu⟩
  -- 2. the positive distance from `R_r`
  have hK : IsCompact (η '' Icc 0 r) := isCompact_Icc.image_of_continuousOn (hηc.mono fun _ h => h.1)
  have hKne : (η '' Icc 0 r).Nonempty := ⟨η 0, 0, ⟨le_rfl, hr0⟩, rfl⟩
  have h2 : ∃ δ > 0, ∀ x ∈ Icc v v₂, ∀ y ∈ η '' Icc 0 r, δ ≤ dist (α x) y := by
    have hfc : ContinuousOn (fun x => infDist (α x) (η '' Icc 0 r)) (Icc v v₂) :=
      (continuous_infDist_pt _).comp_continuousOn (hαc.mono fun x hx => by
        simp only [mem_Ici]; linarith [hx.1])
    obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (by linarith)) hfc
    have hpos : 0 < infDist (α x₀) (η '' Icc 0 r) :=
      (infDist_pos_iff_notMem_closure hKne).1 (by rw [hK.isClosed.closure_eq]; exact hdisj x₀ hx₀)
    exact ⟨_, hpos, fun x hx y hy => (hmin hx).trans (infDist_le_dist_of_mem hy)⟩
  -- 3. the unchanged visited part of the pocket
  have h3 : ∀ t ∈ Icc r s, C ∩ η '' Icc 0 t = C ∩ η '' Icc 0 r := fun t ht =>
    inter_image_eq_of_avoid havoid ht
  -- 4. the unvisited collar
  refine ⟨h1, h2, h3, fun x hx => ?_⟩
  obtain ⟨δ, hδ, hsep⟩ := h2
  refine ⟨δ, hδ, eq_empty_of_forall_notMem fun z ⟨⟨hzb, hzC⟩, hzs⟩ => ?_⟩
  have hzr : z ∈ C ∩ η '' Icc 0 r := by
    rw [← h3 s ⟨hrs.le, le_rfl⟩]
    exact ⟨hzC, hzs⟩
  have := hsep x hx z hzr.2
  rw [mem_ball, dist_comm] at hzb
  linarith

end Collar

/-! ### A strip-pocket witness lies in one angle piece of its wall -/

section Piece

open StripPocketPath PocketJordan
open WangWu (discTime)

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {η : ℝ → ℂ}

/-- An affine parameter `lo + x (hi − lo)` is on the same side of `d` as `x` is of `(d − lo)/(hi − lo)`. -/
theorem affine_lt_iff {lo hi d x : ℝ} (hlh : lo < hi) : lo + x * (hi - lo) < d ↔ x < (d - lo) / (hi - lo) := by
  rw [lt_div_iff₀ (sub_pos.2 hlh)]
  constructor <;> intro h <;> linarith

theorem lt_affine_iff {lo hi d x : ℝ} (hlh : lo < hi) : d < lo + x * (hi - lo) ↔ (d - lo) / (hi - lo) < x := by
  rw [div_lt_iff₀ (sub_pos.2 hlh)]
  constructor <;> intro h <;> linarith

/-- **A strip-pocket witness lies in one angle piece of each wall** (p. 198: "They can be chosen inside one
constant-angle piece of the selected open side"): the disc parameters `rightLo + x (rightHi − rightLo)` of the right
arc over `[v, v₂]` lie all below or all above the change time `discTime 1` of `α`, and those of the left arc all below
or all above the change time `discTime r` of `β^{(r)}`. -/
theorem _root_.InteractingSLE.Sec7.StripPocketPath.IsPocketWitness.piece {s₁ s₂ v v₁ v₂ : ℝ}
    (hw : IsPocketWitness R L r η s₁ s₂ v v₁ v₂) (hR : rightLo R L r < rightHi R L r)
    (hL : leftLo R L r < leftHi R L r) :
    ((∀ x ∈ Icc v v₂, rightLo R L r + x * (rightHi R L r - rightLo R L r) < discTime 1) ∨
        ∀ x ∈ Icc v v₂, discTime 1 < rightLo R L r + x * (rightHi R L r - rightLo R L r)) ∧
      ((∀ x ∈ Icc v v₂, leftLo R L r + x * (leftHi R L r - leftLo R L r) < discTime r) ∨
        ∀ x ∈ Icc v v₂, discTime r < leftLo R L r + x * (leftHi R L r - leftLo R L r)) := by
  have hcR := hw.2 ((discTime 1 - rightLo R L r) / (rightHi R L r - rightLo R L r)) (by simp [chgPts])
  have hcL := hw.2 ((discTime r - leftLo R L r) / (leftHi R L r - leftLo R L r)) (by simp [chgPts])
  refine ⟨?_, ?_⟩
  · rcases not_and_or.1 hcR with h | h
    · exact Or.inr fun x hx => (lt_affine_iff hR).2 (lt_of_lt_of_le (not_le.1 h) hx.1)
    · exact Or.inl fun x hx => (affine_lt_iff hR).2 (lt_of_le_of_lt hx.2 (not_le.1 h))
  · rcases not_and_or.1 hcL with h | h
    · exact Or.inr fun x hx => (lt_affine_iff hL).2 (lt_of_lt_of_le (not_le.1 h) hx.1)
    · exact Or.inl fun x hx => (affine_lt_iff hL).2 (lt_of_le_of_lt hx.2 (not_le.1 h))

end Piece

end InteractingSLE.Sec7.Aux37Witness
