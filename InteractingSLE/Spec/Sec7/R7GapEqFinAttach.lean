/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqFinBoundary
import InteractingSLE.Spec.Sec7.Aux37Witness

/-!
# Aux. 37 for one contained barrier of a mixed pocket

PROVE-R7-GAPEQ continuation. Reuse the landed continuity and phase contradiction, removing
the irrelevant requirement that the other pocket side is reverse visited. Attachment
constancy reduces to the field comparison at one rational witness, with its exact type below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology

namespace InteractingSLE.Sec7.R7GapEqFin

open Sec6 R7GapEq R7StopIn Aux37Attach

variable {η B : ℝ → ℂ} {C : Set ℂ} {τ σ : ℝ}

/-- A single reverse-visited barrier has a continuous first-visit attachment from its entrance
time onwards. This is the landed Aux. 37 continuity theorem, specialized without a second arm. -/
theorem continuousOn_barrier_firstVisit (hη : ContinuousOn η (Ici 0))
    (hBc : ContinuousOn B (Icc 0 1)) (hBi : InjOn B (Icc 0 1))
    (hrev : R16.IsReverseVisitOrder B fun t => η '' Icc 0 t)
    (hτ0 : 0 ≤ τ) (hτ : η τ = B 1) :
    ContinuousOn (firstVisit (fun t => η '' Icc 0 t) B) (Ici τ) := by
  have hne : ∀ t ≥ τ, ∃ v ∈ Icc (0 : ℝ) 1, B v ∈ η '' Icc 0 t :=
    fun t ht => ⟨1, ⟨zero_le_one, le_rfl⟩, τ, ⟨hτ0, ht⟩, hτ⟩
  apply continuousOn_firstVisit_Ici hτ0 hη hBc hBi hne
  intro t ht v hv huv
  have hmem := firstVisit_mem (R := fun t => η '' Icc 0 t) hBc
    (isCompact_Icc.image_of_continuousOn (hη.mono fun _ hs => hs.1)).isClosed (hne t ht)
  exact hrev t _ hmem.1 v hv huv hmem.2

/-- A strict attachment decrease yields an existing `IsAttachWitness` on rational times and
parameters. Only continuity of that one attachment is used in this extraction. -/
theorem exists_rat_barrierWitness_of_lt
    (hcont : ContinuousOn (firstVisit (fun t => η '' Icc 0 t) B) (Ici τ))
    (marks : Finset ℝ) {a b : ℝ} (hτa : τ ≤ a) (hab : a ≤ b) (hbσ : b < σ)
    (hC : ∀ t ∈ Icc a b, η t ∉ C)
    (hlt : firstVisit (fun t => η '' Icc 0 t) B b < firstVisit (fun t => η '' Icc 0 t) B a) :
    ∃ r s v v₁ v₂ : ℚ, IsAttachWitness η C B τ σ r s v v₁ v₂ ∧
      ∀ x ∈ marks, x ∉ Icc (v : ℝ) v₂ := by
  let u := firstVisit (fun t => η '' Icc 0 t) B
  have hab' : a < b := lt_of_le_of_ne hab fun he => by
    rw [he] at hlt
    exact lt_irrefl _ hlt
  let δ := u a - u b
  have hδ : 0 < δ := sub_pos.2 hlt
  obtain ⟨ρ, hρ, hρa⟩ := Metric.continuousWithinAt_iff.1 (hcont a hτa) (δ / 3) (by linarith)
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn
    (show a < min (a + ρ) b from lt_min (by linarith) hab')
  have hra : u a - δ / 3 < u r := by
    have h := hρa (show (r : ℝ) ∈ Ici τ from hτa.trans hr1.le) (by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [min_le_left (a + ρ) b])
    rw [Real.dist_eq, abs_lt] at h
    linarith [h.1]
  have hrb : (r : ℝ) < b := lt_of_lt_of_le hr2 (min_le_right _ _)
  obtain ⟨ρ', hρ', hρb⟩ := Metric.continuousWithinAt_iff.1 (hcont b (hτa.trans hab)) (δ / 3)
    (by linarith)
  obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn
    (show max (r : ℝ) (b - ρ') < b from max_lt hrb (by linarith))
  have hsb : u s < u b + δ / 3 := by
    have h := hρb (show (s : ℝ) ∈ Ici τ from
      hτa.trans (hr1.le.trans ((le_max_left _ _).trans hs1.le))) (by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right (r : ℝ) (b - ρ')])
    rw [Real.dist_eq, abs_lt] at h
    linarith [h.2]
  have hrs : (r : ℝ) < s := lt_of_le_of_lt (le_max_left _ _) hs1
  obtain ⟨v, v₁, v₂, hv, hvv₁, hv₁v₂, hv₂, hmarks⟩ :=
    exists_rat_triple_avoid (show u s < u r by dsimp [δ] at hra hsb; linarith) marks
  exact ⟨r, s, v, v₁, v₂, ⟨hτa.trans hr1.le, hrs, hs2.trans hbσ,
    fun t ht => hC t ⟨hr1.le.trans ht.1, ht.2.trans hs2.le⟩, hv, hvv₁, hv₁v₂, hv₂⟩, hmarks⟩

/-- **One-barrier Aux. 37 from rational witness exclusion.** No premise concerns the visit order
of the other boundary side. This is applicable to the contained arm of a mixed pocket. -/
theorem barrierAttachConst_of_noWitness (hη : ContinuousOn η (Ici 0))
    (hBc : ContinuousOn B (Icc 0 1)) (hBi : InjOn B (Icc 0 1))
    (hrev : R16.IsReverseVisitOrder B fun t => η '' Icc 0 t)
    (hτ0 : 0 ≤ τ) (hτ : η τ = B 1) (marks : Finset ℝ)
    (hno : ∀ r s v v₁ v₂ : ℚ, IsAttachWitness η C B τ σ r s v v₁ v₂ →
      (∀ x ∈ marks, x ∉ Icc (v : ℝ) v₂) → False) : BarrierAttachConst η C B τ σ := by
  have hc := continuousOn_barrier_firstVisit hη hBc hBi hrev hτ0 hτ
  intro a b hτa hab hbσ hgap
  by_contra hne
  have hanti : firstVisit (fun t => η '' Icc 0 t) B b ≤
      firstVisit (fun t => η '' Icc 0 t) B a :=
    firstVisit_anti monotone_image_Icc hab ⟨1, ⟨zero_le_one, le_rfl⟩, τ, ⟨hτ0, hτa⟩, hτ⟩
  obtain ⟨r, s, v, v₁, v₂, hw, hm⟩ := exists_rat_barrierWitness_of_lt hc marks hτa hab hbσ
    hgap (lt_of_le_of_ne hanti hne)
  exact hno r s v v₁ v₂ hw hm

/-- **One-barrier Aux. 37 from its precise germ comparison.** The named `hcompare` input is
the genuinely stochastic step: the unchanged mean has both the incoming flow germ and the
new counterflow germ, with an integer argument difference. The phase contradiction is reused.
The side sign allows the far extremal angle, exactly as in `Aux37WallsR7`. -/
theorem barrierAttachConst_of_germs (hη : ContinuousOn η (Ici 0))
    (hBc : ContinuousOn B (Icc 0 1)) (hBi : InjOn B (Icc 0 1))
    (hrev : R16.IsReverseVisitOrder B fun t => η '' Icc 0 t)
    (hτ0 : 0 ≤ τ) (hτ : η τ = B 1) (marks : Finset ℝ)
    {χ lam lam' ε θ : ℝ} (hχ : 0 < χ) (hlam : lam - lam' = Real.pi * χ / 2)
    (hside : (ε = 1 ∧ θ ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) ∨
      (ε = -1 ∧ θ ∈ Ico (-(Real.pi / 2)) (Real.pi / 2)))
    (hcompare : ∀ r s v v₁ v₂ : ℚ, IsAttachWitness η C B τ σ r s v v₁ v₂ →
      (∀ x ∈ marks, x ∉ Icc (v : ℝ) v₂) →
      ∃ (F : Filter ℂ) (M Lf Lc : ℂ → ℝ) (k : ℤ), F.NeBot ∧
        Tendsto (fun z => M z + χ * Lf z) F (𝓝 (ε * lam - θ * χ)) ∧
        Tendsto (fun z => M z + χ * Lc z) F (𝓝 (ε * lam' - Real.pi * χ)) ∧
        Tendsto (fun z => Lf z - Lc z) F (𝓝 (2 * Real.pi * k))) :
    BarrierAttachConst η C B τ σ := by
  apply barrierAttachConst_of_noWitness hη hBc hBi hrev hτ0 hτ marks
  intro r s v v₁ v₂ hw hm
  obtain ⟨F, M, Lf, Lc, k, hF, hf, hc, hk⟩ := hcompare r s v v₁ v₂ hw hm
  have : F.NeBot := hF
  exact Aux37Witness.false_of_side_germs_of_side hχ hlam hside hf hc hk

end InteractingSLE.Sec7.R7GapEqFin
