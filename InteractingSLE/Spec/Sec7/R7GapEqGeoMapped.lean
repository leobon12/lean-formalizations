/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqGeoLoewner

/-!
# Mapped gaps: the fresh-endpoint case and the remaining old-access input

PROVE-R7-GAPEQ. Physical gap equality supplies the common endpoint. If it is outside the
earlier range, no entry into swallowed pockets and inverse-map injectivity prove mapped gap
equality. Only endpoints already in the earlier range need the fixed-chart gate separation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology
open QuantumZipper (H fwdHull)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7GapEqGeo

open Sec6 R7StopIn

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {x₀ y₀ : ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}

/-- A visit limit strictly after a later chart time is still a visit limit after that time.
This allows the old-access gate argument to choose its rational chart after both attachments. -/
theorem mem_closure_visits_after {η : ℝ → ℂ} {C : Set ℂ} {s r a : ℝ}
    (hra : r < a) (ha : a ∈ closure {t | s < t ∧ η t ∈ C}) :
    a ∈ closure {t | r < t ∧ η t ∈ C} := by
  have hcl : a ∈ closure (Ioi r ∩ {t | s < t ∧ η t ∈ C}) :=
    isOpen_Ioi.inter_closure ⟨hra, ha⟩
  exact closure_mono (s := Ioi r ∩ {t | s < t ∧ η t ∈ C})
    (t := {t | r < t ∧ η t ∈ C}) (fun t ht => ⟨ht.1, ht.2.2⟩) hcl

/-- The mapped endpoint equality is automatic when the common physical endpoint lies in
`H` and was not visited in the earlier chart's range. No singleton-tip assertion is used. -/
theorem mapped_gap_eq_of_fresh_endpoint {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {s a b : ℝ} (hs : 0 ≤ s) (hsa : s ≤ a) (hsb : s ≤ b) (heq : η a = η b)
    (haH : η a ∈ H) (hfresh : η a ∉ η '' Icc 0 s) :
    trMap W s a 0 = trMap W s b 0 :=
  ownFuture_eq_of_mem_domain hη hW hW0 hs hsa hsb heq
    ⟨haH, trace_notMem_fwdHull hη hW hW0 hs hsa hfresh⟩

/-- **Mapped gaps from their old-access case.** The exact `hOld` hypothesis concerns only
common endpoints already visited in the earlier chart. It is the remaining prime-end
separation step, to be supplied by the landed fixed-chart gate lemma and the mixed incoming
tree geometry. The ambient interior condition is the source's non-boundary original trace. -/
theorem mapped_gap_eq_of_old_access {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ}
    {x₀ y₀ : ℂ} {τ σ : ℝ} (hP : IsErasurePocket η C x₀ y₀ τ σ)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hηH : ∀ t, 0 < t → η t ∈ H)
    (hOld : ∀ s ∈ Ico τ σ, ∀ a b : ℝ, s < a → a < b → b < σ →
      (∀ t ∈ Icc a b, η t ∉ C) →
      a ∈ closure {t | s < t ∧ η t ∈ C} → b ∈ closure {t | a < t ∧ η t ∈ C} →
      η a ∈ η '' Icc 0 s → trMap W s a 0 = trMap W s b 0) :
    ∀ s ∈ Ico τ σ, ∀ a b : ℝ, s < a → a < b → b < σ →
      (∀ t ∈ Icc a b, η t ∉ C) →
      a ∈ closure {t | s < t ∧ η t ∈ C} → b ∈ closure {t | a < t ∧ η t ∈ C} →
      trMap W s a 0 = trMap W s b 0 := by
  intro s hs a b hsa hab hbσ hgap ha hb
  by_cases hold : η a ∈ η '' Icc 0 s
  · exact hOld s hs a b hsa hab hbσ hgap ha hb hold
  · have hs0 : 0 ≤ s := hP.nonneg.trans hs.1
    have heq := hP.gap a b (hs.1.trans hsa.le) hab hbσ hgap hb (Or.inr
      (closure_mono (s := {t | s < t ∧ η t ∈ C})
        (t := {t | τ < t ∧ η t ∈ C}) (fun t ht => ⟨hs.1.trans_lt ht.1, ht.2⟩) ha))
    exact mapped_gap_eq_of_fresh_endpoint hη hW hW0 hs0 hsa.le (hsa.trans hab).le heq
      (hηH a (hs0.trans_lt hsa)) hold

/-- **Finite relative driver with only the old-access gap case left.** The target face's
conformal chart and confinement of the retained future are proved by the previous reductions;
only the displayed planar target-face geometry and old prime-end separation are inputs. -/
theorem relLoewner_of_target_faces_of_old_access (hP : IsErasurePocket η C x₀ y₀ τ σ)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hCH : C ⊆ H) (hψ : IsJordanCoord C x₀ y₀ ψ)
    (hηH : ∀ t, 0 < t → η t ∈ H)
    (hOld : ∀ s ∈ Ico τ σ, ∀ a b : ℝ, s < a → a < b → b < σ →
      (∀ t ∈ Icc a b, η t ∉ C) →
      a ∈ closure {t | s < t ∧ η t ∈ C} → b ∈ closure {t | a < t ∧ η t ∈ C} →
      η a ∈ η '' Icc 0 s → trMap W s a 0 = trMap W s b 0)
    (hgeometry : ∀ u ∈ Ico (0 : ℝ) (pocketClock η C τ σ σ),
      ∃ (Γ : Set ℂ) (p q : ℂ), LQGMetric.JordanMap.IsJordanCurve Γ ∧ p ∈ Γᶜ ∧
        IsBounded (connectedComponentIn Γᶜ p) ∧ connectedComponentIn Γᶜ p ⊆ H ∧
        trMap W 0 (pocketFibre η C τ σ u) '' connectedComponentIn Γᶜ p =
          connectedComponentIn (C ∩ (H \ fwdHull W (pocketFibre η C τ σ u))) q ∧
        x₀ ∈ closure (trMap W 0 (pocketFibre η C τ σ u) '' connectedComponentIn Γᶜ p) ∧
        ∀ t, pocketFibre η C τ σ u ≤ t → η t ∈ C →
          trMap W (pocketFibre η C τ σ u) t 0 ∈ H →
          trMap W (pocketFibre η C τ σ u) t 0 ∈ connectedComponentIn Γᶜ p) :
    RelLoewner (fun v => ψ (erasedPath η C τ σ v)) (pocketClock η C τ σ σ) := by
  exact relLoewner_of_target_faces hP hη hW hW0 hCH hψ
    (mapped_gap_eq_of_old_access hP hη hW hW0 hηH hOld) hgeometry

end InteractingSLE.Sec7.R7GapEqGeo
