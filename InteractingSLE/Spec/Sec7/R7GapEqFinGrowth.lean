/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqFinBoundary
import InteractingSLE.Spec.Sec7.R7StopInWire
import InteractingSLE.Spec.Sec6.Aux41Full

/-!
# Strict growth for the erased path of a mixed pocket

PROVE-R7-GAPEQ continuation. The proof of `Sec6.IsReversePocket.drivingCriterionB` uses only
its erasure facts and ambient strict hull growth. Adapt that landed proof to `IsErasurePocket`;
no reverse visit order is imposed on the outer arm.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.R7GapEqFin

open Sec6 R7StopIn

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {x₀ y₀ : ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}

/-- No relative interval of an erased mixed-pocket trace lies in the old relative range
and the real boundary. Strict ambient Loewner growth excludes the interior-visit interval. -/
theorem drivingCriterionB_erasure (hP : IsErasurePocket η C x₀ y₀ τ σ)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hψ : IsJordanCoord C (x₀) (y₀) ψ) {S : ℝ} (hS : S < pocketClock η C τ σ σ) :
    DrivingCriterionB (fun v => ψ (erasedPath η C τ σ v)) S := by
  intro t ht
  set A := {u ∈ Ioo t S | ψ (erasedPath η C τ σ u) ∈ (fun v => ψ (erasedPath η C τ σ v)) ''
    Icc 0 t ∨ (ψ (erasedPath η C τ σ u)).im = 0} with hAdef
  by_contra hne
  obtain ⟨v₀, hv₀⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨ε, hε, hεA⟩ := Metric.isOpen_iff.1 isOpen_interior v₀ hv₀
  have hball : ∀ v, |v - v₀| < ε → v ∈ A := fun v hv =>
    interior_subset (hεA (by rw [mem_ball, Real.dist_eq]; exact hv))
  set v₁ := v₀ - ε / 2 with hv₁
  set v₂ := v₀ + ε / 2 with hv₂
  have hA₁ := hball v₁ (by rw [hv₁, abs_of_neg (by linarith)]; linarith)
  have hA₂ := hball v₂ (by rw [hv₂, abs_of_pos (by linarith)]; linarith)
  have hσ₂ : v₂ < pocketClock η C τ σ σ := hA₂.1.2.trans hS
  have h0₁ : 0 ≤ v₁ := ht.1.le.trans hA₁.1.1.le
  set a₁ := pocketFibre η C τ σ v₁ with ha₁
  set a₂ := pocketFibre η C τ σ v₂ with ha₂
  have hℓ₁ := hP.clock_fibre ⟨h0₁, (show v₁ < v₂ by linarith).le.trans hσ₂.le⟩
  have hℓ₂ := hP.clock_fibre ⟨h0₁.trans (by linarith), hσ₂.le⟩
  have ha₁₂ : a₁ < a₂ := by
    by_contra h
    push Not at h
    have := hP.monotone_clock h
    rw [hℓ₁, hℓ₂] at this
    linarith
  obtain ⟨t₀, ht₀, ht₀I⟩ := hP.exists_mem_of_clock_lt ha₁₂ (by rw [hℓ₁, hℓ₂]; linarith)
  obtain ⟨δ, hδ, hδI⟩ := Metric.isOpen_iff.1 hP.isOpen_visitSet t₀ ht₀I
  set l := max (t₀ - δ) a₁ with hl
  set r := min (t₀ + δ) a₂ with hr
  have hlt : l < t₀ := max_lt (by linarith) ht₀.1
  have htr : t₀ < r := lt_min (by linarith) ht₀.2
  have hJ : ∀ x, l < x → x < r → x ∈ visitSet η C τ σ := fun x hlx hxr => hδI (by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor
    · linarith [le_max_left (t₀ - δ) a₁]
    · linarith [min_le_left (t₀ + δ) a₂])
  set c := (l + t₀) / 2 with hc
  set d := (t₀ + r) / 2 with hd
  have hcd : c < d := by rw [hc, hd]; linarith
  have hc0 : 0 ≤ c := hP.nonneg.trans ((hJ c (by rw [hc]; linarith) (by rw [hc]; linarith)).1.1.le)
  have hsub : η '' Icc c d ⊆ η '' Icc 0 c := by
    rintro _ ⟨t', ht', rfl⟩
    have ht'I := hJ t' (by rw [hc] at ht'; linarith [ht'.1]) (by rw [hd] at ht'; linarith [ht'.2])
    have hal : a₁ ≤ l := le_max_right _ _
    have hlo : pocketClock η C τ σ a₁ < pocketClock η C τ σ t' := hP.clock_lt_of_mem
      (t := (l + c) / 2) (by rw [hc]; linarith) (by rw [hc] at ht'; linarith [ht'.1])
      (hJ _ (by rw [hc]; linarith) (by rw [hc]; linarith))
    have hhi : pocketClock η C τ σ t' < pocketClock η C τ σ a₂ := hP.clock_lt_of_mem
      (t := (d + r) / 2) (by rw [hd] at ht'; linarith [ht'.2]) (by
        have : r ≤ a₂ := min_le_right _ _
        rw [hd]; linarith) (hJ _ (by rw [hd]; linarith) (by rw [hd]; linarith))
    rw [hℓ₁] at hlo
    rw [hℓ₂] at hhi
    set w := pocketClock η C τ σ t' with hw
    have hwA := hball w (by rw [abs_lt]; constructor <;> linarith)
    have hfw : pocketFibre η C τ σ w = t' := hP.fibre_clock_of_mem ht'I
    have hηC : η t' ∈ C := ht'I.2
    have hCsub : ∀ z ∈ C, z ∈ closure C \ {x₀} := fun z hz =>
      ⟨subset_closure hz, fun h => hP.notMem_x (h ▸ hz)⟩
    rcases hwA.2 with ⟨w', hw', hψw⟩ | him
    · simp only [erasedPath, hfw] at hψw
      have heq : erasedPath η C τ σ w' = η t' := hψ.2.1
        (hP.erasedPath_mem ⟨hw'.1, hw'.2.trans_lt (ht.2.trans hS)⟩) (hCsub _ hηC) hψw
      have hmem : η t' ∈ erasedPath η C τ σ '' Icc 0 t ∩ C := ⟨⟨w', hw', heq⟩, hηC⟩
      rw [hP.erasedPath_image_inter ⟨ht.1.le, (ht.2.trans hS).le⟩] at hmem
      obtain ⟨t'', ht'', he⟩ := hmem.1
      have hft : pocketFibre η C τ σ t ≤ a₁ := hP.monotone_fibre hA₁.1.1.le
      exact ⟨t'', ⟨ht''.1, ht''.2.trans (hft.trans (hal.trans (by rw [hc]; linarith)))⟩, he⟩
    · simp only [erasedPath, hfw] at him
      exact absurd him (ne_of_gt (hψ.2.2.2.1.2.1 hηC))
  exact not_image_subset_of_lt hη hW hW0 hc0 hcd hsub

end InteractingSLE.Sec7.R7GapEqFin
