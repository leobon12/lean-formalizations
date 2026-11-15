/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityGapErasure

/-!
# Nondegeneracy of infinite mixed-pocket erasure

PROVE-R7-GAPEQ. Adapt the landed Aux. 40 infinity proof to its weaker erasure
interface. Ambient strict growth rules out a relative interval on the old range
and real line; no outer reverse-order or visitation premise is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Sec7.R7RelativeInf

open Sec6 R7StopIn

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {y₀ : ℂ} {τ : ℝ} {ψ : ℂ → ℂ}

/-- The erased mixed-pocket curve has no interval on its previous range and the
real line. This uses only erasure facts and strict ambient Loewner growth. -/
theorem drivingCriterionB_erasure (hP : IsErasurePocketInf η C y₀ τ)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hψ : IsJordanCoordInf C y₀ ψ) {S : ℝ} (hS : S < clockEnd η C τ) :
    DrivingCriterionB (fun v => ψ (erasedPathInf η C τ v)) S := by
  intro t ht
  set A := {u ∈ Ioo t S | ψ (erasedPathInf η C τ u) ∈ (fun v => ψ (erasedPathInf η C τ v)) ''
    Icc 0 t ∨ (ψ (erasedPathInf η C τ u)).im = 0} with hAdef
  by_contra hne
  obtain ⟨v₀, hv₀⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨ε, hε, hεA⟩ := Metric.isOpen_iff.1 isOpen_interior v₀ hv₀
  have hball : ∀ v, |v - v₀| < ε → v ∈ A := fun v hv =>
    interior_subset (hεA (by rw [mem_ball, Real.dist_eq]; exact hv))
  set v₁ := v₀ - ε / 2 with hv₁
  set v₂ := v₀ + ε / 2 with hv₂
  have hA₁ := hball v₁ (by rw [hv₁, abs_of_neg (by linarith)]; linarith)
  have hA₂ := hball v₂ (by rw [hv₂, abs_of_pos (by linarith)]; linarith)
  have hσ₂ : v₂ < clockEnd η C τ := hA₂.1.2.trans hS
  have h0₁ : 0 ≤ v₁ := ht.1.le.trans hA₁.1.1.le
  have hm₁ : v₁ ∈ Ico 0 (clockEnd η C τ) := ⟨h0₁, (show v₁ < v₂ by linarith).trans hσ₂⟩
  have hm₂ : v₂ ∈ Ico 0 (clockEnd η C τ) := ⟨h0₁.trans (by linarith), hσ₂⟩
  set a₁ := pocketFibreInf η C τ v₁ with ha₁
  set a₂ := pocketFibreInf η C τ v₂ with ha₂
  have hℓ₁ := hP.clock_fibre hm₁
  have hℓ₂ := hP.clock_fibre hm₂
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
  have hJ : ∀ x, l < x → x < r → x ∈ visitSetInf η C τ := fun x hlx hxr => hδI (by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor
    · linarith [le_max_left (t₀ - δ) a₁]
    · linarith [min_le_left (t₀ + δ) a₂])
  set c := (l + t₀) / 2 with hc
  set d := (t₀ + r) / 2 with hd
  have hcd : c < d := by rw [hc, hd]; linarith
  have hc0 : 0 ≤ c :=
    hP.nonneg.trans (le_of_lt (hJ c (by rw [hc]; linarith) (by rw [hc]; linarith)).1)
  have hsub : η '' Icc c d ⊆ η '' Icc 0 c := by
    rintro _ ⟨t', ht', rfl⟩
    have ht'I := hJ t' (by rw [hc] at ht'; linarith [ht'.1]) (by rw [hd] at ht'; linarith [ht'.2])
    have hal : a₁ ≤ l := le_max_right _ _
    have hlo : pocketClockInf η C τ a₁ < pocketClockInf η C τ t' := hP.clock_lt_of_mem
      (t := (l + c) / 2) (by rw [hc]; linarith) (by rw [hc] at ht'; linarith [ht'.1])
      (hJ _ (by rw [hc]; linarith) (by rw [hc]; linarith))
    have hhi : pocketClockInf η C τ t' < pocketClockInf η C τ a₂ := hP.clock_lt_of_mem
      (t := (d + r) / 2) (by rw [hd] at ht'; linarith [ht'.2]) (by
        have : r ≤ a₂ := min_le_right _ _
        rw [hd]; linarith) (hJ _ (by rw [hd]; linarith) (by rw [hd]; linarith))
    rw [hℓ₁] at hlo
    rw [hℓ₂] at hhi
    set w := pocketClockInf η C τ t' with hw
    have hwA := hball w (by rw [abs_lt]; constructor <;> linarith)
    have hfw : pocketFibreInf η C τ w = t' := hP.fibre_clock_of_mem ht'I
    have hηC : η t' ∈ C := ht'I.2
    rcases hwA.2 with ⟨w', hw', hψw⟩ | him
    · simp only [erasedPathInf, hfw] at hψw
      have heq : erasedPathInf η C τ w' = η t' := hψ.2.1
        (hP.erasedPath_mem ⟨hw'.1, hw'.2.trans_lt (ht.2.trans hS)⟩) (subset_closure hηC) hψw
      have hmem : η t' ∈ erasedPathInf η C τ '' Icc 0 t ∩ C := ⟨⟨w', hw', heq⟩, hηC⟩
      rw [hP.erasedPath_image_inter ⟨ht.1.le, ht.2.trans hS⟩] at hmem
      obtain ⟨t'', ht'', he⟩ := hmem.1
      have hft : pocketFibreInf η C τ t ≤ a₁ :=
        hP.monotoneOn_fibre ⟨ht.1.le, ht.2.trans hS⟩ hm₁ hA₁.1.1.le
      exact ⟨t'', ⟨ht''.1, ht''.2.trans (hft.trans (hal.trans (by rw [hc]; linarith)))⟩, he⟩
    · simp only [erasedPathInf, hfw] at him
      exact absurd him (ne_of_gt (hψ.2.2.2.1.2.1 hηC))
  exact not_image_subset_of_lt hη hW hW0 hc0 hcd hsub

end InteractingSLE.Sec7.R7RelativeInf
