/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5EnlMean
import InteractingSLE.GFF.LocalSets.GermApprox

/-!
# Traces of germ σ-algebras on an event where two random sets agree

Packet PROVE-R5-ENLARGED. Aux. 35's proof (`source/spec/p193-240.md` L28, p. 194): on `{q < T}` "the retained stopped
information and the marked harmonic mean for `A_{T_q}` are exactly those for `A_T`. This is an equality of the
restricted stopped sigma-algebras". The retained records are `germSigma K h ⊔ ℋ` (germs and marks). If two random
sets agree on an event `E` and the marks have the same trace on `E`, the two records have the same trace on `E`.
The germ σ-algebra is a decreasing intersection `⨅ₙ 𝒜_{1/(n+1)}`; the trace of a **decreasing** intersection is the
intersection of the traces (a `limsup` of representatives), which is the only non-formal step.

## Main results

* `comap_val_iInf_of_antitone` — traces commute with decreasing countable intersections;
* `comap_val_germSigmaAt_congr`, **`comap_val_germSigma_congr`** — sets equal on `E` have equal germ traces on `E`;
* `measurableSet_inter_iff_of_comap_val_eq` — the trace form used by Mathlib's
  `condExp_ae_eq_restrict_of_measurableSpace_eq_on`;
* **`measurableSet_inter_germSigma_sup_iff`** — the two retained records have the same trace on `E`.

Conditional helpers with distinct names; nothing here uses Theorem 1.2/1.3 or any `*_of_param` (R43, R48).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec7.R5Enl

open LocalSets

section Trace

variable {Ω : Type*}

/-- **The trace of a decreasing countable intersection of σ-algebras is the intersection of the traces.** -/
theorem comap_val_iInf_of_antitone (E : Set Ω) {S : ℕ → MeasurableSpace Ω} (hS : Antitone S) :
    MeasurableSpace.comap ((↑) : E → Ω) (⨅ n, S n) = ⨅ n, MeasurableSpace.comap ((↑) : E → Ω) (S n) := by
  refine le_antisymm (le_iInf fun n => MeasurableSpace.comap_mono (iInf_le S n)) ?_
  intro t ht
  have hmem : ∀ n, ∃ F : Set Ω, MeasurableSet[S n] F ∧ ((↑) : E → Ω) ⁻¹' F = t := fun n =>
    (MeasurableSpace.measurableSet_iInf.1 ht) n
  choose F hF hFt using hmem
  refine ⟨⋂ m, ⋃ j, F (m + j), ?_, ?_⟩
  · refine MeasurableSpace.measurableSet_iInf.2 fun k => ?_
    have e : (⋂ m, ⋃ j, F (m + j)) = ⋂ m, ⋃ j, F (m + k + j) := by
      ext ω
      simp only [mem_iInter, mem_iUnion]
      constructor
      · intro h m
        exact h (m + k)
      · intro h m
        obtain ⟨j, hj⟩ := h m
        exact ⟨k + j, by rwa [← add_assoc]⟩
    rw [e]
    refine MeasurableSet.iInter fun m => MeasurableSet.iUnion fun j => ?_
    exact hS (show k ≤ m + k + j by omega) _ (hF (m + k + j))
  · ext x
    simp only [preimage_iInter, preimage_iUnion, mem_iInter, mem_iUnion, hFt]
    exact ⟨fun h => (h 0).choose_spec, fun h _ => ⟨0, h⟩⟩

/-- On `E` the trace of the measurable sets of a σ-algebra containing `E` is the trace of the comap. -/
theorem measurableSet_inter_iff_comap_val {m : MeasurableSpace Ω} {E : Set Ω} (hE : MeasurableSet[m] E)
    (t : Set Ω) : MeasurableSet[m] (E ∩ t) ↔
      MeasurableSet[MeasurableSpace.comap ((↑) : E → Ω) m] (((↑) : E → Ω) ⁻¹' t) := by
  constructor
  · intro h
    refine ⟨E ∩ t, h, ?_⟩
    ext x
    simp only [mem_preimage, mem_inter_iff, x.2, true_and]
  · rintro ⟨F, hF, hFt⟩
    have e : E ∩ t = E ∩ F := by
      ext ω
      constructor
      · rintro ⟨hω, ht⟩
        have : (⟨ω, hω⟩ : E) ∈ ((↑) : E → Ω) ⁻¹' F := by rw [hFt]; exact ht
        exact ⟨hω, this⟩
      · rintro ⟨hω, hF'⟩
        have : (⟨ω, hω⟩ : E) ∈ ((↑) : E → Ω) ⁻¹' t := by rw [← hFt]; exact hF'
        exact ⟨hω, this⟩
    rw [e]
    exact hE.inter hF

/-- **Equal traces give the trace condition of `condExp_ae_eq_restrict_of_measurableSpace_eq_on`.** -/
theorem measurableSet_inter_iff_of_comap_val_eq {m₁ m₂ : MeasurableSpace Ω} {E : Set Ω}
    (hE₁ : MeasurableSet[m₁] E) (hE₂ : MeasurableSet[m₂] E)
    (heq : MeasurableSpace.comap ((↑) : E → Ω) m₁ = MeasurableSpace.comap ((↑) : E → Ω) m₂) (t : Set Ω) :
    MeasurableSet[m₁] (E ∩ t) ↔ MeasurableSet[m₂] (E ∩ t) := by
  rw [measurableSet_inter_iff_comap_val hE₁, measurableSet_inter_iff_comap_val hE₂, heq]

variable {A A' : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- Random sets agreeing on `E` have the same trace of `𝒜_δ` on `E`. -/
theorem comap_val_germSigmaAt_congr {E : Set Ω} (hAE : ∀ ω ∈ E, A ω = A' ω) (δ : ℝ) :
    MeasurableSpace.comap ((↑) : E → Ω) (germSigmaAt A h δ) =
      MeasurableSpace.comap ((↑) : E → Ω) (germSigmaAt A' h δ) := by
  have hcomp : A ∘ ((↑) : E → Ω) = A' ∘ ((↑) : E → Ω) := funext fun x => hAE x.1 x.2
  simp only [germSigmaAt, MeasurableSpace.comap_sup, MeasurableSpace.comap_comp, hcomp,
    MeasurableSpace.comap_generateFrom]
  congr 2
  ext s
  simp only [mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨φ, B, hB, rfl⟩, rfl⟩
    refine ⟨_, ⟨φ, B, hB, rfl⟩, ?_⟩
    ext x
    simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, hAE x.1 x.2]
  · rintro ⟨_, ⟨φ, B, hB, rfl⟩, rfl⟩
    refine ⟨_, ⟨φ, B, hB, rfl⟩, ?_⟩
    ext x
    simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, hAE x.1 x.2]

/-- The germ approximations `𝒜_{1/(n+1)}` decrease. -/
theorem antitone_germSigmaAt (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) :
    Antitone fun n : ℕ => germSigmaAt A h (1 / ((n : ℝ) + 1)) := by
  intro m n hmn
  refine germSigmaAt_mono (by positivity) ?_
  have : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
  exact one_div_le_one_div_of_le (by positivity) this

/-- **Random sets agreeing on `E` have the same trace of the germ σ-algebra on `E`.** -/
theorem comap_val_germSigma_congr {E : Set Ω} (hAE : ∀ ω ∈ E, A ω = A' ω) :
    MeasurableSpace.comap ((↑) : E → Ω) (germSigma A h) =
      MeasurableSpace.comap ((↑) : E → Ω) (germSigma A' h) := by
  rw [germSigma_eq_iInf, germSigma_eq_iInf, comap_val_iInf_of_antitone E (antitone_germSigmaAt A h),
    comap_val_iInf_of_antitone E (antitone_germSigmaAt A' h)]
  exact iInf_congr fun n => comap_val_germSigmaAt_congr hAE _

/-- **The retained records `germSigma A h ⊔ ℋ` and `germSigma A' h ⊔ ℋ'` have the same trace on `E`** when the sets
agree on `E`, the marks have the same trace on `E`, and `E` is measurable for both records. -/
theorem measurableSet_inter_germSigma_sup_iff {ℋ ℋ' : MeasurableSpace Ω} {E : Set Ω}
    (hAE : ∀ ω ∈ E, A ω = A' ω)
    (hmarks : MeasurableSpace.comap ((↑) : E → Ω) ℋ = MeasurableSpace.comap ((↑) : E → Ω) ℋ')
    (hE : MeasurableSet[germSigma A h ⊔ ℋ] E) (hE' : MeasurableSet[germSigma A' h ⊔ ℋ'] E) (t : Set Ω) :
    MeasurableSet[germSigma A h ⊔ ℋ] (E ∩ t) ↔ MeasurableSet[germSigma A' h ⊔ ℋ'] (E ∩ t) := by
  refine measurableSet_inter_iff_of_comap_val_eq hE hE' ?_ t
  rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_sup, comap_val_germSigma_congr hAE, hmarks]

end Trace

end InteractingSLE.Sec7.R5Enl
