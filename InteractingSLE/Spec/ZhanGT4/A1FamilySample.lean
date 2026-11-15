/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1FamilyFilt

/-!
# A.1's seeded frozen-sample families, II: the families from one-sample laws

Packet PROVE-A1-FAMILY (R76). Source: Astra, *Follow-up proofs* §A.1.3 (`ig1_followup_proofs.txt` L341–L353, R38),
§A.1.4 (L400–L407: "the identical calculation (D8), with the conformal map of `K₂(I)` frozen"); follow-up 5 §1.3
(L203–L222, R73).

A1-FROZEN's `FrozenFamily` (resp. `FrozenFamilyFst`) asks, for every cap `m`, almost every frozen conditioning sample
and **every** deterministic frozen time `σ`, for the frozen-sample law of the canonical image at the stop `σ`. This
file builds the families from the one-sample law `IsSeedSampleLaw` of the sections (which `A1FamilyFilt` derives from
A22's seeded line, `isSeedSampleLaw_of_seed`):

* **`isSeedSampleLaw_of_cap_zero`**: the degenerate cap (`0`: the frozen hull is not inside the rectangle's protection,
  or the conditioning curve is not live at `σ`) needs only a continuous Brownian motion under the tilted law;
* **`FrozenFamily.ofSampleLaw`**, **`FrozenFamilyFst.ofSampleLaw`**: the families from jointly measurable data and the
  one-sample laws of the sections at almost every frozen sample and every frozen time;
* **`cover_of_clock`**: the cap cover of the canonical image lifetime from caps above the canonical clock at every
  pre-contact own time (the deterministic form of the countable protected-rectangle exhaustion).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Family

open A1Canon A1Ref A1Core A1Frozen

/-! ### The degenerate cap -/

section Zero

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ}
  {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {N : ℝ≥0 → Ω → ℝ} {Scap : ℕ → Ω → ℝ≥0} {m : ℕ}

/-- **The one-sample law at a zero cap**: a continuous Brownian motion of any filtration under `Q` and a noise
starting at `0` suffice (the cap event is empty and the agreement is at time `0` only). -/
theorem isSeedSampleLaw_of_cap_zero {Q : Measure Ω} {𝓗 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsFilteredBrownianReal 𝓗 B Q) (hBc : ∀ ω, Continuous (B · ω)) (hN0 : ∀ ω, N 0 ω = 0)
    (hS0 : ∀ ω, Scap m ω = 0) : IsSeedSampleLaw Q W ζ VL VR N Scap m := by
  have hE : ∀ s : ℝ≥0, {ω | s < Scap m ω} = ∅ := fun s => by
    ext ω
    simp only [mem_ofPred_eq, hS0, not_lt_zero, mem_empty_iff_false]
  refine ⟨𝓗, B, hB, hBc, fun s => by rw [hE]; exact @MeasurableSet.empty _ (𝓗 s),
    fun s g _ => by rw [hE, inter_empty]; exact @MeasurableSet.empty _ (𝓗 s), ?_⟩
  filter_upwards [hB.1.eval_zero_ae_eq_zero] with ω hω t ht
  rw [hS0, nonpos_iff_eq_zero] at ht
  rw [ht, hω, hN0]

end Zero

/-! ### The families -/

section Families

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {nL nR : ℕ}

/-- **A `FrozenFamily` from the one-sample laws of the sections** (conditioning curve on `Y`): jointly measurable
data indexed by the frozen time `σ`, a continuous noise from `0`, and for every cap `m`, almost every frozen sample `y`
and every frozen time `σ` the one-sample law of the sections at `y` of the canonical image at the stop `σ` under the
tilted law `D σ m (·, y) · P₁`. -/
def FrozenFamily.ofSampleLaw {P₁ : Measure X} {P₂ : Measure Y} {live : ℝ≥0 → Y → Prop} {xj : ℝ}
    {Wj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → Y → ℝ}
    (VL : ℝ≥0 → Fin nL → ℝ≥0 → X × Y → ℝ) (VR : ℝ≥0 → Fin nR → ℝ≥0 → X × Y → ℝ)
    (N : ℝ≥0 → ℝ≥0 → X × Y → ℝ) (S : ℝ≥0 → ℕ → X × Y → ℝ≥0) (D : ℝ≥0 → ℕ → X × Y → ℝ≥0∞)
    (hVL : ∀ i t, Measurable fun p : ℝ≥0 × (X × Y) => VL p.1 i t p.2)
    (hVR : ∀ j t, Measurable fun p : ℝ≥0 × (X × Y) => VR p.1 j t p.2)
    (hNc : ∀ σ z, Continuous (N σ · z)) (hN0 : ∀ σ z, N σ 0 z = 0)
    (hN : ∀ t, Measurable fun p : ℝ≥0 × (X × Y) => N p.1 t p.2)
    (hS : ∀ m, Measurable fun p : ℝ≥0 × (X × Y) => S p.1 m p.2)
    (hD : ∀ m, Measurable fun p : ℝ≥0 × (X × Y) => D p.1 m p.2)
    (hlaw : ∀ m, ∀ᵐ y ∂P₂, ∀ σ : ℝ≥0, IsSeedSampleLaw (P₁.withDensity fun x => D σ m (x, y))
      (fun t x => rDrv live xj Wj ζj xk Wk (fun _ => σ) t (x, y))
      (fun x => rLife live xj Wj ζj xk Wk (fun _ => σ) (x, y)) (fun i t x => VL σ i t (x, y))
      (fun j t x => VR σ j t (x, y)) (fun t x => N σ t (x, y)) (fun k x => S σ k (x, y)) m) :
    FrozenFamily P₁ P₂ live xj Wj ζj xk Wk nL nR where
  VL := VL
  VR := VR
  N := N
  S := S
  D := D
  measurable_VL := hVL
  measurable_VR := hVR
  continuous_N := hNc
  N_zero := hN0
  measurable_N := hN
  measurable_S := hS
  measurable_D := hD
  frozen m := (hlaw m).mono fun _ hy σ => (hy σ).isFrozenSampleLaw

/-- **A `FrozenFamilyFst` from the one-sample laws of the sections** (conditioning curve on `X`, mirror). -/
def FrozenFamilyFst.ofSampleLaw {P₁ : Measure X} {P₂ : Measure Y} {live : ℝ≥0 → X → Prop} {xj : ℝ}
    {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → X → ℝ}
    (VL : ℝ≥0 → Fin nL → ℝ≥0 → X × Y → ℝ) (VR : ℝ≥0 → Fin nR → ℝ≥0 → X × Y → ℝ)
    (N : ℝ≥0 → ℝ≥0 → X × Y → ℝ) (S : ℝ≥0 → ℕ → X × Y → ℝ≥0) (D : ℝ≥0 → ℕ → X × Y → ℝ≥0∞)
    (hVL : ∀ i t, Measurable fun p : ℝ≥0 × (X × Y) => VL p.1 i t p.2)
    (hVR : ∀ j t, Measurable fun p : ℝ≥0 × (X × Y) => VR p.1 j t p.2)
    (hNc : ∀ σ z, Continuous (N σ · z)) (hN0 : ∀ σ z, N σ 0 z = 0)
    (hN : ∀ t, Measurable fun p : ℝ≥0 × (X × Y) => N p.1 t p.2)
    (hS : ∀ m, Measurable fun p : ℝ≥0 × (X × Y) => S p.1 m p.2)
    (hD : ∀ m, Measurable fun p : ℝ≥0 × (X × Y) => D p.1 m p.2)
    (hlaw : ∀ m, ∀ᵐ x ∂P₁, ∀ σ : ℝ≥0, IsSeedSampleLaw (P₂.withDensity fun y => D σ m (x, y))
      (fun t y => rDrvFst live xj Wj ζj xk Wk (fun _ => σ) t (x, y))
      (fun y => rLifeFst live xj Wj ζj xk Wk (fun _ => σ) (x, y)) (fun i t y => VL σ i t (x, y))
      (fun j t y => VR σ j t (x, y)) (fun t y => N σ t (x, y)) (fun k y => S σ k (x, y)) m) :
    FrozenFamilyFst P₁ P₂ live xj Wj ζj xk Wk nL nR where
  VL := VL
  VR := VR
  N := N
  S := S
  D := D
  measurable_VL := hVL
  measurable_VR := hVR
  continuous_N := hNc
  N_zero := hN0
  measurable_N := hN
  measurable_S := hS
  measurable_D := hD
  frozen m := (hlaw m).mono fun _ hx σ => (hx σ).isFrozenSampleLawFst

end Families

/-! ### The cap cover of the canonical image lifetime -/

section Cover

/-- **Caps above the canonical clock at every pre-contact own time cover the canonical image lifetime**: the
lifetime is the supremum of the clock before the contact time. -/
theorem exists_cap_of_lt_imgLife {xj : ℝ} {wj : ℝ → ℝ} {ζj : ℝ≥0∞} {xk : ℝ} {wk : ℝ → ℝ} {τ : ℝ}
    {S : ℕ → ℝ≥0}
    (hS : ∀ s : ℝ≥0, (s : ℝ≥0∞) < A2X.contactTime xj wj ζj xk wk τ → ∃ m, A1Ref.imgClk xj wj xk wk τ s ≤ S m)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < A1Ref.imgLife xj wj ζj xk wk τ) : ∃ m, t ≤ S m := by
  unfold A1Ref.imgLife at ht
  obtain ⟨s, hs⟩ := lt_iSup_iff.1 ht
  obtain ⟨hsc, hts⟩ := lt_iSup_iff.1 hs
  rw [← ENNReal.ofReal_coe_nnreal] at hts
  obtain ⟨m, hm⟩ := hS s hsc
  exact ⟨m, NNReal.coe_le_coe.1 ((ENNReal.ofReal_lt_ofReal_iff'.1 hts).1.le.trans hm)⟩

variable {X Y : Type*}

/-- **The cap cover at the stop `τ`** (conditioning curve on `Y`): on the live event, caps above the canonical clock
of the image at every pre-contact own time cover the masked canonical image lifetime. -/
theorem cover_of_clock {live : ℝ≥0 → Y → Prop} {xj : ℝ} {Wj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞} {xk : ℝ}
    {Wk : ℝ≥0 → Y → ℝ} {τ : Y → ℝ≥0} {S : ℕ → X × Y → ℝ≥0} {z : X × Y} (hlive : live (τ z.2) z.2)
    (hS : ∀ s : ℝ≥0, (s : ℝ≥0∞) < A2X.contactTime xj (Strip.extPath (Wj · z.1)) (ζj z.1) xk
        (Strip.extPath (Wk · z.2)) (τ z.2) →
      ∃ m, A1Ref.imgClk xj (Strip.extPath (Wj · z.1)) xk (Strip.extPath (Wk · z.2)) (τ z.2) s ≤ S m z) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < rLife live xj Wj ζj xk Wk τ z → ∃ m, t ≤ S m z := by
  intro t ht
  simp only [rLife, cImgLifeM, cImgLife, ite_eq_left hlive] at ht
  exact exists_cap_of_lt_imgLife hS ht

/-- **The cap cover at the stop `τ`** (conditioning curve on `X`, mirror). -/
theorem cover_of_clock_fst {live : ℝ≥0 → X → Prop} {xj : ℝ} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {xk : ℝ}
    {Wk : ℝ≥0 → X → ℝ} {τ : X → ℝ≥0} {S : ℕ → X × Y → ℝ≥0} {z : X × Y} (hlive : live (τ z.1) z.1)
    (hS : ∀ s : ℝ≥0, (s : ℝ≥0∞) < A2X.contactTime xj (Strip.extPath (Wj · z.2)) (ζj z.2) xk
        (Strip.extPath (Wk · z.1)) (τ z.1) →
      ∃ m, A1Ref.imgClk xj (Strip.extPath (Wj · z.2)) xk (Strip.extPath (Wk · z.1)) (τ z.1) s ≤ S m z) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < rLifeFst live xj Wj ζj xk Wk τ z → ∃ m, t ≤ S m z := by
  intro t ht
  simp only [rLifeFst, cImgLifeM, cImgLife, ite_eq_left hlive] at ht
  exact exists_cap_of_lt_imgLife hS ht

end Cover

end InteractingSLE.ZhanGT4.A1Family
