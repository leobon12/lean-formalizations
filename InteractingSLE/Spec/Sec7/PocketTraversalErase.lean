/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketTraversal
import InteractingSLE.Spec.Sec7.Lemma71Capacity
import InteractingSLE.Spec.Sec6.Aux41Full
import InteractingSLE.Spec.Sec6.Aux40InfLoewner

/-!
# The erased pocket traversal in its Jordan coordinate is a curve with local drivers

Packet PROVE-STRIPSYS10 (specification §7.4.1, proof of Lemma 7.25, p. 414: "the erased counterflow is therefore a
complete continuous traversal […] with a continuous relative driver"; Aux. lemmas 40–41, pp. 203–206).

Aux. lemma 41 (`Sec6.IsReversePocket.aux41`, `Sec6.IsReversePocketInf.aux41`) gives, for the pause-free erased path
`ζ = ψ ∘ γ̂_C` on its clock interval `[0, L)` (`L = ℓ(σ)`, resp. `ℓ(∞)`), a continuous Loewner driver on every
`[0, S']`, `S' < L`, with a continuous strictly increasing clock. Read on `[0, ∞)` through the reparametrization
`u ↦ L u/(1 + u)` (`relCurve ζ L`), this is exactly `IsDrivenCurve` (`PocketTraversal.lean`), so the erased traversal
has **one canonical relative driver** `segDriver (relCurve ζ L)` (an explicit formula in the filled prefixes),
continuous and vanishing at `0`, generating the filled prefixes, with the capacity reparametrization as a continuous
generating trace up to every capacity time below the terminal one.

The premises are those of Aux. lemmas 40–41 in the Lean development: the pathwise pocket hypotheses
(`IsReversePocket`, `IsReversePocketInf`), Aux. lemma 37's attachment constancy (`AttachmentConstancy`,
`AttachmentConstancyInf`) and a Jordan coordinate of the pocket.

## Main results

* `clockOf`, `relCurve`; `isDrivenCurve_relCurve`: local drivers on `[0, L)` give a driven curve on `[0, ∞)`;
* **`isDrivenCurve_relCurve_of_isReversePocket`**, **`isDrivenCurve_relCurve_of_isReversePocketInf`**;
* **`exists_relDriver_of_isReversePocket`**, **`exists_relDriver_of_isReversePocketInf`**: the continuous relative
  driver of the erased traversal, with its generating trace.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketTraversal

open Lemma71C

/-! ### The reparametrization `[0, ∞) → [0, L)` -/

/-- The clock reparametrization `u ↦ L u/(1 + u)`, an increasing bijection of `[0, ∞)` onto `[0, L)` for `L > 0`. -/
def clockOf (L u : ℝ) : ℝ := L * (u / (1 + u))

/-- **The relative curve** of a path `ζ` on `[0, L)`: `u ↦ ζ (L u/(1 + u))` on `[0, ∞)`. -/
def relCurve (ζ : ℝ → ℂ) (L : ℝ) (u : ℝ) : ℂ := ζ (clockOf L u)

variable {L : ℝ}

theorem clockOf_zero (L : ℝ) : clockOf L 0 = 0 := by simp [clockOf]

theorem clockOf_nonneg (hL : 0 < L) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ clockOf L u := by
  unfold clockOf
  positivity

theorem clockOf_lt (hL : 0 < L) {u : ℝ} (hu : 0 ≤ u) : clockOf L u < L := by
  unfold clockOf
  have h1 : u / (1 + u) < 1 := by rw [div_lt_one (by linarith)]; linarith
  calc L * (u / (1 + u)) < L * 1 := mul_lt_mul_of_pos_left h1 hL
    _ = L := mul_one L

theorem clockOf_mem_Ico (hL : 0 < L) {u : ℝ} (hu : 0 ≤ u) : clockOf L u ∈ Ico 0 L :=
  ⟨clockOf_nonneg hL hu, clockOf_lt hL hu⟩

theorem strictMonoOn_clockOf (hL : 0 < L) : StrictMonoOn (clockOf L) (Ici 0) := by
  intro a ha b hb hab
  unfold clockOf
  refine mul_lt_mul_of_pos_left ?_ hL
  have ha' : (0 : ℝ) < 1 + a := by linarith [mem_Ici.1 ha]
  have hb' : (0 : ℝ) < 1 + b := by linarith [mem_Ici.1 hb]
  rw [div_lt_div_iff₀ ha' hb']
  nlinarith

theorem continuousOn_clockOf (L : ℝ) : ContinuousOn (clockOf L) (Ici 0) := by
  unfold clockOf
  refine continuousOn_const.mul (continuousOn_id.div (continuousOn_const.add continuousOn_id) fun u hu => ?_)
  have : (0 : ℝ) ≤ u := hu
  positivity

/-- The reparametrization maps `[0, t]` onto `[0, clockOf L t]`. -/
theorem image_clockOf_Icc (hL : 0 < L) {t : ℝ} (ht : 0 ≤ t) : clockOf L '' Icc 0 t = Icc 0 (clockOf L t) := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨clockOf_nonneg hL hu.1, (strictMonoOn_clockOf hL).monotoneOn hu.1 ht hu.2⟩
  · intro hv
    have hc : ContinuousOn (clockOf L) (Icc 0 t) := (continuousOn_clockOf L).mono fun u hu => hu.1
    obtain ⟨u, hu, hut⟩ := intermediate_value_Icc ht hc ⟨by rw [clockOf_zero]; exact hv.1, hv.2⟩
    exact ⟨u, hu, hut⟩

theorem image_relCurve_Icc (ζ : ℝ → ℂ) (hL : 0 < L) {t : ℝ} (ht : 0 ≤ t) :
    relCurve ζ L '' Icc 0 t = ζ '' Icc 0 (clockOf L t) := by
  rw [← image_clockOf_Icc hL ht, image_image]
  rfl

/-! ### Local drivers on `[0, L)` give a driven curve on `[0, ∞)` -/

/-- **The relative curve is driven** when `ζ` is continuous on `[0, L)`, starts at `0`, and has on every `[0, S']`,
`0 < S' < L`, a continuous driver with a continuous strictly increasing clock generating its filled prefixes (the
conclusion of Aux. lemma 41). -/
theorem isDrivenCurve_relCurve {ζ : ℝ → ℂ} (hL : 0 < L) (hζc : ContinuousOn ζ (Ico 0 L)) (hζ0 : ζ 0 = 0)
    (hloc : ∀ S' : ℝ, 0 < S' → S' < L → ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∃ σ : ℝ → ℝ, σ 0 = 0 ∧
      StrictMonoOn σ (Icc 0 S') ∧ ContinuousOn σ (Icc 0 S') ∧
      ∀ t ∈ Icc 0 S', QuantumZipper.fwdHull W (σ t) = fillH (ζ '' Icc 0 t)) :
    IsDrivenCurve (relCurve ζ L) := by
  refine ⟨hζc.comp (continuousOn_clockOf L) fun u hu => clockOf_mem_Ico hL hu, ?_, fun S hS => ?_⟩
  · simp only [relCurve, clockOf_zero, hζ0]
  set S' := clockOf L S with hS'
  have hS'0 : 0 < S' := by
    have := strictMonoOn_clockOf hL (self_mem_Ici) (show S ∈ Ici (0 : ℝ) from hS.le) hS
    rwa [clockOf_zero] at this
  obtain ⟨W, hW, hW0, σ, hσ0, hσm, hσc, hK⟩ := hloc S' hS'0 (clockOf_lt hL hS.le)
  have hmaps : MapsTo (clockOf L) (Icc 0 S) (Icc 0 S') := fun u hu =>
    ⟨clockOf_nonneg hL hu.1, (strictMonoOn_clockOf hL).monotoneOn hu.1 hS.le hu.2⟩
  have hσnn : ∀ v ∈ Icc 0 S', 0 ≤ σ v := fun v hv => by
    rw [← hσ0]
    exact hσm.monotoneOn ⟨le_rfl, hS'0.le⟩ hv hv.1
  -- the capacity clock of the relative curve is `σ ∘ clockOf L`
  have hcap : ∀ t ∈ Icc 0 S, capClock (relCurve ζ L) t = σ (clockOf L t) := by
    intro t ht
    have hv := hmaps ht
    have hA : QuantumZipper.fwdHull W (σ (clockOf L t)) = fillH (relCurve ζ L '' Icc 0 t) := by
      rw [image_relCurve_Icc ζ hL ht.1]
      exact hK _ hv
    simp only [capClock, Lemma71.hcapSet_eq_of_fwdHull_eq hW hW0 (hσnn _ hv) hA]
    ring
  have hcap0 : capClock (relCurve ζ L) 0 = 0 := by
    rw [hcap 0 ⟨le_rfl, hS.le⟩, clockOf_zero, hσ0]
  refine ⟨W, hW, hW0, hcap0, ?_, ?_, fun t ht => ⟨?_, ?_⟩⟩
  · intro a ha b hb hab
    rw [hcap a ha, hcap b hb]
    exact hσm (hmaps ha) (hmaps hb) (strictMonoOn_clockOf hL ha.1 hb.1 hab)
  · refine (hσc.comp ((continuousOn_clockOf L).mono fun u hu => hu.1) hmaps).congr fun t ht => ?_
    exact hcap t ht
  · rw [hcap t ht]
    exact hσnn _ (hmaps ht)
  · rw [hcap t ht, image_relCurve_Icc ζ hL ht.1]
    exact hK _ (hmaps ht)

/-! ### The erased traversal of a reverse-contained pocket -/

section Pocket

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ β : ℝ → ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}

/-- **The erased traversal of a reverse-contained pocket (finite junction) is a driven curve** in a Jordan coordinate
(`x₀ ↦ ∞`, `y₀ ↦ 0`), under Aux. lemma 37's attachment constancy (Aux. lemmas 40–41). -/
theorem isDrivenCurve_relCurve_of_isReversePocket (hP : Sec6.IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : Sec6.AttachmentConstancy η C α₁ α₂ τ σ) (hψ : Sec6.IsJordanCoord C (α₁ 0) (α₁ 1) ψ) :
    IsDrivenCurve (relCurve (fun v => ψ (Sec6.erasedPath η C τ σ v)) (Sec6.pocketClock η C τ σ σ)) :=
  isDrivenCurve_relCurve (hP.clock_σ_pos hAC) (hP.continuousOn_ζ hAC hψ) (hP.ζ_zero hAC hψ)
    fun _ hS'0 hS' => (hP.aux41 hAC hψ hS'0 hS').1

/-- **The erased traversal of a reverse-contained pocket at infinity is a driven curve** in a Jordan coordinate at
infinity (`y₀ ↦ 0`), under the attachment constancy (Aux. lemmas 40–41 at infinity). -/
theorem isDrivenCurve_relCurve_of_isReversePocketInf (hP : Sec6.IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : Sec6.AttachmentConstancyInf η C α₁ α₂ τ) (hψ : Sec6.IsJordanCoordInf C (α₁ 0) ψ) :
    IsDrivenCurve (relCurve (fun v => ψ (Sec6.erasedPathInf η C τ v)) (Sec6.clockEnd η C τ)) :=
  isDrivenCurve_relCurve (hP.clockEnd_pos hAC) (hP.continuousOn_ζ hAC hψ) (hP.ζ_zero hAC hψ)
    fun _ hS'0 hS' => (hP.aux41 hAC hψ hS'0 hS').1

/-- **The continuous relative driver of the erased traversal** (finite junction; Lemma 7.25's proof, p. 414): the
canonical driver `segDriver γ` of the relative curve `γ` vanishes at `0`, is continuous below the terminal capacity
time, every erased prefix is its hull, and the capacity reparametrization of `γ` is a continuous generating trace on
`[0, T]` for every `T` below the terminal capacity time. -/
theorem exists_relDriver_of_isReversePocket (hP : Sec6.IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : Sec6.AttachmentConstancy η C α₁ α₂ τ σ) (hψ : Sec6.IsJordanCoord C (α₁ 0) (α₁ 1) ψ) :
    let γ := relCurve (fun v => ψ (Sec6.erasedPath η C τ σ v)) (Sec6.pocketClock η C τ σ σ)
    segDriver γ 0 = 0 ∧ ContinuousOn (segDriver γ) {s : ℝ≥0 | (s : ℝ≥0∞) < capLife γ} ∧
      (∀ v ∈ Ico 0 (Sec6.pocketClock η C τ σ σ), ∃ s : ℝ≥0, (s : ℝ≥0∞) < capLife γ ∧
        QuantumZipper.fwdHull (fun r : ℝ => segDriver γ r.toNNReal) s =
          fillH ((fun v => ψ (Sec6.erasedPath η C τ σ v)) '' Icc 0 v)) ∧
      ∀ T : ℝ≥0∞, T < capLife γ → IsGeneratingTrace (segDriver γ) T (capTrace γ) := by
  intro γ
  have hγ : IsDrivenCurve γ := isDrivenCurve_relCurve_of_isReversePocket hP hAC hψ
  have hL := hP.clock_σ_pos hAC
  obtain ⟨h0, hc, hK⟩ := hγ.segDriver_spec
  refine ⟨h0, hc, fun v hv => ?_, fun T hT => hγ.isGeneratingTrace hT⟩
  -- `v = clockOf L u` with `u = v/(L − v)`
  set Lc := Sec6.pocketClock η C τ σ σ with hLc
  have hLv : 0 < Lc - v := by linarith [hv.2]
  set u := v / (Lc - v) with hu
  have hu0 : 0 ≤ u := div_nonneg hv.1 hLv.le
  have hcl : clockOf Lc u = v := by
    simp only [clockOf, hu]
    have h1 : 1 + v / (Lc - v) = Lc / (Lc - v) := by field_simp; ring
    rw [h1]
    field_simp
  obtain ⟨s, hs, hsK⟩ := hK u hu0
  refine ⟨s, hs, ?_⟩
  rw [hsK, show γ = relCurve (fun v => ψ (Sec6.erasedPath η C τ σ v)) Lc from rfl,
    image_relCurve_Icc _ hL hu0, hcl]

end Pocket

end InteractingSLE.Sec7.PocketTraversal
