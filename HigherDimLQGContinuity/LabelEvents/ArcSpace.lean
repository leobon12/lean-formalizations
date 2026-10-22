import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Topology.Junction
import HigherDimLQGContinuity.Witness.Basic
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# The arc space of source arcs (packet Q5; Part B `b:def-arcspace`, `b:lem-arcspace`)

Source: [C] §4.1, l. 701–711 (measurability of the label events); planning audit NA2, item 13, R8 (the compact path
space and the closed existence events), Details (b) (`β > 0` is needed for closedness); blueprint Part B
`b:def-arcspace`, `b:lem-arcspace`.

* `ArcSpace Kt A α β`: the continuous arcs `γ : [0, 1] → ℝ^d` with image in `Kt` and the two-sided moduli (4.1)
  `|γ s - γ t| ≤ A |s - t|^α`, `|s - t| ≤ A |γ s - γ t|^β` (NA2's shape), with the compact-open (= uniform) topology;
  `mem_arcSpace_iff_arcModuli` relates it to packet Q1's `Topology.ArcModuli` of the real-parameter extension.
* `isClosed_arcSpace` (`Kt` closed, `β ≥ 0`) and `isCompact_arcSpace` (`Kt` compact, `α, β > 0`; Arzelà–Ascoli:
  the first modulus makes the family equicontinuous, and the pointwise image is a closed subset of `∏ Kt`).
* `isClosed_exists_arc` (`b:lem-arcspace`(b), NA2's shape): for a closed `S ⊆ X × C([0, 1], ℝ^d) × ℝ`, the set of
  `x` with an arc of the arc space and an own length `ℓ ∈ [ℓ₀, ℓ₁]` with `(x, γ, ℓ) ∈ S` is closed (projection
  along a compact factor, `isClosedMap_fst_of_compactSpace`); `isClosed_exists_arc_of_inter` only needs `S` to be
  closed relative to `X × ArcSpace × [ℓ₀, ℓ₁]`, which is how the source events use it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

variable {d : ℕ}

/-- The arc space (Part B `b:def-arcspace`, NA2 shape): continuous arcs `[0, 1] → Kt` with the two-sided moduli
(4.1), as a subset of `C([0, 1], ℝ^d)` with the compact-open (uniform) topology. -/
def ArcSpace (Kt : Set (Rd d)) (A α β : ℝ) : Set C(unitInterval, Rd d) :=
  {γ | (∀ t, γ t ∈ Kt) ∧ ∀ s t : unitInterval,
    ‖γ s - γ t‖ ≤ A * |(s : ℝ) - t| ^ α ∧ |(s : ℝ) - t| ≤ A * ‖γ s - γ t‖ ^ β}

/-- The pointwise form of the arc space: maps `[0, 1] → ℝ^d` (not assumed continuous) with image in `Kt` and the
two moduli. -/
def q5ArcFun (Kt : Set (Rd d)) (A α β : ℝ) : Set (unitInterval → Rd d) :=
  {f | (∀ t, f t ∈ Kt) ∧ ∀ s t : unitInterval,
    ‖f s - f t‖ ≤ A * |(s : ℝ) - t| ^ α ∧ |(s : ℝ) - t| ≤ A * ‖f s - f t‖ ^ β}

theorem mem_arcSpace_iff {Kt : Set (Rd d)} {A α β : ℝ} {γ : C(unitInterval, Rd d)} :
    γ ∈ ArcSpace Kt A α β ↔ (∀ t, γ t ∈ Kt) ∧ ∀ s t : unitInterval,
      ‖γ s - γ t‖ ≤ A * |(s : ℝ) - t| ^ α ∧ |(s : ℝ) - t| ≤ A * ‖γ s - γ t‖ ^ β :=
  Iff.rfl

theorem ArcSpace.mem {Kt : Set (Rd d)} {A α β : ℝ} {γ : C(unitInterval, Rd d)}
    (hγ : γ ∈ ArcSpace Kt A α β) (t : unitInterval) : γ t ∈ Kt :=
  hγ.1 t

theorem ArcSpace.norm_sub_le {Kt : Set (Rd d)} {A α β : ℝ} {γ : C(unitInterval, Rd d)}
    (hγ : γ ∈ ArcSpace Kt A α β) (s t : unitInterval) : ‖γ s - γ t‖ ≤ A * |(s : ℝ) - t| ^ α :=
  (hγ.2 s t).1

theorem ArcSpace.abs_sub_le {Kt : Set (Rd d)} {A α β : ℝ} {γ : C(unitInterval, Rd d)}
    (hγ : γ ∈ ArcSpace Kt A α β) (s t : unitInterval) : |(s : ℝ) - t| ≤ A * ‖γ s - γ t‖ ^ β :=
  (hγ.2 s t).2

/-- The arc space in terms of packet Q1's `Topology.ArcModuli` of the real-parameter extension `witExt γ`
(`γ ∘ projIcc`). -/
theorem mem_arcSpace_iff_arcModuli {Kt : Set (Rd d)} {A α β : ℝ} {γ : C(unitInterval, Rd d)} :
    γ ∈ ArcSpace Kt A α β ↔ (∀ t, γ t ∈ Kt) ∧ Topology.ArcModuli (witExt γ) A α β := by
  constructor
  · rintro ⟨hK, hmod⟩
    refine ⟨hK, fun s hs t ht => ?_⟩
    rw [witExt_of_mem γ hs, witExt_of_mem γ ht]
    exact hmod ⟨s, hs⟩ ⟨t, ht⟩
  · rintro ⟨hK, hmod⟩
    refine ⟨hK, fun s t => ?_⟩
    have h := hmod s s.2 t t.2
    rwa [witExt_coe, witExt_coe] at h

/-! ## Closedness -/

/-- The arc space is closed when `Kt` is closed and `β ≥ 0` (for `β < 0`, `0 ^ β = 0` in Lean and the inverse
modulus is not a closed condition). -/
theorem isClosed_arcSpace {Kt : Set (Rd d)} (hKt : IsClosed Kt) {A α β : ℝ} (hβ : 0 ≤ β) :
    IsClosed (ArcSpace Kt A α β) := by
  have h1 : IsClosed {γ : C(unitInterval, Rd d) | ∀ t, γ t ∈ Kt} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun t => hKt.preimage (continuous_eval_const t)
  have h2 : IsClosed {γ : C(unitInterval, Rd d) | ∀ s t : unitInterval,
      ‖γ s - γ t‖ ≤ A * |(s : ℝ) - t| ^ α ∧ |(s : ℝ) - t| ≤ A * ‖γ s - γ t‖ ^ β} := by
    simp only [ofPred_forall, ofPred_and]
    refine isClosed_iInter fun s => isClosed_iInter fun t => IsClosed.inter ?_ ?_
    · exact isClosed_le ((continuous_eval_const s).sub (continuous_eval_const t)).norm continuous_const
    · exact isClosed_le continuous_const (continuous_const.mul ((Real.continuous_rpow_const hβ).comp
        ((continuous_eval_const s).sub (continuous_eval_const t)).norm))
  rw [ArcSpace, ofPred_and]
  exact h1.inter h2

/-- The pointwise arc space is closed in the product topology. -/
theorem q5_isClosed_arcFun {Kt : Set (Rd d)} (hKt : IsClosed Kt) {A α β : ℝ} (hβ : 0 ≤ β) :
    IsClosed (q5ArcFun Kt A α β) := by
  have h1 : IsClosed {f : unitInterval → Rd d | ∀ t, f t ∈ Kt} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun t => hKt.preimage (continuous_apply t)
  have h2 : IsClosed {f : unitInterval → Rd d | ∀ s t : unitInterval,
      ‖f s - f t‖ ≤ A * |(s : ℝ) - t| ^ α ∧ |(s : ℝ) - t| ≤ A * ‖f s - f t‖ ^ β} := by
    simp only [ofPred_forall, ofPred_and]
    refine isClosed_iInter fun s => isClosed_iInter fun t => IsClosed.inter ?_ ?_
    · exact isClosed_le ((continuous_apply s).sub (continuous_apply t)).norm continuous_const
    · exact isClosed_le continuous_const (continuous_const.mul ((Real.continuous_rpow_const hβ).comp
        ((continuous_apply s).sub (continuous_apply t)).norm))
  rw [q5ArcFun, ofPred_and]
  exact h1.inter h2

/-- The first modulus with a positive exponent makes a map continuous. -/
theorem q5_continuous_of_holder {f : unitInterval → Rd d} {A α : ℝ} (hα : 0 < α)
    (hf : ∀ s t : unitInterval, ‖f s - f t‖ ≤ A * |(s : ℝ) - t| ^ α) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous fun s : unitInterval => A * |(s : ℝ) - t| ^ α :=
    continuous_const.mul ((Real.continuous_rpow_const hα.le).comp
      (continuous_abs.comp (continuous_subtype_val.sub continuous_const)))
  have h0 : A * |((t : unitInterval) : ℝ) - t| ^ α = 0 := by
    rw [sub_self, abs_zero, Real.zero_rpow hα.ne', mul_zero]
  have hg : Tendsto (fun s : unitInterval => A * |(s : ℝ) - t| ^ α) (𝓝 t) (𝓝 0) := by
    have := hc.continuousAt (x := t)
    rwa [ContinuousAt, h0] at this
  exact squeeze_zero (fun _ => norm_nonneg _) (fun s => hf s t) hg

/-- The arc space is the set of continuous elements of the pointwise arc space; for `α > 0` every element of the
pointwise arc space is continuous. -/
theorem q5_image_toFun_arcSpace {Kt : Set (Rd d)} {A α β : ℝ} (hα : 0 < α) :
    ContinuousMap.toFun '' ArcSpace Kt A α β = q5ArcFun Kt A α β := by
  ext f
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact hγ
  · intro hf
    exact ⟨⟨f, q5_continuous_of_holder hα fun s t => (hf.2 s t).1⟩, hf, rfl⟩

/-- **Compactness of the arc space** (`b:lem-arcspace`(a)): Arzelà–Ascoli. -/
theorem isCompact_arcSpace {Kt : Set (Rd d)} (hKt : IsCompact Kt) {A α β : ℝ} (hα : 0 < α)
    (hβ : 0 < β) : IsCompact (ArcSpace Kt A α β) := by
  refine ArzelaAscoli.isCompact_of_equicontinuous _ ?_ ?_
  · rw [q5_image_toFun_arcSpace hα]
    refine (isCompact_univ_pi fun _ => hKt).of_isClosed_subset (q5_isClosed_arcFun hKt.isClosed hβ.le) ?_
    intro f hf t _
    exact hf.1 t
  · intro t
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    have hc : Continuous fun s : unitInterval => A * |(s : ℝ) - t| ^ α :=
      continuous_const.mul ((Real.continuous_rpow_const hα.le).comp
        (continuous_abs.comp (continuous_subtype_val.sub continuous_const)))
    have h0 : A * |((t : unitInterval) : ℝ) - t| ^ α = 0 := by
      rw [sub_self, abs_zero, Real.zero_rpow hα.ne', mul_zero]
    have hev : ∀ᶠ s : unitInterval in 𝓝 t, A * |(s : ℝ) - t| ^ α < ε := by
      have := hc.continuousAt (x := t)
      rw [ContinuousAt, h0] at this
      exact this (Iio_mem_nhds hε)
    filter_upwards [hev] with s hs
    intro γ
    rw [dist_eq_norm, norm_sub_rev]
    exact lt_of_le_of_lt (ArcSpace.norm_sub_le γ.2 s t) hs

/-! ## Closed existence events (`b:lem-arcspace`(b)) -/

/-- **Closed existence events, relative form**: if `S` is closed relative to `X × ArcSpace × [ℓ₀, ℓ₁]`, the set of
`x` with an arc and an own length in that compact factor is closed. -/
theorem isClosed_exists_arc_of_inter {X : Type*} [TopologicalSpace X] {Kt : Set (Rd d)}
    (hKt : IsCompact Kt) {A α β ℓ₀ ℓ₁ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (S : Set (X × C(unitInterval, Rd d) × ℝ))
    (hS : IsClosed (S ∩ (univ ×ˢ (ArcSpace Kt A α β ×ˢ Icc ℓ₀ ℓ₁)))) :
    IsClosed {x | ∃ γ ∈ ArcSpace Kt A α β, ∃ ℓ ∈ Icc ℓ₀ ℓ₁, (x, γ, ℓ) ∈ S} := by
  set C : Set (C(unitInterval, Rd d) × ℝ) := ArcSpace Kt A α β ×ˢ Icc ℓ₀ ℓ₁ with hCdef
  have hC : IsCompact C := (isCompact_arcSpace hKt hα hβ).prod isCompact_Icc
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let ι : X × C → X × C(unitInterval, Rd d) × ℝ := fun p => (p.1, (p.2 : C(unitInterval, Rd d) × ℝ))
  have hι : Continuous ι := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hT : IsClosed (ι ⁻¹' (S ∩ (univ ×ˢ C))) := hS.preimage hι
  have heq : {x | ∃ γ ∈ ArcSpace Kt A α β, ∃ ℓ ∈ Icc ℓ₀ ℓ₁, (x, γ, ℓ) ∈ S} =
      Prod.fst '' (ι ⁻¹' (S ∩ (univ ×ˢ C))) := by
    ext x
    constructor
    · rintro ⟨γ, hγ, ℓ, hℓ, hS'⟩
      exact ⟨(x, ⟨(γ, ℓ), hγ, hℓ⟩), ⟨hS', mem_univ _, hγ, hℓ⟩, rfl⟩
    · rintro ⟨⟨x', ⟨⟨γ, ℓ⟩, hγ, hℓ⟩⟩, ⟨hS', -⟩, rfl⟩
      exact ⟨γ, hγ, ℓ, hℓ, hS'⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace _ hT

/-- **Closed existence events** (`b:lem-arcspace`(b), NA2's shape `isClosed_exists_arc`): projection along the
compact factor `ArcSpace × [ℓ₀, ℓ₁]` (`isClosedMap_fst_of_compactSpace`). -/
theorem isClosed_exists_arc {X : Type*} [TopologicalSpace X] {Kt : Set (Rd d)}
    (hKt : IsCompact Kt) {A α β ℓ₀ ℓ₁ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (S : Set (X × C(unitInterval, Rd d) × ℝ)) (hS : IsClosed S) :
    IsClosed {x | ∃ γ ∈ ArcSpace Kt A α β, ∃ ℓ ∈ Icc ℓ₀ ℓ₁, (x, γ, ℓ) ∈ S} :=
  isClosed_exists_arc_of_inter hKt hα hβ S
    (hS.inter (isClosed_univ.prod ((isClosed_arcSpace hKt.isClosed hβ.le).prod isClosed_Icc)))

end HigherDimLQGContinuity
