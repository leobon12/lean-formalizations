/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.MeanIdentArc
import InteractingSLE.WangWu.Prop418Side
import QuantumZipper.Proofs.Loewner.ArcDeterminesDriver
import QuantumZipper.Proofs.Loewner.CaraR8

/-!
# Wang–Wu Proposition 4.18: a simple Loewner trace is determined by its range

Packet PROVE-WW-B6. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), last paragraph of the
proof of Proposition 4.18 (text dump L1649–1653):

> Lemma 4.1 makes the oriented forward range a function of `h`. **Half-plane capacity determines the parameter of a
> simple Loewner trace, so the complete hull history is determined.**

This file proves the deterministic statement in brackets:

* `IsProperArc.exists_reparam_of_arcRange_subset`: if the range of a simple proper arc `γ₂` lies in the range of
  another, `γ₁`, then `γ₂ = γ₁ ∘ φ` for a continuous strictly increasing `φ` with `φ 0 = 0`, and initial pieces
  correspond: `γ₂((0, t]) = γ₁((0, φ t])` (the inverse `φ = γ₁⁻¹ ∘ γ₂` is continuous because a proper arc maps closed
  time sets to closed sets, `IsProperArc.isClosed_image`; continuous and injective, it is monotone).
* **`eqOn_of_arcRange_eq`**: two simple proper Loewner traces (`IsLoewnerTrace` of continuous drivers from `0`,
  capacity parametrization) with the same range are equal, and so are their drivers. Equal ranges give equal hulls
  `K²_t = K¹_{φ(t)}`; equal simple hulls have equal half-plane capacity, so `φ(t) = t` (QuantumZipper's
  `ArcDriver.fwdHull_eq_imp`, with the Carathéodory input `CaraR.revMapCaratheodory`), and the centred maps then force
  equal drivers (`ArcDriver.eqOn_of_fwdMap_rel`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.WangWu

/-! ### Reparametrization of proper arcs with nested ranges -/

namespace IsProperArc

variable {γ₁ γ₂ : ℝ → ℂ}

/-- **Reparametrization.** If the range of a simple proper arc `γ₂` lies in that of `γ₁`, then `γ₂ = γ₁ ∘ φ` on
`[0, ∞)` for a continuous strictly increasing `φ ≥ 0` with `φ 0 = 0`. -/
theorem exists_reparam_of_arcRange_subset (hγ₁ : IsProperArc γ₁) (hγ₂ : IsProperArc γ₂)
    (hsub : arcRange γ₂ ⊆ arcRange γ₁) :
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Ici 0) ∧ StrictMonoOn φ (Ici 0) ∧ φ 0 = 0 ∧
      ∀ s, 0 ≤ s → 0 ≤ φ s ∧ γ₁ (φ s) = γ₂ s := by
  set φ : ℝ → ℝ := fun s => Function.invFunOn γ₁ (Ici 0) (γ₂ s) with hφdef
  have hφ : ∀ s, 0 ≤ s → 0 ≤ φ s ∧ γ₁ (φ s) = γ₂ s := fun s hs => by
    have hm : γ₂ s ∈ γ₁ '' Ici 0 := hsub ⟨s, mem_Ici.2 hs, rfl⟩
    exact ⟨Function.invFunOn_mem hm, Function.invFunOn_eq hm⟩
  have hφ0 : φ 0 = 0 :=
    hγ₁.inj (mem_Ici.2 (hφ 0 le_rfl).1) (mem_Ici.2 le_rfl) (by rw [(hφ 0 le_rfl).2, hγ₂.zero, hγ₁.zero])
  have hinj : InjOn φ (Ici 0) := fun s hs s' hs' e =>
    hγ₂.inj hs hs' (by rw [← (hφ s hs).2, ← (hφ s' hs').2, e])
  have hcont : ContinuousOn φ (Ici 0) := by
    rw [continuousOn_iff_isClosed]
    intro F hF
    have hG : IsClosed (γ₁ '' (F ∩ Ici 0)) := hγ₁.isClosed_image (hF.inter isClosed_Ici) inter_subset_right
    refine ⟨Ici 0 ∩ γ₂ ⁻¹' (γ₁ '' (F ∩ Ici 0)),
      hγ₂.cont.preimage_isClosed_of_isClosed isClosed_Ici hG, ?_⟩
    ext s
    simp only [mem_inter_iff, mem_preimage, mem_image, mem_Ici]
    constructor
    · rintro ⟨hsF, hs⟩
      exact ⟨⟨hs, φ s, ⟨hsF, (hφ s hs).1⟩, (hφ s hs).2⟩, hs⟩
    · rintro ⟨⟨hs, r, ⟨hrF, hr⟩, e⟩, -⟩
      refine ⟨?_, hs⟩
      have : φ s = r := hγ₁.inj (mem_Ici.2 (hφ s hs).1) (mem_Ici.2 hr) ((hφ s hs).2.trans e.symm)
      rw [this]
      exact hrF
  refine ⟨φ, hcont, ?_, hφ0, hφ⟩
  intro s hs s' hs' hss'
  have hn : (0 : ℝ) ≤ s' := hs'
  rcases ContinuousOn.strictMonoOn_of_injOn_Icc' hn (hcont.mono Icc_subset_Ici_self)
      (hinj.mono Icc_subset_Ici_self) with hmono | hanti
  · exact hmono ⟨hs, hss'.le⟩ ⟨hn, le_rfl⟩ hss'
  · exfalso
    have h1 := hanti ⟨le_rfl, hn⟩ ⟨hn, le_rfl⟩ (lt_of_le_of_lt (mem_Ici.1 hs) hss')
    rw [hφ0] at h1
    exact absurd (hφ s' hn).1 (not_le.2 h1)

/-- Under the reparametrization, initial pieces correspond: `γ₂((0, t]) = γ₁((0, φ t])`. -/
theorem image_Ioc_eq_of_reparam {φ : ℝ → ℝ} (hc : ContinuousOn φ (Ici 0))
    (hm : StrictMonoOn φ (Ici 0)) (h0 : φ 0 = 0) (hφ : ∀ s, 0 ≤ s → 0 ≤ φ s ∧ γ₁ (φ s) = γ₂ s) {t : ℝ}
    (ht : 0 ≤ t) : γ₂ '' Ioc 0 t = γ₁ '' Ioc 0 (φ t) := by
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨φ s, ⟨?_, hm.monotoneOn (mem_Ici.2 hs.1.le) (mem_Ici.2 ht) hs.2⟩, (hφ s hs.1.le).2⟩
    have := hm (mem_Ici.2 le_rfl) (mem_Ici.2 hs.1.le) hs.1
    rwa [h0] at this
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨s, hs, e⟩ := intermediate_value_Icc ht (hc.mono Icc_subset_Ici_self)
      (show r ∈ Icc (φ 0) (φ t) by rw [h0]; exact ⟨hr.1.le, hr.2⟩)
    refine ⟨s, ⟨lt_of_le_of_ne hs.1 fun h => ?_, hs.2⟩, by rw [← (hφ s hs.1).2, e]⟩
    rw [← h, h0] at e
    exact absurd e (ne_of_lt hr.1)

end IsProperArc

/-! ### A simple Loewner trace is determined by its range -/

section Range

variable {W₁ W₂ : ℝ → ℝ} {η₁ η₂ : ℝ → ℂ}

/-- The hull of a simple proper trace at a positive time is a simple curve hull. -/
theorem isSimpleCurveHull_fwdHull (hη : IsLoewnerTrace W₁ η₁) (hγ : IsProperArc η₁) {a : ℝ} (ha : 0 < a) :
    QuantumZipper.IsSimpleCurveHull (fwdHull W₁ a) := by
  refine ⟨fun u => η₁ (a * u), ?_, ?_, ?_, ?_, ?_⟩
  · exact hγ.cont.comp (continuousOn_const.mul continuousOn_id) fun u hu =>
      mem_Ici.2 (mul_nonneg ha.le hu.1)
  · intro u hu u' hu' e
    have := hγ.inj (mem_Ici.2 (mul_nonneg ha.le hu.1)) (mem_Ici.2 (mul_nonneg ha.le hu'.1)) e
    exact mul_left_cancel₀ ha.ne' this
  · simp [hγ.zero]
  · intro u hu
    exact hγ.mem_H _ (mul_pos ha hu.1)
  · rw [fwdHull_eq_image_Ioc hη hγ ha.le]
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s / a, ⟨div_pos hs.1 ha, (div_le_one ha).2 hs.2⟩, ?_⟩
      simp only
      rw [mul_div_cancel₀ s ha.ne']
    · rintro ⟨u, hu, rfl⟩
      exact ⟨a * u, ⟨mul_pos ha hu.1, by nlinarith [hu.2]⟩, rfl⟩

/-- **A simple proper Loewner trace is determined by its range** (Wang–Wu, proof of Proposition 4.18: "Half-plane
capacity determines the parameter of a simple Loewner trace, so the complete hull history is determined"). Two simple
proper arcs that are continuous Loewner traces of continuous drivers from `0` (capacity parametrization) and have the
same range coincide on `[0, ∞)`, and so do their drivers. -/
theorem eqOn_of_arcRange_eq (hη₁ : IsLoewnerTrace W₁ η₁) (hη₂ : IsLoewnerTrace W₂ η₂)
    (hγ₁ : IsProperArc η₁) (hγ₂ : IsProperArc η₂) (hW₁ : Continuous W₁) (hW₂ : Continuous W₂)
    (hW₁0 : W₁ 0 = 0) (hW₂0 : W₂ 0 = 0) (heq : arcRange η₁ = arcRange η₂) :
    EqOn η₁ η₂ (Ici 0) ∧ EqOn W₁ W₂ (Ici 0) := by
  obtain ⟨φ, hc, hm, h0, hφ⟩ := hγ₁.exists_reparam_of_arcRange_subset hγ₂ heq.symm.le
  -- equal hulls at corresponding times, hence equal times
  have hhull : ∀ t, 0 < t → fwdHull W₂ t = fwdHull W₁ (φ t) := fun t ht => by
    have hφt : 0 < φ t := by
      have := hm (mem_Ici.2 le_rfl) (mem_Ici.2 ht.le) ht
      rwa [h0] at this
    rw [fwdHull_eq_image_Ioc hη₂ hγ₂ ht.le, fwdHull_eq_image_Ioc hη₁ hγ₁ hφt.le,
      IsProperArc.image_Ioc_eq_of_reparam hc hm h0 hφ ht.le]
  have himp : ∀ t, 0 < t → φ t = t ∧ ∀ w ∈ H \ fwdHull W₁ (φ t),
      fwdMap W₂ t w + W₂ t = fwdMap W₁ (φ t) w + W₁ (φ t) := fun t ht => by
    have hφt : 0 < φ t := by
      have := hm (mem_Ici.2 le_rfl) (mem_Ici.2 ht.le) ht
      rwa [h0] at this
    exact QuantumZipper.ArcDriver.fwdHull_eq_imp QuantumZipper.CaraR.revMapCaratheodory hW₁ hW₂ hW₁0 hW₂0
      hφt ht (isSimpleCurveHull_fwdHull hη₁ hγ₁ hφt) (hhull t ht)
  have hφid : ∀ t, 0 ≤ t → φ t = t := fun t ht => by
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h, h0]
    · exact (himp t h).1
  refine ⟨fun t ht => ?_, fun T hT => ?_⟩
  · rw [← (hφ t ht).2, hφid t ht]
  · rcases eq_or_lt_of_le (mem_Ici.1 hT) with h | h
    · rw [← h, hW₁0, hW₂0]
    have hsame : fwdHull W₂ T = fwdHull W₁ T := by rw [hhull T h, hφid T h.le]
    have hrel : ∀ s ∈ Ioc 0 T, ∀ w ∈ H \ fwdHull W₁ s, fwdMap W₂ s w + W₂ s = fwdMap W₁ s w + W₁ s := by
      intro s hs w hw
      have := (himp s hs.1).2 w (by rw [(himp s hs.1).1]; exact hw)
      rwa [(himp s hs.1).1] at this
    exact QuantumZipper.ArcDriver.eqOn_of_fwdMap_rel hW₁ hW₂ hW₁0 hW₂0 h hsame hrel ⟨le_rfl.trans (le_of_lt h), le_rfl⟩

end Range

end InteractingSLE.WangWu
