/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.Concat
import InteractingSLE.Spec.Restart.RetAux79Zone

/-!
# Loewner concatenation when the continuation touches the boundary

Packet PROVE-GW2-SWITCH (round 2). `LoewnerConcat.isGeneratingTrace_catPath` assumes the
continuation's trace stays in `ℍ` at positive times. Flow-line pieces of a switched GW2 schedule may
bounce off `ℝ` or off earlier pieces, so that premise fails. It is not needed:

* a generating trace lies in `ℍ̄` (`Restart.RetAux79.mem_Hbar_of_isGeneratingTrace`), which is all the
  continuity of the joined trace uses (`continuous_joinedTrace_bdry`);
* the boundary extension `F̄_a` of the prefix's inverse map sends no real point into `ℍ ∖ K_a`
  (`extendFrom_real_notMem_bdry`: `f_a ∘ F_a = id` and continuity of `f_a` at an interior image
  point would make that point's image real). Hence the part of the joined path in the prefix domain
  is still the image of the continuation's part in `ℍ` (`joinedTrace_inter_domain_bdry`);
* **`isGeneratingTrace_catPath_bdry`**: a closed continuous generating prefix followed by ANY
  generating trace of the continuation generates the concatenated driver, with the joined trace.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open InteractingSLE.Sec7.StripSideHeightProb

namespace InteractingSLE.LoewnerConcat

variable {w₀ w₁ : ℝ≥0 → ℝ} {η₀ η₁ : ℝ≥0 → ℂ} {a : ℝ≥0}

/-- A generating trace on `[0, ∞)` of a continuous driver lies in `ℍ̄`. -/
theorem trace_mem_Hbar_bdry (h₁ : Continuous w₁) (h10 : w₁ 0 = 0)
    (hη₁ : IsGeneratingTrace w₁ ⊤ η₁) (s : ℝ≥0) : η₁ s ∈ Hbar :=
  Restart.RetAux79.mem_Hbar_of_isGeneratingTrace hη₁ h₁ h10 ENNReal.coe_lt_top

/-- **The boundary extension of the prefix map sends no real point into the prefix domain.** -/
theorem extendFrom_real_notMem_bdry (h₀ : Continuous w₀) (h00 : w₀ 0 = 0)
    (hη₀ : IsGeneratingTrace w₀ a η₀) {p : ℂ} (hp : p.im = 0) :
    extendFrom H (fwdMapInv (Ito.rpath w₀) a) p ∉ H \ fwdHull (Ito.rpath w₀) a := by
  intro hx
  have hW : Continuous (Ito.rpath w₀) := h₀.comp continuous_real_toNNReal
  have hW0 : Ito.rpath w₀ 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using h00
  have ha : (0 : ℝ) ≤ a := a.coe_nonneg
  have hpH : p ∈ Hbar := by
    change 0 ≤ p.im
    rw [hp]
  have hNB : (𝓝[H] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact hpH)
  have hB := (prefix_boundary h₀ h00 hη₀).1
  have hfc : ContinuousAt (fwdMap (Ito.rpath w₀) a) (extendFrom H (fwdMapInv (Ito.rpath w₀) a) p) :=
    ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ha).differentiableAt
      ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW ha).mem_nhds hx)).continuousAt
  have h1 := hfc.tendsto.comp (hB.tendsto hpH)
  have h2 : Tendsto (fun y => fwdMap (Ito.rpath w₀) a (fwdMapInv (Ito.rpath w₀) a y))
      (𝓝[H] p) (𝓝 p) := by
    refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 ha hy).symm
  have h3 := tendsto_nhds_unique h1 h2
  have h4 : (0 : ℝ) < (fwdMap (Ito.rpath w₀) a (extendFrom H (fwdMapInv (Ito.rpath w₀) a) p)).im :=
    QuantumZipper.FwdHolo.mapsTo_fwdMap hW ha hx
  rw [h3, hp] at h4
  exact lt_irrefl 0 h4

/-- The joined trace is continuous for any generating continuation (no `ℍ`-avoidance needed). -/
theorem continuous_joinedTrace_bdry (h₀ : Continuous w₀) (h00 : w₀ 0 = 0)
    (h₁ : Continuous w₁) (h10 : w₁ 0 = 0)
    (hη₀ : IsGeneratingTrace w₀ a η₀) (hη₁ : IsGeneratingTrace w₁ ⊤ η₁) :
    Continuous (joinedTrace w₀ η₀ a η₁) := by
  obtain ⟨hb, htip⟩ := prefix_boundary h₀ h00 hη₀
  have hc₁ : Continuous η₁ := continuousOn_univ.1
    (hη₁.2.1.mono (fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top))
  have hbar : ∀ s, η₁ s ∈ Hbar := trace_mem_Hbar_bdry h₁ h10 hη₁
  have hleft : Continuous (fun t : ℝ≥0 => η₀ (min t a)) :=
    hη₀.2.1.comp_continuous (continuous_id.min continuous_const)
      (fun _ => ENNReal.coe_le_coe.2 (min_le_right _ _))
  have hright : Continuous (fun t : ℝ≥0 =>
      extendFrom H (fwdMapInv (Ito.rpath w₀) a) (η₁ (t - a))) :=
    hb.continuousOn.comp_continuous (hc₁.comp (continuous_id.sub continuous_const))
      (fun t => hbar (t - a))
  have hc := Continuous.if_le hleft hright continuous_id (continuous_const (y := a))
    (fun t (ht : t = a) => by rw [ht, min_self, tsub_self, hη₁.1, htip])
  refine hc.congr fun t => ?_
  by_cases ht : t ≤ a
  · simp only [joinedTrace, id_eq, ht, ↓reduceIte, min_eq_left ht]
  · simp only [joinedTrace, id_eq, ht, ↓reduceIte]

/-- The part of the joined path inside the prefix domain is the inverse image of the continuation's
part in `ℍ`, for any generating continuation. -/
theorem joinedTrace_inter_domain_bdry (h₀ : Continuous w₀) (h00 : w₀ 0 = 0)
    (h₁ : Continuous w₁) (h10 : w₁ 0 = 0)
    (hη₀ : IsGeneratingTrace w₀ a η₀) (hη₁ : IsGeneratingTrace w₁ ⊤ η₁)
    (hK : fwdHull (Ito.rpath w₀) a = fillH (η₀ '' Icc 0 a)) (s : ℝ≥0) :
    (joinedTrace w₀ η₀ a η₁ '' Icc 0 (a + s)) ∩ (H \ fwdHull (Ito.rpath w₀) a) =
      fwdMapInv (Ito.rpath w₀) a '' ((η₁ '' Icc 0 s) ∩ H) := by
  have hW : Continuous (Ito.rpath w₀) := h₀.comp continuous_real_toNNReal
  have hW0 : Ito.rpath w₀ 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using h00
  have hF : ∀ z ∈ H, extendFrom H (fwdMapInv (Ito.rpath w₀) a) z =
      fwdMapInv (Ito.rpath w₀) a z := fun z hz =>
    extendFrom_H_eq (continuousOn_fwdMapInv hW hW0 a.coe_nonneg) hz
  ext z
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hz⟩
    by_cases hta : t ≤ a
    · rw [joinedTrace_of_le hta] at hz
      exact False.elim (hz.2 (hK ▸ ⟨hz.1, Or.inl (subset_closure ⟨t, ⟨ht.1, hta⟩, rfl⟩)⟩))
    · have hext : joinedTrace w₀ η₀ a η₁ t =
          extendFrom H (fwdMapInv (Ito.rpath w₀) a) (η₁ (t - a)) := by
        simp only [joinedTrace, hta, ↓reduceIte]
      have hηH : η₁ (t - a) ∈ H := by
        by_contra hnot
        have hbar := trace_mem_Hbar_bdry h₁ h10 hη₁ (t - a)
        have him : (η₁ (t - a)).im = 0 :=
          le_antisymm (not_lt.1 hnot) hbar
        rw [hext] at hz
        exact extendFrom_real_notMem_bdry h₀ h00 hη₀ him hz
      have heq : joinedTrace w₀ η₀ a η₁ t = fwdMapInv (Ito.rpath w₀) a (η₁ (t - a)) := by
        rw [hext]
        exact hF _ hηH
      exact ⟨η₁ (t - a), ⟨⟨t - a, ⟨bot_le,
        tsub_le_iff_right.2 (by simpa only [add_comm] using ht.2)⟩, rfl⟩,
        hηH⟩, heq.symm⟩
  · rintro ⟨v, ⟨⟨t, ht, rfl⟩, hvH⟩, rfl⟩
    have htpos : 0 < t := by
      by_contra h
      have ht0 : t = 0 := le_antisymm (not_lt.1 h) bot_le
      rw [ht0, hη₁.1] at hvH
      exact lt_irrefl 0 (show 0 < (0 : ℂ).im from hvH)
    refine ⟨⟨a + t, ⟨bot_le, add_le_add_right ht.2 a⟩, ?_⟩,
      QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 a.coe_nonneg hvH⟩
    rw [joinedTrace_add htpos, hF _ hvH]

end InteractingSLE.LoewnerConcat
