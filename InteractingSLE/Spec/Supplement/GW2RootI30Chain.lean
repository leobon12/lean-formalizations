/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootI30Mobius
import InteractingSLE.Spec.Supplement.GB6LawTrace
import InteractingSLE.Spec.Supplement.GB6Glue

/-!
# Fixed retained charts for chains based at any real point

Packet PROVE-T14-GW2ROOT2. The existing GB6 factorization and filling
transport do not restrict the moving chain's starting point. Applying
the translated Möbius theorem to both factors supplies its intrinsic
capacity clock, without a zero-root hypothesis.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H fwdHull)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootI30

open ConformalImage ConformalImageFull Sec5.CrossRestart Supp8.GB6

/-- A retained chart sends a chain from any real root to a Loewner chain
with its intrinsic capacity clock, before closed-hull contact. -/
theorem exists_relative_chain {W U : ℝ → ℝ} (hW : Continuous W)
    (hU : Continuous U) (hU0 : U 0 = 0) {s T : ℝ} (hs : 0 < s) (hT : 0 < T)
    {p : ℂ} (htip : Tendsto (QuantumZipper.fwdMapInv U s) (𝓝[H] 0) (𝓝 p))
    (hd : Disjoint (closure (fwdHull U s))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull W T))) :
    ∃ V : ℝ → ℝ, Continuous V ∧ relClock U s W 0 = 0 ∧
      StrictMonoOn (relClock U s W) (Icc 0 T) ∧
      ContinuousOn (relClock U s W) (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, 0 ≤ relClock U s W t ∧
        fwdHull V (relClock U s W t) = relMap U s '' fwdHull W t := by
  obtain ⟨x, r₁, A, gA, a, b, c, d, x₁, r₃, hx, hr₁, hd₁, hA, hgA, hdA,
    _, hdet, hc, _, _, hr₃, hclear, hfac⟩ :=
    exists_relMap_factor hW hU hU0 hs hT.le htip hd
  have hdet₁ : (0 : ℝ) < 1 * 1 - 0 * x := by norm_num
  obtain ⟨τ₁, W₁, hW₁, _, hτ₁0, hτ₁m, hτ₁c, h₁⟩ :=
    exists_mobius_chain hW hT hdet₁ hx hr₁ hd₁
  have hT₁ : 0 < τ₁ T := by
    rw [← hτ₁0]
    exact hτ₁m ⟨le_rfl, hT.le⟩ ⟨hT.le, le_rfl⟩ hT
  have hdA₁ : Disjoint (closure A) (closure (fwdHull W₁ (τ₁ T))) := by
    rw [(h₁ T ⟨hT.le, le_rfl⟩).2]
    exact hdA.mono_right (subset_insert _ _)
  obtain ⟨τ₂, W₂, hW₂, hτ₂0, hτ₂m, hτ₂c, h₂⟩ :=
    exists_loewner_image_of_pos hW₁ hT₁ hA hgA hdA₁
  have hT₂ : 0 < τ₂ (τ₁ T) := by
    rw [← hτ₂0]
    exact hτ₂m ⟨le_rfl, hT₁.le⟩ ⟨hT₁.le, le_rfl⟩ hT₁
  have hd₂ : Disjoint (ball (mobPole c d : ℂ) r₃) (fwdHull W₂ (τ₂ (τ₁ T))) := by
    rw [(h₂ _ ⟨hT₁.le, le_rfl⟩).2.1, (h₁ _ ⟨hT.le, le_rfl⟩).2]
    apply disjoint_left.mpr
    rintro _ hb ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact (not_lt_of_ge (hclear z hz)) (by simpa only [mem_ball, dist_eq_norm] using hb)
  obtain ⟨τ₃, V, hV, _, hτ₃0, hτ₃m, hτ₃c, h₃⟩ :=
    exists_mobius_chain hW₂ hT₂ hdet hc hr₃ hd₂
  have hmaps₁ : MapsTo τ₁ (Icc 0 T) (Icc 0 (τ₁ T)) := fun t ht =>
    ⟨by rw [← hτ₁0]; exact hτ₁m.monotoneOn ⟨le_rfl, hT.le⟩ ht ht.1,
      hτ₁m.monotoneOn ht ⟨hT.le, le_rfl⟩ ht.2⟩
  have hmaps₂ : MapsTo τ₂ (Icc 0 (τ₁ T)) (Icc 0 (τ₂ (τ₁ T))) := fun t ht =>
    ⟨by rw [← hτ₂0]; exact hτ₂m.monotoneOn ⟨le_rfl, hT₁.le⟩ ht ht.1,
      hτ₂m.monotoneOn ht ⟨hT₁.le, le_rfl⟩ ht.2⟩
  have himg : ∀ t ∈ Icc 0 T,
      realMobius a b c d '' fwdHull W₂ (τ₂ (τ₁ t)) = relMap U s '' fwdHull W t := by
    intro t ht
    rw [(h₂ _ (hmaps₁ ht)).2.1, (h₁ t ht).2, image_image, image_image]
    apply image_congr
    intro z hz
    have hzT := (QuantumZipper.fwdHull_mono (W := W)).1 ht.2 hz
    have hzH := (isHPHull_fwdHull hW hT.le).1 hzT
    have hzD : -z⁻¹ ∉ fwdHull U s := fun hzU => disjoint_left.mp hd
      (subset_closure hzU) (subset_closure ⟨z, hzT, rfl⟩)
    exact (hfac z hzH hzD).2.symm
  have he : EqOn (fun t => τ₃ (τ₂ (τ₁ t))) (relClock U s W) (Icc 0 T) := by
    intro t ht
    change τ₃ (τ₂ (τ₁ t)) = relClock U s W t
    rw [(h₃ _ (hmaps₂ (hmaps₁ ht))).1, himg t ht]
    rfl
  have hm : StrictMonoOn (fun t => τ₃ (τ₂ (τ₁ t))) (Icc 0 T) := by
    intro t ht u hu htu
    exact hτ₃m (hmaps₂ (hmaps₁ ht)) (hmaps₂ (hmaps₁ hu))
      (hτ₂m (hmaps₁ ht) (hmaps₁ hu) (hτ₁m ht hu htu))
  have h0 : relClock U s W 0 = 0 := by
    calc
      relClock U s W 0 = τ₃ (τ₂ (τ₁ 0)) := (he ⟨le_rfl, hT.le⟩).symm
      _ = 0 := by rw [hτ₁0, hτ₂0, hτ₃0]
  refine ⟨V, hV, h0, hm.congr he,
    (hτ₃c.comp (hτ₂c.comp hτ₁c hmaps₁) (hmaps₂.comp hmaps₁)).congr he.symm, ?_⟩
  intro t ht
  refine ⟨?_, ?_⟩
  · rw [← h0]
    exact (hm.congr he).monotoneOn ⟨le_rfl, hT.le⟩ ht ht.1
  · rw [← he ht, (h₃ _ (hmaps₂ (hmaps₁ ht))).2, himg t ht]

end InteractingSLE.Theorem14.GW2TipSystem.RootI30
