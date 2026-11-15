/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootH29Arc
import InteractingSLE.Spec.Supplement.GW2RootU19Path
import InteractingSLE.Spec.Supplement.GW2RootY20Records
import InteractingSLE.Spec.Supplement.GW2RootC24Data

/-!
# Relative geometry for switched histories at every nonnegative root

Packet PROVE-T14-GW2ROOT2. The untouched connector extends the landed
zero-root geometry to the positive roots of the first low arc. The
actual image has a continuous carrier attached at a real chart value;
the source GFF law supplies the physical carrier at every switch.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootH29

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric RootC24
open Supp8.GB6 Supp8.GB6.CoordB

/-- The full mapped path, including its real visits, is a continuous
carrier of the visible relative image and starts on the real line. -/
theorem exists_relative_path_of_real_arc {w : ℝ≥0 → ℝ} {T : ℝ≥0∞}
    {α γ : ℝ≥0 → ℂ} (hα : IsGeneratingTrace w T α)
    (hw : Continuous w) (hw0 : w 0 = 0) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < T)
    {x : ℝ} (hx : 0 ≤ x) {v : ℝ≥0} (hγ : ContinuousOn γ (Icc 0 v))
    (hγ0 : γ 0 = x) (hγH : MapsTo γ (Icc 0 v) Hbar)
    (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
    (hsep : Disjoint (α '' Icc 0 s)
      ((fun z : ℂ => -z⁻¹) '' (γ '' Icc 0 v \ {0}))) :
    ∃ Γ : ℝ≥0 → ℂ, ContinuousOn Γ (Icc 0 v) ∧ (Γ 0).im = 0 ∧
      relMap (Ito.rpath w) s '' (γ '' Icc 0 v ∩ relDomain (Ito.rpath w) s) =
        Γ '' Icc 0 v ∩ H := by
  let U := Ito.rpath w
  have hU : Continuous U := hw.comp continuous_real_toNNReal
  have hU0 : U 0 = 0 := by simpa only [U, Ito.rpath, Real.toNNReal_zero] using hw0
  have hsafe := path_mem_relSafe_of_real_arc hα hw hw0 hs hx hγ hγ0 hγH harc hsep
  let Γ := fun t => relBdry U s (γ t)
  refine ⟨Γ, (continuousOn_relBdry hU hU0 s.coe_nonneg).comp hγ hsafe, ?_, ?_⟩
  · have hz := (hsafe (show (0 : ℝ≥0) ∈ Icc 0 v from ⟨le_rfl, zero_le⟩)).2
    rw [hγ0] at hz
    change (relBdry U s (γ 0)).im = 0
    rw [hγ0]
    exact im_relBdry_of_real hU hU0 s.coe_nonneg hz
  · have hi : γ '' Icc 0 v ∩ relDomain U s = γ '' Icc 0 v ∩ H := by
      apply Subset.antisymm
      · exact inter_subset_inter_right _ fun _ hz => hz.1
      · rintro z ⟨⟨t, ht, rfl⟩, hzH⟩
        exact ⟨mem_image_of_mem γ ht, (mem_relDomain_iff _ _ _).mpr
          ⟨hzH, fun hbad => (hsafe ht).2
            (subset_closure ⟨-(γ t)⁻¹, hbad, neg_inv_neg_inv _⟩)⟩⟩
    rw [hi, ← image_relBdry_inter_H hU hU0 s.coe_nonneg
      (show γ '' Icc 0 v ⊆ relSafe U s from by
        rintro _ ⟨t, ht, rfl⟩; exact hsafe ht), image_image]

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Every actual switched history at a nonnegative root has a relative
continuous carrier before trace contact, provided its root arc is untouched. -/
theorem ae_exists_relative_prefix (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (x : ℝ) (hx : 0 ≤ x) (l : List (ℝ × ℝ≥0)) :
    ∀ᵐ ω ∂c.P, (∀ u ∈ Icc 0 c.s, x * ‖c.α ω u‖ < 1) →
      Disjoint (c.α ω '' Icc 0 c.s)
        ((fun z : ℂ => -z⁻¹) ''
          (prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h x l ω \ {0})) →
      ∃ Γ : ℝ≥0 → ℂ, ContinuousOn Γ (Icc 0 1) ∧ (Γ 0).im = 0 ∧
        prefixImage c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h
          (regW c.s c.W c.ζ) c.s x l ω = Γ '' Icc 0 1 ∩ H := by
  filter_upwards [RootU19.ae_exists_path_prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀
    c.P c.h h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh x l, c.hα,
    GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ, c.hζ]
    with ω hp hα hreg hζ harc hsep
  obtain ⟨p, hp, hp0, hpH, hset⟩ := hp
  obtain ⟨_, _, hW, hW0, _⟩ := hreg
  let γ : ℝ≥0 → ℂ := fun t => p t
  have hcoe : MapsTo ((↑) : ℝ≥0 → ℝ) (Icc 0 1) (Icc 0 1) :=
    fun t ht => ⟨t.coe_nonneg, by exact_mod_cast ht.2⟩
  have hset' : prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h x l ω =
      γ '' Icc 0 1 := by
    rw [hset]
    apply Subset.antisymm
    · rintro _ ⟨t, ht, rfl⟩
      refine ⟨t.toNNReal, ⟨zero_le, Real.toNNReal_le_one.mpr ht.2⟩, ?_⟩
      change p (t.toNNReal : ℝ) = p t
      rw [Real.coe_toNNReal _ ht.1]
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨t, hcoe ht, rfl⟩
  rw [hset'] at hsep
  obtain ⟨Γ, hc, h0, himage⟩ := exists_relative_path_of_real_arc hα hW hW0
    ENNReal.coe_lt_top hx (hp.comp continuous_subtype_val.continuousOn hcoe)
    hp0 (fun t ht => hpH (hcoe ht)) harc hsep
  have he : (fun q : ℝ => regW c.s c.W c.ζ q.toNNReal ω) =
      Ito.rpath (c.W · ω) := by
    funext t
    exact regW_eq c.s hζ hW0 hW t.toNNReal
  refine ⟨Γ, hc, h0, ?_⟩
  rw [prefixImage, he, hset', ← RootY20.relDomain_eq_jointDomain]
  exact himage

/-- Boundedness, attachment and a compact filling representative now
hold at the low-arc roots as well as at zero, for every switched history. -/
theorem ae_prefixImage_geometry (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (x : ℝ) (hx : 0 ≤ x) (l : List (ℝ × ℝ≥0)) :
    ∀ᵐ ω ∂c.P, (∀ u ∈ Icc 0 c.s, x * ‖c.α ω u‖ < 1) →
      Disjoint (c.α ω '' Icc 0 c.s)
        ((fun z : ℂ => -z⁻¹) ''
          (prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h x l ω \ {0})) →
      let A := prefixImage c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h
        (regW c.s c.W c.ζ) c.s x l ω
      Bornology.IsBounded A ∧ IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0}) ∧
        ∃ K : Set ℂ, IsCompact K ∧ fillH A = fillH K := by
  filter_upwards [ae_exists_relative_prefix h13 c x hx l] with ω hω harc hsep
  obtain ⟨Γ, hc, h0, himage⟩ := hω harc hsep
  dsimp only
  rw [himage]
  obtain ⟨hK, hb, ha, hf⟩ := RootD12.upper_prefix_geometry hc h0.le
  exact ⟨hb, ha, Γ '' Icc 0 1, hK, hf⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootH29
