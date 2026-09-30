import QuantumZipper.Proofs.Section5.Prop16NodeBIoo
import QuantumZipper.Proofs.Section5.Prop16PalmMaskBasic
import QuantumZipper.Proofs.GFF.K3.MixedM7A1
import Mathlib.Topology.TietzeExtension

/-!
# Proposition 1.6, Palm node B′: the local compact sets of a window

For a window `[a', b'] ⊆ (a, b)` of the free arc, `palmWinK D a b a' b' g` is the closed
`g/2`-neighbourhood of `[a', b']` in `Hbar`, where `g ≤ min_{[a',b']} gap` (the distance to
`Hbar \ (D ∪ (a,b))`, `palmGap`). It satisfies the standing local hypotheses of K3 M5–M7
(`K3.MixedLocalHyp`, via the half-disc local balls `K3.localBall_of_halfDisc_m7a`), lies inside
`D ∪ (a,b)` (where `h0` is continuous; `exists_continuous_eqOn` extends `h0` from it by Tietze),
contains `[a', b']`, and carries every folded circle of radius `≤ g/2` centred on `[a', b']`.
These are exactly the geometric hypotheses of `palm_formula_mixed_Ioo`.

Own elementary geometry (no source needed); Tietze extension from mathlib
(`ContinuousMap.exists_restrict_eq`).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

/-- The local compact set of the window `[a', b']` at scale `g`. -/
def palmWinK (a' b' g : ℝ) : Set ℂ := cthickening (g / 2) (realSet (Icc a' b')) ∩ Hbar

theorem isCompact_realSet_Icc (a' b' : ℝ) : IsCompact (realSet (Icc a' b')) :=
  isCompact_Icc.image Complex.continuous_ofReal

theorem isCompact_palmWinK (a' b' g : ℝ) : IsCompact (palmWinK a' b' g) :=
  (isCompact_realSet_Icc a' b').cthickening.inter_right isClosed_Hbar

theorem exists_mem_of_mem_palmWinK {a' b' g : ℝ} (hg : 0 < g) {z : ℂ}
    (hz : z ∈ palmWinK a' b' g) : ∃ t ∈ Icc a' b', dist z (t : ℂ) ≤ g / 2 := by
  have h := hz.1
  rw [(isCompact_realSet_Icc a' b').cthickening_eq_biUnion_closedBall (by positivity)] at h
  simp only [mem_iUnion, mem_closedBall] at h
  obtain ⟨_, ⟨t, ht, rfl⟩, hd⟩ := h
  exact ⟨t, ht, hd⟩

theorem ofReal_mem_palmWinK {a' b' g : ℝ} {x : ℝ} (hx : x ∈ Icc a' b') :
    (x : ℂ) ∈ palmWinK a' b' g :=
  ⟨self_subset_cthickening _ ⟨x, hx, rfl⟩, show (0 : ℝ) ≤ ((x : ℂ)).im by simp⟩

/-- Small folded circles centred on the window are carried by `palmWinK`. -/
theorem foldedCircle_palmWinK_compl {a' b' g : ℝ} {x : ℝ} (hx : x ∈ Icc a' b') {r : ℝ}
    (hr : 0 ≤ r) (hrg : r ≤ g / 2) : foldedCircle (x : ℂ) r (palmWinK a' b' g)ᶜ = 0 := by
  refine measure_mono_null (compl_subset_compl.2 fun z hz => ⟨?_, hz.2⟩)
    (K3.foldedCircle_compl_eq_zero (show (0 : ℝ) ≤ ((x : ℂ)).im by simp) hr)
  exact mem_cthickening_of_dist_le z x _ _ ⟨x, hx, rfl⟩ ((mem_closedBall.1 hz.1).trans hrg)

section

variable {D : Set ℂ} {c d a b a' b' g : ℝ}

/-- Points closer than the gap stay inside `D ∪ (a,b)`. -/
theorem mem_of_dist_lt_palmGap {t : ℝ} {z : ℂ} (hz : z ∈ Hbar)
    (hd : dist z (t : ℂ) < palmGap D a b t) : z ∈ D ∪ realSet (Ioo a b) := by
  by_contra hn
  have hout : z ∈ palmOutside D a b := ⟨hz, hn⟩
  have := infDist_le_dist_of_mem (x := (t : ℂ)) hout
  rw [dist_comm] at hd
  exact absurd (lt_of_le_of_lt this hd) (lt_irrefl _)

variable (hgeom : K3.Prop16Geometry D c d) (hca : c ≤ a) (hbd : b ≤ d) (hg : 0 < g)
  (hgap : ∀ t ∈ Icc a' b', g ≤ palmGap D a b t)
include hgeom hca hbd hg hgap

theorem ball_inter_H_subset_of_gap {t : ℝ} (ht : t ∈ Icc a' b') :
    ball (t : ℂ) g ∩ H ⊆ D := by
  intro z hz
  have h := mem_of_dist_lt_palmGap (D := D) (a := a) (b := b) (t := t)
    (show (0 : ℝ) ≤ z.im from le_of_lt hz.2)
    (lt_of_lt_of_le (mem_ball.1 hz.1) (hgap t ht))
  rcases h with h | ⟨u, -, hu⟩
  · exact h
  · have : z.im = 0 := by rw [← hu]; simp
    have h2 : (0 : ℝ) < z.im := hz.2
    rw [this] at h2
    exact absurd h2 (lt_irrefl 0)

/-- **The window set satisfies the K3 local hypotheses.** -/
theorem mixedLocalHyp_palmWinK :
    K3.MixedLocalHyp D (realSet (Icc c d)) (palmWinK a' b' g) ((g - g / 2) / 4) := by
  obtain ⟨hD, -, hbdd, hDH, -, -, -⟩ := id hgeom
  refine ⟨hD, hDH, hbdd, ?_, isCompact_palmWinK a' b' g, by linarith, fun z hz => ?_⟩
  · rintro _ ⟨s, -, rfl⟩; simp
  · obtain ⟨t, ht, hdt⟩ := exists_mem_of_mem_palmWinK hg hz
    exact K3.localBall_of_halfDisc_m7a hgeom (by linarith)
      (ball_inter_H_subset_of_gap hgeom hca hbd hg hgap ht) ⟨mem_closedBall.2 hdt, hz.2⟩

omit hgeom hca hbd in
/-- The window set lies in `D ∪ (a,b)`. -/
theorem palmWinK_subset : palmWinK a' b' g ⊆ D ∪ realSet (Ioo a b) := by
  intro z hz
  obtain ⟨t, ht, hdt⟩ := exists_mem_of_mem_palmWinK hg hz
  exact mem_of_dist_lt_palmGap hz.2 (lt_of_le_of_lt hdt (by linarith [hgap t ht]))

end

/-- **Tietze extension** of `h0` from a closed set on which it is continuous. -/
theorem exists_continuous_eqOn {K : Set ℂ} (hK : IsClosed K) {h0 : ℂ → ℝ}
    (h : ContinuousOn h0 K) : ∃ m : ℂ → ℝ, Continuous m ∧ EqOn m h0 K := by
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hK ⟨K.restrict h0, h.restrict⟩
  refine ⟨G, G.continuous, fun z hz => ?_⟩
  exact congrArg (fun f : C(K, ℝ) => f ⟨z, hz⟩) hG

/-- A positive lower bound for the gap on a compact window inside `(a,b)`. -/
theorem exists_gap_lower {D : Set ℂ} {c d a b a' b' : ℝ} (hgeom : K3.Prop16Geometry D c d)
    (hca : c ≤ a) (hbd : b ≤ d) (ha : a < a') (hb : b' < b) :
    ∃ g > 0, ∀ t ∈ Icc a' b', g ≤ palmGap D a b t := by
  obtain ⟨-, -, -, hDH, -, -, hhd⟩ := hgeom
  rcases (Icc a' b').eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun t ht => by rw [he] at ht; exact ht.elim⟩
  have hcont : ContinuousOn (fun t : ℝ => palmGap D a b t) (Icc a' b') :=
    ((continuous_infDist_pt _).comp Complex.continuous_ofReal).continuousOn
  obtain ⟨t0, ht0, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont
  refine ⟨palmGap D a b t0, palmGap_pos hDH hhd hca hbd ⟨by linarith [ht0.1], by linarith [ht0.2]⟩,
    fun t ht => hmin ht⟩

end Prop16Asm

end QuantumZipper
