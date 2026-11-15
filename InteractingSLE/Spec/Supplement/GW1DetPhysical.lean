/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1DetUnique
import InteractingSLE.Spec.Supplement.GW4LeafConn

/-!
# Retargeting through a retained chart and the connector's first visit

Packet PROVE-GW1-DET. The physical tip relation passes through every retained
chart with a proper boundary extension. The first-visit assertion follows
from an explicit boundary preimage condition for the connector; the strict
ordering of visits is reused from `GW4Leaf.firstVisit_lt_of_real_farther`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GW1Det

open GW1Path

/-- Reading a finite tip through a proper retained chart. -/
theorem tipAt_trans_iff_exists {c : Chart} {f : ℂ → ℂ} {C : ℝ}
    (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p)))
    (hC : ∀ p ∈ Hbar, ‖f p - p‖ ≤ C) {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace W ⊤ γ) (hW : Continuous W) (hW0 : W 0 = 0) {r : ℝ≥0} {z : ℂ} :
    (c.trans infinitySourceChart).tipAt W r z ↔
      ∃ p : ℂ, infinitySourceChart.tipAt W r p ∧ z = f p := by
  constructor
  · intro hz
    obtain ⟨hr, he⟩ := GW4Leaf.tipAt_trans_imp hf hC hγ hW hW0 hz
    exact ⟨-(γ r)⁻¹, (GW4Leaf.tipAt_infinitySourceChart_iff hγ hW hW0 r _).2 ⟨hr, rfl⟩, he⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨hr, rfl⟩ := (GW4Leaf.tipAt_infinitySourceChart_iff hγ hW hW0 r p).1 hp
    exact GW2aPiece.tipAt_trans_of_ne_zero hf hγ hW hW0 hr

/-- The explicit boundary extension after real recentring. -/
theorem tendsto_recenter_inv {c : Chart} {f : ℂ → ℂ}
    (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) (v : ℝ) :
    ∀ p ∈ Hbar, Tendsto (c.recenter v).2.1 (𝓝[H] p) (𝓝 (f (p + v))) := by
  intro p hp
  have hpv : p + (v : ℂ) ∈ Hbar := by
    change 0 ≤ (p + (v : ℂ)).im
    simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using (show 0 ≤ p.im from hp)
  apply (hf _ hpv).comp
  refine tendsto_nhdsWithin_iff.2 ⟨((continuous_id.add continuous_const).tendsto p).mono_left
    nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  change 0 < (z + (v : ℂ)).im
  simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using (show 0 < z.im from hz)

/-- **The retargeting relation in physical coordinates**, through any proper
retained chart. No injectivity of its boundary extension is needed. -/
theorem isRetargetOf_tipAt_trans {d : Chart} (hd : GW1P.HasProperBdryExt d)
    {U Q : ℝ≥0 → ℝ} {v : ℝ} (hQ : IsRegCf Q) (hU : Continuous U)
    (hret : IsRetargetOf U Q v) {ℓ : ℝ≥0 → ℝ≥0}
    (hℓ : ∀ r z, ((Chart.id.recenter v).trans infinitySourceChart).tipAt U r z ↔
      infinitySourceChart.tipAt Q (ℓ r) z) (r : ℝ≥0) (z : ℂ) :
    ((d.recenter v).trans infinitySourceChart).tipAt U r z ↔
      (d.trans infinitySourceChart).tipAt Q (ℓ r) z := by
  obtain ⟨f, C, hf, hC⟩ := hd
  obtain ⟨γU, hγU, -⟩ := hret.1
  obtain ⟨hQc, hQ0, γQ, hγQ, -⟩ := hQ
  have hU0 := Sec7.SideHeight.w_zero_of_isGeneratingTrace hγU (by simp)
  have hshift : ∀ p ∈ Hbar, ‖f (p + (v : ℂ)) - p‖ ≤ C + |v| := by
    intro p hp
    have hpv : p + (v : ℂ) ∈ Hbar := by
      change 0 ≤ (p + (v : ℂ)).im
      simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using (show 0 ≤ p.im from hp)
    calc
      ‖f (p + (v : ℂ)) - p‖ = ‖(f (p + (v : ℂ)) - (p + (v : ℂ))) + (v : ℂ)‖ := by
        congr 1
        ring
      _ ≤ ‖f (p + (v : ℂ)) - (p + (v : ℂ))‖ + ‖(v : ℂ)‖ := norm_add_le _ _
      _ ≤ C + |v| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact add_le_add (hC _ hpv) le_rfl
  rw [tipAt_trans_iff_exists (tendsto_recenter_inv hf v) hshift hγU hU hU0,
    tipAt_trans_iff_exists hf hC hγQ hQc hQ0]
  constructor
  · rintro ⟨p, hp, he⟩
    refine ⟨p + v, (hℓ r _).1 ?_, he⟩
    rw [tipAt_recenter_infinity_iff, add_sub_cancel_right]
    exact hp
  · rintro ⟨p, hp, he⟩
    refine ⟨p - v, ?_, ?_⟩
    · exact tipAt_recenter_infinity_iff.1 ((hℓ r p).2 hp)
    · simpa only [sub_add_cancel] using he

/-- The two existing definitions of first physical visit agree. -/
theorem firstTipTime_singleton_eq_firstVisit {Q : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace Q ⊤ γ) (hQ : Continuous Q) (hQ0 : Q 0 = 0) (p : ℂ) :
    firstTipTime infinitySourceChart Q {p} = GB11.firstVisit γ p := by
  unfold firstTipTime GB11.firstVisit
  refine iInf_congr fun t => iInf_congr_Prop ?_ fun _ => rfl
  constructor
  · rintro ⟨z, hz, htip⟩
    rw [mem_singleton_iff] at hz
    subst z
    obtain ⟨hne, he⟩ := (GW4Leaf.tipAt_infinitySourceChart_iff hγ hQ hQ0 t p).1 htip
    exact ⟨hne, he.symm⟩
  · rintro ⟨hne, he⟩
    exact ⟨p, mem_singleton p, (GW4Leaf.tipAt_infinitySourceChart_iff hγ hQ hQ0 t p).2 ⟨hne, he.symm⟩⟩

/-- **The far endpoint is the first connector contact.** The geometric premise
specifies the preimage of the new union under the retained chart's boundary
extension, outside the old union. It is the closed real interval between `0`
and `v`; real first-visit ordering then excludes every earlier contact. -/
theorem firstTipTime_connector_of_preimage {d : Chart} {f : ℂ → ℂ} {C : ℝ}
    (hf : ∀ p ∈ Hbar, Tendsto d.2.1 (𝓝[H] p) (𝓝 (f p)))
    (hC : ∀ p ∈ Hbar, ‖f p - p‖ ≤ C) {Q : ℝ≥0 → ℝ} (hQ : IsRegCf Q)
    {A B : Set ℂ} {v : ℝ} (hv : (v : ℂ) ∈ infinitySourceChart.tipSet Q ⊤)
    (havoid : ∀ r z, (d.trans infinitySourceChart).tipAt Q r z → z ∉ A)
    (hend : f (v : ℂ) ∈ B)
    (hpre : ∀ p ∈ Hbar, f p ∈ B → f p ∈ A ∨
      ∃ x : ℝ, p = (x : ℂ) ∧ ((0 ≤ x ∧ x ≤ v) ∨ (v ≤ x ∧ x ≤ 0))) :
    ∃ T : ℝ≥0, firstTipTime infinitySourceChart Q {(v : ℂ)} = T ∧
      firstTipTime (d.trans infinitySourceChart) Q B = T ∧
      (d.trans infinitySourceChart).tipAt Q T (f (v : ℂ)) := by
  obtain ⟨hQc, hQ0, γ, hγ, -⟩ := hQ
  obtain ⟨r, -, hr⟩ := hv
  obtain ⟨hγr, hrv⟩ := (GW4Leaf.tipAt_infinitySourceChart_iff hγ hQc hQ0 r v).1 hr
  have hvis : ∃ r, γ r ≠ 0 ∧ -(γ r)⁻¹ = (v : ℂ) := ⟨r, hγr, hrv.symm⟩
  have hfin : GB11.firstVisit γ (v : ℂ) < ⊤ :=
    lt_of_le_of_lt (hrv ▸ GB11.firstVisit_le hγr) ENNReal.coe_lt_top
  obtain ⟨T, hT, hγT, hvT⟩ := GW4Reg.exists_eq_firstVisit (Sec5.continuous_of_isGeneratingTrace_top hγ) hfin
  have htipT : (d.trans infinitySourceChart).tipAt Q T (f (v : ℂ)) := by
    rw [← hvT]
    exact GW2aPiece.tipAt_trans_of_ne_zero hf hγ hQc hQ0 hγT
  have hsingle := firstTipTime_singleton_eq_firstVisit hγ hQc hQ0 (v : ℂ)
  refine ⟨T, hsingle.trans hT.symm, le_antisymm (iInf₂_le T ⟨_, hend, htipT⟩) ?_, htipT⟩
  refine le_iInf₂ fun t ht => ?_
  obtain ⟨z, hzB, hzt⟩ := ht
  obtain ⟨hγt, hz⟩ := GW4Leaf.tipAt_trans_imp hf hC hγ hQc hQ0 hzt
  have hpH := GW2aPiece.neg_inv_mem_Hbar (GW2aPiece.trace_mem_Hbar hγ hQc hQ0 t)
  rcases hpre _ hpH (hz ▸ hzB) with hA | ⟨x, hx, hdir⟩
  · exact (havoid t z hzt (hz.symm ▸ hA)).elim
  have hvisitx : GB11.firstVisit γ (x : ℂ) ≤ t := hx ▸ GB11.firstVisit_le hγt
  have hle : GB11.firstVisit γ (v : ℂ) ≤ GB11.firstVisit γ (x : ℂ) := by
    by_cases hxv : x = v
    · rw [hxv]
    · apply (GW4Leaf.firstVisit_lt_of_real_farther hQc hQ0 hγ ?_ hvis).le
      rcases hdir with ⟨h0, hxv'⟩ | ⟨hvx, h0⟩
      · exact Or.inl ⟨h0, lt_of_le_of_ne hxv' hxv⟩
      · exact Or.inr ⟨lt_of_le_of_ne hvx (Ne.symm hxv), h0⟩
  rw [hT]
  exact hle.trans hvisitx

end InteractingSLE.Theorem14.GW1Det
