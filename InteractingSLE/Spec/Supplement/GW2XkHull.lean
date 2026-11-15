/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2XkFac
import InteractingSLE.Spec.Supplement.GW2ShrFill
import InteractingSLE.Spec.Supplement.SB2VrRad

/-!
# The root-`x` kernel port (D38): the retained hull through a translated launch chart

Packet PROVE-GW2-GEOM2, round 11. STAGEMEAN's root-`0` chain reads the retained counterflow hull through the launch
chart with `GW2Shr.invHull_eq_launch` (`succChart 0`). At a root `x` the launch chart's inverse is
`x + fwdMapInv J T` (`Swc.succChart_inv_eq x`), and the old hull is the explored hull translated to `x`.

* **`fwdMapInv_image_invHull_gen`**: `GW2Shr.fwdMapInv_image_invHull` with the counterflow given abstractly by a
  half-plane hull `K'` filling a trace `γ''` and the tip relation in trace form;
* `negInv_realMobius`: in inverted coordinates, physical translation by `−x` is the real Möbius map
  `M(w) = w/(xw + 1)`;
* **`chartInv_image_invHullX`**: for a chart whose inverse is `x + fwdMapInv J T` on `ℍ`, with a proper boundary
  extension and the datum's tip relation, if the counterflow's trace misses the pole `−1/x` of `M` up to `ℓ t₀`, the
  pole lies off its closed hull (`x > 0`; `GW2XkSeg` derives both from the counterflow's later visit to `x`), and the
  translated old hull misses the counterflow's inverted hull (closures), the chart's inverse carries `invHull W_k t₀`
  onto `invHull W' (ℓ t₀)`. The case `x = 0` is the root-`0` statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv fwdHull)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE.Theorem14.GW2Xk

open GW2Shr Supp8 Sec5.CrossRestart

/-! ### The hull identity for an abstract counterflow hull -/

/-- **The filled retained hull through the inverse Loewner map, for an abstract counterflow hull**
(`GW2Shr.fwdMapInv_image_invHull` with the original counterflow given by a half-plane hull `K'` filling the trace
`γ''` up to `ℓ t₀`, and the tip relation in trace form through a boundary extension `g` of `fwdMapInv J T`). -/
theorem fwdMapInv_image_invHull_gen {J : ℝ → ℝ} {T : ℝ} {Wk : ℝ≥0 → ℝ} {γk : ℝ≥0 → ℂ} {ℓ : ℝ≥0 → ℝ≥0}
    {K' : Set ℂ} {γ'' : ℝ≥0 → ℂ} {g : ℂ → ℂ}
    (hJ : Continuous J) (hJ0 : J 0 = 0) (hT : 0 ≤ T)
    (hg : ∀ p ∈ Hbar, Tendsto (fwdMapInv J T) (𝓝[H] p) (𝓝 (g p)))
    (hWk : Continuous Wk) (hWk0 : Wk 0 = 0) (hγk : IsGeneratingTrace Wk ⊤ γk)
    (hℓc : Continuous ℓ) (hℓm : Monotone ℓ) (hℓ0 : ℓ 0 = 0) {t₀ : ℝ≥0}
    (hK' : IsHPHull K') (hS' : IsFilling K' (γ'' '' Icc 0 (ℓ t₀)))
    (hrel : ∀ r : ℝ≥0, r ≤ t₀ → (γk r = 0 ↔ γ'' (ℓ r) = 0) ∧
      (γk r ≠ 0 → g (WangWu.negInv (γk r)) = WangWu.negInv (γ'' (ℓ r))))
    (hd : Disjoint (closure (fwdHull J T)) (closure ((fun w : ℂ => -w⁻¹) '' K'))) :
    fwdMapInv J T '' Supp8.Q3Rel.invHull (fun r : ℝ => Wk r.toNNReal) (t₀ : ℝ) = (fun w : ℂ => -w⁻¹) '' K' := by
  have hUk : Continuous fun r : ℝ => Wk r.toNNReal := hWk.comp continuous_real_toNNReal
  -- the inverted points of the original hull are free for the old hull
  have hfree : ∀ w ∈ K', -w⁻¹ ∈ H \ fwdHull J T := fun w hw =>
    ⟨GW2aPiece.neg_inv_mem_H (hK'.1 hw),
      fun hK => hd.ne_of_mem (subset_closure hK) (subset_closure ⟨w, hw, rfl⟩) rfl⟩
  have hrm : ∀ x, Supp8.GB6.relMap J T x = WangWu.negInv (QuantumZipper.fwdMap J T (WangWu.negInv x)) :=
    fun _ => rfl
  have hrelH : ∀ w ∈ K', Supp8.GB6.relMap J T w ∈ H :=
    fun w hw => GW2aPiece.neg_inv_mem_H (QuantumZipper.FwdHolo.mapsTo_fwdMap hJ hT (hfree w hw))
  -- (A) the relative map of the launch chart carries the original filling
  have hA : IsFilling (Supp8.GB6.relMap J T '' K') (Supp8.GB6.relMap J T '' (γ'' '' Icc 0 (ℓ t₀) ∩ H)) := by
    rcases hT.eq_or_lt with hT0 | hTpos
    · subst hT0
      have hid : ∀ w ∈ H, Supp8.GB6.relMap J 0 w = w := fun w hw => by
        have hw' := GW2aPiece.neg_inv_mem_H hw
        show -(QuantumZipper.fwdMap J 0 (-w⁻¹))⁻¹ = w
        rw [Ito.fwdMap_zero_eq_sub J hw', hJ0]
        simp only [Complex.ofReal_zero, sub_zero, inv_neg, inv_inv, neg_neg]
      rw [image_congr fun w hw => hid w (hK'.1 hw), image_congr fun w hw => hid w hw.2, image_id', image_id']
      exact isFilling_inter_H_iff.2 hS'
    · exact isFilling_relMap_image_gen hK' hK' subset_rfl hJ hJ0 hTpos (hg 0 (by simp [Hbar])) hd hS'
  -- (B) the tip relation, read on the traces
  have hrelEq : ∀ r : ℝ≥0, WangWu.negInv (γk r) ∈ H →
      fwdMapInv J T (WangWu.negInv (γk r)) = WangWu.negInv (γ'' (ℓ r)) →
      Supp8.GB6.relMap J T (γ'' (ℓ r)) = γk r := fun r hnH e => by
    rw [hrm, ← e, QuantumZipper.RS.fwdMap_fwdMapInv hJ hJ0 hT hnH, GW2Sgk.negInv_negInv]
  have hnegH : ∀ x : ℂ, WangWu.negInv x ∈ H → x ∈ H := fun x hx => by
    have := GW2aPiece.neg_inv_mem_H hx
    rwa [← WangWu.negInv, GW2Sgk.negInv_negInv] at this
  have hne0 : ∀ x : ℂ, x ∈ H → x ≠ 0 := fun x hx h => by
    rw [h] at hx
    exact (lt_irrefl _ (show (0 : ℂ).im > 0 from hx))
  -- (C) the traces agree in `ℍ`
  have hC' : γk '' Icc 0 t₀ ∩ H = Supp8.GB6.relMap J T '' (γ'' '' Icc 0 (ℓ t₀) ∩ H) ∩ H := by
    ext z
    constructor
    · rintro ⟨⟨r, hr, rfl⟩, hzH⟩
      have hnH : WangWu.negInv (γk r) ∈ H := GW2aPiece.neg_inv_mem_H hzH
      have e := (hrel r hr.2).2 (hne0 _ hzH)
      rw [bdry_eq_of_mem_H hJ hJ0 hT hnH (hg _ (QuantumZipper.H_subset_Hbar hnH))] at e
      have hfr := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hJ hJ0 hT hnH
      rw [e] at hfr
      exact ⟨⟨γ'' (ℓ r), ⟨⟨ℓ r, ⟨zero_le, hℓm hr.2⟩, rfl⟩, hnegH _ hfr.1⟩, hrelEq r hnH e⟩, hzH⟩
    · rintro ⟨⟨_, ⟨⟨u, hu, rfl⟩, hγH⟩, rfl⟩, -⟩
      have hIcc : u ∈ Icc (ℓ 0) (ℓ t₀) := by rw [hℓ0]; exact hu
      obtain ⟨r, hrI, rfl⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ t₀) hℓc.continuousOn hIcc
      have hne : γk r ≠ 0 := fun h => hne0 _ hγH ((hrel r hrI.2).1.1 h)
      have e := (hrel r hrI.2).2 hne
      have hq : WangWu.negInv (γ'' (ℓ r)) ∈ H \ fwdHull J T :=
        hfree _ (inter_H_subset_of_isFilling hS' ⟨⟨ℓ r, hu, rfl⟩, hγH⟩)
      have hHb : WangWu.negInv (γk r) ∈ Hbar :=
        GW4Traverse.negInv_mem_Hbar (GW2aPiece.trace_mem_Hbar hγk hWk hWk0 r)
      have hnH : WangWu.negInv (γk r) ∈ H := by
        by_contra hc
        exact bdry_notMem_of_real hJ hJ0 hT hHb hc (hg _ hHb) (e ▸ hq)
      rw [bdry_eq_of_mem_H hJ hJ0 hT hnH (hg _ hHb)] at e
      refine ⟨⟨r, hrI, (hrelEq r hnH e).symm⟩, ?_⟩
      rw [hrelEq r hnH e]
      exact hnegH _ hnH
  -- (D) both hulls fill the same compact trace, so they agree
  have hγkc : Continuous γk := by
    have := hγk.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  have hcpt : IsCompact (γk '' Icc 0 t₀) := isCompact_Icc.image hγkc
  have hAk : IsFilling (fwdHull (fun r : ℝ => Wk r.toNNReal) (t₀ : ℝ)) (γk '' Icc 0 t₀) :=
    hγk.2.2 t₀ ENNReal.coe_lt_top
  have hA' : IsFilling (Supp8.GB6.relMap J T '' K') (γk '' Icc 0 t₀) :=
    (Supp8.GB6.CoordB.isFilling_congr_inter_H hC'.symm).1 hA
  have e1 := (isFilling_iff_inter_H_eq_fillH hcpt.isBounded hcpt.isClosed).1 hAk
  have e2 := (isFilling_iff_inter_H_eq_fillH hcpt.isBounded hcpt.isClosed).1 hA'
  have hsub : Supp8.GB6.relMap J T '' K' ⊆ H := by
    rintro _ ⟨w, hw, rfl⟩
    exact hrelH w hw
  have hKeq : fwdHull (fun r : ℝ => Wk r.toNNReal) (t₀ : ℝ) = Supp8.GB6.relMap J T '' K' := by
    rw [← inter_eq_left.2 (isHPHull_fwdHull hUk t₀.coe_nonneg).1, e1, ← e2, inter_eq_left.2 hsub]
  -- (E) invert
  show fwdMapInv J T '' ((fun z : ℂ => -z⁻¹) '' fwdHull (fun r : ℝ => Wk r.toNNReal) (t₀ : ℝ)) =
    (fun z : ℂ => -z⁻¹) '' K'
  rw [hKeq, image_image, image_image]
  refine image_congr fun w hw => ?_
  show fwdMapInv J T (-(-(QuantumZipper.fwdMap J T (-w⁻¹))⁻¹)⁻¹) = -w⁻¹
  rw [inv_neg, inv_inv, neg_neg]
  exact QuantumZipper.RS.fwdMapInv_fwdMap hJ hJ0 hT (hfree w hw)

/-! ### Translation by `−x` in inverted coordinates -/

/-- `x w + 1 ≠ 0` off the pole: inside the disc `x‖w‖ < 1`, and on `ℍ` for `x ≥ 0`. -/
theorem mobDen_ne_zero_of_norm {x : ℝ} (hx : 0 ≤ x) {v : ℂ} (hv : x * ‖v‖ < 1) : (x : ℂ) * v + 1 ≠ 0 := by
  intro h
  have : (x : ℂ) * v = -1 := by linear_combination h
  have hn := congrArg norm this
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx, norm_neg, norm_one] at hn
  linarith

theorem mobDen_ne_zero_of_mem_H {x : ℝ} (hx : 0 ≤ x) {v : ℂ} (hv : v ∈ H) : (x : ℂ) * v + 1 ≠ 0 := by
  intro h
  rcases hx.eq_or_lt with h0 | hpos
  · subst h0; simp at h
  · have him : ((x : ℂ) * v + 1).im = x * v.im := by simp [Complex.mul_im]
    rw [h, Complex.zero_im] at him
    have hv' : 0 < v.im := hv
    have := mul_pos hpos hv'
    linarith

/-- **Physical translation by `−x` in inverted coordinates** is `M(w) = w/(xw + 1)`. -/
theorem negInv_realMobius {x : ℝ} {v : ℂ} (hv0 : v ≠ 0) :
    -(realMobius 1 0 x 1 v)⁻¹ = -v⁻¹ - x := by
  have e : realMobius 1 0 x 1 v = v / ((x : ℂ) * v + 1) := by
    show ((1 : ℝ) * v + (0 : ℝ)) / ((x : ℂ) * v + (1 : ℝ)) = v / ((x : ℂ) * v + 1)
    push_cast
    ring
  rw [e, inv_div]
  by_cases hv : (x : ℂ) * v + 1 = 0
  · have hxv : (x : ℂ) = -v⁻¹ := by field_simp; linear_combination hv
    rw [hv, zero_div, neg_zero, hxv]
    ring
  · field_simp
    ring

theorem realMobius_eq_zero_iff {x : ℝ} {v : ℂ} (hv : (x : ℂ) * v + 1 ≠ 0) : realMobius 1 0 x 1 v = 0 ↔ v = 0 := by
  show ((1 : ℝ) * v + (0 : ℝ)) / ((x : ℂ) * v + (1 : ℝ)) = 0 ↔ v = 0
  push_cast
  rw [div_eq_zero_iff]
  simp only [one_mul, add_zero]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h hv
  · intro h; exact Or.inl h

/-! ### The root-`x` hull identity -/

/-- **The retained hull through a launch chart translated to the root `x`**: for a chart whose inverse is
`x + fwdMapInv J T` on `ℍ`, with a proper boundary extension and the datum's tip relation, if the counterflow's trace
misses the pole `−1/x` of the translation `M(w) = w/(xw + 1)` up to `ℓ t₀`, the pole lies off its closed hull at `ℓ t₀`
(`x > 0`), and the explored hull translated to `x` misses the counterflow's inverted hull at `ℓ t₀` (closures), the
chart's inverse carries `invHull W_k t₀` onto `invHull W' (ℓ t₀)`. -/
theorem chartInv_image_invHullX {x : ℝ} (hx0 : 0 ≤ x) {c : Chart} {J : ℝ → ℝ} {T : ℝ}
    (hJ : Continuous J) (hJ0 : J 0 = 0) (hT : 0 ≤ T)
    (hinv : ∀ w ∈ H, c.2.1 w = (x : ℂ) + fwdMapInv J T w) (hext : GW1P.HasProperBdryExt c)
    {Wk W' : ℝ≥0 → ℝ} {γk γ' : ℝ≥0 → ℂ}
    (hWk : Continuous Wk) (hWk0 : Wk 0 = 0) (hγk : IsGeneratingTrace Wk ⊤ γk)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hγ' : IsGeneratingTrace W' ⊤ γ')
    {ℓ : ℝ≥0 → ℝ≥0} (hℓc : Continuous ℓ) (hℓm : Monotone ℓ) (hℓ0 : ℓ 0 = 0)
    (hiff : ∀ (r : ℝ≥0) (z : ℂ), (c.trans infinitySourceChart).tipAt Wk r z ↔
      infinitySourceChart.tipAt W' (ℓ r) z) {t₀ : ℝ≥0}
    (hden : ∀ u ≤ ℓ t₀, (x : ℂ) * γ' u + 1 ≠ 0)
    (hpole : 0 < x → ((mobPole x 1 : ℝ) : ℂ) ∉ closure (fwdHull (fun r : ℝ => W' r.toNNReal) (ℓ t₀ : ℝ)))
    (hd : Disjoint (closure ((fun z : ℂ => z + x) '' fwdHull J T))
      (closure (Supp8.Q3Rel.invHull (fun r : ℝ => W' r.toNNReal) (ℓ t₀ : ℝ)))) :
    c.2.1 '' Supp8.Q3Rel.invHull (fun r : ℝ => Wk r.toNNReal) (t₀ : ℝ) =
      Supp8.Q3Rel.invHull (fun r : ℝ => W' r.toNNReal) (ℓ t₀ : ℝ) := by
  obtain ⟨f, C, hf, hC⟩ := hext
  set σ := ℓ t₀ with hσ
  set M := realMobius 1 0 x 1 with hM
  have hU' : Continuous fun r : ℝ => W' r.toNNReal := hW'.comp continuous_real_toNNReal
  have hUk : Continuous fun r : ℝ => Wk r.toNNReal := hWk.comp continuous_real_toNNReal
  set K := fwdHull (fun r : ℝ => W' r.toNNReal) (σ : ℝ) with hKdef
  have hKhp : IsHPHull K := isHPHull_fwdHull hU' σ.coe_nonneg
  set A := γ' '' Icc 0 σ with hAdef
  have hγ'c : Continuous γ' := by
    have := hγ'.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  have hAc : IsCompact A := isCompact_Icc.image hγ'c
  have hKA : IsFilling K A := hγ'.2.2 σ ENNReal.coe_lt_top
  -- the boundary extension of `fwdMapInv J T`
  have hg : ∀ p ∈ Hbar, Tendsto (fwdMapInv J T) (𝓝[H] p) (𝓝 (f p - x)) := fun p hp =>
    ((hf p hp).sub_const (x : ℂ)).congr' (eventually_nhdsWithin_of_forall fun w hw => by
      rw [hinv w hw]; ring)
  -- the trace relation through the Möbius map
  have hrel0 : ∀ r, (γk r = 0 ↔ γ' (ℓ r) = 0) ∧
      (γk r ≠ 0 → f (WangWu.negInv (γk r)) = WangWu.negInv (γ' (ℓ r))) :=
    fun r => (BW1Det.tipRel_iff_traces hf hC hγk hWk hWk0 hγ' hW' hW'0 r (ℓ r)).1 (hiff r)
  have hden' : ∀ r : ℝ≥0, r ≤ t₀ → (x : ℂ) * γ' (ℓ r) + 1 ≠ 0 := fun r hr => hden _ (hℓm hr)
  have hrel : ∀ r : ℝ≥0, r ≤ t₀ → (γk r = 0 ↔ (fun u => M (γ' u)) (ℓ r) = 0) ∧
      (γk r ≠ 0 → (fun p => f p - x) (WangWu.negInv (γk r)) = WangWu.negInv ((fun u => M (γ' u)) (ℓ r))) := by
    intro r hr
    refine ⟨(hrel0 r).1.trans (realMobius_eq_zero_iff (hden' r hr)).symm, fun hne => ?_⟩
    have hv0 : γ' (ℓ r) ≠ 0 := fun h => hne ((hrel0 r).1.2 h)
    show f (WangWu.negInv (γk r)) - x = -(M (γ' (ℓ r)))⁻¹
    rw [(hrel0 r).2 hne, negInv_realMobius hv0]
    rfl
  -- the Möbius image of the counterflow hull fills the Möbius image of its trace
  have hfill : IsHPHull (M '' K) ∧ IsFilling (M '' K) ((fun u => M (γ' u)) '' Icc 0 σ) := by
    rcases hx0.eq_or_lt with h0 | hpos
    · have hid : ∀ v, M v = v := fun v => by
        show ((1 : ℝ) * v + (0 : ℝ)) / ((x : ℂ) * v + (1 : ℝ)) = v
        rw [← h0]; push_cast; ring
      rw [image_congr fun v _ => hid v, image_id', image_congr fun u _ => hid (γ' u)]
      exact ⟨hKhp, hKA⟩
    · -- a ball around the pole misses the closed hull
      have hxne : x ≠ 0 := hpos.ne'
      have hdet : (0 : ℝ) < 1 * 1 - 0 * x := by norm_num
      obtain ⟨ρ, hr, hsub⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ (hpole hpos)
      have hball : Disjoint (ball (mobPole x 1 : ℂ) ρ) K :=
        Set.disjoint_left.2 fun v hv hvK => hsub hv (subset_closure hvK)
      have hK' := isHPHull_image hdet hxne hKhp hr hball
      have h1 := isFilling_image_realMobius hdet hxne hKhp hr hball hKA
      refine ⟨hK', ?_⟩
      have hset : M '' (A ∩ H) ∩ H = M '' A ∩ H := by
        ext v
        constructor
        · rintro ⟨⟨a, ha, rfl⟩, hvH⟩
          exact ⟨⟨a, ha.1, rfl⟩, hvH⟩
        · rintro ⟨⟨a, ha, rfl⟩, hvH⟩
          refine ⟨⟨a, ⟨ha, ?_⟩, rfl⟩, hvH⟩
          obtain ⟨u, hu, rfl⟩ := ha
          have hHb := GW2aPiece.trace_mem_Hbar hγ' hW' hW'0 u
          rcases (show (0 : ℝ) ≤ (γ' u).im from hHb).eq_or_lt with hre | him
          · exfalso
            have hreal : γ' u = ((γ' u).re : ℂ) := Complex.ext (by simp) (by simp [← hre])
            have hd0 : (x : ℂ) * γ' u + 1 ≠ 0 := hden u hu.2
            have hMre : (M (γ' u)).im = 0 := by
              show (((1 : ℝ) * γ' u + (0 : ℝ)) / ((x : ℂ) * γ' u + (1 : ℝ))).im = 0
              rw [hreal]
              push_cast
              rw [show ((1 : ℂ) * ((γ' u).re : ℂ) + 0) / ((x : ℂ) * ((γ' u).re : ℂ) + 1) =
                (((γ' u).re / (x * (γ' u).re + 1) : ℝ) : ℂ) by push_cast; ring]
              exact Complex.ofReal_im _
            have : (0 : ℝ) < (M (γ' u)).im := hvH
            linarith
          · exact him
      have h2 : IsFilling (M '' K) (M '' A ∩ H) := hset ▸ isFilling_inter_H_iff.2 h1
      rw [← image_image (g := M) (f := γ')]
      exact isFilling_inter_H_iff.1 h2
  -- the translated physical hulls
  have hneg : (fun w : ℂ => -w⁻¹) '' (M '' K) =
      (fun z : ℂ => z - x) '' Supp8.Q3Rel.invHull (fun r : ℝ => W' r.toNNReal) (σ : ℝ) := by
    show (fun w : ℂ => -w⁻¹) '' (M '' K) = (fun z : ℂ => z - x) '' ((fun z : ℂ => -z⁻¹) '' K)
    rw [image_image, image_image]
    refine image_congr fun w hw => ?_
    have hw0 : w ≠ 0 := fun h => by
      have := hKhp.1 hw
      rw [h] at this
      exact lt_irrefl _ (show (0 : ℂ).im > 0 from this)
    exact negInv_realMobius hw0
  have hd' : Disjoint (closure (fwdHull J T)) (closure ((fun w : ℂ => -w⁻¹) '' (M '' K))) := by
    rw [hneg]
    have e1 : closure ((fun z : ℂ => z - x) '' Supp8.Q3Rel.invHull (fun r : ℝ => W' r.toNNReal) (σ : ℝ)) =
        (fun z : ℂ => z - x) '' closure (Supp8.Q3Rel.invHull (fun r : ℝ => W' r.toNNReal) (σ : ℝ)) :=
      ((Homeomorph.subRight (x : ℂ)).image_closure _).symm
    have e2 : closure ((fun z : ℂ => z + x) '' fwdHull J T) = (fun z : ℂ => z + x) '' closure (fwdHull J T) :=
      ((Homeomorph.addRight (x : ℂ)).image_closure _).symm
    rw [e1, Set.disjoint_left]
    rintro y hy ⟨b, hb, rfl⟩
    have hmem : b ∈ closure ((fun z : ℂ => z + x) '' fwdHull J T) := by
      rw [e2]; exact ⟨b - x, hy, by ring⟩
    exact Set.disjoint_left.1 hd hmem hb
  -- the abstract identity, then translate back
  have hgen := fwdMapInv_image_invHull_gen hJ hJ0 hT hg hWk hWk0 hγk hℓc hℓm hℓ0 hfill.1 hfill.2 hrel hd'
  rw [hneg] at hgen
  have hsubH : Supp8.Q3Rel.invHull (fun r : ℝ => Wk r.toNNReal) (t₀ : ℝ) ⊆ H := invHull_subset_H hUk t₀.coe_nonneg
  rw [image_congr fun w hw => hinv w (hsubH hw)]
  rw [show (fun w => (x : ℂ) + fwdMapInv J T w) = (fun z : ℂ => (x : ℂ) + z) ∘ fwdMapInv J T from rfl,
    image_comp, hgen, image_image]
  simp only [add_sub_cancel, image_id']

end InteractingSLE.Theorem14.GW2Xk
