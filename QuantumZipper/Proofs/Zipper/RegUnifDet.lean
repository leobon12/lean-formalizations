import QuantumZipper.Proofs.LQG.RegularSample
import QuantumZipper.Proofs.GFF.CoordRegSwap
import QuantumZipper.Proofs.LQG.LocalRule

/-!
# REG-UNIF, deterministic part: regular witnesses uniformly in a time parameter

A regular sample (`IsRegularWith y F`) is certified by three facts about a candidate witness `F`
continuous on `Hbar × (0, ∞)`:

* (raw) the raw values of `y` at the countably many folded dyadic circles `fc(d, 2^{-k})`,
  `d ∈ Dy` (the dyadic lattice points folded into `Hbar`), equal `F(d, 2^{-k})`;
* (comm) the commutation `∫ F(u, ρ) dfc(w, r)(u) = ∫ F(v, r) dfc(w, ρ)(v)` (both sides are the
  field paired with `fc(w, r) ⊛ fc(·, ρ) = fc(w, ρ) ⊛ fc(·, r)`).

`isRegularWith_of_witness` proves this, together with raw convergence at every centre of `ℂ`
(`RawConverges y univ`, needed by the consumers `B3d.CapCocycleRegStmt`), by the deterministic
part of the proof of `CoordReg.exists_regular_witness_revMap` (clauses (i), (ii); that proof
follows Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Prop. 3.1 / arXiv:0808.1560 p. 18), isolated here.

`forall_isRegularWith_of_joint` is the time-uniform version: a family `y t`, `t ∈ [0, T]`, with a
witness `G t` jointly continuous in `(t, w, r)`, raw values continuous in `t` at every folded
dyadic circle, (raw) at a dense set of times and (comm) at a dense set of parameters, is regular
with witness `G t` at **every** `t ∈ [0, T]`. `regEq_of_raw_eq` and `forall_regEq_of_dense` give
the analogous time-uniformization of `RegEq` (for the field cocycles).

Source: the deterministic steps of Duplantier–Sheffield Prop. 3.1 as formalized in
`CoordRegRC2`; the uniformization in time by density and continuity is an **own elementary
argument** (standard: a jointly continuous modification identified on a countable dense set).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace RegUnif

open RegSample CircleFubini

/-- The dyadic lattice points folded into `Hbar`: the centres `foldH (dyadicRoundC n z)` at
which the raw values of a field are read by `avgReg`. -/
def Dy : Set ℂ := ⋃ n : ℕ, range fun z => foldH (dyadicRoundC n z)

theorem countable_Dy : Dy.Countable := by
  refine countable_iUnion fun n => ?_
  refine ((countable_range fun p : ℤ × ℤ => CircleCont.lpt n p.1 p.2).image foldH).mono ?_
  rintro _ ⟨z, rfl⟩
  exact ⟨_, ⟨(⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋), rfl⟩,
    by simp only [CircleCont.dyadicRoundC_eq_lpt]⟩

theorem Dy_subset_Hbar : Dy ⊆ Hbar := by
  rintro _ ⟨_, ⟨n, rfl⟩, z, rfl⟩
  exact foldH_mem_Hbar' _

theorem foldH_dyadicRoundC_mem_Dy (n : ℕ) (z : ℂ) : foldH (dyadicRoundC n z) ∈ Dy :=
  mem_iUnion.2 ⟨n, z, rfl⟩

/-- The raw value at a dyadic folded circle is the raw value at the folded centre. -/
theorem raw_eq_foldH (y : FieldSample) (n k : ℕ) (z : ℂ) :
    y (foldedCircle (dyadicRoundC n z) (radius k)) =
      y (foldedCircle (foldH (dyadicRoundC n z)) (radius k)) := by
  rw [CoordReg.foldedCircle_foldH]

/-! ## Regularity from a witness -/

/-- Raw values converge, at every centre of `ℂ`, to the witness at the folded centre. -/
theorem tendsto_raw_of_witness {y : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : ContinuousOn F (Hbar ×ˢ Ioi 0))
    (hraw : ∀ k : ℕ, ∀ d ∈ Dy, y (foldedCircle d (radius k)) = F (d, radius k)) (k : ℕ) (z : ℂ) :
    Tendsto (fun n => y (foldedCircle (dyadicRoundC n z) (radius k))) atTop
      (𝓝 (F (foldH z, radius k))) := by
  have hr : (0 : ℝ) < radius k := radius_pos k
  have hc : Tendsto (fun n => foldH (dyadicRoundC n z)) atTop (𝓝 (foldH z)) :=
    (continuous_foldH'.tendsto _).comp (RegClosure.tendsto_dyadicRoundC z)
  have ht : Tendsto (fun n => (foldH (dyadicRoundC n z), radius k)) atTop
      (𝓝[Hbar ×ˢ Ioi 0] (foldH z, radius k)) :=
    tendsto_nhdsWithin_iff.2 ⟨hc.prodMk_nhds tendsto_const_nhds,
      Eventually.of_forall fun n => (⟨foldH_mem_Hbar' _, hr⟩ :
        (foldH (dyadicRoundC n z), radius k) ∈ Hbar ×ˢ Ioi (0 : ℝ))⟩
  have := (hF _ (⟨foldH_mem_Hbar' z, hr⟩ : (foldH z, radius k) ∈ Hbar ×ˢ Ioi (0 : ℝ))).tendsto.comp ht
  refine this.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [raw_eq_foldH y n k z, hraw k _ (foldH_dyadicRoundC_mem_Dy n z)]

/-- **Regular sample from a witness** (deterministic): (raw) at the folded dyadic circles and
(comm) everywhere make `F` a regular witness of `y`; moreover raw values converge at every centre
of `ℂ`. -/
theorem isRegularWith_of_witness {y : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : ContinuousOn F (Hbar ×ˢ Ioi 0))
    (hraw : ∀ k : ℕ, ∀ d ∈ Dy, y (foldedCircle d (radius k)) = F (d, radius k))
    (hcomm : ∀ w ∈ Hbar, ∀ r ρ : ℝ, 0 < r → 0 < ρ →
      ∫ u, F (u, ρ) ∂foldedCircle w r = ∫ v, F (v, r) ∂foldedCircle w ρ) :
    IsRegularWith y F ∧ LocalRule.RawConverges y univ := by
  refine ⟨⟨hF, fun k z hz => ?_, ?_⟩, fun k z _ => ⟨_, tendsto_raw_of_witness hF hraw k z⟩⟩
  · have := tendsto_raw_of_witness hF hraw k z
    rwa [foldH_of_mem' hz] at this
  · set S : Set (ℂ × ℝ) := Hbar ×ˢ Ioi 0 with hS
    set Φ : (ℂ × ℝ) × ℝ → ℝ := fun p => ∫ v, F (v, p.1.2) ∂foldedCircle p.1.1 p.2 with hΦ
    have hH : ContinuousOn (fun q : ((ℂ × ℝ) × ℝ) × ℂ => F (q.2, q.1.1.2))
        ((S ×ˢ Ici 0) ×ˢ Hbar) := by
      have hm : Continuous fun q : ((ℂ × ℝ) × ℝ) × ℂ => (q.2, q.1.1.2) := by fun_prop
      exact hF.comp hm.continuousOn fun q hq => ⟨hq.2, hq.1.1.2⟩
    have hΦc : ContinuousOn Φ (S ×ˢ Ici 0) :=
      RegClosure.continuousOn_integral_fc (P := (ℂ × ℝ) × ℝ) (H := fun p v => F (v, p.1.2))
        (c := fun p => p.1.1) (r := fun p => p.2) hH
        (continuous_fst.comp continuous_fst).continuousOn continuous_snd.continuousOn
    have hΦ0 : ∀ p ∈ S, Φ (p, 0) = F p := by
      intro p hp
      simp only [hΦ]
      rw [fc_zero, integral_dirac, foldH_of_mem' hp.1]
    refine RegClosure.tluo_of_dist_le (tluo_of_continuousOn (Φ := Φ) (hΦc.mono ?_)) ?_
    · intro p hp; exact ⟨⟨hp.1.1, hp.1.2⟩, hp.2⟩
    · filter_upwards [self_mem_nhdsWithin] with ρ (hρ' : 0 < ρ) q hq
      rw [hcomm q.1 hq.1 q.2 ρ hq.2 hρ', ← hΦ0 q hq]

/-! ## Uniformity in time -/

/-- **Regular samples uniformly in time** (deterministic). -/
theorem forall_isRegularWith_of_joint {T : ℝ} {y : ℝ → FieldSample} {G : ℝ → ℂ × ℝ → ℝ}
    (hG : ContinuousOn (fun q : ℝ × (ℂ × ℝ) => G q.1 q.2) (Icc 0 T ×ˢ (Hbar ×ˢ Ioi 0)))
    (hyc : ∀ k : ℕ, ∀ d ∈ Dy,
      ContinuousOn (fun t => y t (foldedCircle d (radius k))) (Icc 0 T))
    {D : Set ℝ} (hDT : D ⊆ Icc 0 T) (hTD : Icc 0 T ⊆ closure D)
    (hraw : ∀ t ∈ D, ∀ k : ℕ, ∀ d ∈ Dy, y t (foldedCircle d (radius k)) = G t (d, radius k))
    {D4 : Set (ℝ × ((ℂ × ℝ) × ℝ))}
    (hD4 : D4 ⊆ Icc 0 T ×ˢ ((Hbar ×ˢ Ioi 0) ×ˢ Ioi 0))
    (hD4d : Icc 0 T ×ˢ ((Hbar ×ˢ Ioi 0) ×ˢ Ioi 0) ⊆ closure D4)
    (hcomm : ∀ q ∈ D4, ∫ u, G q.1 (u, q.2.2) ∂foldedCircle q.2.1.1 q.2.1.2 =
      ∫ v, G q.1 (v, q.2.1.2) ∂foldedCircle q.2.1.1 q.2.2) :
    ∀ t ∈ Icc 0 T, IsRegularWith (y t) (G t) ∧ LocalRule.RawConverges (y t) univ := by
  intro t ht
  set S4 : Set (ℝ × ((ℂ × ℝ) × ℝ)) := Icc 0 T ×ˢ ((Hbar ×ˢ Ioi 0) ×ˢ Ioi 0) with hS4
  -- (comm) everywhere, by density
  have hL : ContinuousOn (fun q : ℝ × ((ℂ × ℝ) × ℝ) =>
      ∫ u, G q.1 (u, q.2.2) ∂foldedCircle q.2.1.1 q.2.1.2) S4 := by
    have hm : Continuous fun q : (ℝ × ((ℂ × ℝ) × ℝ)) × ℂ => (q.1.1, (q.2, q.1.2.2)) := by
      fun_prop
    exact RegClosure.continuousOn_integral_fc (P := ℝ × ((ℂ × ℝ) × ℝ))
      (H := fun q u => G q.1 (u, q.2.2)) (c := fun q => q.2.1.1) (r := fun q => q.2.1.2)
      (hG.comp hm.continuousOn fun q hq => ⟨hq.1.1, hq.2, hq.1.2.2⟩)
      (by fun_prop) (by fun_prop)
  have hR : ContinuousOn (fun q : ℝ × ((ℂ × ℝ) × ℝ) =>
      ∫ v, G q.1 (v, q.2.1.2) ∂foldedCircle q.2.1.1 q.2.2) S4 := by
    have hm : Continuous fun q : (ℝ × ((ℂ × ℝ) × ℝ)) × ℂ => (q.1.1, (q.2, q.1.2.1.2)) := by
      fun_prop
    exact RegClosure.continuousOn_integral_fc (P := ℝ × ((ℂ × ℝ) × ℝ))
      (H := fun q v => G q.1 (v, q.2.1.2)) (c := fun q => q.2.1.1) (r := fun q => q.2.2)
      (hG.comp hm.continuousOn fun q hq => ⟨hq.1.1, hq.2, hq.1.2.1.2⟩)
      (by fun_prop) (by fun_prop)
  have hcomm' := Set.EqOn.of_subset_closure (fun q hq => hcomm q hq) hL hR hD4 hD4d
  -- the witness at time `t`
  have hFt : ContinuousOn (G t) (Hbar ×ˢ Ioi 0) :=
    hG.comp (continuousOn_const.prodMk continuousOn_id) fun p hp => ⟨ht, hp⟩
  refine isRegularWith_of_witness hFt (fun k d hd => ?_) fun w hw r ρ hr hρ =>
    hcomm' (show (t, ((w, r), ρ)) ∈ S4 from ⟨ht, ⟨hw, hr⟩, hρ⟩)
  have hGc : ContinuousOn (fun s => G s (d, radius k)) (Icc 0 T) :=
    hG.comp (continuousOn_id.prodMk continuousOn_const) fun s hs =>
      ⟨hs, Dy_subset_Hbar hd, radius_pos k⟩
  exact Set.EqOn.of_subset_closure (fun s hs => hraw s hs k d hd) (hyc k d hd) hGc hDT hTD ht

/-! ## `RegEq` from the raw values at the folded dyadic circles -/

/-- Equal raw values at every folded dyadic circle give `RegEq`. -/
theorem regEq_of_raw_eq {y y' : FieldSample}
    (h : ∀ k : ℕ, ∀ d ∈ Dy, y (foldedCircle d (radius k)) = y' (foldedCircle d (radius k))) :
    RegEq y y' := by
  intro k z
  unfold avgReg
  congr 1
  funext n
  rw [raw_eq_foldH y n k z, raw_eq_foldH y' n k z, h k _ (foldH_dyadicRoundC_mem_Dy n z)]

/-- Raw convergence transfers along equal raw values at the folded dyadic circles. -/
theorem rawConverges_of_raw_eq {y y' : FieldSample}
    (h : ∀ k : ℕ, ∀ d ∈ Dy, y (foldedCircle d (radius k)) = y' (foldedCircle d (radius k)))
    (hy' : LocalRule.RawConverges y' univ) : LocalRule.RawConverges y univ := by
  intro k z hz
  obtain ⟨l, hl⟩ := hy' k z hz
  refine ⟨l, hl.congr fun n => ?_⟩
  rw [raw_eq_foldH y n k z, raw_eq_foldH y' n k z, h k _ (foldH_dyadicRoundC_mem_Dy n z)]

end RegUnif
end QuantumZipper
