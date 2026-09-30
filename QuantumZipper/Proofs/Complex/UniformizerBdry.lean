/-
Copyright (c) 2026 The quantum-zipper authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: quantum-zipper (CA-H4U, EXT-CA node U4, topological part)
-/
import QuantumZipper.Proofs.Complex.UniformizerTopo
import QuantumZipper.Proofs.Complex.BasicsCayley
import QuantumZipper.Proofs.Complex.TopoSep
import QuantumZipper.Proofs.Complex.CarLengthArea
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# The θ-curve of a chord in the disk model (EXT-CA node U4, topological inputs)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 "U", node U4.  For a simple chord `η` and
`D = leftComponent η`, the bounded model of the Carathéodory theory (nodes C) uses the compact set
`thetaCurve η = cayley '' (ℝ ∪ η[0,∞)) ∪ {1}` (the unit circle together with the arc
`cayley ∘ η` on `[0,∞]`, closed up at `1`).

* `thetaCurve_eq`: `thetaCurve η = sphere 0 1 ∪ cayley '' η[0,∞)`;
* `chordArc`: a parametrization of `cayley '' η[0,∞) ∪ {1}` by `[0,1]`
  (`s ↦ cayley (η (s/(1-s)))`, `1 ↦ 1`), continuous (`continuousOn_chordArc`);
* `isCompact_thetaCurve`, `ulc_thetaCurve`: the θ-curve is compact and uniformly locally
  connected (T7 for circles and arcs, `ULC.union_of_isCompact_of_isClosed`);
* `carHyp_cayley_comp`: for a holomorphic bijection `ψ : ℍ → D`, the map `cayley ∘ ψ` satisfies
  the standing hypotheses `CarHyp` of the C nodes with `E = thetaCurve η` and `R₀ = 1`.

## Sources

Elementary plane topology and the Cayley transform; the blueprint's U4 sketch.  **Own elementary
proof** (cost rule of `AGENT_GUIDE.md`).
-/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace QuantumZipper.CA.Uniformizer

variable {η : ℝ → ℂ}

/-- The θ-curve `cayley '' (ℝ ∪ η[0,∞)) ∪ {1}` of node U4. -/
def thetaCurve (η : ℝ → ℂ) : Set ℂ := cayley '' theta η ∪ {1}

theorem add_I_ne_zero_of_mem_Hbar {z : ℂ} (hz : z ∈ Hbar) : z + Complex.I ≠ 0 :=
  add_I_ne_zero_of_im_nonneg hz

theorem chordSet_subset_Hbar (hη : IsSimpleChord η) : chordSet η ⊆ Hbar := by
  rintro _ ⟨t, ht, rfl⟩
  rcases (mem_Ici.1 ht).eq_or_lt with h0 | hpos
  · rw [← h0, hη.1]; show (0 : ℝ) ≤ (0 : ℂ).im; simp
  · exact H_subset_Hbar (hη.2.2.2.1 t hpos)

theorem theta_subset_Hbar (hη : IsSimpleChord η) : theta η ⊆ Hbar := by
  rintro z (hz | hz)
  · show (0 : ℝ) ≤ z.im; rw [show z.im = 0 from hz]
  · exact chordSet_subset_Hbar hη hz

theorem cayley_injOn_Hbar : InjOn cayley Hbar := fun z hz w hw h => by
  rw [← cayleyInv_cayley (add_I_ne_zero_of_mem_Hbar hz), h,
    cayleyInv_cayley (add_I_ne_zero_of_mem_Hbar hw)]

/-- The Cayley image of the real line, closed up at `1`, is the unit circle. -/
theorem cayley_image_real : cayley '' {z : ℂ | z.im = 0} ∪ {1} = sphere (0 : ℂ) 1 := by
  apply Subset.antisymm
  · rintro w (⟨z, hz, rfl⟩ | hw)
    · have hzI : z + Complex.I ≠ 0 := add_I_ne_zero_of_im_nonneg (le_of_eq (Eq.symm hz))
      have h := one_sub_sq_norm_cayley z hzI
      rw [show z.im = 0 from hz, mul_zero, zero_div] at h
      rw [mem_sphere_zero_iff_norm]
      have h2 : ‖cayley z‖ ^ 2 = 1 := by linarith
      have h3 : 0 ≤ ‖cayley z‖ := norm_nonneg _
      nlinarith
    · rw [mem_singleton_iff.1 hw]; simp
  · intro w hw
    by_cases h1 : w = 1
    · exact Or.inr h1
    refine Or.inl ⟨cayleyInv w, ?_, cayley_cayleyInv h1⟩
    show (cayleyInv w).im = 0
    rw [im_cayleyInv, mem_sphere_zero_iff_norm.1 hw]
    simp

theorem thetaCurve_eq : thetaCurve η = sphere (0 : ℂ) 1 ∪ cayley '' chordSet η := by
  rw [thetaCurve, theta, image_union, ← cayley_image_real]
  ext w
  simp only [mem_union]
  tauto

/-- The reparametrization `s ↦ s / (1 - s)` of `[0,1)` onto `[0,∞)`. -/
def stretch (s : ℝ) : ℝ := s / (1 - s)

theorem stretch_nonneg {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) : 0 ≤ stretch s :=
  div_nonneg h0 (by linarith)

theorem stretch_pos {s : ℝ} (h0 : 0 < s) (h1 : s < 1) : 0 < stretch s :=
  div_pos h0 (by linarith)

theorem stretch_inv {t : ℝ} (ht : 0 ≤ t) : stretch (t / (1 + t)) = t := by
  have h : (1 + t) ≠ 0 := by positivity
  unfold stretch
  rw [one_sub_div h]
  field_simp
  ring

theorem div_one_add_mem {t : ℝ} (ht : 0 ≤ t) : 0 ≤ t / (1 + t) ∧ t / (1 + t) < 1 :=
  ⟨by positivity, (div_lt_one (by positivity)).2 (by linarith)⟩

/-- The arc `cayley ∘ η` on `[0,∞]`, parametrized by `[0,1]`. -/
def chordArc (η : ℝ → ℂ) (s : ℝ) : ℂ := if s < 1 then cayley (η (stretch s)) else 1

theorem chordArc_image : chordArc η '' Icc 0 1 = cayley '' chordSet η ∪ {1} := by
  apply Subset.antisymm
  · rintro _ ⟨s, hs, rfl⟩
    unfold chordArc
    split_ifs with h
    · exact Or.inl ⟨η (stretch s), ⟨stretch s, stretch_nonneg hs.1 h, rfl⟩, rfl⟩
    · exact Or.inr rfl
  · rintro w (⟨_, ⟨t, ht, rfl⟩, rfl⟩ | hw)
    · have h := div_one_add_mem (mem_Ici.1 ht)
      refine ⟨t / (1 + t), ⟨h.1, h.2.le⟩, ?_⟩
      simp only [chordArc, if_pos h.2, stretch_inv (mem_Ici.1 ht)]
    · refine ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
      rw [mem_singleton_iff.1 hw]; simp [chordArc]

theorem continuousOn_stretch : ContinuousOn stretch (Ico 0 1) :=
  continuousOn_id.div (continuousOn_const.sub continuousOn_id) fun s hs =>
    show (1 : ℝ) - s ≠ 0 from sub_ne_zero.2 (ne_of_gt hs.2)

theorem continuousOn_cayley_chord (hη : IsSimpleChord η) :
    ContinuousOn (fun s => cayley (η (stretch s))) (Ico 0 1) :=
  continuousOn_cayley.comp (hη.2.1.comp continuousOn_stretch
    fun s hs => stretch_nonneg hs.1 hs.2) fun s hs =>
    ne_neg_I_iff.2 (add_I_ne_zero_of_mem_Hbar (chordSet_subset_Hbar hη
      ⟨stretch s, stretch_nonneg hs.1 hs.2, rfl⟩))

theorem tendsto_stretch : Tendsto stretch (𝓝[<] 1) atTop := by
  have h1 : Tendsto (fun s : ℝ => 1 - s) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun s : ℝ => 1 - s) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact show 0 < 1 - s from sub_pos.2 hs
  have h2 : Tendsto (fun s : ℝ => (1 - s)⁻¹) (𝓝[<] 1) atTop :=
    tendsto_inv_nhdsGT_zero.comp h1
  have h3 : Tendsto (fun s : ℝ => s) (𝓝[<] 1) (𝓝 1) := tendsto_nhdsWithin_of_tendsto_nhds
    (continuous_id.tendsto 1)
  exact (h3.pos_mul_atTop one_pos h2).congr fun s => by simp [stretch, div_eq_mul_inv]

theorem continuousOn_chordArc (hη : IsSimpleChord η) : ContinuousOn (chordArc η) (Icc 0 1) := by
  have heq : EqOn (chordArc η) (fun s => cayley (η (stretch s))) (Ico 0 1) :=
    fun s hs => ite_eq_left_iff.2 fun h => absurd hs.2 h
  have hIco : ContinuousOn (chordArc η) (Ico 0 1) := (continuousOn_cayley_chord hη).congr heq
  intro s hs
  rcases hs.2.lt_or_eq with h | rfl
  · refine (hIco s ⟨hs.1, h⟩).mono_of_mem_nhdsWithin ?_
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h)]
      with u hu hu' using ⟨hu.1, hu'⟩
  · rw [← Ico_insert_right zero_le_one, continuousWithinAt_insert_self]
    have hlim : Tendsto (fun s => cayley (η (stretch s))) (𝓝[<] 1) (𝓝 1) := by
      refine tendsto_cayley_cobounded.comp ?_
      rw [← tendsto_norm_atTop_iff_cobounded]
      exact hη.2.2.2.2.comp tendsto_stretch
    have hval : chordArc η 1 = 1 := by simp [chordArc]
    rw [ContinuousWithinAt, hval]
    refine (hlim.mono_left (nhdsWithin_mono _ fun u hu => hu.2)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu using (heq hu).symm

theorem thetaCurve_eq_arc : thetaCurve η = sphere (0 : ℂ) 1 ∪ chordArc η '' Icc 0 1 := by
  rw [thetaCurve_eq, chordArc_image]
  ext w
  simp only [mem_union, mem_singleton_iff]
  constructor
  · tauto
  · rintro (h | h | rfl)
    · exact Or.inl h
    · exact Or.inr h
    · left; simp

theorem isCompact_chordArc (hη : IsSimpleChord η) : IsCompact (chordArc η '' Icc 0 1) :=
  isCompact_Icc.image_of_continuousOn (continuousOn_chordArc hη)

theorem isCompact_thetaCurve (hη : IsSimpleChord η) : IsCompact (thetaCurve η) := by
  rw [thetaCurve_eq_arc]; exact (isCompact_sphere 0 1).union (isCompact_chordArc hη)

/-- **U4 (ULC).** The θ-curve is uniformly locally connected. -/
theorem ulc_thetaCurve (hη : IsSimpleChord η) : Topo.ULC (thetaCurve η) := by
  rw [thetaCurve_eq_arc]
  exact Topo.ULC.union_of_isCompact_of_isClosed (isCompact_sphere 0 1)
    (isCompact_chordArc hη).isClosed (Topo.ULC.sphere 0 1)
    (Topo.ULC.image_Icc (continuousOn_chordArc hη))

theorem ne_one_of_mem_unitBall {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : w ≠ 1 := by
  rintro rfl
  simp at hw

/-- **U4 (standing hypotheses).** For a holomorphic bijection `ψ : ℍ → leftComponent η`, the map
`cayley ∘ ψ` onto the bounded domain `cayley '' leftComponent η` satisfies the hypotheses `CarHyp`
of the Carathéodory nodes C1–C7, with `E = thetaCurve η` and `R₀ = 1`. -/
theorem carHyp_cayley_comp (hη : IsSimpleChord η) {ψ : ℂ → ℂ}
    (hψb : BijOn ψ H (leftComponent η)) (hψd : DifferentiableOn ℂ ψ H) :
    Car.CarHyp (cayley ∘ ψ) (cayley '' leftComponent η) (thetaCurve η) 1 := by
  have hDH := leftComponent_subset_H η
  have hDHb : leftComponent η ⊆ Hbar := hDH.trans H_subset_Hbar
  have hDo := isOpen_leftComponent hη
  have hopen : IsOpen (cayley '' leftComponent η) :=
    cayleyOPH.isOpen_image_of_subset_source hDo fun z hz =>
      ne_neg_I_iff.2 (add_I_ne_zero_of_mem_Hbar (hDHb hz))
  have hEc := isCompact_thetaCurve hη
  refine ⟨(differentiableOn_cayley_Hbar.mono hDHb).comp hψd hψb.mapsTo,
    ((cayley_injOn_Hbar.mono hDHb).bijOn_image).comp hψb, hopen, ?_, hEc.isClosed, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact cayley_mem_ball (hDH hz)
  · rw [hopen.frontier_eq]
    rintro w ⟨hwc, hwD⟩
    have hwB : w ∈ closedBall (0 : ℂ) 1 := closure_minimal
      (by rintro _ ⟨z, hz, rfl⟩; exact ball_subset_closedBall (cayley_mem_ball (hDH hz)))
      isClosed_closedBall hwc
    by_cases hs : ‖w‖ = 1
    · rw [thetaCurve_eq]; exact Or.inl (mem_sphere_zero_iff_norm.2 hs)
    have hwb : w ∈ ball (0 : ℂ) 1 :=
      mem_ball_zero_iff.2 (lt_of_le_of_ne (mem_closedBall_zero_iff.1 hwB) hs)
    have hw1 : w ≠ 1 := ne_one_of_mem_unitBall hwb
    have hzw : cayley (cayleyInv w) = w := cayley_cayleyInv hw1
    have hinv : LeftInvOn cayleyInv cayley (leftComponent η) :=
      fun z hz => cayleyInv_cayley (add_I_ne_zero_of_mem_Hbar (hDHb hz))
    have hzc : cayleyInv w ∈ closure (leftComponent η) := by
      have := mem_closure_image (continuousOn_cayleyInv.continuousAt (isOpen_ne.mem_nhds hw1)) hwc
      rwa [hinv.image_image] at this
    have hzD : cayleyInv w ∉ leftComponent η := fun h => hwD ⟨_, h, hzw⟩
    have hzθ : cayleyInv w ∈ theta η :=
      frontier_leftComponent_subset hη (by rw [hDo.frontier_eq]; exact ⟨hzc, hzD⟩)
    exact Or.inl ⟨_, hzθ, hzw⟩
  · rintro w hwE ⟨d, hd, rfl⟩
    rcases (hwE : cayley d ∈ cayley '' theta η ∪ {1}) with ⟨t, ht, hte⟩ | hw1
    · obtain rfl := cayley_injOn_Hbar (theta_subset_Hbar hη ht) (hDHb hd) hte
      rcases ht with ht | ht
      · have h1 := hDH hd
        simp only [H, mem_ofPred_eq] at h1
        rw [show t.im = 0 from ht] at h1
        exact lt_irrefl _ h1
      · exact (leftComponent_subset_slitH η hd).2 ht
    · have := cayley_mem_ball (hDH hd)
      rw [mem_singleton_iff.1 hw1] at this
      simp at this
  · rw [thetaCurve_eq]
    rintro w (hw | ⟨t, ht, rfl⟩)
    · exact sphere_subset_closedBall hw
    · exact cayley_mem_closedBall (chordSet_subset_Hbar hη ht)

/-! ### `E \ {q}` is connected for `q = cayley 0 = -1` and `q = 1` -/

theorem isPreconnected_setOf_im_eq_zero : IsPreconnected {z : ℂ | z.im = 0} := by
  have : {z : ℂ | z.im = 0} = range ((↑) : ℝ → ℂ) := by
    ext z
    constructor
    · intro h
      exact ⟨z.re, Complex.ext (by simp) (by simp [show z.im = 0 from h])⟩
    · rintro ⟨x, rfl⟩
      simp
  rw [this]
  exact isPreconnected_range Complex.continuous_ofReal

theorem isPreconnected_theta (hη : IsSimpleChord η) : IsPreconnected (theta η) :=
  isPreconnected_setOf_im_eq_zero.union 0 (by simp) (zero_mem_chordSet hη)
    (isPreconnected_Ici.image η hη.2.1)

theorem thetaCurve_diff_one (hη : IsSimpleChord η) : thetaCurve η \ {1} = cayley '' theta η := by
  rw [thetaCurve, union_diff_right]
  exact diff_singleton_eq_self fun ⟨t, ht, h⟩ =>
    cayley_ne_one (add_I_ne_zero_of_mem_Hbar (theta_subset_Hbar hη ht)) h

/-- **U4 (`q = ∞`).** `E \ {1}` is connected. -/
theorem isPreconnected_thetaCurve_diff_one (hη : IsSimpleChord η) :
    IsPreconnected (thetaCurve η \ {1}) := by
  rw [thetaCurve_diff_one hη]
  exact (isPreconnected_theta hη).image _ (continuousOn_cayley.mono fun z hz =>
    ne_neg_I_iff.2 (add_I_ne_zero_of_mem_Hbar (theta_subset_Hbar hη hz)))

theorem sphere_diff_one : sphere (0 : ℂ) 1 \ {1} = cayley '' {z : ℂ | z.im = 0} := by
  rw [← cayley_image_real, union_diff_right]
  exact diff_singleton_eq_self fun ⟨t, ht, h⟩ =>
    cayley_ne_one (add_I_ne_zero_of_im_nonneg (le_of_eq (Eq.symm ht))) h

theorem isPreconnected_sphere_diff_one : IsPreconnected (sphere (0 : ℂ) 1 \ {1}) := by
  rw [sphere_diff_one]
  exact isPreconnected_setOf_im_eq_zero.image _ (continuousOn_cayley.mono fun z hz =>
    ne_neg_I_iff.2 (add_I_ne_zero_of_im_nonneg (le_of_eq (Eq.symm hz))))

theorem isPreconnected_sphere_diff_neg_one : IsPreconnected (sphere (0 : ℂ) 1 \ {-1}) := by
  have : sphere (0 : ℂ) 1 \ {-1} = (fun w => -w) '' (sphere (0 : ℂ) 1 \ {1}) := by
    ext w
    constructor
    · rintro ⟨hw, hw1⟩
      refine ⟨-w, ⟨by simpa using hw, fun h => hw1 ?_⟩, neg_neg w⟩
      rw [mem_singleton_iff] at h ⊢
      rw [← neg_neg w, h]
    · rintro ⟨v, ⟨hv, hv1⟩, rfl⟩
      refine ⟨by simpa using hv, fun h => hv1 ?_⟩
      rw [mem_singleton_iff] at h ⊢
      have h' : -v = -1 := h
      rw [← neg_neg v, h', neg_neg]
  rw [this]
  exact isPreconnected_sphere_diff_one.image _ continuous_neg.continuousOn

theorem cayley_zero : cayley 0 = -1 := by simp [cayley]

theorem thetaCurve_diff_neg_one (hη : IsSimpleChord η) :
    thetaCurve η \ {-1} = (sphere (0 : ℂ) 1 \ {-1}) ∪ chordArc η '' Ioc 0 1 := by
  apply Subset.antisymm
  · rintro w ⟨hw, hw1⟩
    rw [thetaCurve_eq] at hw
    rcases hw with hw | ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩
    · exact Or.inl ⟨hw, hw1⟩
    · right
      rcases (mem_Ici.1 hτ).eq_or_lt with h0 | hpos
      · exfalso
        apply hw1
        rw [mem_singleton_iff, ← h0, hη.1, cayley_zero]
      · have h := div_one_add_mem hpos.le
        refine ⟨τ / (1 + τ), ⟨div_pos hpos (by linarith), h.2.le⟩, ?_⟩
        simp only [chordArc, if_pos h.2, stretch_inv hpos.le]
  · rintro w (⟨hw, hw1⟩ | ⟨s, hs, rfl⟩)
    · exact ⟨by rw [thetaCurve_eq]; exact Or.inl hw, hw1⟩
    · refine ⟨by rw [thetaCurve_eq_arc]; exact Or.inr ⟨s, Ioc_subset_Icc_self hs, rfl⟩, ?_⟩
      rw [mem_singleton_iff]
      unfold chordArc
      split_ifs with h
      · intro hc
        have := cayley_mem_ball (hη.2.2.2.1 _ (stretch_pos hs.1 h))
        rw [hc] at this
        simp at this
      · norm_num

/-- **U4 (`q = 0`).** `E \ {cayley 0}` is connected. -/
theorem isPreconnected_thetaCurve_diff_cayley_zero (hη : IsSimpleChord η) :
    IsPreconnected (thetaCurve η \ {cayley 0}) := by
  rw [cayley_zero, thetaCurve_diff_neg_one hη]
  exact isPreconnected_sphere_diff_neg_one.union 1 ⟨by simp, by norm_num⟩
    ⟨1, ⟨zero_lt_one, le_rfl⟩, by simp [chordArc]⟩
    (isPreconnected_Ioc.image _ ((continuousOn_chordArc hη).mono Ioc_subset_Icc_self))

end QuantumZipper.CA.Uniformizer
