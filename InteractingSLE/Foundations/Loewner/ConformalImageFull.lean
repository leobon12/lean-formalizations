import InteractingSLE.Foundations.Loewner.ConformalImageFullClearance

/-!
# The conformal image of a Loewner chain: Specification Aux. lemma 8, (HD1)–(HD3)

Packet PROVE-GEO-LOC2. `exists_loewner_image_of_clearance` (`ConformalImage.lean`) without the
clearance hypothesis and for a driver with arbitrary starting point `W 0`:

* the clearance follows from (HD1) (`ConformalImageFull.exists_clearance`,
  `ConformalImageFullClearance.lean`);
* a general `W 0` reduces to `W 0 = 0` by translating the driver, the obstacle `A` and its
  mapping-out function by `−W 0` (affine covariance, `IsMapOut.comp_affHomeo`,
  `HPHull.hcap_affHomeo`; QuantumZipper's `fwdMap_sub_const`).

## Main results

* `exists_loewner_image`: Aux. lemma 8, (HD1)–(HD3), with (HD1) in the form
  `closure A ∩ (closure K_T ∪ {W_0}) = ∅`, i.e. positive distance of `A` from the closed filled
  hull of `γ([0, T])`, which contains the seed `γ(0) = W_0`.
* `exists_loewner_image_of_pos`: for `T > 0` the seed is in `closure K_T`, so (HD1) is
  `closure A ∩ closure K_T = ∅`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace ConformalImageFull

/-- Translating the driver by `c` translates the hulls by `c`. -/
theorem fwdHull_add_const (U : ℝ → ℝ) (c t : ℝ) :
    QuantumZipper.fwdHull (fun s => U s + c) t =
      (fun z : ℂ => z + c) '' QuantumZipper.fwdHull U t := by
  ext w
  constructor
  · intro hw
    have key := QuantumZipper.ASep.GC.mem_fwdHull_sub_const (fun s => U s + c) c w t
    simp only [add_sub_cancel_right] at key
    exact ⟨w - c, key.2 hw, by ring⟩
  · rintro ⟨z, hz, rfl⟩
    have key := QuantumZipper.ASep.GC.mem_fwdHull_sub_const (fun s => U s + c) c (z + c) t
    simp only [add_sub_cancel_right] at key
    exact key.1 hz

/-- Translating the driver by `c` conjugates the centered maps by the translation. -/
theorem fwdMap_add_const (U : ℝ → ℝ) (c σ : ℝ) (w : ℂ) :
    QuantumZipper.fwdMap (fun s => U s + c) σ w = QuantumZipper.fwdMap U σ (w - c) := by
  have key := QuantumZipper.ASep.GC.fwdMap_sub_const (fun s => U s + c) c w σ
  simp only [add_sub_cancel_right] at key
  exact key.symm

theorem affHomeo_one_apply (c : ℝ) (z : ℂ) : affHomeo 1 one_pos c z = z + c := by
  simp [coe_affHomeo]

theorem affHomeo_one_symm_apply (c : ℝ) (w : ℂ) : (affHomeo 1 one_pos c).symm w = w - c := by
  rw [affHomeo_symm_apply]
  simp
/-- Aux. lemma 8 for the driver `V + c` with `V 0 = 0` (the translation step). -/
theorem exists_loewner_image_add_const {V : ℝ → ℝ} (hV : Continuous V) (hV0 : V 0 = 0) (c : ℝ)
    {T : ℝ} (hT : 0 ≤ T) {A : Set ℂ} (hA : IsHPHull A) {φ : ℂ → ℂ} (hφ : IsMapOut A φ)
    (hd : Disjoint (closure A)
      (insert (c : ℂ) (closure (QuantumZipper.fwdHull (fun s => V s + c) T)))) :
    ∃ (a : ℝ → ℝ) (W' : ℝ → ℝ), Continuous W' ∧ a 0 = 0 ∧ StrictMonoOn a (Icc 0 T) ∧
      ContinuousOn a (Icc 0 T) ∧ ∀ t ∈ Icc (0 : ℝ) T,
        (∃ hK : IsHPHull (φ '' QuantumZipper.fwdHull (fun s => V s + c) t),
          a t = HPHull.hcap ⟨_, hK⟩ / 2) ∧
        QuantumZipper.fwdHull W' (a t) = φ '' QuantumZipper.fwdHull (fun s => V s + c) t ∧
        ∀ R : ℂ → ℂ, IsMapOut ((fun z => QuantumZipper.fwdMap (fun s => V s + c) t z +
            (((V t + c : ℝ)) : ℂ)) '' A) R →
          (∀ z ∈ H \ (A ∪ QuantumZipper.fwdHull (fun s => V s + c) t),
            QuantumZipper.fwdMap W' (a t) (φ z) + W' (a t) =
              R (QuantumZipper.fwdMap (fun s => V s + c) t z + (((V t + c : ℝ)) : ℂ))) ∧
          Tendsto R (𝓝[H] (((V t + c : ℝ)) : ℂ)) (𝓝 (W' (a t) : ℂ)) := by
  set U : ℝ → ℝ := fun s => V s + c with hU
  set e := affHomeo 1 one_pos (-c) with he
  set ep := affHomeo 1 one_pos c with hep
  have he_apply : ∀ z, e z = z - c := fun z => by
    rw [he, affHomeo_one_apply]; push_cast; ring
  have he_symm : ∀ w, e.symm w = w + c := fun w => by
    rw [he, affHomeo_one_symm_apply]; push_cast; ring
  have hep_apply : ∀ z, ep z = z + c := fun z => affHomeo_one_apply c z
  have hKU : ∀ t, QuantumZipper.fwdHull U t = (fun z : ℂ => z + c) '' QuantumZipper.fwdHull V t :=
    fun t => fwdHull_add_const V c t
  have hKV : ∀ t, QuantumZipper.fwdHull V t = e '' QuantumZipper.fwdHull U t := fun t => by
    rw [hKU, image_image]
    conv_lhs => rw [← image_id (QuantumZipper.fwdHull V t)]
    refine image_congr fun z _ => ?_
    simp [he_apply]
  set A' := e '' A with hA'
  set φ' : ℂ → ℂ := fun w => e (φ (e.symm w)) with hφ'
  have hA'h : IsHPHull A' := hA.image_affHomeo one_pos
  have hφ'm : IsMapOut A' φ' := hφ.comp_affHomeo one_pos
  have hd' : Disjoint (closure A') (closure (QuantumZipper.fwdHull V T)) := by
    rw [hKV, hA', ← e.image_closure, ← e.image_closure, disjoint_image_iff e.injective]
    exact hd.mono_right (subset_insert _ _)
  have h0' : (0 : ℂ) ∉ closure A' := by
    rw [hA', ← e.image_closure]
    rintro ⟨z, hz, hz0⟩
    rw [he_apply, sub_eq_zero] at hz0
    exact Set.disjoint_left.1 hd hz (hz0 ▸ mem_insert _ _)
  obtain ⟨ρ, hρ, hclr⟩ := exists_clearance hV hV0 hT hA'h hd' h0'
  obtain ⟨a, W'', hW''c, ha0, hamono, hacont, hmain⟩ :=
    exists_loewner_image_of_clearance hV hV0 hT hA'h hφ'm hd' hρ hclr
  refine ⟨a, fun σ => W'' σ + c, hW''c.add continuous_const, ha0, hamono, hacont,
    fun t ht => ?_⟩
  obtain ⟨⟨hK', hat⟩, hhull, hR⟩ := hmain t ht
  have himg : φ '' QuantumZipper.fwdHull U t = ep '' (φ' '' QuantumZipper.fwdHull V t) := by
    rw [hKV, image_image, image_image]
    refine image_congr fun z _ => ?_
    simp only [hφ', hep_apply, he_apply, he_symm, sub_add_cancel]
  refine ⟨⟨himg ▸ hK'.image_affHomeo one_pos, ?_⟩, ?_, fun R hRU => ?_⟩
  · rw [hat]
    have h1 := HPHull.hcap_affHomeo (x := c) ⟨_, hK'⟩ one_pos
    rw [one_pow, one_mul] at h1
    rw [← h1]
    congr 1
    exact HPHull.hcap_congr himg.symm
  · rw [fwdHull_add_const, hhull, himg]
    exact image_congr fun z _ => (hep_apply z).symm
  · -- the obstacle `E_t` and its mapping-out function, translated
    set R' : ℂ → ℂ := fun w => e (R (e.symm w)) with hR'
    have hEV : (fun z => QuantumZipper.fwdMap V t z + V t) '' A' =
        e '' ((fun z => QuantumZipper.fwdMap U t z + (((V t + c : ℝ)) : ℂ)) '' A) := by
      rw [hA', image_image, image_image]
      refine image_congr fun z _ => ?_
      simp only [he_apply, hU, fwdMap_add_const]
      push_cast
      ring
    have hR'm : IsMapOut ((fun z => QuantumZipper.fwdMap V t z + V t) '' A') R' := by
      rw [hEV]
      exact hRU.comp_affHomeo one_pos
    obtain ⟨hR1, hR2⟩ := hR R' hR'm
    refine ⟨fun z hz => ?_, ?_⟩
    · have hz' : e z ∈ H \ (A' ∪ QuantumZipper.fwdHull V t) := by
        refine ⟨(affHomeo_mem_H_iff one_pos).2 hz.1, ?_⟩
        rintro (⟨w, hw, hwz⟩ | hK)
        · exact hz.2 (Or.inl (e.injective hwz ▸ hw))
        · rw [hKV] at hK
          obtain ⟨w, hw, hwz⟩ := hK
          exact hz.2 (Or.inr (e.injective hwz ▸ hw))
      have h1 := hR1 (e z) hz'
      simp only [hφ', hR', he_symm, he_apply, sub_add_cancel] at h1
      rw [fwdMap_add_const, fwdMap_add_const]
      push_cast
      simp only [← add_assoc]
      linear_combination h1
    · show Tendsto R (𝓝[H] (((V t + c : ℝ)) : ℂ)) (𝓝 (((W'' (a t) + c : ℝ)) : ℂ))
      have hcont : Tendsto e (𝓝[H] (((V t + c : ℝ)) : ℂ)) (𝓝[H] ((V t : ℝ) : ℂ)) := by
        have := (e.continuous.continuousWithinAt (s := H)
          (x := (((V t + c : ℝ)) : ℂ))).tendsto_nhdsWithin (t := H)
          fun z hz => (affHomeo_mem_H_iff one_pos).2 hz
        have he' : e (((V t + c : ℝ)) : ℂ) = ((V t : ℝ) : ℂ) := by
          rw [he_apply]; push_cast; ring
        rwa [he'] at this
      have h2 := ((hR2.comp hcont).add_const (c : ℂ))
      rw [ofReal_add (W'' (a t))]
      refine h2.congr fun w => ?_
      simp only [Function.comp_apply, hR', he_symm, he_apply, sub_add_cancel]

/-- **Specification Aux. lemma 8** ((HD1)–(HD3); [Law05] §4.6.1): the conformal image of a
Loewner chain under the mapping-out function of a fixed obstacle.

Let `W` be continuous, `K_t = fwdHull W t` the hulls of the chordal Loewner chain driven by `W`,
`g_t = f_t + W_t` its mapping-out functions, `A` a compact `ℍ`-hull with mapping-out function
`φ = g_A`, and assume (HD1): `closure A` is disjoint from `closure K_T ∪ {W_0}` (the closed filled
hull of `γ([0, T])`, which contains the seed `γ(0) = W_0`). Then there are a capacity clock `a`
(continuous, strictly increasing on `[0, T]`, `a 0 = 0`) and a continuous driver `W'` such that
for every `t ∈ [0, T]`:
* (HD2) `φ(K_t)` is a compact `ℍ`-hull and `a t = ½ hcap(φ(K_t))`;
* `φ(K_t)` is the hull at time `a t` of the Loewner chain driven by `W'`;
* (HD3) for every mapping-out function `R` of `E_t = g_t(A)`: `g̃_{a(t)} ∘ φ = R ∘ g_t` on
  `ℍ \ (A ∪ K_t)` (with `g̃_σ = f̃_σ + W'_σ`), and `W'(a t) = R(W_t)`, the boundary limit of `R`
  at `W_t`. -/
theorem exists_loewner_image {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
    {A : Set ℂ} (hA : IsHPHull A) {φ : ℂ → ℂ} (hφ : IsMapOut A φ)
    (hd : Disjoint (closure A) (insert (W 0 : ℂ) (closure (QuantumZipper.fwdHull W T)))) :
    ∃ (a : ℝ → ℝ) (W' : ℝ → ℝ), Continuous W' ∧ a 0 = 0 ∧ StrictMonoOn a (Icc 0 T) ∧
      ContinuousOn a (Icc 0 T) ∧ ∀ t ∈ Icc (0 : ℝ) T,
        (∃ hK : IsHPHull (φ '' QuantumZipper.fwdHull W t), a t = HPHull.hcap ⟨_, hK⟩ / 2) ∧
        QuantumZipper.fwdHull W' (a t) = φ '' QuantumZipper.fwdHull W t ∧
        ∀ R : ℂ → ℂ, IsMapOut ((fun z => QuantumZipper.fwdMap W t z + W t) '' A) R →
          (∀ z ∈ H \ (A ∪ QuantumZipper.fwdHull W t),
            QuantumZipper.fwdMap W' (a t) (φ z) + W' (a t) =
              R (QuantumZipper.fwdMap W t z + W t)) ∧
          Tendsto R (𝓝[H] (W t : ℂ)) (𝓝 (W' (a t) : ℂ)) := by
  have hfun : (fun s => (W s - W 0) + W 0) = W := funext fun s => sub_add_cancel _ _
  have h := exists_loewner_image_add_const (V := fun s => W s - W 0) (hW.sub continuous_const)
    (sub_self _) (W 0) hT hA hφ (by rw [hfun]; exact hd)
  simp only [sub_add_cancel] at h
  exact h

/-- **Specification Aux. lemma 8** for `T > 0`: the seed `W_0` lies in `closure K_T`, so (HD1)
is `closure A ∩ closure K_T = ∅`. -/
theorem exists_loewner_image_of_pos {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 < T)
    {A : Set ℂ} (hA : IsHPHull A) {φ : ℂ → ℂ} (hφ : IsMapOut A φ)
    (hd : Disjoint (closure A) (closure (QuantumZipper.fwdHull W T))) :
    ∃ (a : ℝ → ℝ) (W' : ℝ → ℝ), Continuous W' ∧ a 0 = 0 ∧ StrictMonoOn a (Icc 0 T) ∧
      ContinuousOn a (Icc 0 T) ∧ ∀ t ∈ Icc (0 : ℝ) T,
        (∃ hK : IsHPHull (φ '' QuantumZipper.fwdHull W t), a t = HPHull.hcap ⟨_, hK⟩ / 2) ∧
        QuantumZipper.fwdHull W' (a t) = φ '' QuantumZipper.fwdHull W t ∧
        ∀ R : ℂ → ℂ, IsMapOut ((fun z => QuantumZipper.fwdMap W t z + W t) '' A) R →
          (∀ z ∈ H \ (A ∪ QuantumZipper.fwdHull W t),
            QuantumZipper.fwdMap W' (a t) (φ z) + W' (a t) =
              R (QuantumZipper.fwdMap W t z + W t)) ∧
          Tendsto R (𝓝[H] (W t : ℂ)) (𝓝 (W' (a t) : ℂ)) := by
  refine exists_loewner_image hW hT.le hA hφ ?_
  rw [Set.disjoint_insert_right]
  refine ⟨fun h => ?_, hd⟩
  have h0 := zero_mem_closure_fwdHull (W := fun s => W s - W 0) (hW.sub continuous_const)
    (sub_self _) hT
  have hK : QuantumZipper.fwdHull W T = (fun z : ℂ => z + W 0) ''
      QuantumZipper.fwdHull (fun s => W s - W 0) T := by
    rw [← fwdHull_add_const]
    simp only [sub_add_cancel]
  have hmem : (W 0 : ℂ) ∈ closure (QuantumZipper.fwdHull W T) := by
    rw [hK]
    exact image_closure_subset_closure_image (f := fun z : ℂ => z + W 0) (by fun_prop)
      ⟨0, h0, zero_add _⟩
  exact Set.disjoint_left.1 hd h hmem

end ConformalImageFull

end InteractingSLE
