import InteractingSLE.Foundations.Loewner.CapacityEstimates
import QuantumZipper.Proofs.Complex.TopoJaniszewski
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Unions of hulls with disjoint closures, and the two mapping-out factorizations

Packet GEO-LOC (`planning/INFRA-GEO.md` §4), first layer. Specification Aux. lemma 8, proof,
first paragraph (`source/spec/p049-096.md`, L327–L331): if `A` and `K` are compact `ℍ`-hulls whose
closures are disjoint (the hypothesis (HD1) `dist(A, K_T) > 0`), then

* `IsHPHull.union_of_disjoint_closure`: `A ∪ K` is a compact `ℍ`-hull (connectedness of
  `ℍ \ (A ∪ K)` is Janiszewski's theorem, [Yua22, Theorem 2.4]; we apply QuantumZipper's compact
  form `QuantumZipper.CA.Topo.janiszewski` after the inversion `z ↦ 1/(z + i)`, which sends `ℍ` onto
  the disc `B(−i/2, 1/2)`);
* `IsMapOut.isHPHull_image_of_disjoint_closure`: the image `g_A(K)` of `K` under the mapping-out
  function of `A` is a compact `ℍ`-hull;
* `IsMapOut.comp_eqOn_comp_of_disjoint_closure`: the two factorizations of the mapping-out
  function of `A ∪ K` agree, `g_{g_A(K)} ∘ g_A = g_{g_K(A)} ∘ g_K` on `ℍ \ (A ∪ K)` (the first
  identity of (HD3), "uniqueness of hydrodynamic normalization");
* `HPHull.hcap_add_hcap_image_eq`: `hcap(g_A(K)) + hcap(A) = hcap(g_K(A)) + hcap(K)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace ConformalImage

/-- The inversion `z ↦ 1/(z + i)`; it maps `ℍ` onto the disc `B(−i/2, 1/2)`. -/
def inv (z : ℂ) : ℂ := (z + I)⁻¹

/-- Its inverse `p ↦ 1/p − i`. -/
def invInv (p : ℂ) : ℂ := p⁻¹ - I

theorem add_I_ne_zero_of_nonneg {z : ℂ} (hz : 0 ≤ z.im) : z + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [add_im, I_im, zero_im] at this
  linarith

theorem invInv_inv {z : ℂ} (_hz : 0 ≤ z.im) : invInv (inv z) = z := by
  simp [inv, invInv, inv_inv]

theorem inv_injOn : InjOn inv {z : ℂ | 0 ≤ z.im} := fun a ha b hb h => by
  rw [← invInv_inv ha, ← invInv_inv hb, h]

theorem continuousOn_inv : ContinuousOn inv {z : ℂ | 0 ≤ z.im} :=
  ((continuous_id.add continuous_const).continuousOn).inv₀ fun _ hz => add_I_ne_zero_of_nonneg hz

/-- `|1/(z + i) + i/2| < 1/2` iff `Im z > 0` (for `z ≠ −i`). -/
theorem inv_mem_ball_iff {z : ℂ} (hz : z + I ≠ 0) :
    inv z ∈ ball (-I / 2) (1 / 2) ↔ 0 < z.im := by
  have hn : 0 < ‖z + I‖ := norm_pos_iff.2 hz
  have key : inv z + I / 2 = (z - I) * I / (2 * (z + I)) := by
    unfold inv
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [mem_ball, dist_eq_norm, show inv z - -I / 2 = inv z + I / 2 by ring, key, norm_div,
    norm_mul, norm_I, mul_one, norm_mul, Complex.norm_two,
    div_lt_div_iff₀ (by positivity) (by norm_num), one_mul]
  have h1 : ‖z - I‖ ^ 2 = z.re ^ 2 + (z.im - 1) ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]; simp; ring
  have h2 : ‖z + I‖ ^ 2 = z.re ^ 2 + (z.im + 1) ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]; simp; ring
  constructor
  · intro h
    have h' : ‖z - I‖ ^ 2 < ‖z + I‖ ^ 2 := by
      have h0 : 0 ≤ ‖z - I‖ := norm_nonneg _
      nlinarith
    rw [h1, h2] at h'
    nlinarith
  · intro h
    have h' : ‖z - I‖ ^ 2 < ‖z + I‖ ^ 2 := by rw [h1, h2]; nlinarith
    have h0 : 0 ≤ ‖z - I‖ := norm_nonneg _
    have h0' : 0 ≤ ‖z + I‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖z - I‖ - ‖z + I‖)]

theorem inv_mem_ball {z : ℂ} (hz : z ∈ H) : inv z ∈ ball (-I / 2) (1 / 2) :=
  (inv_mem_ball_iff (add_I_ne_zero_of_nonneg (le_of_lt hz))).2 hz

theorem ne_zero_of_mem_ball {p : ℂ} (hp : p ∈ ball (-I / 2) (1 / 2)) : p ≠ 0 := by
  rintro rfl
  rw [mem_ball, dist_eq_norm, zero_sub, norm_neg, neg_div, norm_neg, norm_div, norm_I,
    Complex.norm_two] at hp
  norm_num at hp

theorem inv_invInv (p : ℂ) : inv (invInv p) = p := by
  simp [inv, invInv, inv_inv]

theorem invInv_mem_H {p : ℂ} (hp : p ∈ ball (-I / 2) (1 / 2)) : invInv p ∈ H := by
  have hp0 := ne_zero_of_mem_ball hp
  have hne : invInv p + I ≠ 0 := by simp [invInv, hp0]
  show 0 < (invInv p).im
  rw [← inv_mem_ball_iff hne, inv_invInv]
  exact hp

theorem norm_inv_le_one {z : ℂ} (hz : 0 ≤ z.im) : ‖inv z‖ ≤ 1 := by
  unfold inv
  rw [norm_inv]
  refine inv_le_one_of_one_le₀ ?_
  calc (1 : ℝ) ≤ (z + I).im := by simp; linarith
    _ ≤ |(z + I).im| := le_abs_self _
    _ ≤ ‖z + I‖ := abs_im_le_norm _

/-- The closure of the image under `inv` of a bounded set whose closure lies in `{Im ≥ 0}` is the
image of its closure. -/
theorem closure_image_inv {A : Set ℂ} (hA : Bornology.IsBounded A)
    (hAc : closure A ⊆ {z : ℂ | 0 ≤ z.im}) : closure (inv '' A) = inv '' closure A := by
  have hcpt : IsCompact (closure A) := hA.isCompact_closure
  have hcpt' : IsCompact (inv '' closure A) :=
    hcpt.image_of_continuousOn (continuousOn_inv.mono hAc)
  refine Subset.antisymm (closure_minimal (image_mono subset_closure) hcpt'.isClosed) ?_
  exact (continuousOn_inv.mono hAc).image_closure

theorem closure_subset_im_nonneg {A : Set ℂ} (hA : A ⊆ H) : closure A ⊆ {z : ℂ | 0 ≤ z.im} :=
  closure_minimal (fun z hz => show 0 ≤ z.im from le_of_lt (hA hz))
    (isClosed_le continuous_const continuous_im)

/-- A point of `ℍ \ A` is not sent by `inv` into `inv '' closure A`. -/
theorem inv_notMem_image_closure {A : Set ℂ} (hA : IsHPHull A) {z : ℂ} (hz : z ∈ H \ A) :
    inv z ∉ inv '' closure A := by
  rintro ⟨a, ha, haz⟩
  have hza : a = z :=
    inv_injOn (closure_subset_im_nonneg hA.1 ha) (show 0 ≤ z.im from le_of_lt hz.1) haz
  exact hz.2 (hA.mem_of_mem_closure hz.1 (hza ▸ ha))

theorem notMem_sphere_of_mem_ball {p : ℂ} (hp : p ∈ ball (-I / 2) (1 / 2)) :
    p ∉ sphere (-I / 2) (1 / 2) := by
  rw [mem_ball] at hp
  rw [mem_sphere]
  exact ne_of_lt hp

/-- **Janiszewski's theorem in `ℍ`** (Specification Aux. lemma 8, proof, L327; [Yua22, Theorem
2.4]): if `A`, `K` are compact `ℍ`-hulls with disjoint closures, then `ℍ \ (A ∪ K)` is connected. -/
theorem isPreconnected_H_diff_union {A K : Set ℂ} (hA : IsHPHull A) (hK : IsHPHull K)
    (hd : Disjoint (closure A) (closure K)) : IsPreconnected (H \ (A ∪ K)) := by
  set D := ball (-I / 2) (1 / 2 : ℝ) with hDdef
  set S := sphere (-I / 2) (1 / 2 : ℝ) with hSdef
  set X := inv '' closure A ∪ S with hXdef
  set Y := inv '' closure K ∪ S with hYdef
  have hclA := closure_subset_im_nonneg hA.1
  have hclK := closure_subset_im_nonneg hK.1
  have hXc : IsCompact X :=
    (hA.2.1.isCompact_closure.image_of_continuousOn (continuousOn_inv.mono hclA)).union
      (isCompact_sphere _ _)
  have hYc : IsCompact Y :=
    (hK.2.1.isCompact_closure.image_of_continuousOn (continuousOn_inv.mono hclK)).union
      (isCompact_sphere _ _)
  have hXY : X ∩ Y = S := by
    refine Subset.antisymm ?_ fun p hp => ⟨Or.inr hp, Or.inr hp⟩
    rintro p ⟨hpX, hpY⟩
    rcases hpX with ⟨a, ha, rfl⟩ | hpS
    · rcases hpY with ⟨k, hk, hka⟩ | hpS
      · have hak : k = a := inv_injOn (hclK hk) (hclA ha) hka
        exact absurd (hak ▸ hk) (Set.disjoint_left.1 hd ha)
      · exact hpS
    · exact hpS
  have hS : IsPreconnected (X ∩ Y) := by
    rw [hXY]
    exact (isConnected_sphere (by rw [rank_real_complex]; exact Nat.one_lt_ofNat) _
      (by norm_num)).isPreconnected
  have hnotXY : ∀ z ∈ H \ (A ∪ K), inv z ∉ X ∪ Y := by
    intro z hz
    have hzA : z ∈ H \ A := ⟨hz.1, fun h => hz.2 (Or.inl h)⟩
    have hzK : z ∈ H \ K := ⟨hz.1, fun h => hz.2 (Or.inr h)⟩
    have hzS := notMem_sphere_of_mem_ball (inv_mem_ball hz.1)
    rintro ((h | h) | (h | h))
    · exact inv_notMem_image_closure hA hzA h
    · exact hzS h
    · exact inv_notMem_image_closure hK hzK h
    · exact hzS h
  have hcomp : ∀ {B : Set ℂ}, IsHPHull B → ∀ {z w : ℂ}, z ∈ H \ B → w ∈ H \ B →
      inv w ∈ connectedComponentIn (inv '' closure B ∪ S)ᶜ (inv z) := by
    intro B hB z w hz hw
    have hpre : IsPreconnected (inv '' (H \ B)) :=
      hB.isConnected.isPreconnected.image _
        (continuousOn_inv.mono fun u hu => le_of_lt (show 0 < u.im from hu.1))
    refine hpre.subset_connectedComponentIn ⟨z, hz, rfl⟩ ?_ ⟨w, hw, rfl⟩
    rintro _ ⟨u, hu, rfl⟩ (h | h)
    · exact inv_notMem_image_closure hB hu h
    · exact notMem_sphere_of_mem_ball (inv_mem_ball hu.1) h
  refine isPreconnected_of_forall_pair fun x hx y hy => ?_
  have hxA : x ∈ H \ A := ⟨hx.1, fun h => hx.2 (Or.inl h)⟩
  have hxK : x ∈ H \ K := ⟨hx.1, fun h => hx.2 (Or.inr h)⟩
  have hyA : y ∈ H \ A := ⟨hy.1, fun h => hy.2 (Or.inl h)⟩
  have hyK : y ∈ H \ K := ⟨hy.1, fun h => hy.2 (Or.inr h)⟩
  have hJ := QuantumZipper.CA.Topo.janiszewski hXc hYc hS (hnotXY x hx) (hnotXY y hy)
    (hcomp hA hxA hyA) (hcomp hK hxK hyK)
  set C := connectedComponentIn (X ∪ Y)ᶜ (inv x) with hCdef
  have hxC : inv x ∈ C := mem_connectedComponentIn (hnotXY x hx)
  have hCsub : C ⊆ (X ∪ Y)ᶜ := connectedComponentIn_subset _ _
  have hCD : C ⊆ D := by
    refine isPreconnected_connectedComponentIn.subset_left_of_subset_union isOpen_ball
      (isClosed_closedBall (x := -I / 2) (ε := (1 / 2 : ℝ))).isOpen_compl ?_ ?_
      ⟨inv x, hxC, inv_mem_ball hx.1⟩
    · exact Set.disjoint_left.2 fun p hp hp' => hp' (ball_subset_closedBall hp)
    · intro p hp
      by_cases hpb : p ∈ D
      · exact Or.inl hpb
      · refine Or.inr fun hpc => ?_
        have : p ∈ S := by
          rw [hSdef, mem_sphere]
          rw [hDdef, mem_ball, not_lt] at hpb
          rw [mem_closedBall] at hpc
          exact le_antisymm hpc hpb
        exact hCsub hp (Or.inr (Or.inr this))
  refine ⟨invInv '' C, ?_, ⟨inv x, hxC, invInv_inv (le_of_lt hx.1)⟩,
    ⟨inv y, hJ, invInv_inv (le_of_lt hy.1)⟩, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    have hpD := hCD hp
    refine ⟨invInv_mem_H hpD, ?_⟩
    rintro (h | h)
    · exact hCsub hp (Or.inl (Or.inl ⟨invInv p, subset_closure h, inv_invInv p⟩))
    · exact hCsub hp (Or.inr (Or.inl ⟨invInv p, subset_closure h, inv_invInv p⟩))
  · refine isPreconnected_connectedComponentIn.image _ ?_
    refine ContinuousOn.sub (ContinuousOn.inv₀ continuousOn_id fun p hp => ?_) continuousOn_const
    exact ne_zero_of_mem_ball (hCD hp)

end ConformalImage

open ConformalImage in
/-- **The union of two compact `ℍ`-hulls with disjoint closures is a compact `ℍ`-hull**
(Specification Aux. lemma 8, proof, L327: Janiszewski's separation theorem gives connectedness of
`ℍ \ (A ∪ K)`; every complementary component is unbounded since it contains one of `A ∪ ℍᶜ`,
`K ∪ ℍᶜ`'s unbounded components). -/
theorem IsHPHull.union_of_disjoint_closure {A K : Set ℂ} (hA : IsHPHull A) (hK : IsHPHull K)
    (hd : Disjoint (closure A) (closure K)) : IsHPHull (A ∪ K) := by
  have hU : H \ (A ∪ K) = (H \ A) ∩ (H \ K) := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff, not_or]
    tauto
  have hUo : IsOpen (H \ (A ∪ K)) := by rw [hU]; exact hA.isOpen.inter hK.isOpen
  refine ⟨union_subset hA.1 hK.1, hA.2.1.union hK.2.1, hUo, ?_⟩
  obtain ⟨R, hR, hAR⟩ := hA.exists_subset_ball
  obtain ⟨R', hR', hKR⟩ := hK.exists_subset_ball
  have hne : (H \ (A ∪ K)).Nonempty := by
    refine ⟨((R + R' : ℝ) : ℂ) * I, ?_, ?_⟩
    · show 0 < (((R + R' : ℝ) : ℂ) * I).im
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      linarith
    · have hn : ‖((R + R' : ℝ) : ℂ) * I‖ = R + R' := by
        rw [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
      rintro (h | h)
      · have := hAR h
        rw [mem_ball, dist_zero_right, hn] at this
        linarith
      · have := hKR h
        rw [mem_ball, dist_zero_right, hn] at this
        linarith
  refine isSimplyConnected_of_forall_not_isBounded hUo
    ⟨hne, isPreconnected_H_diff_union hA hK hd⟩ fun a ha hbd => ?_
  by_cases haK : a ∈ K
  · have haK' : a ∉ H \ K := fun h => h.2 haK
    refine not_isBounded_connectedComponentIn_compl_of_isSimplyConnected hK.isOpen hK.2.2.2 haK'
      (hbd.subset (connectedComponentIn_mono _ ?_))
    exact compl_subset_compl.2 fun z hz => ⟨hz.1, fun h => hz.2 (Or.inr h)⟩
  · have haA : a ∉ H \ A := fun h => ha ⟨h.1, fun h' => h'.elim h.2 haK⟩
    refine not_isBounded_connectedComponentIn_compl_of_isSimplyConnected hA.isOpen hA.2.2.2 haA
      (hbd.subset (connectedComponentIn_mono _ ?_))
    exact compl_subset_compl.2 fun z hz => ⟨hz.1, fun h => hz.2 (Or.inl h)⟩


namespace ConformalImage

variable {A K : Set ℂ} {φ g : ℂ → ℂ}

theorem union_sdiff_left_of_disjoint_closure (hd : Disjoint (closure A) (closure K)) :
    (A ∪ K) \ A = K := by
  have hd' : Disjoint A K := hd.mono subset_closure subset_closure
  rw [union_sdiff_left, sdiff_eq_left]
  exact hd'.symm

theorem union_sdiff_right_of_disjoint_closure (hd : Disjoint (closure A) (closure K)) :
    (A ∪ K) \ K = A := by
  rw [union_comm]
  exact union_sdiff_left_of_disjoint_closure hd.symm

end ConformalImage

open ConformalImage

/-- The image `g_A(K)` of a hull `K` whose closure is disjoint from that of `A`, under the
mapping-out function of `A`, is a compact `ℍ`-hull (Specification Aux. lemma 8, proof, L329). -/
theorem IsMapOut.isHPHull_image_of_disjoint_closure {A K : Set ℂ} {φ : ℂ → ℂ} (hA : IsHPHull A)
    (hK : IsHPHull K) (hd : Disjoint (closure A) (closure K)) (hφ : IsMapOut A φ) :
    IsHPHull (φ '' K) := by
  have h := hφ.isHPHull_image hA (hA.union_of_disjoint_closure hK hd) subset_union_left
  rwa [union_sdiff_left_of_disjoint_closure hd] at h

/-- `g_{g_A(K)} ∘ g_A` maps out `A ∪ K`. -/
theorem IsMapOut.comp_of_disjoint_closure {A K : Set ℂ} {φ ψ : ℂ → ℂ} (hA : IsHPHull A)
    (hK : IsHPHull K) (hd : Disjoint (closure A) (closure K)) (hφ : IsMapOut A φ)
    (hψ : IsMapOut (φ '' K) ψ) : IsMapOut (A ∪ K) (ψ ∘ φ) := by
  refine hφ.comp hA (hA.union_of_disjoint_closure hK hd) subset_union_left ?_
  rwa [union_sdiff_left_of_disjoint_closure hd]

/-- **The two factorizations of the mapping-out function of `A ∪ K` agree** (Specification
(HD3), first identity, by uniqueness of the hydrodynamic normalization, L336):
`g_{g_A(K)} ∘ g_A = g_{g_K(A)} ∘ g_K` on `ℍ \ (A ∪ K)`. -/
theorem IsMapOut.comp_eqOn_comp_of_disjoint_closure {A K : Set ℂ} {φ g ψ R : ℂ → ℂ}
    (hA : IsHPHull A) (hK : IsHPHull K) (hd : Disjoint (closure A) (closure K))
    (hφ : IsMapOut A φ) (hg : IsMapOut K g) (hψ : IsMapOut (φ '' K) ψ)
    (hR : IsMapOut (g '' A) R) : EqOn (ψ ∘ φ) (R ∘ g) (H \ (A ∪ K)) := by
  have h1 := hφ.comp_of_disjoint_closure hA hK hd hψ
  have h2 := hg.comp_of_disjoint_closure hK hA hd.symm hR
  rw [union_comm] at h2
  exact h1.eqOn (hA.union_of_disjoint_closure hK hd) h2

/-- **Capacity of the union, two ways**: `hcap(A ∪ K) = hcap(g_A(K)) + hcap(A)`. -/
theorem HPHull.hcap_union_eq_add {A K : Set ℂ} {φ : ℂ → ℂ} (hA : IsHPHull A) (hK : IsHPHull K)
    (hd : Disjoint (closure A) (closure K)) (hφ : IsMapOut A φ) :
    HPHull.hcap ⟨A ∪ K, hA.union_of_disjoint_closure hK hd⟩ =
      HPHull.hcap ⟨φ '' K, hφ.isHPHull_image_of_disjoint_closure hA hK hd⟩ +
        HPHull.hcap ⟨A, hA⟩ := by
  rw [HPHull.hcap_eq_add (A := ⟨A, hA⟩) (B := ⟨A ∪ K, hA.union_of_disjoint_closure hK hd⟩)
    subset_union_left hφ]
  congr 1
  exact HPHull.hcap_congr (by simp only [union_sdiff_left_of_disjoint_closure hd])

/-- `hcap(g_A(K)) + hcap(A) = hcap(g_K(A)) + hcap(K)`. -/
theorem HPHull.hcap_add_hcap_image_eq {A K : Set ℂ} {φ g : ℂ → ℂ} (hA : IsHPHull A)
    (hK : IsHPHull K) (hd : Disjoint (closure A) (closure K)) (hφ : IsMapOut A φ)
    (hg : IsMapOut K g) :
    HPHull.hcap ⟨φ '' K, hφ.isHPHull_image_of_disjoint_closure hA hK hd⟩ + HPHull.hcap ⟨A, hA⟩ =
      HPHull.hcap ⟨g '' A, hg.isHPHull_image_of_disjoint_closure hK hA hd.symm⟩ +
        HPHull.hcap ⟨K, hK⟩ := by
  rw [← HPHull.hcap_union_eq_add hA hK hd hφ, ← HPHull.hcap_union_eq_add hK hA hd.symm hg]
  exact HPHull.hcap_congr (union_comm _ _)

end InteractingSLE
