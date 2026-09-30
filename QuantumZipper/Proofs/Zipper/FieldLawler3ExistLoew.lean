import QuantumZipper.Proofs.Zipper.FieldLawler3ExistCar
import QuantumZipper.Proofs.Zipper.FieldLawler2Circ

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL3-EXIST: harmonic measures on the slit half-disc minus circular arcs

Task FL3-EXIST (Track A, towards `FieldLawler.FLImageSumBoundStmt`). For a curve `γ` on `[0, t]`
with `γ 0 = 0` (the Loewner trace, `K = γ((0, t])`), the region
`U = ((ℍ \ K) ∩ B(0, R)) \ ⋃_{i ∈ I} C_ε(αᵢ, βᵢ)` (finitely many open arcs of `C_ε` whose endpoints
lie on `γ([0, t]) ∪ {Im ≤ 0}`) carries a harmonic measure of every bounded `A` disjoint from `U`,
provided `U` has finitely many connected components (`flExist_loewner`).

The frame is `E = γ([0,t]) ∪ [-R, R] ∪ C_R ∪ ⋃ closed arcs`, a finite union of compact ULC sets
(`Topo.ULC.union_of_isCompact_of_isClosed`, `Topo.ULC.image_Icc`, `Topo.ULC.sphere`), and every point
off `U` lies in an unbounded connected subset of `Uᶜ` (`γ([0,t]) ∪ {Im ≤ 0}`, plus a closed arc, or
a radial ray). Then `flExist_of_frame` applies. Source: as in `FieldLawler3ExistCar.lean`
(Garnett–Marshall Ch. I §1 (1.6); Pommerenke Thm 2.1); the topological bookkeeping is our own
elementary argument.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar
open QuantumZipper.CA

/-- ULC of the image of any compact interval. -/
lemma flExist_ulc_image_Icc {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) : Topo.ULC (γ '' Icc a b) := by
  have hmaps : MapsTo (fun s : ℝ => a + (b - a) * s) (Icc 0 1) (Icc a b) := by
    intro s hs
    constructor <;> nlinarith [hs.1, hs.2]
  have himg : (fun s : ℝ => γ (a + (b - a) * s)) '' Icc 0 1 = γ '' Icc a b := by
    rw [show (fun s : ℝ => γ (a + (b - a) * s)) = γ ∘ (fun s : ℝ => a + (b - a) * s) from rfl,
      image_comp]
    congr 1
    refine Subset.antisymm (image_subset_iff.2 hmaps) fun u hu => ?_
    rcases hab.eq_or_lt with h | h
    · subst h
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by
        have := hu.1; have := hu.2; simp; linarith⟩
    · refine ⟨(u - a) / (b - a), ⟨div_nonneg (by linarith [hu.1]) (by linarith),
        (div_le_one (by linarith)).2 (by linarith [hu.2])⟩, ?_⟩
      field_simp
      ring
  rw [← himg]
  exact Topo.ULC.image_Icc (hγ.comp (by fun_prop) hmaps)

/-- The closed arc `{ε e^{iθ} : θ ∈ [α, β]}`. -/
def flClArc (ε α β : ℝ) : Set ℂ := (fun θ : ℝ => (ε : ℂ) * exp (θ * I)) '' Icc α β

lemma flClArc_cont (ε : ℝ) : Continuous fun θ : ℝ => (ε : ℂ) * exp (θ * I) := by fun_prop

lemma flCircArc_sub_clArc (ε α β : ℝ) : flCircArc ε α β ⊆ flClArc ε α β :=
  image_mono Ioo_subset_Icc_self

/-- A radial ray `{s a : s ≥ 1}` (`a ≠ 0`) is not bounded. -/
lemma flExist_ray_unbdd {a : ℂ} (ha : a ≠ 0) :
    ¬ Bornology.IsBounded ((fun s : ℝ => (s : ℂ) * a) '' Ici 1) := by
  intro hb
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hb
  have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha
  set s : ℝ := max 1 ((|M| + 1) / ‖a‖)
  have h1 := hM _ ⟨s, show (1 : ℝ) ≤ s from le_max_left _ _, rfl⟩
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
  have h2 : (|M| + 1) / ‖a‖ * ‖a‖ ≤ s * ‖a‖ :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hapos.le
  rw [div_mul_cancel₀ _ hapos.ne'] at h2
  linarith [le_abs_self M]

lemma flExist_ray_preconn (a : ℂ) : IsPreconnected ((fun s : ℝ => (s : ℂ) * a) '' Ici 1) :=
  isPreconnected_Ici.image _ (by fun_prop)

/-- The lower closed half-plane is preconnected and unbounded. -/
lemma flExist_lower_preconn : IsPreconnected {z : ℂ | z.im ≤ 0} :=
  (convex_halfSpace_le (𝕜 := ℝ) ⟨fun x y => add_im x y, fun c x => by simp⟩ 0).isPreconnected

lemma flExist_lower_unbdd : ¬ Bornology.IsBounded {z : ℂ | z.im ≤ 0} := fun hb =>
  flExist_ray_unbdd (a := -I) (by simp) (hb.subset (by
    rintro _ ⟨s, hs, rfl⟩
    simp only [mem_ofPred_eq, mul_im, ofReal_re, neg_im, I_im, ofReal_im, neg_re, I_re]
    simp only [mem_Ici] at hs
    nlinarith))

/-- Finite unions of compact ULC sets are compact and ULC. -/
lemma flExist_ulc_biUnion {ι : Type*} (s : Finset ι) (f : ι → Set ℂ)
    (hc : ∀ i ∈ s, IsCompact (f i)) (hu : ∀ i ∈ s, Topo.ULC (f i)) :
    IsCompact (⋃ i ∈ s, f i) ∧ Topo.ULC (⋃ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty]
    exact ⟨isCompact_empty, fun _ _ => ⟨1, one_pos, fun a ha => absurd ha (notMem_empty a)⟩⟩
  | insert j s hj ih =>
    rw [Finset.set_biUnion_insert]
    obtain ⟨ihc, ihu⟩ := ih (fun i hi => hc i (Finset.mem_insert_of_mem hi))
      (fun i hi => hu i (Finset.mem_insert_of_mem hi))
    exact ⟨(hc j (Finset.mem_insert_self j s)).union ihc,
      Topo.ULC.union_of_isCompact_of_isClosed (hc j (Finset.mem_insert_self j s)) ihc.isClosed
        (hu j (Finset.mem_insert_self j s)) ihu⟩

/-- **Harmonic measure on the slit half-disc minus finitely many circular arcs.** For a curve
`γ` continuous on `[0, t]` with `γ 0 = 0`, `K = γ((0, t])`, and finitely many open arcs
`C_ε(αᵢ, βᵢ)` (`i ∈ I₀`) whose endpoints lie on `γ([0, t]) ∪ {Im ≤ 0}`, the open set
`U = ((ℍ \ K) ∩ B(0, R)) \ ⋃ᵢ C_ε(αᵢ, βᵢ)` carries a harmonic measure of every bounded `A`
disjoint from it, provided `U` has finitely many connected components. -/
theorem flExist_loewner {γ : ℝ → ℂ} {t R ε : ℝ} (ht : 0 ≤ t) (hR : 0 < R)
    (hγc : ContinuousOn γ (Icc 0 t)) (hγ0 : γ 0 = 0)
    {ι : Type*} (I₀ : Finset ι) {α β : ι → ℝ} (hαβ : ∀ i ∈ I₀, α i ≤ β i)
    (hend : ∀ i ∈ I₀, (ε : ℂ) * exp (α i * I) ∈ γ '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0} ∧
      (ε : ℂ) * exp (β i * I) ∈ γ '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0})
    {A : Set ℂ} (hA : Bornology.IsBounded A)
    (hAU : Disjoint A (((H \ γ '' Ioc 0 t) ∩ ball 0 R) \ ⋃ i ∈ I₀, flCircArc ε (α i) (β i)))
    (hfin : (connectedComponentIn (((H \ γ '' Ioc 0 t) ∩ ball 0 R) \
        ⋃ i ∈ I₀, flCircArc ε (α i) (β i)) ''
      (((H \ γ '' Ioc 0 t) ∩ ball 0 R) \ ⋃ i ∈ I₀, flCircArc ε (α i) (β i))).Finite) :
    ∃ g : ℂ → ℝ, IsHarmMeas (((H \ γ '' Ioc 0 t) ∩ ball 0 R) \
      ⋃ i ∈ I₀, flCircArc ε (α i) (β i)) A g := by
  set U := ((H \ γ '' Ioc 0 t) ∩ ball 0 R) \ ⋃ i ∈ I₀, flCircArc ε (α i) (β i) with hUdef
  set K := γ '' Icc 0 t with hKdef
  set L := {z : ℂ | z.im ≤ 0} with hLdef
  set Cl := ⋃ i ∈ I₀, flClArc ε (α i) (β i) with hCldef
  set seg := (fun x : ℝ => (x : ℂ)) '' Icc (-R) R with hsegdef
  have hKH : ∀ z ∈ K, z ∈ H → z ∈ γ '' Ioc 0 t := by
    rintro _ ⟨s, hs, rfl⟩ hH
    rcases hs.1.eq_or_lt with h0 | hpos
    · subst h0; simp [H, hγ0] at hH
    · exact ⟨s, ⟨hpos, hs.2⟩, rfl⟩
  have hLH : ∀ z ∈ L, z ∉ H := fun z hz hH => by
    simp only [hLdef, mem_ofPred_eq] at hz
    exact absurd (hH : (0 : ℝ) < z.im) (not_lt.2 hz)
  have hUeq : U = (H ∩ ball 0 R) \ (K ∪ Cl) := by
    ext z
    simp only [hUdef, Set.mem_sdiff, mem_inter_iff, mem_union, not_or]
    constructor
    · rintro ⟨⟨⟨hH, hK⟩, hb⟩, hA'⟩
      refine ⟨⟨hH, hb⟩, fun hk => hK (hKH z hk hH), fun hc => ?_⟩
      obtain ⟨i, hi, θ, hθ, rfl⟩ := mem_iUnion₂.1 hc
      rcases hθ.1.eq_or_lt with h1 | h1
      · rw [← h1] at hH hK
        rcases (hend i hi).1 with h | h
        · exact hK (hKH _ h hH)
        · exact hLH _ h hH
      rcases hθ.2.eq_or_lt with h2 | h2
      · rw [h2] at hH hK
        rcases (hend i hi).2 with h | h
        · exact hK (hKH _ h hH)
        · exact hLH _ h hH
      exact hA' (mem_iUnion₂.2 ⟨i, hi, θ, ⟨h1, h2⟩, rfl⟩)
    · rintro ⟨⟨hH, hb⟩, hK, hC⟩
      refine ⟨⟨⟨hH, fun h => hK (image_mono Ioc_subset_Icc_self h)⟩, hb⟩, fun h => hC ?_⟩
      obtain ⟨i, hi, hz⟩ := mem_iUnion₂.1 h
      exact mem_iUnion₂.2 ⟨i, hi, flCircArc_sub_clArc _ _ _ hz⟩
  have hKc : IsCompact K := isCompact_Icc.image_of_continuousOn hγc
  obtain ⟨hClc, hClu⟩ := flExist_ulc_biUnion I₀ (fun i => flClArc ε (α i) (β i))
    (fun i _ => isCompact_Icc.image (flClArc_cont ε))
    (fun i hi => flExist_ulc_image_Icc (hαβ i hi) (flClArc_cont ε).continuousOn)
  have hsegc : IsCompact seg := isCompact_Icc.image continuous_ofReal
  have hUo : IsOpen U := by
    rw [hUeq]
    exact (isOpen_H.inter isOpen_ball).sdiff (hKc.isClosed.union hClc.isClosed)
  set E := ((K ∪ seg) ∪ sphere (0 : ℂ) R) ∪ Cl with hEdef
  have hEc : IsCompact E := ((hKc.union hsegc).union (isCompact_sphere _ _)).union hClc
  have hEu : Topo.ULC E := by
    refine Topo.ULC.union_of_isCompact_of_isClosed ((hKc.union hsegc).union (isCompact_sphere _ _))
      hClc.isClosed ?_ hClu
    refine Topo.ULC.union_of_isCompact_of_isClosed (hKc.union hsegc) isClosed_sphere ?_
      (Topo.ULC.sphere _ _)
    exact Topo.ULC.union_of_isCompact_of_isClosed hKc hsegc.isClosed
      (flExist_ulc_image_Icc ht hγc)
      (flExist_ulc_image_Icc (by linarith) continuous_ofReal.continuousOn)
  have hsegL : seg ⊆ L := by
    rintro _ ⟨x, -, rfl⟩
    simp [hLdef]
  have hEU : E ⊆ Uᶜ := by
    intro z hz hzU
    rw [hUeq] at hzU
    obtain ⟨⟨hH, hb⟩, hKC⟩ := hzU
    rcases hz with ((hk | hs) | hs) | hc
    · exact hKC (Or.inl hk)
    · exact hLH z (hsegL hs) hH
    · rw [mem_sphere, dist_zero_right] at hs
      rw [mem_ball, dist_zero_right] at hb
      linarith
    · exact hKC (Or.inr hc)
  obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).1 hEc.isBounded
  have hUb : U ⊆ ball 0 (max r R) := by
    intro z hz
    rw [hUeq] at hz
    exact ball_subset_ball (le_max_right _ _) hz.1.2
  have hEb : E ⊆ closedBall 0 (max r R) := hr.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hfrE : frontier U ⊆ E := by
    intro z hz
    rw [hUo.frontier_eq] at hz
    obtain ⟨hcl, hnU⟩ := hz
    have hcl' : z ∈ {w : ℂ | 0 ≤ w.im} ∩ closedBall 0 R := by
      refine closure_minimal (fun w hw => ?_) ((isClosed_le continuous_const continuous_im).inter
        isClosed_closedBall) hcl
      rw [hUeq] at hw
      exact ⟨show (0 : ℝ) ≤ w.im from le_of_lt hw.1.1, ball_subset_closedBall hw.1.2⟩
    rw [hUeq] at hnU
    by_cases hKC : z ∈ K ∪ Cl
    · rcases hKC with hk | hc
      · exact Or.inl (Or.inl (Or.inl hk))
      · exact Or.inr hc
    · have hnb : ¬ (z ∈ H ∧ z ∈ ball 0 R) := fun h => hnU ⟨h, hKC⟩
      have hzn : ‖z‖ ≤ R := by simpa using hcl'.2
      by_cases hH : z ∈ H
      · have hb : z ∉ ball 0 R := fun h => hnb ⟨hH, h⟩
        rw [mem_ball, dist_zero_right, not_lt] at hb
        refine Or.inl (Or.inr ?_)
        rw [mem_sphere, dist_zero_right]
        linarith
      · have him : z.im = 0 := le_antisymm (not_lt.1 hH) hcl'.1
        refine Or.inl (Or.inl (Or.inr ⟨z.re, ⟨?_, ?_⟩, Complex.ext (by simp) (by simp [him])⟩))
        · linarith [neg_abs_le z.re, Complex.abs_re_le_norm z]
        · linarith [le_abs_self z.re, Complex.abs_re_le_norm z]
  have hΓ : IsPreconnected (K ∪ L) :=
    (isPreconnected_Icc.image γ hγc).union 0 ⟨0, ⟨le_rfl, ht⟩, hγ0⟩ (by simp [hLdef])
      flExist_lower_preconn
  have hΓU : K ∪ L ⊆ Uᶜ := by
    rintro z (hk | hl) hzU
    · rw [hUeq] at hzU; exact hzU.2 (Or.inl hk)
    · rw [hUeq] at hzU; exact hLH z hl hzU.1.1
  have hΓb : ¬ Bornology.IsBounded (K ∪ L) := fun h =>
    flExist_lower_unbdd (h.subset subset_union_right)
  have hcomp : ∀ a ∉ U, ∃ C : Set ℂ, IsPreconnected C ∧ a ∈ C ∧ C ⊆ Uᶜ ∧
      ¬ Bornology.IsBounded C := by
    intro a haU
    rw [hUeq] at haU
    by_cases hKC : a ∈ K ∪ Cl
    · rcases hKC with hk | hc
      · exact ⟨K ∪ L, hΓ, Or.inl hk, hΓU, hΓb⟩
      · obtain ⟨i, hi, hai⟩ := mem_iUnion₂.1 hc
        refine ⟨flClArc ε (α i) (β i) ∪ (K ∪ L),
          (isPreconnected_Icc.image _ (flClArc_cont ε).continuousOn).union _
            ⟨α i, left_mem_Icc.2 (hαβ i hi), rfl⟩ (hend i hi).1 hΓ, Or.inl hai, ?_,
          fun h => hΓb (h.subset subset_union_right)⟩
        refine union_subset (fun w hw hwU => ?_) hΓU
        rw [hUeq] at hwU
        exact hwU.2 (Or.inr (mem_iUnion₂.2 ⟨i, hi, hw⟩))
    · by_cases hH : a ∈ H
      · have hb : a ∉ ball 0 R := fun h => haU ⟨⟨hH, h⟩, hKC⟩
        have ha0 : a ≠ 0 := fun h => by simp [h, H] at hH
        refine ⟨_, flExist_ray_preconn a, ⟨1, show (1 : ℝ) ≤ 1 from le_rfl, by simp⟩, ?_, flExist_ray_unbdd ha0⟩
        rintro _ ⟨s, hs, rfl⟩ hwU
        rw [hUeq] at hwU
        have h1 := hwU.1.2
        rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs] at h1
        rw [mem_ball, dist_zero_right, not_lt] at hb
        simp only [mem_Ici] at hs
        rw [abs_of_pos (by linarith)] at h1
        nlinarith [norm_nonneg a]
      · exact ⟨K ∪ L, hΓ, Or.inr (show a.im ≤ 0 from not_lt.1 hH), hΓU, hΓb⟩
  exact flExist_of_frame hUo hUb hfin hA hAU hcomp hEc.isClosed hEu hfrE hEU hEb

/-- The harmonic measure of the removed arcs themselves (`A = ⋃ᵢ C_ε(αᵢ, βᵢ)`), as needed for the
inputs `hh`, `hw`, `hu` of `fl3_lemma33`. -/
theorem flExist_loewner_arcs {γ : ℝ → ℂ} {t R ε : ℝ} (ht : 0 ≤ t) (hR : 0 < R)
    (hγc : ContinuousOn γ (Icc 0 t)) (hγ0 : γ 0 = 0)
    {ι : Type*} (I₀ : Finset ι) {α β : ι → ℝ} (hαβ : ∀ i ∈ I₀, α i ≤ β i)
    (hend : ∀ i ∈ I₀, (ε : ℂ) * exp (α i * I) ∈ γ '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0} ∧
      (ε : ℂ) * exp (β i * I) ∈ γ '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0})
    (hfin : (connectedComponentIn (((H \ γ '' Ioc 0 t) ∩ ball 0 R) \
        ⋃ i ∈ I₀, flCircArc ε (α i) (β i)) ''
      (((H \ γ '' Ioc 0 t) ∩ ball 0 R) \ ⋃ i ∈ I₀, flCircArc ε (α i) (β i))).Finite) :
    ∃ g : ℂ → ℝ, IsHarmMeas (((H \ γ '' Ioc 0 t) ∩ ball 0 R) \
      ⋃ i ∈ I₀, flCircArc ε (α i) (β i)) (⋃ i ∈ I₀, flCircArc ε (α i) (β i)) g := by
  refine flExist_loewner ht hR hγc hγ0 I₀ hαβ hend ?_ disjoint_sdiff_right hfin
  refine (isBounded_sphere (x := (0 : ℂ)) (r := |ε|)).subset fun z hz => ?_
  obtain ⟨i, -, θ, -, rfl⟩ := mem_iUnion₂.1 hz
  simp [Complex.norm_exp_ofReal_mul_I]

lemma flExist_iUnion_univ {n : ℕ} (f : Fin n → Set ℂ) :
    (⋃ k, f k) = ⋃ k ∈ (Finset.univ : Finset (Fin n)), f k := by
  simp

lemma flExist_iUnion_single {n : ℕ} (f : Fin n → Set ℂ) (k : Fin n) :
    f k = ⋃ i ∈ ({k} : Finset (Fin n)), f i := by
  simp

lemma flExist_iUnion_ne {n : ℕ} (f : Fin n → Set ℂ) (k : Fin n) :
    (⋃ (i) (_ : i ≠ k), f i) = ⋃ i ∈ (Finset.univ.erase k : Finset (Fin n)), f i := by
  simp

end FieldLawler
end QuantumZipper
