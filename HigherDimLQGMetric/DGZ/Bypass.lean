import HigherDimLQGMetric.DGZ.BypassDefs
import HigherDimLQGMetric.DGZ.BypassSplice

/-!
# The bypass lemma (DGZ Lemma 5.11; packet L4b2)

Source: [2] = Ding–Gwynne–Zhuang, arXiv:2310.03996v5, Lemma 5.11 (TeX l. 2486–2598, pp. 48–50),
with the repairs of gap G12 written in MA7 (`planning/audits/MA7-ref2-sections-4-6.md`) Details (a)
D-5.11. Target (MA7 §5 row L4b2): `bypass : ∀ d, 2 ≤ d → BypassShape d`, deterministic; the cover
`IsBypassCover` is kept abstract, so nothing here depends on probability.

Proof (D-5.11, with the bookkeeping made explicit).
* **Levels.** The centres `z ∈ X j` that are `4Rs_j`-far (in `ℓ^∞`) from both endpoints of `γ` are
  processed level by level, `j = m - 1, …, 1` (`exists_bypass_level`), each centre at most once
  (`Finset.induction_on`): if the current path meets `B̄_{2Rs_j}(z)`, it is rerouted by the
  single-detour step `exists_detour_splice` along a detour of length `< w_j · across(x_z)` inside
  the shell `B̄_{4Rs_j}(z) \ B_{2Rs_j}(z)` (around-good property). After level `j` the path avoids
  `B_{2Rs_j}(z)` for all these centres, and each of its points is within `6Rs_j` of the path before
  level `j` (an entry point of a detour cannot lie on an earlier detour of the same level, by the
  separation `> s_{j+1}/4 ≥ 10Rs_j`).
* **Margins.** After the levels `> k` the path avoids `B_{Rs_j + 7Rs_k}(z)` for the processed
  centres of the levels `j > k` (`7Rs_k ≤ Rs_{k+1}`, and level `k + 1` moves points by at most
  `6Rs_{k+1}`).
* **Length bookkeeping.** `BypassLengthBound`: on every measurable set `J` of times at which the
  current path is in `G = B₂(0) \ 𝒰`, its LFPP integral is at most `len(γ|_G)` plus the costs of the
  inserted detours whose box `B̄_{4Rs_j}(z)` the path meets at a time of `J`. The in-place splice of
  `BypassSplice` keeps the untouched times, so this survives every detour.
* **Final cut.** `γ'` is the sub-path of the final path between the last visit of `B̄_{s_m}(γ(0))`
  before the first visit of `B̄_{s_m}(γ(1))`; it lies in `G` (the centres near the endpoints have
  `B_{Rs_j}(z) ⊆ B_{s_m}(γ(i))`), and its endpoints are `> 8s_m` apart.
* **Accounting.** For a detour met by `γ'`, the path `γ'` crosses
  `A′ = B̄_{4s_{j+1}}(x_z) \ B_{2s_{j+1}}(x_z)`, so the cost of the detour is at most
  `w_j · len(γ'|_{A′})` (`acrossDist_le_of_crossing`); a point lies in at most
  `41^d` sets `A′` of one level (`card_le_forty_one_pow`); so
  `ℓ(γ') ≤ len(γ|_G) + Σ_j 41^d w_j ℓ(γ') ≤ len(γ|_G) + ℓ(γ')/4`, whence `ℓ(γ') ≤ (4/3) len(γ|_G)`.

The hypotheses `d ≥ 2`, `s_m ≤ 1/100` and `X j ⊆ B₂(0)` of `BypassShape`/`IsBypassCover` are not
needed (`bypass_of_any`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ}

/-! ## `ℓ^∞` boxes -/

section Boxes

theorem mem_cbox_swap {a b : Rd d} {r : ℝ} : a ∈ cbox b r ↔ b ∈ cbox a r :=
  ⟨fun h i => by rw [abs_sub_comm]; exact h i, fun h i => by rw [abs_sub_comm]; exact h i⟩

/-- Triangle inequality for closed `ℓ^∞` boxes. -/
theorem mem_cbox_add {a b c : Rd d} {r r' : ℝ} (h1 : a ∈ cbox b r) (h2 : b ∈ cbox c r') :
    a ∈ cbox c (r + r') := fun i => by
  have e : a i - c i = (a i - b i) + (b i - c i) := by ring
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add (h1 i) (h2 i))

theorem mem_obox_add_of_mem_cbox {a b c : Rd d} {r r' : ℝ} (h1 : a ∈ cbox b r)
    (h2 : b ∈ obox c r') : a ∈ obox c (r + r') := fun i => by
  have e : a i - c i = (a i - b i) + (b i - c i) := by ring
  rw [e]
  exact (abs_add_le _ _).trans_lt (add_lt_add_of_le_of_lt (h1 i) (h2 i))

theorem mem_obox_add_of_mem_obox {a b c : Rd d} {r r' : ℝ} (h1 : a ∈ obox b r)
    (h2 : b ∈ cbox c r') : a ∈ obox c (r + r') := fun i => by
  have e : a i - c i = (a i - b i) + (b i - c i) := by ring
  rw [e]
  exact (abs_add_le _ _).trans_lt (add_lt_add_of_lt_of_le (h1 i) (h2 i))

theorem self_mem_cbox_of_nonneg (c : Rd d) {r : ℝ} (hr : 0 ≤ r) : c ∈ cbox c r := fun i => by
  rw [sub_self, abs_zero]
  exact hr

/-- **Packing** (MA7 D-5.11, "a point lies in at most `41^d` sets `A′_z`"): points of `ℝ^d` lying in
the cube `B̄_{20a}(p)` and pairwise more than `a` apart in `ℓ^∞` are at most `41^d` in number. -/
theorem card_le_forty_one_pow {ι : Type*} (S : Finset ι) (f : ι → Rd d) {p : Rd d} {a : ℝ}
    (ha : 0 < a) (hsep : ∀ i ∈ S, ∀ i' ∈ S, i ≠ i' → f i' ∉ cbox (f i) a)
    (hS : ∀ i ∈ S, f i ∈ cbox p (20 * a)) : S.card ≤ 41 ^ d := by
  classical
  set g : ι → Fin d → ℤ := fun i k => ⌊(f i k - p k) / a⌋ + 20 with hg
  have hmaps : Set.MapsTo g S (Fintype.piFinset fun _ : Fin d => Finset.Icc (0 : ℤ) 40) := by
    intro i hi
    rw [Finset.mem_coe] at hi ⊢
    rw [Fintype.mem_piFinset]
    intro k
    have hk := abs_le.1 (hS i hi k)
    have hlo : (-20 : ℝ) ≤ (f i k - p k) / a := by rw [le_div_iff₀ ha]; linarith
    have hhi : (f i k - p k) / a ≤ 20 := by rw [div_le_iff₀ ha]; linarith
    have h1 : (-20 : ℤ) ≤ ⌊(f i k - p k) / a⌋ := Int.le_floor.2 (by exact_mod_cast hlo)
    have h2 : ⌊(f i k - p k) / a⌋ ≤ 20 := by
      have : ((⌊(f i k - p k) / a⌋ : ℤ) : ℝ) ≤ 20 := (Int.floor_le _).trans hhi
      exact_mod_cast this
    rw [Finset.mem_Icc]
    simp only [hg]
    constructor <;> omega
  have hinj : Set.InjOn g S := by
    intro i hi i' hi' he
    by_contra hne
    refine hsep i hi i' hi' hne fun k => ?_
    have hk : ⌊(f i k - p k) / a⌋ = ⌊(f i' k - p k) / a⌋ := by
      have := congr_fun he k
      simp only [hg] at this
      omega
    have h1 := Int.abs_sub_lt_one_of_floor_eq_floor hk
    have e : (f i k - p k) / a - (f i' k - p k) / a = (f i k - f i' k) / a := by ring
    rw [e, abs_div, abs_of_pos ha, div_lt_one ha] at h1
    rw [abs_sub_comm]
    exact h1.le
  calc S.card ≤ (Fintype.piFinset fun _ : Fin d => Finset.Icc (0 : ℤ) 40).card :=
        Finset.card_le_card_of_injOn g hmaps hinj
    _ = 41 ^ d := by rw [Fintype.card_piFinset_const, Int.card_Icc]; rfl

end Boxes

/-! ## Length bookkeeping -/

/-- **Length bookkeeping of the bypass construction** (MA7 D-5.11, "Length"; the bookkeeping of
pieces with disjoint parameter intervals, gap G12). For the current path `π` and the finite set `T`
of inserted detours: on every measurable set `J ⊆ [0, 1]` of times at which `π` stays in `G`, the
LFPP integral of `π` over `J` is at most the length of the original path `γ` inside `G` plus the
costs of those detours `i ∈ T` whose region `K i` is met by `π` at a time of `J`. -/
def BypassLengthBound (ξ : ℝ) (φ : Rd d → ℝ) (γ : ℝ → Rd d) (G : Set (Rd d)) {ι : Type*}
    (K : ι → Set (Rd d)) (cost : ι → ℝ) (π : ℝ → Rd d) (T : Finset ι) : Prop :=
  ∀ J : Set ℝ, J ⊆ Icc 0 1 → MeasurableSet J → (∀ u ∈ J, π u ∈ G) →
    ∫ u in J, lfppIntegrand ξ φ π u ≤
      lfppLengthIn ξ φ γ G + ∑ i ∈ T, {i | ∃ u ∈ J, π u ∈ K i}.indicator cost i

section LengthBound

variable {ξ : ℝ} {φ : Rd d → ℝ} {γ : ℝ → Rd d} {G : Set (Rd d)} {ι : Type*}
  {K : ι → Set (Rd d)} {cost : ι → ℝ}

/-- At the start (no detour), the bookkeeping holds for the original path. -/
theorem bypassLengthBound_init (hφ : Continuous φ) {x y : Rd d} (hγ : IsPcwC1Path γ x y) :
    BypassLengthBound ξ φ γ G K cost γ ∅ := by
  intro J hJ _ hJG
  rw [Finset.sum_empty, add_zero, lfppLengthIn_eq_setIntegral]
  exact setIntegral_mono_set ((integrableOn_lfppIntegrand hγ hφ ξ).mono_set inter_subset_left)
    (ae_of_all _ fun u => lfppIntegrand_nonneg ξ φ γ u)
    (show J ⊆ Icc 0 1 ∩ γ ⁻¹' G from fun u hu => ⟨hJ hu, hJG u hu⟩).eventuallyLE

/-- **The bookkeeping survives a detour**: if on every measurable `J` the new path `π'` costs at
most the old path on some `J₀ ⊆ J` where they agree, plus `cost i₀`, and nothing more when `π'`
misses `K i₀` on `J`, then the bookkeeping holds for `π'` with the new detour `i₀ ∉ T`. -/
theorem BypassLengthBound.insert [DecidableEq ι] {π π' : ℝ → Rd d} {T : Finset ι}
    (hL : BypassLengthBound ξ φ γ G K cost π T) (hcost : ∀ i, 0 ≤ cost i) {i₀ : ι}
    (hi₀ : i₀ ∉ T)
    (hπ' : ∀ J : Set ℝ, J ⊆ Icc 0 1 → MeasurableSet J →
      ∃ J₀ ⊆ J, MeasurableSet J₀ ∧ (∀ u ∈ J₀, π' u = π u) ∧
        ∫ u in J, lfppIntegrand ξ φ π' u ≤ (∫ u in J₀, lfppIntegrand ξ φ π u) + cost i₀ ∧
        ((∀ u ∈ J, π' u ∉ K i₀) →
          ∫ u in J, lfppIntegrand ξ φ π' u ≤ ∫ u in J₀, lfppIntegrand ξ φ π u)) :
    BypassLengthBound ξ φ γ G K cost π' (insert i₀ T) := by
  intro J hJ hJm hJG
  obtain ⟨J₀, hJ₀J, hJ₀m, heq, hle, hle'⟩ := hπ' J hJ hJm
  have h1 := hL J₀ (hJ₀J.trans hJ) hJ₀m fun u hu => heq u hu ▸ hJG u (hJ₀J hu)
  have h2 : ∑ i ∈ T, {i | ∃ u ∈ J₀, π u ∈ K i}.indicator cost i ≤
      ∑ i ∈ T, {i | ∃ u ∈ J, π' u ∈ K i}.indicator cost i := by
    refine Finset.sum_le_sum fun i _ => Set.indicator_le_indicator_of_subset ?_ hcost i
    rintro i ⟨u, hu, huK⟩
    exact ⟨u, hJ₀J hu, by rw [heq u hu]; exact huK⟩
  rw [Finset.sum_insert hi₀]
  by_cases hmeet : i₀ ∈ {i | ∃ u ∈ J, π' u ∈ K i}
  · rw [Set.indicator_of_mem hmeet]
    linarith
  · rw [Set.indicator_of_notMem hmeet]
    have := hle' fun u hu huK => hmeet ⟨u, hu, huK⟩
    linarith

end LengthBound

/-! ## One level of the construction -/

section Level

variable {ξ : ℝ} {φ : Rd d → ℝ}

/-- **One level of the bypass construction** (MA7 D-5.11, "Level `j`", with `ρ = R s_j`). Let `Z`
be a finite set of centres, pairwise more than `10ρ` apart, each with an around-good shell
`B̄_{4ρ}(z) \ B_{2ρ}(z)` (inside `B`) of threshold `< cost (j, z)` and with both endpoints of `γ`
outside `B_{4ρ}(z)`. From a path `π₀` (piecewise `C¹` from `γ 0` to `γ 1` in `B`, with the length
bookkeeping for detours `T₀` of other levels) the centres of `Z` are processed one by one. The
result `π₁` avoids `B_{2ρ}(z)` for every `z ∈ Z`, each of its points is within `6ρ` of a point of
`π₀`, and the bookkeeping holds with the new detours `(j, z)`, `z ∈ Z`. -/
theorem exists_bypass_level (hφ : Continuous φ) {γ : ℝ → Rd d} {G B : Set (Rd d)}
    {K : ℕ × Rd d → Set (Rd d)} {cost : ℕ × Rd d → ℝ} (hcost : ∀ i, 0 ≤ cost i) {j : ℕ}
    {ρ : ℝ} (hρ : 0 < ρ) (hK : ∀ z, K (j, z) = cbox z (4 * ρ)) (Z : Finset (Rd d))
    (hsep : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → z' ∉ cbox z (10 * ρ))
    (hctrl : ∀ z ∈ Z, ∃ t, AroundGood ξ φ z (4 * ρ) (2 * ρ) B t ∧ t < cost (j, z))
    (hfar : ∀ z ∈ Z, γ 0 ∉ obox z (4 * ρ) ∧ γ 1 ∉ obox z (4 * ρ))
    {π₀ : ℝ → Rd d} {T₀ : Finset (ℕ × Rd d)} (hπ₀ : IsPcwC1Path π₀ (γ 0) (γ 1))
    (hπ₀B : MapsTo π₀ (Icc 0 1) B) (hT₀ : ∀ i ∈ T₀, i.1 ≠ j)
    (hL₀ : BypassLengthBound ξ φ γ G K cost π₀ T₀) :
    ∃ (π₁ : ℝ → Rd d) (T₁ : Finset (ℕ × Rd d)), IsPcwC1Path π₁ (γ 0) (γ 1) ∧
      MapsTo π₁ (Icc 0 1) B ∧ (∀ i ∈ T₁, i ∈ T₀ ∨ (i.1 = j ∧ i.2 ∈ Z)) ∧
      BypassLengthBound ξ φ γ G K cost π₁ T₁ ∧
      (∀ z ∈ Z, ∀ u ∈ Icc (0 : ℝ) 1, π₁ u ∉ obox z (2 * ρ)) ∧
      ∀ u ∈ Icc (0 : ℝ) 1, ∃ v ∈ Icc (0 : ℝ) 1, π₁ u ∈ cbox (π₀ v) (6 * ρ) := by
  classical
  suffices h : ∀ F : Finset (Rd d), F ⊆ Z → ∃ (π : ℝ → Rd d) (T : Finset (ℕ × Rd d)),
      IsPcwC1Path π (γ 0) (γ 1) ∧ MapsTo π (Icc 0 1) B ∧
      (∀ i ∈ T, i ∈ T₀ ∨ (i.1 = j ∧ i.2 ∈ F)) ∧ BypassLengthBound ξ φ γ G K cost π T ∧
      (∀ z ∈ F, ∀ u ∈ Icc (0 : ℝ) 1, π u ∉ obox z (2 * ρ)) ∧
      ∀ u ∈ Icc (0 : ℝ) 1, (∃ v ∈ Icc (0 : ℝ) 1, π u = π₀ v) ∨
        ∃ z ∈ F, π u ∈ cbox z (4 * ρ) ∧ ∃ v ∈ Icc (0 : ℝ) 1, π₀ v ∈ cbox z (2 * ρ) by
    obtain ⟨π, T, h1, h2, h3, h4, h5, h6⟩ := h Z subset_rfl
    refine ⟨π, T, h1, h2, h3, h4, h5, fun u hu => ?_⟩
    rcases h6 u hu with ⟨v, hv, he⟩ | ⟨z, -, hu', v, hv, hv'⟩
    · exact ⟨v, hv, he ▸ self_mem_cbox_of_nonneg (π₀ v) (by linarith)⟩
    · refine ⟨v, hv, ?_⟩
      have := mem_cbox_add hu' (mem_cbox_swap.1 hv')
      rwa [show 4 * ρ + 2 * ρ = 6 * ρ by ring] at this
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨π₀, T₀, hπ₀, hπ₀B, fun i hi => Or.inl hi, hL₀,
      fun z hz => absurd hz (Finset.notMem_empty z), fun u hu => Or.inl ⟨u, hu, rfl⟩⟩
  | insert a F haF ih =>
    intro hFZ
    obtain ⟨π, T, hπ, hπB, hT, hL, hav, himg⟩ := ih ((Finset.subset_insert a F).trans hFZ)
    have haZ : a ∈ Z := hFZ (Finset.mem_insert_self a F)
    -- boxes around `a` and another centre of `F` with radii adding up to `≤ 10ρ` are disjoint
    have hdisj : ∀ z ∈ F, ∀ (p : Rd d) (r r' : ℝ), r + r' ≤ 10 * ρ → p ∈ cbox a r →
        p ∈ cbox z r' → False := by
      intro z hz p r r' hrr hpa hpz
      have hne : a ≠ z := fun h => haF (h ▸ hz)
      exact hsep a haZ z (hFZ (Finset.mem_insert_of_mem hz)) hne
        (cbox_mono (by linarith) (mem_cbox_add (mem_cbox_swap.1 hpz) hpa))
    obtain ⟨t, hgood, htc⟩ := hctrl a haZ
    obtain ⟨π', hπ', hπ'B, hav', himg', hlen'⟩ := exists_detour_splice hφ hπ hπB
      (by linarith : 2 * ρ < 4 * ρ) hgood htc (hcost _) (hfar a haZ).1 (hfar a haZ).2
    have hnot : (j, a) ∉ T := by
      intro h
      rcases hT _ h with h | ⟨-, h⟩
      · exact hT₀ _ h rfl
      · exact haF h
    refine ⟨π', insert (j, a) T, hπ', hπ'B, ?_, ?_, ?_, ?_⟩
    · -- the new detour has level `j` and centre `a`
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact Or.inr ⟨rfl, Finset.mem_insert_self a F⟩
      · rcases hT i hi with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, Finset.mem_insert_of_mem h2⟩
    · -- the bookkeeping
      refine hL.insert hcost hnot fun J hJ hJm => ?_
      obtain ⟨J₀, h1, h2, h3, h4, h5⟩ := hlen' J hJ hJm
      refine ⟨J₀, h1, h2, h3, h4, fun h => h5 fun u hu => ?_⟩
      rw [← hK]
      exact h u hu
    · -- avoidance of the inner boxes of the processed centres
      intro z hz u hu
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hav' u hu
      · rcases himg' u hu with ⟨v, hv, he⟩ | ⟨hin, -⟩
        · rw [he]
          exact hav z hz v hv
        · exact fun h => hdisj z hz _ (4 * ρ) (2 * ρ) (by linarith) hin
            (HigherDimLFPP.DGZ.obox_subset_cbox z _ h)
    · -- new points are points of `π₀` or lie near a centre that `π₀` visits
      intro u hu
      rcases himg' u hu with ⟨v, hv, he⟩ | ⟨hin, v, hv, hvK⟩
      · rw [he]
        rcases himg v hv with h | ⟨z, hz, h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨z, Finset.mem_insert_of_mem hz, h1, h2⟩
      · rcases himg v hv with ⟨v', hv', he'⟩ | ⟨z, hz, h1, -⟩
        · exact Or.inr ⟨a, Finset.mem_insert_self a F, hin, v', hv', he' ▸ hvK⟩
        · exact (hdisj z hz _ (2 * ρ) (4 * ρ) (by linarith) hvK h1).elim

end Level

/-! ## The final cut and the accounting -/

section Final

variable {ξ : ℝ} {φ : Rd d → ℝ}

/-- **Final cut and accounting** (MA7 D-5.11, "Output" and "Length"). From the path `π` obtained
after all levels (avoiding `B_{Rs_j + 7Rs_0}(z)` for the processed centres `z ∈ Zf j`, with the
length bookkeeping for the detours `T`), the sub-path between the last visit of `B̄_{s_m}(γ(0))`
before the first visit of `B̄_{s_m}(γ(1))` is the bypass. -/
theorem exists_bypass_of_state (hφ : Continuous φ) {R : ℝ} {m : ℕ} {s w : ℕ → ℝ}
    {X : ℕ → Set (Rd d)} (hR : 1 ≤ R) (hs : ∀ j, 0 < s j)
    (hss : ∀ j, 40 * (R * s j) ≤ s (j + 1)) (hw : ∀ j, 0 ≤ w j)
    (hsum : (∑ j ∈ Finset.Ico 1 m, 2 * (41 : ℝ) ^ d * w j) ≤ 1 / 2)
    (hsep : ∀ j, ∀ z ∈ X j, ∀ z' ∈ X j, z ≠ z' → ¬ (z' ∈ cbox z (s (j + 1) / 4)))
    {xc : ℕ × Rd d → Rd d}
    (hxc : ∀ i : ℕ × Rd d, 1 ≤ i.1 → i.1 < m → i.2 ∈ X i.1 → xc i ∈ cbox i.2 (s (i.1 + 1)))
    {γ : ℝ → Rd d} (hfar : γ 1 ∉ cbox (γ 0) (10 * s m)) {Zf : ℕ → Finset (Rd d)}
    (hZf : ∀ j, ∀ z ∈ X j, z ∉ Zf j →
      γ 0 ∈ cbox z (4 * (R * s j)) ∨ γ 1 ∈ cbox z (4 * (R * s j)))
    {π : ℝ → Rd d} {T : Finset (ℕ × Rd d)} (hπ : IsPcwC1Path π (γ 0) (γ 1))
    (hπB : MapsTo π (Icc 0 1) (obox 0 2)) (hT : ∀ i ∈ T, 1 ≤ i.1 ∧ i.1 < m ∧ i.2 ∈ X i.1)
    (hL : BypassLengthBound ξ φ γ (obox 0 2 \ coverU R m s X)
      (fun i => cbox i.2 (4 * (R * s i.1)))
      (fun i => w i.1 * acrossDist ξ φ (xc i) (4 * s (i.1 + 1)) (2 * s (i.1 + 1))) π T)
    (hav : ∀ j, 1 ≤ j → j < m → ∀ z ∈ Zf j, ∀ u ∈ Icc (0 : ℝ) 1,
      π u ∉ obox z (R * s j + 7 * (R * s 0))) :
    ∃ γ' : ℝ → Rd d, IsPcwC1Path γ' (γ' 0) (γ' 1) ∧
      MapsTo γ' (Icc 0 1) (obox 0 2 \ coverU R m s X) ∧
      γ' 0 ∈ cbox (γ 0) (10 * s m) ∧ γ' 1 ∈ cbox (γ 1) (10 * s m) ∧
      lfppLength ξ φ γ' ≤ 2 * lfppLengthIn ξ φ γ (obox 0 2 \ coverU R m s X) := by
  classical
  set G : Set (Rd d) := obox 0 2 \ coverU R m s X with hG
  have hRpos : 0 < R := by linarith
  have hmono : Monotone s := monotone_nat_of_le_succ fun j => by
    have h1 := hss j
    have h2 : 0 < R * s j := mul_pos hRpos (hs j)
    nlinarith [hs j]
  have hsm : 0 < s m := hs m
  -- the two end boxes are disjoint
  have hdisj : Disjoint (cbox (γ 0) (s m)) (cbox (γ 1) (s m)) := by
    rw [Set.disjoint_left]
    intro p hp0 hp1
    exact hfar (cbox_mono (by linarith) (mem_cbox_add (mem_cbox_swap.1 hp1) hp0))
  obtain ⟨t₀, t₁, ht₀, ht₀₁, ht₁, h0K, h1K, hout⟩ := exists_cut_between hπ.continuousOn
    (HigherDimLFPP.DGZ.isClosed_cbox _ _) (HigherDimLFPP.DGZ.isClosed_cbox _ _) hdisj
    (by rw [hπ.source]; exact self_mem_cbox_of_nonneg _ hsm.le)
    (by rw [hπ.target]; exact self_mem_cbox_of_nonneg _ hsm.le)
  have hπc : ContinuousOn π (Icc t₀ t₁) := hπ.continuousOn.mono (Icc_subset_Icc ht₀ ht₁)
  -- on `[t₀, t₁]` the path avoids the two open end boxes
  have hcut : ∀ u ∈ Icc t₀ t₁, π u ∉ obox (γ 0) (s m) ∧ π u ∉ obox (γ 1) (s m) := by
    have hI0 : ∀ u ∈ Ioo t₀ t₁, π u ∉ obox (γ 0) (s m) := fun u hu h =>
      (hout u hu).1 (HigherDimLFPP.DGZ.obox_subset_cbox _ _ h)
    have hI1 : ∀ u ∈ Ioo t₀ t₁, π u ∉ obox (γ 1) (s m) := fun u hu h =>
      (hout u hu).2 (HigherDimLFPP.DGZ.obox_subset_cbox _ _ h)
    have hL0 := notMem_obox_left_of_Ioo ht₀₁ hπc hI0
    have hR1 := notMem_obox_right_of_Ioo ht₀₁ hπc hI1
    intro u hu
    rcases hu.1.lt_or_eq with h | h
    · rcases hu.2.lt_or_eq with h' | h'
      · exact ⟨hI0 u ⟨h, h'⟩, hI1 u ⟨h, h'⟩⟩
      · rw [h']
        exact ⟨fun h'' => Set.disjoint_left.1 hdisj
          (HigherDimLFPP.DGZ.obox_subset_cbox _ _ h'') h1K, hR1⟩
    · rw [← h]
      exact ⟨hL0, fun h'' => Set.disjoint_left.1 hdisj h0K
        (HigherDimLFPP.DGZ.obox_subset_cbox _ _ h'')⟩
  -- on `[t₀, t₁]` the path stays in `G = B₂(0) \ 𝒰`
  have hGt : ∀ u ∈ Icc t₀ t₁, π u ∈ G := by
    intro u hu
    have hu01 : u ∈ Icc (0 : ℝ) 1 := ⟨ht₀.trans hu.1, hu.2.trans ht₁⟩
    refine ⟨hπB hu01, fun hU => ?_⟩
    simp only [coverU, mem_iUnion] at hU
    obtain ⟨j, hj, z, hz, hzu⟩ := hU
    rw [Finset.mem_Ico] at hj
    have hRsj : 0 < R * s j := mul_pos hRpos (hs j)
    by_cases hzZ : z ∈ Zf j
    · have h7 : 0 ≤ 7 * (R * s 0) := by have := mul_pos hRpos (hs 0); linarith
      exact hav j hj.1 hj.2 z hzZ u hu01 (obox_mono (le_add_of_nonneg_right h7) hzu)
    · have h5 : 5 * (R * s j) ≤ s m := by
        have h1 := hss j
        have h2 := hmono (show j + 1 ≤ m by omega)
        linarith
      rcases hZf j z hz hzZ with h0 | h1
      · exact (hcut u hu).1 (obox_mono (by linarith)
          (mem_obox_add_of_mem_obox hzu (mem_cbox_swap.1 h0)))
      · exact (hcut u hu).2 (obox_mono (by linarith)
          (mem_obox_add_of_mem_obox hzu (mem_cbox_swap.1 h1)))
  -- the bypass `γ'`
  set γ' := subPath π t₀ t₁ with hγ'def
  have hγ' : IsPcwC1Path γ' (π t₀) (π t₁) := hπ.subPath ht₀ ht₀₁.le ht₁
  have hγ'0 : γ' 0 = π t₀ := subPath_zero π t₀ t₁
  have hγ'1 : γ' 1 = π t₁ := subPath_one π t₀ t₁
  have hlen : lfppLength ξ φ γ' = ∫ u in Icc t₀ t₁, lfppIntegrand ξ φ π u := by
    rw [hγ'def, lfppLength_subPath ξ φ π ht₀₁.le, intervalIntegral.integral_of_le ht₀₁.le,
      integral_Icc_eq_integral_Ioc]
  have hmain := hL (Icc t₀ t₁) (Icc_subset_Icc ht₀ ht₁) measurableSet_Icc hGt
  rw [← hlen] at hmain
  -- each detour met by `γ'` costs at most `w_j len(γ'|_{A′})`
  set A' : ℕ × Rd d → Set (Rd d) := fun i =>
    cbox (xc i) (4 * s (i.1 + 1)) \ obox (xc i) (2 * s (i.1 + 1)) with hA'
  have hterm : ∀ i ∈ T,
      {i : ℕ × Rd d | ∃ u ∈ Icc t₀ t₁, π u ∈ cbox i.2 (4 * (R * s i.1))}.indicator
        (fun i => w i.1 * acrossDist ξ φ (xc i) (4 * s (i.1 + 1)) (2 * s (i.1 + 1))) i ≤
      w i.1 * lfppLengthIn ξ φ γ' (A' i) := by
    intro i hi
    obtain ⟨hi1, him, hiX⟩ := hT i hi
    by_cases hmeet : i ∈ {i : ℕ × Rd d | ∃ u ∈ Icc t₀ t₁, π u ∈ cbox i.2 (4 * (R * s i.1))}
    · rw [Set.indicator_of_mem hmeet]
      refine mul_le_mul_of_nonneg_left ?_ (hw _)
      obtain ⟨u, hu, huK⟩ := hmeet
      have hxi := hxc i hi1 him hiX
      have hsj : s (i.1 + 1) ≤ s m := hmono (by omega)
      have hρj := hss i.1
      have hRsj : 0 < R * s i.1 := mul_pos hRpos (hs _)
      -- the visit at time `u` lies in the inner box of `A′`
      have hin : π u ∈ cbox (xc i) (2 * s (i.1 + 1)) :=
        cbox_mono (by linarith) (mem_cbox_add huK (mem_cbox_swap.1 hxi))
      have hc : 0 < t₁ - t₀ := sub_pos.2 ht₀₁
      have ha01 : (t₁ - t₀)⁻¹ * (u - t₀) ∈ Icc (0 : ℝ) 1 := by
        refine ⟨mul_nonneg (inv_nonneg.2 hc.le) (sub_nonneg.2 hu.1), ?_⟩
        rw [inv_mul_le_iff₀ hc, mul_one]
        linarith [hu.2]
      have hγ'a : γ' ((t₁ - t₀)⁻¹ * (u - t₀)) = π u := by
        rw [hγ'def]
        simp only [subPath]
        rw [mul_inv_cancel_left₀ hc.ne', sub_add_cancel]
      -- one endpoint of `γ'` lies outside the outer box of `A′`
      have hend : ∃ b ∈ Icc (0 : ℝ) 1, γ' b ∉ obox (xc i) (4 * s (i.1 + 1)) := by
        by_contra hcon
        push Not at hcon
        have e0 := hcon 0 (left_mem_Icc.2 zero_le_one)
        have e1 := hcon 1 (right_mem_Icc.2 zero_le_one)
        rw [hγ'0] at e0
        rw [hγ'1] at e1
        apply hfar
        have h3 := mem_cbox_add (mem_cbox_add (mem_cbox_add (mem_cbox_swap.1 h1K)
          (HigherDimLFPP.DGZ.obox_subset_cbox _ _ e1))
          (mem_cbox_swap.1 (HigherDimLFPP.DGZ.obox_subset_cbox _ _ e0))) h0K
        exact cbox_mono (by linarith) h3
      obtain ⟨b, hb, hbout⟩ := hend
      exact acrossDist_le_of_crossing hφ (by linarith [hs (i.1 + 1)]) hγ' ha01 hb
        (hγ'a ▸ hin) hbout
    · rw [Set.indicator_of_notMem hmeet]
      exact mul_nonneg (hw _) (lfppLengthIn_nonneg _ _ _ _)
  -- a point lies in at most `41^d` sets `A′` of one level
  have hlevel : ∀ j, ∑ i ∈ T with i.1 = j, w i.1 * lfppLengthIn ξ φ γ' (A' i) ≤
      (41 : ℝ) ^ d * w j * lfppLength ξ φ γ' := by
    intro j
    have hw' : ∑ i ∈ T with i.1 = j, w i.1 * lfppLengthIn ξ φ γ' (A' i) =
        w j * ∑ i ∈ T with i.1 = j, lfppLengthIn ξ φ γ' (A' i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2]
    have hmult : ∑ i ∈ T with i.1 = j, lfppLengthIn ξ φ γ' (A' i) ≤
        ((41 ^ d : ℕ) : ℝ) * lfppLength ξ φ γ' := by
      refine sum_lfppLengthIn_le_mul hφ hγ' _ A' (fun i _ =>
        (HigherDimLFPP.DGZ.isClosed_cbox _ _).measurableSet.diff
          (HigherDimLFPP.DGZ.isOpen_obox _ _).measurableSet) fun p => ?_
      refine card_le_forty_one_pow _ Prod.snd (p := p) (a := s (j + 1) / 4)
        (by linarith [hs (j + 1)]) ?_ ?_
      · intro i hi i' hi' hne
        simp only [Finset.mem_filter] at hi hi'
        have hj1 : i.1 = j := hi.1.2
        have hj2 : i'.1 = j := hi'.1.2
        have hne2 : i.2 ≠ i'.2 := fun h => hne (Prod.ext (hj1.trans hj2.symm) h)
        have hX1 := (hT i hi.1.1).2.2
        have hX2 := (hT i' hi'.1.1).2.2
        rw [hj1] at hX1
        rw [hj2] at hX2
        exact hsep j i.2 hX1 i'.2 hX2 hne2
      · intro i hi
        simp only [Finset.mem_filter] at hi
        obtain ⟨⟨hiT, hj1⟩, hpA⟩ := hi
        have hxi := hxc i (hT i hiT).1 (hT i hiT).2.1 (hT i hiT).2.2
        have h3 := mem_cbox_add (mem_cbox_swap.1 hxi) (mem_cbox_swap.1 hpA.1)
        rw [hj1] at h3
        exact cbox_mono (by linarith) h3
    rw [hw']
    calc w j * ∑ i ∈ T with i.1 = j, lfppLengthIn ξ φ γ' (A' i)
        ≤ w j * (((41 ^ d : ℕ) : ℝ) * lfppLength ξ φ γ') := mul_le_mul_of_nonneg_left hmult (hw j)
      _ = (41 : ℝ) ^ d * w j * lfppLength ξ φ γ' := by push_cast; ring
  have hfib : ∑ i ∈ T, w i.1 * lfppLengthIn ξ φ γ' (A' i) ≤
      (∑ j ∈ Finset.Ico 1 m, (41 : ℝ) ^ d * w j) * lfppLength ξ φ γ' := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := T) (t := Finset.Ico 1 m) (g := Prod.fst)
      (fun i hi => Finset.mem_Ico.2 ⟨(hT i hi).1, (hT i hi).2.1⟩)
      (fun i => w i.1 * lfppLengthIn ξ φ γ' (A' i)), Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => hlevel j
  have hquarter : (∑ j ∈ Finset.Ico 1 m, (41 : ℝ) ^ d * w j) ≤ 1 / 4 := by
    have e : (∑ j ∈ Finset.Ico 1 m, 2 * (41 : ℝ) ^ d * w j) =
        2 * ∑ j ∈ Finset.Ico 1 m, (41 : ℝ) ^ d * w j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    linarith
  have hℓ0 : 0 ≤ lfppLength ξ φ γ' := lfppLength_nonneg ξ φ γ'
  have hG0 : 0 ≤ lfppLengthIn ξ φ γ G := lfppLengthIn_nonneg ξ φ γ G
  have hkey : lfppLength ξ φ γ' ≤ lfppLengthIn ξ φ γ G + 1 / 4 * lfppLength ξ φ γ' :=
    calc lfppLength ξ φ γ'
        ≤ lfppLengthIn ξ φ γ G + ∑ i ∈ T, w i.1 * lfppLengthIn ξ φ γ' (A' i) :=
          hmain.trans (add_le_add le_rfl (Finset.sum_le_sum hterm))
      _ ≤ lfppLengthIn ξ φ γ G + (∑ j ∈ Finset.Ico 1 m, (41 : ℝ) ^ d * w j) *
            lfppLength ξ φ γ' := add_le_add le_rfl hfib
      _ ≤ lfppLengthIn ξ φ γ G + 1 / 4 * lfppLength ξ φ γ' :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right hquarter hℓ0)
  refine ⟨γ', by rw [hγ'0, hγ'1]; exact hγ', fun v hv => hGt _ (affine_mem_Icc ht₀₁.le hv),
    ?_, ?_, by linarith⟩
  · rw [hγ'0]
    exact cbox_mono (by linarith) h0K
  · rw [hγ'1]
    exact cbox_mono (by linarith) h1K

end Final

/-! ## The bypass lemma -/

/-- **DGZ Lemma 5.11** (MA7 D-5.11), in every dimension. -/
theorem bypass_of_any (d : ℕ) : BypassShape d := by
  intro ξ φ hφ R m s w X hR hs hss hw hsum _ hX γ hγ hγB hfar
  classical
  have hR1 : 1 ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  have hss' : ∀ j, 40 * (R * s j) ≤ s (j + 1) := fun j => by
    have := hss j
    rwa [mul_assoc] at this
  have h7 : ∀ k, 7 * (R * s k) ≤ R * s (k + 1) := fun k => by
    have h1 := hss' k
    have h2 : 0 < R * s k := mul_pos hRpos (hs k)
    have h3 : s (k + 1) ≤ R * s (k + 1) := by nlinarith [hs (k + 1)]
    linarith
  -- the control points `x_z` of the cover
  have hctrl : ∀ i : ℕ × Rd d, ∃ x : Rd d, 1 ≤ i.1 → i.1 < m → i.2 ∈ X i.1 →
      x ∈ cbox i.2 (s (i.1 + 1)) ∧ ∃ t : ℝ,
        AroundGood ξ φ i.2 (4 * R * s i.1) (2 * R * s i.1) (obox 0 2) t ∧
        t < w i.1 * acrossDist ξ φ x (4 * s (i.1 + 1)) (2 * s (i.1 + 1)) := by
    intro i
    by_cases h : 1 ≤ i.1 ∧ i.1 < m ∧ i.2 ∈ X i.1
    · obtain ⟨x, hx, t, ht⟩ := hX.ctrl i.1 h.1 h.2.1 i.2 h.2.2
      exact ⟨x, fun _ _ _ => ⟨hx, t, ht⟩⟩
    · exact ⟨0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose xc hxc using hctrl
  -- the centres processed at level `j`: those `4Rs_j`-far from both endpoints of `γ`
  set Zf : ℕ → Finset (Rd d) := fun j => (hX.finite j).toFinset.filter fun z =>
    γ 0 ∉ cbox z (4 * (R * s j)) ∧ γ 1 ∉ cbox z (4 * (R * s j)) with hZf
  have hZmem : ∀ j z, z ∈ Zf j ↔
      z ∈ X j ∧ γ 0 ∉ cbox z (4 * (R * s j)) ∧ γ 1 ∉ cbox z (4 * (R * s j)) := by
    intro j z
    simp only [hZf, Finset.mem_filter, Set.Finite.mem_toFinset]
  set K : ℕ × Rd d → Set (Rd d) := fun i => cbox i.2 (4 * (R * s i.1)) with hK
  set cost : ℕ × Rd d → ℝ := fun i =>
    w i.1 * acrossDist ξ φ (xc i) (4 * s (i.1 + 1)) (2 * s (i.1 + 1)) with hcostdef
  set G : Set (Rd d) := obox 0 2 \ coverU R m s X with hG
  have hcost : ∀ i, 0 ≤ cost i := fun i => mul_nonneg (hw _) (acrossDist_nonneg _ _ _ _ _)
  -- the levels `> k` processed, by downward induction on `k`
  have key : ∀ n k : ℕ, m ≤ k + n → ∃ (π : ℝ → Rd d) (T : Finset (ℕ × Rd d)),
      IsPcwC1Path π (γ 0) (γ 1) ∧ MapsTo π (Icc 0 1) (obox 0 2) ∧
      (∀ i ∈ T, k + 1 ≤ i.1 ∧ i.1 < m ∧ i.2 ∈ X i.1) ∧
      BypassLengthBound ξ φ γ G K cost π T ∧
      ∀ j, k + 1 ≤ j → j < m → ∀ z ∈ Zf j, ∀ u ∈ Icc (0 : ℝ) 1,
        π u ∉ obox z (R * s j + 7 * (R * s k)) := by
    intro n
    induction n with
    | zero =>
      intro k hk
      exact ⟨γ, ∅, hγ, hγB, fun i hi => absurd hi (Finset.notMem_empty i),
        bypassLengthBound_init hφ hγ, fun j hj hjm => absurd hjm (by omega)⟩
    | succ n ih =>
      intro k hk
      obtain ⟨π₀, T₀, hπ₀, hπ₀B, hT₀, hL₀, hav₀⟩ := ih (k + 1) (by omega)
      by_cases hkm : k + 1 < m
      · -- process the level `k + 1`
        have hρ : 0 < R * s (k + 1) := mul_pos hRpos (hs _)
        obtain ⟨π₁, T₁, hπ₁, hπ₁B, hT₁, hL₁, hav₁, hclose⟩ :=
          exists_bypass_level (j := k + 1) (ρ := R * s (k + 1)) hφ hcost hρ (fun z => rfl)
            (Zf (k + 1))
            (fun z hz z' hz' hne h => hX.sep (k + 1) z ((hZmem _ _).1 hz).1 z'
              ((hZmem _ _).1 hz').1 hne (cbox_mono (by linarith [hss' (k + 1)]) h))
            (fun z hz => by
              obtain ⟨-, t, hgood, htc⟩ := hxc (k + 1, z) (by omega) hkm ((hZmem _ _).1 hz).1
              exact ⟨t, by simpa only [mul_assoc] using hgood, htc⟩)
            (fun z hz => ⟨fun h => ((hZmem _ _).1 hz).2.1
                (HigherDimLFPP.DGZ.obox_subset_cbox _ _ h),
              fun h => ((hZmem _ _).1 hz).2.2 (HigherDimLFPP.DGZ.obox_subset_cbox _ _ h)⟩)
            hπ₀ hπ₀B (fun i hi => by have := (hT₀ i hi).1; omega) hL₀
        refine ⟨π₁, T₁, hπ₁, hπ₁B, fun i hi => ?_, hL₁, ?_⟩
        · rcases hT₁ i hi with h | ⟨h1, h2⟩
          · have := hT₀ i h
            exact ⟨by omega, this.2⟩
          · rw [h1]
            exact ⟨le_rfl, hkm, ((hZmem _ _).1 h2).1⟩
        · intro j hj hjm z hz u hu hzu
          rcases (show j = k + 1 ∨ k + 1 + 1 ≤ j by omega) with rfl | hj'
          · exact hav₁ z hz u hu (obox_mono (by linarith [h7 k]) hzu)
          · obtain ⟨v, hv, hvc⟩ := hclose u hu
            exact hav₀ j hj' hjm z hz v hv (obox_mono (by linarith [h7 k])
              (mem_obox_add_of_mem_cbox (mem_cbox_swap.1 hvc) hzu))
      · -- no level `k + 1` below `m`
        exact ⟨π₀, T₀, hπ₀, hπ₀B, fun i hi => ⟨by have := (hT₀ i hi).1; omega, (hT₀ i hi).2⟩,
          hL₀, fun j hj hjm => absurd hjm (by omega)⟩
  obtain ⟨π, T, hπ, hπB, hT, hL, hav⟩ := key m 0 (by omega)
  have hZf' : ∀ j, ∀ z ∈ X j, z ∉ Zf j →
      γ 0 ∈ cbox z (4 * (R * s j)) ∨ γ 1 ∈ cbox z (4 * (R * s j)) := by
    intro j z hz hzZ
    by_contra h
    push Not at h
    exact hzZ ((hZmem j z).2 ⟨hz, h.1, h.2⟩)
  exact exists_bypass_of_state hφ hR1 hs hss' hw hsum hX.sep
    (fun i h1 h2 h3 => (hxc i h1 h2 h3).1) hfar hZf' hπ hπB hT hL hav

/-- **DGZ Lemma 5.11** (MA7 §5 row L4b2): `bypass : ∀ d, 2 ≤ d → BypassShape d`. -/
theorem bypass (d : ℕ) (_hd : 2 ≤ d) : BypassShape d :=
  bypass_of_any d

end HigherDimLQGMetric.DGZ
