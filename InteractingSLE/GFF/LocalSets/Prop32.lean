import InteractingSLE.GFF.LocalSets.GermZeroOne
import InteractingSLE.GFF.LocalSets.GermCutoff

/-!
# Proposition 3.2: the σ-algebra of the projection onto `H^⊥(D ∖ K)` is the germ on `K`

Source: `source/ig1-specification.pdf`, §3.1, Proposition 3.2 and its proof (pp. 43–44;
transcription `source/spec/p001-048.md#prop-3.2`, `#prop-3.2-proof`): for a deterministic closed
`K ⊆ D`, `F_{K+}^h = ⋂_{U ⊇ K} F_U^h`, the intersection over all open `U ⊆ D` containing `K`, with
completed σ-algebras ("We work with completed sigma-algebras").

Here `F_U^h = restrictSigma U h = σ(h|_U)`; `F_{K+}^h = complSigma h hV = σ(h − h_V)` for a Markov
decomposition `h = h_V + (h − h_V)` along `V = D ∖ K` (Proposition 3.1; `h − h_V` is the
projection of `h` onto `H^⊥(D ∖ K)`); completion is QuantumZipper's
`LateralGerm.aeClosure m P` (sets a.e. equal to a set of `m`). `K` closed in `D` is
`IsOpen (D ∖ K)`.

## Main results

* `IsMarkovDecomposition.exists_ae_eq_complSigma_of_mem_iInf_restrictSigma_of_disjoint`: for open
  `U₀ ⊇ U₁ ⊇ ⋯` in an admissible `D` that every compact subset of `V` eventually avoids,
  `⋂ₙ F_{Uₙ} ⊆ F_{K+}` modulo null sets (the conditional helper of `GermExchange.lean` with its
  hypothesis `htriv` discharged by the germ zero-one law of `GermZeroOne.lean`);
* `iInf_aeClosure_restrictSigma_le_aeClosure_complSigma` (**Proposition 3.2, `⊇`**, any
  admissible `D`, any Markov decomposition, completed σ-algebras):
  `⋂_{U ⊇ K} F̄_U ⊆ F̄_{K+}`; `iInf_restrictSigma_le_aeClosure_complSigma` (uncompleted
  intersection);
* `aeClosure_complSigma_le_aeClosure_restrictSigma_of_isCompact` (**Proposition 3.2, `⊆`**,
  `D = ℍ`, `ℍ ∖ K` relatively compact in `ℍ`): `F̄_{K+} ⊆ F̄_U` for every open `U ⊇ K`, from
  PROVE-LS-B2's germ lemma `LocalSets.exists_measurable_markovCompl_germ`;
* `aeClosure_complSigma_eq_iInf_aeClosure_restrictSigma_of_isCompact` (**Proposition 3.2**, `D = ℍ`,
  `ℍ ∖ K` relatively compact in `ℍ`, any Markov decomposition): `F̄_{K+} = ⋂_{U ⊇ K} F̄_U`;
  `…_of_isCompact_closure`: the same for `K = ℍ ∖ W`, `W` open with compact closure in `ℍ`.

The inclusion `F_{K+} ⊆ F_U` for a general closed `K` and a general open `U ⊇ K` (no uniform
margin) is the Dirichlet ideal property of the source proof (quasi-continuous representatives)
and is not proved here; see the PROVE-LS-A3 handoff.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric
open QuantumZipper QuantumZipper.GermZeroOne QuantumZipper.LateralGerm LQGMetric

namespace InteractingSLE
namespace GFF

/-! ### The thickened neighbourhoods `Uₙ = D ∩ {dist(·, K) < 1/(n+1)}` -/

section Thickening

/-- `D ∩ {z : dist(z, K) < 1/(n+1)}`, the open neighbourhoods of `K` used in the proof. -/
def germOpens (D : Opens ℂ) (K : Set ℂ) (n : ℕ) : Opens ℂ :=
  D ⊓ ⟨thickening (1 / ((n : ℝ) + 1)) K, isOpen_thickening⟩

lemma germOpens_le (D : Opens ℂ) (K : Set ℂ) (n : ℕ) : germOpens D K n ≤ D := inf_le_left

lemma antitone_germOpens (D : Opens ℂ) (K : Set ℂ) : Antitone (germOpens D K) := by
  intro m n hmn
  refine inf_le_inf_left D (thickening_mono ?_ K)
  gcongr

lemma subset_germOpens {D : Opens ℂ} {K : Set ℂ} (hKD : K ⊆ D) (n : ℕ) :
    K ⊆ germOpens D K n :=
  fun x hx => ⟨hKD hx, self_subset_thickening (by positivity) K hx⟩

/-- Every compact subset of `D ∖ K` (`K` closed in `D`) is disjoint from some `Uₙ`. -/
lemma exists_disjoint_germOpens {D : Opens ℂ} {K : Set ℂ} (hK : IsOpen ((D : Set ℂ) \ K))
    {C : Set ℂ} (hC : IsCompact C) (hCV : C ⊆ (D : Set ℂ) \ K) :
    ∃ n, Disjoint C (germOpens D K n) := by
  have hCK : C ⊆ (closure K)ᶜ := fun x hx hxK => by
    have := hK.inter_closure ⟨hCV hx, hxK⟩
    rw [sdiff_inter_self, closure_empty] at this
    exact this
  obtain ⟨δ, hδ, hsub⟩ := hC.exists_thickening_subset_open isClosed_closure.isOpen_compl hCK
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n, Set.disjoint_left.2 fun x hxC hxU => ?_⟩
  obtain ⟨k, hk, hxk⟩ := mem_thickening_iff.1 hxU.2
  have : k ∈ thickening δ C := mem_thickening_iff.2 ⟨x, hxC, by rw [dist_comm]; linarith⟩
  exact hsub this (subset_closure hk)

end Thickening

/-! ### `⋂ₙ F_{Uₙ} ⊆ F_{K+}` -/

section Inclusion

variable {D V : Opens ℂ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h hV : Ω → DistOn D}

/-- **`⋂ₙ F_{Uₙ} ⊆ F_{K+}` modulo null sets** (unconditional form of
`exists_ae_eq_complSigma_of_mem_iInf_restrictSigma`). For a Markov decomposition
`h = h_V + (h − h_V)` on an admissible `D` and open `U₀ ⊇ U₁ ⊇ ⋯` in `D` such that every compact
subset of `V` is disjoint from some `Uₙ`, every event of `⋂ₙ σ(h|_{Uₙ})` agrees almost surely with
an event of `σ(h − h_V)`. -/
theorem IsMarkovDecomposition.exists_ae_eq_complSigma_of_mem_iInf_restrictSigma_of_disjoint
    (hD : ZBAdmissible D) (hVD : V ≤ D) (hhm : Measurable h)
    (hd : IsMarkovDecomposition V D h hV P) {U : ℕ → Opens ℂ} (hU : Antitone U)
    (hUD : ∀ n, U n ≤ D)
    (hsep : ∀ C : Set ℂ, IsCompact C → C ⊆ V → ∃ n, Disjoint C (U n))
    {E : Set Ω} (hE : MeasurableSet[⨅ n, restrictSigma (U n) h] E) :
    ∃ E' : Set Ω, MeasurableSet[complSigma h hV] E' ∧ E =ᵐ[P] E' :=
  exists_ae_eq_complSigma_of_mem_iInf_restrictSigma hhm hd hU hUD
    (hd.isZBGFFExtOn.isTrivialSigma_iInf_restrictSigma hD hVD hU hUD hsep) hE

/-- `⋂ₙ F_{Uₙ} ⊆ F_{K+}` modulo null sets for the thickenings `Uₙ = D ∩ {dist(·, K) < 1/(n+1)}`
of a set `K` closed in `D`. -/
theorem IsMarkovDecomposition.exists_ae_eq_complSigma_of_mem_iInf_germOpens {K : Set ℂ}
    (hK : IsOpen ((D : Set ℂ) \ K)) (hD : ZBAdmissible D) (hhm : Measurable h)
    (hd : IsMarkovDecomposition ⟨(D : Set ℂ) \ K, hK⟩ D h hV P) {E : Set Ω}
    (hE : MeasurableSet[⨅ n, restrictSigma (germOpens D K n) h] E) :
    ∃ E' : Set Ω, MeasurableSet[complSigma h hV] E' ∧ E =ᵐ[P] E' :=
  hd.exists_ae_eq_complSigma_of_mem_iInf_restrictSigma_of_disjoint hD sdiff_subset hhm
    (antitone_germOpens D K) (germOpens_le D K)
    (fun _ hC hCV => exists_disjoint_germOpens hK hC hCV) hE

omit [IsProbabilityMeasure P] in
/-- A set that is a.e. equal to an event of each `F_{Uₙ}` (`Uₙ` decreasing) is a.e. equal to an
event of `⋂ₙ F_{Uₙ}` (its `limsup`). -/
lemma exists_ae_eq_mem_iInf_restrictSigma {U : ℕ → Opens ℂ} (hU : Antitone U)
    (hUD : ∀ n, U n ≤ D) {E : Set Ω}
    (hE : ∀ n, MeasurableSet[aeClosure (restrictSigma (U n) h) P] E) :
    ∃ E' : Set Ω, MeasurableSet[⨅ n, restrictSigma (U n) h] E' ∧ E =ᵐ[P] E' := by
  choose F hF hEF using hE
  set G : ℕ → Set Ω := fun m => ⋃ n, ⋃ (_ : m ≤ n), F n
  have hG : ∀ k m, k ≤ m → MeasurableSet[restrictSigma (U k) h] (G m) := fun k m hkm =>
    MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun hmn =>
      restrictSigma_antitone (hU (hkm.trans hmn)) (hUD k) h _ (hF n)
  have hGanti : ∀ m, G (m + 1) ⊆ G m := fun m =>
    iUnion_mono fun n => iUnion_subset fun hmn => subset_iUnion_of_subset (Nat.le_of_succ_le hmn)
      subset_rfl
  have hGeq : ∀ k, ⋂ m, G m = ⋂ m, G (m + k) := by
    intro k
    refine Subset.antisymm (subset_iInter fun m => iInter_subset _ _) (subset_iInter fun m => ?_)
    refine (iInter_subset _ m).trans ?_
    induction k with
    | zero => simp
    | succ k ih => exact (hGanti _).trans (by simpa [Nat.add_succ] using ih)
  refine ⟨⋂ m, G m, ?_, ?_⟩
  · rw [MeasurableSpace.measurableSet_iInf]
    intro k
    rw [hGeq k]
    exact MeasurableSet.iInter fun m => hG k (m + k) (Nat.le_add_left k m)
  · have hall : ∀ᵐ ω ∂P, ∀ n, (ω ∈ E) = (ω ∈ F n) := ae_all_iff.2 hEF
    filter_upwards [hall] with ω hω
    simp only [eq_iff_iff, G, mem_iInter, mem_iUnion]
    constructor
    · intro hωE m
      exact ⟨m, le_rfl, by rw [← hω m]; exact hωE⟩
    · intro h'
      obtain ⟨n, -, hn⟩ := h' 0
      rw [hω n]; exact hn

/-- **Proposition 3.2, inclusion `⋂_{U ⊇ K} F_U ⊆ F_{K+}`** (completed σ-algebras; any admissible
`D`, any set `K ⊆ D` closed in `D`, any Markov decomposition along `D ∖ K`). -/
theorem iInf_aeClosure_restrictSigma_le_aeClosure_complSigma {K : Set ℂ}
    (hK : IsOpen ((D : Set ℂ) \ K)) (hKD : K ⊆ D) (hD : ZBAdmissible D) (hhm : Measurable h)
    (hd : IsMarkovDecomposition ⟨(D : Set ℂ) \ K, hK⟩ D h hV P) :
    (⨅ (U : Opens ℂ) (_ : U ≤ D) (_ : K ⊆ U), aeClosure (restrictSigma U h) P) ≤
      aeClosure (complSigma h hV) P := by
  intro E hE
  have hEn : ∀ n, MeasurableSet[aeClosure (restrictSigma (germOpens D K n) h) P] E := by
    intro n
    simp only [MeasurableSpace.measurableSet_iInf] at hE
    exact hE _ (germOpens_le D K n) (subset_germOpens hKD n)
  obtain ⟨E', hE', hEE'⟩ := exists_ae_eq_mem_iInf_restrictSigma (antitone_germOpens D K)
    (germOpens_le D K) hEn
  obtain ⟨E'', hE'', hE'E''⟩ := hd.exists_ae_eq_complSigma_of_mem_iInf_germOpens hK hD hhm hE'
  exact ⟨E'', hE'', hEE'.trans hE'E''⟩

/-- **Proposition 3.2, inclusion `⋂_{U ⊇ K} F_U ⊆ F_{K+}` modulo null sets** (intersection of the
uncompleted σ-algebras). -/
theorem iInf_restrictSigma_le_aeClosure_complSigma {K : Set ℂ} (hK : IsOpen ((D : Set ℂ) \ K))
    (hKD : K ⊆ D) (hD : ZBAdmissible D) (hhm : Measurable h)
    (hd : IsMarkovDecomposition ⟨(D : Set ℂ) \ K, hK⟩ D h hV P) :
    (⨅ (U : Opens ℂ) (_ : U ≤ D) (_ : K ⊆ U), restrictSigma U h) ≤
      aeClosure (complSigma h hV) P := by
  refine le_trans ?_ (iInf_aeClosure_restrictSigma_le_aeClosure_complSigma hK hKD hD hhm hd)
  exact iInf₂_mono fun U _ => iInf_mono fun _ =>
    (aeSub_of_le le_rfl : AESub (restrictSigma U h) (restrictSigma U h) P)

end Inclusion

/-! ### `F_{K+} ⊆ F_U` on `ℍ` when `ℍ ∖ K` is relatively compact -/

section UpperHalfPlane

/-- A smooth cutoff `χ ∈ C_c^∞(W)` with values in `[0, 1]`, equal to `1` on a neighbourhood of the
compact set `s ⊆ W`. -/
lemma exists_cutoff_of_isCompact {s W : Set ℂ} (hs : IsCompact s) (hW : IsOpen W) (hsW : s ⊆ W) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ (∀ z, χ z ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ W ∧ tsupport (fun z => 1 - χ z) ⊆ sᶜ := by
  obtain ⟨δ, hδ, hsub⟩ := hs.exists_cthickening_subset_open hW hsW
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    (isOpen_thickening (δ := δ) (E := s)) (isClosed_cthickening (δ := δ / 2) (E := s))
    (cthickening_subset_thickening' hδ (by linarith) s)
  have htsupp : tsupport χ ⊆ cthickening δ s := by
    rw [tsupport, hχs]
    exact closure_thickening_subset_cthickening δ s
  refine ⟨χ, hχ, fun z => hχr ⟨z, rfl⟩, ?_, htsupp.trans hsub, ?_⟩
  · exact hs.cthickening.of_isClosed_subset (isClosed_tsupport _) htsupp
  · have hsupp : Function.support (fun z => 1 - χ z) ⊆ (thickening (δ / 2) s)ᶜ := by
      intro z hz hzs
      exact hz (by rw [sub_eq_zero]; exact ((hχ1 z).1
        (thickening_subset_cthickening _ _ hzs)).symm)
    refine (closure_minimal hsupp isOpen_thickening.isClosed_compl).trans ?_
    exact compl_subset_compl.2 (self_subset_thickening (by linarith) s)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

omit mΩ [IsProbabilityMeasure P] in
/-- `σ(h(ψ) : supp ψ ⊆ U) ⊆ σ(h|_U)`. -/
lemma fieldSigmaOn_le_restrictSigma {U : Opens ℂ} (hU : U ≤ upperHalfPlaneOpens) :
    LocalSets.fieldSigmaOn h U ≤ restrictSigma U h := by
  refine iSup₂_le fun ψ hψ => ?_
  let ψ' : TestOn U :=
    { toFun := ψ
      contDiff' := ψ.contDiff
      hasCompactSupport' := ψ.hasCompactSupport
      tsupport_subset' := hψ }
  have e : testIncl U upperHalfPlaneOpens ψ' = ψ :=
    TestFunction.ext fun x => by rw [coe_testIncl hU]; rfl
  have hm : Measurable[restrictSigma U h] fun ω => restrictDist U (h ω) ψ' :=
    (measurable_distOn_apply ψ').comp (comap_measurable fun ω => restrictDist U (h ω))
  simp_rw [restrictDist_apply, e] at hm
  exact hm.comap_le

/-- **Proposition 3.2, inclusion `F_{K+} ⊆ F_U`**, on `ℍ`, for `K ⊆ ℍ` closed in `ℍ` such that
`ℍ ∖ K` is relatively compact in `ℍ`, any Markov decomposition along `ℍ ∖ K`, and any open
`U ⊆ ℍ` containing `K` (completed σ-algebras). From PROVE-LS-B2's germ lemma
`LocalSets.exists_measurable_markovCompl_germ` with a cutoff equal to `1` near `ℍ ∖ U`. -/
theorem aeClosure_complSigma_le_aeClosure_restrictSigma_of_isCompact {K : Set ℂ}
    (hK : IsOpen ((upperHalfPlaneOpens : Set ℂ) \ K))
    (hKc : IsCompact (closure ((upperHalfPlaneOpens : Set ℂ) \ K)))
    (hKH : closure ((upperHalfPlaneOpens : Set ℂ) \ K) ⊆ upperHalfPlaneOpens)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {hV : Ω → DistOn upperHalfPlaneOpens}
    (hd : IsMarkovDecomposition ⟨(upperHalfPlaneOpens : Set ℂ) \ K, hK⟩ upperHalfPlaneOpens h
      hV P) {U : Opens ℂ} (hU : U ≤ upperHalfPlaneOpens) (hKU : K ⊆ U) :
    aeClosure (complSigma h hV) P ≤ aeClosure (restrictSigma U h) P := by
  set W : Opens ℂ := ⟨(upperHalfPlaneOpens : Set ℂ) \ K, hK⟩
  have hWH : (W : Set ℂ) ⊆ H := sdiff_subset
  obtain ⟨G, hGm, hG⟩ := LocalSets.exists_markovMap W hWH
  have hdG := hG hh
  have hVG : hV =ᵐ[P] fun ω => G (h ω) := LocalSets.ae_eq_of_isMarkovDecomposition hWH hd hdG
  -- the cutoff
  set s : Set ℂ := (upperHalfPlaneOpens : Set ℂ) \ U
  have hsW : s ⊆ W := fun z hz => ⟨hz.1, fun hzK => hz.2 (hKU hzK)⟩
  have hscl : IsClosed s := by
    refine closure_subset_iff_isClosed.1 fun z hz => ⟨hKH (closure_mono hsW hz), ?_⟩
    exact (closure_minimal (fun w hw => hw.2) U.isOpen.isClosed_compl) hz
  obtain ⟨χ, hχ, hχ01, hχc, hχW, hχs⟩ :=
    exists_cutoff_of_isCompact (hKc.of_isClosed_subset hscl (hsW.trans subset_closure)) W.isOpen
      hsW
  have hχO : tsupport (fun z => 1 - χ z) ∩ H ⊆ U := fun z hz => by
    by_contra hzU
    exact hχs hz.1 ⟨hz.2, hzU⟩
  -- every pairing of `h − G h` has a `σ(h|_U)`-measurable version
  have hpair : ∀ Φ : TestOn upperHalfPlaneOpens,
      AESub (MeasurableSpace.comap (fun ω => (h ω - G (h ω)) Φ) inferInstance)
        (restrictSigma U h) P := by
    intro Φ
    obtain ⟨Z, hZ, hZe⟩ := LocalSets.exists_measurable_markovCompl_germ hh hWH hdG hχ hχ01 hχc
      hχW hχO Φ
    exact aeSub_comap (hZ.mono (fieldSigmaOn_le_restrictSigma hU) le_rfl) hZe
  have hG' : AESub (complSigma h fun ω => G (h ω)) (restrictSigma U h) P := by
    refine AESub.trans (m₂ := ⨆ Φ : TestOn upperHalfPlaneOpens,
      MeasurableSpace.comap (fun ω => (h ω - G (h ω)) Φ) inferInstance) ?_ (aeSub_iSup hpair)
    refine aeSub_of_le (Measurable.comap_le ?_)
    refine (@measurable_distOn_iff upperHalfPlaneOpens Ω (⨆ Φ : TestOn upperHalfPlaneOpens,
      MeasurableSpace.comap (fun ω => (h ω - G (h ω)) Φ) inferInstance) _).2 fun Φ => ?_
    exact (comap_measurable (fun ω => (h ω - G (h ω)) Φ)).mono (le_iSup (fun Φ :
      TestOn upperHalfPlaneOpens => MeasurableSpace.comap (fun ω => (h ω - G (h ω)) Φ)
        inferInstance) Φ) le_rfl
  have hV' : AESub (complSigma h hV) (complSigma h fun ω => G (h ω)) P := by
    refine aeSub_comap (comap_measurable fun ω => h ω - G (h ω)) ?_
    filter_upwards [hVG] with ω hω
    rw [hω]
  rintro E ⟨E₁, hE₁, hEE₁⟩
  obtain ⟨E₂, hE₂, hE₁E₂⟩ := (hV'.trans hG') E₁ hE₁
  exact ⟨E₂, hE₂, hEE₁.trans hE₁E₂⟩

/-- **Proposition 3.2 on `ℍ`** (completed σ-algebras): for `K ⊆ ℍ` closed in `ℍ` such that `ℍ ∖ K`
is relatively compact in `ℍ` (in particular every cover value of §3.2, which contains a
neighbourhood of `∂ℍ` and of `∞`), and any Markov decomposition `h = h_V + (h − h_V)` along
`V = ℍ ∖ K`, the σ-algebra of the projection `h − h_V` onto `H^⊥(ℍ ∖ K)` is the intersection of the
σ-algebras `σ(h|_U)` over all open `U ⊆ ℍ` containing `K`. -/
theorem aeClosure_complSigma_eq_iInf_aeClosure_restrictSigma_of_isCompact {K : Set ℂ}
    (hK : IsOpen ((upperHalfPlaneOpens : Set ℂ) \ K)) (hKD : K ⊆ upperHalfPlaneOpens)
    (hKc : IsCompact (closure ((upperHalfPlaneOpens : Set ℂ) \ K)))
    (hKH : closure ((upperHalfPlaneOpens : Set ℂ) \ K) ⊆ upperHalfPlaneOpens)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {hV : Ω → DistOn upperHalfPlaneOpens}
    (hd : IsMarkovDecomposition ⟨(upperHalfPlaneOpens : Set ℂ) \ K, hK⟩ upperHalfPlaneOpens h
      hV P) :
    aeClosure (complSigma h hV) P =
      ⨅ (U : Opens ℂ) (_ : U ≤ upperHalfPlaneOpens) (_ : K ⊆ U), aeClosure (restrictSigma U h) P :=
  le_antisymm (le_iInf₂ fun _U hU => le_iInf fun hKU =>
      aeClosure_complSigma_le_aeClosure_restrictSigma_of_isCompact hK hKc hKH hh hd hU hKU)
    (iInf_aeClosure_restrictSigma_le_aeClosure_complSigma hK hKD
      (zbAdmissible_of_subset_H subset_rfl) hh.measurable hd)

/-- **Proposition 3.2 on `ℍ` for `K = ℍ ∖ W`**, `W ⊆ ℍ` open with compact closure in `ℍ` (the
form of the cover values of §3.2, e.g. `LocalSets.coverCompl`): `σ(h − h_W)` is the intersection
of the σ-algebras `σ(h|_U)` over all open `U ⊆ ℍ` containing `ℍ ∖ W` (completed σ-algebras). -/
theorem aeClosure_complSigma_eq_iInf_aeClosure_restrictSigma_of_isCompact_closure
    {W : Opens ℂ} (hWc : IsCompact (closure (W : Set ℂ)))
    (hWH : closure (W : Set ℂ) ⊆ upperHalfPlaneOpens)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {hV : Ω → DistOn upperHalfPlaneOpens}
    (hd : IsMarkovDecomposition W upperHalfPlaneOpens h hV P) :
    aeClosure (complSigma h hV) P =
      ⨅ (U : Opens ℂ) (_ : U ≤ upperHalfPlaneOpens)
        (_ : (upperHalfPlaneOpens : Set ℂ) \ W ⊆ U), aeClosure (restrictSigma U h) P := by
  have hW : (W : Set ℂ) ⊆ upperHalfPlaneOpens := subset_closure.trans hWH
  have he : (upperHalfPlaneOpens : Set ℂ) \ ((upperHalfPlaneOpens : Set ℂ) \ W) = W :=
    sdiff_sdiff_cancel_left hW
  have hK : IsOpen ((upperHalfPlaneOpens : Set ℂ) \ ((upperHalfPlaneOpens : Set ℂ) \ W)) :=
    by rw [he]; exact W.isOpen
  have hWeq : (⟨_, hK⟩ : Opens ℂ) = W := Opens.ext he
  rw [← hWeq] at hd
  exact aeClosure_complSigma_eq_iInf_aeClosure_restrictSigma_of_isCompact hK sdiff_subset
    (by rw [he]; exact hWc) (by rw [he]; exact hWH) hh hd

end UpperHalfPlane

end GFF
end InteractingSLE
