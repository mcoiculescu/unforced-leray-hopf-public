import UnforcedLeray.Units.B0220
import UnforcedLeray.Lib.Axisymmetric.RingChart

/-!
# B0226, part 1: test functions and the two solenoidal subspaces

Blueprint unit B0226, `paper/main.tex` lines 3394–3402 (§`sec:st18-2436`), on the spaces of
B0220 (lines 3279–3314): `H = L²(s^{-3/2} ds dq dη)` on one `q`-cell (`HSpace c Merid`) and
`L²(dx dτ)` over one `τ` period `2εc` (`PhysL2 ε c`).

* Physical side (`ℝ³ × period`). Tests are smooth functions `φ(x,τ)`, `2εc`-periodic in `τ`,
  vanishing for large `|x|` (`IsPhysTest`). Their `x`-gradients `∇ₓφ` (`gradX`) lie in
  `L²(dx dτ)` (`physGrad`). The divergence-free subspace is the orthogonal complement of these
  gradients (`physSolenoidal`): `V` lies in it iff `∫∫ V · ∇ₓφ dx dτ = 0` for every test
  (`mem_physSolenoidal_iff`), i.e. `div_x V = 0` in the sense of distributions on
  `ℝ³ × period`; `⟪v, ∇ₓφ⟫` is the library pairing `∑ᵢ vᵢ ∂ᵢφ` (`inner_gradX_eq_sum`).
  `P3D` is the orthogonal projection onto it, the `L²` Leray projection on `ℝ³ × period`
  (the library's `Leray.projection`, `lean/UnforcedLeray/Analysis/LerayProjection/Basic.lean`,
  is the same construction on `ℝ³` without the period variable).
* Profile side (the cylinder `s > 0`, `q ∈ ℝ/cℤ`, `η ∈ ℝ`). Tests are smooth `Φ(s,q,η)`,
  `c`-periodic in `q`, supported in a band `s₀ ≤ s ≤ s₁`, `|η| ≤ L` with `s₀ > 0`
  (`IsProfileTest`). With `K = 2s∂_s + η∂_η` (tex line 3330; `Kop`) and `D_ε = ∂_q − εK`
  (tex line 3400; `Deps`), the profile gradient is `(D_εΦ, ∂_ηΦ)` (`profileGrad`), an element
  of `H` (`profileGradH`). The exact solenoidal subspace `{D_ε b_r + ∂_η b_z = 0}` is its
  orthogonal complement in `H` (`solenoidalH`): `b` lies in it iff
  `∫ s^{-3/2} (b_r D_εΦ + b_z ∂_ηΦ) ds dq dη = 0` for all tests (`mem_solenoidalH_iff`).
  The Lebesgue-pairing form of the same distributional equation is in `B0226/Distrib.lean`.
* `P0 c` is the flat cylinder Leray projection on `(b_r, b_z)`: the orthogonal projection of
  `H` onto `{∂_q b_r + ∂_η b_z = 0}`, i.e. `solenoidalH` at `ε = 0` (`Deps_zero`). Since the
  weight `s^{-3/2}` depends on `s` only, this is the flat `(q,η)` Leray projection acting at each
  age `s`; its identification with the Fourier multiplier is not used here.

Profile partial derivatives are `Axi.dS`, `Axi.dQ`, `Axi.dEta`

`Profile = ℝ × ℝ × ℝ` ordered `(s, q, η)` as in B0220.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Filter
open scoped ENNReal Topology InnerProductSpace

namespace UnforcedLeray.B0226

open UnforcedLeray.B0220

/-! ### A bounded-support `L^p` criterion -/

/-- A continuous function vanishing (a.e.) off a compact set of finite measure is in `L^p`. -/
theorem memLp_of_continuous_of_ae_vanish {X E : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [NormedAddCommGroup E]
    [SecondCountableTopologyEither X E] {μ : Measure X} {f : X → E} (hf : Continuous f)
    {A : Set X} (hA : IsCompact A) (hμA : μ A ≠ ∞) (h0 : ∀ᵐ x ∂μ, x ∉ A → f x = 0)
    (p : ℝ≥0∞) : MemLp f p μ := by
  have hAm : MeasurableSet A := hA.isClosed.measurableSet
  have hind : A.indicator f =ᵐ[μ] f := by
    filter_upwards [h0] with x hx
    by_cases hxA : x ∈ A
    · simp [hxA]
    · simp [hxA, hx hxA]
  refine MemLp.ae_eq hind ?_
  rw [memLp_indicator_iff_restrict hAm]
  have : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.2 hμA
  obtain ⟨C, hC⟩ := hA.exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C ((ae_restrict_iff' hAm).2 (ae_of_all _ hC))

/-! ### Physical tests and the Leray projection on `ℝ³ × period` -/

/-- Test functions of `ℝ³ × period`: smooth, `P`-periodic in `τ`, and vanishing for large `|x|`.
With `P = 2εc` these are the smooth test functions of `ℝ³ × (ℝ/Pℤ)` (tex lines 3289–3290,
3394). -/
structure IsPhysTest (P : ℝ) (φ : Space × ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ
  periodic : ∀ (x : Space) (τ : ℝ), φ (x, τ + P) = φ (x, τ)
  bounded : ∃ R : ℝ, ∀ y : Space × ℝ, φ y ≠ 0 → ‖y.1‖ ≤ R

/-- The physical tests for the period `2εc`. -/
abbrev PhysTest (ε c : ℝ) := {φ : Space × ℝ → ℝ // IsPhysTest (2 * ε * c) φ}

/-- The spatial gradient `∇ₓφ(x,τ)`: the Riesz vector of `v ↦ Dφ(x,τ)(v, 0)`. -/
def gradX (φ : Space × ℝ → ℝ) (y : Space × ℝ) : Space :=
  (InnerProductSpace.toDual ℝ Space).symm
    ((fderiv ℝ φ y).comp (ContinuousLinearMap.inl ℝ Space ℝ))

theorem inner_gradX (φ : Space × ℝ → ℝ) (y : Space × ℝ) (w : Space) :
    ⟪gradX φ y, w⟫_ℝ = fderiv ℝ φ y (w, 0) := by
  rw [gradX, InnerProductSpace.toDual_symm_apply]
  rfl

/-- `⟪v, ∇ₓφ⟫ = ∑ᵢ vᵢ ∂ᵢφ(·,τ)`: the pairing of `Statement.IsSolenoidal` at each time. -/
theorem inner_gradX_eq_sum {φ : Space × ℝ → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (v : Space)
    (y : Space × ℝ) :
    ⟪v, gradX φ y⟫_ℝ = ∑ i : Fin 3, v i * spatialTestDerivative i (fun x => φ (x, y.2)) y.1 := by
  have hd : HasFDerivAt (fun x => φ (x, y.2))
      ((fderiv ℝ φ y).comp (ContinuousLinearMap.inl ℝ Space ℝ)) y.1 :=
    ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp y.1
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) y.1 y.2)
  simp only [spatialTestDerivative, hd.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply]
  rw [real_inner_comm, inner_gradX]
  have hv : ((v, 0) : Space × ℝ) = ∑ i : Fin 3, v i • ((coordinateVector i, 0) : Space × ℝ) := by
    ext j
    · simp only [Prod.fst_sum, Prod.smul_fst, coordinateVector]
      rw [Fin.sum_univ_three]
      fin_cases j <;> simp
    · simp [Prod.snd_sum]
  rw [hv, map_sum]
  simp only [map_smul, smul_eq_mul]

theorem continuous_gradX {φ : Space × ℝ → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) : Continuous (gradX φ) :=
  (InnerProductSpace.toDual ℝ Space).symm.continuous.comp
    ((hφ.continuous_fderiv (by simp)).clm_comp continuous_const)

theorem gradX_eq_zero_of_notMem {φ : Space × ℝ → ℝ} {y : Space × ℝ} (hy : y ∉ tsupport φ) :
    gradX φ y = 0 := by
  simp [gradX, fderiv_of_notMem_tsupport ℝ hy]

theorem tsupport_subset_of_bound {φ : Space × ℝ → ℝ} {R : ℝ}
    (hR : ∀ y : Space × ℝ, φ y ≠ 0 → ‖y.1‖ ≤ R) :
    tsupport φ ⊆ {y : Space × ℝ | ‖y.1‖ ≤ R} :=
  closure_minimal (fun y hy => hR y hy)
    (isClosed_le (continuous_norm.comp continuous_fst) continuous_const)

theorem memLp_gradX {ε c : ℝ} {φ : Space × ℝ → ℝ} (hφ : IsPhysTest (2 * ε * c) φ) :
    MemLp (gradX φ) 2 (physMeasure ε c) := by
  obtain ⟨R, hR⟩ := hφ.bounded
  have hA : IsCompact (Metric.closedBall (0 : Space) R ×ˢ Icc 0 (2 * ε * c)) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  refine memLp_of_continuous_of_ae_vanish (continuous_gradX hφ.smooth) hA ?_ ?_ 2
  · exact ((Measure.restrict_apply_le _ _).trans_lt (hA.measure_lt_top (μ := volume))).ne
  · filter_upwards [ae_physMeasure ε c] with y hy hyA
    refine gradX_eq_zero_of_notMem fun hmem => hyA ⟨?_, Ioc_subset_Icc_self hy.2⟩
    exact mem_closedBall_zero_iff.2 (tsupport_subset_of_bound hR hmem)

/-- `∇ₓφ` as an element of `L²(dx dτ)` over one period. -/
def physGrad (ε c : ℝ) (φ : PhysTest ε c) : PhysL2 ε c := (memLp_gradX φ.2).toLp _

theorem coeFn_physGrad (ε c : ℝ) (φ : PhysTest ε c) :
    physGrad ε c φ =ᵐ[physMeasure ε c] gradX φ.1 :=
  MemLp.coeFn_toLp _

theorem inner_physGrad {ε c : ℝ} (V : PhysL2 ε c) (φ : PhysTest ε c) :
    ⟪V, physGrad ε c φ⟫_ℝ = ∫ y, ⟪V y, gradX φ.1 y⟫_ℝ ∂physMeasure ε c := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_physGrad ε c φ] with y hy
  rw [hy]

/-- The distributionally divergence-free fields of `L²(dx dτ)` over one period: the orthogonal
complement of all test gradients `∇ₓφ`. -/
def physSolenoidal (ε c : ℝ) : Submodule ℝ (PhysL2 ε c) :=
  (Submodule.span ℝ (Set.range (physGrad ε c)))ᗮ

instance (ε c : ℝ) : CompleteSpace (physSolenoidal ε c) :=
  (Submodule.isClosed_orthogonal _).completeSpace_coe

theorem mem_orthogonal_span_range {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : ι → E) (v : E) : v ∈ (Submodule.span ℝ (Set.range g))ᗮ ↔ ∀ i, ⟪v, g i⟫_ℝ = 0 := by
  constructor
  · intro h i
    exact (Submodule.mem_orthogonal' _ v).1 h _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro h
    refine (Submodule.mem_orthogonal _ v).2 fun u hu => ?_
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [real_inner_comm]
      exact h i
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

/-- `div_x V = 0` against every test of `ℝ³ × period`. -/
theorem mem_physSolenoidal_iff {ε c : ℝ} (V : PhysL2 ε c) :
    V ∈ physSolenoidal ε c ↔
      ∀ φ : PhysTest ε c, ∫ y, ⟪V y, gradX φ.1 y⟫_ℝ ∂physMeasure ε c = 0 := by
  rw [physSolenoidal, mem_orthogonal_span_range]
  simp only [inner_physGrad]

theorem physGrad_mem_orthogonal {ε c : ℝ} (φ : PhysTest ε c) :
    physGrad ε c φ ∈ (physSolenoidal ε c)ᗮ :=
  Submodule.le_orthogonal_orthogonal _ (Submodule.subset_span ⟨φ, rfl⟩)

/-- `P_3D`: the `L²` Leray projection on `ℝ³ × period`, the orthogonal projection onto the
divergence-free fields (tex line 3396). -/
def P3D (ε c : ℝ) : PhysL2 ε c →L[ℝ] PhysL2 ε c := (physSolenoidal ε c).starProjection

theorem P3D_mem {ε c : ℝ} (V : PhysL2 ε c) : P3D ε c V ∈ physSolenoidal ε c :=
  Submodule.starProjection_apply_mem _ V

theorem P3D_eq_self_iff {ε c : ℝ} (V : PhysL2 ε c) : P3D ε c V = V ↔ V ∈ physSolenoidal ε c :=
  Submodule.starProjection_eq_self_iff

theorem norm_P3D_le (ε c : ℝ) : ‖P3D ε c‖ ≤ 1 := Submodule.starProjection_norm_le _

/-! ### Profile tests and the operators `K`, `D_ε` -/

/-- `K Φ = 2s ∂_sΦ + η ∂_ηΦ` (tex line 3330). -/
def Kop (Φ : Profile → ℝ) (p : Profile) : ℝ := 2 * p.1 * Axi.dS Φ p + p.2.2 * Axi.dEta Φ p

/-- `D_ε Φ = ∂_qΦ − ε KΦ` (tex line 3400). -/
def Deps (ε : ℝ) (Φ : Profile → ℝ) (p : Profile) : ℝ := Axi.dQ Φ p - ε * Kop Φ p

theorem Deps_zero (Φ : Profile → ℝ) : Deps 0 Φ = Axi.dQ Φ := by
  funext p
  simp [Deps]

/-- The profile gradient `(D_εΦ, ∂_ηΦ)`, components in `(e_r, e_z)`. -/
def profileGrad (ε : ℝ) (Φ : Profile → ℝ) (p : Profile) : Merid :=
  Deps ε Φ p • EuclideanSpace.single 0 1 + Axi.dEta Φ p • EuclideanSpace.single 1 1

@[simp] theorem profileGrad_zero (ε : ℝ) (Φ : Profile → ℝ) (p : Profile) :
    profileGrad ε Φ p 0 = Deps ε Φ p := by
  simp [profileGrad]

@[simp] theorem profileGrad_one (ε : ℝ) (Φ : Profile → ℝ) (p : Profile) :
    profileGrad ε Φ p 1 = Axi.dEta Φ p := by
  simp [profileGrad]

theorem inner_profileGrad (ε : ℝ) (Φ : Profile → ℝ) (p : Profile) (v : Merid) :
    ⟪v, profileGrad ε Φ p⟫_ℝ = v 0 * Deps ε Φ p + v 1 * Axi.dEta Φ p := by
  simp only [profileGrad, inner_add_right, inner_smul_right, EuclideanSpace.inner_single_right,
    one_mul]
  simp only [conj_trivial]
  ring

/-- Test functions of the cylinder: smooth, `c`-periodic in `q`, supported in a band
`s₀ ≤ s ≤ s₁`, `|η| ≤ L` with `s₀ > 0`. These are the smooth compactly supported functions of
`(0,∞) × (ℝ/cℤ) × ℝ`. -/
structure IsProfileTest (c : ℝ) (Φ : Profile → ℝ) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ
  periodic : QPeriodic c Φ
  band : ∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p : Profile, Φ p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L

/-- The profile tests for the cell `(0, c]`. -/
abbrev ProfileTest (c : ℝ) := {Φ : Profile → ℝ // IsProfileTest c Φ}

theorem tsupport_subset_band {Φ : Profile → ℝ} {s0 s1 L : ℝ}
    (h : ∀ p : Profile, Φ p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) :
    tsupport Φ ⊆ {p : Profile | p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L} :=
  closure_minimal (fun p hp => h p hp)
    ((isClosed_Icc.preimage continuous_fst).inter
      (isClosed_le (continuous_abs.comp (continuous_snd.comp continuous_snd)) continuous_const))

theorem profileGrad_eq_zero_of_notMem {ε : ℝ} {Φ : Profile → ℝ} {p : Profile}
    (hp : p ∉ tsupport Φ) : profileGrad ε Φ p = 0 := by
  have h := fderiv_of_notMem_tsupport ℝ hp
  simp [profileGrad, Deps, Kop, Axi.dS, Axi.dQ, Axi.dEta, h]

theorem continuous_profileGrad (ε : ℝ) {Φ : Profile → ℝ} (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) :
    Continuous (profileGrad ε Φ) := by
  have hD : Continuous fun p => fderiv ℝ Φ p := hΦ.continuous_fderiv (by simp)
  have h1 : ∀ v : Profile, Continuous fun p => fderiv ℝ Φ p v := fun v =>
    hD.clm_apply continuous_const
  unfold profileGrad Deps Kop Axi.dS Axi.dQ Axi.dEta
  fun_prop

theorem measureH_band_ne_top (c : ℝ) {s0 : ℝ} (hs0 : 0 < s0) (s1 L : ℝ) :
    measureH c (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L)) ≠ ∞ := by
  set A : Set Profile := Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L) with hAdef
  have hA : IsCompact A := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  rw [measureH, withDensity_apply _ hA.measurableSet]
  refine (lt_of_le_of_lt (setLIntegral_mono (measurable_const (a := ENNReal.ofReal
    (s0 ^ (-(3 / 2 : ℝ))))) fun p hp => ?_) ?_).ne
  · exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hs0 hp.1.1 (by norm_num))
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ((Measure.restrict_apply_le _ _).trans_lt (hA.measure_lt_top (μ := volume)))

theorem memLp_profileGrad {c : ℝ} (ε : ℝ) {Φ : Profile → ℝ} (hΦ : IsProfileTest c Φ) :
    MemLp (profileGrad ε Φ) 2 (measureH c) := by
  obtain ⟨s0, s1, L, hs0, hb⟩ := hΦ.band
  have hA : IsCompact (Icc s0 s1 ×ˢ (Icc 0 c ×ˢ Icc (-L) L)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  refine memLp_of_continuous_of_ae_vanish (continuous_profileGrad ε hΦ.smooth) hA
    (measureH_band_ne_top c hs0 s1 L) ?_ 2
  filter_upwards [ae_cell_measureH c] with p hp hpA
  refine profileGrad_eq_zero_of_notMem fun hmem => hpA ?_
  obtain ⟨h1, h2⟩ := tsupport_subset_band hb hmem
  exact ⟨h1, Ioc_subset_Icc_self hp.2.1, abs_le.1 h2⟩

/-- `(D_εΦ, ∂_ηΦ)` as an element of `H`. -/
def profileGradH (ε c : ℝ) (Φ : ProfileTest c) : HSpace c Merid :=
  (memLp_profileGrad ε Φ.2).toLp _

theorem coeFn_profileGradH (ε c : ℝ) (Φ : ProfileTest c) :
    profileGradH ε c Φ =ᵐ[measureH c] profileGrad ε Φ.1 :=
  MemLp.coeFn_toLp _

theorem inner_profileGradH {ε c : ℝ} (b : HSpace c Merid) (Φ : ProfileTest c) :
    ⟪b, profileGradH ε c Φ⟫_ℝ =
      ∫ p, (b p 0 * Deps ε Φ.1 p + b p 1 * Axi.dEta Φ.1 p) ∂measureH c := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_profileGradH ε c Φ] with p hp
  rw [hp, inner_profileGrad]

/-- The exact solenoidal subspace `{b ∈ H : D_ε b_r + ∂_η b_z = 0}` (tex lines 3398–3400), in
the weak form dual to `H`: `b ⟂_H (D_εΦ, ∂_ηΦ)` for every profile test `Φ`. -/
def solenoidalH (ε c : ℝ) : Submodule ℝ (HSpace c Merid) :=
  (Submodule.span ℝ (Set.range (profileGradH ε c)))ᗮ

/-- `b ∈ solenoidalH ε c` iff `∫ s^{-3/2} (b_r D_εΦ + b_z ∂_ηΦ) ds dq dη = 0` for every test. -/
theorem mem_solenoidalH_iff {ε c : ℝ} (b : HSpace c Merid) :
    b ∈ solenoidalH ε c ↔
      ∀ Φ : ProfileTest c, ∫ p, (b p 0 * Deps ε Φ.1 p + b p 1 * Axi.dEta Φ.1 p) ∂measureH c = 0 := by
  rw [solenoidalH, mem_orthogonal_span_range]
  simp only [inner_profileGradH]

instance (ε c : ℝ) : CompleteSpace (solenoidalH ε c) :=
  (Submodule.isClosed_orthogonal _).completeSpace_coe

theorem profileGradH_mem_orthogonal {ε c : ℝ} (Φ : ProfileTest c) :
    profileGradH ε c Φ ∈ (solenoidalH ε c)ᗮ :=
  Submodule.le_orthogonal_orthogonal _ (Submodule.subset_span ⟨Φ, rfl⟩)

/-- `P_0`: the flat cylinder Leray projection on `(b_r, b_z)` (tex lines 3396–3397), the
orthogonal projection of `H` onto `{∂_q b_r + ∂_η b_z = 0}`, i.e. `solenoidalH` at `ε = 0`. -/
def P0 (c : ℝ) : HSpace c Merid →L[ℝ] HSpace c Merid := (solenoidalH 0 c).starProjection

/-- The constraint of `P_0` is `∂_q b_r + ∂_η b_z = 0`. -/
theorem mem_range_P0_iff {c : ℝ} (b : HSpace c Merid) :
    P0 c b = b ↔
      ∀ Φ : ProfileTest c, ∫ p, (b p 0 * Axi.dQ Φ.1 p + b p 1 * Axi.dEta Φ.1 p) ∂measureH c = 0 := by
  rw [P0, Submodule.starProjection_eq_self_iff, mem_solenoidalH_iff]
  simp only [Deps_zero]

theorem norm_P0_le (c : ℝ) : ‖P0 c‖ ≤ 1 := Submodule.starProjection_norm_le _

end UnforcedLeray.B0226
