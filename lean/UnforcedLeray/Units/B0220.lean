import UnforcedLeray.Units.B0220.Frame
import UnforcedLeray.Units.B0220.WeightedComp

/-!
# B0220: exact outer lift, force normalization, Hilbert spaces and the unitary `J_ε`

Blueprint unit B0220 (label `eq:st18-t00113`), `paper/main.tex` lines 3279–3314
(§`sec:st18-2288`). Fix `c > 0`, `ε > 0`. In outer Cartesian coordinates
`x = (r cos φ, r sin φ, z)` put `a = 1/r`, `s = r⁻²`, `q = ε⁻¹ log r + τ/(2ε)`, `η = z/(εr)`
(`liftA`, `ageS`, `cellQ`, `etaCoord`, file `B0220/Chart.lean`). A `c`-periodic profile `b`
lifts to the `2εc`-periodic field `U = a b(s,q,η)` and a source `g` to `F = a³ g(s,q,η)`
(`fieldU`, `fieldF`, components in `(e_r, e_z)`; `liftU`, `liftF` componentwise; file
`B0220/Frame.lean`).

Contents, in the order of the manuscript:

* the `L²` identities `‖U‖² = 2πε² ∫ s^{-3/2}|b|²`, `‖F‖² = 2πε² ∫ s^{1/2}|g|²`
  (tex lines 3295–3304): `lintegral_fieldU`, `lintegral_fieldF` (and `lintegral_liftU`,
  `lintegral_liftF`), restated here as `l2_identity_U`, `l2_identity_F`;
* `H = L²(s^{-3/2} ds dq dη)`, `H_g = L²(s^{1/2} ds dq dη)` (tex lines 3305–3308):
  `HSpace`, `HgSpace`;
* `M_s g = s g` is an isometry `H_g → H` (tex line 3309): `Ms`; it is onto (`MsEquiv`);
* the rescaled lift `J_ε = (√(2π) ε)⁻¹ · (b ↦ U)` (tex lines 3309–3311): `J`, with
  `coeFn_J`; the rescaled source lift is `J_ε ∘ M_s` (`JF`, `coeFn_JF`), which fixes both the
  source and the output weights (tex line 3311);
* unitarity: `J_ε` is a unitary map of `H` onto the axisymmetric meridional (no swirl)
  fields `B_r(r,z,τ) e_r + B_z(r,z,τ) e_z` of `L²(dx dτ)` (`range_J`, `Jequiv`). The
  manuscript says "unitary"; its range is exactly this subspace and not all of `L²(dx dτ)`
  (blueprint note on B0220);
* on a compact age band `[s₀, S₁]` the `H` and `H_g` norms are equivalent to the unweighted
  cylinder norm `L²(ds dq dη)` with constants `S₁^{-3/2}, s₀^{-3/2}` and `s₀^{1/2}, S₁^{1/2}`
  (tex lines 3311–3313): `band_equiv_H`, `band_equiv_Hg`.

The `q`-measure is the unnormalized `dq` on one cell `(0, c]`, as in the manuscript at these
lines. Elements of `H` are functions on the cell; the lift uses their `c`-periodic extension
(`periodize`), equivalently the chart with `q` reduced into the cell (`cellChart`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real
open scoped ENNReal

namespace UnforcedLeray.B0220

/-! ### The `L²` identities (tex lines 3295–3304) -/

/-- `‖U‖²_{L²(dx dτ)} = 2πε² ∫ s^{-3/2} |b|² ds dq dη`, integrating over one full `τ` period,
the physical azimuth and one `q`-cell (tex lines 3295–3300), for the meridional lift
`U = a (b_r e_r + b_z e_z)` of a measurable `c`-periodic profile. -/
theorem l2_identity_U {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (b : Profile → Merid)
    (hb : Measurable b) (hper : QPeriodic c b) :
    ∫⁻ y, ‖fieldU ε b y‖ₑ ^ 2 ∂physMeasure ε c =
      ENNReal.ofReal (2 * π * ε ^ 2) *
        ∫⁻ p in cell c, ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) * ‖b p‖ₑ ^ 2 :=
  lintegral_fieldU hε hc b hb hper

/-- `‖F‖²_{L²(dx dτ)} = 2πε² ∫ s^{1/2} |g|² ds dq dη` (tex lines 3301–3303), for the
meridional source lift `F = a³ (g_r e_r + g_z e_z)`. -/
theorem l2_identity_F {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (g : Profile → Merid)
    (hg : Measurable g) (hper : QPeriodic c g) :
    ∫⁻ y, ‖fieldF ε g y‖ₑ ^ 2 ∂physMeasure ε c =
      ENNReal.ofReal (2 * π * ε ^ 2) *
        ∫⁻ p in cell c, ENNReal.ofReal (p.1 ^ (1 / 2 : ℝ)) * ‖g p‖ₑ ^ 2 :=
  lintegral_fieldF hε hc g hg hper

/-! ### The Hilbert spaces `H` and `H_g` (tex lines 3305–3308) -/

/-- `H = L²(s^{-3/2} ds dq dη)` on one cell, with values in `E` (tex line 3307). -/
abbrev HSpace (c : ℝ) (E : Type*) [NormedAddCommGroup E] := Lp E 2 (measureH c)

/-- `H_g = L²(s^{1/2} ds dq dη)` on one cell, with values in `E` (tex line 3308). -/
abbrev HgSpace (c : ℝ) (E : Type*) [NormedAddCommGroup E] := Lp E 2 (measureHg c)

/-- `L²(dx dτ)` of physical vector fields over one `τ` period `(0, 2εc]`. -/
abbrev PhysL2 (ε c : ℝ) := Lp Space 2 (physMeasure ε c)

theorem ae_cell_measureH (c : ℝ) : ∀ᵐ p ∂measureH c, p ∈ cell c :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem (measurableSet_cell c))

theorem ae_cell_measureHg (c : ℝ) : ∀ᵐ p ∂measureHg c, p ∈ cell c :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem (measurableSet_cell c))

/-! ### The multiplication `M_s : H_g → H` (tex line 3309) -/

section Ms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

theorem measureH_withDensity_sq (c : ℝ) :
    (measureH c).withDensity (fun p => ENNReal.ofReal (|p.1| ^ 2)) = measureHg c := by
  have hm : Measurable fun p : Profile => ENNReal.ofReal (|p.1| ^ 2) :=
    ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp measurable_fst).pow_const 2)
  rw [measureH, ← withDensity_mul _ measurable_weightH hm, measureHg, cellMeasure]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_cell c)] with p hp
  have hs : 0 < p.1 := hp.1
  simp only [Pi.mul_apply, weightH, weightHg, sq_abs]
  exact weight_mul_sq hs

theorem measureHg_withDensity_inv_sq (c : ℝ) :
    (measureHg c).withDensity (fun p => ENNReal.ofReal (|p.1⁻¹| ^ 2)) = measureH c := by
  have hm : Measurable fun p : Profile => ENNReal.ofReal (|p.1⁻¹| ^ 2) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_abs.measurable.comp measurable_fst.inv).pow_const 2)
  rw [measureHg, ← withDensity_mul _ measurable_weightHg hm, measureH, cellMeasure]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_cell c)] with p hp
  have hs : 0 < p.1 := hp.1
  simp only [Pi.mul_apply, weightH, weightHg, sq_abs]
  rw [← ENNReal.ofReal_mul (by positivity), inv_pow, ← Real.rpow_two, ← Real.rpow_neg hs.le,
    ← Real.rpow_add hs]
  norm_num

/-- `M_s g = s g` as a weighted composition `H_g → H`. -/
def msComp (c : ℝ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] : WeightedComp (measureH c) (measureHg c) E E where
  T := id
  L p := p.1 • LinearMap.id
  ρ p := |p.1|
  measurable_T := measurable_id
  measurable_ρ := continuous_abs.measurable.comp measurable_fst
  measurable_L := by
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    exact (measurable_fst.comp measurable_fst).smul measurable_snd
  nonneg_ρ _ := abs_nonneg _
  norm_L p v := by simp [norm_smul]
  map_eq := by rw [Measure.map_id]; exact measureH_withDensity_sq c

/-- `M_s⁻¹ f = s⁻¹ f` as a weighted composition `H → H_g`. -/
def msInvComp (c : ℝ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] : WeightedComp (measureHg c) (measureH c) E E where
  T := id
  L p := p.1⁻¹ • LinearMap.id
  ρ p := |p.1⁻¹|
  measurable_T := measurable_id
  measurable_ρ := continuous_abs.measurable.comp measurable_fst.inv
  measurable_L := by
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    exact (measurable_fst.comp measurable_fst).inv.smul measurable_snd
  nonneg_ρ _ := abs_nonneg _
  norm_L p v := by simp [norm_smul]
  map_eq := by rw [Measure.map_id]; exact measureHg_withDensity_inv_sq c

/-- Multiplication `M_s g = s g` is an isometry `H_g → H` (tex line 3309). -/
def Ms (c : ℝ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] : HgSpace c E →ₗᵢ[ℝ] HSpace c E :=
  (msComp c E).toLI

theorem coeFn_Ms (c : ℝ) (g : HgSpace c E) : Ms c E g =ᵐ[measureH c] fun p => p.1 • g p := by
  filter_upwards [(msComp c E).coeFn_toLI g] with p hp
  rw [Ms, hp]
  simp [WeightedComp.compFun, msComp]

/-- `‖M_s g‖_H = ‖g‖_{H_g}` (tex line 3309). -/
theorem norm_Ms (c : ℝ) (g : HgSpace c E) : ‖Ms c E g‖ = ‖g‖ := (Ms c E).norm_map g

theorem Ms_surjective (c : ℝ) : Function.Surjective (Ms c E) := by
  intro f
  refine ⟨(msInvComp c E).toLI f, Lp.ext ?_⟩
  have h1 := (msComp c E).ae_comp ((msInvComp c E).coeFn_toLI f)
  filter_upwards [coeFn_Ms c ((msInvComp c E).toLI f), h1, ae_cell_measureH c] with p hp hp1 hp2
  have hs : 0 < p.1 := hp2.1
  have hT : (msComp c E).T p = p := rfl
  have hρ : (msComp c E).ρ p ≠ 0 := by simp [msComp, hs.ne']
  have h := hp1 hρ
  rw [hT] at h
  rw [hp, h]
  simp [WeightedComp.compFun, msInvComp, smul_smul, hs.ne']

/-- `M_s` is a unitary map `H_g ≃ H`. -/
def MsEquiv (c : ℝ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] : HgSpace c E ≃ₗᵢ[ℝ] HSpace c E :=
  LinearIsometryEquiv.ofSurjective (Ms c E) (Ms_surjective c)

theorem MsEquiv_apply (c : ℝ) (g : HgSpace c E) : MsEquiv c E g = Ms c E g := rfl

end Ms

/-! ### The rescaled lift `J_ε` (tex lines 3309–3311) -/

/-- The common constant of the lift: `(√(2π) ε)⁻¹`, so that `(2πε²) · const² = 1`. -/
def jConst (ε : ℝ) : ℝ := (√(2 * π) * ε)⁻¹

theorem jConst_nonneg {ε : ℝ} (hε : 0 < ε) : 0 ≤ jConst ε := by
  unfold jConst; positivity

theorem jConst_sq_mul {ε : ℝ} (hε : 0 < ε) : jConst ε ^ 2 * (2 * π * ε ^ 2) = 1 := by
  unfold jConst
  rw [inv_pow, mul_pow, Real.sq_sqrt (by positivity)]
  exact inv_mul_cancel₀ (by positivity)

/-- The density `const² a²` pushes forward to `s^{-3/2} ds dq dη` on the cell. -/
theorem map_cellChart_jDensity {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ((physMeasure ε c).withDensity
        fun y => ENNReal.ofReal ((jConst ε * liftA y.1) ^ 2)).map (cellChart ε c) =
      measureH c := by
  have hd : (fun y : Space × ℝ => ENNReal.ofReal ((jConst ε * liftA y.1) ^ 2)) =
      ENNReal.ofReal (jConst ε ^ 2) • liftDensity := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, liftDensity]
    rw [← ENNReal.ofReal_mul (by positivity), mul_pow]
  rw [hd, withDensity_smul _ measurable_liftDensity, Measure.map_smul, map_cellChart hε hc,
    smul_smul, ← ENNReal.ofReal_mul (by positivity), jConst_sq_mul hε, ENNReal.ofReal_one,
    one_smul]

theorem norm_smul_frame {ε : ℝ} (hε : 0 < ε) (x : Space) (v : Merid) :
    ‖(jConst ε * liftA x) • frame x v‖ = jConst ε * liftA x * ‖v‖ := by
  rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (jConst_nonneg hε) (liftA_nonneg x))]
  by_cases hx : radius x = 0
  · simp [liftA_eq_zero hx]
  · rw [norm_frame hx]

/-- `J_ε` as a weighted composition: `b ↦ (√(2π) ε)⁻¹ a (b_r e_r + b_z e_z)`. -/
def jComp {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    WeightedComp (physMeasure ε c) (measureH c) Merid Space where
  T := cellChart ε c
  L y := (jConst ε * liftA y.1) • frame y.1
  ρ y := jConst ε * liftA y.1
  measurable_T := measurable_cellChart ε c
  measurable_ρ := (measurable_liftA.comp measurable_fst).const_mul _
  measurable_L := by
    simp only [LinearMap.smul_apply]
    exact (((measurable_liftA.comp measurable_fst).const_mul _).comp measurable_fst).smul
      (measurable_frame_uncurry measurable_fst)
  nonneg_ρ y := mul_nonneg (jConst_nonneg hε) (liftA_nonneg _)
  norm_L y v := by rw [LinearMap.smul_apply]; exact norm_smul_frame hε y.1 v
  map_eq := map_cellChart_jDensity hε hc

/-- The rescaled lift `J_ε : H → L²(dx dτ)`, an isometry (tex lines 3309–3311). -/
def J {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) : HSpace c Merid →ₗᵢ[ℝ] PhysL2 ε c :=
  (jComp hε hc).toLI

/-- `J_ε b = (√(2π) ε)⁻¹ U`, where `U = a b(s,q,η)` is the lift of the `c`-periodic extension
of `b` (tex lines 3292, 3309–3311). -/
theorem coeFn_J {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (b : HSpace c Merid) :
    J hε hc b =ᵐ[physMeasure ε c] fun y => (√(2 * π) * ε)⁻¹ • fieldU ε (periodize c b) y := by
  filter_upwards [(jComp hε hc).coeFn_toLI b] with y hy
  rw [J, hy]
  simp only [WeightedComp.compFun, jComp, LinearMap.smul_apply, fieldU, mul_smul]
  rfl

/-- `‖J_ε b‖_{L²(dx dτ)} = ‖b‖_H`. -/
theorem norm_J {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (b : HSpace c Merid) :
    ‖J hε hc b‖ = ‖b‖ := (J hε hc).norm_map b

/-- The rescaled source lift `J_ε ∘ M_s : H_g → L²(dx dτ)`. -/
def JF {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) : HgSpace c Merid →ₗᵢ[ℝ] PhysL2 ε c :=
  (J hε hc).comp (Ms c Merid)

/-- `J_ε (M_s g) = (√(2π) ε)⁻¹ F` with `F = a³ g(s,q,η)`: the same constant normalizes the
source lift `H_g → L²(dx dτ)` (tex lines 3292, 3309–3311). -/
theorem coeFn_JF {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (g : HgSpace c Merid) :
    JF hε hc g =ᵐ[physMeasure ε c] fun y => (√(2 * π) * ε)⁻¹ • fieldF ε (periodize c g) y := by
  have h1 := (jComp hε hc).coeFn_toLI (Ms c Merid g)
  have h2 := (jComp hε hc).compFun_congr (coeFn_Ms c g)
  filter_upwards [h1, h2] with y hy1 hy2
  change (jComp hε hc).toLI (Ms c Merid g) y = _
  rw [hy1, hy2]
  simp only [WeightedComp.compFun, jComp, LinearMap.smul_apply, fieldF, map_smul, smul_smul]
  have hs : (cellChart ε c y).1 = liftA y.1 ^ 2 := (liftA_sq y.1).symm
  rw [hs]
  congr 1
  · unfold jConst; ring

/-- `‖J_ε M_s g‖_{L²(dx dτ)} = ‖g‖_{H_g}`. -/
theorem norm_JF {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (g : HgSpace c Merid) :
    ‖JF hε hc g‖ = ‖g‖ := (JF hε hc).norm_map g

/-! ### Unitarity: the range of `J_ε` -/

/-- The axisymmetric meridional fields without swirl in `L²(dx dτ)`:
`V(x,τ) = B_r(r,z,τ) e_r + B_z(r,z,τ) e_z` with `B` measurable. -/
def meridionalSubspace (ε c : ℝ) : Submodule ℝ (PhysL2 ε c) where
  carrier := {V | ∃ B : ℝ × ℝ × ℝ → Merid, Measurable B ∧
    (V : Space × ℝ → Space) =ᵐ[physMeasure ε c]
      fun y => frame y.1 (B (radius y.1, y.1 2, y.2))}
  add_mem' := by
    rintro V W ⟨B, hB, hV⟩ ⟨C, hC, hW⟩
    refine ⟨B + C, hB.add hC, ?_⟩
    filter_upwards [Lp.coeFn_add V W, hV, hW] with y h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Pi.add_apply, map_add]
  zero_mem' := ⟨0, measurable_const, by
    filter_upwards [Lp.coeFn_zero (E := Space) (p := 2) (μ := physMeasure ε c)] with y hy
    rw [hy]
    simp⟩
  smul_mem' := by
    rintro r V ⟨B, hB, hV⟩
    refine ⟨r • B, hB.const_smul r, ?_⟩
    filter_upwards [Lp.coeFn_smul r V, hV] with y h1 h2
    rw [h1, Pi.smul_apply, h2, Pi.smul_apply, map_smul]

theorem measurableSet_physDomain (ε c : ℝ) : MeasurableSet (physDomain ε c) :=
  MeasurableSet.univ.prod measurableSet_Ioc

/-- Almost every point of one period is off the axis. -/
theorem ae_physMeasure (ε c : ℝ) :
    ∀ᵐ y ∂physMeasure ε c, radius y.1 ≠ 0 ∧ y.2 ∈ Ioc 0 (2 * ε * c) := by
  have h1 : ∀ᵐ y ∂physMeasure ε c, y ∈ physDomain ε c :=
    ae_restrict_mem (measurableSet_physDomain ε c)
  have h2 : ∀ᵐ y ∂(volume : Measure (Space × ℝ)), radius y.1 ≠ 0 := by
    rw [ae_iff]
    have : {y : Space × ℝ | ¬radius y.1 ≠ 0} = axis ×ˢ (univ : Set ℝ) := by
      ext y
      simp [axis]
    rw [this, Measure.volume_eq_prod, Measure.prod_prod, volume_axis, zero_mul]
  filter_upwards [h1, ae_restrict_of_ae h2] with y hy1 hy2
  exact ⟨hy2, hy1.2⟩

/-- Inverse chart: `r = s^{-1/2}`. -/
def invR (p : Profile) : ℝ := √(p.1⁻¹)

/-- Inverse chart: `z = ε r η`. -/
def invZ (ε : ℝ) (p : Profile) : ℝ := ε * invR p * p.2.2

/-- Inverse chart: `τ = 2εq + log s`, reduced into one period `(0, 2εc]`. -/
def invTau (ε c : ℝ) (p : Profile) : ℝ := reduceIoc (2 * ε * c) (2 * ε * p.2.1 + Real.log p.1)

theorem measurable_invR : Measurable invR := measurable_fst.inv.sqrt

theorem measurable_invZ (ε : ℝ) : Measurable (invZ ε) :=
  (measurable_invR.const_mul ε).mul (measurable_snd.comp measurable_snd)

theorem measurable_invTau (ε c : ℝ) : Measurable (invTau ε c) :=
  (measurable_reduceIoc _).comp
    ((measurable_const.mul (measurable_fst.comp measurable_snd)).add
      (Real.measurable_log.comp measurable_fst))

theorem invChart {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) {y : Space × ℝ} (hr : radius y.1 ≠ 0)
    (hτ : y.2 ∈ Ioc 0 (2 * ε * c)) :
    invR (cellChart ε c y) = radius y.1 ∧ invZ ε (cellChart ε c y) = y.1 2 ∧
      invTau ε c (cellChart ε c y) = y.2 := by
  have hr0 : 0 < radius y.1 := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr)
  have hR : invR (cellChart ε c y) = radius y.1 := by
    simp only [invR, cellChart, ageS, inv_inv]
    exact Real.sqrt_sq hr0.le
  refine ⟨hR, ?_, ?_⟩
  · rw [invZ, hR]
    simp only [cellChart, etaCoord]
    field_simp
  · set q := cellQ ε y.1 y.2 with hq
    have key : 2 * ε * reduceIoc c q + Real.log ((radius y.1 ^ 2)⁻¹) =
        y.2 - ((⌈q / c⌉ - 1 : ℤ) : ℝ) * (2 * ε * c) := by
      rw [reduceIoc_eq_sub, Real.log_inv, Real.log_pow, hq, cellQ]
      field_simp
      push_cast
      ring
    have hper : Function.Periodic (reduceIoc (2 * ε * c)) (2 * ε * c) :=
      fun t => reduceIoc_add (by positivity) t
    simp only [invTau, cellChart, ageS]
    rw [← hq, key, hper.sub_int_mul_eq, reduceIoc_of_mem (by positivity) hτ]

/-- `J_ε` maps `H` into, and onto, the axisymmetric meridional fields. -/
theorem range_J {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    LinearMap.range (J hε hc).toLinearMap = meridionalSubspace ε c := by
  ext V
  constructor
  · rintro ⟨b, rfl⟩
    have hbm : Measurable (b : Profile → Merid) := (Lp.stronglyMeasurable b).measurable
    refine ⟨fun w => (jConst ε * w.1⁻¹) •
      b ((w.1 ^ 2)⁻¹, reduceIoc c (ε⁻¹ * Real.log w.1 + w.2.2 / (2 * ε)), w.2.1 / (ε * w.1)),
      ?_, ?_⟩
    · refine (measurable_fst.inv.const_mul _).smul (hbm.comp ?_)
      exact ((measurable_fst.pow_const 2).inv).prodMk
        (((measurable_reduceIoc c).comp (((Real.measurable_log.comp measurable_fst).const_mul _).add
          ((measurable_snd.comp measurable_snd).div_const _))).prodMk
          ((measurable_fst.comp measurable_snd).div (measurable_fst.const_mul ε)))
    · filter_upwards [(jComp hε hc).coeFn_toLI b] with y hy
      change (jComp hε hc).toLI b y = _
      rw [hy]
      simp only [WeightedComp.compFun, jComp, LinearMap.smul_apply, map_smul]
      rfl
  · rintro ⟨B, hB, hV⟩
    set b₀ : Profile → Merid := fun p =>
      (√(2 * π) * ε * invR p) • B (invR p, invZ ε p, invTau ε c p) with hb₀
    have hb₀m : Measurable b₀ :=
      ((measurable_invR.const_mul _)).smul
        (hB.comp (measurable_invR.prodMk ((measurable_invZ ε).prodMk (measurable_invTau ε c))))
    have hpt : (jComp hε hc).compFun b₀ =ᵐ[physMeasure ε c]
        fun y => frame y.1 (B (radius y.1, y.1 2, y.2)) := by
      filter_upwards [ae_physMeasure ε c] with y ⟨hr, hτ⟩
      obtain ⟨h1, h2, h3⟩ := invChart hε hc hr hτ
      have hk : √(2 * π) * ε * radius y.1 * (jConst ε * liftA y.1) = 1 := by
        have : √(2 * π) ≠ 0 := by positivity
        simp only [jConst, liftA]
        field_simp
      simp only [WeightedComp.compFun, jComp, LinearMap.smul_apply, hb₀, h1, h2, h3, map_smul,
        smul_smul, hk, one_smul]
    have hb₀L : MemLp b₀ 2 (measureH c) :=
      ⟨hb₀m.aestronglyMeasurable, by
        rw [← (jComp hε hc).eLpNorm_compFun hb₀m, eLpNorm_congr_ae (hpt.trans hV.symm)]
        exact Lp.eLpNorm_lt_top V⟩
    refine ⟨hb₀L.toLp b₀, Lp.ext ?_⟩
    exact ((jComp hε hc).coeFn_toLI_toLp hb₀L).trans (hpt.trans hV.symm)

/-- `J_ε` is unitary from `H` onto the axisymmetric meridional (no swirl) fields of
`L²(dx dτ)` (tex lines 3309–3311). -/
def Jequiv {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) : HSpace c Merid ≃ₗᵢ[ℝ] meridionalSubspace ε c :=
  (J hε hc).equivRange.trans (LinearIsometryEquiv.ofEq _ _ (range_J hε hc))

theorem Jequiv_apply {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (b : HSpace c Merid) :
    (Jequiv hε hc b : PhysL2 ε c) = J hε hc b := rfl

/-! ### Local equivalence on a compact age band (tex lines 3311–3313) -/

/-- The age band `s ∈ [s₀, S₁]`. -/
def ageBand (s0 S1 : ℝ) : Set Profile := {p | p.1 ∈ Icc s0 S1}

theorem measurableSet_ageBand (s0 S1 : ℝ) : MeasurableSet (ageBand s0 S1) :=
  measurable_fst measurableSet_Icc

section Band

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]

theorem setLIntegral_band_withDensity {s0 S1 : ℝ} (c : ℝ) (w : Profile → ℝ≥0∞)
    (hw : Measurable w) (b : Profile → E) (hb : Measurable b) :
    ∫⁻ p in ageBand s0 S1, ‖b p‖ₑ ^ 2 ∂(cellMeasure c).withDensity w =
      ∫⁻ p in ageBand s0 S1, w p * ‖b p‖ₑ ^ 2 ∂cellMeasure c := by
  rw [restrict_withDensity (measurableSet_ageBand s0 S1),
    lintegral_withDensity_eq_lintegral_mul _ hw (hb.enorm.pow_const 2)]
  rfl

/-- On the compact age band `[s₀, S₁]`, `S₁^{-3/2} ‖b‖²_{L²} ≤ ‖b‖²_H ≤ s₀^{-3/2} ‖b‖²_{L²}`,
where `L² = L²(ds dq dη)` is the unweighted cylinder norm (tex lines 3311–3313). -/
theorem band_equiv_H {s0 S1 : ℝ} (hs0 : 0 < s0) (c : ℝ) (b : Profile → E)
    (hb : Measurable b) :
    ENNReal.ofReal (S1 ^ (-(3 / 2 : ℝ))) * ∫⁻ p in ageBand s0 S1, ‖b p‖ₑ ^ 2 ∂cellMeasure c ≤
        ∫⁻ p in ageBand s0 S1, ‖b p‖ₑ ^ 2 ∂measureH c ∧
      ∫⁻ p in ageBand s0 S1, ‖b p‖ₑ ^ 2 ∂measureH c ≤
        ENNReal.ofReal (s0 ^ (-(3 / 2 : ℝ))) *
          ∫⁻ p in ageBand s0 S1, ‖b p‖ₑ ^ 2 ∂cellMeasure c := by
  rw [measureH, setLIntegral_band_withDensity c weightH measurable_weightH b hb]
  constructor
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem (measurableSet_ageBand s0 S1)] with p hp
    have hs : 0 < p.1 := lt_of_lt_of_le hs0 hp.1
    gcongr ?_ * _
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hs hp.2 (by norm_num))
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem (measurableSet_ageBand s0 S1)] with p hp
    gcongr ?_ * _
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hs0 hp.1 (by norm_num))

/-- On the compact age band `[s₀, S₁]`, `s₀^{1/2} ‖g‖²_{L²} ≤ ‖g‖²_{H_g} ≤ S₁^{1/2} ‖g‖²_{L²}`
(tex lines 3311–3313). -/
theorem band_equiv_Hg {s0 S1 : ℝ} (hs0 : 0 < s0) (c : ℝ) (g : Profile → E)
    (hg : Measurable g) :
    ENNReal.ofReal (s0 ^ (1 / 2 : ℝ)) * ∫⁻ p in ageBand s0 S1, ‖g p‖ₑ ^ 2 ∂cellMeasure c ≤
        ∫⁻ p in ageBand s0 S1, ‖g p‖ₑ ^ 2 ∂measureHg c ∧
      ∫⁻ p in ageBand s0 S1, ‖g p‖ₑ ^ 2 ∂measureHg c ≤
        ENNReal.ofReal (S1 ^ (1 / 2 : ℝ)) *
          ∫⁻ p in ageBand s0 S1, ‖g p‖ₑ ^ 2 ∂cellMeasure c := by
  rw [measureHg, setLIntegral_band_withDensity c weightHg measurable_weightHg g hg]
  constructor
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem (measurableSet_ageBand s0 S1)] with p hp
    gcongr ?_ * _
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hs0.le hp.1 (by norm_num))
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem (measurableSet_ageBand s0 S1)] with p hp
    have hs : 0 ≤ p.1 := hs0.le.trans hp.1
    gcongr ?_ * _
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hs hp.2 (by norm_num))

end Band

end UnforcedLeray.B0220
