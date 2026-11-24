import UnforcedLeray.Units.B0008
import UnforcedLeray.Lib.PlanarSectors.NUE.Parseval
import UnforcedLeray.Lib.PlanarSectors.NUE.Symmetry

/-!
# Planar weighted space `L²_M` and its angular sectors (INF12 targets P1, P2)


§5, Level P, targets **P1** (weighted plane space) and **P2** (angular sectors on `L²_M`).
Blueprint unit `B0008` (`paper/main.tex` lines 653–660, `eq:st18-t00003`): for `M > 1` the
space `H^0_M = L²(⟨y⟩^{2M} dy)` of complex functions on `ℝ² = ℂ`, with no angular restriction,
and `𝒳_{0,M} = {f ∈ H^0_M : ∫ f = 0}`; "`M > 1` makes the integral bounded" (line 660).
The sector decomposition is the one used for G1/G2 by bypass B1 (decision D7): every
`f ∈ L²_M` is the `L²_M`-convergent sum of its angular sectors `f_n(r) e^{inϑ}`, `n ∈ ℤ`
(`paper/main.tex` line 1366 "For `w ∈ L²_M` in angular sector `n ≥ 1`", line 2027 "G1--G2
retain every angular sector", line 979 "`q̄` ... in angular sector `-2`").

Main declarations (namespace `UnforcedLeray.Planar`):
* `wMeasure M = volume.withDensity ((1 + ‖y‖²)^M)` and `L2w M = Lp ℂ 2 (wMeasure M)`
  (definitionally the measure of the drafted unit `B0008`, `wMeasure_eq_B0008`);
* `measurePreserving_rot_wMeasure`: rotations preserve the weighted measure;
* `massCLM hM : L2w M →L[ℂ] ℂ`, `f ↦ ∫_{ℝ²} f dy` (Lebesgue integral; `M > 1`), and
  `X0 hM = ker (massCLM hM)`, the space `𝒳_{0,M}`;
* `weightIso M : L2w M ≃ₗᵢ[ℂ] L²(ℂ)`, `f ↦ ⟨y⟩^M f`, which commutes with rotations;
* `sectorProjW M n : L2w M →L[ℂ] L2w M`, the sector projection
  `P_n f(x) = (2π)⁻¹ ∫₀^{2π} e^{-inφ} f(e^{iφ}x) dφ` (`coeFn_sectorProjW`), with
  `hasSum_sectorProjW` (`f = ∑ₙ P_n f` in `L²_M`), `hasSum_norm_sq_sectorProjW` (Parseval),
  `inner_sectorProjW_of_ne` (orthogonality), `inner_sectorProjW` (self-adjointness),
  `sectorProjW_comp` (`P_m P_n = δ_{mn} P_n`), and `sectorProjW_conj` (conjugation maps sector
  `n` to sector `-n`).

The unweighted sector theory on `L²(ℂ)` is the NonUniqueEuler library I-ANG, copied into
`Lib/PlanarSectors/NUE/` (namespace `UnforcedLeray.Planar.NUE`). It is transported to `L²_M`
through `weightIso`: the weight `⟨y⟩^M` is radial, so it commutes with every sector projection
(`NUE.Ang.sectorProj_radial_mul`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Planar

open UnforcedLeray.Planar.NUE

/-! ### P1: the weighted measure and the space `L²_M` -/

/-- The density `⟨y⟩^{2M} = (1 + |y|²)^M` of `L²_M` (`paper/main.tex` line 655). -/
def wDensity (M : ℝ) (y : ℂ) : ℝ≥0∞ := ENNReal.ofReal ((1 + ‖y‖ ^ 2) ^ M)

/-- The weighted measure `⟨y⟩^{2M} dy` on `ℝ² = ℂ` (`paper/main.tex` lines 653–660, blueprint
unit `B0008`). -/
def wMeasure (M : ℝ) : Measure ℂ :=
  volume.withDensity fun y => ENNReal.ofReal ((1 + ‖y‖ ^ 2) ^ M)

/-- The weighted space `H^0_M = L²(⟨y⟩^{2M} dy)` (`paper/main.tex` line 655, `j = 0`). -/
abbrev L2w (M : ℝ) : Type := Lp ℂ 2 (wMeasure M)

/-- `wMeasure` is the measure of the drafted unit `B0008`. -/
theorem wMeasure_eq_B0008 (M : ℝ) : wMeasure M = B0008.wMeasure M := rfl

theorem wMeasure_ac (M : ℝ) : wMeasure M ≪ volume := B0008.wMeasure_ac M

theorem volume_ac (M : ℝ) : (volume : Measure ℂ) ≪ wMeasure M := B0008.volume_ac M

theorem measurable_wDensity (M : ℝ) : Measurable (wDensity M) := by
  unfold wDensity
  fun_prop

theorem wDensity_rot (M θ : ℝ) (y : ℂ) : wDensity M (rot θ y) = wDensity M y := by
  simp [wDensity, Polar.norm_rot]

/-- Rotations preserve the weighted measure, since `⟨y⟩` is radial. -/
theorem measurePreserving_rot_wMeasure (M θ : ℝ) :
    MeasurePreserving (rot θ) (wMeasure M) (wMeasure M) := by
  have hm : Measurable (rot θ) := (Polar.measurePreserving_rot θ).measurable
  refine ⟨hm, ?_⟩
  ext s hs
  change Measure.map (rot θ) (volume.withDensity (wDensity M)) s =
    (volume.withDensity (wDensity M)) s
  rw [Measure.map_apply hm hs, withDensity_apply _ (hm hs), withDensity_apply _ hs,
    ← lintegral_indicator (hm hs), ← lintegral_indicator hs]
  have h : ∀ y, (rot θ ⁻¹' s).indicator (wDensity M) y = s.indicator (wDensity M) (rot θ y) := by
    intro y
    by_cases hy : rot θ y ∈ s
    · rw [indicator_of_mem (show y ∈ rot θ ⁻¹' s from hy), indicator_of_mem hy, wDensity_rot]
    · rw [indicator_of_notMem (show y ∉ rot θ ⁻¹' s from hy), indicator_of_notMem hy]
  simp_rw [h]
  exact (Polar.measurePreserving_rot θ).lintegral_comp ((measurable_wDensity M).indicator hs)

/-- The mass functional `f ↦ ∫_{ℝ²} f dy` on `L²_M`, `M > 1` (`paper/main.tex` line 660). It is
bounded because `‖f‖_{L¹} ≤ C_M ‖f‖_{L²_M}` (`B0008.integral_norm_le`). -/
def massCLM {M : ℝ} (hM : 1 < M) : L2w M →L[ℂ] ℂ := B0008.integralCLM M hM

/-- Every `f ∈ L²_M` is Lebesgue integrable for `M > 1`, so `massCLM` is the true integral. -/
theorem integrable_L2w {M : ℝ} (hM : 1 < M) (f : L2w M) : Integrable (f : ℂ → ℂ) volume :=
  B0008.integrable_L2w hM f

theorem massCLM_apply {M : ℝ} (hM : 1 < M) (f : L2w M) : massCLM hM f = ∫ y, f y :=
  B0008.integralCLM_apply hM f

/-- `𝒳_{0,M} = {f ∈ L²_M : ∫ f = 0}` (`paper/main.tex` line 656, `j = 0`). -/
abbrev X0 {M : ℝ} (hM : 1 < M) : Submodule ℂ (L2w M) :=
  LinearMap.ker (massCLM hM : L2w M →ₗ[ℂ] ℂ)

theorem mem_X0_iff {M : ℝ} (hM : 1 < M) (f : L2w M) : f ∈ X0 hM ↔ ∫ y, f y = 0 := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, massCLM_apply]

theorem isClosed_X0 {M : ℝ} (hM : 1 < M) : IsClosed (X0 hM : Set (L2w M)) :=
  ContinuousLinearMap.isClosed_ker _

/-! ### The weight isometry `f ↦ ⟨y⟩^M f` -/

/-- The multiplier `⟨y⟩^M = (1 + |y|²)^{M/2}`. -/
def wt (M : ℝ) (y : ℂ) : ℝ := B0008.bracket y ^ M

/-- The radial profile of `wt M`. -/
def wtR (M : ℝ) (r : ℝ) : ℂ := ((Real.sqrt (1 + r ^ 2) ^ M : ℝ) : ℂ)

theorem wt_pos (M : ℝ) (y : ℂ) : 0 < wt M y := Real.rpow_pos_of_pos (B0008.bracket_pos y) M

theorem wt_ne_zero (M : ℝ) (y : ℂ) : wt M y ≠ 0 := (wt_pos M y).ne'

theorem wt_eq_wtR (M : ℝ) (y : ℂ) : ((wt M y : ℝ) : ℂ) = wtR M ‖y‖ := rfl

theorem memLp_wt_smul {M : ℝ} {f : ℂ → ℂ} (hf : MemLp f 2 (wMeasure M)) :
    MemLp (fun y => wt M y • f y) 2 volume :=
  (B0008.memLp_wMeasure_iff M).1 hf

theorem memLp_wt_inv_smul {M : ℝ} {g : ℂ → ℂ} (hg : MemLp g 2 volume) :
    MemLp (fun y => (wt M y)⁻¹ • g y) 2 (wMeasure M) := by
  refine (B0008.memLp_wMeasure_iff M).2 ?_
  have h : (fun y => B0008.bracket y ^ M • (fun y => (wt M y)⁻¹ • g y) y) = g := by
    funext y
    change wt M y • ((wt M y)⁻¹ • g y) = g y
    rw [smul_smul, mul_inv_cancel₀ (wt_ne_zero M y), one_smul]
  rw [h]
  exact hg

theorem norm_toLp_wt_smul {M : ℝ} (f : L2w M) :
    ‖(memLp_wt_smul (Lp.memLp f)).toLp (fun y => wt M y • f y)‖ = ‖f‖ := by
  rw [Lp.norm_toLp]
  exact (B0008.norm_L2w M f).symm

/-- `f ↦ ⟨y⟩^M f` as a linear map `L²_M → L²(ℂ)`. -/
def weightLin (M : ℝ) : L2w M →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℂ) where
  toFun f := (memLp_wt_smul (Lp.memLp f)).toLp (fun y => wt M y • f y)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_wt_smul (Lp.memLp (f + g))),
      MemLp.coeFn_toLp (memLp_wt_smul (Lp.memLp f)),
      MemLp.coeFn_toLp (memLp_wt_smul (Lp.memLp g)),
      Lp.coeFn_add ((memLp_wt_smul (Lp.memLp f)).toLp (fun y => wt M y • f y))
        ((memLp_wt_smul (Lp.memLp g)).toLp (fun y => wt M y • g y)),
      (volume_ac M).ae_le (Lp.coeFn_add f g)] with y h1 h2 h3 h4 h5
    rw [h1, h4, Pi.add_apply, h2, h3, h5, Pi.add_apply, smul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_wt_smul (Lp.memLp (c • f))),
      MemLp.coeFn_toLp (memLp_wt_smul (Lp.memLp f)),
      Lp.coeFn_smul c ((memLp_wt_smul (Lp.memLp f)).toLp (fun y => wt M y • f y)),
      (volume_ac M).ae_le (Lp.coeFn_smul c f)] with y h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h2, h4, Pi.smul_apply, smul_comm]

/-- The weight isometry `L²_M ≃ L²(ℂ)`, `f ↦ ⟨y⟩^M f`. -/
def weightIso (M : ℝ) : L2w M ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℂ) where
  toLinearEquiv :=
    { weightLin M with
      invFun := fun g => (memLp_wt_inv_smul (M := M) (Lp.memLp g)).toLp
        (fun y => (wt M y)⁻¹ • g y)
      left_inv := fun f => by
        apply Lp.ext
        change ⇑((memLp_wt_inv_smul (M := M) (Lp.memLp ((memLp_wt_smul (Lp.memLp f)).toLp
          (fun y => wt M y • f y)))).toLp _) =ᵐ[wMeasure M] ⇑f
        filter_upwards [MemLp.coeFn_toLp (memLp_wt_inv_smul (M := M)
            (Lp.memLp ((memLp_wt_smul (Lp.memLp f)).toLp (fun y => wt M y • f y)))),
          (wMeasure_ac M).ae_le (MemLp.coeFn_toLp (memLp_wt_smul (Lp.memLp f)))]
          with y h1 h2
        rw [h1, h2, smul_smul, inv_mul_cancel₀ (wt_ne_zero M y), one_smul]
      right_inv := fun g => by
        apply Lp.ext
        change ⇑((memLp_wt_smul (Lp.memLp ((memLp_wt_inv_smul (M := M) (Lp.memLp g)).toLp
          (fun y => (wt M y)⁻¹ • g y)))).toLp _) =ᵐ[volume] ⇑g
        filter_upwards [MemLp.coeFn_toLp (memLp_wt_smul (Lp.memLp
            ((memLp_wt_inv_smul (M := M) (Lp.memLp g)).toLp (fun y => (wt M y)⁻¹ • g y)))),
          (volume_ac M).ae_le (MemLp.coeFn_toLp (memLp_wt_inv_smul (M := M) (Lp.memLp g)))]
          with y h1 h2
        rw [h1, h2, smul_smul, mul_inv_cancel₀ (wt_ne_zero M y), one_smul] }
  norm_map' f := norm_toLp_wt_smul f

theorem coeFn_weightIso (M : ℝ) (f : L2w M) :
    (weightIso M f : ℂ → ℂ) =ᵐ[volume] fun y => wt M y • f y :=
  MemLp.coeFn_toLp (memLp_wt_smul (Lp.memLp f))

theorem coeFn_weightIso_symm (M : ℝ) (g : Lp ℂ 2 (volume : Measure ℂ)) :
    ((weightIso M).symm g : ℂ → ℂ) =ᵐ[volume] fun y => (wt M y)⁻¹ • g y :=
  (volume_ac M).ae_le (MemLp.coeFn_toLp (memLp_wt_inv_smul (M := M) (Lp.memLp g)))

/-! ### P2: the sector projections on `L²_M` -/

/-- The angular sector projection on `L²_M`,
`P_n f(x) = (2π)⁻¹ ∫₀^{2π} e^{-inφ} f(e^{iφ}x) dφ` (`coeFn_sectorProjW`), defined by transport
of the `L²(ℂ)` projection `NUE.Ang.sectorProjL n` through `weightIso`. -/
def sectorProjW (M : ℝ) (n : ℤ) : L2w M →L[ℂ] L2w M :=
  (weightIso M).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((Ang.sectorProjL n).comp (weightIso M).toLinearIsometry.toContinuousLinearMap)

theorem sectorProjW_apply (M : ℝ) (n : ℤ) (f : L2w M) :
    sectorProjW M n f = (weightIso M).symm (Ang.sectorProjL n (weightIso M f)) := rfl

theorem weightIso_sectorProjW (M : ℝ) (n : ℤ) (f : L2w M) :
    weightIso M (sectorProjW M n f) = Ang.sectorProjL n (weightIso M f) := by
  rw [sectorProjW_apply, LinearIsometryEquiv.apply_symm_apply]

/-- **The pointwise formula.** `P_n f(x) = (2π)⁻¹ ∫₀^{2π} e^{-inφ} f(e^{iφ}x) dφ` for almost
every `x`. -/
theorem coeFn_sectorProjW (M : ℝ) (n : ℤ) (f : L2w M) :
    (sectorProjW M n f : ℂ → ℂ) =ᵐ[wMeasure M] Ang.sectorProj n f := by
  have hrad : Ang.sectorProj n (fun y => wt M y • f y) =
      fun y => wt M y • Ang.sectorProj n f y := by
    have h := Ang.sectorProj_radial_mul n (wtR M) f
    simp only [← wt_eq_wtR] at h
    simpa only [Complex.real_smul] using h
  have h1 := coeFn_weightIso_symm M (Ang.sectorProjL n (weightIso M f))
  have h2 := Ang.sectorProjL_spec n (weightIso M f)
  have h3 := Ang.sectorProj_congr_ae n (coeFn_weightIso M f)
  refine (wMeasure_ac M).ae_le ?_
  filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
  rw [sectorProjW_apply, hy1, hy2, hy3, hrad, smul_smul, inv_mul_cancel₀ (wt_ne_zero M y),
    one_smul]

/-- `P_n f = f_n(r) e^{inϑ}` with the angular sector `f_n(r) = (2π)⁻¹∫₀^{2π} f(re^{iθ})e^{-inθ}dθ`
(`NUE.Polar.angularSector`), almost everywhere. -/
theorem sectorProjW_ae_eq_ofProfile (M : ℝ) (n : ℤ) (f : L2w M) :
    (sectorProjW M n f : ℂ → ℂ) =ᵐ[wMeasure M]
      Ang.ofProfile n (Polar.angularSector (f : ℂ → ℂ) n) :=
  (coeFn_sectorProjW M n f).trans
    ((wMeasure_ac M).ae_le (Ang.SectorL2Aux.sectorProj_ae_eq_ofProfile n f))

/-- **The angular Fourier series converges in `L²_M`**: `f = ∑_{n ∈ ℤ} P_n f`. -/
theorem hasSum_sectorProjW {M : ℝ} (f : L2w M) :
    HasSum (fun n : ℤ => sectorProjW M n f) f := by
  have h := (Ang.hasSum_sectorProjL (weightIso M f)).mapL
    (weightIso M).symm.toLinearIsometry.toContinuousLinearMap
  simpa [sectorProjW_apply] using h

/-- **Parseval in `L²_M`**: `‖f‖² = ∑_n ‖P_n f‖²`. -/
theorem hasSum_norm_sq_sectorProjW {M : ℝ} (f : L2w M) :
    HasSum (fun n : ℤ => ‖sectorProjW M n f‖ ^ 2) (‖f‖ ^ 2) := by
  have h := Ang.hasSum_norm_sq_sectorProjL (weightIso M f)
  rw [LinearIsometryEquiv.norm_map] at h
  refine h.congr_fun fun n => ?_
  rw [sectorProjW_apply, LinearIsometryEquiv.norm_map]

/-- **Orthogonality of different sectors** in `L²_M`. -/
theorem inner_sectorProjW_of_ne {M : ℝ} {m n : ℤ} (h : m ≠ n) (f g : L2w M) :
    ⟪sectorProjW M m f, sectorProjW M n g⟫_ℂ = 0 := by
  rw [sectorProjW_apply, sectorProjW_apply, LinearIsometryEquiv.inner_map_map]
  exact Ang.inner_sectorProjL_of_ne h _ _

/-- `P_n` is self-adjoint on `L²_M`. -/
theorem inner_sectorProjW {M : ℝ} (n : ℤ) (f g : L2w M) :
    ⟪sectorProjW M n f, g⟫_ℂ = ⟪f, sectorProjW M n g⟫_ℂ := by
  have hf : f = (weightIso M).symm (weightIso M f) := by simp
  have hg : g = (weightIso M).symm (weightIso M g) := by simp
  rw [sectorProjW_apply, sectorProjW_apply]
  conv_lhs => rw [hg]
  conv_rhs => rw [hf]
  rw [LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]
  exact Ang.inner_sectorProjL n _ _

/-- `P_m P_n = δ_{mn} P_n` on `L²_M`. -/
theorem sectorProjW_comp {M : ℝ} (m n : ℤ) :
    (sectorProjW M m).comp (sectorProjW M n) = if m = n then sectorProjW M n else 0 := by
  have h := Ang.sectorProjL_comp m n
  refine ContinuousLinearMap.ext fun f => ?_
  rw [ContinuousLinearMap.comp_apply, sectorProjW_apply, weightIso_sectorProjW]
  have h' := congrArg (fun T => T (weightIso M f)) h
  simp only [ContinuousLinearMap.comp_apply] at h'
  rw [h']
  split_ifs
  · rfl
  · simp

theorem sectorProjW_idem {M : ℝ} (n : ℤ) (f : L2w M) :
    sectorProjW M n (sectorProjW M n f) = sectorProjW M n f := by
  have h := congrArg (fun T => T f) (sectorProjW_comp (M := M) n n)
  simpa using h

/-- **Conjugate sectors**: complex conjugation maps sector `n` to sector `-n`,
`P_{-n}(f̄) = conj (P_n f)`. -/
theorem sectorProjW_conj {M : ℝ} (n : ℤ) (f : L2w M) :
    sectorProjW M (-n) (star f) = star (sectorProjW M n f) := by
  apply Lp.ext
  have hs : ((star f : L2w M) : ℂ → ℂ) =ᵐ[volume] fun y => conj (f y) := by
    filter_upwards [(volume_ac M).ae_le (Lp.coeFn_star f)] with y hy
    rw [hy, Pi.star_apply]
    rfl
  have h1 := coeFn_sectorProjW M (-n) (star f)
  have h2 := (wMeasure_ac M).ae_le (Ang.sectorProj_congr_ae (-n) hs)
  have h3 := Lp.coeFn_star (sectorProjW M n f)
  have h4 := coeFn_sectorProjW M n f
  filter_upwards [h1, h2, h3, h4] with y hy1 hy2 hy3 hy4
  rw [hy1, hy2, Ang.sectorProj_conj, hy3, Pi.star_apply, hy4]
  rfl

end UnforcedLeray.Planar
