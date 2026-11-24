import UnforcedLeray.Units.B0583

/-!
# B0610 `unlabeled:9889`: zero circulation, extended unstable projection, velocity reconstruction

Blueprint unit **B0610** (label `unlabeled:9889`), `paper/main.tex` lines 9889–9895, inside the
weak-source construction of `lem:operator-3-5` (`paper/main.tex:9869-9910`):

> The curl source has zero circulation. Smooth finite-rank dual kernels lie in `H^1_{-m}`;
> hence the unstable projection extends to this negative space. The complete nonzero-mode and
> zero-mode reconstruction [`prepared:p1.3`–`prepared:p1.4`] gives
> `‖K_c ω‖_{H¹} ≤ C(1 + c)‖ω‖_{X_m}`.

Dependencies: `B0579` (`prepared:p1.1`: `X_m`, `H^1_{±m}`, `H^{-1}_m = (H^1_{-m})^*` with the
unweighted pairing, `paper/main.tex:9370-9387`), `B0582` (`prepared:p1.3`, Hardy) and `B0583`
(`prepared:p1.4`, velocity reconstruction, `paper/main.tex:9405-9433`).

## The three claims

1. **Zero circulation of the curl source.** The vorticity force of the meridional correction
   equation is `f = -curl_{q,η} G` with `G = v₀·∇b_{0,mer} + b_{0,mer}·∇v₀` (eq.
   `eq:st18-t00555`, `paper/main.tex:9875-9880`), and `G ∈ X_m` by `prepared:p1.2`
   (`paper/main.tex:9389-9405`, `eq:st18-t00556`). For every `G = (G_q, G_η) ∈ X_m²` the
   functional `curlSource c m G ∈ H^{-1}_m`, `⟨f, φ⟩ = ∫_cell G_η ∂_qφ - ∫_cell G_q ∂_ηφ`
   (`toDistribution_curlSource`: on test functions it is the distribution `-(∂_q G_η - ∂_η G_q)`),
   annihilates every element of `H^1_{-m}` with zero gradient (`curlSource_apply_of_der_eq_zero`).
   For `m > 1/2` the constant `1` lies in `H^1_{-m}` (`oneH1`, gradient `0`), and *zero
   circulation* of `ℓ ∈ H^{-1}_m` is `ℓ(1) = 0` (`HasZeroCirculation`); this is exactly the
   hypothesis `∫_cell ω = 0` of `B0583` when `ℓ` is the source functional of `ω ∈ X_m`
   (`hasZeroCirculation_sourceCLM_iff`). `hasZeroCirculation_curlSource`: the curl source has
   zero circulation.
2. **Extension of the unstable projection.** A smooth dual kernel (`IsSmoothDualKernel`) is a
   smooth `c`-periodic `ψ` with `ψ, ∂_qψ, ∂_ηψ ∈ X_{-m}`; it lies in `H^1_{-m}`
   (`IsSmoothDualKernel.memH1`, `IsSmoothDualKernel.toH1`: its classical gradient is its weak
   gradient on the cylinder, `hasWeakCellDeriv_of_smooth`). Bounded smooth kernels with bounded
   gradient are smooth dual kernels for every `m > 1/2` (`isSmoothDualKernel_of_bounded`). A
   finite-rank operator `P f = ∑_j (∫_cell f ψ_j) φ_j` with smooth dual kernels
   (`IsSmoothFiniteRank`) extends continuously to `H^{-1}_m` by `ℓ ↦ ∑_j ℓ(ψ_j) φ_j`
   (`projExt`, `projExt_sourceCLM`, `norm_projExt_apply_le`, `exists_negExtension`); on the curl
   source it is `∑_j (∫ G_η ∂_qψ_j - ∫ G_q ∂_ηψ_j) φ_j` (`projExt_curlSource_smooth`).
3. **Velocity reconstruction.** `B0583.velocity_reconstruction`: `‖K_c ω‖_{H¹} ≤ 5(1 + c)‖ω‖_{X_m}`
   for `m > 1` and `∫_cell ω = 0`.

`zeroCirculation_projection_reconstruction` states the unit as one conjunction.

Variable names: a vorticity `ω ∈ X_m` of the manuscript is written `w` in the code, because
`open scoped ContDiff` (needed for `ContDiff ℝ ∞`) makes `ω` a notation.

## Hypotheses made explicit

* The unit speaks of *the* unstable projection of the cylinder problem (finite rank, with smooth
  direct and dual vectors, `paper/main.tex:9482-9484`, `9909-9910`). Its construction belongs to
  the spectral theory of the cylinder linearization (`sec:mixed-background`,
  `paper/main.tex:4092-5062`), which is not built. The extension is therefore proved for every
  operator of smooth finite-rank form (`IsSmoothFiniteRank`); that the unstable projection has
  this form is the named input, recorded in the docstring of `IsSmoothFiniteRank`.
* "Smooth dual kernels lie in `H^1_{-m}`" needs, besides smoothness and periodicity, that the
  kernels and their gradients lie in `X_{-m}`. This is part of `IsSmoothDualKernel`; it holds for
  bounded kernels with bounded gradient as soon as `m > 1/2` (`isSmoothDualKernel_of_bounded`),
  weaker than the manuscript's `m > 1` (and its standing `m > 8`).
* Zero circulation needs the constant `1 ∈ H^1_{-m}`, i.e. `m > 1/2` (weaker than `m > 1`).
* The reconstruction is `B0583` verbatim: `c > 0` (`[Fact (0 < c)]`, the manuscript's
  `c = ν^{-ρ}`), `m > 1`, `∫_cell ω = 0` (an absolutely convergent integral for `m ≥ 1`,
  `B0583.integrable_of_X`, so no Bochner junk value).
* All other statements hold for every real `c` (for `c ≤ 0` the cell is empty).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff Topology

namespace UnforcedLeray.B0610

open B0579

/-! ### Square integrability of slowly decaying weights on the cell -/

/-- `⟨x⟩^{-m} ∈ L²(cell)` for `m > 1/2`: on the cell `⟨x⟩^{-2m} ≤ (1 + η²)^{-m}`, which is
integrable in `η` for `2m > 1`, and the cell has finite width in `q`. -/
theorem memLp_bracket_neg_of_half {c m : ℝ} (hm : 1 / 2 < m) :
    MemLp (fun x => bracket x ^ (-m)) 2 (volume.restrict (cell c)) := by
  have hcont : Continuous fun x => bracket x ^ (-m) := continuous_bracket_rpow (-m)
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  have hr : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < 2 * m := by
    rw [Module.finrank_self]; push_cast; linarith
  have hint : Integrable (fun x : Plane => (1 + ‖x.2‖ ^ 2) ^ (-(2 * m) / 2)) (B0581.cellVol c) := by
    rw [B0581.cellVol_eq]
    exact (integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure ℝ)) hr).comp_snd
      (B0581.μq c)
  refine hint.mono' (hcont.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have hj := jb_pos x
  have hb : 0 ≤ bracket x ^ (-m) := (bracket_rpow_pos (-m) x).le
  have hsq : (bracket x ^ (-m)) ^ 2 = jb x ^ (-m) := by
    rw [bracket_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hj.le]
    congr 1
    push_cast
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hb 2), hsq, Real.norm_eq_abs, sq_abs,
    show -(2 * m) / 2 = -m by ring]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by unfold jb; nlinarith [sq_nonneg x.1])
    (by linarith)

/-- A bounded continuous function lies in `X_{-m}` for every `m > 1/2`. -/
theorem memLp_neg_of_bounded {c m : ℝ} (hm : 1 / 2 < m) {f : Plane → ℝ} (hf : Continuous f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) : MemLp f 2 (cellMeasure c (-m)) := by
  rw [memLp_cellMeasure_iff]
  refine ((memLp_bracket_neg_of_half (c := c) hm).const_mul C).of_le
    ((continuous_bracket_rpow (-m)).mul hf).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have hb := bracket_rpow_pos (-m) x
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC x)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hb, abs_of_nonneg hC0,
    mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC x) hb.le

/-! ### Smooth periodic functions: classical gradient is the weak cylinder gradient -/

/-- A smooth `c`-periodic function times a cylinder test function is a cylinder test function. -/
theorem isCylTest_smooth_mul {c : ℝ} {ψ φ : Plane → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hper : ∀ x : Plane, ψ (x.1 + c, x.2) = ψ x) (hφ : IsCylTest c φ) :
    IsCylTest c (fun x => ψ x * φ x) where
  smooth := hψ.mul hφ.smooth
  periodic x := by simp only [hper x, hφ.periodic x]
  band := by
    obtain ⟨R, hR⟩ := hφ.band
    exact ⟨R, fun x hx => by simp [hR x hx]⟩

/-- Integration by parts on the cylinder against a smooth periodic function (no decay in `η`
is needed, since the test function has compact support on the cylinder): the classical
derivative `∂_j ψ` is the weak cylinder derivative of `ψ`. -/
theorem hasWeakCellDeriv_of_smooth {c : ℝ} {ψ : Plane → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hper : ∀ x : Plane, ψ (x.1 + c, x.2) = ψ x) (j : Fin 2) :
    HasWeakCellDeriv c j ψ (pd j ψ) := by
  intro φ hφ
  have h0 := integral_pd_eq_zero (isCylTest_smooth_mul hψ hper hφ) j
  have heq : pd j (fun y => ψ y * φ y) = fun x => pd j ψ x * φ x + ψ x * pd j φ x :=
    funext (pd_mul (hψ.differentiable (by simp)) hφ.differentiable j)
  obtain ⟨R, hR⟩ := hφ.vanish
  obtain ⟨R', hR'⟩ := (hφ.pd j).vanish
  have i1 : IntegrableOn (fun x => pd j ψ x * φ x) (cell c) :=
    integrableOn_cell_of_continuous ((contDiff_pd hψ j).continuous.mul hφ.continuous)
      (isCompact_box c R) (fun x hx hxK => by simp [hR x hx hxK])
  have i2 : IntegrableOn (fun x => ψ x * pd j φ x) (cell c) :=
    integrableOn_cell_of_continuous (hψ.continuous.mul (hφ.pd j).continuous)
      (isCompact_box c R') (fun x hx hxK => by simp [hR' x hx hxK])
  rw [heq, integral_add i1 i2] at h0
  linarith

/-! ### The constant `1 ∈ H^1_{-m}` and zero circulation -/

section One

variable {c m : ℝ}

theorem memLp_one_neg (hm : 1 / 2 < m) :
    MemLp (fun _ : Plane => (1 : ℝ)) 2 (cellMeasure c (-m)) :=
  memLp_neg_of_bounded hm continuous_const (C := 1) (fun _ => by simp)

variable (c m) in
/-- The constant function `1` as an element of `X_{-m}` (`m > 1/2`). -/
def oneX (hm : 1 / 2 < m) : X c (-m) := (memLp_one_neg hm).toLp _

theorem coeFn_oneX (hm : 1 / 2 < m) :
    (oneX c m hm : Plane → ℝ) =ᵐ[volume.restrict (cell c)] fun _ => (1 : ℝ) :=
  (ac_cellMeasure c (-m)).ae_le (MemLp.coeFn_toLp _)

variable (c m) in
/-- **The constant `1 ∈ H^1_{-m}`** for `m > 1/2`, with weak gradient `0`
(`∫_cell ∂_jφ = 0` for cylinder test functions, `B0579.integral_pd_eq_zero`). -/
def oneH1 (hm : 1 / 2 < m) : H1 c (-m) :=
  ⟨tuple c (-m) (oneX c m hm) (fun _ => 0), by
    rw [mem_H1Sub_iff]
    intro j
    have h : HasWeakCellDeriv c j (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) := fun φ hφ => by
      simp only [one_mul, zero_mul, integral_zero, neg_zero]
      exact integral_pd_eq_zero hφ j
    have e0 : ((0 : X c (-m)) : Plane → ℝ) =ᵐ[volume.restrict (cell c)] 0 :=
      (ac_cellMeasure c (-m)).ae_le (Lp.coeFn_zero ℝ 2 (cellMeasure c (-m)))
    exact h.congr (coeFn_oneX hm).symm e0.symm⟩

@[simp] theorem oneH1_value (hm : 1 / 2 < m) : (oneH1 c m hm).value = oneX c m hm := rfl

@[simp] theorem oneH1_der (hm : 1 / 2 < m) (j : Fin 2) : (oneH1 c m hm).der j = 0 := rfl

variable (c m) in
/-- **Zero total circulation** of `ℓ ∈ H^{-1}_m` (`m > 1/2`): `⟨ℓ, 1⟩ = 0`. -/
def HasZeroCirculation (hm : 1 / 2 < m) (ℓ : Hneg c m) : Prop := ℓ (oneH1 c m hm) = 0

/-- The source functional of `ω ∈ X_m` paired with `1` is the total circulation `∫_cell ω`
(absolutely convergent, `B0579.integrableOn_source`). -/
theorem sourceCLM_oneH1 (hm : 1 / 2 < m) (w : X c m) :
    sourceCLM c m w (oneH1 c m hm) = ∫ x in cell c, w x := by
  rw [sourceCLM_apply, oneH1_value]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_oneX (c := c) hm] with x hx
  rw [hx, mul_one]

/-- For sources given by a function `ω ∈ X_m`, zero circulation in `H^{-1}_m` is exactly the
hypothesis `∫_cell ω = 0` of `B0583` (`prepared:p1.4`). -/
theorem hasZeroCirculation_sourceCLM_iff (hm : 1 / 2 < m) (w : X c m) :
    HasZeroCirculation c m hm (sourceCLM c m w) ↔ ∫ x in cell c, w x = 0 := by
  rw [HasZeroCirculation, sourceCLM_oneH1]

end One

/-! ### The curl source `f = -curl_{q,η} G` -/

section Curl

variable {c m : ℝ}

/-- A derivative source `∂_j G` vanishes on every `F ∈ H^1_{-m}` with `∂_j F = 0`. -/
theorem derivSourceCLM_apply_of_der_eq_zero (j : Fin 2) (G : X c m) (F : H1 c (-m))
    (hF : F.der j = 0) : derivSourceCLM c m j G F = 0 := by
  have h0 : conjDer c m j F = 0 := by
    simp only [conjDer, ContinuousLinearMap.comp_apply, H1.derCLM_apply, hF, map_zero]
  rw [derivSourceCLM, neg_apply, neg_apply,
    pairCLM_apply, h0, inner_zero_right, neg_zero]

variable (c m) in
/-- **The curl source** `f = -curl_{q,η} G = -(∂_q G_η - ∂_η G_q) ∈ H^{-1}_m` of a vector field
`G = (G_q, G_η) ∈ X_m²` (order `(q, η)`; `G 0 = G_q`, `G 1 = G_η`): the vorticity force
`eq:st18-t00555` (`paper/main.tex:9875-9880`) with `G = v₀·∇b_{0,mer} + b_{0,mer}·∇v₀`.
It is written as `∂_η G_q - ∂_q G_η` with the derivative sources `B0579.derivSourceCLM`
(`⟨∂_j G, φ⟩ = -∫_cell G ∂_jφ`). -/
def curlSource (G : Fin 2 → X c m) : Hneg c m :=
  derivSourceCLM c m 1 (G 0) - derivSourceCLM c m 0 (G 1)

/-- `⟨f, φ⟩ = ∫_cell G_η ∂_qφ - ∫_cell G_q ∂_ηφ` (unweighted pairing). -/
theorem curlSource_apply (G : Fin 2 → X c m) (φ : H1 c (-m)) :
    curlSource c m G φ =
      (∫ x in cell c, G 1 x * φ.der 0 x) - ∫ x in cell c, G 0 x * φ.der 1 x := by
  simp only [curlSource, sub_apply, derivSourceCLM_apply]
  ring

/-- On cylinder test functions the curl source is the distribution `-(∂_q G_η - ∂_η G_q)`. -/
theorem toDistribution_curlSource (G : Fin 2 → X c m) (φ : {φ : Plane → ℝ // IsCylTest c φ}) :
    toDistribution c m (curlSource c m G) φ =
      (∫ x in cell c, G 1 x * pd 0 φ.1 x) - ∫ x in cell c, G 0 x * pd 1 φ.1 x := by
  simp only [toDistribution, curlSource,
    sub_apply]
  have h0 := toDistribution_derivSourceCLM c m 0 (G 1) φ
  have h1 := toDistribution_derivSourceCLM c m 1 (G 0) φ
  simp only [toDistribution] at h0 h1
  rw [h0, h1]
  ring

/-- `‖-curl G‖_{H^{-1}_m} ≤ ‖G_q‖_{X_m} + ‖G_η‖_{X_m}`. -/
theorem norm_curlSource_le (G : Fin 2 → X c m) : ‖curlSource c m G‖ ≤ ‖G 0‖ + ‖G 1‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun φ => ?_
  simp only [curlSource, sub_apply]
  calc ‖derivSourceCLM c m 1 (G 0) φ - derivSourceCLM c m 0 (G 1) φ‖
      ≤ ‖derivSourceCLM c m 1 (G 0) φ‖ + ‖derivSourceCLM c m 0 (G 1) φ‖ := norm_sub_le _ _
    _ ≤ ‖G 0‖ * ‖φ‖ + ‖G 1‖ * ‖φ‖ := by
        gcongr
        · exact ((derivSourceCLM c m 1 (G 0)).le_opNorm φ).trans
            (by gcongr; exact norm_derivSourceCLM_le c m 1 _)
        · exact ((derivSourceCLM c m 0 (G 1)).le_opNorm φ).trans
            (by gcongr; exact norm_derivSourceCLM_le c m 0 _)
    _ = (‖G 0‖ + ‖G 1‖) * ‖φ‖ := by ring

/-- The curl source annihilates every element of `H^1_{-m}` with zero weak gradient. -/
theorem curlSource_apply_of_der_eq_zero (G : Fin 2 → X c m) (F : H1 c (-m))
    (hF : ∀ j, F.der j = 0) : curlSource c m G F = 0 := by
  simp only [curlSource, sub_apply, derivSourceCLM_apply_of_der_eq_zero 0 (G 1) F (hF 0),
    derivSourceCLM_apply_of_der_eq_zero 1 (G 0) F (hF 1), sub_zero]

/-- **The curl source has zero circulation** (`paper/main.tex:9891`), for every `m > 1/2`. -/
theorem hasZeroCirculation_curlSource (hm : 1 / 2 < m) (G : Fin 2 → X c m) :
    HasZeroCirculation c m hm (curlSource c m G) :=
  curlSource_apply_of_der_eq_zero G _ (oneH1_der hm)

end Curl

/-! ### Smooth dual kernels and the extension of finite-rank projections -/

section Projection

variable {c m : ℝ}

/-- A **smooth dual kernel** for the unweighted pairing with `X_m`: smooth, `c`-periodic in `q`
(a smooth function on the cylinder), with `ψ, ∂_qψ, ∂_ηψ ∈ X_{-m}`. -/
structure IsSmoothDualKernel (c m : ℝ) (ψ : Plane → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ ψ
  periodic : ∀ x : Plane, ψ (x.1 + c, x.2) = ψ x
  memLp : MemLp ψ 2 (cellMeasure c (-m))
  memLp_pd : ∀ j : Fin 2, MemLp (pd j ψ) 2 (cellMeasure c (-m))

/-- A smooth dual kernel as an element of `H^1_{-m}`, with its classical gradient. -/
def IsSmoothDualKernel.toH1 {ψ : Plane → ℝ} (h : IsSmoothDualKernel c m ψ) : H1 c (-m) :=
  ⟨tuple c (-m) (h.memLp.toLp ψ) (fun j => (h.memLp_pd j).toLp (pd j ψ)), by
    rw [mem_H1Sub_iff]
    intro j
    have e0 : ((h.memLp.toLp ψ : X c (-m)) : Plane → ℝ) =ᵐ[volume.restrict (cell c)] ψ :=
      (ac_cellMeasure c (-m)).ae_le (MemLp.coeFn_toLp h.memLp)
    have e1 : (((h.memLp_pd j).toLp (pd j ψ) : X c (-m)) : Plane → ℝ)
        =ᵐ[volume.restrict (cell c)] pd j ψ :=
      (ac_cellMeasure c (-m)).ae_le (MemLp.coeFn_toLp (h.memLp_pd j))
    exact (hasWeakCellDeriv_of_smooth h.smooth h.periodic j).congr e0.symm e1.symm⟩

theorem IsSmoothDualKernel.coeFn_toH1_value {ψ : Plane → ℝ} (h : IsSmoothDualKernel c m ψ) :
    (h.toH1.value : Plane → ℝ) =ᵐ[volume.restrict (cell c)] ψ :=
  (ac_cellMeasure c (-m)).ae_le (MemLp.coeFn_toLp h.memLp)

theorem IsSmoothDualKernel.coeFn_toH1_der {ψ : Plane → ℝ} (h : IsSmoothDualKernel c m ψ)
    (j : Fin 2) : (h.toH1.der j : Plane → ℝ) =ᵐ[volume.restrict (cell c)] pd j ψ :=
  (ac_cellMeasure c (-m)).ae_le (MemLp.coeFn_toLp (h.memLp_pd j))

/-- **Smooth dual kernels lie in `H^1_{-m}`** (`paper/main.tex:9891-9892`). -/
theorem IsSmoothDualKernel.memH1 {ψ : Plane → ℝ} (h : IsSmoothDualKernel c m ψ) :
    MemH1 c (-m) ψ :=
  (memH1_iff c (-m) ψ).2 ⟨h.toH1, h.coeFn_toH1_value⟩

/-- Smooth periodic kernels that are bounded with bounded gradient are smooth dual kernels for
every `m > 1/2`. -/
theorem isSmoothDualKernel_of_bounded (hm : 1 / 2 < m) {ψ : Plane → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hper : ∀ x : Plane, ψ (x.1 + c, x.2) = ψ x) (hb : ∃ C, ∀ x, |ψ x| ≤ C)
    (hdb : ∀ j : Fin 2, ∃ C, ∀ x, |pd j ψ x| ≤ C) : IsSmoothDualKernel c m ψ := by
  obtain ⟨C, hC⟩ := hb
  refine ⟨hψ, hper, memLp_neg_of_bounded hm hψ.continuous hC, fun j => ?_⟩
  obtain ⟨C', hC'⟩ := hdb j
  exact memLp_neg_of_bounded hm (contDiff_pd hψ j).continuous hC'

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable (c m) in
/-- **The extension to `H^{-1}_m`** of the finite-rank operator `f ↦ ∑_j ⟨f, ψ_j⟩ φ_j` with dual
kernels `ψ_j ∈ H^1_{-m}` and direct vectors `φ_j ∈ V`: `ℓ ↦ ∑_j ℓ(ψ_j) φ_j`. -/
def projExt {n : ℕ} (ψ : Fin n → H1 c (-m)) (φ : Fin n → V) : Hneg c m →L[ℝ] V :=
  ∑ j, (ContinuousLinearMap.apply ℝ ℝ (ψ j)).smulRight (φ j)

theorem projExt_apply {n : ℕ} (ψ : Fin n → H1 c (-m)) (φ : Fin n → V) (ℓ : Hneg c m) :
    projExt c m ψ φ ℓ = ∑ j, ℓ (ψ j) • φ j := by
  simp [projExt]

/-- On sources `f ∈ X_m` the extension is the finite-rank operator
`f ↦ ∑_j (∫_cell f ψ_j) φ_j`. -/
theorem projExt_sourceCLM {n : ℕ} (ψ : Fin n → H1 c (-m)) (φ : Fin n → V) (f : X c m) :
    projExt c m ψ φ (sourceCLM c m f) = ∑ j, (∫ x in cell c, f x * (ψ j).value x) • φ j := by
  rw [projExt_apply]
  simp only [sourceCLM_apply]

/-- `‖∑_j ℓ(ψ_j) φ_j‖ ≤ (∑_j ‖ψ_j‖_{H^1_{-m}} ‖φ_j‖) ‖ℓ‖_{H^{-1}_m}`: the operator norm of the
extension is at most `∑_j ‖ψ_j‖ ‖φ_j‖`. -/
theorem norm_projExt_apply_le {n : ℕ} (ψ : Fin n → H1 c (-m)) (φ : Fin n → V) (ℓ : Hneg c m) :
    ‖projExt c m ψ φ ℓ‖ ≤ (∑ j, ‖ψ j‖ * ‖φ j‖) * ‖ℓ‖ := by
  rw [projExt_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul]
  calc ‖ℓ (ψ j)‖ * ‖φ j‖ ≤ ‖ℓ‖ * ‖ψ j‖ * ‖φ j‖ := by
        gcongr
        exact ℓ.le_opNorm _
    _ = ‖ψ j‖ * ‖φ j‖ * ‖ℓ‖ := by ring

/-- The extension applied to the curl source: `∑_j (∫ G_η ∂_qψ_j - ∫ G_q ∂_ηψ_j) φ_j`. -/
theorem projExt_curlSource {n : ℕ} (ψ : Fin n → H1 c (-m)) (φ : Fin n → V)
    (G : Fin 2 → X c m) :
    projExt c m ψ φ (curlSource c m G) =
      ∑ j, ((∫ x in cell c, G 1 x * (ψ j).der 0 x) -
        ∫ x in cell c, G 0 x * (ψ j).der 1 x) • φ j := by
  rw [projExt_apply]
  simp only [curlSource_apply]

/-- For smooth dual kernels, the extension on the curl source uses the classical gradients. -/
theorem projExt_curlSource_smooth {n : ℕ} {ψ : Fin n → Plane → ℝ}
    (hψ : ∀ j, IsSmoothDualKernel c m (ψ j)) (φ : Fin n → V) (G : Fin 2 → X c m) :
    projExt c m (fun j => (hψ j).toH1) φ (curlSource c m G) =
      ∑ j, ((∫ x in cell c, G 1 x * pd 0 (ψ j) x) -
        ∫ x in cell c, G 0 x * pd 1 (ψ j) x) • φ j := by
  rw [projExt_curlSource]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  · refine integral_congr_ae ?_
    filter_upwards [(hψ j).coeFn_toH1_der 0] with x hx
    rw [hx]
  · refine integral_congr_ae ?_
    filter_upwards [(hψ j).coeFn_toH1_der 1] with x hx
    rw [hx]

variable (c m) in
/-- **Smooth finite-rank form** of an operator `P : X_m → V`: `P f = ∑_j (∫_cell f ψ_j) φ_j` for
finitely many smooth dual kernels `ψ_j` (`IsSmoothDualKernel`) and direct vectors `φ_j ∈ V`.

*Named input.* The manuscript applies the unit to the finite-rank unstable projection of the
cylinder problem, "extended directly by its smooth direct and dual vectors"
(`paper/main.tex:9482-9484`, `9909-9910`). Its construction (the unstable spectral subspace
of the cylinder linearization and its smooth dual vectors) belongs to `sec:mixed-background`
(`paper/main.tex:4092-5062`), which is not built in Lean; that the unstable projection is of
this form is the input the extension statement is conditioned on. -/
def IsSmoothFiniteRank (P : X c m → V) : Prop :=
  ∃ (n : ℕ) (ψ : Fin n → Plane → ℝ) (φ : Fin n → V), (∀ j, IsSmoothDualKernel c m (ψ j)) ∧
    ∀ f : X c m, P f = ∑ j, (∫ x in cell c, f x * ψ j x) • φ j

/-- **The unstable projection extends continuously to `H^{-1}_m`** (`paper/main.tex:9891-9893`):
an operator of smooth finite-rank form on `X_m` is the restriction, through the source embedding
`X_m → H^{-1}_m`, of a bounded operator on `H^{-1}_m`. -/
theorem exists_negExtension {P : X c m → V} (hP : IsSmoothFiniteRank c m P) :
    ∃ Pe : Hneg c m →L[ℝ] V, ∀ f : X c m, Pe (sourceCLM c m f) = P f := by
  obtain ⟨n, ψ, φ, hψ, hPf⟩ := hP
  refine ⟨projExt c m (fun j => (hψ j).toH1) φ, fun f => ?_⟩
  rw [projExt_sourceCLM, hPf]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [(hψ j).coeFn_toH1_value] with x hx
  rw [hx]

end Projection

/-! ### The unit -/

/-- **B0610** (`unlabeled:9889`, `paper/main.tex:9889-9895`).

1. *The curl source has zero circulation*: for `m > 1/2` and every `G = (G_q, G_η) ∈ X_m²`,
   `f = -curl_{q,η} G ∈ H^{-1}_m` (eq. `eq:st18-t00555`) satisfies `⟨f, 1⟩ = 0`; for sources
   `ω ∈ X_m` this is `∫_cell ω = 0`.
2. *Smooth dual kernels lie in `H^1_{-m}`* (in particular bounded smooth periodic kernels with
   bounded gradient, for `m > 1/2`), *hence the unstable projection extends to `H^{-1}_m`*: every
   operator of smooth finite-rank form on `X_m` (`IsSmoothFiniteRank`, the named input) is the
   restriction of a bounded operator on `H^{-1}_m`.
3. *Reconstruction* (`B0583`): there is `C` (here `5`), independent of `c`, with
   `‖K_c ω‖_{H¹} ≤ C(1 + c)‖ω‖_{X_m}` for `c > 0`, `m > 1` and `∫_cell ω = 0`. -/
theorem zeroCirculation_projection_reconstruction :
    (∀ (c m : ℝ) (hm : 1 / 2 < m) (G : Fin 2 → X c m),
        HasZeroCirculation c m hm (curlSource c m G)) ∧
    (∀ (c m : ℝ) (hm : 1 / 2 < m) (w : X c m),
        HasZeroCirculation c m hm (sourceCLM c m w) ↔ ∫ x in cell c, w x = 0) ∧
    (∀ (c m : ℝ) (ψ : Plane → ℝ), IsSmoothDualKernel c m ψ → MemH1 c (-m) ψ) ∧
    (∀ (c m : ℝ), 1 / 2 < m → ∀ ψ : Plane → ℝ, ContDiff ℝ ∞ ψ →
        (∀ x : Plane, ψ (x.1 + c, x.2) = ψ x) → (∃ C, ∀ x, |ψ x| ≤ C) →
        (∀ j : Fin 2, ∃ C, ∀ x, |pd j ψ x| ≤ C) → IsSmoothDualKernel c m ψ) ∧
    (∀ (c m : ℝ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (P : X c m → V),
        IsSmoothFiniteRank c m P →
          ∃ Pe : Hneg c m →L[ℝ] V, ∀ f : X c m, Pe (sourceCLM c m f) = P f) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) [Fact (0 < c)] (m : ℝ) (hm : 1 < m) (w : X c m)
      (hcirc : ∫ x in cell c, w x = 0),
      B0583.HasWeakVelDeriv c 0 (B0583.velocity c hm.le w hcirc) (B0583.velGradQ c hm.le w) ∧
      B0583.HasWeakVelDeriv c 1 (B0583.velocity c hm.le w hcirc)
        (B0583.velGradEta c hm.le w hcirc) ∧
      B0583.h1Norm (B0583.velocity c hm.le w hcirc) (B0583.velGradQ c hm.le w)
        (B0583.velGradEta c hm.le w hcirc) ≤ C * (1 + c) * ‖w‖) :=
  ⟨fun _ _ hm G => hasZeroCirculation_curlSource hm G,
    fun _ _ hm w => hasZeroCirculation_sourceCLM_iff hm w,
    fun _ _ _ h => h.memH1,
    fun _ _ hm _ hψ hper hb hdb => isSmoothDualKernel_of_bounded hm hψ hper hb hdb,
    fun _ _ _ _ _ _ hP => exists_negExtension hP,
    B0583.velocity_reconstruction⟩

end UnforcedLeray.B0610
