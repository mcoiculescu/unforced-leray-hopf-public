import UnforcedLeray.Short.PartIIb.Tasks.EarlyBound.GreenVorticityUncurl.Needed
import UnforcedLeray.Short.PartIIb.Tasks.EarlyBound.GreenVorticityUncurl.SliceGlue
import UnforcedLeray.Short.PartIIb.Tasks.EarlyBound.GreenVorticityUncurl.CylKEqBS
import UnforcedLeray.Short.PartIIb.Tasks.EarlyBound.GreenVorticityUncurl.VelocityEq

/-!
# Part II-b, task `PartII-b:F6/2`: Green vorticity selector and Biot–Savart uncurl (`GreenVorticityUncurl`, SP 2219–2222, 2254–2268)

Source of record: `the November 2 reference manuscript`
(SP), lines 2219–2222 and 2254–2268, display `short-bg:early` at line 2263.

This file proves:
1. `eLpNorm_toCMerid_le` and `sliceH1Norm_le_of_coord_sum`: vector-norm triangle inequality on
   `CMerid = EuclideanSpace ℂ (Fin 2)` bounding `sliceH1Norm c z zq zη s` by the coordinate sum
   `∑ j : Fin 2, (‖z_j(s)‖_{L²(cell)} + ‖zq_j(s)‖_{L²(cell)} + ‖zη_j(s)‖_{L²(cell)})`, and hence by
   `ENNReal.ofReal (C_bs * c ^ N_bs * ‖ω s‖)` for any cylinder Biot–Savart slice `(u, uq, uη)`;
2. `green_omega_alpha_norm_le`, `mkContinuous_alphaMap`, and `sliceH1Norm_add_alpha_le`:
   combining the Green selector `L¹ → L^∞` estimate
   `‖ω s‖ + ‖α‖ ≤ C_green * e^{a' p.H} * ∫_0^{p.H} ‖f t‖ dt` with the curl-source `L¹` bound
   `∫_0^{p.H} ‖curlSourceOf F t‖ dt ≤ C_L1 * ‖F‖` to promote `αOf : HpR p.c →ₗ[ℝ] E2` to a
   continuous linear map `αMap : HpR p.c →L[ℝ] E2` and establish the uniform slice bound
   `sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s + ENNReal.ofReal ‖αMap F‖ ≤
     ENNReal.ofReal ((C_bs * p.c ^ N_bs + 1) * C_green * e^{a' p.H} * C_L1 * ‖F‖)`;
3. `isMeridionalCorrectionOn_zero`, `isMeridionalCorrectionOn_add`, `isMeridionalCorrectionOn_smul_real`:
   full `ℝ`-linear closure of `entranceVorticityComb` and `IsMeridionalCorrectionOn`;
4. `canonical_bs_ae_eq_of_hbs`: uniqueness transfer (`Short.IIIa.CTE.isBiotSavart_unique` +
   `LinearBodySourceHelp.hasWeakCellDerivC_ae_zero_of_ae_zero`) proving that the canonical linear
   `B0583.velocity` / `velGradQ` / `velGradEta` operators agree a.e. on `B0579.cell c` with any
   existential `CylinderBiotSavartH1` witness `(u, uq, uη)` and inherit its `C_bs * c ^ N_bs * ‖w‖`
   coordinate `H¹` bound;
5. `tendsto_omega_zero_of_duhamel` and `initial_curl_of_tendsto_omega`: strong `Xmc` right-continuity
   `ω s → ω 0` as `s → 0+` from the propagator Duhamel formula and resulting `initial_curl`
   convergence in `L²(cell)`;
6. `GreenBiotSavartUncurlStep` and `greenVorticityUncurl_of`: conditional assembly of
   `GreenVorticityUncurl`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint

namespace GreenUncurlHelp

/-! ## 1. `CMerid` slice `L²(cell)` and `sliceH1Norm` bounds from coordinate `L²(cell)` bounds -/

/-- Lift a coordinate-pair function `v : B0579.Plane → Fin 2 → ℂ` to `B0579.Plane → CMerid`. -/
def toCMerid (v : B0579.Plane → Fin 2 → ℂ) (x : B0579.Plane) : CMerid :=
  WithLp.toLp 2 (v x)

/-- Single-coordinate vector in `CMerid = EuclideanSpace ℂ (Fin 2)`. -/
def cMeridSingle (j : Fin 2) (z : ℂ) : CMerid :=
  WithLp.toLp 2 (fun k : Fin 2 => if k = j then z else 0)

lemma toCMerid_eq_add_single (v : B0579.Plane → Fin 2 → ℂ) :
    toCMerid v =
      (fun x => cMeridSingle 0 (v x 0)) +
        (fun x => cMeridSingle 1 (v x 1)) := by
  funext x
  ext j
  fin_cases j <;> simp [toCMerid, cMeridSingle]

lemma norm_single_cMerid (j : Fin 2) (z : ℂ) :
    ‖cMeridSingle j z‖ = ‖z‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  fin_cases j <;> simp [cMeridSingle]

lemma aestronglyMeasurable_single_cMerid {μ : Measure B0579.Plane} (j : Fin 2)
    {f : B0579.Plane → ℂ} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => cMeridSingle j (f x)) μ := by
  let L : ℂ →L[ℂ] CMerid :=
    ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ)
      (cMeridSingle j (1 : ℂ))
  have hL : (fun x => cMeridSingle j (f x)) = fun x => L (f x) := by
    funext x
    ext k
    fin_cases j <;> fin_cases k <;> simp [L, cMeridSingle]
  rw [hL]
  exact L.continuous.comp_aestronglyMeasurable hf

lemma eLpNorm_single_cMerid (j : Fin 2) (f : B0579.Plane → ℂ) (μ : Measure B0579.Plane) :
    eLpNorm (fun x => cMeridSingle j (f x)) 2 μ = eLpNorm f 2 μ := by
  refine eLpNorm_congr_norm_ae (Eventually.of_forall fun x => ?_)
  exact norm_single_cMerid j (f x)

/-- For any `v : B0579.Plane → Fin 2 → ℂ` with `AEStronglyMeasurable` components on `μ`,
`eLpNorm (toCMerid v) 2 μ ≤ eLpNorm (v · 0) 2 μ + eLpNorm (v · 1) 2 μ`. -/
theorem eLpNorm_toCMerid_le {μ : Measure B0579.Plane} {v : B0579.Plane → Fin 2 → ℂ}
    (hv0 : AEStronglyMeasurable (fun x => v x 0) μ)
    (hv1 : AEStronglyMeasurable (fun x => v x 1) μ) :
    eLpNorm (toCMerid v) 2 μ ≤
      eLpNorm (fun x => v x 0) 2 μ + eLpNorm (fun x => v x 1) 2 μ := by
  rw [toCMerid_eq_add_single]
  have hm0 := aestronglyMeasurable_single_cMerid 0 hv0
  have hm1 := aestronglyMeasurable_single_cMerid 1 hv1
  calc eLpNorm ((fun x => cMeridSingle 0 (v x 0)) +
          (fun x => cMeridSingle 1 (v x 1))) 2 μ
      ≤ eLpNorm (fun x => cMeridSingle 0 (v x 0)) 2 μ +
          eLpNorm (fun x => cMeridSingle 1 (v x 1)) 2 μ :=
        eLpNorm_add_le hm0 hm1 one_le_two
    _ = eLpNorm (fun x => v x 0) 2 μ + eLpNorm (fun x => v x 1) 2 μ := by
        rw [eLpNorm_single_cMerid 0, eLpNorm_single_cMerid 1]

/-- If at age `s`, `(z (s, ·), zq (s, ·), zη (s, ·))` agree a.e. on `B0579.cell c` with
`(toCMerid u, toCMerid uq, toCMerid uη)` where `u, uq, uη` have `AEStronglyMeasurable` components on
`B0579.cell c`, then `sliceH1Norm c z zq zη s` is bounded by the coordinate `H¹` sum of `u, uq, uη`. -/
theorem sliceH1Norm_le_of_coord_sum {c s : ℝ} {z zq zη : CProf}
    {u uq uη : B0579.Plane → Fin 2 → ℂ}
    (hu_m : ∀ j : Fin 2, AEStronglyMeasurable (fun x => u x j) (volume.restrict (B0579.cell c)))
    (huq_m : ∀ j : Fin 2, AEStronglyMeasurable (fun x => uq x j) (volume.restrict (B0579.cell c)))
    (huη_m : ∀ j : Fin 2, AEStronglyMeasurable (fun x => uη x j) (volume.restrict (B0579.cell c)))
    (hz_ae : (fun x => z (s, x)) =ᵐ[volume.restrict (B0579.cell c)] toCMerid u)
    (hzq_ae : (fun x => zq (s, x)) =ᵐ[volume.restrict (B0579.cell c)] toCMerid uq)
    (hzη_ae : (fun x => zη (s, x)) =ᵐ[volume.restrict (B0579.cell c)] toCMerid uη) :
    sliceH1Norm c z zq zη s ≤
      ∑ j : Fin 2,
        (eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun x => uq x j) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun x => uη x j) 2 (volume.restrict (B0579.cell c))) := by
  set μ := volume.restrict (B0579.cell c)
  unfold sliceH1Norm
  rw [eLpNorm_congr_ae hz_ae, eLpNorm_congr_ae hzq_ae, eLpNorm_congr_ae hzη_ae, Fin.sum_univ_two]
  have h1 := eLpNorm_toCMerid_le (hu_m 0) (hu_m 1)
  have h2 := eLpNorm_toCMerid_le (huq_m 0) (huq_m 1)
  have h3 := eLpNorm_toCMerid_le (huη_m 0) (huη_m 1)
  calc eLpNorm (toCMerid u) 2 μ + eLpNorm (toCMerid uq) 2 μ + eLpNorm (toCMerid uη) 2 μ
      ≤ (eLpNorm (fun x => u x 0) 2 μ + eLpNorm (fun x => u x 1) 2 μ) +
          (eLpNorm (fun x => uq x 0) 2 μ + eLpNorm (fun x => uq x 1) 2 μ) +
          (eLpNorm (fun x => uη x 0) 2 μ + eLpNorm (fun x => uη x 1) 2 μ) :=
        add_le_add (add_le_add h1 h2) h3
    _ = (eLpNorm (fun x => u x 0) 2 μ + eLpNorm (fun x => uq x 0) 2 μ +
            eLpNorm (fun x => uη x 0) 2 μ) +
          (eLpNorm (fun x => u x 1) 2 μ + eLpNorm (fun x => uq x 1) 2 μ +
            eLpNorm (fun x => uη x 1) 2 μ) := by
        abel

/-! ## 2. Green selector `L¹ → L^∞` bounds and continuous linear promotion of `αMap` -/

/-- Combining the Green selector bound `‖ω s‖ + ‖α‖ ≤ C_green * e^{a' H} * ∫_0^H ‖f t‖ dt` with the
source `L¹` bound `∫_0^H ‖f t‖ dt ≤ C_L1 * ‖F‖` bounds `‖ω s‖ + ‖α‖`, `‖ω s‖`, and `‖α‖` by
`C_green * e^{a' H} * C_L1 * ‖F‖`. -/
theorem green_omega_alpha_norm_le
    {c m H a' C_green C_L1 : ℝ} (hC_green : 0 < C_green)
    {F : HpR c} {f : ℝ → Xmc c m} {ω : ℝ → Xmc c m} {α : E2}
    (h_green : ∀ s ∈ Icc 0 H, ‖ω s‖ + ‖α‖ ≤ C_green * Real.exp (a' * H) * ∫ t in Ioc 0 H, ‖f t‖)
    (h_L1 : ∫ t in Ioc 0 H, ‖f t‖ ≤ C_L1 * ‖F‖)
    {s : ℝ} (hs : s ∈ Icc 0 H) :
    ‖ω s‖ + ‖α‖ ≤ C_green * Real.exp (a' * H) * C_L1 * ‖F‖ ∧
    ‖ω s‖ ≤ C_green * Real.exp (a' * H) * C_L1 * ‖F‖ ∧
    ‖α‖ ≤ C_green * Real.exp (a' * H) * C_L1 * ‖F‖ := by
  have h_sum : ‖ω s‖ + ‖α‖ ≤ C_green * Real.exp (a' * H) * C_L1 * ‖F‖ := by
    calc ‖ω s‖ + ‖α‖
        ≤ C_green * Real.exp (a' * H) * ∫ t in Ioc 0 H, ‖f t‖ := h_green s hs
      _ ≤ C_green * Real.exp (a' * H) * (C_L1 * ‖F‖) :=
          mul_le_mul_of_nonneg_left h_L1 (by positivity)
      _ = C_green * Real.exp (a' * H) * C_L1 * ‖F‖ := by ring
  exact ⟨h_sum, (le_add_of_nonneg_right (norm_nonneg α)).trans h_sum,
    (le_add_of_nonneg_left (norm_nonneg (ω s))).trans h_sum⟩

/-- Promote a linear map `αOf : HpR c →ₗ[ℝ] E2` satisfying
`‖αOf F‖ ≤ C_green * Real.exp (a' * H) * C_L1 * ‖F‖` to a continuous linear map
`HpR c →L[ℝ] E2`. -/
def mkContinuous_alphaMap {c H a' C_green C_L1 : ℝ}
    (αOf : HpR c →ₗ[ℝ] E2)
    (h_bd : ∀ F : HpR c, ‖αOf F‖ ≤ C_green * Real.exp (a' * H) * C_L1 * ‖F‖) :
    HpR c →L[ℝ] E2 :=
  αOf.mkContinuous (C_green * Real.exp (a' * H) * C_L1) h_bd

@[simp] lemma mkContinuous_alphaMap_apply {c H a' C_green C_L1 : ℝ}
    (αOf : HpR c →ₗ[ℝ] E2)
    (h_bd : ∀ F : HpR c, ‖αOf F‖ ≤ C_green * Real.exp (a' * H) * C_L1 * ‖F‖)
    (F : HpR c) :
    mkContinuous_alphaMap αOf h_bd F = αOf F := rfl

/-- If `sliceH1Norm c z zq zη s ≤ ENNReal.ofReal (C_bs * c ^ N_bs * ‖ω s‖)` and both `‖ω s‖` and
`‖α‖` are bounded by `C_green * e^{a' H} * C_L1 * ‖F‖`, then
`sliceH1Norm c z zq zη s + ENNReal.ofReal ‖α‖ ≤ ENNReal.ofReal ((C_bs * c ^ N_bs + 1) * C_green * e^{a' H} * C_L1 * ‖F‖)`. -/
theorem sliceH1Norm_add_alpha_le
    {c m H a' C_bs C_green C_L1 : ℝ} {N_bs : ℕ}
    (hc0 : 0 ≤ c) (hC_bs : 0 < C_bs) (hC_green : 0 < C_green) (hC_L1 : 0 ≤ C_L1)
    {F : HpR c} {z zq zη : CProf} {w : Xmc c m} {α : E2} {s : ℝ}
    (h_slice : sliceH1Norm c z zq zη s ≤ ENNReal.ofReal (C_bs * c ^ N_bs * ‖w‖))
    (hw_bd : ‖w‖ ≤ C_green * Real.exp (a' * H) * C_L1 * ‖F‖)
    (hα_bd : ‖α‖ ≤ C_green * Real.exp (a' * H) * C_L1 * ‖F‖) :
    sliceH1Norm c z zq zη s + ENNReal.ofReal ‖α‖ ≤
      ENNReal.ofReal ((C_bs * c ^ N_bs + 1) * C_green * Real.exp (a' * H) * C_L1 * ‖F‖) := by
  set M : ℝ := C_green * Real.exp (a' * H) * C_L1 * ‖F‖
  have hM_nn : 0 ≤ M := by dsimp [M]; positivity
  have hCbs_c_nn : 0 ≤ C_bs * c ^ N_bs := mul_nonneg hC_bs.le (pow_nonneg hc0 N_bs)
  have h1 : sliceH1Norm c z zq zη s ≤ ENNReal.ofReal (C_bs * c ^ N_bs * M) :=
    h_slice.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hw_bd hCbs_c_nn))
  have h2 : ENNReal.ofReal ‖α‖ ≤ ENNReal.ofReal M :=
    ENNReal.ofReal_le_ofReal hα_bd
  calc sliceH1Norm c z zq zη s + ENNReal.ofReal ‖α‖
      ≤ ENNReal.ofReal (C_bs * c ^ N_bs * M) + ENNReal.ofReal M := add_le_add h1 h2
    _ = ENNReal.ofReal (C_bs * c ^ N_bs * M + M) :=
        (ENNReal.ofReal_add (mul_nonneg hCbs_c_nn hM_nn) hM_nn).symm
    _ = ENNReal.ofReal ((C_bs * c ^ N_bs + 1) * C_green * Real.exp (a' * H) * C_L1 * ‖F‖) := by
        congr 1
        dsimp [M]
        ring

/-! ## 3. `ℝ`-linear closure of `entranceVorticityComb` and `IsMeridionalCorrectionOn` -/

lemma entranceVorticityComb_zero (p : Params) (x : B0579.Plane) :
    entranceVorticityComb p 0 x = 0 := by
  simp [entranceVorticityComb]

lemma entranceVorticityComb_add (p : Params) (α₁ α₂ : E2) (x : B0579.Plane) :
    entranceVorticityComb p (α₁ + α₂) x =
      entranceVorticityComb p α₁ x + entranceVorticityComb p α₂ x := by
  simp only [entranceVorticityComb, PiLp.add_apply, add_mul, Finset.sum_add_distrib]

lemma entranceVorticityComb_smul_real (p : Params) (a : ℝ) (α : E2) (x : B0579.Plane) :
    entranceVorticityComb p (a • α) x = a * entranceVorticityComb p α x := by
  simp only [entranceVorticityComb, PiLp.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]

lemma isMeridionalCorrectionOn_zero (p : Params) (T : ℝ) :
    IsMeridionalCorrectionOn p T 0 0 0 0 0 := by
  refine ⟨LinearBodySourceHelp.qPeriodic_zero p.c,
    LinearBodySourceHelp.hasWeakVec_zero vQ0 dZero,
    LinearBodySourceHelp.hasWeakVec_zero vEta dZero,
    fun φ _ _ => ⟨by simp, by simp⟩,
    fun Ψ _ _ => ?_,
    ?_⟩
  · rw [LinearBodySourceHelp.flatBv_zero]
    have h0 : cdot (0 : CProf) Ψ = 0 := by funext x; simp [cdot]
    rw [h0]
    refine ⟨by simp, integrable_zero _ _ _, integrable_zero _ _ _, by simp⟩
  · have hfun : (fun s : ℝ => eLpNorm
        (fun x => profCurl 0 0 (s, x) - ((entranceVorticityComb p 0 x : ℝ) : ℂ))
        2 (B0579.cellMeasure p.c 0)) = fun _ => 0 := by
      funext s
      have hx : (fun x : B0579.Plane =>
          profCurl (0 : CProf) 0 (s, x) - ((entranceVorticityComb p 0 x : ℝ) : ℂ)) = 0 := by
        funext x
        simp [profCurl, entranceVorticityComb_zero]
      rw [hx, eLpNorm_zero]
    rw [hfun]
    exact tendsto_const_nhds

lemma isMeridionalCorrectionOn_smul_real {p : Params} {T : ℝ} (a : ℝ)
    {g z zq zη : CProf} {α : E2}
    (h : IsMeridionalCorrectionOn p T g z zq zη α) :
    IsMeridionalCorrectionOn p T (a • g) (a • z) (a • zq) (a • zη) (a • α) := by
  refine ⟨LinearBodySourceHelp.qPeriodic_smul_real a h.periodic,
    LinearBodySourceHelp.hasWeakVec_smul_real a h.weak_q,
    LinearBodySourceHelp.hasWeakVec_smul_real a h.weak_eta,
    fun φ hφ hsupp => ?_,
    fun Ψ hΨ hsupp => ?_,
    ?_⟩
  · obtain ⟨hI, h0⟩ := h.solenoidal φ hφ hsupp
    have hfun : (fun x : Coord => (a • z) x 0 * (cpd 1 φ x : ℂ) +
        (a • z) x 1 * (cpd 2 φ x : ℂ)) =
        fun x => (a : ℂ) * (z x 0 * (cpd 1 φ x : ℂ) + z x 1 * (cpd 2 φ x : ℂ)) := by
      funext x; simp only [Pi.smul_apply, PiLp.smul_apply, Complex.real_smul]; ring
    rw [hfun]
    refine ⟨hI.const_mul (a : ℂ), ?_⟩
    rw [integral_const_mul, h0, mul_zero]
  · obtain ⟨hIz, hIB, hIg, hEq⟩ := h.equation Ψ hΨ hsupp
    rw [LinearBodySourceHelp.flatBv_smul_real]
    have hfunZ : (fun x : Coord => ∑ i : Fin 2, (a • z) x i * meridTranspose p.ν Ψ x i) =
        fun x => (a : ℂ) * (∑ i : Fin 2, z x i * meridTranspose p.ν Ψ x i) := by
      funext x
      simp only [Pi.smul_apply, PiLp.smul_apply, Complex.real_smul, mul_assoc, ← Finset.mul_sum]
    have hfunB : cdot (a • flatBv p.train z zq zη) Ψ =
        fun x => (a : ℂ) * cdot (flatBv p.train z zq zη) Ψ x := by
      funext x
      simp only [cdot, Pi.smul_apply, PiLp.smul_apply, Complex.real_smul, mul_assoc, ← Finset.mul_sum]
    have hfunG : cdot (a • g) Ψ = fun x => (a : ℂ) * cdot g Ψ x := by
      funext x
      simp only [cdot, Pi.smul_apply, PiLp.smul_apply, Complex.real_smul, mul_assoc, ← Finset.mul_sum]
    rw [hfunZ, hfunB, hfunG]
    refine ⟨hIz.const_mul (a : ℂ), hIB.const_mul (a : ℂ), hIg.const_mul (a : ℂ), ?_⟩
    have hsum : (fun x : Coord => ∑ i : Fin 2, (a • z) x i * meridTranspose p.ν Ψ x i +
        (fun y => (a : ℂ) * cdot (flatBv p.train z zq zη) Ψ y) x) =
        fun x => (a : ℂ) * ((∑ i : Fin 2, z x i * meridTranspose p.ν Ψ x i) +
          cdot (flatBv p.train z zq zη) Ψ x) := by
      funext x
      simp only [Pi.smul_apply, PiLp.smul_apply, Complex.real_smul, mul_assoc, ← Finset.mul_sum]
      ring
    rw [hsum, integral_const_mul, integral_const_mul, hEq]
  · have hfun : (fun s : ℝ => eLpNorm
        (fun x => profCurl (a • zq) (a • zη) (s, x) -
          ((entranceVorticityComb p (a • α) x : ℝ) : ℂ))
        2 (B0579.cellMeasure p.c 0)) =
        fun s : ℝ => ‖(a : ℂ)‖ₑ * eLpNorm
          (fun x => profCurl zq zη (s, x) - ((entranceVorticityComb p α x : ℝ) : ℂ))
          2 (B0579.cellMeasure p.c 0) := by
      funext s
      have hx : (fun x : B0579.Plane => profCurl (a • zq) (a • zη) (s, x) -
          ((entranceVorticityComb p (a • α) x : ℝ) : ℂ)) =
          (a : ℂ) • (fun x => profCurl zq zη (s, x) - ((entranceVorticityComb p α x : ℝ) : ℂ)) := by
        funext x
        rw [LinearBodySourceHelp.profCurl_smul_real, entranceVorticityComb_smul_real]
        push_cast
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [hx, eLpNorm_const_smul]
    rw [hfun, ← mul_zero ‖(a : ℂ)‖ₑ]
    exact ENNReal.Tendsto.const_mul h.initial_curl (Or.inr enorm_ne_top)

lemma isMeridionalCorrectionOn_add {p : Params} {T : ℝ}
    {g₁ z₁ zq₁ zη₁ g₂ z₂ zq₂ zη₂ : CProf} {α₁ α₂ : E2}
    (hm₁ : ∀ᶠ s in 𝓝[Ioi 0] 0, AEStronglyMeasurable
      (fun x => profCurl zq₁ zη₁ (s, x) - ((entranceVorticityComb p α₁ x : ℝ) : ℂ))
      (B0579.cellMeasure p.c 0))
    (hm₂ : ∀ᶠ s in 𝓝[Ioi 0] 0, AEStronglyMeasurable
      (fun x => profCurl zq₂ zη₂ (s, x) - ((entranceVorticityComb p α₂ x : ℝ) : ℂ))
      (B0579.cellMeasure p.c 0))
    (h₁ : IsMeridionalCorrectionOn p T g₁ z₁ zq₁ zη₁ α₁)
    (h₂ : IsMeridionalCorrectionOn p T g₂ z₂ zq₂ zη₂ α₂) :
    IsMeridionalCorrectionOn p T (g₁ + g₂) (z₁ + z₂) (zq₁ + zq₂) (zη₁ + zη₂) (α₁ + α₂) := by
  refine ⟨LinearBodySourceHelp.qPeriodic_add h₁.periodic h₂.periodic,
    F10Help.hasWeakVec_add' h₁.weak_q h₂.weak_q,
    F10Help.hasWeakVec_add' h₁.weak_eta h₂.weak_eta,
    fun φ hφ hsupp => ?_,
    fun Ψ hΨ hsupp => ?_,
    ?_⟩
  · obtain ⟨hI₁, h0₁⟩ := h₁.solenoidal φ hφ hsupp
    obtain ⟨hI₂, h0₂⟩ := h₂.solenoidal φ hφ hsupp
    have hfun : (fun x : Coord => (z₁ + z₂) x 0 * (cpd 1 φ x : ℂ) +
        (z₁ + z₂) x 1 * (cpd 2 φ x : ℂ)) =
        fun x => (z₁ x 0 * (cpd 1 φ x : ℂ) + z₁ x 1 * (cpd 2 φ x : ℂ)) +
          (z₂ x 0 * (cpd 1 φ x : ℂ) + z₂ x 1 * (cpd 2 φ x : ℂ)) := by
      funext x; simp only [Pi.add_apply, PiLp.add_apply]; ring
    rw [hfun]
    refine ⟨hI₁.add hI₂, ?_⟩
    rw [integral_add hI₁ hI₂, h0₁, h0₂, add_zero]
  · obtain ⟨hIz₁, hIB₁, hIg₁, hEq₁⟩ := h₁.equation Ψ hΨ hsupp
    obtain ⟨hIz₂, hIB₂, hIg₂, hEq₂⟩ := h₂.equation Ψ hΨ hsupp
    rw [LinearBodySourceHelp.flatBv_add]
    have hfunZ : (fun x : Coord => ∑ i : Fin 2, (z₁ + z₂) x i * meridTranspose p.ν Ψ x i) =
        fun x => (∑ i : Fin 2, z₁ x i * meridTranspose p.ν Ψ x i) +
          (∑ i : Fin 2, z₂ x i * meridTranspose p.ν Ψ x i) := by
      funext x
      simp only [Pi.add_apply, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
    have hfunB : cdot (flatBv p.train z₁ zq₁ zη₁ + flatBv p.train z₂ zq₂ zη₂) Ψ =
        fun x => cdot (flatBv p.train z₁ zq₁ zη₁) Ψ x +
          cdot (flatBv p.train z₂ zq₂ zη₂) Ψ x := by
      funext x
      simp only [cdot, Pi.add_apply, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
    have hfunG : cdot (g₁ + g₂) Ψ = fun x => cdot g₁ Ψ x + cdot g₂ Ψ x := by
      funext x
      simp only [cdot, Pi.add_apply, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
    rw [hfunZ, hfunB, hfunG]
    refine ⟨hIz₁.add hIz₂, hIB₁.add hIB₂, hIg₁.add hIg₂, ?_⟩
    have hsum : (fun x : Coord => ∑ i : Fin 2, (z₁ + z₂) x i * meridTranspose p.ν Ψ x i +
        (fun y => cdot (flatBv p.train z₁ zq₁ zη₁) Ψ y +
          cdot (flatBv p.train z₂ zq₂ zη₂) Ψ y) x) =
        fun x => ((∑ i : Fin 2, z₁ x i * meridTranspose p.ν Ψ x i) +
            cdot (flatBv p.train z₁ zq₁ zη₁) Ψ x) +
          ((∑ i : Fin 2, z₂ x i * meridTranspose p.ν Ψ x i) +
            cdot (flatBv p.train z₂ zq₂ zη₂) Ψ x) := by
      funext x
      simp only [Pi.add_apply, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
      ring
    have hIzB₁ : Integrable (fun x : Coord =>
        (∑ i : Fin 2, z₁ x i * meridTranspose p.ν Ψ x i) +
          cdot (flatBv p.train z₁ zq₁ zη₁) Ψ x) := hIz₁.add hIB₁
    have hIzB₂ : Integrable (fun x : Coord =>
        (∑ i : Fin 2, z₂ x i * meridTranspose p.ν Ψ x i) +
          cdot (flatBv p.train z₂ zq₂ zη₂) Ψ x) := hIz₂.add hIB₂
    rw [hsum, integral_add hIzB₁ hIzB₂, integral_add hIg₁ hIg₂, hEq₁, hEq₂]
  · have h00 : Tendsto (fun s =>
        eLpNorm (fun x => profCurl zq₁ zη₁ (s, x) - ((entranceVorticityComb p α₁ x : ℝ) : ℂ))
          2 (B0579.cellMeasure p.c 0) +
        eLpNorm (fun x => profCurl zq₂ zη₂ (s, x) - ((entranceVorticityComb p α₂ x : ℝ) : ℂ))
          2 (B0579.cellMeasure p.c 0)) (𝓝[Ioi 0] 0) (𝓝 0) := by
      simpa using h₁.initial_curl.add h₂.initial_curl
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h00
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [hm₁, hm₂] with s hs₁ hs₂
    have hx : (fun x : B0579.Plane => profCurl (zq₁ + zq₂) (zη₁ + zη₂) (s, x) -
        ((entranceVorticityComb p (α₁ + α₂) x : ℝ) : ℂ)) =
        (fun x => profCurl zq₁ zη₁ (s, x) - ((entranceVorticityComb p α₁ x : ℝ) : ℂ)) +
        (fun x => profCurl zq₂ zη₂ (s, x) - ((entranceVorticityComb p α₂ x : ℝ) : ℂ)) := by
      funext x
      rw [LinearBodySourceHelp.profCurl_add, entranceVorticityComb_add]
      simp only [Pi.add_apply]
      push_cast
      ring
    rw [hx]
    exact eLpNorm_add_le hs₁ hs₂ one_le_two

/-! ## 4. Canonical `B0583` Biot–Savart uniqueness transfer and Duhamel `s → 0+` trace -/

/-- Any weak cylinder derivative `g` (`IIIa.HasWeakCellDerivC c k φ g`) is a.e. strongly measurable
on `B0579.cell c` (via `η`-cutoff cylinder tests `b_n(η)`). -/
lemma aestronglyMeasurable_of_hasWeakCellDerivC {c : ℝ} {k : Fin 2} {φ g : ℝ × ℝ → ℂ}
    (hg : IIIa.HasWeakCellDerivC c k φ g) :
    AEStronglyMeasurable g (volume.restrict (B0579.cell c)) := by
  let b : ℕ → ContDiffBump (0 : ℝ) := fun n =>
    ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩
  let ψ : ℕ → B0579.Plane → ℝ := fun n x => b n x.2
  have hψ : ∀ n, B0579.IsCylTest c (ψ n) := fun n =>
    ⟨(b n).contDiff.comp contDiff_snd, fun _ => rfl, ⟨(n : ℝ) + 2, fun x hx =>
      (b n).zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hx.le)⟩⟩
  have hm : ∀ n, AEStronglyMeasurable (fun x => g x * (ψ n x : ℂ))
      (volume.restrict (B0579.cell c)) :=
    fun n => ((hg.1 (ψ n) (hψ n)).2).aestronglyMeasurable
  refine aestronglyMeasurable_of_tendsto_ae atTop hm (Eventually.of_forall fun x => ?_)
  refine tendsto_atTop_of_eventually_const (i₀ := ⌈|x.2|⌉₊) fun n hn => ?_
  have hle : |x.2| ≤ (n : ℝ) + 1 := by
    have : (⌈|x.2|⌉₊ : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
    linarith [Nat.le_ceil |x.2|]
  have hone : ψ n x = 1 := (b n).one_of_mem_closedBall (by
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact hle)
  simp [hone]

lemma hasWeakCellDerivC_sub {c : ℝ} {k : Fin 2} {φ₁ φ₂ g₁ g₂ : ℝ × ℝ → ℂ}
    (h₁ : IIIa.HasWeakCellDerivC c k φ₁ g₁)
    (h₂ : IIIa.HasWeakCellDerivC c k φ₂ g₂) :
    IIIa.HasWeakCellDerivC c k (fun x => φ₁ x - φ₂ x) (fun x => g₁ x - g₂ x) := by
  have hL_eq : ∀ ψ : B0579.Plane → ℝ, (fun x => (φ₁ x - φ₂ x) * (B0579.pd k ψ x : ℂ)) =
      fun x => φ₁ x * (B0579.pd k ψ x : ℂ) - φ₂ x * (B0579.pd k ψ x : ℂ) := by
    intro ψ; funext x; ring
  have hR_eq : ∀ ψ : B0579.Plane → ℝ, (fun x => (g₁ x - g₂ x) * (ψ x : ℂ)) =
      fun x => g₁ x * (ψ x : ℂ) - g₂ x * (ψ x : ℂ) := by
    intro ψ; funext x; ring
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · rw [hL_eq ψ]; exact (h₁.1 ψ hψ).1.sub (h₂.1 ψ hψ).1
  · rw [hR_eq ψ]; exact (h₁.1 ψ hψ).2.sub (h₂.1 ψ hψ).2
  · rw [hL_eq ψ, hR_eq ψ, integral_sub (h₁.1 ψ hψ).1 (h₂.1 ψ hψ).1,
      integral_sub (h₁.1 ψ hψ).2 (h₂.1 ψ hψ).2, h₁.2 ψ hψ, h₂.2 ψ hψ]
    ring

/-- **Canonical Biot–Savart uniqueness transfer**: for `1 ≤ c`, `1 < m`, and `w : Xmc c m` with
`HasZeroCirculationR c w`, the canonical `B0583` triple
`(B0583.velocity c hm.le w hw.2, B0583.velGradQ c hm.le w, B0583.velGradEta c hm.le w hw.2)`
agrees `volume.restrict (B0579.cell c)`-a.e. on both components with ANY witness `(u, uq, uη)` of
`IIIa.IsBiotSavart c (fun x => ((w x : ℝ) : ℂ)) u` + weak cell derivatives + coordinate `H¹` bound
`≤ ENNReal.ofReal B`, and therefore inherits that exact coordinate `H¹` bound. -/
theorem canonical_bs_ae_eq_of_hbs {c m B : ℝ} (hc1 : 1 ≤ c) (hm : 1 < m)
    {w : Xmc c m} (hw : HasZeroCirculationR c w)
    {u uq uη : B0579.Plane → Fin 2 → ℂ}
    (hu_bs : IIIa.IsBiotSavart c (fun x => ((w x : ℝ) : ℂ)) u)
    (hu_deriv : ∀ j : Fin 2, IIIa.HasWeakCellDerivC c 0 (fun x => u x j) (fun x => uq x j) ∧
      IIIa.HasWeakCellDerivC c 1 (fun x => u x j) (fun x => uη x j))
    (hu_bd : (∑ j : Fin 2,
      (eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => uq x j) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => uη x j) 2 (volume.restrict (B0579.cell c)))) ≤
      ENNReal.ofReal B) :
    haveI : Fact (0 < c) := ⟨by linarith⟩
    let uLp := B0583.velocity c hm.le w hw.2
    let uqLp := B0583.velGradQ c hm.le w
    let uηLp := B0583.velGradEta c hm.le w hw.2
    (∀ j : Fin 2,
      (fun x => (uLp : B0579.Plane → B0581.Vel) x j) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => u x j)) ∧
    (∀ j : Fin 2,
      (fun x => (uqLp : B0579.Plane → B0581.Vel) x j) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => uq x j)) ∧
    (∀ j : Fin 2,
      (fun x => (uηLp : B0579.Plane → B0581.Vel) x j) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => uη x j)) ∧
    (∑ j : Fin 2,
      (eLpNorm (fun x => (uLp : B0579.Plane → B0581.Vel) x j) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => (uqLp : B0579.Plane → B0581.Vel) x j) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => (uηLp : B0579.Plane → B0581.Vel) x j) 2 (volume.restrict (B0579.cell c)))) ≤
      ENNReal.ofReal B := by
  have hc0 : 0 < c := by linarith
  have : Fact (0 < c) := ⟨hc0⟩
  set uLp := B0583.velocity c hm.le w hw.2
  set uqLp := B0583.velGradQ c hm.le w
  set uηLp := B0583.velGradEta c hm.le w hw.2
  have hCan_bs : IIIa.IsBiotSavart c (fun x => ((w x : ℝ) : ℂ))
      (fun x j => (uLp : B0579.Plane → B0581.Vel) x j) :=
    Short.IIIa.CTE.velocityIsBiotSavart c m hm w hw.2
  have hu_vec := Short.IIIa.CTE.isBiotSavart_unique c hc0 (fun x => ((w x : ℝ) : ℂ))
    (fun x j => (uLp : B0579.Plane → B0581.Vel) x j) u hCan_bs hu_bs
  have hu_eq : ∀ j : Fin 2,
      (fun x => (uLp : B0579.Plane → B0581.Vel) x j) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => u x j) :=
    fun j => hu_vec.mono fun x hx => congrFun hx j
  have hsum_lt : (∑ j : Fin 2,
      (eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => uq x j) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => uη x j) 2 (volume.restrict (B0579.cell c)))) < ⊤ :=
    lt_of_le_of_lt hu_bd ENNReal.ofReal_lt_top
  have hterm_lt : ∀ j : Fin 2,
      eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => uq x j) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => uη x j) 2 (volume.restrict (B0579.cell c)) < ⊤ := by
    rw [Fin.sum_univ_two] at hsum_lt
    intro j
    fin_cases j
    · exact lt_of_le_of_lt le_self_add hsum_lt
    · exact lt_of_le_of_lt le_add_self hsum_lt
  have huq_eq : ∀ j : Fin 2,
      (fun x => (uqLp : B0579.Plane → B0581.Vel) x j) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => uq x j) := by
    intro j
    have hm_can : MemLp (fun x => (uqLp : B0579.Plane → B0581.Vel) x j) 2
        (volume.restrict (B0579.cell c)) :=
      ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj j : B0581.Vel →L[ℂ] ℂ) (Lp.memLp uqLp)
    have hm_uq : MemLp (fun x => uq x j) 2 (volume.restrict (B0579.cell c)) :=
      ⟨aestronglyMeasurable_of_hasWeakCellDerivC (hu_deriv j).1,
        lt_of_le_of_lt (le_add_self.trans le_self_add) (hterm_lt j)⟩
    have hw_sub := hasWeakCellDerivC_sub
      (hasWeakCellDerivC_of_hasWeakVelDeriv (j := j) (B0583.hasWeakVelDeriv_velocity_q c hm.le w hw.2))
      (hu_deriv j).1
    have hdiff0 := LinearBodySourceHelp.hasWeakCellDerivC_ae_zero_of_ae_zero hc0
      ((hu_eq j).mono fun x hx => sub_eq_zero.mpr hx) (hm_can.sub hm_uq) hw_sub
    exact hdiff0.mono fun x hx => sub_eq_zero.mp hx
  have huη_eq : ∀ j : Fin 2,
      (fun x => (uηLp : B0579.Plane → B0581.Vel) x j) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => uη x j) := by
    intro j
    have hm_can : MemLp (fun x => (uηLp : B0579.Plane → B0581.Vel) x j) 2
        (volume.restrict (B0579.cell c)) :=
      ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj j : B0581.Vel →L[ℂ] ℂ) (Lp.memLp uηLp)
    have hm_uη : MemLp (fun x => uη x j) 2 (volume.restrict (B0579.cell c)) :=
      ⟨aestronglyMeasurable_of_hasWeakCellDerivC (hu_deriv j).2,
        lt_of_le_of_lt le_add_self (hterm_lt j)⟩
    have hw_sub := hasWeakCellDerivC_sub
      (hasWeakCellDerivC_of_hasWeakVelDeriv (j := j) (B0583.hasWeakVelDeriv_velocity_eta c hm.le w hw.2))
      (hu_deriv j).2
    have hdiff0 := LinearBodySourceHelp.hasWeakCellDerivC_ae_zero_of_ae_zero hc0
      ((hu_eq j).mono fun x hx => sub_eq_zero.mpr hx) (hm_can.sub hm_uη) hw_sub
    exact hdiff0.mono fun x hx => sub_eq_zero.mp hx
  refine ⟨hu_eq, huq_eq, huη_eq, ?_⟩
  have hsum_eq : (∑ j : Fin 2,
      (eLpNorm (fun x => (uLp : B0579.Plane → B0581.Vel) x j) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => (uqLp : B0579.Plane → B0581.Vel) x j) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => (uηLp : B0579.Plane → B0581.Vel) x j) 2 (volume.restrict (B0579.cell c)))) =
      ∑ j : Fin 2,
        (eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun x => uq x j) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun x => uη x j) 2 (volume.restrict (B0579.cell c))) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eLpNorm_congr_ae (hu_eq j), eLpNorm_congr_ae (huq_eq j), eLpNorm_congr_ae (huη_eq j)]
  rw [hsum_eq]
  exact hu_bd

lemma cellMeasure_zero_eq_cellVol (c : ℝ) :
    B0579.cellMeasure c 0 = volume.restrict (B0579.cell c) := by
  rw [B0579.cellMeasure]
  have hd : (fun x : B0579.Plane => ((B0579.density (0 : ℝ) x : NNReal) : ENNReal)) =
      fun _ => (1 : ENNReal) := by
    funext x
    have hreal : (B0579.density (0 : ℝ) x : ℝ) = 1 := by
      rw [B0579.coe_density]
      simp [Real.rpow_zero]
    have hnn : B0579.density (0 : ℝ) x = 1 := Subtype.ext hreal
    exact_mod_cast hnn
  rw [hd]
  exact withDensity_one

/-- From the propagator Duhamel formula `ω s = U s 0 (ω 0) + ∫ t in Ioc 0 s, U s t (f t)`
(proved internally in `Sub/PartII-b_F4.lean`), `ω s → ω 0` strongly in `Xmc p.c m` as `s → 0+`. -/
theorem tendsto_omega_zero_of_duhamel {m : ℝ} {p : Params} (hH : 0 < p.H)
    {U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)} (hU : IsCoupledPropagator m p U)
    {M_U : ℝ} (hMU0 : 0 ≤ M_U)
    (hU_bd : ∀ t s : ℝ, 0 ≤ t → t ≤ s → s ≤ p.H → ‖U s t‖ ≤ M_U)
    {f ω : ℝ → Xmc p.c m} (hf : IntegrableOn f (Ioc 0 p.H) volume)
    (h_duh : ∀ s ∈ Icc 0 p.H, ω s = U s 0 (ω 0) + ∫ t in Ioc 0 s, U s t (f t)) :
    Tendsto ω (𝓝[Ioi 0] 0) (𝓝 (ω 0)) := by
  have hIoo_mem : Ioo 0 p.H ∈ 𝓝[Ioi 0] (0 : ℝ) :=
    mem_nhdsWithin.2 ⟨Iio p.H, isOpen_Iio, hH, fun s hs => ⟨hs.2, hs.1⟩⟩
  have h1 : Tendsto (fun s => U s 0 (ω 0)) (𝓝[Ioi 0] 0) (𝓝 (ω 0)) := by
    have hc := (hU.strongCont 0 ⟨le_rfl, hH.le⟩ (ω 0)).continuousWithinAt ⟨le_rfl, hH.le⟩
    rw [ContinuousWithinAt, hU.id_self 0 ⟨le_rfl, hH.le⟩, ContinuousLinearMap.id_apply] at hc
    exact hc.mono_left (nhdsWithin_le_iff.2 (Filter.mem_of_superset hIoo_mem Ioo_subset_Icc_self))
  have h2 : Tendsto (fun s => ∫ t in Ioc 0 s, U s t (f t)) (𝓝[Ioi 0] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmeas_tend : Tendsto ((volume.restrict (Ioc 0 p.H)) ∘ fun s : ℝ => Ioc 0 s)
        (𝓝[Ioi 0] 0) (𝓝 0) := by
      have hofr : Tendsto ENNReal.ofReal (𝓝[Ioi 0] (0 : ℝ)) (𝓝 0) := by
        simpa using ENNReal.tendsto_ofReal
          ((continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hofr
        (Eventually.of_forall fun _ => zero_le) ?_
      filter_upwards [self_mem_nhdsWithin] with s _
      calc (volume.restrict (Ioc 0 p.H)) (Ioc 0 s)
          ≤ volume (Ioc 0 s) := Measure.restrict_apply_le _ _
        _ = ENNReal.ofReal s := by rw [Real.volume_Ioc, sub_zero]
    have hint_tend : Tendsto (fun s : ℝ => ∫ t in Ioc 0 s, ‖f t‖ ∂volume.restrict (Ioc 0 p.H))
        (𝓝[Ioi 0] 0) (𝓝 0) :=
      hf.norm.tendsto_setIntegral_nhds_zero hmeas_tend
    have hmul_tend : Tendsto (fun s : ℝ => M_U * ∫ t in Ioc 0 s, ‖f t‖ ∂volume.restrict (Ioc 0 p.H))
        (𝓝[Ioi 0] 0) (𝓝 0) := by
      simpa using hint_tend.const_mul M_U
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmul_tend
    filter_upwards [hIoo_mem] with s hs
    have hsub : Ioc 0 s ⊆ Ioc 0 p.H := Ioc_subset_Ioc_right hs.2.le
    rw [Measure.restrict_restrict_of_subset hsub]
    calc ‖∫ t in Ioc 0 s, U s t (f t)‖
        ≤ ∫ t in Ioc 0 s, ‖U s t (f t)‖ := norm_integral_le_integral_norm _
      _ ≤ M_U * ∫ t in Ioc 0 s, ‖f t‖ := by
          by_cases hInt : IntegrableOn (fun t => ‖U s t (f t)‖) (Ioc 0 s) volume
          · have hf_s : IntegrableOn (fun t => ‖f t‖) (Ioc 0 s) volume := (hf.mono_set hsub).norm
            have hpw : ∀ᵐ t ∂volume.restrict (Ioc 0 s), ‖U s t (f t)‖ ≤ M_U * ‖f t‖ := by
              filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
              exact ((U s t).le_opNorm (f t)).trans
                (mul_le_mul_of_nonneg_right (hU_bd t s ht.1.le ht.2 hs.2.le) (norm_nonneg _))
            exact (integral_mono_ae hInt (hf_s.const_mul M_U) hpw).trans_eq
              (integral_const_mul M_U _)
          · rw [integral_undef hInt]
            exact mul_nonneg hMU0 (integral_nonneg fun _ => norm_nonneg _)
  have hsum := by simpa using h1.add h2
  refine hsum.congr' ?_
  filter_upwards [hIoo_mem] with s hs
  exact (h_duh s ⟨hs.1.le, hs.2.le⟩).symm

/-- Once `ω s → ω 0` strongly in `Xmc p.c m` (`0 ≤ m`) as `s → 0+`, `ω 0 =ᵐ entranceVorticityComb p α`,
and `profCurl zq zη (s, ·) =ᵐ ω s` on `B0579.cell p.c` for `s ∈ Ioc 0 p.H`, the `L²(cell)` entrance
curl trace `IsMeridionalCorrectionOn.initial_curl` follows immediately. -/
theorem initial_curl_of_tendsto_omega {m : ℝ} (hm0 : 0 ≤ m) {p : Params} (hH : 0 < p.H)
    {ω : ℝ → Xmc p.c m} {α : E2} {zq zη : CProf}
    (hω_tend : Tendsto ω (𝓝[Ioi 0] 0) (𝓝 (ω 0)))
    (hω0 : (ω 0 : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure p.c m] entranceVorticityComb p α)
    (hcurl : ∀ s ∈ Ioc 0 p.H,
      (fun x => profCurl zq zη (s, x)) =ᵐ[volume.restrict (B0579.cell p.c)]
        (fun x => ((ω s x : ℝ) : ℂ))) :
    Tendsto (fun s => eLpNorm
        (fun x => profCurl zq zη (s, x) - ((entranceVorticityComb p α x : ℝ) : ℂ))
        2 (B0579.cellMeasure p.c 0))
      (𝓝[Ioi 0] 0) (𝓝 0) := by
  have hIoo_mem : Ioo 0 p.H ∈ 𝓝[Ioi 0] (0 : ℝ) :=
    mem_nhdsWithin.2 ⟨Iio p.H, isOpen_Iio, hH, fun s hs => ⟨hs.2, hs.1⟩⟩
  have hω0_vol : (ω 0 : B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell p.c)]
      entranceVorticityComb p α :=
    (B0579.ac_cellMeasure p.c m).ae_le hω0
  have hnorm_tend : Tendsto (fun s => ENNReal.ofReal ‖ω s - ω 0‖) (𝓝[Ioi 0] 0) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_iff_norm_sub_tendsto_zero.mp hω_tend)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hnorm_tend
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hIoo_mem] with s hs
  have hsub_ae : (((ω s - ω 0 : Xmc p.c m) : B0579.Plane → ℝ)) =ᵐ[volume.restrict (B0579.cell p.c)]
      (fun x => ω s x - ω 0 x) :=
    (B0579.ac_cellMeasure p.c m).ae_le (Lp.coeFn_sub (ω s) (ω 0))
  have hae : (fun x => profCurl zq zη (s, x) - ((entranceVorticityComb p α x : ℝ) : ℂ)) =ᵐ[
      volume.restrict (B0579.cell p.c)]
      (fun x => ((((ω s - ω 0 : Xmc p.c m) : B0579.Plane → ℝ) x : ℝ) : ℂ)) := by
    filter_upwards [hcurl s ⟨hs.1, hs.2.le⟩, hω0_vol, hsub_ae] with x hcx h0x hsx
    rw [hcx, ← h0x, hsx]
    push_cast
    ring
  rw [cellMeasure_zero_eq_cellVol p.c, eLpNorm_congr_ae hae]
  calc eLpNorm (fun x => ((((ω s - ω 0 : Xmc p.c m) : B0579.Plane → ℝ) x : ℝ) : ℂ))
        2 (volume.restrict (B0579.cell p.c))
      = eLpNorm ((ω s - ω 0 : Xmc p.c m) : B0579.Plane → ℝ) 2 (B0581.cellVol p.c) :=
        eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by simp)
    _ ≤ eLpNorm ((ω s - ω 0 : Xmc p.c m) : B0579.Plane → ℝ) 2 (B0579.cellMeasure p.c m) :=
        eLpNorm_mono_measure _ (B0581.cellVol_le_cellMeasure p.c hm0)
    _ = ENNReal.ofReal ‖ω s - ω 0‖ := by
        rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (ω s - ω 0))]

/-! ## 5. Strong continuity of Duhamel trajectories, canonical `B0583` `=ᵐ`-linearity, and weak curl -/

lemma toCMerid_zero : toCMerid 0 = 0 := by
  funext x; ext j; simp [toCMerid]

lemma toCMerid_add (v₁ v₂ : B0579.Plane → Fin 2 → ℂ) :
    toCMerid (fun x j => v₁ x j + v₂ x j) = toCMerid v₁ + toCMerid v₂ := by
  funext x; ext j; simp [toCMerid]

lemma toCMerid_smul_real (a : ℝ) (v : B0579.Plane → Fin 2 → ℂ) :
    toCMerid (fun x j => (a : ℂ) * v x j) = a • toCMerid v := by
  funext x; ext j; simp [toCMerid, Complex.real_smul]

lemma ae_coord_of_toCMerid {μ : Measure B0579.Plane} {f : B0579.Plane → CMerid}
    {v : B0579.Plane → Fin 2 → ℂ} (h : f =ᵐ[μ] toCMerid v) (j : Fin 2) :
    (fun x => f x j) =ᵐ[μ] (fun x => v x j) :=
  h.mono fun x hx => by dsimp; rw [hx]; rfl

lemma toCMerid_ae_of_coord {μ : Measure B0579.Plane} {f : B0579.Plane → CMerid}
    {v : B0579.Plane → Fin 2 → ℂ}
    (h : ∀ j : Fin 2, (fun x => f x j) =ᵐ[μ] (fun x => v x j)) :
    f =ᵐ[μ] toCMerid v := by
  filter_upwards [h 0, h 1] with x h0 h1
  ext j; fin_cases j
  · exact h0
  · exact h1

lemma hasWeakCellDerivC_zero (c : ℝ) (k : Fin 2) :
    IIIa.HasWeakCellDerivC c k 0 0 :=
  ⟨fun _ _ => ⟨by simp, by simp⟩, fun _ _ => by simp⟩

lemma hasWeakCellDerivC_add {c : ℝ} {k : Fin 2} {φ₁ φ₂ g₁ g₂ : ℝ × ℝ → ℂ}
    (h₁ : IIIa.HasWeakCellDerivC c k φ₁ g₁)
    (h₂ : IIIa.HasWeakCellDerivC c k φ₂ g₂) :
    IIIa.HasWeakCellDerivC c k (fun x => φ₁ x + φ₂ x) (fun x => g₁ x + g₂ x) := by
  have hL_eq : ∀ ψ : B0579.Plane → ℝ, (fun x => (φ₁ x + φ₂ x) * (B0579.pd k ψ x : ℂ)) =
      fun x => φ₁ x * (B0579.pd k ψ x : ℂ) + φ₂ x * (B0579.pd k ψ x : ℂ) := by
    intro ψ; funext x; ring
  have hR_eq : ∀ ψ : B0579.Plane → ℝ, (fun x => (g₁ x + g₂ x) * (ψ x : ℂ)) =
      fun x => g₁ x * (ψ x : ℂ) + g₂ x * (ψ x : ℂ) := by
    intro ψ; funext x; ring
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · rw [hL_eq ψ]; exact (h₁.1 ψ hψ).1.add (h₂.1 ψ hψ).1
  · rw [hR_eq ψ]; exact (h₁.1 ψ hψ).2.add (h₂.1 ψ hψ).2
  · rw [hL_eq ψ, hR_eq ψ, integral_add (h₁.1 ψ hψ).1 (h₂.1 ψ hψ).1,
      integral_add (h₁.1 ψ hψ).2 (h₂.1 ψ hψ).2, h₁.2 ψ hψ, h₂.2 ψ hψ]
    ring

lemma hasWeakCellDerivC_smul_real {c : ℝ} {k : Fin 2} (a : ℝ) {φ g : ℝ × ℝ → ℂ}
    (h : IIIa.HasWeakCellDerivC c k φ g) :
    IIIa.HasWeakCellDerivC c k (fun x => (a : ℂ) * φ x) (fun x => (a : ℂ) * g x) := by
  have hL_eq : ∀ ψ : B0579.Plane → ℝ, (fun x => ((a : ℂ) * φ x) * (B0579.pd k ψ x : ℂ)) =
      fun x => (a : ℂ) * (φ x * (B0579.pd k ψ x : ℂ)) := by
    intro ψ; funext x; ring
  have hR_eq : ∀ ψ : B0579.Plane → ℝ, (fun x => ((a : ℂ) * g x) * (ψ x : ℂ)) =
      fun x => (a : ℂ) * (g x * (ψ x : ℂ)) := by
    intro ψ; funext x; ring
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · rw [hL_eq ψ]; exact (h.1 ψ hψ).1.const_mul (a : ℂ)
  · rw [hR_eq ψ]; exact (h.1 ψ hψ).2.const_mul (a : ℂ)
  · rw [hL_eq ψ, hR_eq ψ, integral_const_mul, integral_const_mul, h.2 ψ hψ, mul_neg]

lemma hasWeakCellDerivC_congr_ae {c : ℝ} {k : Fin 2} {φ₁ φ₂ g₁ g₂ : ℝ × ℝ → ℂ}
    (hφ : φ₁ =ᵐ[volume.restrict (B0579.cell c)] φ₂)
    (hg : g₁ =ᵐ[volume.restrict (B0579.cell c)] g₂)
    (h₁ : IIIa.HasWeakCellDerivC c k φ₁ g₁) :
    IIIa.HasWeakCellDerivC c k φ₂ g₂ := by
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · have hae1 : (fun x => φ₁ x * (B0579.pd k ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => φ₂ x * (B0579.pd k ψ x : ℂ)) := hφ.mono fun x hx => by dsimp; rw [hx]
    have hae2 : (fun x => g₁ x * (ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => g₂ x * (ψ x : ℂ)) := hg.mono fun x hx => by dsimp; rw [hx]
    exact ⟨(h₁.1 ψ hψ).1.congr hae1, (h₁.1 ψ hψ).2.congr hae2⟩
  · have hae1 : (fun x => φ₁ x * (B0579.pd k ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => φ₂ x * (B0579.pd k ψ x : ℂ)) := hφ.mono fun x hx => by dsimp; rw [hx]
    have hae2 : (fun x => g₁ x * (ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => g₂ x * (ψ x : ℂ)) := hg.mono fun x hx => by dsimp; rw [hx]
    rw [← integral_congr_ae hae1, ← integral_congr_ae hae2]
    exact h₁.2 ψ hψ

lemma isBiotSavart_congr_ae {c : ℝ} {w₁ w₂ : ℝ × ℝ → ℂ} {u₁ u₂ : ℝ × ℝ → Fin 2 → ℂ}
    (hw : w₁ =ᵐ[volume.restrict (B0579.cell c)] w₂)
    (hu : ∀ j : Fin 2, (fun x => u₁ x j) =ᵐ[volume.restrict (B0579.cell c)] (fun x => u₂ x j))
    (h₁ : IIIa.IsBiotSavart c w₁ u₁) :
    IIIa.IsBiotSavart c w₂ u₂ := by
  refine ⟨fun j => ⟨(h₁.1 j).1.congr (hu j),
      by rw [← eLpNorm_congr_ae (hu j)]; exact (h₁.1 j).2⟩,
    fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · have hae : (fun x => u₁ x 0 * (B0579.pd 0 ψ x : ℂ) + u₁ x 1 * (B0579.pd 1 ψ x : ℂ)) =ᵐ[
        volume.restrict (B0579.cell c)]
        (fun x => u₂ x 0 * (B0579.pd 0 ψ x : ℂ) + u₂ x 1 * (B0579.pd 1 ψ x : ℂ)) := by
      filter_upwards [hu 0, hu 1] with x h0 h1
      simp only [h0, h1]
    rw [← integral_congr_ae hae]
    exact h₁.2.1 ψ hψ
  · have haeL : (fun x => w₁ x * (ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => w₂ x * (ψ x : ℂ)) := hw.mono fun x hx => by dsimp; rw [hx]
    have haeR : (fun x => u₁ x 0 * (B0579.pd 1 ψ x : ℂ) - u₁ x 1 * (B0579.pd 0 ψ x : ℂ)) =ᵐ[
        volume.restrict (B0579.cell c)]
        (fun x => u₂ x 0 * (B0579.pd 1 ψ x : ℂ) - u₂ x 1 * (B0579.pd 0 ψ x : ℂ)) := by
      filter_upwards [hu 0, hu 1] with x h0 h1
      simp only [h0, h1]
    rw [← integral_congr_ae haeL, ← integral_congr_ae haeR]
    exact h₁.2.2 ψ hψ

theorem canonical_bs_unique_ae {c m : ℝ} (hc1 : 1 ≤ c) (hm : 1 < m)
    {w : Xmc c m} (hw : HasZeroCirculationR c w)
    {u uq uη : B0579.Plane → Fin 2 → ℂ}
    (hu_bs : IIIa.IsBiotSavart c (fun x => ((w x : ℝ) : ℂ)) u)
    (hu_deriv : ∀ j : Fin 2, IIIa.HasWeakCellDerivC c 0 (fun x => u x j) (fun x => uq x j) ∧
      IIIa.HasWeakCellDerivC c 1 (fun x => u x j) (fun x => uη x j))
    (huq_mem : ∀ j : Fin 2, MemLp (fun x => uq x j) 2 (volume.restrict (B0579.cell c)))
    (huη_mem : ∀ j : Fin 2, MemLp (fun x => uη x j) 2 (volume.restrict (B0579.cell c))) :
    haveI : Fact (0 < c) := ⟨by linarith⟩
    let uLp := B0583.velocity c hm.le w hw.2
    let uqLp := B0583.velGradQ c hm.le w
    let uηLp := B0583.velGradEta c hm.le w hw.2
    (∀ j : Fin 2,
      (fun x => (uLp : B0579.Plane → B0581.Vel) x j) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => u x j)) ∧
    (∀ j : Fin 2,
      (fun x => (uqLp : B0579.Plane → B0581.Vel) x j) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => uq x j)) ∧
    (∀ j : Fin 2,
      (fun x => (uηLp : B0579.Plane → B0581.Vel) x j) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => uη x j)) := by
  have hc0 : 0 < c := by linarith
  have : Fact (0 < c) := ⟨hc0⟩
  set uLp := B0583.velocity c hm.le w hw.2
  set uqLp := B0583.velGradQ c hm.le w
  set uηLp := B0583.velGradEta c hm.le w hw.2
  have hCan_bs : IIIa.IsBiotSavart c (fun x => ((w x : ℝ) : ℂ))
      (fun x j => (uLp : B0579.Plane → B0581.Vel) x j) :=
    Short.IIIa.CTE.velocityIsBiotSavart c m hm w hw.2
  have hu_vec := Short.IIIa.CTE.isBiotSavart_unique c hc0 (fun x => ((w x : ℝ) : ℂ))
    (fun x j => (uLp : B0579.Plane → B0581.Vel) x j) u hCan_bs hu_bs
  have hu_eq : ∀ j : Fin 2,
      (fun x => (uLp : B0579.Plane → B0581.Vel) x j) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => u x j) :=
    fun j => hu_vec.mono fun x hx => congrFun hx j
  have huq_eq : ∀ j : Fin 2,
      (fun x => (uqLp : B0579.Plane → B0581.Vel) x j) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => uq x j) := by
    intro j
    have hm_can : MemLp (fun x => (uqLp : B0579.Plane → B0581.Vel) x j) 2
        (volume.restrict (B0579.cell c)) :=
      ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj j : B0581.Vel →L[ℂ] ℂ) (Lp.memLp uqLp)
    have hw_sub := hasWeakCellDerivC_sub
      (hasWeakCellDerivC_of_hasWeakVelDeriv (j := j) (B0583.hasWeakVelDeriv_velocity_q c hm.le w hw.2))
      (hu_deriv j).1
    have hdiff0 := LinearBodySourceHelp.hasWeakCellDerivC_ae_zero_of_ae_zero hc0
      ((hu_eq j).mono fun x hx => sub_eq_zero.mpr hx) (hm_can.sub (huq_mem j)) hw_sub
    exact hdiff0.mono fun x hx => sub_eq_zero.mp hx
  have huη_eq : ∀ j : Fin 2,
      (fun x => (uηLp : B0579.Plane → B0581.Vel) x j) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => uη x j) := by
    intro j
    have hm_can : MemLp (fun x => (uηLp : B0579.Plane → B0581.Vel) x j) 2
        (volume.restrict (B0579.cell c)) :=
      ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj j : B0581.Vel →L[ℂ] ℂ) (Lp.memLp uηLp)
    have hw_sub := hasWeakCellDerivC_sub
      (hasWeakCellDerivC_of_hasWeakVelDeriv (j := j) (B0583.hasWeakVelDeriv_velocity_eta c hm.le w hw.2))
      (hu_deriv j).2
    have hdiff0 := LinearBodySourceHelp.hasWeakCellDerivC_ae_zero_of_ae_zero hc0
      ((hu_eq j).mono fun x hx => sub_eq_zero.mpr hx) (hm_can.sub (huη_mem j)) hw_sub
    exact hdiff0.mono fun x hx => sub_eq_zero.mp hx
  exact ⟨hu_eq, huq_eq, huη_eq⟩

theorem canonical_bs_weakCurl_ae {c m : ℝ} (hc1 : 1 ≤ c) (hm : 1 < m)
    {w : Xmc c m} (hw : HasZeroCirculationR c w) :
    haveI : Fact (0 < c) := ⟨by linarith⟩
    let uqLp := B0583.velGradQ c hm.le w
    let uηLp := B0583.velGradEta c hm.le w hw.2
    (fun x => (uqLp : B0579.Plane → B0581.Vel) x 1 -
        (uηLp : B0579.Plane → B0581.Vel) x 0) =ᵐ[volume.restrict (B0579.cell c)]
      (fun x => ((w x : ℝ) : ℂ)) := by
  have hc0 : 0 < c := by linarith
  have hm0 : 0 ≤ m := by linarith
  have : Fact (0 < c) := ⟨hc0⟩
  set uLp := B0583.velocity c hm.le w hw.2
  set uqLp := B0583.velGradQ c hm.le w
  set uηLp := B0583.velGradEta c hm.le w hw.2
  have hCan_bs : IIIa.IsBiotSavart c (fun x => ((w x : ℝ) : ℂ))
      (fun x j => (uLp : B0579.Plane → B0581.Vel) x j) :=
    Short.IIIa.CTE.velocityIsBiotSavart c m hm w hw.2
  have hq1 : IIIa.HasWeakCellDerivC c 0
      (fun x => (uLp : B0579.Plane → B0581.Vel) x 1)
      (fun x => (uqLp : B0579.Plane → B0581.Vel) x 1) :=
    hasWeakCellDerivC_of_hasWeakVelDeriv (j := 1) (B0583.hasWeakVelDeriv_velocity_q c hm.le w hw.2)
  have hη0 : IIIa.HasWeakCellDerivC c 1
      (fun x => (uLp : B0579.Plane → B0581.Vel) x 0)
      (fun x => (uηLp : B0579.Plane → B0581.Vel) x 0) :=
    hasWeakCellDerivC_of_hasWeakVelDeriv (j := 0) (B0583.hasWeakVelDeriv_velocity_eta c hm.le w hw.2)
  set g : B0579.Plane → ℂ := fun x =>
    (uqLp : B0579.Plane → B0581.Vel) x 1 - (uηLp : B0579.Plane → B0581.Vel) x 0 - ((w x : ℝ) : ℂ)
  have hm_uq1 : MemLp (fun x => (uqLp : B0579.Plane → B0581.Vel) x 1) 2
      (volume.restrict (B0579.cell c)) :=
    ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj 1 : B0581.Vel →L[ℂ] ℂ) (Lp.memLp uqLp)
  have hm_uη0 : MemLp (fun x => (uηLp : B0579.Plane → B0581.Vel) x 0) 2
      (volume.restrict (B0579.cell c)) :=
    ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj 0 : B0581.Vel →L[ℂ] ℂ) (Lp.memLp uηLp)
  have hm_wR : MemLp (w : B0579.Plane → ℝ) 2 (volume.restrict (B0579.cell c)) := by
    refine ⟨(Lp.memLp w).aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure c m), ?_⟩
    exact lt_of_le_of_lt (eLpNorm_mono_measure _ (B0581.cellVol_le_cellMeasure c hm0))
      (Lp.eLpNorm_lt_top w)
  have hm_wC : MemLp (fun x => ((w x : ℝ) : ℂ)) 2 (volume.restrict (B0579.cell c)) :=
    Complex.ofRealCLM.comp_memLp' hm_wR
  have hm_g : MemLp g 2 (volume.restrict (B0579.cell c)) :=
    (hm_uq1.sub hm_uη0).sub hm_wC
  have hw_g : IIIa.HasWeakCellDerivC c 0 0 g := by
    refine ⟨fun ψ hψ => ⟨by simp, ?_⟩, fun ψ hψ => ?_⟩
    · have hIw_R := PartIIbF4Aux.integrableOn_mul_cylTest c m hψ w
      have hIw : IntegrableOn (fun x => ((w x : ℝ) : ℂ) * (ψ x : ℂ)) (B0579.cell c) volume :=
        (Complex.ofRealCLM.integrable_comp hIw_R).congr (Eventually.of_forall fun x => by simp)
      have hq1_I : IntegrableOn (fun x => (uqLp : B0579.Plane → B0581.Vel) x 1 * (ψ x : ℂ))
          (B0579.cell c) volume := (hq1.1 ψ hψ).2
      have hη0_I : IntegrableOn (fun x => (uηLp : B0579.Plane → B0581.Vel) x 0 * (ψ x : ℂ))
          (B0579.cell c) volume := (hη0.1 ψ hψ).2
      have hfun : (fun x => g x * (ψ x : ℂ)) =
          fun x => ((uqLp : B0579.Plane → B0581.Vel) x 1 * (ψ x : ℂ) -
            (uηLp : B0579.Plane → B0581.Vel) x 0 * (ψ x : ℂ)) -
            ((w x : ℝ) : ℂ) * (ψ x : ℂ) := by
        funext x; dsimp [g]; ring
      rw [hfun]
      exact (hq1_I.sub hη0_I).sub hIw
    · have hIw_R := PartIIbF4Aux.integrableOn_mul_cylTest c m hψ w
      have hIw : IntegrableOn (fun x => ((w x : ℝ) : ℂ) * (ψ x : ℂ)) (B0579.cell c) volume :=
        (Complex.ofRealCLM.integrable_comp hIw_R).congr (Eventually.of_forall fun x => by simp)
      have hq1_I : IntegrableOn (fun x => (uqLp : B0579.Plane → B0581.Vel) x 1 * (ψ x : ℂ))
          (B0579.cell c) volume := (hq1.1 ψ hψ).2
      have hη0_I : IntegrableOn (fun x => (uηLp : B0579.Plane → B0581.Vel) x 0 * (ψ x : ℂ))
          (B0579.cell c) volume := (hη0.1 ψ hψ).2
      have hqη_I : IntegrableOn
          (fun x => (uqLp : B0579.Plane → B0581.Vel) x 1 * (ψ x : ℂ) -
            (uηLp : B0579.Plane → B0581.Vel) x 0 * (ψ x : ℂ))
          (B0579.cell c) volume := hq1_I.sub hη0_I
      have hIu0 : IntegrableOn
          (fun x => (uLp : B0579.Plane → B0581.Vel) x 0 * (B0579.pd 1 ψ x : ℂ))
          (B0579.cell c) volume := (hη0.1 ψ hψ).1
      have hIu1 : IntegrableOn
          (fun x => (uLp : B0579.Plane → B0581.Vel) x 1 * (B0579.pd 0 ψ x : ℂ))
          (B0579.cell c) volume := (hq1.1 ψ hψ).1
      have hfun : (fun x => g x * (ψ x : ℂ)) =
          fun x => ((uqLp : B0579.Plane → B0581.Vel) x 1 * (ψ x : ℂ) -
            (uηLp : B0579.Plane → B0581.Vel) x 0 * (ψ x : ℂ)) -
            ((w x : ℝ) : ℂ) * (ψ x : ℂ) := by
        funext x; dsimp [g]; ring
      have hq1_eq : (∫ x in B0579.cell c,
          (uLp : B0579.Plane → B0581.Vel) x 1 * (B0579.pd 0 ψ x : ℂ)) =
          -∫ x in B0579.cell c, (uqLp : B0579.Plane → B0581.Vel) x 1 * (ψ x : ℂ) :=
        hq1.2 ψ hψ
      have hη0_eq : (∫ x in B0579.cell c,
          (uLp : B0579.Plane → B0581.Vel) x 0 * (B0579.pd 1 ψ x : ℂ)) =
          -∫ x in B0579.cell c, (uηLp : B0579.Plane → B0581.Vel) x 0 * (ψ x : ℂ) :=
        hη0.2 ψ hψ
      have hbs_eq : (∫ x in B0579.cell c, ((w x : ℝ) : ℂ) * (ψ x : ℂ)) =
          ∫ x in B0579.cell c,
            ((uLp : B0579.Plane → B0581.Vel) x 0 * (B0579.pd 1 ψ x : ℂ) -
              (uLp : B0579.Plane → B0581.Vel) x 1 * (B0579.pd 0 ψ x : ℂ)) :=
        hCan_bs.2.2 ψ hψ
      rw [integral_sub hIu0 hIu1] at hbs_eq
      have hq1_eq' : (∫ x in B0579.cell c,
          (uqLp : B0579.Plane → B0581.Vel) x 1 * (ψ x : ℂ)) =
          -∫ x in B0579.cell c, (uLp : B0579.Plane → B0581.Vel) x 1 * (B0579.pd 0 ψ x : ℂ) :=
        neg_eq_iff_eq_neg.mp hq1_eq.symm
      have hη0_eq' : (∫ x in B0579.cell c,
          (uηLp : B0579.Plane → B0581.Vel) x 0 * (ψ x : ℂ)) =
          -∫ x in B0579.cell c, (uLp : B0579.Plane → B0581.Vel) x 0 * (B0579.pd 1 ψ x : ℂ) :=
        neg_eq_iff_eq_neg.mp hη0_eq.symm
      simp only [Pi.zero_apply, zero_mul, integral_zero]
      rw [hfun, integral_sub hqη_I hIw, integral_sub hq1_I hη0_I,
        hbs_eq, hq1_eq', hη0_eq']
      ring
  have hg0 := LinearBodySourceHelp.hasWeakCellDerivC_ae_zero_of_ae_zero hc0
    (Filter.EventuallyEq.refl _ _) hm_g hw_g
  exact hg0.mono fun x hx => sub_eq_zero.mp hx

theorem canonical_bs_zero_ae {c m : ℝ} (hc1 : 1 ≤ c) (hm : 1 < m)
    (hw0 : HasZeroCirculationR c ((0 : Xmc c m) : B0579.Plane → ℝ)) :
    haveI : Fact (0 < c) := ⟨by linarith⟩
    (∀ j : Fin 2,
      (fun x => (B0583.velocity c hm.le (0 : Xmc c m) hw0.2 : B0579.Plane → B0581.Vel) x j) =ᵐ[
          volume.restrict (B0579.cell c)] 0) ∧
    (∀ j : Fin 2,
      (fun x => (B0583.velGradQ c hm.le (0 : Xmc c m) : B0579.Plane → B0581.Vel) x j) =ᵐ[
          volume.restrict (B0579.cell c)] 0) ∧
    (∀ j : Fin 2,
      (fun x => (B0583.velGradEta c hm.le (0 : Xmc c m) hw0.2 : B0579.Plane → B0581.Vel) x j) =ᵐ[
          volume.restrict (B0579.cell c)] 0) := by
  have hw0_cell : (fun x => ((((0 : Xmc c m) : B0579.Plane → ℝ) x : ℝ) : ℂ)) =ᵐ[
      volume.restrict (B0579.cell c)] 0 := by
    filter_upwards [(B0579.ac_cellMeasure c m).ae_le
      (Lp.coeFn_zero ℝ 2 (B0579.cellMeasure c m))] with x hx
    have hx0 : ((0 : Xmc c m) : B0579.Plane → ℝ) x = 0 := hx
    exact (congrArg Complex.ofReal hx0).trans Complex.ofReal_zero
  have hbs0 : IIIa.IsBiotSavart c
      (fun x => ((((0 : Xmc c m) : B0579.Plane → ℝ) x : ℝ) : ℂ)) 0 :=
    isBiotSavart_congr_ae hw0_cell.symm (fun _ => Filter.EventuallyEq.refl _ _)
      ⟨fun _ => MemLp.zero, fun _ _ => by simp, fun _ _ => by simp⟩
  exact canonical_bs_unique_ae hc1 hm hw0 hbs0
    (fun _ => ⟨hasWeakCellDerivC_zero c 0, hasWeakCellDerivC_zero c 1⟩)
    (fun _ => MemLp.zero) (fun _ => MemLp.zero)

theorem canonical_bs_smul_ae {c m : ℝ} (hc1 : 1 ≤ c) (hm : 1 < m) (a : ℝ)
    {w : Xmc c m} (hw : HasZeroCirculationR c w)
    (haw : HasZeroCirculationR c ((a • w : Xmc c m) : B0579.Plane → ℝ)) :
    haveI : Fact (0 < c) := ⟨by linarith⟩
    (∀ j : Fin 2,
      (fun x => (B0583.velocity c hm.le (a • w) haw.2 : B0579.Plane → B0581.Vel) x j) =ᵐ[
          volume.restrict (B0579.cell c)]
        (fun x => (a : ℂ) * (B0583.velocity c hm.le w hw.2 : B0579.Plane → B0581.Vel) x j)) ∧
    (∀ j : Fin 2,
      (fun x => (B0583.velGradQ c hm.le (a • w) : B0579.Plane → B0581.Vel) x j) =ᵐ[
          volume.restrict (B0579.cell c)]
        (fun x => (a : ℂ) * (B0583.velGradQ c hm.le w : B0579.Plane → B0581.Vel) x j)) ∧
    (∀ j : Fin 2,
      (fun x => (B0583.velGradEta c hm.le (a • w) haw.2 : B0579.Plane → B0581.Vel) x j) =ᵐ[
          volume.restrict (B0579.cell c)]
        (fun x => (a : ℂ) * (B0583.velGradEta c hm.le w hw.2 : B0579.Plane → B0581.Vel) x j)) := by
  have hc0 : 0 < c := by linarith
  have : Fact (0 < c) := ⟨hc0⟩
  set uLp := B0583.velocity c hm.le w hw.2
  set uqLp := B0583.velGradQ c hm.le w
  set uηLp := B0583.velGradEta c hm.le w hw.2
  have hCan_bs : IIIa.IsBiotSavart c (fun x => ((w x : ℝ) : ℂ))
      (fun x j => (uLp : B0579.Plane → B0581.Vel) x j) :=
    Short.IIIa.CTE.velocityIsBiotSavart c m hm w hw.2
  have haw_ae : (fun x => ((((a • w : Xmc c m) : B0579.Plane → ℝ) x : ℝ) : ℂ)) =ᵐ[
      volume.restrict (B0579.cell c)] (fun x => (a : ℂ) * ((w x : ℝ) : ℂ)) := by
    filter_upwards [(B0579.ac_cellMeasure c m).ae_le (Lp.coeFn_smul a w)] with x hx
    rw [hx]; simp [Pi.smul_apply]
  have hbs_smul : IIIa.IsBiotSavart c
      (fun x => ((((a • w : Xmc c m) : B0579.Plane → ℝ) x : ℝ) : ℂ))
      (fun x j => (a : ℂ) * (uLp : B0579.Plane → B0581.Vel) x j) := by
    refine isBiotSavart_congr_ae haw_ae.symm (fun _ => Filter.EventuallyEq.refl _ _) ?_
    refine ⟨fun j => (hCan_bs.1 j).const_mul (a : ℂ), fun ψ hψ => ?_, fun ψ hψ => ?_⟩
    · have hfun : (fun x => ((a : ℂ) * (uLp : B0579.Plane → B0581.Vel) x 0) * (B0579.pd 0 ψ x : ℂ) +
          ((a : ℂ) * (uLp : B0579.Plane → B0581.Vel) x 1) * (B0579.pd 1 ψ x : ℂ)) =
          fun x => (a : ℂ) * ((uLp : B0579.Plane → B0581.Vel) x 0 * (B0579.pd 0 ψ x : ℂ) +
            (uLp : B0579.Plane → B0581.Vel) x 1 * (B0579.pd 1 ψ x : ℂ)) := by
        funext x; ring
      rw [hfun, integral_const_mul, hCan_bs.2.1 ψ hψ, mul_zero]
    · have hL : (fun x => ((a : ℂ) * ((w x : ℝ) : ℂ)) * (ψ x : ℂ)) =
          fun x => (a : ℂ) * (((w x : ℝ) : ℂ) * (ψ x : ℂ)) := by funext x; ring
      have hR : (fun x => ((a : ℂ) * (uLp : B0579.Plane → B0581.Vel) x 0) * (B0579.pd 1 ψ x : ℂ) -
          ((a : ℂ) * (uLp : B0579.Plane → B0581.Vel) x 1) * (B0579.pd 0 ψ x : ℂ)) =
          fun x => (a : ℂ) * ((uLp : B0579.Plane → B0581.Vel) x 0 * (B0579.pd 1 ψ x : ℂ) -
            (uLp : B0579.Plane → B0581.Vel) x 1 * (B0579.pd 0 ψ x : ℂ)) := by
        funext x; ring
      rw [hL, hR, integral_const_mul, integral_const_mul, hCan_bs.2.2 ψ hψ]
  exact canonical_bs_unique_ae (w := a • w) hc1 hm haw hbs_smul
    (fun j => ⟨hasWeakCellDerivC_smul_real a
        (hasWeakCellDerivC_of_hasWeakVelDeriv (j := j) (B0583.hasWeakVelDeriv_velocity_q c hm.le w hw.2)),
      hasWeakCellDerivC_smul_real a
        (hasWeakCellDerivC_of_hasWeakVelDeriv (j := j) (B0583.hasWeakVelDeriv_velocity_eta c hm.le w hw.2))⟩)
    (fun j => (ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj j : B0581.Vel →L[ℂ] ℂ)
      (Lp.memLp uqLp)).const_mul (a : ℂ))
    (fun j => (ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj j : B0581.Vel →L[ℂ] ℂ)
      (Lp.memLp uηLp)).const_mul (a : ℂ))

theorem canonical_bs_add_ae {c m : ℝ} (hc1 : 1 ≤ c) (hm : 1 < m)
    {w₁ w₂ : Xmc c m} (hw₁ : HasZeroCirculationR c w₁) (hw₂ : HasZeroCirculationR c w₂)
    (hw₁₂ : HasZeroCirculationR c ((w₁ + w₂ : Xmc c m) : B0579.Plane → ℝ)) :
    haveI : Fact (0 < c) := ⟨by linarith⟩
    (∀ j : Fin 2,
      (fun x => (B0583.velocity c hm.le (w₁ + w₂) hw₁₂.2 : B0579.Plane → B0581.Vel) x j) =ᵐ[
          volume.restrict (B0579.cell c)]
        (fun x => (B0583.velocity c hm.le w₁ hw₁.2 : B0579.Plane → B0581.Vel) x j +
          (B0583.velocity c hm.le w₂ hw₂.2 : B0579.Plane → B0581.Vel) x j)) ∧
    (∀ j : Fin 2,
      (fun x => (B0583.velGradQ c hm.le (w₁ + w₂) : B0579.Plane → B0581.Vel) x j) =ᵐ[
          volume.restrict (B0579.cell c)]
        (fun x => (B0583.velGradQ c hm.le w₁ : B0579.Plane → B0581.Vel) x j +
          (B0583.velGradQ c hm.le w₂ : B0579.Plane → B0581.Vel) x j)) ∧
    (∀ j : Fin 2,
      (fun x => (B0583.velGradEta c hm.le (w₁ + w₂) hw₁₂.2 : B0579.Plane → B0581.Vel) x j) =ᵐ[
          volume.restrict (B0579.cell c)]
        (fun x => (B0583.velGradEta c hm.le w₁ hw₁.2 : B0579.Plane → B0581.Vel) x j +
          (B0583.velGradEta c hm.le w₂ hw₂.2 : B0579.Plane → B0581.Vel) x j)) := by
  have hc0 : 0 < c := by linarith
  have : Fact (0 < c) := ⟨hc0⟩
  set uLp₁ := B0583.velocity c hm.le w₁ hw₁.2
  set uqLp₁ := B0583.velGradQ c hm.le w₁
  set uηLp₁ := B0583.velGradEta c hm.le w₁ hw₁.2
  set uLp₂ := B0583.velocity c hm.le w₂ hw₂.2
  set uqLp₂ := B0583.velGradQ c hm.le w₂
  set uηLp₂ := B0583.velGradEta c hm.le w₂ hw₂.2
  have hCan₁ : IIIa.IsBiotSavart c (fun x => ((w₁ x : ℝ) : ℂ))
      (fun x j => (uLp₁ : B0579.Plane → B0581.Vel) x j) :=
    Short.IIIa.CTE.velocityIsBiotSavart c m hm w₁ hw₁.2
  have hCan₂ : IIIa.IsBiotSavart c (fun x => ((w₂ x : ℝ) : ℂ))
      (fun x j => (uLp₂ : B0579.Plane → B0581.Vel) x j) :=
    Short.IIIa.CTE.velocityIsBiotSavart c m hm w₂ hw₂.2
  have hdq₁ : ∀ j, IIIa.HasWeakCellDerivC c 0
      (fun x => (uLp₁ : B0579.Plane → B0581.Vel) x j)
      (fun x => (uqLp₁ : B0579.Plane → B0581.Vel) x j) :=
    fun j => hasWeakCellDerivC_of_hasWeakVelDeriv (j := j) (B0583.hasWeakVelDeriv_velocity_q c hm.le w₁ hw₁.2)
  have hdη₁ : ∀ j, IIIa.HasWeakCellDerivC c 1
      (fun x => (uLp₁ : B0579.Plane → B0581.Vel) x j)
      (fun x => (uηLp₁ : B0579.Plane → B0581.Vel) x j) :=
    fun j => hasWeakCellDerivC_of_hasWeakVelDeriv (j := j) (B0583.hasWeakVelDeriv_velocity_eta c hm.le w₁ hw₁.2)
  have hdq₂ : ∀ j, IIIa.HasWeakCellDerivC c 0
      (fun x => (uLp₂ : B0579.Plane → B0581.Vel) x j)
      (fun x => (uqLp₂ : B0579.Plane → B0581.Vel) x j) :=
    fun j => hasWeakCellDerivC_of_hasWeakVelDeriv (j := j) (B0583.hasWeakVelDeriv_velocity_q c hm.le w₂ hw₂.2)
  have hdη₂ : ∀ j, IIIa.HasWeakCellDerivC c 1
      (fun x => (uLp₂ : B0579.Plane → B0581.Vel) x j)
      (fun x => (uηLp₂ : B0579.Plane → B0581.Vel) x j) :=
    fun j => hasWeakCellDerivC_of_hasWeakVelDeriv (j := j) (B0583.hasWeakVelDeriv_velocity_eta c hm.le w₂ hw₂.2)
  have hw_add_ae : (fun x => ((((w₁ + w₂ : Xmc c m) : B0579.Plane → ℝ) x : ℝ) : ℂ)) =ᵐ[
      volume.restrict (B0579.cell c)] (fun x => ((w₁ x : ℝ) : ℂ) + ((w₂ x : ℝ) : ℂ)) := by
    filter_upwards [(B0579.ac_cellMeasure c m).ae_le (Lp.coeFn_add w₁ w₂)] with x hx
    rw [hx]; simp [Pi.add_apply]
  have hbs_add : IIIa.IsBiotSavart c
      (fun x => ((((w₁ + w₂ : Xmc c m) : B0579.Plane → ℝ) x : ℝ) : ℂ))
      (fun x j => (uLp₁ : B0579.Plane → B0581.Vel) x j +
        (uLp₂ : B0579.Plane → B0581.Vel) x j) := by
    refine isBiotSavart_congr_ae hw_add_ae.symm (fun _ => Filter.EventuallyEq.refl _ _) ?_
    refine ⟨fun j => (hCan₁.1 j).add (hCan₂.1 j), fun ψ hψ => ?_, fun ψ hψ => ?_⟩
    · have hI₁0 : IntegrableOn
          (fun x => (uLp₁ : B0579.Plane → B0581.Vel) x 0 * (B0579.pd 0 ψ x : ℂ))
          (B0579.cell c) volume := ((hdq₁ 0).1 ψ hψ).1
      have hI₁1 : IntegrableOn
          (fun x => (uLp₁ : B0579.Plane → B0581.Vel) x 1 * (B0579.pd 1 ψ x : ℂ))
          (B0579.cell c) volume := ((hdη₁ 1).1 ψ hψ).1
      have hI₂0 : IntegrableOn
          (fun x => (uLp₂ : B0579.Plane → B0581.Vel) x 0 * (B0579.pd 0 ψ x : ℂ))
          (B0579.cell c) volume := ((hdq₂ 0).1 ψ hψ).1
      have hI₂1 : IntegrableOn
          (fun x => (uLp₂ : B0579.Plane → B0581.Vel) x 1 * (B0579.pd 1 ψ x : ℂ))
          (B0579.cell c) volume := ((hdη₂ 1).1 ψ hψ).1
      have hI₁ : IntegrableOn
          (fun x => (uLp₁ : B0579.Plane → B0581.Vel) x 0 * (B0579.pd 0 ψ x : ℂ) +
            (uLp₁ : B0579.Plane → B0581.Vel) x 1 * (B0579.pd 1 ψ x : ℂ))
          (B0579.cell c) volume := hI₁0.add hI₁1
      have hI₂ : IntegrableOn
          (fun x => (uLp₂ : B0579.Plane → B0581.Vel) x 0 * (B0579.pd 0 ψ x : ℂ) +
            (uLp₂ : B0579.Plane → B0581.Vel) x 1 * (B0579.pd 1 ψ x : ℂ))
          (B0579.cell c) volume := hI₂0.add hI₂1
      have hfun : (fun x => ((uLp₁ : B0579.Plane → B0581.Vel) x 0 +
            (uLp₂ : B0579.Plane → B0581.Vel) x 0) * (B0579.pd 0 ψ x : ℂ) +
          ((uLp₁ : B0579.Plane → B0581.Vel) x 1 +
            (uLp₂ : B0579.Plane → B0581.Vel) x 1) * (B0579.pd 1 ψ x : ℂ)) =
          fun x => ((uLp₁ : B0579.Plane → B0581.Vel) x 0 * (B0579.pd 0 ψ x : ℂ) +
            (uLp₁ : B0579.Plane → B0581.Vel) x 1 * (B0579.pd 1 ψ x : ℂ)) +
          ((uLp₂ : B0579.Plane → B0581.Vel) x 0 * (B0579.pd 0 ψ x : ℂ) +
            (uLp₂ : B0579.Plane → B0581.Vel) x 1 * (B0579.pd 1 ψ x : ℂ)) := by
        funext x; ring
      have hc1_div : (∫ x in B0579.cell c,
          ((uLp₁ : B0579.Plane → B0581.Vel) x 0 * (B0579.pd 0 ψ x : ℂ) +
            (uLp₁ : B0579.Plane → B0581.Vel) x 1 * (B0579.pd 1 ψ x : ℂ))) = 0 :=
        hCan₁.2.1 ψ hψ
      have hc2_div : (∫ x in B0579.cell c,
          ((uLp₂ : B0579.Plane → B0581.Vel) x 0 * (B0579.pd 0 ψ x : ℂ) +
            (uLp₂ : B0579.Plane → B0581.Vel) x 1 * (B0579.pd 1 ψ x : ℂ))) = 0 :=
        hCan₂.2.1 ψ hψ
      rw [hfun, integral_add hI₁ hI₂, hc1_div, hc2_div, add_zero]
    · have hIw₁ : IntegrableOn (fun x => ((w₁ x : ℝ) : ℂ) * (ψ x : ℂ)) (B0579.cell c) volume :=
        (Complex.ofRealCLM.integrable_comp (PartIIbF4Aux.integrableOn_mul_cylTest c m hψ w₁)).congr
          (Eventually.of_forall fun x => by simp)
      have hIw₂ : IntegrableOn (fun x => ((w₂ x : ℝ) : ℂ) * (ψ x : ℂ)) (B0579.cell c) volume :=
        (Complex.ofRealCLM.integrable_comp (PartIIbF4Aux.integrableOn_mul_cylTest c m hψ w₂)).congr
          (Eventually.of_forall fun x => by simp)
      have hIR₁0 : IntegrableOn
          (fun x => (uLp₁ : B0579.Plane → B0581.Vel) x 0 * (B0579.pd 1 ψ x : ℂ))
          (B0579.cell c) volume := ((hdη₁ 0).1 ψ hψ).1
      have hIR₁1 : IntegrableOn
          (fun x => (uLp₁ : B0579.Plane → B0581.Vel) x 1 * (B0579.pd 0 ψ x : ℂ))
          (B0579.cell c) volume := ((hdq₁ 1).1 ψ hψ).1
      have hIR₂0 : IntegrableOn
          (fun x => (uLp₂ : B0579.Plane → B0581.Vel) x 0 * (B0579.pd 1 ψ x : ℂ))
          (B0579.cell c) volume := ((hdη₂ 0).1 ψ hψ).1
      have hIR₂1 : IntegrableOn
          (fun x => (uLp₂ : B0579.Plane → B0581.Vel) x 1 * (B0579.pd 0 ψ x : ℂ))
          (B0579.cell c) volume := ((hdq₂ 1).1 ψ hψ).1
      have hIR₁ : IntegrableOn
          (fun x => (uLp₁ : B0579.Plane → B0581.Vel) x 0 * (B0579.pd 1 ψ x : ℂ) -
            (uLp₁ : B0579.Plane → B0581.Vel) x 1 * (B0579.pd 0 ψ x : ℂ))
          (B0579.cell c) volume := hIR₁0.sub hIR₁1
      have hIR₂ : IntegrableOn
          (fun x => (uLp₂ : B0579.Plane → B0581.Vel) x 0 * (B0579.pd 1 ψ x : ℂ) -
            (uLp₂ : B0579.Plane → B0581.Vel) x 1 * (B0579.pd 0 ψ x : ℂ))
          (B0579.cell c) volume := hIR₂0.sub hIR₂1
      have hL : (fun x => (((w₁ x : ℝ) : ℂ) + ((w₂ x : ℝ) : ℂ)) * (ψ x : ℂ)) =
          fun x => ((w₁ x : ℝ) : ℂ) * (ψ x : ℂ) + ((w₂ x : ℝ) : ℂ) * (ψ x : ℂ) := by
        funext x; ring
      have hR : (fun x => ((uLp₁ : B0579.Plane → B0581.Vel) x 0 +
            (uLp₂ : B0579.Plane → B0581.Vel) x 0) * (B0579.pd 1 ψ x : ℂ) -
          ((uLp₁ : B0579.Plane → B0581.Vel) x 1 +
            (uLp₂ : B0579.Plane → B0581.Vel) x 1) * (B0579.pd 0 ψ x : ℂ)) =
          fun x => ((uLp₁ : B0579.Plane → B0581.Vel) x 0 * (B0579.pd 1 ψ x : ℂ) -
            (uLp₁ : B0579.Plane → B0581.Vel) x 1 * (B0579.pd 0 ψ x : ℂ)) +
          ((uLp₂ : B0579.Plane → B0581.Vel) x 0 * (B0579.pd 1 ψ x : ℂ) -
            (uLp₂ : B0579.Plane → B0581.Vel) x 1 * (B0579.pd 0 ψ x : ℂ)) := by
        funext x; ring
      have hc1_curl : (∫ x in B0579.cell c, ((w₁ x : ℝ) : ℂ) * (ψ x : ℂ)) =
          ∫ x in B0579.cell c,
            ((uLp₁ : B0579.Plane → B0581.Vel) x 0 * (B0579.pd 1 ψ x : ℂ) -
              (uLp₁ : B0579.Plane → B0581.Vel) x 1 * (B0579.pd 0 ψ x : ℂ)) :=
        hCan₁.2.2 ψ hψ
      have hc2_curl : (∫ x in B0579.cell c, ((w₂ x : ℝ) : ℂ) * (ψ x : ℂ)) =
          ∫ x in B0579.cell c,
            ((uLp₂ : B0579.Plane → B0581.Vel) x 0 * (B0579.pd 1 ψ x : ℂ) -
              (uLp₂ : B0579.Plane → B0581.Vel) x 1 * (B0579.pd 0 ψ x : ℂ)) :=
        hCan₂.2.2 ψ hψ
      rw [hL, hR, integral_add hIw₁ hIw₂, integral_add hIR₁ hIR₂, hc1_curl, hc2_curl]
  exact canonical_bs_unique_ae (w := w₁ + w₂) hc1 hm hw₁₂ hbs_add
    (fun j => ⟨hasWeakCellDerivC_add (hdq₁ j) (hdq₂ j), hasWeakCellDerivC_add (hdη₁ j) (hdη₂ j)⟩)
    (fun j => (ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj j : B0581.Vel →L[ℂ] ℂ)
        (Lp.memLp uqLp₁)).add
      (ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj j : B0581.Vel →L[ℂ] ℂ)
        (Lp.memLp uqLp₂)))
    (fun j => (ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj j : B0581.Vel →L[ℂ] ℂ)
        (Lp.memLp uηLp₁)).add
      (ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj j : B0581.Vel →L[ℂ] ℂ)
        (Lp.memLp uηLp₂)))

/-- From the propagator Duhamel formula `ω s = U s 0 (ω 0) + ∫ t in Ioc 0 s, U s t (f t)` with
`f` Bochner integrable on `Ioc 0 p.H`, `s ↦ ω s` is strongly continuous on `Icc 0 p.H`. -/
theorem continuousOn_omega_of_duhamel {m : ℝ} {p : Params} (hH : 0 < p.H)
    {U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)} (hU : IsCoupledPropagator m p U)
    {M_U : ℝ} (hMU0 : 0 ≤ M_U)
    (hU_bd : ∀ t s : ℝ, 0 ≤ t → t ≤ s → s ≤ p.H → ‖U s t‖ ≤ M_U)
    {f ω : ℝ → Xmc p.c m} (hf : IntegrableOn f (Ioc 0 p.H) volume)
    (h_duh : ∀ s ∈ Icc 0 p.H, ω s = U s 0 (ω 0) + ∫ t in Ioc 0 s, U s t (f t)) :
    ContinuousOn ω (Icc 0 p.H) := by
  let W : ℝ → Xmc p.c m := fun s => ∫ t in Ioc 0 s, U s t (f t)
  have hUint : ∀ s ∈ Icc 0 p.H, IntegrableOn (fun t => U s t (f t)) (Ioc 0 s) volume :=
    fun s hs => PartIIbF4Aux.integrableOn_propagator_apply hs hMU0
      hU.id_self hU.comp_cocycle hU.strongCont hU_bd
      (hf.mono_set (Ioc_subset_Ioc_right hs.2))
  have hW_cont : ContinuousOn W (Icc 0 p.H) := by
    intro s₀ hs₀
    have hunion : Icc 0 p.H = Icc 0 s₀ ∪ Icc s₀ p.H := by
      ext s; simp only [mem_Icc, mem_union]
      exact ⟨fun h => (le_total s s₀).imp (fun hs => ⟨h.1, hs⟩) (fun hs => ⟨hs, h.2⟩),
        fun h => h.elim (fun h1 => ⟨h1.1, h1.2.trans hs₀.2⟩) (fun h2 => ⟨hs₀.1.trans h2.1, h2.2⟩)⟩
    rw [hunion, continuousWithinAt_union]
    refine ⟨?_, ?_⟩
    · -- Left continuity on `Icc 0 s₀` via dominated convergence on `volume.restrict (Ioc 0 s₀)`
      set μ₀ : Measure ℝ := volume.restrict (Ioc 0 s₀)
      let F : ℝ → ℝ → Xmc p.c m := fun s t => (Ioc 0 s).indicator (fun τ => U s τ (f τ)) t
      have hF_int_eq : ∀ s ∈ Icc 0 s₀, ∫ t, F s t ∂μ₀ = W s := by
        intro s hs
        dsimp [F, W, μ₀]
        rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
          inter_eq_self_of_subset_left (Ioc_subset_Ioc_right hs.2)]
      have hWs0 : W s₀ = ∫ t, U s₀ t (f t) ∂μ₀ := rfl
      rw [ContinuousWithinAt, hWs0]
      have hF_meas : ∀ᶠ s in 𝓝[Icc 0 s₀] s₀, AEStronglyMeasurable (F s) μ₀ := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hI := hUint s ⟨hs.1, hs.2.trans hs₀.2⟩
        have hsm_vol : AEStronglyMeasurable (F s) volume :=
          (aestronglyMeasurable_indicator_iff measurableSet_Ioc).2 hI.aestronglyMeasurable
        exact hsm_vol.mono_measure Measure.restrict_le_self
      have h_bound : ∀ᶠ s in 𝓝[Icc 0 s₀] s₀, ∀ᵐ t ∂μ₀, ‖F s t‖ ≤ M_U * ‖f t‖ := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t _
        dsimp [F]
        by_cases ht_s : t ∈ Ioc 0 s
        · rw [Set.indicator_of_mem ht_s]
          exact ((U s t).le_opNorm (f t)).trans
            (mul_le_mul_of_nonneg_right (hU_bd t s ht_s.1.le ht_s.2 (hs.2.trans hs₀.2))
              (norm_nonneg _))
        · rw [Set.indicator_of_notMem ht_s, norm_zero]
          exact mul_nonneg hMU0 (norm_nonneg _)
      have h_bd_int : Integrable (fun t => M_U * ‖f t‖) μ₀ :=
        ((hf.mono_set (Ioc_subset_Ioc_right hs₀.2)).norm).const_mul M_U
      have h_lim : ∀ᵐ t ∂μ₀, Tendsto (fun s => F s t) (𝓝[Icc 0 s₀] s₀) (𝓝 (U s₀ t (f t))) := by
        have hae_ne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ s₀ :=
          compl_mem_ae_iff.2 (measure_singleton s₀)
        filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hae_ne] with t ht hne
        have ht_lt : t < s₀ := lt_of_le_of_ne ht.2 hne
        have hIoi_mem : Ioi t ∈ 𝓝[Icc 0 s₀] s₀ :=
          nhdsWithin_le_nhds (Ioi_mem_nhds ht_lt)
        have ht_Icc : t ∈ Icc 0 p.H := ⟨ht.1.le, ht.2.trans hs₀.2⟩
        have hcont_t := ((hU.strongCont t ht_Icc (f t)).continuousWithinAt
          ⟨ht_lt.le, hs₀.2⟩).tendsto
        have hsub_nhds : 𝓝[Icc 0 s₀] s₀ ≤ 𝓝[Icc t p.H] s₀ := by
          refine nhdsWithin_le_iff.2 ?_
          filter_upwards [self_mem_nhdsWithin, hIoi_mem] with s hs hts
          exact ⟨hts.le, hs.2.trans hs₀.2⟩
        refine (hcont_t.mono_left hsub_nhds).congr' ?_
        filter_upwards [hIoi_mem] with s hts
        exact (Set.indicator_of_mem (show t ∈ Ioc 0 s from ⟨ht.1, hts.le⟩)
          (fun τ => U s τ (f τ))).symm
      have hdct := tendsto_integral_filter_of_dominated_convergence
        (fun t => M_U * ‖f t‖) hF_meas h_bound h_bd_int h_lim
      refine hdct.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact hF_int_eq s hs
    · -- Right continuity on `Icc s₀ p.H` via cocycle split `W s = U s s₀ (W s₀) + ∫_{s₀}^s U s t (f t)`
      rw [ContinuousWithinAt]
      have h1 : Tendsto (fun s => U s s₀ (W s₀)) (𝓝[Icc s₀ p.H] s₀) (𝓝 (W s₀)) := by
        have hc := (hU.strongCont s₀ hs₀ (W s₀)).continuousWithinAt ⟨le_rfl, hs₀.2⟩
        rwa [ContinuousWithinAt, hU.id_self s₀ hs₀, ContinuousLinearMap.id_apply] at hc
      have h2 : Tendsto (fun s => ∫ t in Ioc s₀ s, U s t (f t)) (𝓝[Icc s₀ p.H] s₀) (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hmeas_tend : Tendsto ((volume.restrict (Ioc 0 p.H)) ∘ fun s : ℝ => Ioc s₀ s)
            (𝓝[Icc s₀ p.H] s₀) (𝓝 0) := by
          have hofr : Tendsto (fun s : ℝ => ENNReal.ofReal (s - s₀)) (𝓝[Icc s₀ p.H] s₀) (𝓝 0) := by
            have hsub0 : Tendsto (fun s : ℝ => s - s₀) (𝓝[Icc s₀ p.H] s₀) (𝓝 0) := by
              have hcont_sub : Continuous (fun s : ℝ => s - s₀) :=
                continuous_id.sub continuous_const
              simpa using (hcont_sub.tendsto s₀).mono_left nhdsWithin_le_nhds
            simpa using ENNReal.tendsto_ofReal hsub0
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hofr
            (Eventually.of_forall fun _ => zero_le) ?_
          filter_upwards [self_mem_nhdsWithin] with s _
          calc (volume.restrict (Ioc 0 p.H)) (Ioc s₀ s)
              ≤ volume (Ioc s₀ s) := Measure.restrict_apply_le _ _
            _ = ENNReal.ofReal (s - s₀) := Real.volume_Ioc
        have hint_tend : Tendsto
            (fun s : ℝ => ∫ t in Ioc s₀ s, ‖f t‖ ∂volume.restrict (Ioc 0 p.H))
            (𝓝[Icc s₀ p.H] s₀) (𝓝 0) :=
          hf.norm.tendsto_setIntegral_nhds_zero hmeas_tend
        have hmul_tend : Tendsto
            (fun s : ℝ => M_U * ∫ t in Ioc s₀ s, ‖f t‖ ∂volume.restrict (Ioc 0 p.H))
            (𝓝[Icc s₀ p.H] s₀) (𝓝 0) := by
          simpa using hint_tend.const_mul M_U
        refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmul_tend
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hsub : Ioc s₀ s ⊆ Ioc 0 p.H := fun t ht => ⟨hs₀.1.trans_lt ht.1, ht.2.trans hs.2⟩
        rw [Measure.restrict_restrict_of_subset hsub]
        have hInt_tail : IntegrableOn (fun t => U s t (f t)) (Ioc s₀ s) volume :=
          (hUint s ⟨hs₀.1.trans hs.1, hs.2⟩).mono_set (Ioc_subset_Ioc_left hs₀.1)
        have hf_tail : IntegrableOn (fun t => ‖f t‖) (Ioc s₀ s) volume := (hf.mono_set hsub).norm
        have hpw : ∀ᵐ t ∂volume.restrict (Ioc s₀ s), ‖U s t (f t)‖ ≤ M_U * ‖f t‖ := by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact ((U s t).le_opNorm (f t)).trans
            (mul_le_mul_of_nonneg_right
              (hU_bd t s (hs₀.1.trans ht.1.le) ht.2 hs.2) (norm_nonneg _))
        calc ‖∫ t in Ioc s₀ s, U s t (f t)‖
            ≤ ∫ t in Ioc s₀ s, ‖U s t (f t)‖ := norm_integral_le_integral_norm _
          _ ≤ ∫ t in Ioc s₀ s, M_U * ‖f t‖ := integral_mono_ae hInt_tail.norm (hf_tail.const_mul M_U) hpw
          _ = M_U * ∫ t in Ioc s₀ s, ‖f t‖ := integral_const_mul M_U _
      have hsum : Tendsto (fun s => U s s₀ (W s₀) + ∫ t in Ioc s₀ s, U s t (f t))
          (𝓝[Icc s₀ p.H] s₀) (𝓝 (W s₀)) := by
        simpa using h1.add h2
      refine hsum.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs_H : s ∈ Icc 0 p.H := ⟨hs₀.1.trans hs.1, hs.2⟩
      have hI_full := hUint s hs_H
      have hsplit : W s = (∫ t in Ioc 0 s₀, U s t (f t)) + ∫ t in Ioc s₀ s, U s t (f t) := by
        dsimp [W]
        rw [← Ioc_union_Ioc_eq_Ioc hs₀.1 hs.1,
          setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
            (hI_full.mono_set (Ioc_subset_Ioc_right hs.1))
            (hI_full.mono_set (Ioc_subset_Ioc_left hs₀.1))]
      have hcoc_eq : (∫ t in Ioc 0 s₀, U s t (f t)) = U s s₀ (W s₀) := by
        have hcongr : ∫ t in Ioc 0 s₀, U s t (f t) = ∫ t in Ioc 0 s₀, U s s₀ (U s₀ t (f t)) := by
          refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
          have hc := ContinuousLinearMap.ext_iff.mp
            (hU.comp_cocycle t s₀ s ht.1.le ht.2 hs.1 hs.2) (f t)
          simpa using hc.symm
        rw [hcongr, (U s s₀).integral_comp_comm (hUint s₀ hs₀)]
      rw [hsplit, hcoc_eq]
  exact ((hU.strongCont 0 ⟨le_rfl, hH.le⟩ (ω 0)).add hW_cont).congr fun s hs => h_duh s hs

lemma aestronglyMeasurable_profCurl_sub_entrance {c m : ℝ} {p : Params}
    {zq zη : CProf} {α : E2} {w0 : Xmc c m}
    (sm_zq : StronglyMeasurable zq) (sm_zη : StronglyMeasurable zη)
    (hw0 : (w0 : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure c m] entranceVorticityComb p α)
    (s : ℝ) :
    AEStronglyMeasurable
      (fun x => profCurl zq zη (s, x) - ((entranceVorticityComb p α x : ℝ) : ℂ))
      (B0579.cellMeasure c 0) := by
  rw [cellMeasure_zero_eq_cellVol c]
  have hm_curl : StronglyMeasurable (fun x : B0579.Plane => profCurl zq zη (s, x)) := by
    have hmeas_s : Measurable (fun x : B0579.Plane => ((s, x) : Coord)) :=
      measurable_const.prodMk measurable_id
    have hsm_q := sm_zq.comp_measurable hmeas_s
    have hsm_η := sm_zη.comp_measurable hmeas_s
    exact ((EuclideanSpace.proj 1 : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable hsm_q).sub
      ((EuclideanSpace.proj 0 : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable hsm_η)
  have hm_w0 : AEStronglyMeasurable (w0 : B0579.Plane → ℝ) (volume.restrict (B0579.cell c)) :=
    (Lp.memLp w0).aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure c m)
  have hm_entR : AEStronglyMeasurable (entranceVorticityComb p α)
      (volume.restrict (B0579.cell c)) :=
    hm_w0.congr ((B0579.ac_cellMeasure c m).ae_le hw0)
  have hm_entC : AEStronglyMeasurable (fun x => ((entranceVorticityComb p α x : ℝ) : ℂ))
      (volume.restrict (B0579.cell c)) :=
    Complex.ofRealCLM.continuous.comp_aestronglyMeasurable hm_entR
  exact hm_curl.aestronglyMeasurable.sub hm_entC

end GreenUncurlHelp

open GreenUncurlHelp

/-! ## 3. Biot–Savart uncurl leaf step and conditional assembly of `GreenVorticityUncurl` -/

/-- **Remaining Biot–Savart uncurl leaf step for `PartII-b:F6/2`** (SP 2219–2222, 2254–2268):
given the Green selector operators `(U, P_term, Piu, Pic, G_c, G_u, Γ_α)` on `[0, p.H]` and the
linear body-source/curl-source maps `(b0Of, b0qOf, b0ηOf, gOf, gqOf, gηOf, curlSourceOf)`,
uncurling the zero-circulation Green vorticity trajectory
`ω_F(s) = (∫ t in Ioc 0 s, G_c s t (curlSourceOf F t)) - (∫ t in Ioc s p.H, G_u s t (curlSourceOf F t))`
via the zero-circulation cylinder Biot–Savart operator (`hbs`) produces `ℝ`-linear maps
`αOf : HpR p.c →ₗ[ℝ] E2` and `zOf, zqOf, zηOf : HpR p.c →ₗ[ℝ] CProf` solving
`IsMeridionalCorrectionOn p p.H (gOf F) (zOf F) (zqOf F) (zηOf F) (αOf F)` with measurable
`sliceH1Norm` bounded at each `s ∈ Ioc 0 p.H` by `ENNReal.ofReal (C_bs * p.c ^ N_bs * ‖ω_F(s)‖)`. -/
def GreenBiotSavartUncurlStep : Prop :=
  ∀ m : ℝ, 8 < m →
  ∀ (C_bs : ℝ) (N_bs : ℕ), 0 < C_bs →
    (∀ c : ℝ, 1 ≤ c → ∀ w : Xmc c m, HasZeroCirculationR c w →
      ∃ u uq uη : B0579.Plane → Fin 2 → ℂ,
        IIIa.IsBiotSavart c (fun x => ((w x : ℝ) : ℂ)) u ∧
        (∀ j : Fin 2, IIIa.HasWeakCellDerivC c 0 (fun x => u x j) (fun x => uq x j) ∧
          IIIa.HasWeakCellDerivC c 1 (fun x => u x j) (fun x => uη x j)) ∧
        (∑ j : Fin 2,
          (eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell c)) +
            eLpNorm (fun x => uq x j) 2 (volume.restrict (B0579.cell c)) +
            eLpNorm (fun x => uη x j) 2 (volume.restrict (B0579.cell c)))) ≤
          ENNReal.ofReal (C_bs * c ^ N_bs * ‖w‖)) →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ (a' b' C_green C_src C_L1 : ℝ) (k_src : ℕ),
    0 < a' → a' < b' → b' < lam.re / (1 + Sig) ^ 2 → 0 < C_green → 0 < C_src → 0 ≤ C_L1 →
  ∀ (dm dp : ℝ), 0 < dm →
  ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → 1 ≤ p.c → p.ν ≤ 1 →
    p.ageCut = Sig → p.mode = q →
    ∀ (U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
      (P_term : Xmc p.c m →L[ℝ] E2)
      (Piu Pic : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
      (G_c G_u : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
      (Γ_α : ℝ → (Xmc p.c m →L[ℝ] E2)),
      IsCoupledPropagator m p U →
      (∀ t ∈ Icc 0 p.H,
        (Piu t).comp (Piu t) = Piu t ∧
        Pic t = ContinuousLinearMap.id ℝ (Xmc p.c m) - Piu t ∧
        ‖Piu t‖ ≤ C_green ∧ ‖Pic t‖ ≤ C_green ∧
        ‖Γ_α t‖ ≤ C_green * Real.exp (-b' * t)) →
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H →
        (U t s).comp (Piu s) = (Piu t).comp (U t s) ∧
        (U t s).comp (Pic s) = (Pic t).comp (U t s) ∧
        G_c t s = (U t s).comp (Pic s) ∧
        (U t s).comp (G_u s t) = Piu t ∧
        ‖G_c t s‖ ≤ C_green * Real.exp (a' * (t - s)) ∧
        ‖G_u s t‖ ≤ C_green * Real.exp (-b' * (t - s))) →
      (∀ f : ℝ → Xmc p.c m, IntegrableOn f (Ioc 0 p.H) volume →
        (∀ᵐ t ∂volume, t ∈ Ioc 0 p.H → HasZeroCirculationR p.c (f t)) →
        let ω : ℝ → Xmc p.c m := fun s =>
          (∫ t in Ioc 0 s, G_c s t (f t)) - (∫ t in Ioc s p.H, G_u s t (f t))
        let α : E2 := ∫ t in Ioc 0 p.H, Γ_α t (f t)
        ((ω 0 : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure p.c m] entranceVorticityComb p α) ∧
        P_term (ω p.H) = 0 ∧
        (∀ s ∈ Icc 0 p.H, HasZeroCirculationR p.c (ω s)) ∧
        (∀ φ : B0579.Plane → ℝ, B0579.IsCylTest p.c φ → ∀ s ∈ Icc 0 p.H,
          ∫ x in B0579.cell p.c, ω s x * φ x =
            (∫ x in B0579.cell p.c, ω 0 x * φ x) +
              ∫ r in (0 : ℝ)..s, ∫ x in B0579.cell p.c,
                (cylCoupledIntegrand p.train (ω r) r φ x + f r x * φ x)) ∧
        (∀ s ∈ Icc 0 p.H,
          ‖ω s‖ + ‖α‖ ≤ C_green * Real.exp (a' * p.H) * ∫ t in Ioc 0 p.H, ‖f t‖)) →
    ∀ (b0Of b0qOf b0ηOf gOf gqOf gηOf : HpR p.c →ₗ[ℝ] CProf)
      (curlSourceOf : HpR p.c →ₗ[ℝ] (ℝ → Xmc p.c m)),
      (∀ F : HpR p.c,
        InFlatClass p.c bgp (b0Of F) ∧
        IsFlatResponse p.ν 0 (toProf p.c F) (b0Of F) ∧
        HasWeakVec vQ0 dZero (b0Of F) (b0qOf F) ∧
        HasWeakVec vEta dZero (b0Of F) (b0ηOf F) ∧
        QPeriodic p.c (gOf F) ∧
        HasWeakVec vQ0 dZero (gOf F) (gqOf F) ∧
        HasWeakVec vEta dZero (gOf F) (gηOf F) ∧
        IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf F) ∧
        Measurable (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ∧
        sLpNorm (13 / 8) p.H (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ≤
          ENNReal.ofReal (C_src * (p.ν ^ k_src)⁻¹ * ‖F‖) ∧
        IntegrableOn (curlSourceOf F) (Ioc 0 p.H) volume ∧
        (∀ᵐ t ∂volume, t ∈ Ioc 0 p.H → HasZeroCirculationR p.c (curlSourceOf F t)) ∧
        (∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
          ∀ᵐ x ∂volume, x ∈ B0579.cell p.c →
            ((curlSourceOf F s x : ℝ) : ℂ) = profCurl (gqOf F) (gηOf F) (s, x)) ∧
        ∫ t in Ioc 0 p.H, ‖curlSourceOf F t‖ ≤ C_L1 * ‖F‖) →
      ∃ (αOf : HpR p.c →ₗ[ℝ] E2)
        (zOf zqOf zηOf : HpR p.c →ₗ[ℝ] CProf),
        ∀ F : HpR p.c,
          let f : ℝ → Xmc p.c m := curlSourceOf F
          let ω : ℝ → Xmc p.c m := fun s =>
            (∫ t in Ioc 0 s, G_c s t (f t)) - (∫ t in Ioc s p.H, G_u s t (f t))
          αOf F = (∫ t in Ioc 0 p.H, Γ_α t (f t)) ∧
          IsMeridionalCorrectionOn p p.H (gOf F) (zOf F) (zqOf F) (zηOf F) (αOf F) ∧
          Measurable (sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F)) ∧
          ∀ s ∈ Ioc 0 p.H,
            sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s ≤
              ENNReal.ofReal (C_bs * p.c ^ N_bs * ‖ω s‖)

/-- **Assembly of `GreenVorticityUncurl` (`PartII-b:F6/2`)** from `GreenBiotSavartUncurlStep`,
`green_omega_alpha_norm_le`, `mkContinuous_alphaMap`, and `sliceH1Norm_add_alpha_le`. -/
theorem greenVorticityUncurl_of
    (hStep : GreenBiotSavartUncurlStep) :
    GreenVorticityUncurl := by
  intro m hm C_bs N_bs hC_bs hbs Sig lam q hSig hEig a' b' C_green C_src C_L1 k_src
    ha'0 hb'1 hb'2 hC_green hC_src hC_L1 dm dp hdm p d hreg hc1 hν1 hAge hMode
    hGS_ex b0Of b0qOf b0ηOf gOf gqOf gηOf curlSourceOf hSrc_F
  obtain ⟨U, P_term, Piu, Pic, G_c, G_u, Γ_α, hU, hPt, hKer, hGreen⟩ := hGS_ex
  obtain ⟨αOf, zOf, zqOf, zηOf, hUnc⟩ :=
    hStep m hm C_bs N_bs hC_bs hbs Sig lam q hSig hEig a' b' C_green C_src C_L1 k_src
      ha'0 hb'1 hb'2 hC_green hC_src hC_L1 dm dp hdm p d hreg hc1 hν1 hAge hMode
      U P_term Piu Pic G_c G_u Γ_α hU hPt hKer hGreen
      b0Of b0qOf b0ηOf gOf gqOf gηOf curlSourceOf hSrc_F
  have hH_pos : 0 < p.H := by
    rw [Params.H, hAge]
    exact div_pos hSig p.ν_pos
  have hα_bd : ∀ F : HpR p.c,
      ‖αOf F‖ ≤ C_green * Real.exp (a' * p.H) * C_L1 * ‖F‖ := by
    intro F
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hf_int, hf_circ, _, hf_L1⟩ := hSrc_F F
    obtain ⟨_, _, _, _, h_gn⟩ := hGreen (curlSourceOf F) hf_int hf_circ
    obtain ⟨hα_eq, _, _, _⟩ := hUnc F
    rw [hα_eq]
    exact (green_omega_alpha_norm_le hC_green h_gn hf_L1 ⟨le_rfl, hH_pos.le⟩).2.2
  let αMap : HpR p.c →L[ℝ] E2 := mkContinuous_alphaMap αOf hα_bd
  refine ⟨αMap, zOf, zqOf, zηOf, fun F => ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hf_int, hf_circ, _, hf_L1⟩ := hSrc_F F
  obtain ⟨_, _, _, _, h_gn⟩ := hGreen (curlSourceOf F) hf_int hf_circ
  obtain ⟨hα_eq, h_merid, hm_H1, h_slice⟩ := hUnc F
  refine ⟨h_merid, hm_H1, fun s hs => ?_⟩
  have hs_Icc : s ∈ Icc 0 p.H := ⟨hs.1.le, hs.2⟩
  obtain ⟨_, hw_bd, hα_bd'⟩ := green_omega_alpha_norm_le hC_green h_gn hf_L1 hs_Icc
  change sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s + ENNReal.ofReal ‖αOf F‖ ≤ _
  rw [hα_eq]
  exact sliceH1Norm_add_alpha_le p.c_pos.le hC_bs hC_green hC_L1 (h_slice s hs) hw_bd hα_bd'

/-- **Assembly of `GreenVorticityUncurlDuhamel` (`PartII-b:F6/2`, SP 2219–2222, 2254–2268)** from
the three parallel leaves `SliceBiotSavartGlue` (`PartII-b:F6/2/1`), `CylKEqBiotSavartAe`
(`PartII-b:F6/2/2`), and `GreenVorticityToVelocityEq` (`PartII-b:F6/2/3`), extending basis-wise
via a Hamel basis of `HpR p.c` over `ℝ` and canonical `B0583` `=ᵐ`-linearity. -/
theorem greenVorticityUncurlDuhamel_of_leaves
    (hGlue : GreenVorticityUncurlNeeded.SliceBiotSavartGlue)
    (hK : GreenVorticityUncurlNeeded.CylKEqBiotSavartAe)
    (hVelEq : GreenVorticityUncurlNeeded.GreenVorticityToVelocityEq) :
    GreenVorticityUncurlDuhamel := by
  intro m hm C_bs N_bs hC_bs hbs Sig lam q hSig hEig a' b' C_green C_src C_L1 k_src
    ha'0 hb'1 hb'2 hC_green hC_src hC_L1 dm dp hdm p d hreg hc1 hν1 hAge hMode
    hGS_ex b0Of b0qOf b0ηOf gOf gqOf gηOf curlSourceOf hSrc_F
  obtain ⟨U, Iu0, P_term, Piu, Pic, G_c, G_u, Γ_α, M_U,
    hMU_nn, hU_bd, hIu0, hU, hPt, hKer, hGreen⟩ := hGS_ex
  have hH_pos : 0 < p.H := by
    rw [Params.H, hAge]
    exact div_pos hSig p.ν_pos
  have hc_pos : 0 < p.c := p.c_pos
  have : Fact (0 < p.c) := ⟨hc_pos⟩
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hm1' : (1 : ℝ) < m := by linarith
  have hm0 : 0 ≤ m := by linarith
  let ωOf : HpR p.c → ℝ → Xmc p.c m := fun F s =>
    (∫ t in Ioc 0 s, G_c s t (curlSourceOf F t)) -
      (∫ t in Ioc s p.H, G_u s t (curlSourceOf F t))
  let αFun : HpR p.c → E2 := fun F => ∫ t in Ioc 0 p.H, Γ_α t (curlSourceOf F t)
  have hGreen_F : ∀ F : HpR p.c,
      ((ωOf F 0 : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure p.c m] entranceVorticityComb p (αFun F)) ∧
      P_term (ωOf F p.H) = 0 ∧
      (∀ s ∈ Icc 0 p.H, HasZeroCirculationR p.c (ωOf F s)) ∧
      (∀ φ : B0579.Plane → ℝ, B0579.IsCylTest p.c φ → ∀ s ∈ Icc 0 p.H,
        ∫ x in B0579.cell p.c, ωOf F s x * φ x =
          (∫ x in B0579.cell p.c, ωOf F 0 x * φ x) +
            ∫ r in (0 : ℝ)..s, ∫ x in B0579.cell p.c,
              (cylCoupledIntegrand p.train (ωOf F r) r φ x + curlSourceOf F r x * φ x)) ∧
      (∀ s ∈ Icc 0 p.H,
        ‖ωOf F s‖ + ‖αFun F‖ ≤
          C_green * Real.exp (a' * p.H) * ∫ t in Ioc 0 p.H, ‖curlSourceOf F t‖) ∧
      IntegrableOn (fun t => Γ_α t (curlSourceOf F t)) (Ioc 0 p.H) volume ∧
      ωOf F 0 = Iu0 (αFun F) ∧
      (∀ s ∈ Icc 0 p.H, ωOf F s = U s 0 (ωOf F 0) + ∫ t in Ioc 0 s, U s t (curlSourceOf F t)) := by
    intro F
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hf_int, hf_circ, _, _⟩ := hSrc_F F
    exact hGreen (curlSourceOf F) hf_int hf_circ
  let αOf : HpR p.c →ₗ[ℝ] E2 :=
    { toFun := αFun
      map_add' := fun F₁ F₂ => by
        have hI₁ := (hGreen_F F₁).2.2.2.2.2.1
        have hI₂ := (hGreen_F F₂).2.2.2.2.2.1
        dsimp [αFun]
        have hfun : (fun t => Γ_α t (curlSourceOf (F₁ + F₂) t)) =
            fun t => Γ_α t (curlSourceOf F₁ t) + Γ_α t (curlSourceOf F₂ t) := by
          funext t; simp [map_add]
        rw [hfun, integral_add hI₁ hI₂]
      map_smul' := fun a F => by
        dsimp [αFun]
        have hfun : (fun t => Γ_α t (curlSourceOf (a • F) t)) =
            fun t => a • Γ_α t (curlSourceOf F t) := by
          funext t; simp [map_smul]
        rw [hfun, integral_smul] }
  have hω_zero : ∀ s ∈ Icc 0 p.H, ωOf 0 s = 0 := by
    intro s hs
    have hduh := (hGreen_F 0).2.2.2.2.2.2.2 s hs
    have h0 : ωOf 0 0 = 0 := by
      rw [(hGreen_F 0).2.2.2.2.2.2.1]
      change Iu0 (αOf 0) = 0
      simp
    rw [hduh, h0, map_zero, zero_add]
    simp [map_zero]
  have hω_add : ∀ F₁ F₂ : HpR p.c, ∀ s ∈ Icc 0 p.H,
      ωOf (F₁ + F₂) s = ωOf F₁ s + ωOf F₂ s := by
    intro F₁ F₂ s hs
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hf₁, _, _, _⟩ := hSrc_F F₁
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hf₂, _, _, _⟩ := hSrc_F F₂
    have hU₁ := PartIIbF4Aux.integrableOn_propagator_apply hs hMU_nn
      hU.id_self hU.comp_cocycle hU.strongCont hU_bd (hf₁.mono_set (Ioc_subset_Ioc_right hs.2))
    have hU₂ := PartIIbF4Aux.integrableOn_propagator_apply hs hMU_nn
      hU.id_self hU.comp_cocycle hU.strongCont hU_bd (hf₂.mono_set (Ioc_subset_Ioc_right hs.2))
    have h0 : ωOf (F₁ + F₂) 0 = ωOf F₁ 0 + ωOf F₂ 0 := by
      rw [(hGreen_F (F₁ + F₂)).2.2.2.2.2.2.1, (hGreen_F F₁).2.2.2.2.2.2.1,
        (hGreen_F F₂).2.2.2.2.2.2.1]
      change Iu0 (αOf (F₁ + F₂)) = Iu0 (αOf F₁) + Iu0 (αOf F₂)
      rw [map_add, map_add]
    rw [(hGreen_F (F₁ + F₂)).2.2.2.2.2.2.2 s hs, (hGreen_F F₁).2.2.2.2.2.2.2 s hs,
      (hGreen_F F₂).2.2.2.2.2.2.2 s hs, h0, map_add]
    have hfun : (fun t => U s t (curlSourceOf (F₁ + F₂) t)) =
        fun t => U s t (curlSourceOf F₁ t) + U s t (curlSourceOf F₂ t) := by
      funext t; simp [map_add]
    rw [hfun, integral_add hU₁ hU₂]
    abel
  have hω_smul : ∀ (a : ℝ) (F : HpR p.c), ∀ s ∈ Icc 0 p.H,
      ωOf (a • F) s = a • ωOf F s := by
    intro a F s hs
    have h0 : ωOf (a • F) 0 = a • ωOf F 0 := by
      rw [(hGreen_F (a • F)).2.2.2.2.2.2.1, (hGreen_F F).2.2.2.2.2.2.1]
      change Iu0 (αOf (a • F)) = a • Iu0 (αOf F)
      rw [map_smul, map_smul]
    rw [(hGreen_F (a • F)).2.2.2.2.2.2.2 s hs, (hGreen_F F).2.2.2.2.2.2.2 s hs, h0,
      map_smul, smul_add]
    congr 1
    have hfun : (fun t => U s t (curlSourceOf (a • F) t)) =
        fun t => a • U s t (curlSourceOf F t) := by
      funext t; simp [map_smul]
    rw [hfun, integral_smul]
  have h_slice_bd : ∀ (F : HpR p.c) (z zq zη : CProf) (s : ℝ) (hs : s ∈ Ioc 0 p.H),
      (fun x => z (s, x)) =ᵐ[volume.restrict (B0579.cell p.c)]
        toCMerid (fun x j =>
          (B0583.velocity p.c hm1 (ωOf F s)
            ((hGreen_F F).2.2.1 s ⟨hs.1.le, hs.2⟩).2 : B0579.Plane → B0581.Vel) x j) →
      (fun x => zq (s, x)) =ᵐ[volume.restrict (B0579.cell p.c)]
        toCMerid (fun x j =>
          (B0583.velGradQ p.c hm1 (ωOf F s) : B0579.Plane → B0581.Vel) x j) →
      (fun x => zη (s, x)) =ᵐ[volume.restrict (B0579.cell p.c)]
        toCMerid (fun x j =>
          (B0583.velGradEta p.c hm1 (ωOf F s)
            ((hGreen_F F).2.2.1 s ⟨hs.1.le, hs.2⟩).2 : B0579.Plane → B0581.Vel) x j) →
      sliceH1Norm p.c z zq zη s ≤ ENNReal.ofReal (C_bs * p.c ^ N_bs * ‖ωOf F s‖) := by
    intro F z zq zη s hs hz_ae hzq_ae hzη_ae
    have hw_s := (hGreen_F F).2.2.1 s ⟨hs.1.le, hs.2⟩
    obtain ⟨u, uq, uη, hu_bs, hu_deriv, hu_bd⟩ := hbs p.c hc1 (ωOf F s) hw_s
    obtain ⟨_, _, _, hcan_bd⟩ := canonical_bs_ae_eq_of_hbs hc1 hm1' hw_s hu_bs hu_deriv hu_bd
    set uLp := B0583.velocity p.c hm1 (ωOf F s) hw_s.2
    set uqLp := B0583.velGradQ p.c hm1 (ωOf F s)
    set uηLp := B0583.velGradEta p.c hm1 (ωOf F s) hw_s.2
    refine (sliceH1Norm_le_of_coord_sum
      (fun j => (ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj j : B0581.Vel →L[ℂ] ℂ)
        (Lp.memLp uLp)).aestronglyMeasurable)
      (fun j => (ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj j : B0581.Vel →L[ℂ] ℂ)
        (Lp.memLp uqLp)).aestronglyMeasurable)
      (fun j => (ContinuousLinearMap.comp_memLp' (EuclideanSpace.proj j : B0581.Vel →L[ℂ] ℂ)
        (Lp.memLp uηLp)).aestronglyMeasurable)
      hz_ae hzq_ae hzη_ae).trans hcan_bd
  -- Pointwise Biot–Savart uncurl on each F ∈ HpR p.c
  have h_pt : ∀ F : HpR p.c,
      ∃ z zq zη : CProf,
        StronglyMeasurable z ∧ StronglyMeasurable zq ∧ StronglyMeasurable zη ∧
        IsMeridionalCorrectionOn p p.H (gOf F) z zq zη (αOf F) ∧
        ∀ s : ℝ, ∀ hs : s ∈ Ioc 0 p.H,
          (fun x => z (s, x)) =ᵐ[volume.restrict (B0579.cell p.c)]
            toCMerid (fun x j =>
              (B0583.velocity p.c hm1 (ωOf F s)
                ((hGreen_F F).2.2.1 s ⟨hs.1.le, hs.2⟩).2 : B0579.Plane → B0581.Vel) x j) ∧
          (fun x => zq (s, x)) =ᵐ[volume.restrict (B0579.cell p.c)]
            toCMerid (fun x j =>
              (B0583.velGradQ p.c hm1 (ωOf F s) : B0579.Plane → B0581.Vel) x j) ∧
          (fun x => zη (s, x)) =ᵐ[volume.restrict (B0579.cell p.c)]
            toCMerid (fun x j =>
              (B0583.velGradEta p.c hm1 (ωOf F s)
                ((hGreen_F F).2.2.1 s ⟨hs.1.le, hs.2⟩).2 : B0579.Plane → B0581.Vel) x j) := by
    intro F
    obtain ⟨hb0_cls, _, _, _, hg_per, hgq, hgη, hg_src, hm_gH1, hg_lp,
      hf_int, _, hf_curl, hf_L1⟩ := hSrc_F F
    obtain ⟨hω0_ae, _, hω_circ, hω_weak, hω_gn, _, _, hω_duh⟩ := hGreen_F F
    have hω_cont : ContinuousOn (ωOf F) (Icc 0 p.H) :=
      continuousOn_omega_of_duhamel hH_pos hU hMU_nn hU_bd hf_int hω_duh
    obtain ⟨z, zq, zη, sm_z, sm_zq, sm_zη, per_z, per_zq, per_zη, wq_z, wη_z, sol_z, hae_z⟩ :=
      hGlue m hm p.c p.H hc1 hH_pos (ωOf F) hω_cont hω_circ
    have hM_z : ∃ M : ℝ, ∀ s ∈ Ioc 0 p.H, sliceH1Norm p.c z zq zη s ≤ ENNReal.ofReal M := by
      refine ⟨C_bs * p.c ^ N_bs * (C_green * Real.exp (a' * p.H) * C_L1 * ‖F‖), fun s hs => ?_⟩
      obtain ⟨hz_s, hzq_s, hzη_s⟩ := hae_z s hs
      have h1 := h_slice_bd F z zq zη s hs hz_s hzq_s hzη_s
      have hw_bd := (green_omega_alpha_norm_le hC_green hω_gn hf_L1 ⟨hs.1.le, hs.2⟩).2.1
      have hCbs_nn : 0 ≤ C_bs * p.c ^ N_bs := mul_nonneg hC_bs.le (pow_nonneg hc_pos.le N_bs)
      exact h1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hw_bd hCbs_nn))
    have hslice_bs : ∀ s ∈ Ioc 0 p.H,
        IIIa.IsBiotSavart p.c (fun x => ((ωOf F s x : ℝ) : ℂ)) (fun x j => z (s, x) j) ∧
        (∀ j : Fin 2,
          IIIa.HasWeakCellDerivC p.c 0 (fun x => z (s, x) j) (fun x => zq (s, x) j) ∧
          IIIa.HasWeakCellDerivC p.c 1 (fun x => z (s, x) j) (fun x => zη (s, x) j)) ∧
        (fun x (j : Fin 2) => ((UnforcedLeray.Cyl.K p.c (ωOf F s) x j : ℝ) : ℂ)) =ᵐ[
            volume.restrict (B0579.cell p.c)]
          (fun x j => z (s, x) j) := by
      intro s hs
      obtain ⟨hz_s, hzq_s, hzη_s⟩ := hae_z s hs
      have hw_s := hω_circ s ⟨hs.1.le, hs.2⟩
      have hCan_bs : IIIa.IsBiotSavart p.c (fun x => ((ωOf F s x : ℝ) : ℂ))
          (fun x j => (B0583.velocity p.c hm1 (ωOf F s) hw_s.2 : B0579.Plane → B0581.Vel) x j) :=
        Short.IIIa.CTE.velocityIsBiotSavart p.c m hm1' (ωOf F s) hw_s.2
      have hz_bs : IIIa.IsBiotSavart p.c (fun x => ((ωOf F s x : ℝ) : ℂ))
          (fun x j => z (s, x) j) :=
        isBiotSavart_congr_ae (Filter.EventuallyEq.refl _ _)
          (fun j => (ae_coord_of_toCMerid hz_s j).symm) hCan_bs
      have hz_deriv : ∀ j : Fin 2,
          IIIa.HasWeakCellDerivC p.c 0 (fun x => z (s, x) j) (fun x => zq (s, x) j) ∧
          IIIa.HasWeakCellDerivC p.c 1 (fun x => z (s, x) j) (fun x => zη (s, x) j) := fun j =>
        ⟨hasWeakCellDerivC_congr_ae
            (ae_coord_of_toCMerid hz_s j).symm (ae_coord_of_toCMerid hzq_s j).symm
            (hasWeakCellDerivC_of_hasWeakVelDeriv (j := j)
              (B0583.hasWeakVelDeriv_velocity_q p.c hm1 (ωOf F s) hw_s.2)),
          hasWeakCellDerivC_congr_ae
            (ae_coord_of_toCMerid hz_s j).symm (ae_coord_of_toCMerid hzη_s j).symm
            (hasWeakCellDerivC_of_hasWeakVelDeriv (j := j)
              (B0583.hasWeakVelDeriv_velocity_eta p.c hm1 (ωOf F s) hw_s.2))⟩
      exact ⟨hz_bs, hz_deriv, hK m hm p.c hc1 (ωOf F s) hw_s (fun x j => z (s, x) j) hz_bs⟩
    have hg_lt_top : sLpNorm (13 / 8) p.H (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) < ⊤ :=
      lt_of_le_of_lt hg_lp ENNReal.ofReal_lt_top
    have heq_z := hVelEq m hm p d dm dp hreg hc1 hH_pos (ωOf F) (curlSourceOf F)
      hω_cont hf_int hω_circ hω_weak z zq zη sm_z sm_zq sm_zη per_z per_zq per_zη
      wq_z wη_z sol_z hM_z hslice_bs
      (b0Of F) (b0qOf F) (b0ηOf F) (gOf F) (gqOf F) (gηOf F)
      hb0_cls hg_per hgq hgη hg_src hm_gH1 hg_lt_top hf_curl
    have hcurl_ae : ∀ s ∈ Ioc 0 p.H,
        (fun x => profCurl zq zη (s, x)) =ᵐ[volume.restrict (B0579.cell p.c)]
          (fun x => ((ωOf F s x : ℝ) : ℂ)) := by
      intro s hs
      obtain ⟨_, hzq_s, hzη_s⟩ := hae_z s hs
      have hw_s := hω_circ s ⟨hs.1.le, hs.2⟩
      have hcan_curl := canonical_bs_weakCurl_ae hc1 hm1' hw_s
      filter_upwards [ae_coord_of_toCMerid hzq_s 1, ae_coord_of_toCMerid hzη_s 0, hcan_curl]
        with x hq1 hη0 hc_eq
      dsimp [profCurl]
      rw [hq1, hη0, hc_eq]
    have hinit_z := initial_curl_of_tendsto_omega hm0 hH_pos
      (tendsto_omega_zero_of_duhamel hH_pos hU hMU_nn hU_bd hf_int hω_duh)
      hω0_ae hcurl_ae
    exact ⟨z, zq, zη, sm_z, sm_zq, sm_zη,
      ⟨per_z, wq_z, wη_z, sol_z, heq_z, hinit_z⟩, hae_z⟩
  -- Extend linearly from a Hamel basis of HpR p.c over ℝ
  let B := Module.Basis.ofVectorSpace ℝ (HpR p.c)
  choose z_bas zq_bas zη_bas h_bas using fun i => h_pt (B i)
  let zOf : HpR p.c →ₗ[ℝ] CProf := B.constr ℝ z_bas
  let zqOf : HpR p.c →ₗ[ℝ] CProf := B.constr ℝ zq_bas
  let zηOf : HpR p.c →ₗ[ℝ] CProf := B.constr ℝ zη_bas
  have h_lin : ∀ F : HpR p.c,
      StronglyMeasurable (zOf F) ∧ StronglyMeasurable (zqOf F) ∧ StronglyMeasurable (zηOf F) ∧
      IsMeridionalCorrectionOn p p.H (gOf F) (zOf F) (zqOf F) (zηOf F) (αOf F) ∧
      ∀ s : ℝ, ∀ hs : s ∈ Ioc 0 p.H,
        (fun x => zOf F (s, x)) =ᵐ[volume.restrict (B0579.cell p.c)]
          toCMerid (fun x j =>
            (B0583.velocity p.c hm1 (ωOf F s)
              ((hGreen_F F).2.2.1 s ⟨hs.1.le, hs.2⟩).2 : B0579.Plane → B0581.Vel) x j) ∧
        (fun x => zqOf F (s, x)) =ᵐ[volume.restrict (B0579.cell p.c)]
          toCMerid (fun x j =>
            (B0583.velGradQ p.c hm1 (ωOf F s) : B0579.Plane → B0581.Vel) x j) ∧
        (fun x => zηOf F (s, x)) =ᵐ[volume.restrict (B0579.cell p.c)]
          toCMerid (fun x j =>
            (B0583.velGradEta p.c hm1 (ωOf F s)
              ((hGreen_F F).2.2.1 s ⟨hs.1.le, hs.2⟩).2 : B0579.Plane → B0581.Vel) x j) := by
    let S : Submodule ℝ (HpR p.c) :=
      { carrier := {F |
          StronglyMeasurable (zOf F) ∧ StronglyMeasurable (zqOf F) ∧ StronglyMeasurable (zηOf F) ∧
          IsMeridionalCorrectionOn p p.H (gOf F) (zOf F) (zqOf F) (zηOf F) (αOf F) ∧
          ∀ s : ℝ, ∀ hs : s ∈ Ioc 0 p.H,
            (fun x => zOf F (s, x)) =ᵐ[volume.restrict (B0579.cell p.c)]
              toCMerid (fun x j =>
                (B0583.velocity p.c hm1 (ωOf F s)
                  ((hGreen_F F).2.2.1 s ⟨hs.1.le, hs.2⟩).2 : B0579.Plane → B0581.Vel) x j) ∧
            (fun x => zqOf F (s, x)) =ᵐ[volume.restrict (B0579.cell p.c)]
              toCMerid (fun x j =>
                (B0583.velGradQ p.c hm1 (ωOf F s) : B0579.Plane → B0581.Vel) x j) ∧
            (fun x => zηOf F (s, x)) =ᵐ[volume.restrict (B0579.cell p.c)]
              toCMerid (fun x j =>
                (B0583.velGradEta p.c hm1 (ωOf F s)
                  ((hGreen_F F).2.2.1 s ⟨hs.1.le, hs.2⟩).2 : B0579.Plane → B0581.Vel) x j)}
        zero_mem' := by
          change StronglyMeasurable (zOf 0) ∧ _
          simp only [map_zero]
          refine ⟨stronglyMeasurable_zero, stronglyMeasurable_zero, stronglyMeasurable_zero,
            isMeridionalCorrectionOn_zero p p.H, fun s hs => ?_⟩
          have hs_Icc : s ∈ Icc 0 p.H := ⟨hs.1.le, hs.2⟩
          have hw0 : HasZeroCirculationR p.c ((0 : Xmc p.c m) : B0579.Plane → ℝ) := by
            simpa [hω_zero s hs_Icc] using (hGreen_F 0).2.2.1 s hs_Icc
          obtain ⟨hu0, huq0, huη0⟩ := canonical_bs_zero_ae hc1 hm1' hw0
          refine ⟨?_, ?_, ?_⟩
          · refine toCMerid_ae_of_coord fun j => ?_
            have h0j : (fun x => (B0583.velocity p.c hm1 (ωOf 0 s)
                  ((hGreen_F 0).2.2.1 s hs_Icc).2 : B0579.Plane → B0581.Vel) x j) =ᵐ[
                volume.restrict (B0579.cell p.c)] 0 := by
              simpa [hω_zero s hs_Icc] using hu0 j
            exact h0j.symm
          · refine toCMerid_ae_of_coord fun j => ?_
            have h0j : (fun x => (B0583.velGradQ p.c hm1 (ωOf 0 s) :
                  B0579.Plane → B0581.Vel) x j) =ᵐ[
                volume.restrict (B0579.cell p.c)] 0 := by
              simpa [hω_zero s hs_Icc] using huq0 j
            exact h0j.symm
          · refine toCMerid_ae_of_coord fun j => ?_
            have h0j : (fun x => (B0583.velGradEta p.c hm1 (ωOf 0 s)
                  ((hGreen_F 0).2.2.1 s hs_Icc).2 : B0579.Plane → B0581.Vel) x j) =ᵐ[
                volume.restrict (B0579.cell p.c)] 0 := by
              simpa [hω_zero s hs_Icc] using huη0 j
            exact h0j.symm
        add_mem' := by
          intro F₁ F₂ h₁ h₂
          change StronglyMeasurable (zOf (F₁ + F₂)) ∧ _
          rcases h₁ with ⟨smz₁, smzq₁, smzη₁, mc₁, ae₁⟩
          rcases h₂ with ⟨smz₂, smzq₂, smzη₂, mc₂, ae₂⟩
          simp only [map_add]
          have hm₁ : ∀ᶠ s in 𝓝[Ioi 0] 0, AEStronglyMeasurable
              (fun x => profCurl (zqOf F₁) (zηOf F₁) (s, x) -
                ((entranceVorticityComb p (αOf F₁) x : ℝ) : ℂ))
              (B0579.cellMeasure p.c 0) :=
            Eventually.of_forall
              (aestronglyMeasurable_profCurl_sub_entrance smzq₁ smzη₁ (hGreen_F F₁).1)
          have hm₂ : ∀ᶠ s in 𝓝[Ioi 0] 0, AEStronglyMeasurable
              (fun x => profCurl (zqOf F₂) (zηOf F₂) (s, x) -
                ((entranceVorticityComb p (αOf F₂) x : ℝ) : ℂ))
              (B0579.cellMeasure p.c 0) :=
            Eventually.of_forall
              (aestronglyMeasurable_profCurl_sub_entrance smzq₂ smzη₂ (hGreen_F F₂).1)
          refine ⟨smz₁.add smz₂, smzq₁.add smzq₂, smzη₁.add smzη₂,
            isMeridionalCorrectionOn_add hm₁ hm₂ mc₁ mc₂, fun s hs => ?_⟩
          have hs_Icc : s ∈ Icc 0 p.H := ⟨hs.1.le, hs.2⟩
          obtain ⟨hz₁, hzq₁, hzη₁⟩ := ae₁ s hs
          obtain ⟨hz₂, hzq₂, hzη₂⟩ := ae₂ s hs
          have hw₁ := (hGreen_F F₁).2.2.1 s hs_Icc
          have hw₂ := (hGreen_F F₂).2.2.1 s hs_Icc
          have hw₁₂ : HasZeroCirculationR p.c ((ωOf F₁ s + ωOf F₂ s : Xmc p.c m) : B0579.Plane → ℝ) := by
            simpa [hω_add F₁ F₂ s hs_Icc] using (hGreen_F (F₁ + F₂)).2.2.1 s hs_Icc
          obtain ⟨hu_add, huq_add, huη_add⟩ := canonical_bs_add_ae hc1 hm1' hw₁ hw₂ hw₁₂
          refine ⟨?_, ?_, ?_⟩
          · refine toCMerid_ae_of_coord fun j => ?_
            have hcan_j : (fun x => (B0583.velocity p.c hm1 (ωOf (F₁ + F₂) s)
                  ((hGreen_F (F₁ + F₂)).2.2.1 s hs_Icc).2 : B0579.Plane → B0581.Vel) x j) =ᵐ[
                volume.restrict (B0579.cell p.c)]
                (fun x => (B0583.velocity p.c hm1 (ωOf F₁ s) hw₁.2 : B0579.Plane → B0581.Vel) x j +
                  (B0583.velocity p.c hm1 (ωOf F₂ s) hw₂.2 : B0579.Plane → B0581.Vel) x j) := by
              simpa [hω_add F₁ F₂ s hs_Icc] using hu_add j
            filter_upwards [ae_coord_of_toCMerid hz₁ j, ae_coord_of_toCMerid hz₂ j, hcan_j]
              with x hx₁ hx₂ hcx
            simp only [Pi.add_apply, PiLp.add_apply, hx₁, hx₂, hcx]
          · refine toCMerid_ae_of_coord fun j => ?_
            have hcan_j : (fun x => (B0583.velGradQ p.c hm1 (ωOf (F₁ + F₂) s) :
                  B0579.Plane → B0581.Vel) x j) =ᵐ[volume.restrict (B0579.cell p.c)]
                (fun x => (B0583.velGradQ p.c hm1 (ωOf F₁ s) : B0579.Plane → B0581.Vel) x j +
                  (B0583.velGradQ p.c hm1 (ωOf F₂ s) : B0579.Plane → B0581.Vel) x j) := by
              simpa [hω_add F₁ F₂ s hs_Icc] using huq_add j
            filter_upwards [ae_coord_of_toCMerid hzq₁ j, ae_coord_of_toCMerid hzq₂ j, hcan_j]
              with x hx₁ hx₂ hcx
            simp only [Pi.add_apply, PiLp.add_apply, hx₁, hx₂, hcx]
          · refine toCMerid_ae_of_coord fun j => ?_
            have hcan_j : (fun x => (B0583.velGradEta p.c hm1 (ωOf (F₁ + F₂) s)
                  ((hGreen_F (F₁ + F₂)).2.2.1 s hs_Icc).2 : B0579.Plane → B0581.Vel) x j) =ᵐ[
                volume.restrict (B0579.cell p.c)]
                (fun x => (B0583.velGradEta p.c hm1 (ωOf F₁ s) hw₁.2 : B0579.Plane → B0581.Vel) x j +
                  (B0583.velGradEta p.c hm1 (ωOf F₂ s) hw₂.2 : B0579.Plane → B0581.Vel) x j) := by
              simpa [hω_add F₁ F₂ s hs_Icc] using huη_add j
            filter_upwards [ae_coord_of_toCMerid hzη₁ j, ae_coord_of_toCMerid hzη₂ j, hcan_j]
              with x hx₁ hx₂ hcx
            simp only [Pi.add_apply, PiLp.add_apply, hx₁, hx₂, hcx]
        smul_mem' := by
          intro a F hF
          change StronglyMeasurable (zOf (a • F)) ∧ _
          rcases hF with ⟨smz, smzq, smzη, mc, aeF⟩
          simp only [map_smul]
          refine ⟨smz.const_smul a, smzq.const_smul a, smzη.const_smul a,
            isMeridionalCorrectionOn_smul_real a mc, fun s hs => ?_⟩
          have hs_Icc : s ∈ Icc 0 p.H := ⟨hs.1.le, hs.2⟩
          obtain ⟨hz, hzq, hzη⟩ := aeF s hs
          have hw := (hGreen_F F).2.2.1 s hs_Icc
          have haw : HasZeroCirculationR p.c ((a • ωOf F s : Xmc p.c m) : B0579.Plane → ℝ) := by
            simpa [hω_smul a F s hs_Icc] using (hGreen_F (a • F)).2.2.1 s hs_Icc
          obtain ⟨hu_sm, huq_sm, huη_sm⟩ := canonical_bs_smul_ae hc1 hm1' a hw haw
          refine ⟨?_, ?_, ?_⟩
          · refine toCMerid_ae_of_coord fun j => ?_
            have hcan_j : (fun x => (B0583.velocity p.c hm1 (ωOf (a • F) s)
                  ((hGreen_F (a • F)).2.2.1 s hs_Icc).2 : B0579.Plane → B0581.Vel) x j) =ᵐ[
                volume.restrict (B0579.cell p.c)]
                (fun x => (a : ℂ) * (B0583.velocity p.c hm1 (ωOf F s) hw.2 :
                  B0579.Plane → B0581.Vel) x j) := by
              simpa [hω_smul a F s hs_Icc] using hu_sm j
            filter_upwards [ae_coord_of_toCMerid hz j, hcan_j] with x hx hcx
            simp only [Pi.smul_apply, PiLp.smul_apply, Complex.real_smul, hx, hcx]
          · refine toCMerid_ae_of_coord fun j => ?_
            have hcan_j : (fun x => (B0583.velGradQ p.c hm1 (ωOf (a • F) s) :
                  B0579.Plane → B0581.Vel) x j) =ᵐ[volume.restrict (B0579.cell p.c)]
                (fun x => (a : ℂ) * (B0583.velGradQ p.c hm1 (ωOf F s) :
                  B0579.Plane → B0581.Vel) x j) := by
              simpa [hω_smul a F s hs_Icc] using huq_sm j
            filter_upwards [ae_coord_of_toCMerid hzq j, hcan_j] with x hx hcx
            simp only [Pi.smul_apply, PiLp.smul_apply, Complex.real_smul, hx, hcx]
          · refine toCMerid_ae_of_coord fun j => ?_
            have hcan_j : (fun x => (B0583.velGradEta p.c hm1 (ωOf (a • F) s)
                  ((hGreen_F (a • F)).2.2.1 s hs_Icc).2 : B0579.Plane → B0581.Vel) x j) =ᵐ[
                volume.restrict (B0579.cell p.c)]
                (fun x => (a : ℂ) * (B0583.velGradEta p.c hm1 (ωOf F s) hw.2 :
                  B0579.Plane → B0581.Vel) x j) := by
              simpa [hω_smul a F s hs_Icc] using huη_sm j
            filter_upwards [ae_coord_of_toCMerid hzη j, hcan_j] with x hx hcx
            simp only [Pi.smul_apply, PiLp.smul_apply, Complex.real_smul, hx, hcx] }
    have h_range : Set.range B ⊆ (S : Set (HpR p.c)) := by
      rintro _ ⟨i, rfl⟩
      change StronglyMeasurable (zOf (B i)) ∧ _
      simp only [zOf, zqOf, zηOf, Module.Basis.constr_basis]
      exact h_bas i
    have h_top : S = ⊤ :=
      top_unique (by rw [← B.span_eq]; exact Submodule.span_le.2 h_range)
    intro F
    have hmem : F ∈ S := by rw [h_top]; exact Submodule.mem_top
    exact hmem
  have hα_bd : ∀ F : HpR p.c,
      ‖αOf F‖ ≤ C_green * Real.exp (a' * p.H) * C_L1 * ‖F‖ := by
    intro F
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hf_L1⟩ := hSrc_F F
    exact (green_omega_alpha_norm_le hC_green (hGreen_F F).2.2.2.2.1 hf_L1 ⟨le_rfl, hH_pos.le⟩).2.2
  let αMap : HpR p.c →L[ℝ] E2 := mkContinuous_alphaMap αOf hα_bd
  refine ⟨αMap, zOf, zqOf, zηOf, fun F => ?_⟩
  rcases h_lin F with ⟨sm_z, sm_zq, sm_zη, mc_F, hae_F⟩
  have hm_H1 : Measurable (sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F)) :=
    CylProjectionSub.measurable_sliceH1Norm_cp p.c sm_z sm_zq sm_zη
  refine ⟨mc_F, hm_H1, fun s hs => ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hf_L1⟩ := hSrc_F F
  obtain ⟨hz_s, hzq_s, hzη_s⟩ := hae_F s hs
  obtain ⟨_, hw_bd, hα_bd'⟩ :=
    green_omega_alpha_norm_le hC_green (hGreen_F F).2.2.2.2.1 hf_L1 ⟨hs.1.le, hs.2⟩
  exact sliceH1Norm_add_alpha_le hc_pos.le hC_bs hC_green hC_L1
    (h_slice_bd F (zOf F) (zqOf F) (zηOf F) s hs hz_s hzq_s hzη_s) hw_bd hα_bd'

theorem greenVorticityUncurlDuhamel_proof : UnforcedLeray.Short.IIb.GreenVorticityUncurlDuhamel :=
  greenVorticityUncurlDuhamel_of_leaves
    GreenVorticityUncurlNeeded.sliceBiotSavartGlue_proof
    GreenVorticityUncurlNeeded.cylKEqBiotSavartAe_proof
    GreenVorticityUncurlNeeded.greenVorticityToVelocityEq_proof

end UnforcedLeray.Short.IIb

end
