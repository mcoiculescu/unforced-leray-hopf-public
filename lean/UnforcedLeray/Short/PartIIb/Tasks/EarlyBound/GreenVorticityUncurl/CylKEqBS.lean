import UnforcedLeray.Short.PartIIb.Tasks.EarlyBound.GreenVorticityUncurl.Needed
import UnforcedLeray.Short.PartIIb.Tasks.InteractionCylinder.CylWeightedKernel
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.TranspApprox
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelAdjoint

/-!
# Part II-b, task `PartII-b:F6/2/2`: `Cyl.K c w =ᵐ u` for zero-circulation `X_{m,c}` vorticity

Source of record: `the November 2 reference manuscript` (SP), lines 2081–2084,
2258–2262, and 3230–3240.

Proves `cylKEqBiotSavartAe_proof : CylKEqBiotSavartAe`:
1. `IIIa.ladTestDensity` approximates `w : Xmc c m` (`m > 8`, `1 ≤ c`, zero circulation) in `Xmc c m`
   by smooth zero-circulation cylinder tests `a_n`.
2. For each test `a_n`, `IIIa.kerVel c (a_n)` satisfies `IIIa.IsKernelBiotSavart c (a_n)`
   (`kerVelFarField_of`, `kerVelDivFree_of`, `kerVelCurl_of`), agrees a.e. on `B0579.cell c` with
   `Cyl.K c (a_n)`, and by `IIIa.ladKernelVel` + `IIIa.kernelBiotSavartUnique` satisfies
   `IIIa.IsBiotSavart c (fun x => ((a_n x : ℝ) : ℂ)) (fun x j => ((Cyl.K c (a_n) x j : ℝ) : ℂ))`.
3. `IIIa.ladBSSub` and `IIIa.ladBSBound` give `Cyl.K c (a_n) → u` in `L²(B0579.cell c)`.
4. On each finite-volume strip `S_k = [-c/2, c/2) × [-(k+1), k+1]`, the near/far decomposition of
   `CylWeightedKernel` gives `Cyl.K c (a_n) → Cyl.K c w` in `L²(S_k)` as `testLp (a_n) → w` in
   `Xmc c m`. Uniqueness of `L²(S_k)` limits and countable exhaustion of `B0579.cell c` yield
   `(fun x j => ((Cyl.K c w x j : ℝ) : ℂ)) =ᵐ[volume.restrict (B0579.cell c)] u`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIb.GreenVorticityUncurlCylKEqBSAux

open UnforcedLeray.Short.IIb

private theorem stronglyMeasurable_cylK (c : ℝ) {f : B0579.Plane → ℝ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (UnforcedLeray.Cyl.K c f) := by
  have hF : StronglyMeasurable
      (Function.uncurry fun x y : B0579.Plane => f y • UnforcedLeray.Cyl.bsKernel c (x - y)) :=
    (hf.comp_measurable measurable_snd).smul
      ((UnforcedLeray.Cyl.measurable_bsKernel c).comp
        (measurable_fst.sub measurable_snd)).stronglyMeasurable
  exact hF.integral_prod_right

private theorem stronglyMeasurable_uFarR (c r : ℝ) {f : B0579.Plane → ℝ}
    (hf : StronglyMeasurable f) :
    StronglyMeasurable (uFarR c r f) := by
  have hF : StronglyMeasurable
      (Function.uncurry fun x y : B0579.Plane => f y • kFarR c r (x - y)) :=
    (hf.comp_measurable measurable_snd).smul
      ((measurable_kFarR c r).comp (measurable_fst.sub measurable_snd)).stronglyMeasurable
  exact hF.integral_prod_right

private theorem isKernelBiotSavart_kerVel {c : ℝ} (hc : 1 ≤ c) {ψ : B0579.Plane → ℝ}
    (hψ : B0579.IsCylTest c ψ) :
    IIIa.IsKernelBiotSavart c ψ (IIIa.kerVel c ψ) := by
  have hNF : IIIa.KerNearFar := IIIa.kerNearFar
  have hFub : IIIa.KerAdjFubini := IIIa.kerAdjFubini_of hNF
  exact ⟨IIIa.kerVelFarField_of hNF c hc ψ hψ,
    IIIa.kerVelDivFree_of hFub (IIIa.kerDivPointwise_of hNF) c hc ψ hψ,
    IIIa.kerVelCurl_of hFub (IIIa.kerCurlPointwise_of hNF) c hc ψ hψ⟩

private theorem cylK_testLp_eq {c m : ℝ} {ψ : B0579.Plane → ℝ} (hψ : B0579.IsCylTest c ψ)
    (x : B0579.Plane) :
    UnforcedLeray.Cyl.K c (B0579.testLp c m hψ) x = UnforcedLeray.Cyl.K c ψ x := by
  rw [UnforcedLeray.Cyl.K, UnforcedLeray.Cyl.K, ← cell_eq_cylCell]
  refine integral_congr_ae ?_
  filter_upwards [B0579.coeFn_testLp c m hψ] with y hy
  rw [hy]

private theorem kerVel_ae_eq_cylK {c : ℝ} (hc : 1 ≤ c) {ψ : B0579.Plane → ℝ}
    (hψ : B0579.IsCylTest c ψ) :
    IIIa.kerVel c ψ =ᵐ[volume.restrict (B0579.cell c)]
      fun x j => UnforcedLeray.Cyl.K c ψ x j := by
  set U : Xmc c 3 := B0579.testLp c 3 hψ
  have haeU : (U : B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell c)] ψ :=
    B0579.coeFn_testLp c 3 hψ
  filter_upwards [ae_integrable_bsKernel hc (by norm_num : (1 : ℝ) < 3) U] with x hx
  funext j
  have h1 : IIIa.kerVel c ψ x j =
      ∫ y in B0579.cell c, U y * UnforcedLeray.Cyl.bsKernel c (x - y) j := by
    unfold IIIa.kerVel IIIa.kerD
    refine integral_congr_ae ?_
    filter_upwards [haeU] with y hy
    rw [hy]
  have hcomp := (EuclideanSpace.proj j : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).integral_comp_comm hx
  have h2 : ∫ y in B0579.cell c, U y * UnforcedLeray.Cyl.bsKernel c (x - y) j =
      UnforcedLeray.Cyl.K c U x j := by
    rw [UnforcedLeray.Cyl.K, ← cell_eq_cylCell]
    simpa using hcomp
  rw [h1, h2, cylK_testLp_eq hψ x]

private theorem isBiotSavart_cylK_of_test {c : ℝ} (hc : 1 ≤ c) {ψ : B0579.Plane → ℝ}
    (hψ : B0579.IsCylTest c ψ) (hz : ∫ x in B0579.cell c, ψ x = 0) :
    IIIa.IsBiotSavart c (fun x => ((ψ x : ℝ) : ℂ))
      (fun x j => ((UnforcedLeray.Cyl.K c ψ x j : ℝ) : ℂ)) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨ua, hka, hba⟩ := IIIa.ladKernelVel c ψ hc hψ hz
  have huniq : ua =ᵐ[volume.restrict (B0579.cell c)] IIIa.kerVel c ψ :=
    IIIa.kernelBiotSavartUnique c hc0 ψ ua (IIIa.kerVel c ψ) hka (isKernelBiotSavart_kerVel hc hψ)
  refine IIIa.KernelVelAux.bs_congr_u hba ?_
  filter_upwards [huniq, kerVel_ae_eq_cylK hc hψ] with x hx1 hx2
  funext j
  rw [congrFun hx1 j, congrFun hx2 j]

private def cellStrip (c : ℝ) (k : ℕ) : Set B0579.Plane :=
  Ico (-(c / 2)) (c / 2) ×ˢ Icc (-((k : ℝ) + 1)) ((k : ℝ) + 1)

private theorem cellStrip_subset_cell (c : ℝ) (k : ℕ) : cellStrip c k ⊆ B0579.cell c :=
  fun _ hx => ⟨hx.1, mem_univ _⟩

private theorem volume_cellStrip_lt_top (c : ℝ) (k : ℕ) : volume (cellStrip c k) < ⊤ := by
  rw [cellStrip, IIIa.tail_vol_strip0 c ((k : ℝ) + 1)]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

private theorem enorm_uFarR_coord_le {c m : ℝ} (hc : 1 ≤ c) (g : Xmc c m)
    (x : B0579.Plane) (j : Fin 2) :
    ‖uFarR c 1 g x j‖ₑ ≤ (2 * B0592.weightConst m) * ENNReal.ofReal ‖g‖ := by
  have hk_le : ∀ z : B0579.Plane, ‖kFarR c 1 z‖ₑ ≤ 2 := fun z => by
    have h := norm_kFarR_le hc zero_lt_one z
    calc ‖kFarR c 1 z‖ₑ = ‖‖kFarR c 1 z‖‖ₑ := (enorm_norm _).symm
      _ = ENNReal.ofReal ‖kFarR c 1 z‖ := Real.enorm_eq_ofReal (norm_nonneg _)
      _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal (by linarith)
      _ = 2 := by norm_num
  calc ‖uFarR c 1 g x j‖ₑ
      ≤ ‖uFarR c 1 g x‖ₑ := by
          simp only [enorm_eq_nnnorm, ENNReal.coe_le_coe]
          exact PiLp.nnnorm_apply_le (uFarR c 1 g x) j
    _ ≤ ∫⁻ y in B0579.cell c, ‖g y • kFarR c 1 (x - y)‖ₑ :=
          enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y in B0579.cell c, ‖g y‖ₑ * 2 := by
          refine lintegral_mono fun y => ?_
          rw [enorm_smul]
          gcongr
          exact hk_le (x - y)
    _ = (∫⁻ y in B0579.cell c, ‖g y‖ₑ) * 2 :=
          lintegral_mul_const _ (Lp.stronglyMeasurable g).measurable.enorm
    _ ≤ (B0592.weightConst m * ENNReal.ofReal ‖g‖) * 2 := by
          gcongr
          exact B0592.lintegral_cell_le c g
    _ = (2 * B0592.weightConst m) * ENNReal.ofReal ‖g‖ := by ring

private theorem eLpNorm_cylK_sub_cellStrip_le {c m : ℝ} (hc : 1 ≤ c) (hm : 1 < m) (k : ℕ)
    {ψ : B0579.Plane → ℝ} (hψ : B0579.IsCylTest c ψ) (w : Xmc c m) (j : Fin 2) :
    eLpNorm (fun x => UnforcedLeray.Cyl.K c ψ x j - UnforcedLeray.Cyl.K c w x j) 2
        (volume.restrict (cellStrip c k)) ≤
      (ENNReal.ofReal nearKernelConst +
          (2 * B0592.weightConst m) * volume (cellStrip c k) ^ (2 : ℝ≥0∞).toReal⁻¹) *
        ENNReal.ofReal ‖B0579.testLp c m hψ - w‖ := by
  set U : Xmc c m := B0579.testLp c m hψ
  set g : Xmc c m := U - w
  set μS : Measure B0579.Plane := volume.restrict (cellStrip c k)
  have hm0 : 0 ≤ m := by linarith
  have hsub_ae : (g : B0579.Plane → ℝ) =ᵐ[volume.restrict (B0579.cell c)] fun y => U y - w y :=
    (B0579.ac_cellMeasure c m).ae_le (Lp.coeFn_sub U w)
  have hK_diff : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      UnforcedLeray.Cyl.K c ψ x j - UnforcedLeray.Cyl.K c w x j =
        uNearR c 1 g x j + uFarR c 1 g x j := by
    filter_upwards [ae_integrable_bsKernel hc hm U, ae_integrable_bsKernel hc hm w,
      (B0579.ac_cellMeasure c m).ae_le (ae_K_eq_uNearR_add_uFarR hc zero_lt_one le_rfl hm g)]
      with x hU_int hw_int hsplit
    have h1 : UnforcedLeray.Cyl.K c g x =
        UnforcedLeray.Cyl.K c U x - UnforcedLeray.Cyl.K c w x := by
      rw [UnforcedLeray.Cyl.K, UnforcedLeray.Cyl.K, UnforcedLeray.Cyl.K, ← cell_eq_cylCell,
        ← integral_sub hU_int hw_int]
      refine integral_congr_ae ?_
      filter_upwards [hsub_ae] with y hy
      simp [hy, sub_smul]
    rw [← cylK_testLp_eq (m := m) hψ x, ← PiLp.sub_apply, ← h1, hsplit, PiLp.add_apply]
  have hK_strip : (fun x => UnforcedLeray.Cyl.K c ψ x j - UnforcedLeray.Cyl.K c w x j) =ᵐ[μS]
      fun x => uNearR c 1 g x j + uFarR c 1 g x j :=
    ae_mono (Measure.restrict_mono (cellStrip_subset_cell c k) le_rfl) hK_diff
  rw [eLpNorm_congr_ae hK_strip]
  have hmeas_near : AEStronglyMeasurable (fun x => uNearR c 1 g x j) μS :=
    ((EuclideanSpace.proj j : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).continuous.comp_stronglyMeasurable
      (stronglyMeasurable_uNearR c 1 (Lp.stronglyMeasurable g))).aestronglyMeasurable
  have hmeas_far : AEStronglyMeasurable (fun x => uFarR c 1 g x j) μS :=
    ((EuclideanSpace.proj j : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).continuous.comp_stronglyMeasurable
      (stronglyMeasurable_uFarR c 1 (Lp.stronglyMeasurable g))).aestronglyMeasurable
  have htri : eLpNorm (fun x => uNearR c 1 g x j + uFarR c 1 g x j) 2 μS ≤
      eLpNorm (fun x => uNearR c 1 g x j) 2 μS + eLpNorm (fun x => uFarR c 1 g x j) 2 μS :=
    eLpNorm_add_le hmeas_near hmeas_far (by norm_num)
  have hnear : eLpNorm (fun x => uNearR c 1 g x j) 2 μS ≤
      ENNReal.ofReal nearKernelConst * ENNReal.ofReal ‖g‖ := by
    calc eLpNorm (fun x => uNearR c 1 g x j) 2 μS
        ≤ eLpNorm (fun x => uNearR c 1 g x j) 2 (volume.restrict (B0579.cell c)) :=
            eLpNorm_mono_measure _ (Measure.restrict_mono (cellStrip_subset_cell c k) le_rfl)
      _ ≤ eLpNorm (uNearR c 1 g) 2 (volume.restrict (B0579.cell c)) :=
            eLpNorm_mono fun x => by
              simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (uNearR c 1 g x) j
      _ = eLpNorm (uNearR c 1 g) 2 (UnforcedLeray.Cyl.cellμ c) := by
            rw [cell_eq_cylCell, UnforcedLeray.Cyl.cellμ]
      _ ≤ (∫⁻ y in B0579.cell c, ‖kNearR c 1 y‖ₑ) * ENNReal.ofReal ‖g‖ :=
            eLpNorm_uNearR_le hc hm0 g
      _ ≤ ENNReal.ofReal nearKernelConst * ENNReal.ofReal ‖g‖ := by
            gcongr
            exact lintegral_kNearR_le hc le_rfl
  have hfar : eLpNorm (fun x => uFarR c 1 g x j) 2 μS ≤
      ((2 * B0592.weightConst m) * volume (cellStrip c k) ^ (2 : ℝ≥0∞).toReal⁻¹) *
        ENNReal.ofReal ‖g‖ := by
    have hb := eLpNorm_le_of_ae_enorm_bound (μ := μS) (p := 2)
      (f := fun x => uFarR c 1 g x j)
      (C := (2 * B0592.weightConst m) * ENNReal.ofReal ‖g‖)
      (Eventually.of_forall fun x => enorm_uFarR_coord_le hc g x j)
    have hvol : μS univ = volume (cellStrip c k) := Measure.restrict_apply_univ (cellStrip c k)
    rw [smul_eq_mul, hvol] at hb
    exact hb.trans_eq (by ring)
  exact htri.trans ((add_le_add hnear hfar).trans_eq (by ring))

end UnforcedLeray.Short.IIb.GreenVorticityUncurlCylKEqBSAux

namespace UnforcedLeray.Short.IIb.GreenVorticityUncurlNeeded

open UnforcedLeray.Short.IIb
open UnforcedLeray.Short.IIb.GreenVorticityUncurlCylKEqBSAux

theorem cylKEqBiotSavartAe_proof :
    UnforcedLeray.Short.IIb.GreenVorticityUncurlNeeded.CylKEqBiotSavartAe := by
  intro m hm c hc w hw_circ u hu
  have hm1 : 1 < m := by linarith
  set wC : B0579.Plane → ℂ := fun x => ((w x : ℝ) : ℂ)
  have hwC_mem : MemLp wC 2 (B0579.cellMeasure c m) := (Lp.memLp w).ofReal
  have hwC_circ : IIIa.HasZeroCirculation c wC := by
    refine ⟨hw_circ.1.ofReal, ?_⟩
    show ∫ x in B0579.cell c, ((w x : ℝ) : ℂ) = 0
    rw [integral_complex_ofReal, hw_circ.2]
    simp
  obtain ⟨a, b, hab, hX⟩ := IIIa.ladTestDensity m hm c wC hc hwC_mem hwC_circ
  have ha_test : ∀ n, B0579.IsCylTest c (a n) := fun n => (hab n).1
  have ha_int : ∀ n, IntegrableOn (a n) (B0579.cell c) := fun n => (hab n).2.2.1
  have ha_zero : ∀ n, ∫ x in B0579.cell c, a n x = 0 := fun n => (hab n).2.2.2.2.1
  -- Convergence of the real part `a_n - w` in `X_{m,c}`
  have hpt_re : ∀ (n : ℕ) (x : B0579.Plane),
      |a n x - w x| ≤ ‖((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ) - wC x‖ := by
    intro n x
    have hre : (((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ) - wC x).re = a n x - w x := by
      simp [wC]
    simpa [hre] using
      Complex.abs_re_le_norm (((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ) - wC x)
  have hxNorm_re_le : ∀ n,
      IIIa.xNorm c m (fun x => ((a n x : ℝ) : ℂ) - wC x) ≤
        IIIa.xNorm c m (fun x => ((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ) - wC x) := by
    intro n
    refine eLpNorm_mono fun x => ?_
    change ‖((a n x : ℝ) : ℂ) - ((w x : ℝ) : ℂ)‖ ≤
      ‖((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ) - wC x‖
    rw [← Complex.ofReal_sub, Complex.norm_real]
    exact hpt_re n x
  have hnorm_lp_le : ∀ n,
      ENNReal.ofReal ‖B0579.testLp c m (ha_test n) - w‖ ≤
        IIIa.xNorm c m (fun x => ((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ) - wC x) := by
    intro n
    have hfin : eLpNorm (B0579.testLp c m (ha_test n) - w : Xmc c m) 2
        (B0579.cellMeasure c m) ≠ ⊤ :=
      (Lp.memLp _).eLpNorm_lt_top.ne
    have hcoe : (B0579.testLp c m (ha_test n) - w : Xmc c m) =ᵐ[B0579.cellMeasure c m]
        fun x => a n x - w x := by
      filter_upwards [Lp.coeFn_sub (B0579.testLp c m (ha_test n)) w,
        MemLp.coeFn_toLp ((ha_test n).memLp m)] with x hx1 hx2
      rw [hx1, Pi.sub_apply]
      change (B0579.testLp c m (ha_test n) : B0579.Plane → ℝ) x - w x = a n x - w x
      rw [B0579.testLp, hx2]
    rw [Lp.norm_def, ENNReal.ofReal_toReal hfin, eLpNorm_congr_ae hcoe]
    exact (eLpNorm_mono fun x => by simpa [Real.norm_eq_abs] using hpt_re n x)
  have hlim_lp : Tendsto (fun n => ENNReal.ofReal ‖B0579.testLp c m (ha_test n) - w‖)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hX (fun _ => zero_le) hnorm_lp_le
  -- `Cyl.K c (a_n)` is Biot–Savart for `a_n`, hence converges to `u` in `L²(cell c)`
  obtain ⟨C_bs, hC_bs⟩ := IIIa.ladBSBound m hm
  have hlim_u : ∀ j : Fin 2,
      Tendsto (fun n => eLpNorm
        (fun x => ((UnforcedLeray.Cyl.K c (a n) x j : ℝ) : ℂ) - u x j) 2
          (volume.restrict (B0579.cell c))) atTop (𝓝 0) := by
    intro j
    have hbd : ∀ n, eLpNorm
        (fun x => ((UnforcedLeray.Cyl.K c (a n) x j : ℝ) : ℂ) - u x j) 2
          (volume.restrict (B0579.cell c)) ≤
        ENNReal.ofReal C_bs *
          IIIa.xNorm c m (fun x => ((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ) - wC x) := by
      intro n
      have hBS_n := isBiotSavart_cylK_of_test hc (ha_test n) (ha_zero n)
      have haC_mem : MemLp (fun x => ((a n x : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) :=
        ((ha_test n).memLp m).ofReal
      have hBS_sub := IIIa.ladBSSub m c _ _ _ _ hm1 haC_mem hwC_mem hBS_n hu
      have hz_sub : IIIa.HasZeroCirculation c ((fun x => ((a n x : ℝ) : ℂ)) - wC) := by
        have ia : IntegrableOn (fun x => ((a n x : ℝ) : ℂ)) (B0579.cell c) := (ha_int n).ofReal
        refine ⟨ia.sub hwC_circ.1, ?_⟩
        have hsub := integral_sub ia hwC_circ.1
        simp only [Pi.sub_apply] at hsub ⊢
        rw [hsub, integral_complex_ofReal, ha_zero n, hwC_circ.2]
        simp
      refine (hC_bs c hc _ (haC_mem.sub hwC_mem) hz_sub _ hBS_sub j).trans ?_
      gcongr
      exact hxNorm_re_le n
    have hlim_rhs : Tendsto (fun n => ENNReal.ofReal C_bs *
        IIIa.xNorm c m (fun x => ((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ) - wC x))
        atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C_bs) hX
        (Or.inr ENNReal.ofReal_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim_rhs
      (fun _ => zero_le) hbd
  -- Uniqueness of `L²` limits on every strip `cellStrip c k`
  have hstrip_eq : ∀ (k : ℕ) (j : Fin 2),
      ∀ᵐ x ∂(volume.restrict (cellStrip c k)),
        ((UnforcedLeray.Cyl.K c w x j : ℝ) : ℂ) = u x j := by
    intro k j
    set μS : Measure B0579.Plane := volume.restrict (cellStrip c k)
    set M_k : ℝ≥0∞ :=
      ENNReal.ofReal nearKernelConst +
        (2 * B0592.weightConst m) * volume (cellStrip c k) ^ (2 : ℝ≥0∞).toReal⁻¹
    have hMk_ne_top : M_k ≠ ⊤ := by
      refine ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ?_⟩
      refine ENNReal.mul_ne_top ?_ ?_
      · exact ENNReal.mul_ne_top (by norm_num) (B0592.weightConst_lt_top hm1).ne
      · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (volume_cellStrip_lt_top c k).ne
    have hKw_meas : AEStronglyMeasurable
        (fun x => ((UnforcedLeray.Cyl.K c w x j : ℝ) : ℂ)) μS :=
      (Complex.continuous_ofReal.comp_stronglyMeasurable
        ((EuclideanSpace.proj j : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).continuous.comp_stronglyMeasurable
          (stronglyMeasurable_cylK c (Lp.stronglyMeasurable w)))).aestronglyMeasurable
    have hu_meas : AEStronglyMeasurable (fun x => u x j) μS :=
      (hu.1 j).aestronglyMeasurable.mono_measure
        (Measure.restrict_mono (cellStrip_subset_cell c k) le_rfl)
    have hd_le : ∀ n : ℕ,
        eLpNorm (fun x => ((UnforcedLeray.Cyl.K c w x j : ℝ) : ℂ) - u x j) 2 μS ≤
          eLpNorm (fun x => ((UnforcedLeray.Cyl.K c (a n) x j : ℝ) : ℂ) - u x j) 2
              (volume.restrict (B0579.cell c)) +
            M_k * ENNReal.ofReal ‖B0579.testLp c m (ha_test n) - w‖ := by
      intro n
      have hKa_meas : AEStronglyMeasurable
          (fun x => ((UnforcedLeray.Cyl.K c (a n) x j : ℝ) : ℂ)) μS :=
        (Complex.continuous_ofReal.comp_stronglyMeasurable
          ((EuclideanSpace.proj j : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).continuous.comp_stronglyMeasurable
            (stronglyMeasurable_cylK c (ha_test n).continuous.stronglyMeasurable))).aestronglyMeasurable
      set f1 : B0579.Plane → ℂ :=
        fun x => ((UnforcedLeray.Cyl.K c (a n) x j : ℝ) : ℂ) - u x j
      set f2 : B0579.Plane → ℂ :=
        fun x => ((UnforcedLeray.Cyl.K c w x j : ℝ) : ℂ) -
          ((UnforcedLeray.Cyl.K c (a n) x j : ℝ) : ℂ)
      have hf1_meas : AEStronglyMeasurable f1 μS := hKa_meas.sub hu_meas
      have hf2_meas : AEStronglyMeasurable f2 μS := hKw_meas.sub hKa_meas
      have hsplit_fn :
          (fun x => ((UnforcedLeray.Cyl.K c w x j : ℝ) : ℂ) - u x j) = f1 + f2 := by
        funext x
        simp only [Pi.add_apply, f1, f2]
        ring
      rw [hsplit_fn]
      refine (eLpNorm_add_le hf1_meas hf2_meas (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
        (add_le_add ?_ ?_)
      · exact eLpNorm_mono_measure _ (Measure.restrict_mono (cellStrip_subset_cell c k) le_rfl)
      · have hnorm_f2 : eLpNorm f2 2 μS =
            eLpNorm (fun x => UnforcedLeray.Cyl.K c (a n) x j - UnforcedLeray.Cyl.K c w x j)
              2 μS := by
          refine eLpNorm_congr_norm_ae (Eventually.of_forall fun x => ?_)
          simp only [f2, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          exact abs_sub_comm _ _
        rw [hnorm_f2]
        exact eLpNorm_cylK_sub_cellStrip_le hc hm1 k (ha_test n) w j
    have hlim_sum : Tendsto (fun n =>
        eLpNorm (fun x => ((UnforcedLeray.Cyl.K c (a n) x j : ℝ) : ℂ) - u x j) 2
            (volume.restrict (B0579.cell c)) +
          M_k * ENNReal.ofReal ‖B0579.testLp c m (ha_test n) - w‖) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n => M_k * ENNReal.ofReal ‖B0579.testLp c m (ha_test n) - w‖)
          atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul (a := M_k) hlim_lp (Or.inr hMk_ne_top)
      simpa using (hlim_u j).add h2
    have hd_zero : eLpNorm (fun x => ((UnforcedLeray.Cyl.K c w x j : ℝ) : ℂ) - u x j) 2 μS = 0 :=
      le_antisymm (ge_of_tendsto' hlim_sum hd_le) zero_le
    have hae_sub := (eLpNorm_eq_zero_iff (hKw_meas.sub hu_meas) (by norm_num)).mp hd_zero
    filter_upwards [hae_sub] with x hx
    exact sub_eq_zero.mp hx
  -- Exhaust `B0579.cell c` by the strips `cellStrip c k`
  have hall : ∀ᵐ x ∂volume, ∀ (k : ℕ) (j : Fin 2),
      x ∈ cellStrip c k → ((UnforcedLeray.Cyl.K c w x j : ℝ) : ℂ) = u x j := by
    rw [ae_all_iff]
    intro k
    rw [ae_all_iff]
    intro j
    exact ae_imp_of_ae_restrict (hstrip_eq k j)
  rw [EventuallyEq, ae_restrict_iff' (B0579.measurableSet_cell c)]
  filter_upwards [hall] with x hx hx_cell
  obtain ⟨k, hk⟩ := exists_nat_gt |x.2|
  have hx_strip : x ∈ cellStrip c k := by
    refine ⟨hx_cell.1, ?_⟩
    rw [mem_Icc]
    have h1 := neg_abs_le x.2
    have h2 := le_abs_self x.2
    exact ⟨by linarith, by linarith⟩
  funext j
  exact hx k j hx_strip

end UnforcedLeray.Short.IIb.GreenVorticityUncurlNeeded
