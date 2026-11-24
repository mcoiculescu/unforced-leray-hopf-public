import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitiveLeaf.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.XDiff.Zfield
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Pointwise.Entry
import UnforcedLeray.Short.PartIIIa.Tasks16.Dominated

/-!
# Spatial regularity and far-field decay of `srcX0` for `thinSource` (`CommDerivSplit/SpatialReg`)

Proves that for any `F` satisfying `FarLeafOrg.ThinHyp c ρo F` and `IIIa.thinMoment c F ≠ ⊤`,
`Z = srcX0 ν μ (IIIa.thinSource ε F)` is `C^∞` on `{y | ρo / ε < ϱ y}` at every fixed phase `τ`
and satisfies `‖iteratedFDeriv ℝ j (Z τ) y'‖ ≤ C_j * (ϱ y') ^ (-4 - j)` for `ϱ y' ≥ 2 * (ρo / ε) + 2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.YBPhase

open YBComm FarLeafOrg UnforcedLeray.PhaseSpace

/-- For a thin source with finite `thinMoment`, `sepMajorant m (thinSource ε F) τ n` is
`sepRho`-integrable at every order `n` and every phase `τ`. -/
theorem thin_majorantIntegrable {ε c ρo : ℝ} {m : ℂ}
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hm : -(1 / 4) < m.re)
    (hth : ThinHyp c ρo F) (hN : IIIa.thinMoment c F ≠ ⊤) (τ : ℝ) (n : ℕ) :
    Integrable (sepMajorant m (IIIa.thinSource ε F) τ n) sepRho := by
  have hS := thin_isSep hε hth
  refine ⟨(l5Meas m (2 * ε * c) (ρo / ε) (IIIa.thinSource ε F) hS τ n).aestronglyMeasurable, ?_⟩
  have hmeas : Measurable (fun p => ENNReal.ofReal (sepMajorant m (IIIa.thinSource ε F) τ n p)) :=
    (l5Meas m (2 * ε * c) (ρo / ε) (IIIa.thinSource ε F) hS τ n).ennreal_ofReal
  unfold HasFiniteIntegral
  have hnn : ∀ p : ℝ × Space, p.1 ∈ Ioo (0 : ℝ) 1 →
      0 ≤ sepMajorant m (IIIa.thinSource ε F) τ n p := by
    intro p hp
    have := hp.1
    unfold sepMajorant IIIa.tensorNorm
    positivity
  have ha : (-1 : ℝ) < 2 * m.re + 2 := by linarith
  calc ∫⁻ p, ‖sepMajorant m (IIIa.thinSource ε F) τ n p‖ₑ ∂sepRho
      = ∫⁻ p, ENNReal.ofReal (sepMajorant m (IIIa.thinSource ε F) τ n p) ∂sepRho := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_mem_Ioo_sepRho] with p hp
        exact Real.enorm_of_nonneg (hnn p hp)
    _ = ∫⁻ l in Ioo (0 : ℝ) 1,
          ∫⁻ z : Space, ENNReal.ofReal (sepMajorant m (IIIa.thinSource ε F) τ n (l, z)) := by
        unfold sepRho
        exact lintegral_prod _ hmeas.aemeasurable
    _ ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * m.re + 2)) *
          ∫⁻ z : Space, IIIa.srcNorm (IIIa.thinSource ε F) (τ + 2 * Real.log l) z := by
        refine setLIntegral_mono' measurableSet_Ioo fun l hl => ?_
        have hl0 : 0 < l := hl.1
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_mono fun z => ?_
        unfold sepMajorant IIIa.srcNorm
        simp only
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : (1 + l * ‖z‖) ^ (-(4 + (n : ℝ))) ≤ 1 := by
          have hbase : 1 ≤ 1 + l * ‖z‖ := by
            have : 0 ≤ l * ‖z‖ := mul_nonneg hl0.le (norm_nonneg z)
            linarith
          have hexp : -(4 + (n : ℝ)) ≤ 0 := by
            linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
          exact Real.rpow_le_one_of_one_le_of_nonpos hbase hexp
        have htn : 0 ≤ IIIa.tensorNorm (IIIa.thinSource ε F (τ + 2 * Real.log l) z) := by
          unfold IIIa.tensorNorm; positivity
        have hlp : 0 ≤ l ^ (2 * m.re + 2) := by positivity
        calc l ^ (2 * m.re + 2) * (1 + l * ‖z‖) ^ (-(4 + (n : ℝ))) *
              IIIa.tensorNorm (IIIa.thinSource ε F (τ + 2 * Real.log l) z)
            ≤ l ^ (2 * m.re + 2) * 1 *
                IIIa.tensorNorm (IIIa.thinSource ε F (τ + 2 * Real.log l) z) := by gcongr
          _ = l ^ (2 * m.re + 2) *
                IIIa.tensorNorm (IIIa.thinSource ε F (τ + 2 * Real.log l) z) := by ring
    _ ≤ ENNReal.ofReal (ε / (1 - Real.exp (-(ε * (2 * m.re + 2 + 1) * c)))) *
          ENNReal.ofReal (ε⁻¹) ^ 2 * (ENNReal.ofReal c * IIIa.thinMoment c F) :=
        thin_total hε hc hth (2 * m.re + 2) ha τ
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ?_
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hN))
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)

/-- `sepW` of a thin source with finite `thinMoment` is `C^∞` on `{y | ρo / ε < ϱ y}` at every `τ`. -/
theorem thin_sepW_contDiffOn_top {ν ε c ρo : ℝ} {m : ℂ}
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hρo : 0 ≤ ρo) (hm : -(1 / 4) < m.re)
    (hth : ThinHyp c ρo F) (hN : IIIa.thinMoment c F ≠ ⊤) (τ : ℝ) (i : Fin 3) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => IIIa.sepW ν m (IIIa.thinSource ε F) y τ i)
      {y : Space | ρo / ε < ϱ y} := by
  have hS := thin_isSep hε hth
  have hr : 0 ≤ ρo / ε := div_nonneg hρo hε.le
  refine contDiffOn_of_locally_contDiffOn fun y₀ hy₀ => ?_
  obtain ⟨δ, hδ, hb⟩ :=
    sd_gapPointwise ν m (ρo / ε) (2 * ε * c) (IIIa.thinSource ε F) hν hr hS τ i y₀ hy₀
  choose C hC0 hCb using hb
  refine ⟨Metric.ball y₀ δ, Metric.isOpen_ball, Metric.mem_ball_self hδ, ?_⟩
  have hint : ∀ n : ℕ, Integrable (fun p => C n * sepMajorant m (IIIa.thinSource ε F) τ n p) sepRho :=
    fun n => (thin_majorantIntegrable hε hc hm hth hN τ n).const_mul (C n)
  have hbound : ∀ n : ℕ, ∀ᵐ p ∂sepRho, ∀ y ∈ Metric.ball y₀ δ,
      ‖iteratedFDeriv ℝ n (sepPhi ν m (IIIa.thinSource ε F) τ i p) y‖ ≤
        C n * sepMajorant m (IIIa.thinSource ε F) τ n p := by
    intro n
    filter_upwards [ae_mem_Ioo_sepRho] with p hp y hy
    exact hCb n y hy p.1 hp p.2
  have key : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => ∫ p, sepPhi ν m (IIIa.thinSource ε F) τ i p y ∂sepRho) (Metric.ball y₀ δ) := by
    refine contDiffOn_infty.2 fun n => ?_
    refine paramContDiffOn_nat n sepRho (sepPhi ν m (IIIa.thinSource ε F) τ i) (Metric.ball y₀ δ)
      (fun n p => C n * sepMajorant m (IIIa.thinSource ε F) τ n p) Metric.isOpen_ball ?_ hint hbound ?_
    · filter_upwards [ae_mem_Ioo_sepRho] with p hp
      exact (sd_sepPhi_contDiff ν m (IIIa.thinSource ε F) τ i p.1 p.2 hν hp).contDiffOn
    · intro k y _
      exact sd_sepPhiMeasurable ν m (2 * ε * c) (ρo / ε) (IIIa.thinSource ε F) hν hS τ i k y
  refine (key.mono inter_subset_right).congr fun y hy => ?_
  apply sepW_eq_integral
  have hm0 : AEStronglyMeasurable (fun p => sepPhi ν m (IIIa.thinSource ε F) τ i p y) sepRho := by
    have := (continuousMultilinearCurryFin0 ℝ Space ℂ).continuous.comp_aestronglyMeasurable
      (sd_sepPhiMeasurable ν m (2 * ε * c) (ρo / ε) (IIIa.thinSource ε F) hν hS τ i 0 y)
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp [iteratedFDeriv_zero_eq_comp]
  refine Integrable.mono' (hint 0) hm0 ?_
  filter_upwards [hbound 0] with p hp
  have := hp y hy.2
  simpa [norm_iteratedFDeriv_zero] using this

/-- `srcX0` of a thin source with finite `thinMoment` is `C^∞` on `{y | ρo / ε < ϱ y}` at every `τ`. -/
theorem thin_X0_contDiffOn_top {ν μ ε c ρo : ℝ}
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hε : 0 < ε) (hc : 0 < c) (hρo : 0 ≤ ρo)
    (hth : ThinHyp c ρo F) (hN : IIIa.thinMoment c F ≠ ⊤) (τ : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (srcX0 ν μ (IIIa.thinSource ε F) τ) {y : Space | ρo / ε < ϱ y} := by
  have hm1 : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have hm2 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have hWa : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => IIIa.sepW ν (μ : ℂ) (IIIa.thinSource ε F) z τ) {y : Space | ρo / ε < ϱ y} :=
    contDiffOn_pi.2 fun i => thin_sepW_contDiffOn_top hν hε hc hρo hm1 hth hN τ i
  have hWb : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => IIIa.sepW ν ((μ : ℂ) + 1) (IIIa.thinSource ε F) z τ) {y : Space | ρo / ε < ϱ y} :=
    contDiffOn_pi.2 fun i => thin_sepW_contDiffOn_top hν hε hc hρo hm2 hth hN τ i
  change ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun z => reL (IIIa.sepW ν (μ : ℂ) (IIIa.thinSource ε F) z τ -
      IIIa.sepW ν ((μ : ℂ) + 1) (IIIa.thinSource ε F) z τ)) {y : Space | ρo / ε < ϱ y}
  exact reL.contDiff.comp_contDiffOn (hWa.sub hWb)

/-- Order-`j` bound on `sepKd j D`. -/
theorem sepKd_le_of_pos (j : ℕ) {D : ℝ} (hD : 0 < D) (x : Space) :
    IIIa.sepKd j D x ≤ ENNReal.ofReal (D ^ (-4 - (j : ℝ))) := by
  unfold IIIa.sepKd
  split_ifs with h
  · refine ENNReal.ofReal_le_ofReal ?_
    exact Real.rpow_le_rpow_of_nonpos hD h (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  · exact zero_le

/-- Pointwise bound on `sepDom (2 * m.re + 2) j D` for `thinSource ε F`. -/
theorem sepDom_thin_le {ε c ρo D : ℝ} {m : ℂ}
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hε : 0 < ε) (hc : 0 < c) (hD : 0 < D) (hm : -(1 / 4) < m.re)
    (hth : ThinHyp c ρo F) (j : ℕ) (τ : ℝ) (y : Space) :
    IIIa.sepDom (2 * m.re + 2) j D (IIIa.srcNorm (IIIa.thinSource ε F)) τ y ≤
      ENNReal.ofReal (D ^ (-4 - (j : ℝ))) *
        (ENNReal.ofReal (ε / (1 - Real.exp (-(ε * (2 * m.re + 2 + 1) * c)))) *
          ENNReal.ofReal (ε⁻¹) ^ 2 * (ENNReal.ofReal c * IIIa.thinMoment c F)) := by
  have ha : (-1 : ℝ) < 2 * m.re + 2 := by linarith
  calc IIIa.sepDom (2 * m.re + 2) j D (IIIa.srcNorm (IIIa.thinSource ε F)) τ y
      ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * m.re + 2)) *
          (ENNReal.ofReal (D ^ (-4 - (j : ℝ))) *
            ∫⁻ z : Space, IIIa.srcNorm (IIIa.thinSource ε F) (τ + 2 * Real.log l) z) := by
        unfold IIIa.sepDom
        refine lintegral_mono fun l => mul_le_mul_right ?_ _
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_mono fun z => mul_le_mul_left (sepKd_le_of_pos j hD _) _
    _ = ENNReal.ofReal (D ^ (-4 - (j : ℝ))) *
          ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (2 * m.re + 2)) *
            ∫⁻ z : Space, IIIa.srcNorm (IIIa.thinSource ε F) (τ + 2 * Real.log l) z := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun l => ?_
        ring
    _ ≤ ENNReal.ofReal (D ^ (-4 - (j : ℝ))) *
          (ENNReal.ofReal (ε / (1 - Real.exp (-(ε * (2 * m.re + 2 + 1) * c)))) *
            ENNReal.ofReal (ε⁻¹) ^ 2 * (ENNReal.ofReal c * IIIa.thinMoment c F)) := by
        gcongr
        exact thin_total hε hc hth (2 * m.re + 2) ha τ

/-- Far-field spatial derivative decay of `sepW` for `thinSource ε F`. -/
theorem thin_sepW_far_decay {ν ε c ρo : ℝ} {m : ℂ}
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hρo : 0 ≤ ρo) (hm : -(1 / 4) < m.re)
    (hth : ThinHyp c ρo F) (hN : IIIa.thinMoment c F ≠ ⊤) (τ : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y' : Space, 2 * (ρo / ε) + 2 ≤ ϱ y' →
      ‖iteratedFDeriv ℝ j (fun z => IIIa.sepW ν m (IIIa.thinSource ε F) z τ) y'‖ ≤
        C * (ϱ y') ^ (-4 - (j : ℝ)) := by
  obtain ⟨C0, hC0, hdom⟩ := IIIa.sepWDominated IIIa.sepKernelBounds j
  set M_enn : ℝ≥0∞ :=
    ENNReal.ofReal (ε / (1 - Real.exp (-(ε * (2 * m.re + 2 + 1) * c)))) *
      ENNReal.ofReal (ε⁻¹) ^ 2 * (ENNReal.ofReal c * IIIa.thinMoment c F)
  have hM_lt : M_enn < ⊤ := by
    refine ENNReal.mul_lt_top ?_
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hN))
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
  set M : ℝ := M_enn.toReal
  have hM_nn : 0 ≤ M := ENNReal.toReal_nonneg
  have hM_eq : ENNReal.ofReal M = M_enn := ENNReal.ofReal_toReal hM_lt.ne
  refine ⟨C0 * M * (2 : ℝ) ^ (4 + (j : ℝ)), by positivity, fun y' hy' => ?_⟩
  have hrOut : 0 ≤ ρo / ε := div_nonneg hρo hε.le
  have hy'_pos : 0 < ϱ y' := by linarith
  have hrr : ρo / ε < ϱ y' := by linarith
  have hP : 0 < 2 * ε * c := by positivity
  have hS := thin_isSep hε hth
  set D : ℝ := ϱ y' - ρo / ε
  have hD_half : ϱ y' / 2 ≤ D := by
    show ϱ y' / 2 ≤ ϱ y' - ρo / ε
    linarith
  have hD_pos : 0 < D := by linarith
  have hfin0 : IIIa.sepDom (2 * m.re + 2) 0 D (IIIa.srcNorm (IIIa.thinSource ε F)) τ y' < ⊤ :=
    (sepDom_thin_le hε hc hD_pos hm hth 0 τ y').trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hM_lt)
  have hw := hdom ν hν m hm (ρo / ε) (ϱ y') (2 * ε * c) hrOut hrr hP
    (IIIa.thinSource ε F) hS τ y' le_rfl hfin0
  have hw' : ‖iteratedFDeriv ℝ j (fun z => IIIa.sepW ν m (IIIa.thinSource ε F) z τ) y'‖ₑ ≤
      ENNReal.ofReal (C0 * M * D ^ (-4 - (j : ℝ))) := by
    calc ‖iteratedFDeriv ℝ j (fun z => IIIa.sepW ν m (IIIa.thinSource ε F) z τ) y'‖ₑ
        = IIIa.wDerivNorm ν m (IIIa.thinSource ε F) j τ y' := rfl
      _ ≤ ENNReal.ofReal C0 *
            IIIa.sepDom (2 * m.re + 2) j D (IIIa.srcNorm (IIIa.thinSource ε F)) τ y' := hw
      _ ≤ ENNReal.ofReal C0 * (ENNReal.ofReal (D ^ (-4 - (j : ℝ))) * M_enn) := by
          gcongr
          exact sepDom_thin_le hε hc hD_pos hm hth j τ y'
      _ = ENNReal.ofReal (C0 * M * D ^ (-4 - (j : ℝ))) := by
          rw [← hM_eq, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC0]
          congr 1; ring
  rw [← ofReal_norm] at hw'
  have hreal : ‖iteratedFDeriv ℝ j (fun z => IIIa.sepW ν m (IIIa.thinSource ε F) z τ) y'‖ ≤
      C0 * M * D ^ (-4 - (j : ℝ)) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hw'
  refine hreal.trans ?_
  have hpow : D ^ (-4 - (j : ℝ)) ≤ (2 : ℝ) ^ (4 + (j : ℝ)) * (ϱ y') ^ (-4 - (j : ℝ)) := by
    have h1 : D ^ (-4 - (j : ℝ)) ≤ (ϱ y' / 2) ^ (-4 - (j : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hD_half
        (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
    rw [Real.div_rpow hy'_pos.le (by norm_num)] at h1
    have h2 : (2 : ℝ) ^ (-4 - (j : ℝ)) = ((2 : ℝ) ^ (4 + (j : ℝ)))⁻¹ := by
      rw [show -4 - (j : ℝ) = -(4 + (j : ℝ)) by ring, Real.rpow_neg (by norm_num)]
    rw [h2, div_inv_eq_mul, mul_comm] at h1
    exact h1
  calc C0 * M * D ^ (-4 - (j : ℝ))
      ≤ C0 * M * ((2 : ℝ) ^ (4 + (j : ℝ)) * (ϱ y') ^ (-4 - (j : ℝ))) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = C0 * M * (2 : ℝ) ^ (4 + (j : ℝ)) * (ϱ y') ^ (-4 - (j : ℝ)) := by ring

/-- Far-field spatial derivative decay of `srcX0` for `thinSource ε F`. -/
theorem thin_X0_far_decay {ν μ ε c ρo : ℝ}
    {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hν : 0 < ν) (hμ : -(1 / 4) < μ) (hε : 0 < ε) (hc : 0 < c) (hρo : 0 ≤ ρo)
    (hth : ThinHyp c ρo F) (hN : IIIa.thinMoment c F ≠ ⊤) (τ : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y' : Space, 2 * (ρo / ε) + 2 ≤ ϱ y' →
      ‖iteratedFDeriv ℝ j (srcX0 ν μ (IIIa.thinSource ε F) τ) y'‖ ≤
        C * (ϱ y') ^ (-4 - (j : ℝ)) := by
  have hm1 : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have hm2 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  obtain ⟨C0, hC0, hb0⟩ := thin_sepW_far_decay hν hε hc hρo hm1 hth hN τ j
  obtain ⟨C1, hC1, hb1⟩ := thin_sepW_far_decay hν hε hc hρo hm2 hth hN τ j
  refine ⟨‖reL‖ * (C0 + C1), by positivity, fun y' hy' => ?_⟩
  have hrOut : 0 ≤ ρo / ε := div_nonneg hρo hε.le
  have hy'_mem : ρo / ε < ϱ y' := by linarith
  have hopen : IsOpen {y : Space | ρo / ε < ϱ y} := isOpen_lt continuous_const continuous_ϱ
  have hWa : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => IIIa.sepW ν (μ : ℂ) (IIIa.thinSource ε F) z τ) y' :=
    (contDiffOn_pi.2 fun i =>
      thin_sepW_contDiffOn_top hν hε hc hρo hm1 hth hN τ i).contDiffAt (hopen.mem_nhds hy'_mem)
  have hWb : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => IIIa.sepW ν ((μ : ℂ) + 1) (IIIa.thinSource ε F) z τ) y' :=
    (contDiffOn_pi.2 fun i =>
      thin_sepW_contDiffOn_top hν hε hc hρo hm2 hth hN τ i).contDiffAt (hopen.mem_nhds hy'_mem)
  have hj : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hfun : srcX0 ν μ (IIIa.thinSource ε F) τ =
      reL ∘ ((fun z => IIIa.sepW ν (μ : ℂ) (IIIa.thinSource ε F) z τ) -
        (fun z => IIIa.sepW ν ((μ : ℂ) + 1) (IIIa.thinSource ε F) z τ)) := rfl
  rw [hfun]
  refine (reL.norm_iteratedFDeriv_comp_left (hWa.sub hWb) hj).trans ?_
  have hsub_eq : iteratedFDeriv ℝ j
      (fun x => IIIa.sepW ν (μ : ℂ) (IIIa.thinSource ε F) x τ -
        IIIa.sepW ν ((μ : ℂ) + 1) (IIIa.thinSource ε F) x τ) y' =
      iteratedFDeriv ℝ j (fun z => IIIa.sepW ν (μ : ℂ) (IIIa.thinSource ε F) z τ) y' -
        iteratedFDeriv ℝ j (fun z => IIIa.sepW ν ((μ : ℂ) + 1) (IIIa.thinSource ε F) z τ) y' :=
    iteratedFDeriv_sub_apply (hWa.of_le hj) (hWb.of_le hj)
  rw [hsub_eq]
  have hsub := (norm_sub_le _ _).trans (add_le_add (hb0 y' hy') (hb1 y' hy'))
  calc ‖reL‖ * ‖iteratedFDeriv ℝ j (fun z => IIIa.sepW ν (μ : ℂ) (IIIa.thinSource ε F) z τ) y' -
          iteratedFDeriv ℝ j (fun z => IIIa.sepW ν ((μ : ℂ) + 1) (IIIa.thinSource ε F) z τ) y'‖
      ≤ ‖reL‖ * (C0 * (ϱ y') ^ (-4 - (j : ℝ)) + C1 * (ϱ y') ^ (-4 - (j : ℝ))) :=
        mul_le_mul_of_nonneg_left hsub (norm_nonneg _)
    _ = ‖reL‖ * (C0 + C1) * (ϱ y') ^ (-4 - (j : ℝ)) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.YBPhase
