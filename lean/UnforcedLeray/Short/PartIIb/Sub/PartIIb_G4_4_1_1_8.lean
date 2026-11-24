import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_Fields
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletJointSmooth
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.InletSourceGradPtw
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm
import UnforcedLeray.Short.PartIIb.Tasks.QuadraticEstimate.InletLp
import UnforcedLeray.Short.PartIIb.Tasks.StrongLateCoeff.NvFderiv
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.InletComponentJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.SmoothVanish
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.RawProfileSmooth

/-!
# Part II-b, task `PartII-b:G4/4/1/1/8` (`InletSourceFieldBound`)

Source of record: `the November 2 reference manuscript` (SP) lines 2347-2385
(display `short-bg:affine`, second inequality).

Off the axis the source is the ring lift of the unprojected column,
`inletSourceF p i = N_v(𝒞_εe_i)` (`isfb_ident`, from `InletL0Ptw`, `InletBPtw`, SP 2370-2374).
* `‖F‖_{Y_p} = (πR²)^{1/p}‖𝒞_εe_i‖_{H_p}` (`phaseLpNorm_NvC`, the axis is null), and the column
  envelope `ColEnvelope` with `ColWeightNorm` gives `‖𝒞_εe_i‖_{H_p} ≤ Cν^{-k}` (SP 2385; the raw jets
  `RawJetBound` come from Part I `sct:transverse`, `sct:fixed-band` as in `affineColumnComparison`).
* `∂_jF = ∂_j N_v(𝒞_εe_i)` off the axis, `|DN_vb| ≤ 2s·J(b)` (`nvFderivBound`,
  `gradProfileQuantity_le`), so a first-order chart jet bound of the column (`ColumnChartJet`)
  gives the linear ring envelope `ringEnv1`, whose `L^{11/4}` norm is `≤ Cν^{-k}R^{8/11}`
  (`eLpNorm_le_of_ringEnv1`), `8/11 = 2/p`.

Structure (all proved here except the three leaves marked open):
* `inletSourceFieldBound_of_colJet : RawJointSmooth → ColumnChartJet → InletSourceFieldBound`;
* `columnChartJet_of : RawProfJet2 → ColumnJetCalc → ColumnChartJet` (with `InletComponentJets`,
  `inletSplit`, `bgRawProfileSmooth`);
* `columnJetCalc_of : DSJet1 → VecDiffJet1 → BEpsJet1 → ColumnJetCalc`, `dSJet1`;
* open: `RawProfJet2` (jets of order `≤ 2` of `b_raw` on `0 < s ≤ H`, Part I input one order above
  `RawJetBound`), `VecDiffJet1`, `BEpsJet1` (pure chart calculus one order above `VecDiffJet`,
  `BEpsJet`);
* `inletSourceFieldBound_of` takes the three open leaves as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Blueprint UnforcedLeray.B0412 UnforcedLeray.Axi
open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.Short.PartIIIb.Concrete.ES326Inlet

/-- **First-order chart jets of the unprojected column** (SP 2370-2385; the gradient half of the
second inequality of `short-bg:affine`, `‖·‖_{W^{1,Y_p}}`): on `0 < s ≤ H/2` the real column
`𝒞_εe_i = s[(∂_s - νL_ε)e_ε + B_εe_ε]` (`colEpsR`) is differentiable and its first-order chart jet
`‖G‖ + ‖∂_qG‖ + ‖∂_ηG‖ + ‖KG‖` is `≤ Aν^{-k}(1+|η|)^N e^{-κ|η|/c}`.  Inputs: the jets of order
`≤ 3` of the inlet profile with transverse decay (`InletComponentJets`, SP 2355-2369), the jets of
order `≤ 2` of the raw profile `b_raw = v + εHe_z` on `0 < s ≤ H` (one order above `RawJetBound`;
SP 2419-2423, Part I `sct:transverse`, `sct:fixed-band`), and the chart calculus of `L_ε`, `B_ε`
one order above `VecDiffJet`, `BEpsJet`. -/
def ColumnChartJet : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Planar.Profile), 0 < Sig → Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ (A κ : ℝ) (k N : ℕ) (ν₀ : ℝ), 0 < A ∧ 0 < κ ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ (i : Fin 2) (x : Coord), 0 < x.1 → x.1 ≤ p.H / 2 →
        DifferentiableAt ℝ (colEpsR p i) x ∧
        chartJet (colEpsR p i) x ≤
          A * (p.ν ^ k)⁻¹ * (1 + |x.2.2|) ^ N * Real.exp (-(κ * |x.2.2| / p.c))

/-- `RawJetBound` from the Part I chain (as in `affineColumnComparison`, `Column.lean`). -/
theorem isfb_rawJetBound : RawJetBound :=
  let hFD0 : PartI.OverlapFluctuationDecay :=
    PartI.overlap_fluctuation_decay PartI.overlap_highnorm_uniform
  let hOv : PartI.TrainOverlap :=
    PartI.trainOverlap_proof hFD0
      (PartI.overlap_mean_decay PartI.overlap_highnorm_uniform hFD0 PartI.overlap_mean_primitive)
  let hVort : PartI.TrainVorticityGaussianTail := PartI.train_vorticity_gaussian_tail hOv
  let hTails : PartI.TrainStreamVelocityPressureTails :=
    PartI.train_stream_velocity_pressure_tails hOv hVort
  let hFD : PartI.TrainFluctuationDecay := PartI.trainFluctuationDecay_proof hTails hFD0 hOv
  rawJetBound_of (PartI.trainTransverseTails_proof hVort hTails)
    (PartI.trainFixedBand_proof hTails hFD)

/-- The complex ring lift of a real profile is the real lift: `N_v(cplx f) = realC(N_v f)`. -/
theorem isfb_NvC_cplx (R : ℝ) (f : Coord → Axi.Merid) (τ : ℝ) (y : Space) :
    NvC R (cplx f) (τ, y) = realC (Nv R f τ y) := by
  have h1 : (fun z => reM (cplx f z)) = f := by
    funext z
    ext j
    simp [reM, cplx]
  have h2 : (fun z => imM (cplx f z)) = 0 := by
    funext z
    ext j
    simp [imM, cplx]
  have hz : Axi.Nv R (0 : Coord → Axi.Merid) τ y = 0 := by
    simp [Axi.Nv]
  have hrz : B0412.realC (0 : Space) = 0 := by
    ext j
    simp [B0412.realC_apply]
  simp only [NvC]
  rw [h1, h2, hz, hrz, smul_zero, add_zero]

/-- **Off-axis identification** (SP 2370-2374): `inletSourceF p i = N_v(𝒞_εe_i)` off the axis. -/
theorem isfb_ident {p : Params} {i : Fin 2}
    (hRaw : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2))
    (hL0 : ∀ (α : E2) (τ : ℝ) (y : Space), y ∉ Axi.axis →
        B0411.L0 p.ν (inletC p α) (τ, y) =
          NvC p.R (fun m => ∑ i : Fin 2, ((α i : ℝ) : ℂ) • cplx (colDiffR p i) m) (τ, y))
    (hB : ∀ (α : E2) (τ : ℝ) (y : Space), y ∉ Axi.axis →
        advT p.Ufun (inletC p α) (τ, y) + advT (inletC p α) p.Ufun (τ, y) =
          NvC p.R (fun m => ∑ i : Fin 2, ((α i : ℝ) : ℂ) • cplx (colIntR p i) m) (τ, y))
    (τ : ℝ) (y : Space) (hy : y ∉ Axi.axis) :
    inletSourceF p i (τ, y) = NvC p.R (colEps p i) (τ, y) := by
  set α : E2 := EuclideanSpace.single i 1 with hα
  have hE : inletC p α = p.Efun i := by
    funext x
    simp only [inletC, hα]
    exact sum_single_smul i (fun k => p.Efun k x)
  have hD : (fun m => ∑ k : Fin 2, ((α k : ℝ) : ℂ) • cplx (colDiffR p k) m) =
      cplx (colDiffR p i) := by
    funext m
    exact sum_single_smul i (fun k => cplx (colDiffR p k) m)
  have hI : (fun m => ∑ k : Fin 2, ((α k : ℝ) : ℂ) • cplx (colIntR p k) m) =
      cplx (colIntR p i) := by
    funext m
    exact sum_single_smul i (fun k => cplx (colIntR p k) m)
  have h1 := hL0 α τ y hy
  have h2 := hB α τ y hy
  rw [hE, hD] at h1
  rw [hE, hI] at h2
  have hF : inletSourceF p i (τ, y) =
      B0411.L0 p.ν (p.Efun i) (τ, y) +
        (advT p.Ufun (p.Efun i) (τ, y) + advT (p.Efun i) p.Ufun (τ, y)) := by
    simp only [inletSourceF, B0411.L0, B0411.T0, isgp_advT_Efun_Ufun hRaw i]
    abel
  rw [hF, h1, h2, ← NvC_add_apply]
  apply NvC_apply_congr
  have hs : 0 < (Axi.chart p.R τ y).1 := Axi.age_pos p.R_pos.ne' hy
  rw [colEps_of_pos p i hs]

/-- The phase norm of the source is the ring-lift norm of the column (`phaseLpNorm_NvC`; the
axis is null). -/
theorem isfb_F_eq {p : Params} {i : Fin 2}
    (hid : ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis →
      inletSourceF p i (τ, y) = NvC p.R (colEps p i) (τ, y))
    (hper : QPeriodic p.c (colEps p i))
    (hmeas : AEStronglyMeasurable (colEps p i) (hMeas p.c bgp)) :
    phaseLpNorm p.period bgp (inletSourceF p i) =
      ENNReal.ofReal ((Real.pi * p.R ^ 2) ^ (1 / bgp)) * hNorm p.c bgp (colEps p i) := by
  have hbgp : (0 : ℝ) < bgp := by unfold bgp; norm_num
  have h := phaseLpNorm_NvC p.c_pos hbgp p.ε_pos (colEps p i) hper hmeas
  have hin : ∀ t : ℝ, ∫⁻ y : Space, ‖inletSourceF p i (t, y)‖ₑ ^ bgp =
      ∫⁻ y : Space, ‖NvC p.R (colEps p i) (t, y)‖ₑ ^ bgp := fun t =>
    lintegral_congr_ae (by
      filter_upwards [Axi.ae_not_mem_axis] with y hy
      rw [hid t y hy])
  have e1 : phaseLpNorm p.period bgp (inletSourceF p i) =
      phaseLpNorm p.period bgp (NvC p.R (colEps p i)) := by
    simp only [phaseLpNorm, hin]
  rw [e1]
  exact h

/-- **Pointwise ring envelope of the gradient of the source** off the axis. -/
theorem isfb_G_ptw {p : Params} {i : Fin 2} (j : Fin 3) {B κ : ℝ} {N : ℕ}
    (hF : ContDiff ℝ ∞ (inletSourceF p i))
    (hid : ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis →
      inletSourceF p i (τ, y) = realC (Nv p.R (colEpsR p i) τ y))
    (hvan : ∀ x : Coord, p.H / 2 < x.1 → colEpsR p i x = 0)
    (hJ : ∀ x : Coord, 0 < x.1 → x.1 ≤ p.H / 2 →
      DifferentiableAt ℝ (colEpsR p i) x ∧
      chartJet (colEpsR p i) x ≤ B * (1 + |x.2.2|) ^ N * Real.exp (-(κ * |x.2.2| / p.c)))
    (hB : 0 ≤ B) (hε1 : p.R⁻¹ ≤ 1)
    (τ : ℝ) (y : Space) (hy : y ∉ Axi.axis) :
    ‖inletSourceG p i j (τ, y)‖ ≤ ringEnv1 p.H (2 * B) κ p.c N (age p.R y) (trans p.R y) := by
  have hRpos : 0 < p.R := p.R_pos
  have hs0 : 0 < age p.R y := Axi.age_pos hRpos.ne' hy
  have hd : Differentiable ℝ (inletSourceF p i) := hF.differentiable (by simp)
  have hG : inletSourceG p i j (τ, y) =
      fderiv ℝ (fun z : Space => inletSourceF p i (τ, z)) y
        (UnforcedLeray.coordinateVector j) :=
    (UnforcedLeray.Short.PartIIIb.Concrete.slice_fderiv hd τ y
      (UnforcedLeray.coordinateVector j)).symm
  have hev : (fun z : Space => inletSourceF p i (τ, z)) =ᶠ[𝓝 y]
      fun z => realCL (Nv p.R (colEpsR p i) τ z) := by
    filter_upwards [Axi.isOpen_compl_axis.mem_nhds hy] with z hz
    rw [hid τ z hz, realCL_apply]
  rw [hG, hev.fderiv_eq]
  have hM : 0 ≤ 2 * B := by linarith
  by_cases hle : age p.R y ≤ p.H / 2
  · rw [ringEnv1_of_mem hs0 hle]
    obtain ⟨hdiff, hjet⟩ := hJ (chart p.R τ y) hs0 hle
    have hb := nvFderivBound p.R τ (colEpsR p i) y hRpos hy hdiff
    have hcomp : fderiv ℝ (fun z => realCL (Nv p.R (colEpsR p i) τ z)) y =
        realCL.comp (fderiv ℝ (Nv p.R (colEpsR p i) τ) y) :=
      (realCL.hasFDerivAt.comp y hb.1.hasFDerivAt).fderiv
    rw [hcomp, ContinuousLinearMap.comp_apply, realCL_apply, norm_realC]
    have hq := gradProfileQuantity_le (inv_nonneg.2 hRpos.le) hε1 (colEpsR p i)
      (chart p.R τ y) hs0.le
    have hx1 : (chart p.R τ y).1 = age p.R y := rfl
    have hx2 : (chart p.R τ y).2.2 = trans p.R y := rfl
    rw [hx2] at hjet
    rw [hx1] at hq
    calc ‖fderiv ℝ (Nv p.R (colEpsR p i) τ) y (UnforcedLeray.coordinateVector j)‖
        ≤ ‖fderiv ℝ (Nv p.R (colEpsR p i) τ) y‖ *
            ‖(UnforcedLeray.coordinateVector j : Space)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (Nv p.R (colEpsR p i) τ) y‖ := by rw [norm_cv, mul_one]
      _ ≤ gradProfileQuantity p.R⁻¹ (colEpsR p i) (chart p.R τ y) := hb.2
      _ ≤ 2 * age p.R y * chartJet (colEpsR p i) (chart p.R τ y) := hq
      _ ≤ 2 * age p.R y *
            (B * (1 + |trans p.R y|) ^ N * Real.exp (-(κ * |trans p.R y| / p.c))) :=
          mul_le_mul_of_nonneg_left hjet (by positivity)
      _ = 2 * B * age p.R y *
            ((1 + |trans p.R y|) ^ N * Real.exp (-(κ * |trans p.R y| / p.c))) := by ring
  · set T := (p.H / 2 + age p.R y) / 2 with hTdef
    have hHT : p.H / 2 < T := by rw [hTdef]; linarith [not_le.1 hle]
    have hTa : T < age p.R y := by rw [hTdef]; linarith [not_le.1 hle]
    have hvanT : ∀ m : ℝ × (ℝ × ℝ), T ≤ m.1 → colEpsR p i m = 0 :=
      fun m hm' => hvan m (hHT.trans_le hm')
    have h0 := nv_eventually_zero hRpos hvanT (Or.inr hTa)
    have hz : (fun z => realCL (Nv p.R (colEpsR p i) τ z)) =ᶠ[𝓝 y] fun _ => (0 : CVec3) := by
      filter_upwards [h0] with z hz
      rw [hz τ, map_zero]
    have h0' : fderiv ℝ (fun z => realCL (Nv p.R (colEpsR p i) τ z)) y = 0 := by
      rw [hz.fderiv_eq]
      exact fderiv_const_apply _
    rw [h0', ContinuousLinearMap.zero_apply, norm_zero]
    exact ringEnv1_nonneg hM _ _

/-- `(πR²)^{1/p} = π^{1/p}R^{2/p}`. -/
theorem isfb_piR (R : ℝ) (hR : 0 < R) :
    (Real.pi * R ^ 2) ^ (1 / bgp) = Real.pi ^ (1 / bgp) * R ^ (2 / bgp) := by
  rw [Real.mul_rpow Real.pi_pos.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hR.le]
  congr 2
  push_cast
  ring

/-- **The bound, conditional on the first-order chart jets of the column.** -/
theorem inletSourceFieldBound_of_colJet (hRaw : RawJointSmooth) (hJ : ColumnChartJet) :
    InletSourceFieldBound := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨A, κ, k, N, ν₁, hA, hκ, hν₁, hν₁1, HE⟩ :=
    colEnvelope_of_parts (rawProfJet_of isfb_rawJetBound) inletJetDecay jetLe vecDiffJet
      bEpsJet colVanish Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₂, hν₂, HP⟩ := colQPeriodic Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₃, hν₃, HM⟩ := colAEMeas Sig lam q hSig hq dm dp hdm
  obtain ⟨K, hK, HW⟩ := colWeightNorm N κ hκ
  obtain ⟨ν₄, hν₄, HL⟩ := inletL0Ptw_of inletT0Ptw inletLapPtw Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₅, hν₅, HB⟩ := inletBPtw Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₆, hν₆, HI⟩ := inletJointSmooth Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₇, hν₇, HR⟩ := hRaw Sig lam q hSig hq dm dp hdm
  obtain ⟨A', κ', k', N', ν₈, hA', hκ', hν₈, HJ⟩ := hJ Sig lam q hSig hq dm dp hdm
  obtain ⟨K', hK', HK'⟩ := eLpNorm_le_of_ringEnv1 N' hκ'
  have hSig0 : 0 < 1 + Sig := by linarith
  set C : ℝ := (Real.pi ^ (1 / bgp) * K * A + 6 * K' * A') * (1 + Sig) with hCdef
  set kk : ℕ := k + k' + 2 * N + 2 * N' + 5 with hkk
  have hpi0 : 0 < Real.pi ^ (1 / bgp) := Real.rpow_pos_of_pos Real.pi_pos _
  refine ⟨C, kk, min (min (min ν₁ ν₂) (min ν₃ ν₄)) (min (min ν₅ ν₆) (min ν₇ ν₈)),
    by positivity, by
      refine lt_min (lt_min (lt_min hν₁ hν₂) (lt_min hν₃ hν₄))
        (lt_min (lt_min hν₅ hν₆) (lt_min hν₇ hν₈)), ?_⟩
  intro p d hreg hν hS hm i
  have e1 : p.ν ≤ ν₁ := hν.trans ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have e2 : p.ν ≤ ν₂ := hν.trans ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have e3 : p.ν ≤ ν₃ := hν.trans ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have e4 : p.ν ≤ ν₄ := hν.trans ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  have e5 : p.ν ≤ ν₅ := hν.trans ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have e6 : p.ν ≤ ν₆ := hν.trans ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have e7 : p.ν ≤ ν₇ := hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have e8 : p.ν ≤ ν₈ := hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  have hνpos : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ 1 := e1.trans hν₁1
  set u : ℝ := p.ν⁻¹ with hu
  have hu1 : 1 ≤ u := (one_le_inv₀ hνpos).2 hν1
  have hu0 : 0 < u := by linarith
  have hpow : ∀ m : ℕ, (p.ν ^ m)⁻¹ = u ^ m := fun m => by rw [hu, inv_pow]
  have hc : p.c = u ^ 2 := by rw [hreg.c_eq, hpow]
  have hc1 : 1 ≤ p.c := by rw [hc]; exact one_le_pow₀ hu1
  have hHpos : 0 < p.H := p.H_pos
  have hH : 1 + p.H ≤ (1 + Sig) * u := by
    have e : p.H = Sig * u := by rw [Params.H, hS, hu, div_eq_mul_inv]
    rw [e]
    nlinarith
  have hRpos : 0 < p.R := p.R_pos
  have hε1 : p.R⁻¹ ≤ 1 := by
    have hRe : p.R⁻¹ = p.ε := by simp [Params.R]
    rw [hRe, hreg.eps_eq, Real.exp_le_one_iff]
    have := hreg.dm_le
    have := hreg.dm_pos
    have : 0 ≤ d / p.ν := div_nonneg (by linarith) hνpos.le
    rw [neg_div]
    linarith
  have hupow : ∀ m : ℕ, m ≤ kk → u ^ m ≤ u ^ kk := fun m hm => pow_le_pow_right₀ hu1 hm
  -- the source as a ring lift
  have hid : ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis →
      inletSourceF p i (τ, y) = NvC p.R (colEps p i) (τ, y) :=
    isfb_ident (HR p d hreg e7 hS hm i) (HL p d hreg e4 hS hm) (HB p d hreg e5 hS hm)
  have hid' : ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis →
      inletSourceF p i (τ, y) = realC (Nv p.R (colEpsR p i) τ y) := fun τ y hy => by
    rw [hid τ y hy]
    exact isfb_NvC_cplx p.R (colEpsR p i) τ y
  -- F: the column norm
  obtain ⟨hvan, hbd⟩ := HE p d ⟨hreg, e1, hS, hm⟩ i
  have hMnn : 0 ≤ A * (p.ν ^ k)⁻¹ := by positivity
  have hcol : hNorm p.c bgp (colEps p i) ≤
      ENNReal.ofReal (K * (A * (p.ν ^ k)⁻¹) * (1 + p.H) * p.c ^ (N + 1)) :=
    HW p.c p.H (A * (p.ν ^ k)⁻¹) (colEps p i) hc1 hHpos hMnn
      (fun x hx => by
        have := hvan x hx
        ext j
        simp [colEps, cplx, this])
      (fun x hx0 hx1 => by
        have e : ‖colEps p i x‖ = ‖colEpsR p i x‖ := liftM_norm _
        rw [e]
        exact hbd x hx0 hx1)
  have hFeq := isfb_F_eq hid (HP p d ⟨hreg, e2, hS, hm⟩ i) (HM p d ⟨hreg, e3, hS, hm⟩ i)
  set a : ℝ := (Real.pi * p.R ^ 2) ^ (1 / bgp) with ha
  set b : ℝ := K * (A * (p.ν ^ k)⁻¹) * (1 + p.H) * p.c ^ (N + 1) with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hFle : phaseLpNorm p.period bgp (inletSourceF p i) ≤ ENNReal.ofReal (a * b) := by
    rw [hFeq, ENNReal.ofReal_mul ha0]
    gcongr
  -- G: the gradient
  have hF : ContDiff ℝ ∞ (inletSourceF p i) :=
    contDiff_inletSourceF (HI p d hreg e6 hS hm i) (HR p d hreg e7 hS hm i)
  set B' : ℝ := A' * (p.ν ^ k')⁻¹ with hB'
  have hB'0 : 0 ≤ B' := by positivity
  set g : ℝ := K' * (2 * B') * (1 + p.H) * p.c ^ (N' + 1) * p.R ^ (8 / 11 : ℝ) with hg
  have hg0 : 0 ≤ g := by positivity
  have hGle : ∀ j : Fin 3, phaseLpNorm p.period bgp (inletSourceG p i j) ≤ ENNReal.ofReal g := by
    intro j
    refine phaseLpNorm_bgp_le_of_slice p.period_pos hg0 fun τ => ?_
    exact HK' p.R p.c p.H (2 * B') (fun y => inletSourceG p i j (τ, y)) hRpos hc1 hHpos
      (by linarith) (fun y hy => isfb_G_ptw j hF hid' hvan
        (fun x hx0 hx1 => HJ p d hreg e8 hS hm i x hx0 hx1) hB'0 hε1 τ y hy)
  refine ⟨lt_of_le_of_lt hFle ENNReal.ofReal_lt_top,
    fun j => lt_of_le_of_lt (hGle j) ENNReal.ofReal_lt_top, ?_⟩
  have hFr : (phaseLpNorm p.period bgp (inletSourceF p i)).toReal ≤ a * b :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hFle
  have hGr : ∀ j : Fin 3, (phaseLpNorm p.period bgp (inletSourceG p i j)).toReal ≤ g :=
    fun j => ENNReal.toReal_le_of_le_ofReal hg0 (hGle j)
  have hsum : ∑ j : Fin 3, (phaseLpNorm p.period bgp (inletSourceG p i j)).toReal ≤ 3 * g := by
    calc ∑ j : Fin 3, (phaseLpNorm p.period bgp (inletSourceG p i j)).toReal
        ≤ ∑ _j : Fin 3, g := Finset.sum_le_sum fun j _ => hGr j
      _ = 3 * g := by simp
  have h811 : (8 / 11 : ℝ) = 2 / bgp := by unfold bgp; norm_num
  set Rp : ℝ := p.R ^ (2 / bgp) with hRp
  have hRp0 : 0 ≤ Rp := by positivity
  have haR : a = Real.pi ^ (1 / bgp) * Rp := by rw [ha, hRp]; exact isfb_piR p.R hRpos
  have hgR : g = K' * (2 * B') * (1 + p.H) * p.c ^ (N' + 1) * Rp := by rw [hg, hRp, h811]
  -- polynomial bookkeeping
  have hab : a * b ≤ Real.pi ^ (1 / bgp) * K * A * (1 + Sig) * u ^ kk * Rp := by
    rw [haR, hb, hpow, hc]
    have h1 : (1 + p.H) * (u ^ 2) ^ (N + 1) * u ^ k ≤ (1 + Sig) * u ^ kk := by
      calc (1 + p.H) * (u ^ 2) ^ (N + 1) * u ^ k
          ≤ ((1 + Sig) * u) * (u ^ 2) ^ (N + 1) * u ^ k := by gcongr
        _ = (1 + Sig) * u ^ (k + 2 * N + 3) := by ring
        _ ≤ (1 + Sig) * u ^ kk := by
            gcongr
            rw [hkk]
            omega
    calc Real.pi ^ (1 / bgp) * Rp * (K * (A * u ^ k) * (1 + p.H) * (u ^ 2) ^ (N + 1))
        = Real.pi ^ (1 / bgp) * K * A * Rp * ((1 + p.H) * (u ^ 2) ^ (N + 1) * u ^ k) := by ring
      _ ≤ Real.pi ^ (1 / bgp) * K * A * Rp * ((1 + Sig) * u ^ kk) := by gcongr
      _ = _ := by ring
  have hgb : 3 * g ≤ 6 * K' * A' * (1 + Sig) * u ^ kk * Rp := by
    rw [hgR, hB', hpow, hc]
    have h1 : (1 + p.H) * (u ^ 2) ^ (N' + 1) * u ^ k' ≤ (1 + Sig) * u ^ kk := by
      calc (1 + p.H) * (u ^ 2) ^ (N' + 1) * u ^ k'
          ≤ ((1 + Sig) * u) * (u ^ 2) ^ (N' + 1) * u ^ k' := by gcongr
        _ = (1 + Sig) * u ^ (k' + 2 * N' + 3) := by ring
        _ ≤ (1 + Sig) * u ^ kk := by
            gcongr
            rw [hkk]
            omega
    calc 3 * (K' * (2 * (A' * u ^ k')) * (1 + p.H) * (u ^ 2) ^ (N' + 1) * Rp)
        = 6 * K' * A' * Rp * ((1 + p.H) * (u ^ 2) ^ (N' + 1) * u ^ k') := by ring
      _ ≤ 6 * K' * A' * Rp * ((1 + Sig) * u ^ kk) := by gcongr
      _ = _ := by ring
  rw [hpow]
  calc (phaseLpNorm p.period bgp (inletSourceF p i)).toReal +
        ∑ j : Fin 3, (phaseLpNorm p.period bgp (inletSourceG p i j)).toReal
      ≤ a * b + 3 * g := add_le_add hFr hsum
    _ ≤ Real.pi ^ (1 / bgp) * K * A * (1 + Sig) * u ^ kk * Rp +
          6 * K' * A' * (1 + Sig) * u ^ kk * Rp := add_le_add hab hgb
    _ = C * u ^ kk * p.R ^ (2 / bgp) := by rw [hCdef, hRp]; ring

/-! ## The column jets from the raw jets of order `≤ 2` and the chart calculus -/

/-- **Jets of order `≤ 2` of the raw profile** on the slow band `0 < s ≤ H = Σ/ν` (SP 2419-2423,
one order above `RawJetBound`; Part I `sct:train` (SP 261-291), `sct:transverse` (SP 460-467),
`sct:fixed-band` (SP 468-478) with jets `ℓ + j ≤ 3` of `ψ` and `ℓ + j ≤ 2` of `v`, polynomial
convention SP 255-258): `b_raw = (v₁, v₂ + εH)`, `H = (1-K)ψ`, and its first and second derivatives
in `(s, q, η)` are `≤ Cν^{-k}(1+|η|)^N`. -/
def RawProfJet2 : Prop :=
  ∀ Sig : ℝ, 0 < Sig → ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (k N : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig →
      ∀ x : Coord, 0 < x.1 → x.1 ≤ p.H → ∀ l ≤ 2,
        ‖iteratedFDeriv ℝ l (rawProf p) x‖ ≤ C * (p.ν ^ k)⁻¹ * (1 + |x.2.2|) ^ N

/-- **First-order chart calculus of the column** (pure calculus; SP 2367-2374): for a `C^∞`
inlet profile `e`, a raw profile `C^∞` near `x`, `s > 0`, `ε, ν ≤ 1`, the column
`s[(∂_s - νL_ε)e + B_εe]` is differentiable at `x` and its first-order chart jet is bounded by
`K(1+s+|η|)⁴ (Σ_{l≤3}‖D^l e‖)(1 + Σ_{l≤2}‖D^l b_raw‖)` (`L_ε` has coefficients of degree `≤ 2` in
`(s, η)` and order `2`, `B_ε` is bilinear of order `1` with coefficients of degree `≤ 1`; one
order above `VecDiffJet`, `BEpsJet`, `JetLe`). -/
def ColumnJetCalc : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (p : Params), p.ε ≤ 1 → p.ν ≤ 1 → ∀ i : Fin 2,
    ContDiff ℝ ∞ (p.inletProfile i) → ∀ x : Coord, 0 < x.1 → ContDiffAt ℝ ∞ (rawProf p) x →
      DifferentiableAt ℝ (colEpsR p i) x ∧
      chartJet (colEpsR p i) x ≤ K * (1 + x.1 + |x.2.2|) ^ 4 *
        (∑ l ∈ Finset.range 4, ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖) *
        (1 + ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l (rawProf p) x‖)

/-- Jets of `e_ε = e_0 + εe_1` from those of `e_0`, `e_1` (`inletSplit`, `0 ≤ ε ≤ 1`). -/
theorem isfb_inlet_jet {p : Params} {i : Fin 2} (hε1 : p.ε ≤ 1)
    (h0 : ContDiff ℝ ∞ (inletE0 p i)) (h1 : ContDiff ℝ ∞ (inletE1 p i)) (l : ℕ) (x : Coord) :
    ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤
      ‖iteratedFDeriv ℝ l (inletE0 p i) x‖ + ‖iteratedFDeriv ℝ l (inletE1 p i) x‖ := by
  have hε0 : 0 ≤ p.ε := p.ε_pos.le
  have hsplit : p.inletProfile i = inletE0 p i + p.ε • inletE1 p i := by
    rw [inletSplit]
    rfl
  have hc0 : ContDiffAt ℝ l (inletE0 p i) x :=
    (h0.of_le (by exact_mod_cast le_top)).contDiffAt
  have hc1' : ContDiffAt ℝ l (inletE1 p i) x :=
    (h1.of_le (by exact_mod_cast le_top)).contDiffAt
  have hc1 : ContDiffAt ℝ l (p.ε • inletE1 p i) x := hc1'.const_smul p.ε
  rw [hsplit, iteratedFDeriv_add_apply hc0 hc1, iteratedFDeriv_const_smul_apply hc1']
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_of_nonneg hε0]
  have hn : 0 ≤ ‖iteratedFDeriv ℝ l (inletE1 p i) x‖ := norm_nonneg _
  have : p.ε * ‖iteratedFDeriv ℝ l (inletE1 p i) x‖ ≤ ‖iteratedFDeriv ℝ l (inletE1 p i) x‖ := by
    calc p.ε * ‖iteratedFDeriv ℝ l (inletE1 p i) x‖
        ≤ 1 * ‖iteratedFDeriv ℝ l (inletE1 p i) x‖ := mul_le_mul_of_nonneg_right hε1 hn
      _ = _ := one_mul _
  linarith

/-- **`ColumnChartJet` from the raw jets of order `≤ 2` and the chart calculus.** -/
theorem columnChartJet_of (h2 : RawProfJet2) (hC : ColumnJetCalc) : ColumnChartJet := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨CI, κ, kI, NI, νI, hCI, hκ, hνI, hνI1, HIJ⟩ :=
    inletComponentJets Sig lam q hSig hq dm dp hdm 3
  obtain ⟨νV, hνV, HV⟩ := inletProfileSmoothVanish Sig lam q hSig hq dm dp hdm
  obtain ⟨CR, kR, NR, νR, hCR, hνR, HR2⟩ := h2 Sig hSig dm dp hdm
  obtain ⟨K, hK, HC⟩ := hC
  have hSig0 : 0 < 1 + Sig := by linarith
  refine ⟨K * ((1 + Sig) ^ 4 * (4 * CI) * (1 + 3 * CR)), κ, 4 + kI + kR, 4 + NI + NR,
    min νI (min νV νR), by positivity, hκ, lt_min hνI (lt_min hνV hνR), ?_⟩
  intro p d hreg hν hS hm i x hx0 hxH
  have e1 : p.ν ≤ νI := hν.trans (min_le_left _ _)
  have e2 : p.ν ≤ νV := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have e3 : p.ν ≤ νR := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hνpos : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ 1 := e1.trans hνI1
  have hu1 : 1 ≤ p.ν⁻¹ := (one_le_inv₀ hνpos).2 hν1
  have hpow : ∀ m : ℕ, (p.ν ^ m)⁻¹ = p.ν⁻¹ ^ m := fun m => by rw [inv_pow]
  have hHpos : 0 < p.H := p.H_pos
  have hxH' : x.1 ≤ p.H := by linarith
  have hε1 : p.ε ≤ 1 := by
    rw [hreg.eps_eq, Real.exp_le_one_iff]
    have := hreg.dm_le
    have := hreg.dm_pos
    have : 0 ≤ d / p.ν := div_nonneg (by linarith) hνpos.le
    rw [neg_div]
    linarith
  obtain ⟨hc0, hc1, hjI⟩ := HIJ p d ⟨hreg, e1, hS, hm⟩ i
  have hcd : ContDiff ℝ ∞ (p.inletProfile i) := (HV p d hreg e2 hS hm i).1
  have hraw : ContDiffAt ℝ ∞ (rawProf p) x := by
    have hon := bgRawProfileSmooth p d dm dp hreg
    have hU : (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) ∈ 𝓝 x :=
      (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hx0, trivial⟩
    exact hon.contDiffAt hU
  obtain ⟨hdiff, hbd⟩ := HC p hε1 hν1 i hcd x hx0 hraw
  refine ⟨hdiff, hbd.trans ?_⟩
  have hη0 : 0 ≤ |x.2.2| := abs_nonneg _
  have hE0 : 0 ≤ Real.exp (-(κ * |x.2.2| / p.c)) := (Real.exp_pos _).le
  have hJI0 : 0 ≤ CI * p.ν⁻¹ ^ kI * (1 + |x.2.2|) ^ NI * Real.exp (-(κ * |x.2.2| / p.c)) := by
    positivity
  have he : ∑ l ∈ Finset.range 4, ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤
      4 * (CI * p.ν⁻¹ ^ kI * (1 + |x.2.2|) ^ NI * Real.exp (-(κ * |x.2.2| / p.c))) := by
    have hl : ∀ l ∈ Finset.range 4, ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤
        CI * p.ν⁻¹ ^ kI * (1 + |x.2.2|) ^ NI * Real.exp (-(κ * |x.2.2| / p.c)) := by
      intro l hl
      have hl3 : l ≤ 3 := by simp at hl; omega
      refine (isfb_inlet_jet hε1 hc0 hc1 l x).trans ?_
      have := hjI l hl3 x hxH'
      rw [hpow] at this
      exact this
    refine (Finset.sum_le_sum hl).trans (le_of_eq ?_)
    simp
  have hr : ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l (rawProf p) x‖ ≤
      3 * (CR * p.ν⁻¹ ^ kR * (1 + |x.2.2|) ^ NR) := by
    have hl : ∀ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l (rawProf p) x‖ ≤
        CR * p.ν⁻¹ ^ kR * (1 + |x.2.2|) ^ NR := by
      intro l hl
      have hl2 : l ≤ 2 := by simp at hl; omega
      have := HR2 p d hreg e3 hS x hx0 hxH' l hl2
      rw [hpow] at this
      exact this
    refine (Finset.sum_le_sum hl).trans (le_of_eq ?_)
    simp
  have hH : 1 + p.H ≤ (1 + Sig) * p.ν⁻¹ := by
    have e : p.H = Sig * p.ν⁻¹ := by rw [Params.H, hS, div_eq_mul_inv]
    rw [e]
    nlinarith
  have hlin : 1 + x.1 + |x.2.2| ≤ ((1 + Sig) * p.ν⁻¹) * (1 + |x.2.2|) := by
    have : 1 + x.1 + |x.2.2| ≤ (1 + p.H) * (1 + |x.2.2|) := by nlinarith
    exact this.trans (mul_le_mul_of_nonneg_right hH (by linarith))
  have hpoly : (1 + x.1 + |x.2.2|) ^ 4 ≤ ((1 + Sig) * p.ν⁻¹) ^ 4 * (1 + |x.2.2|) ^ 4 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) hlin 4
  have hR1 : 1 ≤ p.ν⁻¹ ^ kR * (1 + |x.2.2|) ^ NR :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hu1) (one_le_pow₀ (by linarith))
  have hraw' : 1 + ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l (rawProf p) x‖ ≤
      (1 + 3 * CR) * (p.ν⁻¹ ^ kR * (1 + |x.2.2|) ^ NR) := by
    nlinarith
  have hS4 : 0 ≤ ∑ l ∈ Finset.range 4, ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hS3 : 0 ≤ 1 + ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l (rawProf p) x‖ := by
    have := Finset.sum_nonneg fun l (_ : l ∈ Finset.range 3) =>
      norm_nonneg (iteratedFDeriv ℝ l (rawProf p) x)
    linarith
  have hP0 : 0 ≤ ((1 + Sig) * p.ν⁻¹) ^ 4 * (1 + |x.2.2|) ^ 4 := by positivity
  have step := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hpoly hK.le) he hS4
    (mul_nonneg hK.le hP0)) hraw' hS3 (mul_nonneg (mul_nonneg hK.le hP0) (by positivity))
  rw [hpow]
  refine step.trans (le_of_eq ?_)
  ring

/-! ## The chart calculus of the column, split -/

/-- **`∂_s` costs one order** (pure calculus): `‖∂_sF‖ + ‖D∂_sF‖ ≤ Σ_{l≤2}‖D^lF‖`. -/
def DSJet1 : Prop :=
  ∀ (F : Coord → Axi.Merid), ContDiff ℝ ∞ F → ∀ x : Coord,
    DifferentiableAt ℝ (Axi.dS F) x ∧
    ‖Axi.dS F x‖ + ‖fderiv ℝ (Axi.dS F) x‖ ≤ ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l F x‖

/-- **First-order jet of the exact vector diffusion** (pure calculus, SP 2367-2369; one order above
`VecDiffJet`): `L_ε` has order `2` and coefficients of degree `≤ 2` in `(s, η)`, so for `C^∞` `F`
and `0 ≤ ε ≤ 1`, `‖L_εF‖ + ‖DL_εF‖ ≤ K(1+|s|+|η|)²Σ_{l≤3}‖D^lF‖`. -/
def VecDiffJet1 : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (ε : ℝ), 0 ≤ ε → ε ≤ 1 → ∀ (F : Coord → Axi.Merid), ContDiff ℝ ∞ F →
    ∀ x : Coord, DifferentiableAt ℝ (vecDiffEps ε F) x ∧
      ‖vecDiffEps ε F x‖ + ‖fderiv ℝ (vecDiffEps ε F) x‖ ≤
        K * (1 + |x.1| + |x.2.2|) ^ 2 * ∑ l ∈ Finset.range 4, ‖iteratedFDeriv ℝ l F x‖

/-- **First-order jet of the raw interaction** (pure calculus, SP 2007-2012, 2370-2374; one order
above `BEpsJet`): `B_εF = (b_raw·∇_ε)F + (F·∇_ε)b_raw`, `∇_ε = (Q_ε, ∂_η)`, is bilinear of order
`1` with coefficients of degree `≤ 1`, so for `C^∞` `F`, `b_raw` smooth near `x`, `ε ≤ 1`:
`‖B_εF‖ + ‖DB_εF‖ ≤ K(1+|s|+|η|)²(Σ_{l≤2}‖D^lF‖)(Σ_{l≤2}‖D^lb_raw‖)`. -/
def BEpsJet1 : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (p : Params), p.ε ≤ 1 → ∀ (F : Coord → Axi.Merid), ContDiff ℝ ∞ F →
    ∀ x : Coord, ContDiffAt ℝ ∞ (rawProf p) x →
      DifferentiableAt ℝ (bEps p F) x ∧
      ‖bEps p F x‖ + ‖fderiv ℝ (bEps p F) x‖ ≤ K * (1 + |x.1| + |x.2.2|) ^ 2 *
        (∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l F x‖) *
        (∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l (rawProf p) x‖)

/-- `DSJet1` holds. -/
theorem dSJet1 : DSJet1 := by
  intro F hF x
  have hc : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by simp)).differentiable (by simp)
  have hd : DifferentiableAt ℝ (Axi.dS F) x :=
    (hc x).clm_apply (differentiableAt_const _)
  refine ⟨hd, ?_⟩
  have h2 : fderiv ℝ (Axi.dS F) x =
      (fderiv ℝ (fderiv ℝ F) x).flip ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) := by
    have := fderiv_clm_apply (hc x) (differentiableAt_const ((1 : ℝ), ((0 : ℝ), (0 : ℝ))))
    rw [show Axi.dS F = fun y => (fderiv ℝ F y) ((fun _ => ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))) y)
      from rfl, this]
    simp
  have hDS : ‖fderiv ℝ (Axi.dS F) x‖ ≤ ‖fderiv ℝ (fderiv ℝ F) x‖ := by
    rw [h2]
    refine ((fderiv ℝ (fderiv ℝ F) x).flip.le_opNorm _).trans ?_
    rw [ContinuousLinearMap.opNorm_flip]
    exact mul_le_of_le_one_right (norm_nonneg (fderiv ℝ (fderiv ℝ F) x)) JetLeHelp.e1_le
  have hS : ‖Axi.dS F x‖ ≤ ‖fderiv ℝ F x‖ := JetLeHelp.dir_le x _ JetLeHelp.e1_le
  have h1 : ‖iteratedFDeriv ℝ 1 F x‖ = ‖fderiv ℝ F x‖ := norm_iteratedFDeriv_one F
  have h22 : ‖iteratedFDeriv ℝ 2 F x‖ = ‖fderiv ℝ (fderiv ℝ F) x‖ := by
    rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
  have h0 := norm_nonneg (iteratedFDeriv ℝ 0 F x)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith

/-- The first-order chart jet is bounded by the value and the derivative (no smoothness used). -/
theorem isfb_chartJet_le (G : Coord → Axi.Merid) (x : Coord) :
    chartJet G x ≤ (3 + 2 * |x.1| + |x.2.2|) * (‖G x‖ + ‖fderiv ℝ G x‖) := by
  have hS : ‖Axi.dS G x‖ ≤ ‖fderiv ℝ G x‖ := JetLeHelp.dir_le x _ JetLeHelp.e1_le
  have hQ : ‖Axi.dQ G x‖ ≤ ‖fderiv ℝ G x‖ := JetLeHelp.dir_le x _ JetLeHelp.eQ_le
  have hE : ‖Axi.dEta G x‖ ≤ ‖fderiv ℝ G x‖ := JetLeHelp.dir_le x _ JetLeHelp.eEta_le
  have hK : ‖kAge G x‖ ≤ 2 * |x.1| * ‖fderiv ℝ G x‖ + |x.2.2| * ‖fderiv ℝ G x‖ := by
    unfold kAge
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_two]
    have := abs_nonneg x.1
    have := abs_nonneg x.2.2
    gcongr
  unfold chartJet
  have h0 := norm_nonneg (G x)
  have h1 := norm_nonneg (fderiv ℝ G x)
  nlinarith [abs_nonneg x.1, abs_nonneg x.2.2]

/-- **`ColumnJetCalc` from the three first-order calculus leaves.** -/
theorem columnJetCalc_of (hD : DSJet1) (hV : VecDiffJet1) (hB : BEpsJet1) : ColumnJetCalc := by
  obtain ⟨KV, hKV, HV⟩ := hV
  obtain ⟨KB, hKB, HB⟩ := hB
  refine ⟨3 * (1 + KV + KB), by positivity, ?_⟩
  intro p hε1 hν1 i he x hx0 hraw
  have hν0 : 0 ≤ p.ν := p.ν_pos.le
  have hs : |x.1| = x.1 := abs_of_pos hx0
  obtain ⟨hdS, hbS⟩ := hD (p.inletProfile i) he x
  obtain ⟨hdL, hbL⟩ := HV p.ε p.ε_pos.le hε1 (p.inletProfile i) he x
  obtain ⟨hdB, hbB⟩ := HB p hε1 (p.inletProfile i) he x hraw
  obtain ⟨V, hV⟩ : ∃ V : Coord → Axi.Merid, V = fun m => Axi.dS (p.inletProfile i) m -
      p.ν • vecDiffEps p.ε (p.inletProfile i) m + bEps p (p.inletProfile i) m := ⟨_, rfl⟩
  have hev : colEpsR p i =ᶠ[𝓝 x] fun m : Coord => m.1 • V m := by
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hx0] with m hm
    simp only [colEpsR, if_pos (show 0 < m.1 from hm), colDiffR, colIntR, hV, smul_add]
  have hV' : HasFDerivAt V (fderiv ℝ (Axi.dS (p.inletProfile i)) x -
      p.ν • fderiv ℝ (vecDiffEps p.ε (p.inletProfile i)) x +
        fderiv ℝ (bEps p (p.inletProfile i)) x) x := by
    rw [hV]
    exact (hdS.hasFDerivAt.sub (hdL.hasFDerivAt.const_smul p.ν)).add hdB.hasFDerivAt
  have hW : HasFDerivAt (fun m : Coord => m.1 • V m)
      (x.1 • fderiv ℝ V x + (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).smulRight (V x)) x :=
    hasFDerivAt_fst.smul hV'.differentiableAt.hasFDerivAt
  refine ⟨hW.differentiableAt.congr_of_eventuallyEq hev, ?_⟩
  have hcj : chartJet (colEpsR p i) x = chartJet (fun m : Coord => m.1 • V m) x := by
    simp only [chartJet, kAge, Axi.dS, Axi.dQ, Axi.dEta, hev.fderiv_eq, hev.eq_of_nhds]
  rw [hcj]
  refine (isfb_chartJet_le _ x).trans ?_
  rw [hW.fderiv]
  -- the factor `s`
  have hfst : ‖(ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).smulRight (V x)‖ ≤ ‖V x‖ := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.norm_fst_le _ _ _)
  -- the three pieces
  have hVx : ‖V x‖ ≤ ‖Axi.dS (p.inletProfile i) x‖ +
      ‖vecDiffEps p.ε (p.inletProfile i) x‖ + ‖bEps p (p.inletProfile i) x‖ := by
    rw [hV]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans ?_) le_rfl
    rw [norm_smul, Real.norm_of_nonneg hν0]
    have := norm_nonneg (vecDiffEps p.ε (p.inletProfile i) x)
    nlinarith
  have hDVx : ‖fderiv ℝ V x‖ ≤ ‖fderiv ℝ (Axi.dS (p.inletProfile i)) x‖ +
      ‖fderiv ℝ (vecDiffEps p.ε (p.inletProfile i)) x‖ +
        ‖fderiv ℝ (bEps p (p.inletProfile i)) x‖ := by
    rw [hV'.fderiv]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans ?_) le_rfl
    rw [norm_smul, Real.norm_of_nonneg hν0]
    have := norm_nonneg (fderiv ℝ (vecDiffEps p.ε (p.inletProfile i)) x)
    nlinarith
  have hJ32 : ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤
      ∑ l ∈ Finset.range 4, ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ := by
    rw [Finset.sum_range_succ _ 3]
    linarith [norm_nonneg (iteratedFDeriv ℝ 3 (p.inletProfile i) x)]
  have hJ3 : 0 ≤ ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hJr : 0 ≤ ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l (rawProf p) x‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  rw [hs] at hbL hbB
  have hP1 : 1 ≤ 1 + x.1 + |x.2.2| := by have := abs_nonneg x.2.2; linarith
  have hP2 : 1 ≤ (1 + x.1 + |x.2.2|) ^ 2 := one_le_pow₀ hP1
  set a := ∑ l ∈ Finset.range 4, ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ with ha
  set b := ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ with hb
  set r := ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l (rawProf p) x‖ with hr
  set Q := (1 + x.1 + |x.2.2|) ^ 2 with hQ
  have ha0 : 0 ≤ a := hJ3.trans hJ32
  have hQ0 : 0 ≤ Q := by linarith
  clear_value a b r Q
  have hVb : ‖V x‖ + ‖fderiv ℝ V x‖ ≤ (1 + KV + KB) * Q * a * (1 + r) := by
    have t1 : b ≤ Q * a := hJ32.trans (le_mul_of_one_le_left ha0 hP2)
    have hKBQ : 0 ≤ KB * Q := mul_nonneg hKB.le hQ0
    have t2 : KB * Q * b * r ≤ KB * Q * a * r :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ32 hKBQ) hJr
    have t3 : 0 ≤ Q * a * r := mul_nonneg (mul_nonneg hQ0 ha0) hJr
    have t4 : 0 ≤ KV * Q * a * r := mul_nonneg (mul_nonneg (mul_nonneg hKV.le hQ0) ha0) hJr
    have t5 : 0 ≤ KB * Q * a := mul_nonneg hKBQ ha0
    have e : (1 + KV + KB) * Q * a * (1 + r) =
        Q * a + Q * a * r + KV * Q * a + KV * Q * a * r + KB * Q * a + KB * Q * a * r := by ring
    rw [e]
    linarith
  rw [hs]
  have hA : 3 + 2 * x.1 + |x.2.2| ≤ 3 * (1 + x.1 + |x.2.2|) := by
    have := abs_nonneg x.2.2; linarith
  have hB2 : 1 + x.1 ≤ 1 + x.1 + |x.2.2| := by have := abs_nonneg x.2.2; linarith
  have hWb : ‖x.1 • V x‖ +
      ‖x.1 • fderiv ℝ V x + (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).smulRight (V x)‖ ≤
        (1 + x.1) * (‖V x‖ + ‖fderiv ℝ V x‖) := by
    have e2 : ‖x.1 • fderiv ℝ V x + (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).smulRight (V x)‖ ≤
        x.1 * ‖fderiv ℝ V x‖ + ‖V x‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, hs]
      linarith
    rw [norm_smul, Real.norm_eq_abs, hs]
    nlinarith [norm_nonneg (V x), norm_nonneg (fderiv ℝ V x)]
  have hnn : 0 ≤ ‖V x‖ + ‖fderiv ℝ V x‖ := by positivity
  have hP0 : 0 ≤ 1 + x.1 + |x.2.2| := by linarith
  show (3 + 2 * x.1 + |x.2.2|) * (‖x.1 • V x‖ +
      ‖x.1 • fderiv ℝ V x + (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).smulRight (V x)‖) ≤ _
  calc (3 + 2 * x.1 + |x.2.2|) * (‖x.1 • V x‖ +
        ‖x.1 • fderiv ℝ V x + (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).smulRight (V x)‖)
      ≤ (3 * (1 + x.1 + |x.2.2|)) * ((1 + x.1 + |x.2.2|) *
          ((1 + KV + KB) * Q * a * (1 + r))) := by
        gcongr
        exact hWb.trans (mul_le_mul hB2 hVb hnn hP0)
    _ = 3 * (1 + KV + KB) * (1 + x.1 + |x.2.2|) ^ 4 * a * (1 + r) := by rw [hQ]; ring

/-- **The bound from the raw jets of order `≤ 2` and the chart calculus of the column.** -/
theorem inletSourceFieldBound_of_raw2 (hRaw : RawJointSmooth) (h2 : RawProfJet2)
    (hC : ColumnJetCalc) : InletSourceFieldBound :=
  inletSourceFieldBound_of_colJet hRaw (columnChartJet_of h2 hC)

/-- **Task `PartII-b:G4/4/1/1/8`** (`InletSourceFieldBound`, SP 2355-2385), conditional on the
three open leaves `RawProfJet2` (Part I input), `VecDiffJet1`, `BEpsJet1` (chart calculus). -/
theorem inletSourceFieldBound_of_leaves (hRaw : RawJointSmooth) (h2 : RawProfJet2) (hV : VecDiffJet1)
    (hB : BEpsJet1) : InletSourceFieldBound :=
  inletSourceFieldBound_of_raw2 hRaw h2 (columnJetCalc_of dSJet1 hV hB)

end UnforcedLeray.Short.IIb

end
