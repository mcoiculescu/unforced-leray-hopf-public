import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org_C_1.WeakRealPer
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawGood
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.AbsPhaseIBP
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletB
import UnforcedLeray.Short.PartIIb.Tasks.RowOrdRel
import UnforcedLeray.Short.PartIIb.Tasks.StrongLateCoeff.NvFderiv
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth.SmoothPt.NicePhaseTest
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivSmooth.WeakClassical
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivSmooth.SmoothPt.DivOffAxis.Core

/-!
# Helper `NiceKOut` for `PartII-b:G2/1/org/C/1` (`PhysKOutCand`)

1. `isPhaseTest_convT_raw`: when `p.raw` is jointly `C^∞`, `convT p.raw Φ` is a phase test
   for every phase test `Φ`.
2. `chartDivR_rawProf_offAxis_zero`: off the symmetry axis, `chartDivR p.ε (rawProf p)` vanishes
   at `Axi.chart p.R τ y` because `p.raw` is divergence-free off the axis (`offAxis_divFree`).
3. `isKOut_niceProf`: for every `NiceProf p.c b'` with weak derivatives `Qb'`, `Eb'`,
   `IsKOut p b' (kOutChart p b' Qb' Eb')` holds.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.PhysKOutCandHelp

open UnforcedLeray.Short.IIb
open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

private theorem raw_periodic_all (p : Params) (τ : ℝ) (y : Space) :
    p.raw (τ + p.period) y = p.raw τ y := by
  by_cases hy : y ∈ Axi.axis
  · have hev : (Axi.Nv p.R (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ)
        (τ + p.period)) =ᶠ[𝓝[Axi.axisᶜ] y]
        (Axi.Nv p.R (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) τ) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have h1 := raw_periodic_off (p := p) τ hz
      rwa [p.raw_eq_off_axis _ z hz, p.raw_eq_off_axis _ z hz] at h1
    show UnforcedLeray.Cons.C03.Concrete.axisExt _ y = UnforcedLeray.Cons.C03.Concrete.axisExt _ y
    unfold UnforcedLeray.Cons.C03.Concrete.axisExt
    simp only [hy, ↓reduceIte, limUnder]
    rw [Filter.map_congr hev]
  · exact raw_periodic_off τ hy

theorem isPhaseTest_convT_raw {p : Params}
    (hraw : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2))
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest p.period Φ) :
    IsPhaseTest p.period (convT p.raw Φ) := by
  have hVc : ContDiff ℝ ∞ (fun w : ℝ × Space => realC (p.raw w.1 w.2)) :=
    contDiff_realC_field hraw
  have hgrad : ContDiff ℝ ∞ (gradUT p.raw Φ) := by
    have heq : gradUT p.raw Φ =
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℂ)).symm ∘
          (fun x (k : Fin 3) => ∑ i : Fin 3,
            Φ x i * dy k (fun w : ℝ × Space => realC (p.raw w.1 w.2)) x i) := by
      funext x; ext k; simp [gradUT, dy_realC_comp hraw k _ x]
    rw [heq]
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℂ)).symm.contDiff.comp
      (contDiff_pi.mpr fun k => ContDiff.sum fun i _ =>
        (srwf_coord_contDiff hΦ.smooth i).mul
          (srwf_coord_contDiff (UnforcedLeray.PhaseSpace.contDiff_dy hVc k) i))
  have hadv : ContDiff ℝ ∞ (advT (fun x => realC (p.raw x.1 x.2)) Φ) :=
    ContDiff.sum fun k _ =>
      (srwf_coord_contDiff hVc k).smul (UnforcedLeray.PhaseSpace.contDiff_dy hΦ.smooth k)
  refine ⟨hgrad.sub hadv, ?_, ?_⟩
  · intro τ y
    have hraw_per : p.raw (τ + p.period) = p.raw τ := funext (raw_periodic_all p τ)
    have hgrad_per : gradUT p.raw Φ (τ + p.period, y) = gradUT p.raw Φ (τ, y) := by
      ext k
      simp only [gradUT, WithLp.ofLp_toLp, hΦ.periodic τ y, hraw_per]
    have hadv_per : advT (fun x => realC (p.raw x.1 x.2)) Φ (τ + p.period, y) =
        advT (fun x => realC (p.raw x.1 x.2)) Φ (τ, y) := by
      unfold advT
      refine Finset.sum_congr rfl fun k _ => ?_
      dsimp only
      rw [raw_periodic_all p τ y, (hΦ.dy k).periodic τ y]
    simp only [convT, hgrad_per, hadv_per]
  · obtain ⟨R, hR⟩ := hΦ.bounded_support
    exact ⟨R, convT_eq_zero_of_norm_gt hR⟩

theorem chartDivR_rawProf_offAxis_zero {p : Params} {d dm dp : ℝ}
    (hreg : BgRegime p d dm dp) (τ : ℝ) {y : Space} (hy : y ∉ Axi.axis) :
    chartDivR p.ε (rawProf p) (Axi.chart p.R τ y) = 0 := by
  have hdiv0 := offAxis_divFree hreg τ hy
  have hev : p.raw τ =ᶠ[𝓝 y] Axi.Nv p.R (rawProf p) τ := by
    filter_upwards [Axi.isOpen_compl_axis.mem_nhds (Set.mem_compl hy)] with z hz
    exact p.raw_eq_off_axis τ z hz
  have hs : 0 < (Axi.chart p.R τ y).1 := Axi.age_pos p.R_pos.ne' hy
  have hdiff := rawProfDiffAt dm dp p d hreg _ hs
  have hfd : fderiv ℝ (p.raw τ) y = nvL p.R τ (rawProf p) y := by
    rw [hev.fderiv_eq]
    exact (nvFderiv_hasFDerivAt p.R_pos hy hdiff).fderiv
  rw [hfd] at hdiv0
  have hcoord : ∀ k : Fin 3, (EuclideanSpace.single k (1 : ℝ) : Space) = coordinateVector k :=
    fun _ => rfl
  simp only [hcoord, nvL_apply] at hdiv0
  have hRε : p.R⁻¹ = p.ε := inv_inv p.ε
  have hnvQ : nvQ p.R⁻¹ (rawProf p) (Axi.chart p.R τ y) =
      qEps p.ε (rawProf p) (Axi.chart p.R τ y) := by
    rw [hRε]; rfl
  rw [hnvQ] at hdiv0
  have heR_sq : (y 0 * (Axi.ϱ y)⁻¹) ^ 2 + (y 1 * (Axi.ϱ y)⁻¹) ^ 2 = 1 := by
    simp only [← div_eq_mul_inv]
    exact Axi.eR_sq_sum hy
  have hDivE := DivOff.div_eRD hy
  simp only [Fin.sum_univ_three] at hDivE
  have hsqrt : Real.sqrt (Axi.age p.R y) = p.R / Axi.ϱ y := Axi.sqrt_age p.R_pos hy
  have hρne : Axi.ϱ y ≠ 0 := Axi.ϱ_ne_zero hy
  have hRne : p.R ≠ 0 := p.R_pos.ne'
  have h3 : Real.sqrt (Axi.age p.R y) * rawProf p (Axi.chart p.R τ y) 0 *
      (Axi.eRD y (coordinateVector 0) 0 + Axi.eRD y (coordinateVector 1) 1 +
        Axi.eRD y (coordinateVector 2) 2) =
      Axi.age p.R y * (p.ε * rawProf p (Axi.chart p.R τ y) 0) := by
    rw [hDivE, hsqrt, ← hRε]
    unfold Axi.age
    field_simp
  have hcalc : ∑ k : Fin 3,
      (Axi.ϱD y (coordinateVector k) •
          (Axi.age p.R y • Axi.frameL y (qEps p.ε (rawProf p) (Axi.chart p.R τ y))) +
        (coordinateVector k) 2 •
          (Axi.age p.R y • Axi.frameL y (Axi.dEta (rawProf p) (Axi.chart p.R τ y))) +
        (Real.sqrt (Axi.age p.R y) * rawProf p (Axi.chart p.R τ y) 0) •
          Axi.eRD y (coordinateVector k)) k =
      Axi.age p.R y * chartDivR p.ε (rawProf p) (Axi.chart p.R τ y) := by
    simp only [Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Axi.frameL_apply, Axi.ϱD_apply, Axi.coordinateVector_apply,
      Axi.eR_apply_zero, Axi.eR_apply_one, Axi.eR_apply_two, div_eq_mul_inv,
      Fin.isValue, Fin.reduceEq, ↓reduceIte]
    unfold chartDivR
    linear_combination
      Axi.age p.R y * (qEps p.ε (rawProf p) (Axi.chart p.R τ y)).ofLp 0 * heR_sq + h3
  rw [hcalc] at hdiv0
  have hage_pos : 0 < Axi.age p.R y := hs
  exact (mul_eq_zero.mp hdiv0).resolve_left hage_pos.ne'

private theorem convT_slab_ibp {P : ℝ} (hP : 0 < P) {V : ℝ → SpatialField}
    {E Φ : ℝ × Space → CVec3}
    (hV : ContDiff ℝ ∞ (fun x : ℝ × Space => V x.1 x.2))
    (hE : ContDiff ℝ ∞ E)
    (hdiv : ∀ x, E x ≠ 0 →
      ∑ j : Fin 3, (fderiv ℝ (V x.1) x.2 (EuclideanSpace.single j 1)) j = 0)
    (hΦ : IsPhaseTest P Φ) :
    pairF P (convT V Φ) E =
      pairF P Φ (fun x => advT (fun w => realC (V w.1 w.2)) E x +
        advT E (fun w => realC (V w.1 w.2)) x) := by
  let _ : Fact (0 < P) := ⟨hP⟩
  set Vc : ℝ × Space → CVec3 := fun w => realC (V w.1 w.2)
  have hVcc : ContDiff ℝ ∞ Vc := contDiff_realC_field hV
  have hdivc : ∀ x, E x ≠ 0 → ∑ j : Fin 3, dy j Vc x j = 0 := by
    intro x hx
    have h := hdiv x hx
    have : ∑ j : Fin 3, dy j Vc x j = ((∑ j : Fin 3, ((fderiv ℝ (V x.1) x.2
        (EuclideanSpace.single j 1)) j) : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun j _ => dy_realC_comp hV j j x
    rw [this, h]; simp
  obtain ⟨hB, hD, hBD⟩ := abs_adv_slab hΦ hE hVcc hdivc
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  have hG : Integrable (fun z => dotL (Φ z) (advT E Vc z)) (srwfSlab P) := by
    have hc : Continuous (advT E Vc) := by
      unfold advT
      exact continuous_finsetSum _ fun k _ =>
        (srwf_coord_contDiff hE k).continuous.smul
          (UnforcedLeray.PhaseSpace.contDiff_dy hVcc k).continuous
    exact UnforcedLeray.B0005.integrable_slab (𝒯 := P)
      ((dotL.continuous.comp hΦ.smooth.continuous).clm_apply hc) (R := R)
      (fun t y hy => by simp [hR t y hy])
  have e1 : pairF P (convT V Φ) E =
      phaseInt P (fun z => dotL (Φ z) (advT E Vc z) - dotL (advT Vc Φ z) (E z)) := by
    unfold pairF
    congr 1; funext z
    simp only [convT, map_sub, sub_apply]
    rw [abs_gradUT_dot hV]
  have e2 : pairF P Φ (fun x => advT Vc E x + advT E Vc x) =
      phaseInt P (fun z => dotL (Φ z) (advT Vc E z) + dotL (Φ z) (advT E Vc z)) := by
    unfold pairF; congr 1; funext z; simp only [map_add]
  have hI1 : Integrable (fun z => dotL (Φ z) (advT E Vc z) - dotL (advT Vc Φ z) (E z))
      (srwfSlab P) := hG.sub hB
  have hI2 : Integrable (fun z => dotL (Φ z) (advT Vc E z) + dotL (Φ z) (advT E Vc z))
      (srwfSlab P) := hD.add hG
  rw [e1, e2, srwf_phaseInt_eq hI1, srwf_phaseInt_eq hI2,
    integral_sub hG hB, integral_add hD hG, hBD]
  congr 1
  ring

private theorem fderiv_reM_imM {b' : CProf} (hb' : ContDiff ℝ ∞ b') (x w : Coord) (j : Fin 2) :
    ((fderiv ℝ b' x w) j).re = fderiv ℝ (fun y => reM (b' y)) x w j ∧
      ((fderiv ℝ b' x w) j).im = fderiv ℝ (fun y => imM (b' y)) x w j := by
  have hbd : DifferentiableAt ℝ b' x := hb'.differentiable (by simp) x
  have hbRd : DifferentiableAt ℝ (fun y => reM (b' y)) x :=
    (NicePT.contDiff_reM.comp hb').differentiable (by simp) x
  have hbId : DifferentiableAt ℝ (fun y => imM (b' y)) x :=
    (NicePT.contDiff_imM.comp hb').differentiable (by simp) x
  constructor
  · have h1 := (Complex.reCLM.comp
      ((EuclideanSpace.proj j : CMerid →L[ℂ] ℂ).restrictScalars ℝ)).hasFDerivAt.comp
      x hbd.hasFDerivAt
    have h2 := (EuclideanSpace.proj j : Axi.Merid →L[ℝ] ℝ).hasFDerivAt.comp x hbRd.hasFDerivAt
    have heq : (fun y : Coord => (b' y j).re) = fun y => reM (b' y) j := rfl
    have hfd : fderiv ℝ (fun y : Coord => (b' y j).re) x =
        fderiv ℝ (fun y : Coord => reM (b' y) j) x := by rw [heq]
    have h1' := h1.fderiv
    have h2' := h2.fderiv
    change (Complex.reCLM.comp
      ((EuclideanSpace.proj j : CMerid →L[ℂ] ℂ).restrictScalars ℝ) (fderiv ℝ b' x w)) =
      (EuclideanSpace.proj j : Axi.Merid →L[ℝ] ℝ) (fderiv ℝ (fun y => reM (b' y)) x w)
    have hcomp := congrArg (fun L : Coord →L[ℝ] ℝ => L w) (h1'.symm.trans (hfd.trans h2'))
    simpa using hcomp
  · have h1 := (Complex.imCLM.comp
      ((EuclideanSpace.proj j : CMerid →L[ℂ] ℂ).restrictScalars ℝ)).hasFDerivAt.comp
      x hbd.hasFDerivAt
    have h2 := (EuclideanSpace.proj j : Axi.Merid →L[ℝ] ℝ).hasFDerivAt.comp x hbId.hasFDerivAt
    have heq : (fun y : Coord => (b' y j).im) = fun y => imM (b' y) j := rfl
    have hfd : fderiv ℝ (fun y : Coord => (b' y j).im) x =
        fderiv ℝ (fun y : Coord => imM (b' y) j) x := by rw [heq]
    have h1' := h1.fderiv
    have h2' := h2.fderiv
    change (Complex.imCLM.comp
      ((EuclideanSpace.proj j : CMerid →L[ℂ] ℂ).restrictScalars ℝ) (fderiv ℝ b' x w)) =
      (EuclideanSpace.proj j : Axi.Merid →L[ℝ] ℝ) (fderiv ℝ (fun y => imM (b' y)) x w)
    have hcomp := congrArg (fun L : Coord →L[ℝ] ℝ => L w) (h1'.symm.trans (hfd.trans h2'))
    simpa using hcomp

theorem isKOut_niceProf {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp)
    (hraw : ContDiff ℝ ∞ (fun x : ℝ × Space => p.raw x.1 x.2))
    {b' Qb' Eb' : CProf} (hb' : NiceProf p.c b')
    (hQb' : HasWeakVec (vQ p.ε) (dQ p.ε) b' Qb')
    (hEb' : HasWeakVec vEta dZero b' Eb') :
    IsKOut p b' (kOutChart p b' Qb' Eb') := by
  intro Φ hΦ
  have hEtest : IsPhaseTest p.period (NvC p.R b') :=
    nvCNicePhaseTest_proof p.c p.ε b' p.c_pos p.ε_pos hb'
  have hdiv_on_E : ∀ x : ℝ × Space, NvC p.R b' x ≠ 0 →
      ∑ j : Fin 3, (fderiv ℝ (p.raw x.1) x.2 (EuclideanSpace.single j 1)) j = 0 := by
    intro x hx
    by_cases hy : x.2 ∈ Axi.axis
    · exfalso
      apply hx
      have hρ0 : Axi.ϱ x.2 = 0 := (Axi.mem_axis_iff x.2).1 hy
      have hage0 : Axi.age p.R x.2 = 0 := by simp [Axi.age, hρ0]
      have hNv0 : ∀ f : Coord → Axi.Merid, Axi.Nv p.R f x.1 x.2 = 0 := fun f => by
        simp [Axi.Nv, hage0]
      have hrc0 : realC (0 : Space) = 0 := by ext i; simp [realC_apply]
      simp [NvC, hNv0, hrc0]
    · exact offAxis_divFree hreg x.1 hy
  rw [convT_slab_ibp p.period_pos hraw hEtest.smooth hdiv_on_E hΦ]
  set g_cl : CProf := kOutChart p b' (classOp (vQ p.ε) (dQ p.ε) b') (classOp vEta dZero b')
  have hptw : pairF p.period Φ
      (fun x => advT (fun w => realC (p.raw w.1 w.2)) (NvC p.R b') x +
        advT (NvC p.R b') (fun w => realC (p.raw w.1 w.2)) x) =
      pairF p.period Φ (NvC p.R g_cl) := by
    refine pairF_congr_offAxis Φ _ _ fun τ y hy => ?_
    obtain ⟨hsm, _, s0, s1, L, _, hz⟩ := hb'
    set bR : Coord → Axi.Merid := fun z => reM (b' z)
    set bI : Coord → Axi.Merid := fun z => imM (b' z)
    have hbR_sm : ContDiff ℝ ∞ bR := NicePT.contDiff_reM.comp hsm
    have hbI_sm : ContDiff ℝ ∞ bI := NicePT.contDiff_imM.comp hsm
    have hzR : ∀ x : Coord, s1 < x.1 → bR x = 0 := fun x hx => by
      have := hz x (Or.inr (Or.inl hx)); ext i; simp [bR, reM, this]
    have hzI : ∀ x : Coord, s1 < x.1 → bI x = 0 := fun x hx => by
      have := hz x (Or.inr (Or.inl hx)); ext i; simp [bI, imM, this]
    set ER : ℝ × Space → CVec3 := fun x => realC (Axi.Nv p.R bR x.1 x.2)
    set EI : ℝ × Space → CVec3 := fun x => realC (Axi.Nv p.R bI x.1 x.2)
    have hER_sm : ContDiff ℝ ∞ ER :=
      NicePT.contDiff_realC.comp (NicePT.contDiff_Nv p.R_pos hbR_sm hzR)
    have hEI_sm : ContDiff ℝ ∞ EI :=
      NicePT.contDiff_realC.comp (NicePT.contDiff_Nv p.R_pos hbI_sm hzI)
    set Vc : ℝ × Space → CVec3 := fun w => realC (p.raw w.1 w.2)
    set Vnv : ℝ × Space → CVec3 := fun w => realC (Axi.Nv p.R (rawProf p) w.1 w.2)
    have hopen : IsOpen {x : ℝ × Space | x.2 ∉ Axi.axis} :=
      Axi.isOpen_compl_axis.preimage continuous_snd
    have hUev : Vc =ᶠ[𝓝 (τ, y)] Vnv := by
      filter_upwards [hopen.mem_nhds (show (τ, y) ∈ _ from hy)] with x hx
      show realC (p.raw x.1 x.2) = _
      rw [p.raw_eq_off_axis x.1 x.2 hx]
      rfl
    have hdy_lin : ∀ k : Fin 3, dy k (NvC p.R b') (τ, y) =
        dy k ER (τ, y) + Complex.I • dy k EI (τ, y) := by
      intro k
      have hEd : HasFDerivAt (fun x => ER x + Complex.I • EI x)
          (fderiv ℝ ER (τ, y) + Complex.I • fderiv ℝ EI (τ, y)) (τ, y) :=
        ((hER_sm.differentiable (by simp) (τ, y)).hasFDerivAt).add
          (((hEI_sm.differentiable (by simp) (τ, y)).hasFDerivAt).const_smul Complex.I)
      have heq : NvC p.R b' = fun x => ER x + Complex.I • EI x := rfl
      simp only [dy, heq, hEd.fderiv, add_apply, smul_apply]
    have hadv1 : advT Vc (NvC p.R b') (τ, y) =
        advT Vnv ER (τ, y) + Complex.I • advT Vnv EI (τ, y) := by
      have hsplit : advT Vc (NvC p.R b') (τ, y) =
          advT Vc ER (τ, y) + Complex.I • advT Vc EI (τ, y) := by
        unfold advT
        simp only [hdy_lin, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
        congr 2; funext k; rw [smul_comm]
      have c1 : advT Vc ER (τ, y) = advT Vnv ER (τ, y) :=
        advT_congr hUev.eq_of_nhds EventuallyEq.rfl
      have c2 : advT Vc EI (τ, y) = advT Vnv EI (τ, y) :=
        advT_congr hUev.eq_of_nhds EventuallyEq.rfl
      rw [hsplit, c1, c2]
    have hadv2 : advT (NvC p.R b') Vc (τ, y) =
        advT ER Vnv (τ, y) + Complex.I • advT EI Vnv (τ, y) := by
      have hsplit : advT (NvC p.R b') Vc (τ, y) =
          advT ER Vc (τ, y) + Complex.I • advT EI Vc (τ, y) := by
        unfold advT NvC
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, add_smul, mul_smul,
          Finset.sum_add_distrib, Finset.smul_sum]
        rfl
      have c1 : advT ER Vc (τ, y) = advT ER Vnv (τ, y) := advT_congr rfl hUev
      have c2 : advT EI Vc (τ, y) = advT EI Vnv (τ, y) := advT_congr rfl hUev
      rw [hsplit, c1, c2]
    have hs : 0 < (Axi.chart p.R τ y).1 := Axi.age_pos p.R_pos.ne' hy
    have hraw_d := rawProfDiffAt dm dp p d hreg _ hs
    have hcR := chartAdvPtw p.R p.R_pos (rawProf p) bR τ y hy hraw_d
      (hbR_sm.differentiable (by simp) _)
    have hcI := chartAdvPtw p.R p.R_pos (rawProf p) bI τ y hy hraw_d
      (hbI_sm.differentiable (by simp) _)
    have hRε : p.R⁻¹ = p.ε := inv_inv p.ε
    rw [hRε] at hcR hcI
    have hcomb : advT Vc (NvC p.R b') (τ, y) + advT (NvC p.R b') Vc (τ, y) =
        (advT Vnv ER (τ, y) + advT ER Vnv (τ, y)) +
          Complex.I • (advT Vnv EI (τ, y) + advT EI Vnv (τ, y)) := by
      rw [hadv1, hadv2, smul_add]; abel
    rw [hcomb, hcR, hcI]
    set m0 := Axi.chart p.R τ y
    have hdiv_z : chartDivR p.ε (rawProf p) m0 = 0 := chartDivR_rawProf_offAxis_zero hreg τ hy
    have hre_Q : ∀ j : Fin 2, (classOp (vQ p.ε) (dQ p.ε) b' m0 j).re = qEps p.ε bR m0 j := by
      intro j
      have h0 := (fderiv_reM_imM hsm m0 (cdir 0) j).1
      have h1 := (fderiv_reM_imM hsm m0 (cdir 1) j).1
      have h2 := (fderiv_reM_imM hsm m0 (cdir 2) j).1
      simp only [classOp, vQ, dQ, Fin.sum_univ_three, Fin.isValue, PiLp.add_apply, PiLp.smul_apply,
        Complex.add_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, h0, h1, h2]
      simp only [qEps, kAge, Axi.dS, Axi.dQ, Axi.dEta, cdir, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, bR, reM]
      ring
    have him_Q : ∀ j : Fin 2, (classOp (vQ p.ε) (dQ p.ε) b' m0 j).im = qEps p.ε bI m0 j := by
      intro j
      have h0 := (fderiv_reM_imM hsm m0 (cdir 0) j).2
      have h1 := (fderiv_reM_imM hsm m0 (cdir 1) j).2
      have h2 := (fderiv_reM_imM hsm m0 (cdir 2) j).2
      simp only [classOp, vQ, dQ, Fin.sum_univ_three, Fin.isValue, PiLp.add_apply, PiLp.smul_apply,
        Complex.add_im, smul_eq_mul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, h0, h1, h2]
      simp only [qEps, kAge, Axi.dS, Axi.dQ, Axi.dEta, cdir, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, bI, imM]
      ring
    have hre_E : ∀ j : Fin 2, (classOp vEta dZero b' m0 j).re = Axi.dEta bR m0 j := by
      intro j
      simp only [classOp, vEta, dZero, Fin.sum_univ_three, Fin.isValue, PiLp.add_apply,
        PiLp.smul_apply, Complex.add_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, one_mul, add_zero, zero_add, sub_zero, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Axi.dEta, cdir]
      exact (fderiv_reM_imM hsm m0 (0, (0, 1)) j).1
    have him_E : ∀ j : Fin 2, (classOp vEta dZero b' m0 j).im = Axi.dEta bI m0 j := by
      intro j
      simp only [classOp, vEta, dZero, Fin.sum_univ_three, Fin.isValue, PiLp.add_apply,
        PiLp.smul_apply, Complex.add_im, smul_eq_mul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, one_mul, add_zero, zero_add, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Axi.dEta, cdir]
      exact (fderiv_reM_imM hsm m0 (0, (0, 1)) j).2
    have hre_g : reM (g_cl m0) = m0.1 • (rawProf p m0 0 • qEps p.ε bR m0 +
        rawProf p m0 1 • Axi.dEta bR m0 +
        (bR m0 0 • qEps p.ε (rawProf p) m0 + bR m0 1 • Axi.dEta (rawProf p) m0)) := by
      ext j
      simp only [g_cl, kOutChart, hdiv_z, cplx, reM, bR, WithLp.ofLp_toLp,
        PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, hre_Q j, hre_E j]
      ring
    have him_g : imM (g_cl m0) = m0.1 • (rawProf p m0 0 • qEps p.ε bI m0 +
        rawProf p m0 1 • Axi.dEta bI m0 +
        (bI m0 0 • qEps p.ε (rawProf p) m0 + bI m0 1 • Axi.dEta (rawProf p) m0)) := by
      ext j
      simp only [g_cl, kOutChart, hdiv_z, cplx, imM, bI, WithLp.ofLp_toLp,
        PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, add_zero, him_Q j, him_E j]
      ring
    unfold NvC Axi.Nv
    change realC (Real.sqrt (Axi.age p.R y) • Axi.frameL y _) +
        Complex.I • realC (Real.sqrt (Axi.age p.R y) • Axi.frameL y _) =
      realC (Real.sqrt (Axi.age p.R y) • Axi.frameL y (reM (g_cl m0))) +
        Complex.I • realC (Real.sqrt (Axi.age p.R y) • Axi.frameL y (imM (g_cl m0)))
    rw [hre_g, him_g]
  rw [hptw]
  have hvQ_sm : ∀ j : Fin 3, ContDiff ℝ ∞ (fun x : Coord => vQ p.ε x j) := by
    intro j; fin_cases j <;> simp [vQ] <;> fun_prop
  have hvEta_sm : ∀ j : Fin 3, ContDiff ℝ ∞ (fun x : Coord => vEta x j) := by
    intro j; fin_cases j <;> simp [vEta] <;> fun_prop
  have hQae := divWeakClassical_proof (vQ p.ε) (dQ p.ε) p.c b' Qb' hvQ_sm contDiff_const hb' hQb'
  have hEae := divWeakClassical_proof vEta dZero p.c b' Eb' hvEta_sm contDiff_const hb' hEb'
  have hae : ∀ᵐ x : Coord, 0 < x.1 → g_cl x = kOutChart p b' Qb' Eb' x := by
    filter_upwards [hQae, hEae] with x hQx hEx hpos
    unfold g_cl kOutChart
    rw [hQx hpos, hEx hpos]
  exact driftNvCCongr_proof chartNullPullback p.c p.ε g_cl (kOutChart p b' Qb' Eb') Φ
    p.c_pos p.ε_pos hae

end UnforcedLeray.Short.IIb.PhysKOutCandHelp
