import UnforcedLeray.Short.PartIIb.Tasks.WindowComparison.TransverseTail.Leaves
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T20
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.ProfileUnique.WindowZero
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivVanish.FundWindow
import UnforcedLeray.Short.PartIIb.Tasks.StrongLateCoeff.NvFderiv
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletB.RawDiff

/-!
# Chart Identification of the Physical Interaction Output (`KOutChartAe`, helper for `PartII-b:G2/2`)

Source of record: `the November 2 reference manuscript`
(SP), lines 2007–2012 (`K_ε = s B_ε T_ε`, "Exact chart substitution"), 1658–1660 (chart divergence),
and 2434–2445 (young and late physical interaction bounds).

Proves `kOutChartAe : UnforcedLeray.Short.IIb.KOutChartAe`:
1. Smoothness and `p.c`-periodicity in `q` of `rawProf p`, `qEps p.ε (rawProf p)`,
   `Axi.dEta (rawProf p)`, and `chartDivR p.ε (rawProf p)` on `U0 = {s > 0}`.
2. Off-axis pointwise identities for `dotL (gradUT p.raw Φ_j (τ, y)) (NvC p.R b (τ, y))` and
   `dotL (advT (realC ∘ p.raw) Φ_j (τ, y)) (NvC p.R b (τ, y))` when `Φ_j` is the phase test of a
   window test `χ` (`windowPhaseVec`).
3. Pullback of `pairF p.period (convT p.raw Φ_j) (NvC p.R b)` to the chart via
   `periodicRepresentative`, `ringBridgeC`, `chartNullPullback`, and local agreement
   `winPer p.c χ =ᶠ[𝓝 x] χ` on the cell `Ioi 0 ×ˢ Axi.qCell p.c`.
4. Coordinate integration by parts (`HasWeakVec`) against the test functions
   `ψ_i(x) = x.1⁻¹ * rawProf p x i * χ x`, matching `wInt χ (√s • (kOutChart p b Qb Eb)_j)`,
   followed by `fundWindow_proof`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Real
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.PhysKopYLKOut

open UnforcedLeray.Short.IIb
open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-! ## Section 1: Open half-space `U0 = {s > 0}`, smoothness and `q`-periodicity of `rawProf` -/

private abbrev U0 : Set Coord := Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))

private theorem isOpen_U0 : IsOpen U0 := isOpen_Ioi.prod isOpen_univ

private theorem mem_U0_iff {x : Coord} : x ∈ U0 ↔ 0 < x.1 := by
  simp [U0]

private theorem fderiv_apply_cd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Coord → E} (hG : ContDiffOn ℝ ∞ G U0) (v : Coord) :
    ContDiffOn ℝ ∞ (fun x => fderiv ℝ G x v) U0 :=
  (hG.fderiv_of_isOpen isOpen_U0 (m := ∞) (by simp)).clm_apply contDiffOn_const

private theorem dS_cd {G : Coord → Axi.Merid} (hG : ContDiffOn ℝ ∞ G U0) :
    ContDiffOn ℝ ∞ (Axi.dS G) U0 :=
  fderiv_apply_cd hG (1, (0, 0))

private theorem dQ_cd {G : Coord → Axi.Merid} (hG : ContDiffOn ℝ ∞ G U0) :
    ContDiffOn ℝ ∞ (Axi.dQ G) U0 :=
  fderiv_apply_cd hG (0, (1, 0))

private theorem dEta_cd {G : Coord → Axi.Merid} (hG : ContDiffOn ℝ ∞ G U0) :
    ContDiffOn ℝ ∞ (Axi.dEta G) U0 :=
  fderiv_apply_cd hG (0, (0, 1))

private theorem kAge_cd {G : Coord → Axi.Merid} (hG : ContDiffOn ℝ ∞ G U0) :
    ContDiffOn ℝ ∞ (kAge G) U0 := by
  have h1 : ContDiffOn ℝ ∞ (fun x : Coord => 2 * x.1) U0 :=
    (contDiff_const.mul contDiff_fst).contDiffOn
  have h2 : ContDiffOn ℝ ∞ (fun x : Coord => x.2.2) U0 :=
    (contDiff_snd.comp contDiff_snd).contDiffOn
  unfold kAge
  exact (h1.smul (dS_cd hG)).add (h2.smul (dEta_cd hG))

private theorem qEps_cd {ε : ℝ} {G : Coord → Axi.Merid} (hG : ContDiffOn ℝ ∞ G U0) :
    ContDiffOn ℝ ∞ (qEps ε G) U0 := by
  unfold qEps
  exact (dQ_cd hG).sub ((contDiffOn_const (c := ε)).smul ((kAge_cd hG).add hG))

private theorem merid_coord_cd {G : Coord → Axi.Merid} (hG : ContDiffOn ℝ ∞ G U0) (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => G x j) U0 :=
  (EuclideanSpace.proj j : Axi.Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hG

private theorem chartDivR_cd {ε : ℝ} {G : Coord → Axi.Merid} (hG : ContDiffOn ℝ ∞ G U0) :
    ContDiffOn ℝ ∞ (chartDivR ε G) U0 := by
  unfold chartDivR
  exact ((merid_coord_cd (qEps_cd hG) 0).add
    (contDiffOn_const.mul (merid_coord_cd hG 0))).add (merid_coord_cd (dEta_cd hG) 1)

private theorem deriv_eta_eq_fderiv (Ψ : Coord → ℝ) (x : Coord) (hΨ : DifferentiableAt ℝ Ψ x) :
    deriv (fun t => Ψ (x.1, (x.2.1, t))) x.2.2 = fderiv ℝ Ψ x (0, (0, 1)) := by
  have hline : HasDerivAt (fun t : ℝ => ((x.1, (x.2.1, t)) : Coord)) (0, (0, 1)) x.2.2 :=
    (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_id _))
  exact (hΨ.hasFDerivAt.comp_hasDerivAt x.2.2 hline).deriv

private theorem deriv_s_eq_fderiv (Ψ : Coord → ℝ) (x : Coord) (hΨ : DifferentiableAt ℝ Ψ x) :
    deriv (fun t => Ψ (t, (x.2.1, x.2.2))) x.1 = fderiv ℝ Ψ x (1, (0, 0)) := by
  have hline : HasDerivAt (fun t : ℝ => ((t, (x.2.1, x.2.2)) : Coord)) (1, (0, 0)) x.1 :=
    (hasDerivAt_id _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_const _ _))
  exact (hΨ.hasFDerivAt.comp_hasDerivAt x.1 hline).deriv

private theorem rawProf_cd {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp) :
    ContDiffOn ℝ ∞ (rawProf p) U0 := by
  have hv : ContDiffOn ℝ ∞ (fun x : Coord => p.train.v x.1 x.2) U0 :=
    p.train.isTrain.smooth_v.mono (fun x (hx : x ∈ U0) =>
      ⟨show (0 : ℝ) ≤ x.1 from le_of_lt hx.1, trivial⟩)
  have hΨ : ContDiffOn ℝ ∞ (fun x : Coord => p.train.ψ x.1 x.2) U0 := hreg.train_stream_smooth
  have hΨd : ∀ x ∈ U0, DifferentiableAt ℝ (fun x : Coord => p.train.ψ x.1 x.2) x :=
    fun x hx => (hΨ.differentiableOn (by simp)).differentiableAt (isOpen_U0.mem_nhds hx)
  have hD1 : ContDiffOn ℝ ∞
      (fun x : Coord => deriv (fun t => p.train.ψ x.1 (x.2.1, t)) x.2.2) U0 :=
    (fderiv_apply_cd hΨ (0, (0, 1))).congr (fun x hx =>
      deriv_eta_eq_fderiv (fun z => p.train.ψ z.1 z.2) x (hΨd x hx))
  have hD2 : ContDiffOn ℝ ∞
      (fun x : Coord => deriv (fun t => p.train.ψ t (x.2.1, x.2.2)) x.1) U0 :=
    (fderiv_apply_cd hΨ (1, (0, 0))).congr (fun x hx =>
      deriv_s_eq_fderiv (fun z => p.train.ψ z.1 z.2) x (hΨd x hx))
  have hη : ContDiffOn ℝ ∞ (fun x : Coord => x.2.2) U0 :=
    (contDiff_snd.comp contDiff_snd).contDiffOn
  have hs2 : ContDiffOn ℝ ∞ (fun x : Coord => 2 * x.1) U0 :=
    (contDiff_const.mul contDiff_fst).contDiffOn
  have hRS : ContDiffOn ℝ ∞
      (fun x : Coord => UnforcedLeray.Cons.C03.raisedStream p.train.ψ x.1 x.2.1 x.2.2) U0 := by
    unfold UnforcedLeray.Cons.C03.raisedStream
    exact (hΨ.sub ((hη.mul hD1).add (hs2.mul hD2))).congr (fun _ _ => rfl)
  unfold rawProf UnforcedLeray.Cons.C03.rawProfile
  exact hv.add (((contDiffOn_const (c := p.ε)).mul hRS).smul
    (contDiffOn_const (c := EuclideanSpace.single (1 : Fin 2) (1 : ℝ))))

private theorem sInv_cd : ContDiffOn ℝ ∞ (fun x : Coord => x.1⁻¹) U0 :=
  contDiff_fst.contDiffOn.inv (fun _ hx => (mem_U0_iff.mp hx).ne')

private theorem qShift_eq_add (c : ℝ) (x : Coord) : qShift c x = x + (0, (c, 0)) := by
  simp [qShift, Prod.ext_iff]

private theorem qPer_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Coord → E} {c : ℝ} {U : Set Coord} (hU : IsOpen U)
    (hF : ∀ y ∈ U, F (qShift c y) = F y) {x : Coord} (hx : x ∈ U) :
    fderiv ℝ F (qShift c x) = fderiv ℝ F x := by
  have hev : (fun y => F (qShift c y)) =ᶠ[𝓝 x] F := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hF y hy
  have hfun : (fun y => F (qShift c y)) = fun y => F (y + (0, (c, 0))) := by
    funext y
    rw [qShift_eq_add]
  have h1 : fderiv ℝ (fun y => F (qShift c y)) x = fderiv ℝ F x := hev.fderiv_eq
  rw [hfun, fderiv_comp_add_right] at h1
  rw [qShift_eq_add]
  exact h1

private theorem rawProf_qPer (p : Params) {x : Coord} (hx : x ∈ U0) :
    rawProf p (qShift p.c x) = rawProf p x := by
  unfold rawProf
  exact UnforcedLeray.Cons.C03.rawProfile_periodic p.train (mem_U0_iff.mp hx) x.2.1 x.2.2

private theorem dEta_rawProf_qPer (p : Params) {x : Coord} (hx : x ∈ U0) :
    Axi.dEta (rawProf p) (qShift p.c x) = Axi.dEta (rawProf p) x := by
  unfold Axi.dEta
  rw [qPer_fderiv isOpen_U0 (fun _ hy => rawProf_qPer p hy) hx]

private theorem qEps_rawProf_qPer (p : Params) {x : Coord} (hx : x ∈ U0) :
    qEps p.ε (rawProf p) (qShift p.c x) = qEps p.ε (rawProf p) x := by
  have hf := qPer_fderiv isOpen_U0 (fun _ hy => rawProf_qPer p hy) hx
  unfold qEps kAge Axi.dQ Axi.dS Axi.dEta
  rw [hf, rawProf_qPer p hx]
  rfl

/-! ## Section 2: Off-axis pointwise identities for `gradUT` and `advT` -/

private theorem eRD_eR {y : Space} (hy : y ∉ Axi.axis) : Axi.eRD y (Axi.eR y) = 0 := by
  ext k
  rw [Axi.eRD_apply_coord, Axi.ϱD_eR hy]
  fin_cases k
  · simp [Axi.hor, Axi.eR_apply_zero]
  · simp [Axi.hor, Axi.eR_apply_one]
  · simp [Axi.hor]

private theorem eRD_e3 (y : Space) : Axi.eRD y Axi.e3 = 0 := by
  rw [Axi.eRD_apply, Axi.ϱD_e3]
  ext k
  fin_cases k <;> simp [Axi.hor, Axi.e3]

private theorem dotL_gradUT_realC {f : Space → Space} {L : Space →L[ℝ] Space} {y : Space}
    (hf : fderiv ℝ f y = L) (Φv : CVec3) (z : ℂ) (v : Space) :
    dotL (WithLp.toLp 2 fun k : Fin 3 =>
        ∑ i : Fin 3, Φv i * ((fderiv ℝ f y (EuclideanSpace.single k 1) i : ℝ) : ℂ))
      (z • realC v) =
      z * dotL Φv (realC (L v)) := by
  have hv_decomp : v = ∑ k : Fin 3, v k • (EuclideanSpace.single k (1 : ℝ) : Space) := by
    ext i
    fin_cases i <;> simp [Fin.sum_univ_three]
  have hLv : L v = ∑ k : Fin 3, v k • L (EuclideanSpace.single k 1) := by
    conv_lhs => rw [hv_decomp]
    rw [map_sum]
    simp [map_smul]
  rw [hf, hLv]
  simp only [dotL_apply, Fin.sum_univ_three, PiLp.smul_apply, PiLp.add_apply,
    realC_apply, smul_eq_mul]
  push_cast
  ring

private theorem nvC_split (R : ℝ) (b : CProf) (τ : ℝ) (y : Space) :
    NvC R b (τ, y) =
      (((Real.sqrt (Axi.age R y) : ℝ) : ℂ) * b (Axi.chart R τ y) 0) • realC (Axi.eR y) +
        (((Real.sqrt (Axi.age R y) : ℝ) : ℂ) * b (Axi.chart R τ y) 1) • realC Axi.e3 := by
  rw [DriftOff.nvC_rep]
  ext i
  simp [DriftOff.realCL_apply, realC_apply, Complex.real_smul]
  ring

private theorem dotL_ej_frameL (G : ℂ) (j : Fin 2) {y : Space} (hy : y ∉ Axi.axis)
    (s : ℝ) (m : Axi.Merid) :
    dotL (G • realC (WindowZeroHelp.ej j y)) (realC (s • Axi.frameL y m)) =
      G * ((s * m j : ℝ) : ℂ) := by
  rw [Axi.frameL_apply]
  have hsq := Axi.eR_sq_sum hy
  fin_cases j
  · simp [WindowZeroHelp.ej, dotL_apply, Fin.sum_univ_three, realC_apply,
      Axi.eR_apply_zero, Axi.eR_apply_one, Axi.eR_apply_two]
    have h2 := congrArg (fun r : ℝ => (r : ℂ)) hsq
    push_cast at h2
    left
    linear_combination ((s : ℂ) * (m 0 : ℂ)) * h2
  · simp [WindowZeroHelp.ej, dotL_apply, Fin.sum_univ_three, realC_apply,
      Axi.eR_apply_zero, Axi.eR_apply_one, Axi.eR_apply_two]

private theorem nvQ_eq_qEps (p : Params) (x : Coord) :
    nvQ p.R⁻¹ (rawProf p) x = qEps p.ε (rawProf p) x := by
  have hRinv : p.R⁻¹ = p.ε := inv_inv p.ε
  unfold nvQ qEps kAge
  rw [hRinv]

private theorem gradUT_dot_offAxis {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp)
    (W : Coord → ℝ) (b : CProf) (j : Fin 2) (Φ : ℝ × Space → CVec3) (τ : ℝ) {y : Space}
    (hy : y ∉ Axi.axis)
    (hΦy : Φ (τ, y) = ((W (Axi.chart p.R τ y) : ℝ) : ℂ) • realC (WindowZeroHelp.ej j y)) :
    dotL (gradUT p.raw Φ (τ, y)) (NvC p.R b (τ, y)) =
      ((W (Axi.chart p.R τ y) : ℝ) : ℂ) *
        (((Real.sqrt (Axi.chart p.R τ y).1 * (Axi.chart p.R τ y).1 : ℝ) : ℂ) *
          (b (Axi.chart p.R τ y) 0 *
              ((qEps p.ε (rawProf p) (Axi.chart p.R τ y) j : ℝ) : ℂ) +
            b (Axi.chart p.R τ y) 1 *
              ((Axi.dEta (rawProf p) (Axi.chart p.R τ y) j : ℝ) : ℂ))) := by
  set x := Axi.chart p.R τ y
  have hs : 0 < x.1 := Axi.age_pos p.R_pos.ne' hy
  have hev : p.raw τ =ᶠ[𝓝 y] Axi.Nv p.R (rawProf p) τ := by
    filter_upwards [Axi.isClosed_axis.isOpen_compl.mem_nhds hy] with z hz
    exact p.raw_eq_off_axis τ z hz
  have hdiff := rawProfDiffAt dm dp p d hreg x hs
  have hfderiv : fderiv ℝ (p.raw τ) y = nvL p.R τ (rawProf p) y := by
    rw [hev.fderiv_eq, (nvFderiv_hasFDerivAt p.R_pos hy hdiff).fderiv]
  have hL_eR : nvL p.R τ (rawProf p) y (Axi.eR y) =
      x.1 • Axi.frameL y (qEps p.ε (rawProf p) x) := by
    rw [nvL_apply, Axi.ϱD_eR hy, Axi.eR_apply_two, eRD_eR hy, nvQ_eq_qEps]
    simp [x, Axi.chart]
  have hL_e3 : nvL p.R τ (rawProf p) y Axi.e3 =
      x.1 • Axi.frameL y (Axi.dEta (rawProf p) x) := by
    rw [nvL_apply, Axi.ϱD_e3, Axi.e3_two, eRD_e3]
    simp [x, Axi.chart]
  unfold gradUT
  rw [nvC_split p.R b τ y, (dotL _).map_add,
    dotL_gradUT_realC hfderiv (Φ (τ, y)) _ (Axi.eR y),
    dotL_gradUT_realC hfderiv (Φ (τ, y)) _ Axi.e3,
    hΦy, hL_eR, hL_e3,
    dotL_ej_frameL _ j hy x.1 (qEps p.ε (rawProf p) x),
    dotL_ej_frameL _ j hy x.1 (Axi.dEta (rawProf p) x)]
  have hage : Axi.age p.R y = x.1 := rfl
  rw [hage]
  push_cast
  ring

private theorem advT_real_eq_slice_fderiv (u : ℝ × Space → Space) {Φ : ℝ × Space → CVec3}
    (τ : ℝ) (y : Space) (hΦ : DifferentiableAt ℝ Φ (τ, y)) :
    advT (fun q => realC (u q)) Φ (τ, y) =
      fderiv ℝ (fun z : Space => Φ (τ, z)) y (u (τ, y)) := by
  have hslice : HasFDerivAt (fun z : Space => Φ (τ, z))
      ((fderiv ℝ Φ (τ, y)).comp ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space))) y :=
    hΦ.hasFDerivAt.comp y ((hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y))
  have hdy : ∀ k : Fin 3, dy k Φ (τ, y) =
      fderiv ℝ (fun z : Space => Φ (τ, z)) y (coordinateVector k) := by
    intro k
    unfold dy
    rw [hslice.fderiv]
    rfl
  have hsmul : ∀ (r : ℝ) (w : CVec3), (r : ℂ) • w = r • w := by
    intro r w
    ext i
    simp [Complex.real_smul]
  have hv : u (τ, y) = ∑ k : Fin 3, u (τ, y) k • coordinateVector k := by
    ext i
    simp [coordinateVector, Pi.single_apply]
  unfold advT
  simp only [realC_apply, hsmul, hdy]
  conv_rhs => rw [hv]
  rw [map_sum]
  simp [map_smul]

private theorem fderiv_chart_comp_raw (p : Params) {W : Coord → ℝ} (hW : ContDiff ℝ ∞ W)
    (τ : ℝ) {y : Space} (hy : y ∉ Axi.axis) :
    fderiv ℝ (fun z : Space => W (Axi.chart p.R τ z)) y (p.raw τ y) =
      (Axi.chart p.R τ y).1 *
        (rawProf p (Axi.chart p.R τ y) 0 *
            (∑ k : Fin 3, vQ p.ε (Axi.chart p.R τ y) k * cpd k W (Axi.chart p.R τ y)) +
          rawProf p (Axi.chart p.R τ y) 1 * cpd 2 W (Axi.chart p.R τ y)) := by
  set x := Axi.chart p.R τ y
  have hs : 0 < Axi.age p.R y := Axi.age_pos p.R_pos.ne' hy
  have hWd : DifferentiableAt ℝ W x := (hW.differentiable (by simp)) x
  have hraw : p.raw τ y =
      Real.sqrt (Axi.age p.R y) •
        (rawProf p x 0 • Axi.eR y + rawProf p x 1 • Axi.e3) := by
    have hR_def : p.ε⁻¹ = p.R := rfl
    have hprof_def : UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ = rawProf p := rfl
    rw [p.raw_eq_off_axis τ y hy, hR_def, hprof_def]
    simp [Axi.Nv, Axi.frameL_apply, x]
  rw [hraw, map_smul, map_add, map_smul, map_smul,
    Axi.radial_chain p.R_pos hy hWd, Axi.axial_chain p.R_pos hy hWd]
  have hsq : Real.sqrt (Axi.age p.R y) * Real.sqrt (Axi.age p.R y) = x.1 :=
    Real.mul_self_sqrt hs.le
  have hRinv : p.R⁻¹ = p.ε := inv_inv p.ε
  have hcpd0 : Axi.dS W x = cpd 0 W x := rfl
  have hcpd1 : Axi.dQ W x = cpd 1 W x := rfl
  have hcpd2 : Axi.dEta W x = cpd 2 W x := rfl
  have hage : Axi.age p.R y = x.1 := rfl
  have htrans : Axi.trans p.R y = x.2.2 := rfl
  have hvQ_sum : ∑ k : Fin 3, vQ p.ε x k * cpd k W x =
      -2 * p.ε * x.1 * cpd 0 W x + 1 * cpd 1 W x + -p.ε * x.2.2 * cpd 2 W x := by
    rw [Fin.sum_univ_three]
    rfl
  simp only [smul_eq_mul, hRinv]
  rw [hcpd0, hcpd1, hcpd2, htrans, hvQ_sum]
  calc Real.sqrt (Axi.age p.R y) *
        (rawProf p x 0 * (Real.sqrt (Axi.age p.R y) *
            (cpd 1 W x - p.ε * (2 * Axi.age p.R y * cpd 0 W x + x.2.2 * cpd 2 W x))) +
          rawProf p x 1 * (Real.sqrt (Axi.age p.R y) * cpd 2 W x))
      = (Real.sqrt (Axi.age p.R y) * Real.sqrt (Axi.age p.R y)) *
          (rawProf p x 0 * (cpd 1 W x - p.ε * (2 * x.1 * cpd 0 W x + x.2.2 * cpd 2 W x)) +
            rawProf p x 1 * cpd 2 W x) := by rw [hage]; ring
    _ = x.1 * (rawProf p x 0 * (-2 * p.ε * x.1 * cpd 0 W x + 1 * cpd 1 W x +
            -p.ε * x.2.2 * cpd 2 W x) + rawProf p x 1 * cpd 2 W x) := by
          rw [hsq]; ring

private theorem advT_dot_offAxis (p : Params) {W : Coord → ℝ} (hW : ContDiff ℝ ∞ W)
    (b : CProf) (j : Fin 2) {Φ : ℝ × Space → CVec3} (hΦs : ContDiff ℝ ∞ Φ)
    (hΦe : ∀ (t : ℝ) (z : Space), z ∉ Axi.axis →
      Φ (t, z) = ((W (Axi.chart p.R t z) : ℝ) : ℂ) • realC (WindowZeroHelp.ej j z))
    (τ : ℝ) {y : Space} (hy : y ∉ Axi.axis) :
    dotL (advT (fun q => realC (p.raw q.1 q.2)) Φ (τ, y)) (NvC p.R b (τ, y)) =
      (((Axi.chart p.R τ y).1 *
          (rawProf p (Axi.chart p.R τ y) 0 *
              (∑ k : Fin 3, vQ p.ε (Axi.chart p.R τ y) k * cpd k W (Axi.chart p.R τ y)) +
            rawProf p (Axi.chart p.R τ y) 1 * cpd 2 W (Axi.chart p.R τ y)) : ℝ) : ℂ) *
        (((Real.sqrt (Axi.chart p.R τ y).1 : ℝ) : ℂ) * b (Axi.chart p.R τ y) j) := by
  have hΦd : DifferentiableAt ℝ Φ (τ, y) := (hΦs.differentiable (by simp)) (τ, y)
  rw [advT_real_eq_slice_fderiv (fun q => p.raw q.1 q.2) τ y hΦd]
  have hev : (fun z : Space => Φ (τ, z)) =ᶠ[𝓝 y]
      fun z : Space => W (Axi.chart p.R τ z) • DriftOff.realCL (WindowZeroHelp.ej j z) := by
    filter_upwards [Axi.isClosed_axis.isOpen_compl.mem_nhds hy] with z hz
    rw [hΦe τ z hz]
    ext i
    simp [DriftOff.realCL_apply, Complex.real_smul]
  obtain ⟨Dj, hDj, hDj_eR, hDj_e3⟩ :
      ∃ Dj : Space →L[ℝ] Space, HasFDerivAt (WindowZeroHelp.ej j) Dj y ∧
        Dj (Axi.eR y) = 0 ∧ Dj Axi.e3 = 0 := by
    fin_cases j
    · refine ⟨Axi.eRD y, ?_, eRD_eR hy, eRD_e3 y⟩
      show HasFDerivAt (if (0 : Fin 2) = 0 then Axi.eR else fun _ => Axi.e3) _ y
      simp only [↓reduceIte]
      exact Axi.hasFDerivAt_eR hy
    · refine ⟨0, ?_, by simp, by simp⟩
      show HasFDerivAt (if (1 : Fin 2) = 0 then Axi.eR else fun _ => Axi.e3) _ y
      have h10 : (1 : Fin 2) ≠ 0 := by decide
      simp only [h10, ↓reduceIte]
      exact hasFDerivAt_const _ _
  have hWcomp : DifferentiableAt ℝ (fun z : Space => W (Axi.chart p.R τ z)) y :=
    ((hW.differentiable (by simp)) (Axi.chart p.R τ y)).comp y
      (Axi.hasFDerivAt_chart p.R_pos.ne' τ hy).differentiableAt
  have hEj : HasFDerivAt (fun z : Space => DriftOff.realCL (WindowZeroHelp.ej j z))
      (DriftOff.realCL.comp Dj) y :=
    DriftOff.realCL.hasFDerivAt.comp y hDj
  have hprod : HasFDerivAt
      (fun z : Space => W (Axi.chart p.R τ z) • DriftOff.realCL (WindowZeroHelp.ej j z)) _ y :=
    hWcomp.hasFDerivAt.smul hEj
  have hDj_raw : Dj (p.raw τ y) = 0 := by
    rw [p.raw_eq_off_axis τ y hy]
    simp [Axi.Nv, Axi.frameL_apply, map_smul, map_add, hDj_eR, hDj_e3]
  have hf : fderiv ℝ (fun z : Space => Φ (τ, z)) y (p.raw τ y) =
      ((fderiv ℝ (fun z : Space => W (Axi.chart p.R τ z)) y (p.raw τ y) : ℝ) : ℂ) •
        realC (WindowZeroHelp.ej j y) := by
    rw [hev.fderiv_eq, hprod.fderiv]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, ContinuousLinearMap.comp_apply, hDj_raw, map_zero,
      smul_zero]
    ext i
    simp [DriftOff.realCL_apply, Complex.real_smul]
  rw [hf, fderiv_chart_comp_raw p hW τ hy,
    WindowZeroHelp2.dot_ej _ j b p.R τ hy]
  rfl

/-! ## Section 3: Local cell agreement of `winPer` and coordinate test algebra -/

private theorem winPer_eventuallyEq_on_cell {c : ℝ} (hc : 0 < c) {χ : Coord → ℝ}
    (hχ : IsWinTest c χ) {x : Coord} (hx : x ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c) :
    winPer c χ =ᶠ[𝓝 x] χ := by
  have hq : -c / 2 ≤ x.2.1 ∧ x.2.1 < c / 2 := hx.2.1
  rcases eq_or_lt_of_le hq.1 with hleft | hgt
  · obtain ⟨μ, hμ, hmar⟩ := ChartWinHelp.margin_of hc hχ
    have hcont : Continuous fun z : Coord => |z.2.1 - (-c / 2)| := by fun_prop
    have hev : ∀ᶠ z in 𝓝 x, |z.2.1 - (-c / 2)| < μ := by
      refine hcont.continuousAt.eventually_lt continuousAt_const ?_
      rw [← hleft, sub_self, abs_zero]
      exact hμ
    filter_upwards [hev] with z hz
    obtain ⟨hz1, hz2⟩ := abs_lt.mp hz
    have hχz : χ z = 0 := by
      apply hmar
      have hneg : c / 2 - μ < -z.2.1 := by linarith
      exact le_trans hneg.le (neg_le_abs z.2.1)
    have hWz : winPer c χ z = 0 := by
      unfold winPer
      apply hmar
      set m : ℤ := ⌊z.2.1 / c + 1 / 2⌋
      rcases le_or_gt 0 m with hm | hm
      · have hmR : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have hcm : 0 ≤ c * (m : ℝ) := mul_nonneg hc.le hmR
        have hneg : c / 2 - μ < -(z.2.1 - c * (m : ℝ)) := by linarith
        exact le_trans hneg.le (neg_le_abs _)
      · have hm1 : m ≤ -1 := Int.le_sub_one_of_lt hm
        have hmR : (m : ℝ) ≤ -1 := by exact_mod_cast hm1
        have hcm : c * (m : ℝ) ≤ -c := by nlinarith
        have hpos : c / 2 - μ < z.2.1 - c * (m : ℝ) := by linarith
        exact le_trans hpos.le (le_abs_self _)
    rw [hWz, hχz]
  · have hopen : IsOpen {z : Coord | -c / 2 < z.2.1 ∧ z.2.1 < c / 2} :=
      (isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).inter
        (isOpen_lt (continuous_fst.comp continuous_snd) continuous_const)
    filter_upwards [hopen.mem_nhds ⟨hgt, hq.2⟩] with z hz
    exact (winPerFacts c χ hc hχ).2.2 z ⟨hz.1.le, hz.2⟩

private theorem winPer_eq_and_cpd_on_cell {c : ℝ} (hc : 0 < c) {χ : Coord → ℝ}
    (hχ : IsWinTest c χ) {x : Coord} (hx : x ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c) :
    winPer c χ x = χ x ∧ ∀ k : Fin 3, cpd k (winPer c χ) x = cpd k χ x := by
  have hev := winPer_eventuallyEq_on_cell hc hχ hx
  refine ⟨hev.eq_of_nhds, fun k => ?_⟩
  unfold cpd
  rw [hev.fderiv_eq]

private theorem isCoordTest_mul_U0 {ψ φ : Coord → ℝ} (hψ : ContDiffOn ℝ ∞ ψ U0)
    (hφ : IsCoordTest φ) :
    IsCoordTest (fun x => ψ x * φ x) := by
  refine ⟨?_, hφ.compact.mul_left, tsupport_mul_subset_right.trans hφ.supp⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport φ
  · exact (hψ.contDiffAt (isOpen_U0.mem_nhds (hφ.supp hx))).mul hφ.smooth.contDiffAt
  · have hev : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.mp hx
    refine (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Coord => (0 : ℝ)) x).congr_of_eventuallyEq ?_
    filter_upwards [hev] with y hy
    simp [hy]

private theorem tsupport_cpd_subset {φ : Coord → ℝ} (k : Fin 3) :
    tsupport (cpd k φ) ⊆ tsupport φ := by
  intro x hx
  by_contra hnot
  have hev : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.mp hnot
  have hev' : cpd k φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [((isClosed_tsupport φ).isOpen_compl).mem_nhds hnot] with y hy
    unfold cpd
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hy]
    simp
  exact (notMem_tsupport_iff_eventuallyEq.mpr hev') hx

private theorem isCoordTest_cpd {φ : Coord → ℝ} (hφ : IsCoordTest φ) (k : Fin 3) :
    IsCoordTest (cpd k φ) := by
  have hsub := tsupport_cpd_subset (φ := φ) k
  refine ⟨?_, ?_, hsub.trans hφ.supp⟩
  · unfold cpd
    exact (hφ.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  · exact HasCompactSupport.of_support_subset_isCompact hφ.compact
      ((subset_tsupport _).trans hsub)

private theorem isCoordTest_add {φ₁ φ₂ : Coord → ℝ} (h₁ : IsCoordTest φ₁) (h₂ : IsCoordTest φ₂) :
    IsCoordTest (fun x => φ₁ x + φ₂ x) :=
  ⟨h₁.smooth.add h₂.smooth, h₁.compact.add h₂.compact,
    (tsupport_add φ₁ φ₂).trans (union_subset h₁.supp h₂.supp)⟩

private theorem integrable_coordTest_mul_hr {c : ℝ} (hc : 0 < c) {b : CProf}
    (hb : InHr c bgp b) (i : Fin 2) {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    Integrable (fun x : Coord => (φ x : ℂ) * b x i) volume := by
  have hloc := profileLocInt c b hc hb i
  set K := tsupport φ
  have hKc : IsCompact K := hφ.compact
  have hKsub : K ⊆ U0 := hφ.supp
  have h1 : IntegrableOn (fun x : Coord => ((Real.sqrt x.1 : ℝ) : ℂ) * b x i) K volume :=
    hloc.integrableOn_compact_subset hKsub hKc
  have hcont : ContinuousOn (fun x : Coord => ((φ x / Real.sqrt x.1 : ℝ) : ℂ)) K := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    refine hφ.smooth.continuous.continuousOn.div
      (Real.continuous_sqrt.comp continuous_fst).continuousOn ?_
    intro x hx
    exact (Real.sqrt_pos.mpr (mem_U0_iff.mp (hKsub hx))).ne'
  have h2 : IntegrableOn (fun x : Coord => (φ x : ℂ) * b x i) K volume :=
    (h1.continuousOn_mul hcont hKc).congr_fun
      (fun x hx => by
        have hs : (Real.sqrt x.1 : ℂ) ≠ 0 := by
          exact_mod_cast (Real.sqrt_pos.mpr (mem_U0_iff.mp (hKsub hx))).ne'
        push_cast
        field_simp [hs])
      hKc.measurableSet
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 h2
  intro x hx
  by_contra hxK
  apply hx
  have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hxK
  simp [h0]

/-! ## Section 4: Smooth age-cutoff extension for measurable `q`-periodic lift -/

private def sCutoff (a : ℝ) (x : Coord) : ℝ :=
  Real.smoothTransition (2 * x.1 / a - 1)

private theorem sCutoff_eq_zero {a : ℝ} (ha : 0 < a) {x : Coord} (hx : x.1 ≤ a / 2) :
    sCutoff a x = 0 := by
  unfold sCutoff
  apply Real.smoothTransition.zero_of_nonpos
  have : 2 * x.1 / a ≤ 1 := by
    rw [div_le_one ha]
    linarith
  linarith

private theorem sCutoff_eq_one {a : ℝ} (ha : 0 < a) {x : Coord} (hx : a ≤ x.1) :
    sCutoff a x = 1 := by
  unfold sCutoff
  apply Real.smoothTransition.one_of_one_le
  have : 2 ≤ 2 * x.1 / a := by
    rw [le_div_iff₀ ha]
    linarith
  linarith

private theorem sCutoff_mul_contDiff {a : ℝ} (ha : 0 < a) {f : Coord → ℝ}
    (hf : ContDiffOn ℝ ∞ f U0) :
    ContDiff ℝ ∞ (fun x => sCutoff a x * f x) := by
  have hθ : ContDiff ℝ ∞ (sCutoff a) := by
    unfold sCutoff
    exact Real.smoothTransition.contDiff.comp
      (((contDiff_const.mul contDiff_fst).div_const a).sub contDiff_const)
  rw [contDiff_iff_contDiffAt]
  intro x0
  by_cases hx0 : 0 < x0.1
  · exact hθ.contDiffAt.mul (hf.contDiffAt (isOpen_U0.mem_nhds ⟨hx0, trivial⟩))
  · have hopen : IsOpen {x : Coord | x.1 < a / 2} := isOpen_lt continuous_fst continuous_const
    have hmem : x0 ∈ {x : Coord | x.1 < a / 2} := by
      show x0.1 < a / 2
      linarith
    have hev : (fun x => sCutoff a x * f x) =ᶠ[𝓝 x0] fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds hmem] with x hx
      rw [sCutoff_eq_zero ha (le_of_lt hx), zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

private theorem sCutoff_mul_qPer {a : ℝ} (c : ℝ) (ha : 0 < a) (f : Coord → ℝ)
    (hf : ∀ x ∈ U0, f (qShift c x) = f x) (s ξ η : ℝ) :
    sCutoff a (s, (ξ + c, η)) * f (s, (ξ + c, η)) = sCutoff a (s, (ξ, η)) * f (s, (ξ, η)) := by
  by_cases hs : 0 < s
  · have hθ : sCutoff a (s, (ξ + c, η)) = sCutoff a (s, (ξ, η)) := rfl
    have hfx : f (s, (ξ + c, η)) = f (s, (ξ, η)) := hf (s, (ξ, η)) ⟨hs, trivial⟩
    rw [hθ, hfx]
  · have hsle : s ≤ a / 2 := by linarith
    rw [sCutoff_eq_zero ha hsle, sCutoff_eq_zero ha hsle, zero_mul, zero_mul]

private theorem winPer_and_cpd_zero_below (c : ℝ) {χ : Coord → ℝ} {a b_hi : ℝ}
    (hab : ∀ y : Coord, χ y ≠ 0 → a ≤ y.1 ∧ y.1 ≤ b_hi) {x : Coord} (hx : x.1 < a) :
    winPer c χ x = 0 ∧ ∀ k : Fin 3, cpd k (winPer c χ) x = 0 := by
  have hopen : IsOpen {z : Coord | z.1 < a} := isOpen_lt continuous_fst continuous_const
  have hev : winPer c χ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hx] with z hz
    exact ChartWinHelp.winPer_zero_of_s hab z (Or.inl hz)
  refine ⟨hev.eq_of_nhds, fun k => ?_⟩
  unfold cpd
  rw [hev.fderiv_eq]
  simp

/-! ## Section 5: Pullback of `pairF p.period (convT p.raw Φ_j) (NvC p.R b)` to `Coord` -/

private def cellWeightConv (p : Params) (χ : Coord → ℝ) (b : CProf) (j : Fin 2) (x : Coord) : ℂ :=
  (((x.1⁻¹ * qEps p.ε (rawProf p) x j * χ x : ℝ) : ℂ) * b x 0 +
      ((x.1⁻¹ * Axi.dEta (rawProf p) x j * χ x : ℝ) : ℂ) * b x 1) -
    (((x.1⁻¹ * (rawProf p x 0 * (∑ k : Fin 3, vQ p.ε x k * cpd k χ x) +
          rawProf p x 1 * cpd 2 χ x) : ℝ) : ℂ) * b x j)

private theorem vQ_cd (ε : ℝ) (k : Fin 3) : ContDiff ℝ ∞ (fun x : Coord => vQ ε x k) := by
  fin_cases k
  · change ContDiff ℝ ∞ (fun x : Coord => -2 * ε * x.1)
    fun_prop
  · change ContDiff ℝ ∞ (fun _ : Coord => (1 : ℝ))
    fun_prop
  · change ContDiff ℝ ∞ (fun x : Coord => -ε * x.2.2)
    exact contDiff_const.mul (contDiff_snd.comp contDiff_snd)

private theorem vEta_cd (k : Fin 3) : ContDiff ℝ ∞ (fun x : Coord => vEta x k) := by
  fin_cases k
  · change ContDiff ℝ ∞ (fun _ : Coord => (0 : ℝ)); fun_prop
  · change ContDiff ℝ ∞ (fun _ : Coord => (0 : ℝ)); fun_prop
  · change ContDiff ℝ ∞ (fun _ : Coord => (1 : ℝ)); fun_prop

private theorem cellWeightConv_integrable {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp)
    {χ : Coord → ℝ} (hχ : IsWinTest p.c χ) {b : CProf} (hb : InHr p.c bgp b) (j : Fin 2) :
    Integrable (cellWeightConv p χ b j) volume := by
  have hu := rawProf_cd hreg
  have hφ0 : IsCoordTest (fun x => (x.1⁻¹ * qEps p.ε (rawProf p) x j) * χ x) :=
    isCoordTest_mul_U0 (sInv_cd.mul (merid_coord_cd (qEps_cd hu) j)) hχ.1
  have hφ1 : IsCoordTest (fun x => (x.1⁻¹ * Axi.dEta (rawProf p) x j) * χ x) :=
    isCoordTest_mul_U0 (sInv_cd.mul (merid_coord_cd (dEta_cd hu) j)) hχ.1
  have hadv_k : ∀ k : Fin 3,
      IsCoordTest (fun x => (x.1⁻¹ * rawProf p x 0 * vQ p.ε x k) * cpd k χ x) :=
    fun k => isCoordTest_mul_U0
      ((sInv_cd.mul (merid_coord_cd hu 0)).mul (vQ_cd p.ε k).contDiffOn)
      (isCoordTest_cpd hχ.1 k)
  have hadv_e : IsCoordTest (fun x => (x.1⁻¹ * rawProf p x 1) * cpd 2 χ x) :=
    isCoordTest_mul_U0 (sInv_cd.mul (merid_coord_cd hu 1)) (isCoordTest_cpd hχ.1 2)
  have hφadv : IsCoordTest (fun x =>
      x.1⁻¹ * (rawProf p x 0 * (∑ k : Fin 3, vQ p.ε x k * cpd k χ x) +
        rawProf p x 1 * cpd 2 χ x)) := by
    have hsum := isCoordTest_add (isCoordTest_add (isCoordTest_add (hadv_k 0) (hadv_k 1))
      (hadv_k 2)) hadv_e
    have heq : (fun x => x.1⁻¹ * (rawProf p x 0 * (∑ k : Fin 3, vQ p.ε x k * cpd k χ x) +
        rawProf p x 1 * cpd 2 χ x)) =
        fun x => ((x.1⁻¹ * rawProf p x 0 * vQ p.ε x 0) * cpd 0 χ x +
          (x.1⁻¹ * rawProf p x 0 * vQ p.ε x 1) * cpd 1 χ x +
          (x.1⁻¹ * rawProf p x 0 * vQ p.ε x 2) * cpd 2 χ x) +
          (x.1⁻¹ * rawProf p x 1) * cpd 2 χ x := by
      funext x
      rw [Fin.sum_univ_three]
      ring
    rwa [heq]
  unfold cellWeightConv
  exact ((integrable_coordTest_mul_hr p.c_pos hb 0 hφ0).add
    (integrable_coordTest_mul_hr p.c_pos hb 1 hφ1)).sub
    (integrable_coordTest_mul_hr p.c_pos hb j hφadv)

private theorem cellWeightConv_zero_off_cell (p : Params) {χ : Coord → ℝ} (hχ : IsWinTest p.c χ)
    (b : CProf) (j : Fin 2) {x : Coord} (hx : x ∉ Ioi (0 : ℝ) ×ˢ Axi.qCell p.c) :
    cellWeightConv p χ b j x = 0 := by
  have hxnot : x ∉ tsupport χ := by
    intro hmem
    apply hx
    have hs := (hχ.1.supp hmem).1
    obtain ⟨hq1, hq2⟩ := hχ.2 hmem
    exact ⟨hs, ⟨⟨hq1.le, hq2⟩, trivial⟩⟩
  have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport hxnot
  have hcpd0 : ∀ k : Fin 3, cpd k χ x = 0 := fun k =>
    image_eq_zero_of_notMem_tsupport fun h => hxnot (tsupport_cpd_subset k h)
  unfold cellWeightConv
  simp [hχ0, hcpd0]

private theorem rpow_neg_five_halves_mul_sqrt_mul {s : ℝ} (hs : 0 < s) :
    s ^ (-(5 / 2 : ℝ)) * (Real.sqrt s * s) = s⁻¹ := by
  calc s ^ (-(5 / 2 : ℝ)) * (Real.sqrt s * s)
      = s ^ (-(5 / 2 : ℝ)) * (s ^ (1 / 2 : ℝ) * s ^ (1 : ℝ)) := by
          rw [Real.sqrt_eq_rpow, Real.rpow_one]
    _ = s ^ (-(5 / 2 : ℝ) + (1 / 2 : ℝ) + (1 : ℝ)) := by
          rw [← Real.rpow_add hs, ← Real.rpow_add hs, add_assoc]
    _ = s ^ (-1 : ℝ) := by norm_num
    _ = s⁻¹ := Real.rpow_neg_one s

private theorem pairF_convT_eq_coord {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp)
    {χ : Coord → ℝ} (hχ : IsWinTest p.c χ) {b : CProf} (hb : InHr p.c bgp b) (j : Fin 2)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest p.period Φ)
    (hΦe : ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis →
      Φ (τ, y) = ((winPer p.c χ (Axi.chart p.R τ y) : ℝ) : ℂ) • realC (WindowZeroHelp.ej j y)) :
    pairF p.period (convT p.raw Φ) (NvC p.R b) =
      ((Real.pi * p.R ^ 2 / p.c : ℝ) : ℂ) * ∫ x : Coord, cellWeightConv p χ b j x := by
  set W := winPer p.c χ
  have hWcd : ContDiff ℝ ∞ W := ChartWinHelp.winPer_contDiff p.c_pos hχ
  have hWper : ∀ x : Coord, W (qShift p.c x) = W x := fun x =>
    ChartWinHelp.winPer_add_c p.c_pos χ x
  have hWcpd_cd : ∀ k : Fin 3, ContDiff ℝ ∞ (cpd k W) := fun k => by
    unfold cpd
    exact (hWcd.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hWcpd_per : ∀ (k : Fin 3) (x : Coord), cpd k W (qShift p.c x) = cpd k W x := by
    intro k x
    unfold cpd
    rw [qPer_fderiv isOpen_univ (fun z _ => hWper z) trivial]
  obtain ⟨a, ha, b_hi, _, _, hab⟩ := ChartWinHelp.supp_bounds hχ
  have hab' : ∀ y : Coord, χ y ≠ 0 → a ≤ y.1 ∧ y.1 ≤ b_hi :=
    fun y hy => ⟨(hab y hy).1, (hab y hy).2.1⟩
  have hu := rawProf_cd hreg
  set u0s : Coord → ℝ := fun x => sCutoff a x * rawProf p x 0
  set u1s : Coord → ℝ := fun x => sCutoff a x * rawProf p x 1
  set qjs : Coord → ℝ := fun x => sCutoff a x * qEps p.ε (rawProf p) x j
  set ejs : Coord → ℝ := fun x => sCutoff a x * Axi.dEta (rawProf p) x j
  have hu0s_m : Measurable u0s := (sCutoff_mul_contDiff ha (merid_coord_cd hu 0)).continuous.measurable
  have hu1s_m : Measurable u1s := (sCutoff_mul_contDiff ha (merid_coord_cd hu 1)).continuous.measurable
  have hqjs_m : Measurable qjs :=
    (sCutoff_mul_contDiff ha (merid_coord_cd (qEps_cd hu) j)).continuous.measurable
  have hejs_m : Measurable ejs :=
    (sCutoff_mul_contDiff ha (merid_coord_cd (dEta_cd hu) j)).continuous.measurable
  obtain ⟨b', M, hb'm, hb'per, hMm, hM0, hMper, hbb'⟩ :=
    periodicRepresentative p.c bgp p.c_pos b hb.periodic hb.meas
  have hb'c : ∀ i : Fin 2, Measurable fun x : Coord => b' x i := fun i =>
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) i).measurable.comp hb'm
  set F : Coord → ℂ := fun x =>
    ((W x : ℝ) : ℂ) * (((Real.sqrt x.1 * x.1 : ℝ) : ℂ) *
        (b' x 0 * ((qjs x : ℝ) : ℂ) + b' x 1 * ((ejs x : ℝ) : ℂ))) -
      (((x.1 * (u0s x * (∑ k : Fin 3, vQ p.ε x k * cpd k W x) +
          u1s x * cpd 2 W x) : ℝ) : ℂ) *
        (((Real.sqrt x.1 : ℝ) : ℂ) * b' x j))
  have hFm : Measurable F := by
    have hWm : Measurable fun x : Coord => ((W x : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp hWcd.continuous.measurable
    have hs1 : Measurable fun x : Coord => ((Real.sqrt x.1 * x.1 : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp (measurable_fst.sqrt.mul measurable_fst)
    have hsqrt : Measurable fun x : Coord => ((Real.sqrt x.1 : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp measurable_fst.sqrt
    have hadv_r : Measurable fun x : Coord =>
        x.1 * (u0s x * (∑ k : Fin 3, vQ p.ε x k * cpd k W x) + u1s x * cpd 2 W x) := by
      have hsum : Measurable fun x : Coord => ∑ k : Fin 3, vQ p.ε x k * cpd k W x :=
        Finset.measurable_sum _ fun k _ =>
          (vQ_cd p.ε k).continuous.measurable.mul (hWcpd_cd k).continuous.measurable
      exact measurable_fst.mul ((hu0s_m.mul hsum).add (hu1s_m.mul (hWcpd_cd 2).continuous.measurable))
    exact (hWm.mul (hs1.mul (((hb'c 0).mul (Complex.measurable_ofReal.comp hqjs_m)).add
      ((hb'c 1).mul (Complex.measurable_ofReal.comp hejs_m))))).sub
      ((Complex.measurable_ofReal.comp hadv_r).mul (hsqrt.mul (hb'c j)))
  have hFper : ∀ s ξ η : ℝ, F (s, (ξ + p.c, η)) = F (s, (ξ, η)) := by
    intro s ξ η
    have hWp : W (s, (ξ + p.c, η)) = W (s, (ξ, η)) := hWper (s, (ξ, η))
    have hcpdp : ∀ k : Fin 3, cpd k W (s, (ξ + p.c, η)) = cpd k W (s, (ξ, η)) :=
      fun k => hWcpd_per k (s, (ξ, η))
    have hu0p : u0s (s, (ξ + p.c, η)) = u0s (s, (ξ, η)) :=
      sCutoff_mul_qPer p.c ha (fun x => rawProf p x 0)
        (fun z hz => congrArg (fun m => m 0) (rawProf_qPer p hz)) s ξ η
    have hu1p : u1s (s, (ξ + p.c, η)) = u1s (s, (ξ, η)) :=
      sCutoff_mul_qPer p.c ha (fun x => rawProf p x 1)
        (fun z hz => congrArg (fun m => m 1) (rawProf_qPer p hz)) s ξ η
    have hqjp : qjs (s, (ξ + p.c, η)) = qjs (s, (ξ, η)) :=
      sCutoff_mul_qPer p.c ha (fun x => qEps p.ε (rawProf p) x j)
        (fun z hz => congrArg (fun m => m j) (qEps_rawProf_qPer p hz)) s ξ η
    have hejp : ejs (s, (ξ + p.c, η)) = ejs (s, (ξ, η)) :=
      sCutoff_mul_qPer p.c ha (fun x => Axi.dEta (rawProf p) x j)
        (fun z hz => congrArg (fun m => m j) (dEta_rawProf_qPer p hz)) s ξ η
    have hvQp : ∀ k : Fin 3, vQ p.ε (s, (ξ + p.c, η)) k = vQ p.ε (s, (ξ, η)) k := by
      intro k
      fin_cases k <;> rfl
    simp only [F, hWp, hcpdp, hu0p, hu1p, hqjp, hejp, hvQp, hb'per s ξ η]
  -- Pointwise agreement of `F` with the off-axis pairing off `M`
  have hF_off : ∀ x : Coord, 0 < x.1 → x ∉ M →
      F x =
        ((W x : ℝ) : ℂ) * (((Real.sqrt x.1 * x.1 : ℝ) : ℂ) *
            (b x 0 * ((qEps p.ε (rawProf p) x j : ℝ) : ℂ) +
              b x 1 * ((Axi.dEta (rawProf p) x j : ℝ) : ℂ))) -
          (((x.1 * (rawProf p x 0 * (∑ k : Fin 3, vQ p.ε x k * cpd k W x) +
              rawProf p x 1 * cpd 2 W x) : ℝ) : ℂ) *
            (((Real.sqrt x.1 : ℝ) : ℂ) * b x j)) := by
    intro x hx hxM
    have hb_eq := hbb' x hx hxM
    by_cases hxa : a ≤ x.1
    · have hθ1 : sCutoff a x = 1 := sCutoff_eq_one ha hxa
      simp only [F, u0s, u1s, qjs, ejs, hθ1, one_mul, ← hb_eq]
    · obtain ⟨hW0, hcpd0⟩ := winPer_and_cpd_zero_below p.c hab' (lt_of_not_ge hxa)
      simp [F, W, hW0, hcpd0]
  -- Agreement of `s^{-5/2} * F` with `cellWeightConv` on the cell off `M`
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ Axi.qCell p.c) :=
    measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hcell_eq : ∀ x ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell p.c, x ∉ M →
      ((x.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * F x = cellWeightConv p χ b j x := by
    intro x hx hxM
    obtain ⟨hW_eq, hcpd_eq⟩ := winPer_eq_and_cpd_on_cell p.c_pos hχ hx
    have hs : 0 < x.1 := hx.1
    have hrpow := rpow_neg_five_halves_mul_sqrt_mul hs
    rw [hF_off x hs hxM]
    simp only [W, hW_eq, hcpd_eq, cellWeightConv]
    have hrpowC : ((x.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * ((Real.sqrt x.1 * x.1 : ℝ) : ℂ) =
        ((x.1⁻¹ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, hrpow]
    have hrpowC2 : ((x.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * ((x.1 : ℝ) : ℂ) *
        ((Real.sqrt x.1 : ℝ) : ℂ) = ((x.1⁻¹ : ℝ) : ℂ) := by
      calc ((x.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * ((x.1 : ℝ) : ℂ) * ((Real.sqrt x.1 : ℝ) : ℂ)
          = ((x.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * ((Real.sqrt x.1 * x.1 : ℝ) : ℂ) := by
              push_cast; ring
        _ = ((x.1⁻¹ : ℝ) : ℂ) := hrpowC
    push_cast at hrpowC hrpowC2 ⊢
    linear_combination
      (χ x * (b x 0 * qEps p.ε (rawProf p) x j + b x 1 * Axi.dEta (rawProf p) x j)) * hrpowC -
      ((rawProf p x 0 * ∑ k : Fin 3, vQ p.ε x k * cpd k χ x +
          rawProf p x 1 * cpd 2 χ x) * b x j) * hrpowC2
  have hae_cell : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ Axi.qCell p.c)),
      ((x.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * F x = cellWeightConv p χ b j x := by
    have hnull : ∀ᵐ x ∂(volume : Measure Coord), x ∉ M := measure_eq_zero_iff_ae_notMem.1 hM0
    filter_upwards [ae_restrict_of_ae hnull, ae_restrict_mem hS] with x hxM hx
    exact hcell_eq x hx hxM
  -- Finiteness for `ringBridgeC`
  have hint_cw := cellWeightConv_integrable hreg hχ hb j
  have hfin : ∫⁻ x in Ioi (0 : ℝ) ×ˢ Axi.qCell p.c,
      ENNReal.ofReal (p.c⁻¹ * x.1 ^ (-(5 / 2 : ℝ))) * ‖F x‖ₑ < ⊤ := by
    have h1 : IntegrableOn (fun x => ((p.c⁻¹ : ℝ) : ℂ) * cellWeightConv p χ b j x)
        (Ioi (0 : ℝ) ×ˢ Axi.qCell p.c) volume :=
      (hint_cw.const_mul _).integrableOn
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) h1.hasFiniteIntegral
    filter_upwards [hae_cell, ae_restrict_mem hS] with x hx hxm
    have hc0 : 0 ≤ p.c⁻¹ := inv_nonneg.mpr p.c_pos.le
    have hr0 : 0 ≤ x.1 ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hxm.1.le _
    have he1 : ‖((p.c⁻¹ : ℝ) : ℂ)‖ₑ = ENNReal.ofReal p.c⁻¹ := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hc0]
    have he2 : ‖((x.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (x.1 ^ (-(5 / 2 : ℝ))) := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hr0]
    rw [← hx, enorm_mul, enorm_mul, he1, he2, ENNReal.ofReal_mul hc0, mul_assoc]
  have hbr := ringBridgeC p.c p.ε F p.c_pos p.ε_pos hFm hFper hfin
  have hpull := chartNullPullback p.R p.c p.period p.R_pos p.c_pos p.period_eq M hMm hM0 hMper
  have hax : ∀ᵐ y : Space, y ∉ Axi.axis := measure_eq_zero_iff_ae_notMem.1 Axi.volume_axis
  have hinner : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) p.period)),
      ∫ y : Space, dotL (convT p.raw Φ (τ, y)) (NvC p.R b (τ, y)) =
        ∫ y : Space, F (Axi.chart p.ε⁻¹ τ y) := by
    filter_upwards [hpull] with τ hτ
    apply integral_congr_ae
    filter_upwards [hτ, hax] with y hyM hyax
    have hchart_eq : Axi.chart p.ε⁻¹ τ y = Axi.chart p.R τ y := rfl
    rw [hchart_eq, convT, (dotL).map_sub, sub_apply,
      gradUT_dot_offAxis hreg W b j Φ τ hyax (hΦe τ y hyax),
      advT_dot_offAxis p hWcd b j hΦ.smooth hΦe τ hyax,
      hF_off (Axi.chart p.R τ y) (Axi.age_pos p.R_pos.ne' hyax) hyM]
  unfold pairF phaseInt
  have hper_def : p.period = 2 * p.ε * p.c := rfl
  rw [integral_congr_ae hinner, hper_def, hbr]
  have hR_def : p.ε⁻¹ = p.R := rfl
  rw [hR_def]
  congr 1
  rw [integral_congr_ae hae_cell,
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
      cellWeightConv_zero_off_cell p hχ b j hx)]

/-! ## Section 6: Coordinate integration by parts (`HasWeakVec`) -/

private theorem cpd_mul_at {f g : Coord → ℝ} {x : Coord} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (k : Fin 3) :
    cpd k (fun y => f y * g y) x = f x * cpd k g x + g x * cpd k f x := by
  unfold cpd
  have h := fderiv_mul hf hg
  rw [show (fun y => f y * g y) = f * g from rfl, h]
  simp only [add_apply, smul_apply, smul_eq_mul]

private theorem coordTranspose_mul_U0 {v : Coord → Fin 3 → ℝ} (d : Coord → ℝ)
    (hv : ∀ k : Fin 3, ContDiff ℝ ∞ (fun y => v y k))
    {ψ φ : Coord → ℝ} (hψ : ContDiffOn ℝ ∞ ψ U0) (hφ : IsCoordTest φ) (x : Coord) :
    coordTranspose v d (fun y => ψ y * φ y) x =
      ψ x * coordTranspose v d φ x - (∑ k : Fin 3, v x k * cpd k ψ x) * φ x := by
  by_cases hx : x ∈ tsupport φ
  · have hxU : x ∈ U0 := hφ.supp hx
    have hψd : DifferentiableAt ℝ ψ x :=
      (hψ.contDiffAt (isOpen_U0.mem_nhds hxU)).differentiableAt (by simp)
    have hφd : DifferentiableAt ℝ φ x := (hφ.smooth.differentiable (by simp)) x
    have hvd : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => v y k) x :=
      fun k => ((hv k).differentiable (by simp)) x
    have hk : ∀ k : Fin 3, cpd k (fun y => v y k * (ψ y * φ y)) x =
        cpd k ψ x * (v x k * φ x) + ψ x * cpd k (fun y => v y k * φ y) x := by
      intro k
      rw [cpd_mul_at (f := fun y => v y k) (g := fun y => ψ y * φ y) (hvd k) (hψd.mul hφd) k,
        cpd_mul_at hψd hφd k, cpd_mul_at (hvd k) hφd k]
      ring
    simp only [coordTranspose, Fin.sum_univ_three]
    rw [hk 0, hk 1, hk 2]
    ring
  · have hx' : x ∉ tsupport (fun y => ψ y * φ y) := fun h => hx (tsupport_mul_subset_right h)
    have h0_φ : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
    have h0_ct1 : coordTranspose v d (fun y => ψ y * φ y) x = 0 := by
      have hj : ∀ k : Fin 3, cpd k (fun y => v y k * (ψ y * φ y)) x = 0 := fun k => by
        have hxk : x ∉ tsupport (fun y => v y k * (ψ y * φ y)) :=
          fun h => hx' (tsupport_mul_subset_right h)
        simp [cpd, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxk]
      simp [coordTranspose, hj, h0_φ]
    have h0_ct2 : coordTranspose v d φ x = 0 := by
      have hj : ∀ k : Fin 3, cpd k (fun y => v y k * φ y) x = 0 := fun k => by
        have hxk : x ∉ tsupport (fun y => v y k * φ y) :=
          fun h => hx (tsupport_mul_subset_right h)
        simp [cpd, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxk]
      simp [coordTranspose, hj, h0_φ]
    rw [h0_ct1, h0_ct2, h0_φ]
    ring

private theorem coordTranspose_vQ_eq {φ : Coord → ℝ} (hφ : IsCoordTest φ) (ε : ℝ) (x : Coord) :
    coordTranspose (vQ ε) (dQ ε) φ x =
      -(∑ k : Fin 3, vQ ε x k * cpd k φ x) + 2 * ε * φ x := by
  have hd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have cpd_lin : ∀ (ℓ : Coord →L[ℝ] ℝ) (k : Fin 3),
      cpd k (fun y => ℓ y * φ y) x = ℓ x * cpd k φ x + ℓ (cdir k) * φ x := by
    intro ℓ k
    have h : HasFDerivAt (fun y => ℓ y * φ y) (ℓ x • fderiv ℝ φ x + φ x • ℓ) x :=
      ℓ.hasFDerivAt.mul (hd x).hasFDerivAt
    unfold cpd
    rw [h.fderiv]
    simp
    ring
  have e0 : (fun y => vQ ε y 0 * φ y) =
      fun y => ((-2 * ε) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) y * φ y := by
    funext y; simp [vQ]
  have e1 : (fun y => vQ ε y 1 * φ y) = φ := by
    funext y; simp [vQ]
  have e2 : (fun y => vQ ε y 2 * φ y) =
      fun y => ((-ε) • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) y * φ y := by
    funext y; simp [vQ]
  unfold coordTranspose
  rw [Fin.sum_univ_three, Fin.sum_univ_three, e0, e1, e2, cpd_lin _ 0, cpd_lin _ 2]
  simp [vQ, cdir, dQ]
  ring

private theorem coordTranspose_vEta_eq {φ : Coord → ℝ} (x : Coord) :
    coordTranspose vEta dZero φ x = -cpd 2 φ x := by
  have e0 : (fun y => vEta y 0 * φ y) = fun _ => 0 := by funext y; simp [vEta]
  have e1 : (fun y => vEta y 1 * φ y) = fun _ => 0 := by funext y; simp [vEta]
  have e2 : (fun y => vEta y 2 * φ y) = φ := by funext y; simp [vEta]
  unfold coordTranspose
  rw [Fin.sum_univ_three, e0, e1, e2]
  simp [cpd, dZero]

private theorem vGrad_sInv_rawProf0 {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp)
    {x : Coord} (hx : x ∈ U0) :
    (∑ k : Fin 3, vQ p.ε x k * cpd k (fun y : Coord => y.1⁻¹ * rawProf p y 0) x) =
      x.1⁻¹ * (qEps p.ε (rawProf p) x 0 + p.ε * rawProf p x 0) +
        2 * p.ε * (x.1⁻¹ * rawProf p x 0) := by
  have hs : 0 < x.1 := mem_U0_iff.mp hx
  have hsne : x.1 ≠ 0 := hs.ne'
  have hu : DifferentiableAt ℝ (rawProf p) x := rawProfDiffAt dm dp p d hreg x hs
  have hu0_fderiv : HasFDerivAt (fun y : Coord => rawProf p y 0)
      ((EuclideanSpace.proj (0 : Fin 2) : Axi.Merid →L[ℝ] ℝ).comp (fderiv ℝ (rawProf p) x)) x :=
    (EuclideanSpace.proj (0 : Fin 2) : Axi.Merid →L[ℝ] ℝ).hasFDerivAt.comp x hu.hasFDerivAt
  have hinv_fderiv : HasFDerivAt (fun y : Coord => y.1⁻¹)
      ((-(x.1 ^ 2)⁻¹) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x :=
    (hasDerivAt_inv hsne).comp_hasFDerivAt x (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt
  have hprod : HasFDerivAt (fun y : Coord => y.1⁻¹ * rawProf p y 0) _ x :=
    hinv_fderiv.mul hu0_fderiv
  have hcpd : ∀ k : Fin 3,
      cpd k (fun y : Coord => y.1⁻¹ * rawProf p y 0) x =
        x.1⁻¹ * (fderiv ℝ (rawProf p) x (cdir k) 0) -
          (x.1 ^ 2)⁻¹ * (cdir k).1 * rawProf p x 0 := by
    intro k
    unfold cpd
    rw [hprod.fderiv]
    have hfst : (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) (cdir k) = (cdir k).1 := rfl
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, hfst,
      EuclideanSpace.coe_proj, smul_eq_mul]
    ring
  rw [Fin.sum_univ_three, hcpd 0, hcpd 1, hcpd 2]
  have hdS : fderiv ℝ (rawProf p) x (cdir 0) 0 = Axi.dS (rawProf p) x 0 := rfl
  have hdQ : fderiv ℝ (rawProf p) x (cdir 1) 0 = Axi.dQ (rawProf p) x 0 := rfl
  have hdE : fderiv ℝ (rawProf p) x (cdir 2) 0 = Axi.dEta (rawProf p) x 0 := rfl
  rw [hdS, hdQ, hdE]
  have hc0 : (cdir 0).1 = 1 := rfl
  have hc1 : (cdir 1).1 = 0 := rfl
  have hc2 : (cdir 2).1 = 0 := rfl
  rw [hc0, hc1, hc2]
  have hq : qEps p.ε (rawProf p) x 0 =
      Axi.dQ (rawProf p) x 0 -
        p.ε * (2 * x.1 * Axi.dS (rawProf p) x 0 + x.2.2 * Axi.dEta (rawProf p) x 0 +
          rawProf p x 0) := by
    simp [qEps, kAge]
    ring
  have hv0 : vQ p.ε x 0 = -2 * p.ε * x.1 := rfl
  have hv1 : vQ p.ε x 1 = 1 := rfl
  have hv2 : vQ p.ε x 2 = -p.ε * x.2.2 := rfl
  rw [hq, hv0, hv1, hv2]
  field_simp [hsne]
  ring

private theorem cpd2_sInv_rawProf1 {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp)
    {x : Coord} (hx : x ∈ U0) :
    cpd 2 (fun y : Coord => y.1⁻¹ * rawProf p y 1) x =
      x.1⁻¹ * Axi.dEta (rawProf p) x 1 := by
  have hs : 0 < x.1 := mem_U0_iff.mp hx
  have hsne : x.1 ≠ 0 := hs.ne'
  have hu : DifferentiableAt ℝ (rawProf p) x := rawProfDiffAt dm dp p d hreg x hs
  have hu1_fderiv : HasFDerivAt (fun y : Coord => rawProf p y 1)
      ((EuclideanSpace.proj (1 : Fin 2) : Axi.Merid →L[ℝ] ℝ).comp (fderiv ℝ (rawProf p) x)) x :=
    (EuclideanSpace.proj (1 : Fin 2) : Axi.Merid →L[ℝ] ℝ).hasFDerivAt.comp x hu.hasFDerivAt
  have hinv_fderiv : HasFDerivAt (fun y : Coord => y.1⁻¹)
      ((-(x.1 ^ 2)⁻¹) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x :=
    (hasDerivAt_inv hsne).comp_hasFDerivAt x (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt
  have hprod : HasFDerivAt (fun y : Coord => y.1⁻¹ * rawProf p y 1) _ x :=
    hinv_fderiv.mul hu1_fderiv
  unfold cpd
  rw [hprod.fderiv]
  have hdE : fderiv ℝ (rawProf p) x (cdir 2) 1 = Axi.dEta (rawProf p) x 1 := rfl
  have hfst2 : (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) (cdir 2) = 0 := rfl
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, hfst2,
    EuclideanSpace.coe_proj, smul_eq_mul, hdE, mul_zero, add_zero]

private theorem coordTranspose_sum_psi {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp)
    {χ : Coord → ℝ} (hχ : IsWinTest p.c χ) (x : Coord) :
    coordTranspose (vQ p.ε) (dQ p.ε) (fun y => (y.1⁻¹ * rawProf p y 0) * χ y) x +
        coordTranspose vEta dZero (fun y => (y.1⁻¹ * rawProf p y 1) * χ y) x =
      -(x.1⁻¹ * (rawProf p x 0 * (∑ k : Fin 3, vQ p.ε x k * cpd k χ x) +
          rawProf p x 1 * cpd 2 χ x)) -
        x.1⁻¹ * chartDivR p.ε (rawProf p) x * χ x := by
  have hu := rawProf_cd hreg
  have hψ0_cd : ContDiffOn ℝ ∞ (fun y : Coord => y.1⁻¹ * rawProf p y 0) U0 :=
    sInv_cd.mul (merid_coord_cd hu 0)
  have hψ1_cd : ContDiffOn ℝ ∞ (fun y : Coord => y.1⁻¹ * rawProf p y 1) U0 :=
    sInv_cd.mul (merid_coord_cd hu 1)
  rw [coordTranspose_mul_U0 (dQ p.ε) (vQ_cd p.ε) hψ0_cd hχ.1 x,
    coordTranspose_mul_U0 dZero vEta_cd hψ1_cd hχ.1 x,
    coordTranspose_vQ_eq hχ.1 p.ε x, coordTranspose_vEta_eq x]
  by_cases hx : x ∈ tsupport χ
  · have hxU : x ∈ U0 := hχ.1.supp hx
    have hvE : (∑ k : Fin 3, vEta x k * cpd k (fun y : Coord => y.1⁻¹ * rawProf p y 1) x) =
        cpd 2 (fun y : Coord => y.1⁻¹ * rawProf p y 1) x := by
      rw [Fin.sum_univ_three]
      simp [vEta]
    rw [vGrad_sInv_rawProf0 hreg hxU, hvE, cpd2_sInv_rawProf1 hreg hxU]
    unfold chartDivR
    ring
  · have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
    have hcpd0 : ∀ k : Fin 3, cpd k χ x = 0 := fun k =>
      image_eq_zero_of_notMem_tsupport fun h => hx (tsupport_cpd_subset k h)
    simp [hχ0, hcpd0]

private theorem integral_cellWeightConv_eq_wInt {p : Params} {d dm dp : ℝ}
    (hreg : BgRegime p d dm dp) {χ : Coord → ℝ} (hχ : IsWinTest p.c χ)
    {b Qb Eb : CProf} (hb : InHr p.c bgp b)
    (hQb : HasWeakVec (vQ p.ε) (dQ p.ε) b Qb) (hEb : HasWeakVec vEta dZero b Eb) (j : Fin 2) :
    ∫ x : Coord, cellWeightConv p χ b j x =
      wInt χ (fun z : Coord => ((Real.sqrt z.1 : ℝ) : ℂ) * kOutChart p b Qb Eb z j) := by
  have hu := rawProf_cd hreg
  set ψ0 : Coord → ℝ := fun y => (y.1⁻¹ * rawProf p y 0) * χ y
  set ψ1 : Coord → ℝ := fun y => (y.1⁻¹ * rawProf p y 1) * χ y
  have hψ0 : IsCoordTest ψ0 := isCoordTest_mul_U0 (sInv_cd.mul (merid_coord_cd hu 0)) hχ.1
  have hψ1 : IsCoordTest ψ1 := isCoordTest_mul_U0 (sInv_cd.mul (merid_coord_cd hu 1)) hχ.1
  have hφ0 : IsCoordTest (fun x => (x.1⁻¹ * qEps p.ε (rawProf p) x j) * χ x) :=
    isCoordTest_mul_U0 (sInv_cd.mul (merid_coord_cd (qEps_cd hu) j)) hχ.1
  have hφ1 : IsCoordTest (fun x => (x.1⁻¹ * Axi.dEta (rawProf p) x j) * χ x) :=
    isCoordTest_mul_U0 (sInv_cd.mul (merid_coord_cd (dEta_cd hu) j)) hχ.1
  have hφdiv : IsCoordTest (fun x => (x.1⁻¹ * chartDivR p.ε (rawProf p) x) * χ x) :=
    isCoordTest_mul_U0 (sInv_cd.mul (chartDivR_cd hu)) hχ.1
  have I_g0 := integrable_coordTest_mul_hr p.c_pos hb 0 hφ0
  have I_g1 := integrable_coordTest_mul_hr p.c_pos hb 1 hφ1
  have I_div := integrable_coordTest_mul_hr p.c_pos hb j hφdiv
  obtain ⟨I_ct0_raw, I_Qb_raw⟩ := (hQb j).1 ψ0 hψ0
  obtain ⟨I_ct1_raw, I_Eb_raw⟩ := (hEb j).1 ψ1 hψ1
  have I_ct0 : Integrable (fun x : Coord => b x j * (coordTranspose (vQ p.ε) (dQ p.ε) ψ0 x : ℂ)) volume :=
    I_ct0_raw
  have I_Qb : Integrable (fun x : Coord => Qb x j * (ψ0 x : ℂ)) volume := I_Qb_raw
  have I_ct1 : Integrable (fun x : Coord => b x j * (coordTranspose vEta dZero ψ1 x : ℂ)) volume :=
    I_ct1_raw
  have I_Eb : Integrable (fun x : Coord => Eb x j * (ψ1 x : ℂ)) volume := I_Eb_raw
  have hQb_eq : ∫ x : Coord, b x j * (coordTranspose (vQ p.ε) (dQ p.ε) ψ0 x : ℂ) =
      ∫ x : Coord, Qb x j * (ψ0 x : ℂ) := ((hQb j).2 ψ0 hψ0).symm
  have hEb_eq : ∫ x : Coord, b x j * (coordTranspose vEta dZero ψ1 x : ℂ) =
      ∫ x : Coord, Eb x j * (ψ1 x : ℂ) := ((hEb j).2 ψ1 hψ1).symm
  have hpt : ∀ x : Coord, cellWeightConv p χ b j x =
      ((((x.1⁻¹ * qEps p.ε (rawProf p) x j) * χ x : ℝ) : ℂ) * b x 0 +
        (((x.1⁻¹ * Axi.dEta (rawProf p) x j) * χ x : ℝ) : ℂ) * b x 1) +
        (b x j * (coordTranspose (vQ p.ε) (dQ p.ε) ψ0 x : ℂ) +
          b x j * (coordTranspose vEta dZero ψ1 x : ℂ)) +
        (((x.1⁻¹ * chartDivR p.ε (rawProf p) x) * χ x : ℝ) : ℂ) * b x j := by
    intro x
    have hct := congrArg (fun r : ℝ => (r : ℂ)) (coordTranspose_sum_psi hreg hχ x)
    push_cast at hct
    unfold cellWeightConv
    push_cast
    linear_combination (b x j) * (-hct)
  have hint_eq : ∫ x : Coord, cellWeightConv p χ b j x =
      ∫ x : Coord,
        (((((x.1⁻¹ * qEps p.ε (rawProf p) x j) * χ x : ℝ) : ℂ) * b x 0 +
          (((x.1⁻¹ * Axi.dEta (rawProf p) x j) * χ x : ℝ) : ℂ) * b x 1) +
          (Qb x j * (ψ0 x : ℂ) + Eb x j * (ψ1 x : ℂ)) +
          (((x.1⁻¹ * chartDivR p.ε (rawProf p) x) * χ x : ℝ) : ℂ) * b x j) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    have h1 := integral_add ((I_g0.add I_g1).add (I_ct0.add I_ct1)) I_div
    have h2 := integral_add (I_g0.add I_g1) (I_ct0.add I_ct1)
    have h3 := integral_add I_ct0 I_ct1
    have h4 := integral_add I_Qb I_Eb
    have h5 := integral_add (I_g0.add I_g1) (I_Qb.add I_Eb)
    have h6 := integral_add ((I_g0.add I_g1).add (I_Qb.add I_Eb)) I_div
    dsimp only [Pi.add_apply] at h1 h2 h3 h4 h5 h6
    rw [h1, h2, h3, hQb_eq, hEb_eq, ← h4, ← h5, ← h6]
  rw [hint_eq]
  unfold wInt
  congr 1
  funext x
  by_cases hx : χ x = 0
  · simp [ψ0, ψ1, hx]
  · have hxU : x ∈ U0 := hχ.1.supp (subset_tsupport χ (Function.mem_support.2 hx))
    have hs : 0 < x.1 := mem_U0_iff.mp hxU
    have hrpow := rpow_neg_five_halves_mul_sqrt_mul hs
    have hrpowC : ((x.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * ((Real.sqrt x.1 : ℝ) : ℂ) * ((x.1 : ℝ) : ℂ) =
        ((x.1⁻¹ : ℝ) : ℂ) := by
      calc ((x.1 ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) * ((Real.sqrt x.1 : ℝ) : ℂ) * ((x.1 : ℝ) : ℂ)
          = ((x.1 ^ (-(5 / 2 : ℝ)) * (Real.sqrt x.1 * x.1) : ℝ) : ℂ) := by push_cast; ring
        _ = ((x.1⁻¹ : ℝ) : ℂ) := by rw [hrpow]
    simp only [kOutChart, cplx, ψ0, ψ1, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    push_cast at hrpowC ⊢
    linear_combination
      (-(χ x * (rawProf p x 0 * Qb x j + rawProf p x 1 * Eb x j +
          (b x 0 * qEps p.ε (rawProf p) x j + b x 1 * Axi.dEta (rawProf p) x j) +
          chartDivR p.ε (rawProf p) x * b x j))) * hrpowC

/-! ## Section 7: Local integrability of `√s • kOutChart` and proof of `KOutChartAe` -/

private theorem sqrt_kOutChart_locInt {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp)
    {b Qb Eb : CProf} (hb : InHr p.c bgp b)
    (hQb : HasWeakVec (vQ p.ε) (dQ p.ε) b Qb) (hEb : HasWeakVec vEta dZero b Eb) (j : Fin 2) :
    LocallyIntegrableOn
      (fun x : Coord => ((Real.sqrt x.1 : ℝ) : ℂ) * kOutChart p b Qb Eb x j) U0 volume := by
  have hu := rawProf_cd hreg
  have hlc := isOpen_U0.isLocallyClosed
  have hcs : ContinuousOn (fun x : Coord => x.1) U0 := continuous_fst.continuousOn
  have hcsq : ContinuousOn (fun x : Coord => Real.sqrt x.1) U0 :=
    (Real.continuous_sqrt.comp continuous_fst).continuousOn
  have hc1 : ContinuousOn (fun x : Coord => ((Real.sqrt x.1 * x.1 * rawProf p x 0 : ℝ) : ℂ)) U0 :=
    Complex.continuous_ofReal.comp_continuousOn
      ((hcsq.mul hcs).mul (merid_coord_cd hu 0).continuousOn)
  have hc2 : ContinuousOn (fun x : Coord => ((Real.sqrt x.1 * x.1 * rawProf p x 1 : ℝ) : ℂ)) U0 :=
    Complex.continuous_ofReal.comp_continuousOn
      ((hcsq.mul hcs).mul (merid_coord_cd hu 1).continuousOn)
  have hc3 : ContinuousOn (fun x : Coord => ((x.1 * qEps p.ε (rawProf p) x j : ℝ) : ℂ)) U0 :=
    Complex.continuous_ofReal.comp_continuousOn
      (hcs.mul (merid_coord_cd (qEps_cd hu) j).continuousOn)
  have hc4 : ContinuousOn (fun x : Coord => ((x.1 * Axi.dEta (rawProf p) x j : ℝ) : ℂ)) U0 :=
    Complex.continuous_ofReal.comp_continuousOn
      (hcs.mul (merid_coord_cd (dEta_cd hu) j).continuousOn)
  have hc5 : ContinuousOn (fun x : Coord => ((x.1 * chartDivR p.ε (rawProf p) x : ℝ) : ℂ)) U0 :=
    Complex.continuous_ofReal.comp_continuousOn (hcs.mul (chartDivR_cd hu).continuousOn)
  have hL1 := ((hQb j).locallyIntegrableOn).continuousOn_mul hc1 hlc
  have hL2 := ((hEb j).locallyIntegrableOn).continuousOn_mul hc2 hlc
  have hL3 := (profileLocInt p.c b p.c_pos hb 0).continuousOn_mul hc3 hlc
  have hL4 := (profileLocInt p.c b p.c_pos hb 1).continuousOn_mul hc4 hlc
  have hL5 := (profileLocInt p.c b p.c_pos hb j).continuousOn_mul hc5 hlc
  refine (((hL1.add hL2).add (hL3.add hL4)).add hL5).congr ?_
  filter_upwards [self_mem_ae_restrict isOpen_U0.measurableSet] with x _
  simp only [kOutChart, cplx, PiLp.smul_apply, PiLp.add_apply,
    Pi.add_apply, smul_eq_mul]
  push_cast
  ring

/-- **Proof of `KOutChartAe`** (SP 2007–2012): for `b, g ∈ H_p` with `Q_ε b = Qb`, `∂_η b = Eb`,
and `IsKOut p b g`, `g = kOutChart p b Qb Eb` a.e. on the window strip `s > 0, |q| < c/2`. -/
theorem kOutChartAe : KOutChartAe := by
  intro p d dm dp hreg b g Qb Eb hb hg hQb hEb hK
  have hcomp : ∀ j : Fin 2,
      ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (Ioo (-p.c / 2) (p.c / 2) ×ˢ (univ : Set ℝ)))),
        g x j = kOutChart p b Qb Eb x j := by
    intro j
    have hloc_g := profileLocInt p.c g p.c_pos hg j
    have hloc_k := sqrt_kOutChart_locInt hreg hb hQb hEb j
    have hzero := fundWindow_proof p.c
      (fun x : Coord =>
        ((Real.sqrt x.1 : ℝ) : ℂ) * g x j -
          ((Real.sqrt x.1 : ℝ) : ℂ) * kOutChart p b Qb Eb x j)
      p.c_pos (hloc_g.sub hloc_k) (fun χ hχ => by
        obtain ⟨Φ, hΦ, hΦe⟩ := windowPhaseVec p.c p.ε χ p.c_pos p.ε_pos hχ j
        have hpair := hK Φ hΦ
        have hL := pairF_convT_eq_coord hreg hχ hb j hΦ hΦe
        have hR := WindowZeroHelp2.pairF_window p.c p.ε χ p.c_pos p.ε_pos hχ j Φ hΦe g hg
        have hper_def : p.period = 2 * p.ε * p.c := rfl
        have hR_def : p.ε⁻¹ = p.R := rfl
        rw [hper_def] at hpair hL
        rw [hR_def] at hR
        rw [hL, hR, integral_cellWeightConv_eq_wInt hreg hχ hb hQb hEb j] at hpair
        have hne : ((Real.pi * p.R ^ 2 / p.c : ℝ) : ℂ) ≠ 0 := by
          have : (Real.pi * p.R ^ 2 / p.c : ℝ) ≠ 0 := by
            have := p.R_pos
            have := p.c_pos
            positivity
          exact_mod_cast this
        have heq := (mul_left_cancel₀ hne hpair).symm
        rw [WindowZeroHelp2.wInt_sub hχ hloc_g hloc_k, heq, sub_self])
    have hstrip_meas :
        MeasurableSet (Ioi (0 : ℝ) ×ˢ (Ioo (-p.c / 2) (p.c / 2) ×ˢ (univ : Set ℝ))) :=
      measurableSet_Ioi.prod (measurableSet_Ioo.prod MeasurableSet.univ)
    filter_upwards [hzero, ae_restrict_mem hstrip_meas] with x hx hxm
    have hsqrt_ne : ((Real.sqrt x.1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hxm.1).ne'
    exact mul_left_cancel₀ hsqrt_ne (sub_eq_zero.mp hx)
  filter_upwards [hcomp 0, hcomp 1] with x h0 h1
  ext j
  fin_cases j
  · exact h0
  · exact h1

end UnforcedLeray.Short.IIb.PhysKopYLKOut

end
