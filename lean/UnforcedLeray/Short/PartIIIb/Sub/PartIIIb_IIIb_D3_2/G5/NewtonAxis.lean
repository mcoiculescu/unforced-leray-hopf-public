import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5.NewtonTail
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7.NewtonD3Div
import UnforcedLeray.Short.PartIIIb.Proofs.NewtonD2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_6_1.NewtonW
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.XJet

/-!
# Axis Taylor cancellation of the zero-width Newton field (`PartIII-b:IIIb-D3/2/G5/2`)

Defines the zero-shift contraction `newtonV0` and remainder `newtonVRem := newtonV - newtonV0`,
evaluates the axis derivative of `newtonV0` via `newtonLap` (`NewtonD3Div`) and `newtonD2`
(`Proofs/NewtonD2`), and shows that on `0 < t < 4 / (5ν)` the difference
`Lpt c ν 1 μ χo χy M t - ellMuGen c ν 1 μ χo M • aMuFun μ t` reduces to the axis derivative of
`newtonVRem c ν μ χo M - newtonVRem c ν (μ + 1) χo M` at `![1 / √t, 0, 0]`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5

/-- The integrated source matrix `∫_{ℝ²} Σ_M(x') dx'`. -/
def sigmaInt (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) : Mat3 :=
  fun j k => ∫ x' : ℝ × ℝ, sigmaM c ν χo M x' j k

/-- The `t`-integral factor `∫_{(0,1]} (-2 t^{2μ+2}) dt = -2 / (2μ + 3)`. -/
def tInt (μ : ℝ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) 1, -2 * t ^ (2 * μ + 2)

/-- The leading (zero-shift) part of `newtonV`. -/
def newtonV0 (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (y : Vec3) : Vec3 :=
  tInt μ • NewtonVGeom.Lmat (sigmaInt c ν χo M) (NewtonVGeom.D3t y)

/-- The Taylor remainder of `newtonV`. -/
def newtonVRem (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) (y : Vec3) : Vec3 :=
  newtonV c ν μ χo M y - newtonV0 c ν μ χo M y

/-- Structure of the integrated source matrix `sigmaInt c ν χo M` by planar symmetry and polar
integration. -/
def SigmaIntForm (χo : ℝ → ℝ) : Prop :=
  ∀ (c ν : ℝ), 0 < c → 0 < ν → IsOutwardCutoff χo →
    ∀ M : Chart → Mat3, OldThinFinite c ν M →
      (∀ a b : Fin 3, a ≠ b → sigmaInt c ν χo M a b = 0) ∧
      sigmaInt c ν χo M 0 0 = sigmaInt c ν χo M 1 1 ∧
      sigmaInt c ν χo M 2 2 - sigmaInt c ν χo M 0 0 =
        (Real.pi / 2) * ∫ u in Ioi (0 : ℝ),
          χo (ν * u) * u ^ (-(3 / 2 : ℝ)) *
            ConcreteYF.cellInt c (fun p => 2 * M (u, p) 2 2 - M (u, p) 0 0)

/-- Evaluation of `tInt μ = -2 / (2μ + 3)` for `0 ≤ μ`. -/
theorem tInt_eq {μ : ℝ} (hμ : 0 ≤ μ) : tInt μ = -2 / (2 * μ + 3) := by
  unfold tInt
  rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl (by linarith))]
  have h1 : (0 : ℝ) ^ (2 * μ + 2 + 1) = 0 := Real.zero_rpow (by linarith)
  rw [h1, Real.one_rpow]
  have hden : 2 * μ + 3 ≠ 0 := by linarith
  have hden' : 2 * μ + 2 + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- The trace `∑_a ∂_j (newtonD3 x i a a)` vanishes off `0` by harmonicity of `N`. -/
theorem newtonD3_trace_fderiv_zero {w : Vec3} (hw : w ≠ 0) (i j : Fin 3) :
    ∑ a : Fin 3, fderiv ℝ (fun x => newtonD3 x i a a) w (Pi.single j 1) = 0 := by
  have hN : ContDiffOn ℝ NewtonD3.ii newtonN NewtonD3.punct := NewtonD3.newtonN_contDiffOn
  have hQ : ∀ a : Fin 3, ContDiffOn ℝ NewtonD3.ii (DaxD a (DaxD a newtonN)) NewtonD3.punct :=
    fun a => DaxD_smooth (DaxD_smooth hN a) a
  have hS : ∀ y : Vec3, y ≠ 0 → ∑ a, DaxD a (DaxD a newtonN) y = 0 :=
    fun y hy => newtonLap y hy
  have hRy : ∀ y : Vec3, y ≠ 0 → ∑ a : Fin 3, newtonD3 y i a a = 0 := by
    intro y hy
    have hd : ∀ a ∈ (Finset.univ : Finset (Fin 3)),
        DifferentiableAt ℝ (fun z => DaxD a (DaxD a newtonN) z) y :=
      fun a _ => diffAt_of_smoothD (hQ a) hy
    have h1 : fderiv ℝ (fun z => ∑ a, DaxD a (DaxD a newtonN) z) y (Pi.single i 1) = 0 :=
      fderiv_eq_zero_of (fun z hz => hS z hz) hy _
    rw [fderiv_fun_sum hd] at h1
    simp only [FunLike.coe_sum, Finset.sum_apply] at h1
    exact h1
  have hdiff : ∀ a ∈ (Finset.univ : Finset (Fin 3)),
      DifferentiableAt ℝ (fun x => newtonD3 x i a a) w :=
    fun a _ => diffAt_of_smoothD (NewtonD3.newtonD3_contDiffOn i a a) hw
  have hfin : ∑ a : Fin 3, fderiv ℝ (fun x => newtonD3 x i a a) w (Pi.single j 1) =
      fderiv ℝ (fun y => ∑ a : Fin 3, newtonD3 y i a a) w (Pi.single j 1) := by
    rw [fderiv_fun_sum hdiff]
    simp only [FunLike.coe_sum, Finset.sum_apply]
  rw [hfin]
  exact fderiv_eq_zero_of hRy hw _

/-- The explicit formula for `∂_2 ∂_2 N` off `0`. -/
theorem daxD2_newtonN_eq {w : Vec3} (hw : w ≠ 0) :
    DaxD 2 (DaxD 2 newtonN) w =
      (3 * w 2 ^ 2 - (w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2)) /
        (4 * Real.pi * (w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2) ^ (5 / 2 : ℝ)) := by
  have hfun : (fun z : Vec3 => fderiv ℝ newtonN z (Pi.single 2 1)) =
      (fun y : EuclideanSpace ℝ (Fin 3) =>
        fderiv ℝ UnforcedLeray.PressureAnalysis.newtonPotential y
          (UnforcedLeray.coordinateVector 2)) ∘ euAeq := by
    funext z
    have hN : newtonN = fun z => UnforcedLeray.PressureAnalysis.newtonPotential (euAeq z) :=
      funext newtonN_eq_pot
    have hd : fderiv ℝ newtonN z =
        (fderiv ℝ UnforcedLeray.PressureAnalysis.newtonPotential (euAeq z)).comp
          (euAeq : Vec3 →L[ℝ] EuclideanSpace ℝ (Fin 3)) := by
      rw [hN]
      exact ContinuousLinearEquiv.comp_right_fderiv
        (f := UnforcedLeray.PressureAnalysis.newtonPotential) (iso := euAeq)
    show fderiv ℝ newtonN z (Pi.single 2 1) = _
    rw [hd]
    show fderiv ℝ UnforcedLeray.PressureAnalysis.newtonPotential (euAeq z)
      (euAeq (Pi.single 2 1)) = _
    rw [euAeq_single 2]
    rfl
  have hterm : DaxD 2 (DaxD 2 newtonN) w =
      iteratedFDeriv ℝ 2 UnforcedLeray.PressureAnalysis.newtonPotential (euAeq w)
        ![UnforcedLeray.coordinateVector 2, UnforcedLeray.coordinateVector 2] := by
    show fderiv ℝ (fun z : Vec3 => fderiv ℝ newtonN z (Pi.single 2 1)) w (Pi.single 2 1) = _
    rw [hfun, ContinuousLinearEquiv.comp_right_fderiv]
    show fderiv ℝ _ (euAeq w) (euAeq (Pi.single 2 1)) = _
    rw [euAeq_single 2,
      UnforcedLeray.B0635.iteratedFDeriv_eq_nestedDeriv
        (f := UnforcedLeray.PressureAnalysis.newtonPotential)
        (fun y hy => UnforcedLeray.Kernels.contDiffAt_newton hy) 2 _ (euAeq w) (euAeq_ne_zero hw)]
    rfl
  rw [hterm, euHess' (euAeq_ne_zero hw), UnforcedLeray.B0635.inner_coordinateVector]
  have hii : inner ℝ (UnforcedLeray.coordinateVector 2) (UnforcedLeray.coordinateVector 2) = 1 := by
    rw [UnforcedLeray.B0635.inner_coordinateVector]
    simp [UnforcedLeray.coordinateVector]
  have hc2 : (euAeq w) 2 = w 2 := rfl
  have hsq : ∑ i : Fin 3, w i ^ 2 = w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 := Fin.sum_univ_three _
  have hnorm2 : ‖euAeq w‖ ^ 2 = w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 := by
    rw [norm_euAeq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (w i)), hsq]
  have hnorm5 : ‖euAeq w‖ ^ 5 = (w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2) ^ (5 / 2 : ℝ) := by
    have hnn : 0 ≤ w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 := by positivity
    rw [norm_euAeq, hsq, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hnn]
    norm_num
  rw [hii, hc2, hnorm2, hnorm5]
  ring

/-- Evaluation of `∂_j (newtonD3 x i 2 2)` at `![r, 0, 0]` (`r > 0`) via `newtonD2`. -/
theorem newtonD3_zz_axis {r : ℝ} (hr : 0 < r) (i j : Fin 3) :
    fderiv ℝ (fun x => newtonD3 x i 2 2) ![r, 0, 0] (Pi.single j 1) =
      -Dzero i j / (4 * Real.pi * r ^ 5) := by
  let F : (Fin 3 → ℝ) → ℝ := fun x =>
    (3 * x 2 ^ 2 - (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2)) /
      (4 * Real.pi * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) ^ (5 / 2 : ℝ))
  have hr_ne : (![r, 0, 0] : Vec3) ≠ 0 := by
    intro h
    have : (![r, 0, 0] : Vec3) 0 = 0 := by rw [h]; rfl
    simp [hr.ne'] at this
  have hEq : (fun x => newtonD3 x i 2 2) =ᶠ[𝓝 (![r, 0, 0] : Vec3)]
      fun x => fderiv ℝ F x (Pi.single i 1) := by
    filter_upwards [NewtonD3.isOpen_punct.mem_nhds hr_ne] with y hy
    exact congrFD (fun z hz => daxD2_newtonN_eq hz) hy (Pi.single i 1)
  rw [hEq.fderiv_eq]
  have e0 : (![r, 0, 0] : Fin 3 → ℝ) 0 = r := by simp
  have e1 : (![r, 0, 0] : Fin 3 → ℝ) 1 = 0 := by simp
  have e2 : (![r, 0, 0] : Fin 3 → ℝ) 2 = 0 := by simp
  have hQ : (0 : ℝ) < (![r, 0, 0] : Fin 3 → ℝ) 0 ^ 2 + (![r, 0, 0] : Fin 3 → ℝ) 1 ^ 2 +
      (![r, 0, 0] : Fin 3 → ℝ) 2 ^ 2 := by
    rw [e0, e1, e2]
    simpa using pow_pos hr 2
  have hcd : ContDiffAt ℝ 2 F ![r, 0, 0] := by
    have hnum : ContDiffAt ℝ 2
        (fun x : Fin 3 → ℝ => 3 * x 2 ^ 2 - (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2)) ![r, 0, 0] := by
      fun_prop
    have hbase : ContDiffAt ℝ 2
        (fun x : Fin 3 → ℝ => x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) ![r, 0, 0] := by
      fun_prop
    have hden : ContDiffAt ℝ 2
        (fun x : Fin 3 → ℝ => 4 * Real.pi * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) ^ (5 / 2 : ℝ))
        ![r, 0, 0] :=
      contDiffAt_const.mul (hbase.rpow_const_of_ne hQ.ne')
    have hden0 : 4 * Real.pi * ((![r, 0, 0] : Fin 3 → ℝ) 0 ^ 2 + (![r, 0, 0] : Fin 3 → ℝ) 1 ^ 2 +
        (![r, 0, 0] : Fin 3 → ℝ) 2 ^ 2) ^ (5 / 2 : ℝ) ≠ 0 :=
      (mul_pos (by positivity) (Real.rpow_pos_of_pos hQ _)).ne'
    exact hnum.div hden hden0
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) ![r, 0, 0] :=
    (hcd.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hclm : fderiv ℝ (fun x => fderiv ℝ F x (Pi.single i 1)) ![r, 0, 0] (Pi.single j 1) =
      fderiv ℝ (fderiv ℝ F) ![r, 0, 0] (Pi.single j 1) (Pi.single i 1) := by
    rw [fderiv_clm_apply hdF (differentiableAt_const _)]
    simp
  rw [hclm, UnforcedLeray.Short.PartIIIb.newtonD2 r hr j i]
  congr 1
  fin_cases i <;> fin_cases j <;> simp [Dzero]

/-- Smoothness of `newtonV0` off the origin. -/
theorem contDiffAt_newtonV0 (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) {y : Vec3} (hy : y ≠ 0) :
    ContDiffAt ℝ NewtonD3.ii (newtonV0 c ν μ χo M) y :=
  (NewtonVGeom.D3t_contDiffAt hy).continuousLinearMap_comp
    (tInt μ • NewtonVGeom.Lmat (sigmaInt c ν χo M))

theorem differentiableAt_newtonV0 (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) {y : Vec3}
    (hy : y ≠ 0) : DifferentiableAt ℝ (newtonV0 c ν μ χo M) y :=
  (contDiffAt_newtonV0 c ν μ χo M hy).differentiableAt (by simp [NewtonD3.ii])

/-- Formula for `fderiv ℝ (newtonV0 c ν μ χo M)` off `0`. -/
theorem fderiv_newtonV0_apply (c ν μ : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) {y : Vec3}
    (hy : y ≠ 0) (v : Vec3) (i : Fin 3) :
    fderiv ℝ (newtonV0 c ν μ χo M) y v i =
      tInt μ * ∑ a : Fin 3, ∑ b : Fin 3,
        sigmaInt c ν χo M a b * fderiv ℝ (fun x => newtonD3 x i a b) y v := by
  have hdD3 : DifferentiableAt ℝ NewtonVGeom.D3t y :=
    (NewtonVGeom.D3t_contDiffAt hy).differentiableAt (by simp [NewtonD3.ii])
  have hcomp : fderiv ℝ (newtonV0 c ν μ χo M) y =
      (tInt μ • NewtonVGeom.Lmat (sigmaInt c ν χo M)).comp (fderiv ℝ NewtonVGeom.D3t y) :=
    ((tInt μ • NewtonVGeom.Lmat (sigmaInt c ν χo M)).hasFDerivAt.comp y hdD3.hasFDerivAt).fderiv
  rw [hcomp]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul, NewtonVGeom.Lmat_apply]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  have hproj : ((ContinuousLinearMap.proj (i, a, b) : NewtonVGeom.T3 →L[ℝ] ℝ) ∘ NewtonVGeom.D3t) =
      fun x => newtonD3 x i a b := rfl
  rw [← hproj, ((ContinuousLinearMap.proj (i, a, b) : NewtonVGeom.T3 →L[ℝ] ℝ).hasFDerivAt.comp y
    hdD3.hasFDerivAt).fderiv]
  rfl

/-- Contraction of a diagonal matrix with `S 0 0 = S 1 1` against a trace-free vector `d`. -/
theorem diag_sum_trace_zero (S : Mat3) (d : Fin 3 → ℝ)
    (hoff : ∀ a b : Fin 3, a ≠ b → S a b = 0)
    (h01 : S 0 0 = S 1 1)
    (htr : ∑ a : Fin 3, d a = 0) :
    ∑ a : Fin 3, ∑ b : Fin 3, S a b * d (if a = b then a else 0) =
      (S 2 2 - S 0 0) * d 2 := by
  rw [Fin.sum_univ_three] at htr ⊢
  simp only [Fin.sum_univ_three]
  rw [hoff 0 1 (by decide), hoff 0 2 (by decide), hoff 1 0 (by decide),
    hoff 1 2 (by decide), hoff 2 0 (by decide), hoff 2 1 (by decide)]
  simp only [↓reduceIte, zero_mul, add_zero, zero_add]
  linear_combination -d 1 * h01 + S 0 0 * htr

/-- Axis derivative of `newtonV0 c ν μ χo M - newtonV0 c ν (μ + 1) χo M` at `![r, 0, 0]`. -/
theorem fderiv_newtonV0_sub_axis {c ν μ : ℝ} {χo : ℝ → ℝ} (hS : SigmaIntForm χo)
    (hc : 0 < c) (hν : 0 < ν) (hχo : IsOutwardCutoff χo) (hμ : 0 ≤ μ)
    {M : Chart → Mat3} (hM : OldThinFinite c ν M) {r : ℝ} (hr : 0 < r) (i j : Fin 3) :
    fderiv ℝ (newtonV0 c ν μ χo M - newtonV0 c ν (μ + 1) χo M) ![r, 0, 0] (Pi.single j 1) i =
      (ellMuGen c ν 1 μ χo M / (μ + 5 / 2)) * (r ^ 5)⁻¹ * Dzero i j := by
  have hr_ne : (![r, 0, 0] : Vec3) ≠ 0 := by
    intro h
    have : (![r, 0, 0] : Vec3) 0 = 0 := by rw [h]; rfl
    simp [hr.ne'] at this
  obtain ⟨hoff, h01, hdiffS⟩ := hS c ν hc hν hχo M hM
  have hd0 := differentiableAt_newtonV0 c ν μ χo M hr_ne
  have hd1 := differentiableAt_newtonV0 c ν (μ + 1) χo M hr_ne
  rw [fderiv_sub hd0 hd1]
  simp only [ContinuousLinearMap.sub_apply, Pi.sub_apply]
  rw [fderiv_newtonV0_apply c ν μ χo M hr_ne, fderiv_newtonV0_apply c ν (μ + 1) χo M hr_ne]
  have hsum : ∑ a : Fin 3, ∑ b : Fin 3,
      sigmaInt c ν χo M a b * fderiv ℝ (fun x => newtonD3 x i a b) ![r, 0, 0] (Pi.single j 1) =
      (sigmaInt c ν χo M 2 2 - sigmaInt c ν χo M 0 0) *
        (-Dzero i j / (4 * Real.pi * r ^ 5)) := by
    let d : Fin 3 → ℝ := fun a => fderiv ℝ (fun x => newtonD3 x i a a) ![r, 0, 0] (Pi.single j 1)
    have htr : ∑ a : Fin 3, d a = 0 := newtonD3_trace_fderiv_zero hr_ne i j
    have hcongr : ∑ a : Fin 3, ∑ b : Fin 3,
        sigmaInt c ν χo M a b * fderiv ℝ (fun x => newtonD3 x i a b) ![r, 0, 0] (Pi.single j 1) =
        ∑ a : Fin 3, ∑ b : Fin 3, sigmaInt c ν χo M a b * d (if a = b then a else 0) := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases hab : a = b
      · subst hab; simp [d]
      · rw [hoff a b hab, zero_mul, zero_mul]
    rw [hcongr, diag_sum_trace_zero (sigmaInt c ν χo M) d hoff h01 htr]
    congr 1
    exact newtonD3_zz_axis hr i j
  rw [hsum, tInt_eq hμ, tInt_eq (by linarith), hdiffS]
  unfold ellMuGen
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hr5 : r ^ 5 ≠ 0 := pow_ne_zero 5 hr.ne'
  have h1 : 2 * μ + 3 ≠ 0 := by linarith
  have h2 : 2 * (μ + 1) + 3 ≠ 0 := by linarith
  have h3 : μ + 3 / 2 ≠ 0 := by linarith
  have h4 : μ + 5 / 2 ≠ 0 := by linarith
  field_simp
  ring

/-- `chiYr ν 1 χy t = 1` for `5 * ν / 4 ≤ t ^ 2` (`0 < ν`). -/
theorem chiYr_one_of_sq_ge {ν : ℝ} (hν : 0 < ν) {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) {t : ℝ}
    (ht : 5 * ν / 4 ≤ t ^ 2) : chiYr ν 1 χy t = 1 := by
  have ht2 : 0 < t ^ 2 := by linarith
  have ht0 : t ≠ 0 := fun h => by simp [h] at ht2
  unfold chiYr
  rw [if_neg ht0]
  apply hχ.one
  have h1 : (1 * t) ^ 2 = t ^ 2 := by ring
  rw [h1, div_le_iff₀ ht2]
  linarith

/-- `deriv (chiYr ν 1 χy) t = 0` for `5 * ν / 4 < t ^ 2` (`0 < ν`). -/
theorem chiYr_deriv_zero_of_sq_gt {ν : ℝ} (hν : 0 < ν) {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) {t : ℝ}
    (ht : 5 * ν / 4 < t ^ 2) : deriv (chiYr ν 1 χy) t = 0 := by
  have hopen : IsOpen {s : ℝ | 5 * ν / 4 < s ^ 2} :=
    isOpen_lt continuous_const (by fun_prop)
  have hev : chiYr ν 1 χy =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [hopen.mem_nhds (show t ∈ {s : ℝ | 5 * ν / 4 < s ^ 2} from ht)] with s hs
    exact chiYr_one_of_sq_ge hν hχ (le_of_lt hs)
  rw [hev.deriv_eq, deriv_const]

/-- `streamCut ν 1 χy Z` agrees with `Z` on the open region `{w | 5 * ν / 4 < cylR w ^ 2}`. -/
theorem streamCut_eq_self_of_sq_gt {ν : ℝ} (hν : 0 < ν) {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (Z : Vec3 → Vec3) {w : Vec3} (hw : 5 * ν / 4 < cylR w ^ 2) :
    streamCut ν 1 χy Z w = Z w := by
  unfold streamCut
  rw [chiYr_one_of_sq_ge hν hχ hw.le, chiYr_deriv_zero_of_sq_gt hν hχ hw]
  simp

/-- On `0 < t < 4 / (5 * ν)`, `(Lpt c ν 1 μ χo χy M t - (ellMuGen c ν 1 μ χo M • aMuFun μ) t) i j`
equals the axis derivative of `newtonVRem c ν μ χo M - newtonVRem c ν (μ + 1) χo M` at
`![(1 : ℝ)⁻¹ / Real.sqrt t, 0, 0]`. -/
theorem lpt_sub_aMu_eq_fderiv_newtonVRem {c ν ε μ : ℝ} {χo χy : ℝ → ℝ} (hS : SigmaIntForm χo)
    (h : LHyp c ν ε μ χo χy) {M : Chart → Mat3} (hM : OldThinFinite c ν M)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 4 / (5 * ν)) (i j : Fin 3) :
    (Lpt c ν 1 μ χo χy M t - (ellMuGen c ν 1 μ χo M • aMuFun μ) t) i j =
      fderiv ℝ (newtonVRem c ν μ χo M - newtonVRem c ν (μ + 1) χo M)
        ![(1 : ℝ)⁻¹ / Real.sqrt t, 0, 0] (Pi.single j 1) i := by
  set r := (1 : ℝ)⁻¹ / Real.sqrt t with hrdef
  have hsqt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hr : 0 < r := by positivity
  have hr2 : r ^ 2 = 1 / t := by
    rw [hrdef, inv_one, div_pow, one_pow, Real.sq_sqrt ht0.le]
  have hgt : 5 * ν / 4 < r ^ 2 := by
    rw [hr2, lt_div_iff₀ ht0]
    have hν5 : 0 < 5 * ν := by linarith [h.nu_pos]
    have := (lt_div_iff₀ hν5).1 ht1
    linarith
  have hcyl_y : cylR ![r, 0, 0] ^ 2 = r ^ 2 := by
    rw [xj_cylR_sq]
    simp
  have hopen : IsOpen {w : Vec3 | 5 * ν / 4 < cylR w ^ 2} := by
    have hc : Continuous fun w : Vec3 => cylR w ^ 2 := by
      unfold cylR; fun_prop
    exact isOpen_lt continuous_const hc
  have hy_mem : (![r, 0, 0] : Vec3) ∈ {w : Vec3 | 5 * ν / 4 < cylR w ^ 2} := by
    show 5 * ν / 4 < cylR ![r, 0, 0] ^ 2
    rw [hcyl_y]
    exact hgt
  have hXmt_ev : Xmt c ν 1 μ χo χy M =ᶠ[𝓝 (![r, 0, 0] : Vec3)]
      (newtonV c ν μ χo M - newtonV c ν (μ + 1) χo M) := by
    filter_upwards [hopen.mem_nhds hy_mem] with w hw
    unfold Xmt
    rw [streamCut_eq_self_of_sq_gt h.nu_pos h.chiY _ hw]
    simp [youngW]
  have hLpt : Lpt c ν 1 μ χo χy M t i j =
      fderiv ℝ (newtonV c ν μ χo M - newtonV c ν (μ + 1) χo M) ![r, 0, 0] (Pi.single j 1) i := by
    unfold Lpt
    rw [if_pos ht0, ← hrdef, hXmt_ev.fderiv_eq]
  -- Differentiability of `newtonV`, `newtonV0`, `newtonVRem` at `![r, 0, 0]`
  have heuc : ν * (11 / 12) < eucSq ![r, 0, 0] := by
    have : r ^ 2 ≤ eucSq ![r, 0, 0] := by
      rw [← hcyl_y]
      exact xj_sq_le_eucSq _
    linarith [h.nu_pos]
  obtain ⟨CN, hCN⟩ := newtonVRegionBoundW χo
  have hcdV0 := (hCN c ν μ h.c_pos h.nu_pos h.chiO h.mu_pos.le M hM).1
  have hcdV1 := (hCN c ν (μ + 1) h.c_pos h.nu_pos h.chiO (by linarith [h.mu_pos]) M hM).1
  have hdV0 : DifferentiableAt ℝ (newtonV c ν μ χo M) ![r, 0, 0] :=
    (hcdV0.contDiffAt ((NewtonVGeom.isOpen_regU ν).mem_nhds heuc)).differentiableAt (by norm_num)
  have hdV1 : DifferentiableAt ℝ (newtonV c ν (μ + 1) χo M) ![r, 0, 0] :=
    (hcdV1.contDiffAt ((NewtonVGeom.isOpen_regU ν).mem_nhds heuc)).differentiableAt (by norm_num)
  have hr_ne : (![r, 0, 0] : Vec3) ≠ 0 := by
    intro h0
    have : (![r, 0, 0] : Vec3) 0 = 0 := by rw [h0]; rfl
    simp [hr.ne'] at this
  have hd00 := differentiableAt_newtonV0 c ν μ χo M hr_ne
  have hd01 := differentiableAt_newtonV0 c ν (μ + 1) χo M hr_ne
  have hdR0 : DifferentiableAt ℝ (newtonVRem c ν μ χo M) ![r, 0, 0] := hdV0.sub hd00
  have hdR1 : DifferentiableAt ℝ (newtonVRem c ν (μ + 1) χo M) ![r, 0, 0] := hdV1.sub hd01
  have hsplit : (newtonV c ν μ χo M - newtonV c ν (μ + 1) χo M) =
      (newtonV0 c ν μ χo M - newtonV0 c ν (μ + 1) χo M) +
        (newtonVRem c ν μ χo M - newtonVRem c ν (μ + 1) χo M) := by
    funext w
    simp only [Pi.sub_apply, Pi.add_apply, newtonVRem]
    abel
  have hfd_split : fderiv ℝ (newtonV c ν μ χo M - newtonV c ν (μ + 1) χo M) ![r, 0, 0] (Pi.single j 1) i =
      fderiv ℝ (newtonV0 c ν μ χo M - newtonV0 c ν (μ + 1) χo M) ![r, 0, 0] (Pi.single j 1) i +
        fderiv ℝ (newtonVRem c ν μ χo M - newtonVRem c ν (μ + 1) χo M) ![r, 0, 0] (Pi.single j 1) i := by
    rw [hsplit, fderiv_add (hd00.sub hd01) (hdR0.sub hdR1)]
    rfl
  have haMu : (ellMuGen c ν 1 μ χo M • aMuFun μ) t i j =
      fderiv ℝ (newtonV0 c ν μ χo M - newtonV0 c ν (μ + 1) χo M) ![r, 0, 0] (Pi.single j 1) i := by
    rw [fderiv_newtonV0_sub_axis hS h.c_pos h.nu_pos h.chiO h.mu_pos.le hM hr i j]
    simp only [Pi.smul_apply, aMuFun, if_pos ht0, smul_eq_mul]
    have hr5 : (r ^ 5)⁻¹ = t ^ (5 / 2 : ℝ) := by
      have hr_inv : r⁻¹ = Real.sqrt t := by
        rw [hrdef, inv_one, one_div, inv_inv]
      rw [← inv_pow, hr_inv, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
      norm_num
    rw [hr5]
    ring
  simp only [Pi.sub_apply]
  rw [hLpt, hfd_split, haMu]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5
