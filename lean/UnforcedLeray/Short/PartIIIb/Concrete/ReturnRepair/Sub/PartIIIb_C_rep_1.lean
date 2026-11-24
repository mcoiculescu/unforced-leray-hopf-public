import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Seq
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Defs

/-!
# Decomposition of `repairSource` (`PartIII-b:C/rep/1`, source 5169-5176, `repair:source`)

Source: `the November 2 reference manuscript` lines 5132-5146 and 5169-5176:
`F_r = ‖χ_o(r_b⊗w + w⊗r_b)‖_{L²_τL^{22/19}} ≤ P_ν ρ R |N_ν| G(w)`, from `19/22 = 4/11 + 1/2`,
`‖r_b(τ)‖_{11/4} ≤ ρ_b = C₀ν^{-k₀}ρ` and `g ≤ e^{γ/ν}`.

`repairSource_of` proves the target from six leaf statements
* `RbFacts` (the repair `r_b = corr z` of the exact split is axisymmetric without swirl, periodic of
  period `2εc`, and measurable in `y`),
* `RepPhasePointwise` (pointwise bound of the physical repair stress, from the exact multiplier),
* `VelSliceMeas` (phase slices of `𝒩_v w` are a.e.-strongly measurable),
* `HolderPhase` (Hölder `19/22 = 4/11 + 1/2` at one phase),
* `VelPhysL2` (normalized phase `L²` norm of `𝒩_v w`),
* `PeriodSmall` (`2 ε_n c_n ≤ 1` for large `n`),
and the proved lemmas `gamma_le_gauge` (`e^{γ/ν} ≤ ν^{-k}|N_ν|`) and `rhoB_eq` (`ρ_b = C₀ν^{-k₀}ρ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.PhaseSpace

/-- `ρ_b = C₀ ν^{-k₀} ρ` (source 2706-2713, 5138). -/
theorem rhoB_eq (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) :
    L.ρb Pl K = K.C0 * L.ν⁻¹ ^ K.k0 * rhoRep K L := by
  unfold ReturnLevel.ρb UnforcedLeray.Short.IIb.rhoB rhoRep
  simp only [ReturnLevel.params, inv_pow]
  ring

/-- `e^{γ/ν} = |N_ν| ν^{Re κ} ≤ ν^{-k}|N_ν|` for `ν ≤ 1` (source 5118, 5175-5176). -/
theorem gamma_le_gauge (Pl : PlanarData) (L : ReturnLevel) (hν1 : L.ν ≤ 1) :
    Real.exp (gRate Pl / L.ν) ≤ L.ν⁻¹ ^ (⌈-Pl.kappa.re⌉₊) * gaugeN Pl L := by
  have hν := L.ν_pos
  have hN : gaugeN Pl L = Real.exp (gRate Pl / L.ν) * L.ν ^ (-Pl.kappa.re) := by
    unfold gaugeN Nnu
    rw [norm_mul, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos hν]
    simp [gRate, Complex.div_ofReal_re]
  have h1 := UnforcedLeray.Short.PartIIIb.NearInst.seq_rpow_le_inv_pow hν hν1 Pl.kappa.re
  have h2 : Real.exp (gRate Pl / L.ν) = gaugeN Pl L * L.ν ^ Pl.kappa.re := by
    rw [hN, mul_assoc, ← Real.rpow_add hν]; simp
  rw [h2, mul_comm]
  exact mul_le_mul_of_nonneg_right h1 (by rw [hN]; positivity)

/-! ## Leaves -/

/-- **Leaf `RbFacts`** (source 2031, 2522-2523, 2664-2713; `Params.corr_periodic`,
`Params.corr_isAxisymmetricNoSwirl`, `Params.corr_memLp_four`, needing `period = 2εc ≤ 1`): for the
exact split, `r_b = p.corr z` is axisymmetric without swirl, `2c/R`-periodic in `τ`, and
`r_b(τ)` is a.e.-strongly measurable in `y`. -/
def RbFacts : Prop :=
  ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (S : ℝ),
    UnforcedLeray.Short.IIb.ExactSplitII (L.params Pl) (L.ρb Pl K) S L.V L.rb →
    2 * L.ε * cOf L.ν ≤ 1 →
      (∀ τ, AxiNoSwirlPt (L.rb τ)) ∧ (∀ τ y, L.rb (τ + 2 * cOf L.ν / L.ε⁻¹) y = L.rb τ y) ∧
      (∀ τ, AEStronglyMeasurable (L.rb τ) volume)

/-- **Leaf `RepPhasePointwise`** (source 4147, 5169-5171): the physical repair stress
`χ_o(r_b ⊗ 𝒩_v w + 𝒩_v w ⊗ r_b)` (the lift `strPhys` of the repair component of `M_U w`, an exact
multiplier: `concreteBase_isExactMultiplier` with `multPinOfLink` and `nearMU_spec`;
`cartLiftSymOuter_proved`; `0 ≤ χ_o ≤ 1`; null sets of the chart pull back to null sets,
`NearInst.stressPairAE_null`) satisfies `|F| ≤ 2|r_b||𝒩_v w|` for a.e. `(τ, y)` in the cell.
Stated for `C₀ > 0` (source 4147, 5153-5157, 5169-5171): for `C₀ = 0` the gain measure is zero. -/
def RepPhasePointwise : Prop :=
  ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ), 0 < K.C0 → NearAt Pl K L μ →
    (∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsSplitMult M (L.params Pl).R L.V L.rb) →
    (∀ τ, AxiNoSwirlPt (L.rb τ)) →
    (∀ τ y, L.rb (τ + 2 * cOf L.ν / L.ε⁻¹) y = L.rb τ y) →
    ∀ w : LVel Pl L, ∀ᵐ τ ∂(volume.restrict (Ioc 0 (2 * L.ε * cOf L.ν))), ∀ᵐ y : Space,
      UnforcedLeray.Short.IIIa.tensorNorm (repStressPhys Pl K L w (τ, y)) ≤
        2 * ‖L.rb τ y‖ * ‖velPhys L.ε⁻¹ (cOf L.ν) w (τ, y)‖

/-- **Leaf `VelSliceMeas`** (source 2683; `velPhys` of an `L²` chart field is a measurable function
of `(τ, y)` up to null sets, `fwuA1_measurable_velPhys`, `velPhys_congr_chart`): the phase slices of
`𝒩_v w` are a.e.-strongly measurable for a.e. phase in the cell. -/
def VelSliceMeas : Prop :=
  ∀ (Pl : PlanarData) (L : ReturnLevel) (w : LVel Pl L),
    ∀ᵐ τ ∂(volume.restrict (Ioc 0 (2 * L.ε * cOf L.ν))),
      AEStronglyMeasurable (fun y : Space => velPhys L.ε⁻¹ (cOf L.ν) w (τ, y)) volume

/-- **Leaf `HolderPhase`** (source 5175, `19/22 = 4/11 + 1/2`): Hölder at one phase,
`‖f‖_{22/19}² ≤ 4 ‖a‖_{11/4}² ‖b‖_2²` when `f ≤ 2|a||b|` a.e. -/
def HolderPhase : Prop :=
  ∀ (a : Space → Space) (b : Space → UnforcedLeray.PhaseSpace.CVec3) (f : Space → ℝ),
    AEStronglyMeasurable a volume → AEStronglyMeasurable b volume →
    (∀ᵐ y, f y ≤ 2 * ‖a y‖ * ‖b y‖) →
    (∫⁻ y : Space, ENNReal.ofReal (f y) ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ)) ≤
      ENNReal.ofReal 2 ^ 2 * eLpNorm a (ENNReal.ofReal UnforcedLeray.Short.IIb.bgp) volume ^ 2 *
        ∫⁻ y : Space, ENNReal.ofReal ‖b y‖ ^ 2

/-- **Leaf `VelPhysL2`** (source 2683-2689, 5173-5176: `R⁻¹‖𝒩_v b‖_{Y_2} = √π‖b‖_H`, `g ≤ e^{γ/ν}`):
the phase-normalized `L²` norm of `𝒩_v w` is at most `C₁ R e^{γ/ν} ‖w‖`, `C₁` an absolute
constant, `R = ε⁻¹`. Stated for `0 ≤ γ` (`RepairStanding.gamma_pos`): for `γ < 0`, `g ≤ e^{γ/ν}` fails. -/
def VelPhysL2 : Prop :=
  ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ (Pl : PlanarData), 0 ≤ gRate Pl → ∀ (L : ReturnLevel) (w : LVel Pl L),
    ENNReal.ofReal (2 * L.ε * cOf L.ν)⁻¹ *
      ∫⁻ t in Ioc (0 : ℝ) (2 * L.ε * cOf L.ν), ∫⁻ y : Space,
        ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) w (t, y)‖ ^ 2 ≤
      ENNReal.ofReal ((C1 * L.ε⁻¹ * Real.exp (gRate Pl / L.ν) * ‖w‖) ^ 2)

/-- **Leaf `PeriodSmall`** (source 2031-2037, 4109-4124: `ε_n = e^{-d_n/ν_n}`, `d_n ≥ d₋ > 0`,
`c_n = ν_n^{-2}`): `P_n = 2 ε_n c_n ≤ 1` for large `n`. -/
def PeriodSmall : Prop :=
  ∀ (D : SeqData) {dm dp : ℝ}, D.RepairStanding dm dp →
    ∀ᶠ n : ℕ in atTop, 2 * (D.level n).ε * cOf (D.level n).ν ≤ 1

/-! ## Assembly at one level -/

theorem repairSourceAt_level (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (S μ : ℝ)
    (hC0 : 0 < K.C0) (hν1 : L.ν ≤ 1) (hP : 2 * L.ε * cOf L.ν ≤ 1)
    (hsplit : UnforcedLeray.Short.IIb.ExactSplitII (L.params Pl) (L.ρb Pl K) S L.V L.rb)
    (hnear : NearAt Pl K L μ)
    (hs : ∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsSplitMult M (L.params Pl).R L.V L.rb)
    (hRb : RbFacts) (hpt : RepPhasePointwise) (hmeas : VelSliceMeas) (hH : HolderPhase)
    (C1 : ℝ) (hC1 : 0 ≤ C1)
    (hV : ∀ w : LVel Pl L,
      ENNReal.ofReal (2 * L.ε * cOf L.ν)⁻¹ *
        ∫⁻ t in Ioc (0 : ℝ) (2 * L.ε * cOf L.ν), ∫⁻ y : Space,
          ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) w (t, y)‖ ^ 2 ≤
        ENNReal.ofReal ((C1 * L.ε⁻¹ * Real.exp (gRate Pl / L.ν) * ‖w‖) ^ 2)) :
    RepairSourceAt Pl K L (2 * K.C0 * C1) (K.k0 + ⌈-Pl.kappa.re⌉₊) := by
  intro w
  obtain ⟨hax, hper, hrbm⟩ := hRb Pl K L S hsplit hP
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hρeq := rhoB_eq Pl K L
  have hrho : 0 ≤ rhoRep K L := by unfold rhoRep; positivity
  have hρb : 0 ≤ L.ρb Pl K := by rw [hρeq]; positivity
  set P := 2 * L.ε * cOf L.ν with hPdef
  set X : ℝ := C1 * L.ε⁻¹ * Real.exp (gRate Pl / L.ν) * ‖w‖ with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  -- per-phase bound
  have hphase : ∀ᵐ τ ∂(volume.restrict (Ioc 0 P)),
      (∫⁻ y : Space, ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
          (repStressPhys Pl K L w (τ, y))) ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ)) ≤
        (ENNReal.ofReal 2 ^ 2 * ENNReal.ofReal (L.ρb Pl K) ^ 2) *
          ∫⁻ y : Space, ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) w (τ, y)‖ ^ 2 := by
    filter_upwards [hpt Pl K L μ hC0 hnear hs hax hper w, hmeas Pl L w] with τ h1 h2
    refine le_trans (hH (L.rb τ) (fun y => velPhys L.ε⁻¹ (cOf L.ν) w (τ, y)) _ (hrbm τ) h2 h1) ?_
    have he : eLpNorm (L.rb τ) (ENNReal.ofReal UnforcedLeray.Short.IIb.bgp) volume ≤
        ENNReal.ofReal (L.ρb Pl K) :=
      le_trans le_self_add (hsplit.energy τ)
    rw [mul_assoc, mul_assoc]
    gcongr
  have hint : (∫⁻ t in Ioc (0 : ℝ) P, (∫⁻ y : Space, ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
          (repStressPhys Pl K L w (t, y))) ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ))) ≤
      (ENNReal.ofReal 2 ^ 2 * ENNReal.ofReal (L.ρb Pl K) ^ 2) *
        ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
          ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) w (t, y)‖ ^ 2 := by
    rw [← lintegral_const_mul']
    · exact lintegral_mono_ae hphase
    · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hfin : ENNReal.ofReal P⁻¹ * (∫⁻ t in Ioc (0 : ℝ) P, (∫⁻ y : Space,
        ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
          (repStressPhys Pl K L w (t, y))) ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ))) ≤
      ENNReal.ofReal ((2 * L.ρb Pl K * X) ^ 2) := by
    calc _ ≤ ENNReal.ofReal P⁻¹ * ((ENNReal.ofReal 2 ^ 2 * ENNReal.ofReal (L.ρb Pl K) ^ 2) *
          ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
            ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) w (t, y)‖ ^ 2) := by gcongr
      _ = (ENNReal.ofReal 2 ^ 2 * ENNReal.ofReal (L.ρb Pl K) ^ 2) *
          (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
            ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) w (t, y)‖ ^ 2) := by ring
      _ ≤ (ENNReal.ofReal 2 ^ 2 * ENNReal.ofReal (L.ρb Pl K) ^ 2) * ENNReal.ofReal (X ^ 2) := by
          gcongr; exact hV w
      _ = ENNReal.ofReal ((2 * L.ρb Pl K * X) ^ 2) := by
          rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_pow hρb,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  -- take the square root
  have hroot : (ENNReal.ofReal P⁻¹ * (∫⁻ t in Ioc (0 : ℝ) P, (∫⁻ y : Space,
        ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
          (repStressPhys Pl K L w (t, y))) ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ)))) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (2 * L.ρb Pl K * X) := by
    calc _ ≤ (ENNReal.ofReal ((2 * L.ρb Pl K * X) ^ 2)) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hfin (by norm_num)
      _ = ENNReal.ofReal (2 * L.ρb Pl K * X) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
          congr 1
          rw [← Real.sqrt_eq_rpow]
          exact Real.sqrt_sq (by positivity)
  refine le_trans hroot (ENNReal.ofReal_le_ofReal ?_)
  have hg := gamma_le_gauge Pl L hν1
  have hA : 0 ≤ 2 * K.C0 * C1 * L.ν⁻¹ ^ K.k0 * rhoRep K L * L.ε⁻¹ * ‖w‖ := by positivity
  calc 2 * L.ρb Pl K * X
      = (2 * K.C0 * C1 * L.ν⁻¹ ^ K.k0 * rhoRep K L * L.ε⁻¹ * ‖w‖) *
          Real.exp (gRate Pl / L.ν) := by rw [hρeq, hX]; ring
    _ ≤ (2 * K.C0 * C1 * L.ν⁻¹ ^ K.k0 * rhoRep K L * L.ε⁻¹ * ‖w‖) *
          (L.ν⁻¹ ^ (⌈-Pl.kappa.re⌉₊) * gaugeN Pl L) := mul_le_mul_of_nonneg_left hg hA
    _ = _ := by rw [pow_add]; ring

/-! ## The sequence -/

/-- **`repairSource`** from the leaves `RbFacts`, `RepPhasePointwise`, `VelSliceMeas`,
`HolderPhase`, `VelPhysL2`, `PeriodSmall` (source 5169-5176). -/
theorem repairSource_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hRb : RbFacts) (hpt : RepPhasePointwise) (hmeas : VelSliceMeas) (hH : HolderPhase)
    (hV : VelPhysL2) (hPer : PeriodSmall) : D.RepairSource := by
  obtain ⟨C1, hC1, hV⟩ := hV
  refine ⟨2 * D.K.C0 * C1, D.K.k0 + ⌈-D.Pl.kappa.re⌉₊, ?_⟩
  have hν1 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < 1 :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (Iio_mem_nhds one_pos)
  filter_upwards [hν1, hPer D hst, hst.actual, hst.pins, hst.near] with n h1 h2 h3 h4 h5
  have h4' := h4 0 ⟨by norm_num, by norm_num⟩
  exact repairSourceAt_level D.Pl D.K (D.level n) (D.Sin n) (D.mu n 0) hst.C0_pos h1.le h2
    h3.split (h5 0 ⟨by norm_num, by norm_num⟩) h4'.split hRb hpt hmeas hH C1 hC1
    (fun w => hV D.Pl hst.gamma_pos.le (D.level n) w)

end UnforcedLeray.Short.PartIIIb.Concrete
