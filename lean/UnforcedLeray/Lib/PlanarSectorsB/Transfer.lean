import UnforcedLeray.Lib.PlanarSectorsB.Sector
import UnforcedLeray.Lib.PlanarSpectral
import UnforcedLeray.Analysis.GaussianVortex.SmoothLinCoefficient
import UnforcedLeray.Analysis.Rayleigh.RealSpeed.Profile
import UnforcedLeray.Analysis.Sturm.PotentialIntegrable

/-!
# Transfer of sector eigenvectors to the phase-speed operator (INF10 target G-1)


§5, Level G, target **G-1** (`transfer_sector_eigen`), and risk 7 of §6 (the two coordinate
systems). Manuscript (`paper/main.tex`): the phase-speed operator `T_n = Ω - kΔ_n⁻¹`, its
conjugate `T̃_n = Ω - J𝒦_n` (`eq:st18-t00055`–`t00057`, lines 1281–1301, units `B0069`–`B0071`),
and the transfer of nonreal eigenvectors (`eq:st18-t00061`, lines 1380–1386, unit `B0081`(a)):
if `w ∈ L²_M` (sector `n`) and `T_n w = c w` with `c ∉ ℝ`, then `w = (k/(Ω-c))Δ_n⁻¹w` and the
transferred vector is a `T̃_n` eigenvector; the transfer is injective.

**Coordinates.** The project's phase-speed operator `Sturm.phaseSpeedOp hm = Ω - J N_m`
(`Lib/PlanarSpectral/PhaseSpeed.lean`) acts on `L²(ℝ, dt)` in the logarithmic radius `r = e^t`,
with `N_m = √W (-∂² + m²)⁻¹ √W` (`Sturm.birmanSchwingerOperator`), `W = Wlog`. The transferred
vector of a sector-`n` profile `w` is
`f(t) = √W(t) J(t) ψ(e^t) / (Ω(e^t) - c)`, `ψ = Δ_n⁻¹ w = greenN n w`
(`transferFun`, `transfer`). On an eigenvector it equals `-e^{2t} w(e^t)/√W(t)`, which is the
manuscript's `w ↦ w/√v` followed by the unitary `g ↦ e^t g(e^t)` of `L²(r dr)` onto `L²(dt)`
(since `W(t) = e^{2t} v(e^t)`); the formula used here is in `L²(dt)` for every `w ∈ L²_M`
(`memLp_transferFun`), so no decay of `w/√v` has to be proved separately.

Main declarations (namespace `UnforcedLeray.Planar`):
* `integral_comp_exp_univ`, `minmax_exp_pow`, `greenN_exp`: in log radius,
  `greenN n g (e^t) = -(2n)⁻¹ ∫ e^{-n|t-s|} e^{2s} g(e^s) ds`;
  `greenN_exp_eq_neg_freeResolvent`: `greenN n g (e^t) = -R_n[e^{2s} g(e^s)](t)`;
* `Wlog_mul_J`: `W(t) J(t) = -e^{2t} k(e^t)` (from `radialLinPotential_mul_difference`);
* `phaseSpeedOp_transfer`: `T_n w = c w` (a.e.), `Im c ≠ 0` ⟹ `C_n f = c f`;
* `transfer_eq_zero_iff`, `transfer_ne_zero`: injectivity on eigenvectors;
* `transfer_sector_eigen` (**G-1**): for a sector `m ≠ 0`, `Lsec hM m w = z • w`, `Re z ≠ 0`,
  and `c m = i z` (so `c = iz/m`, `Im c = Re z/m ≠ 0`), the transferred `f` satisfies
  `phaseSpeedOp |m| f = c f`, and `f ≠ 0` whenever `w ≠ 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Planar

open UnforcedLeray.GaussianVortex (radialOmega radialK radialOmega_pos)

/-! ### Logarithmic radius -/

/-- Substitution `ρ = e^s` on the whole line: `∫ e^s g(e^s) ds = ∫₀^∞ g`. -/
theorem integral_comp_exp_univ (g : ℝ → ℂ) :
    ∫ s, Real.exp s • g (Real.exp s) = ∫ ρ in Ioi (0 : ℝ), g ρ := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ hxy => Real.exp_injective hxy) g
  rw [image_univ, Real.range_exp] at h
  rw [h, Measure.restrict_univ]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [abs_of_pos (Real.exp_pos s)]

theorem minmax_exp_pow (n : ℕ) (t s : ℝ) :
    (min (Real.exp t) (Real.exp s) / max (Real.exp t) (Real.exp s)) ^ n =
      Real.exp (-(n : ℝ) * |t - s|) := by
  rcases le_total t s with h | h
  · rw [min_eq_left (Real.exp_le_exp.2 h), max_eq_right (Real.exp_le_exp.2 h), ← Real.exp_sub,
      ← Real.exp_nat_mul, abs_of_nonpos (sub_nonpos.2 h)]
    congr 1
    ring
  · rw [min_eq_right (Real.exp_le_exp.2 h), max_eq_left (Real.exp_le_exp.2 h), ← Real.exp_sub,
      ← Real.exp_nat_mul, abs_of_nonneg (sub_nonneg.2 h)]
    congr 1
    ring

/-- **`greenN` in logarithmic radius**: `greenN n g (e^t) = -(2n)⁻¹ ∫ e^{-n|t-s|} e^{2s} g(e^s) ds`
(the kernel `(min/max)ⁿ` of `eq:st18-t00060` becomes `e^{-n|t-s|}`, tex lines 820–836). -/
theorem greenN_exp (n : ℕ) (g : ℝ → ℂ) (t : ℝ) :
    greenN n g (Real.exp t) = -(((2 * n : ℝ)⁻¹ : ℝ) : ℂ) *
      ∫ s, ((Real.exp (-(n : ℝ) * |t - s|) : ℝ) : ℂ) *
        (((Real.exp (2 * s) : ℝ) : ℂ) * g (Real.exp s)) := by
  rw [greenN, ← integral_comp_exp_univ]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [Complex.real_smul]
  rw [minmax_exp_pow, show (2 : ℝ) * s = s + s by ring, Real.exp_add]
  push_cast
  ring

/-- `greenN n g (e^t) = -R_n[e^{2s} g(e^s)](t)`, with `R_n = (-∂² + n²)⁻¹` the free resolvent
`Sturm.freeResolvent` (convolution with `e^{-n|x|}/(2n)`). -/
theorem greenN_exp_eq_neg_freeResolvent (n : ℕ) (g : ℝ → ℂ) (t : ℝ) :
    greenN n g (Real.exp t) =
      -Sturm.freeResolvent n (fun s => ((Real.exp (2 * s) : ℝ) : ℂ) * g (Real.exp s)) t := by
  rw [greenN_exp, Sturm.freeResolvent, NonUniqueEuler.Sob.EnergyAux.psi0]
  simp only [NonUniqueEuler.Sob.EnergyAux.k0, neg_mul]

/-! ### The coefficient identity `W J = -r² k` -/

/-- `W(t) (Ω(e^t) - a_*) = -e^{2t} k(e^t)`: in log radius the neutral potential is
`W = -r² k / J` (tex lines 820–844), with the removable point handled by the completed
coefficient `radialLinPotential`. -/
theorem Wlog_mul_J (t : ℝ) :
    GaussianPotential.Wlog t * (Sturm.neutralOmega t - Sturm.aStar) =
      -(Real.exp (2 * t) * radialK (Real.exp t)) := by
  rw [← GaussianVortex.radialLinPotential_exp_eq_Wlog, ← GaussianVortex.radialOmega_exp,
    Sturm.aStar, mul_assoc, GaussianVortex.radialLinPotential_mul_difference,
    show (2 : ℝ) * t = t + t by ring, Real.exp_add]
  ring

theorem sqrtPotential_sq (t : ℝ) : Sturm.sqrtPotential t ^ 2 = GaussianPotential.Wlog t :=
  Real.sq_sqrt (Sturm.Wlog_pos t).le

theorem sqrtPotential_pos (t : ℝ) : 0 < Sturm.sqrtPotential t :=
  Real.sqrt_pos.2 (Sturm.Wlog_pos t)

theorem memLp_sqrtPotential :
    MemLp (fun t => (Sturm.sqrtPotential t : ℂ)) 2 (volume : Measure ℝ) := by
  have hm : AEStronglyMeasurable (fun t => (Sturm.sqrtPotential t : ℂ)) volume :=
    (Complex.measurable_ofReal.comp Sturm.measurable_sqrtPotential).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  refine Sturm.integrable_Wlog.congr (Eventually.of_forall fun t => ?_)
  simp only
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, sqrtPotential_sq]

theorem abs_J_le_one (t : ℝ) : |Sturm.neutralOmega t - Sturm.aStar| ≤ 1 := by
  have h1 : Sturm.neutralOmega t ≤ 1 := by
    have := Sturm.phaseSpeed_norm_omega_le t
    rwa [Real.norm_of_nonneg (Sturm.phaseSpeed_omega_pos t).le] at this
  have h2 : 0 < Sturm.neutralOmega t := Sturm.phaseSpeed_omega_pos t
  have h3 : 0 < Sturm.aStar := Real.exp_pos _
  have h4 : Sturm.aStar ≤ 1 := by
    unfold Sturm.aStar
    exact Real.exp_le_one_iff.2 (by norm_num)
  rw [abs_le]
  constructor <;> linarith

theorem norm_omega_sub_ge {c : ℂ} (x : ℝ) : |c.im| ≤ ‖(x : ℂ) - c‖ := by
  have h := Complex.abs_im_le_norm ((x : ℂ) - c)
  simpa using h

/-! ### The transferred vector -/

/-- The transferred profile `f(t) = √W(t) J(t) ψ(e^t) / (Ω(e^t) - c)`, `ψ = greenN n w`
(scoping note §6, risk 7). -/
def transferFun (n : ℕ) (c : ℂ) (w : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Sturm.sqrtPotential t : ℂ) * ((Sturm.neutralOmega t - Sturm.aStar : ℝ) : ℂ) *
    greenN n w (Real.exp t) / ((Sturm.neutralOmega t : ℂ) - c)

theorem continuous_greenN_exp {M : ℝ} (hM : 1 < M) (n : ℕ) (w : ProfL2 M) :
    Continuous fun t => greenN n w (Real.exp t) :=
  (continuousOn_greenN hM n w).comp_continuous Real.continuous_exp (fun t => Real.exp_pos t)

theorem omega_sub_ne_zero {c : ℂ} (hc : c.im ≠ 0) (x : ℝ) : (x : ℂ) - c ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hc this

theorem memLp_transferFun {M : ℝ} (hM : 1 < M) (n : ℕ) {c : ℂ} (hc : c.im ≠ 0)
    (w : ProfL2 M) : MemLp (transferFun n c w) 2 (volume : Measure ℝ) := by
  set B : ℝ := (2 * n : ℝ)⁻¹ * ‖wrepLp hM‖ * ‖w‖ / |c.im| with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hcont : Continuous (transferFun n c w) := by
    have hsq : Continuous Sturm.sqrtPotential := Real.continuous_sqrt.comp Sturm.continuous_Wlog
    have h1 : Continuous fun t => (Sturm.sqrtPotential t : ℂ) :=
      Complex.continuous_ofReal.comp hsq
    have h2 : Continuous fun t => ((Sturm.neutralOmega t - Sturm.aStar : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (Sturm.continuous_neutralOmega.sub continuous_const)
    have h3 := continuous_greenN_exp hM n w
    have h4 : Continuous fun t => (Sturm.neutralOmega t : ℂ) - c :=
      (Complex.continuous_ofReal.comp Sturm.continuous_neutralOmega).sub continuous_const
    exact ((h1.mul h2).mul h3).div h4 (fun t => omega_sub_ne_zero hc _)
  refine (memLp_sqrtPotential.const_smul ((B : ℝ) : ℂ)).of_le hcont.aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  have hg := norm_greenN_le_wrep hM n (Real.exp_pos t) w
  have hd := norm_omega_sub_ge (c := c) (Sturm.neutralOmega t)
  have hcim : 0 < |c.im| := abs_pos.2 hc
  have hcim' : |c.im| ≠ 0 := hcim.ne'
  have hJ := abs_J_le_one t
  have hs := (sqrtPotential_pos t).le
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hB0,
    Complex.norm_real, Real.norm_of_nonneg hs, transferFun, norm_div, norm_mul, norm_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hs, Real.norm_eq_abs]
  rw [div_le_iff₀ (hcim.trans_le hd)]
  calc Sturm.sqrtPotential t * |Sturm.neutralOmega t - Sturm.aStar| *
        ‖greenN n (⇑w) (Real.exp t)‖
      ≤ Sturm.sqrtPotential t * 1 * ((2 * n : ℝ)⁻¹ * ‖wrepLp hM‖ * ‖w‖) := by gcongr
    _ = B * Sturm.sqrtPotential t * |c.im| := by
        rw [hB]
        field_simp
    _ ≤ B * Sturm.sqrtPotential t * ‖(Sturm.neutralOmega t : ℂ) - c‖ := by gcongr

/-- **The transfer** `w ↦ √W J (greenN n w)(e^t) / (Ω(e^t) - c)` into `L²(ℝ, dt)`. -/
def transfer {M : ℝ} (hM : 1 < M) (n : ℕ) {c : ℂ} (hc : c.im ≠ 0) (w : ProfL2 M) :
    Sturm.ComplexL2 :=
  (memLp_transferFun hM n hc w).toLp _

theorem coeFn_transfer {M : ℝ} (hM : 1 < M) (n : ℕ) {c : ℂ} (hc : c.im ≠ 0) (w : ProfL2 M) :
    ⇑(transfer hM n hc w) =ᵐ[volume] transferFun n c w :=
  (memLp_transferFun hM n hc w).coeFn_toLp

/-! ### The eigenvalue identity -/

/-- On an eigenvector of `T_n = Ω - kΔ_n⁻¹`, the Green streamfunction in log radius solves
`ψ(e^t) = R_n[W J ψ(e^·)/(Ω - c)](t)`: this is `eq:st18-t00061` (tex 1381–1384) in the
coordinates of the compiled Sturm layer. -/
theorem freeResolvent_eigen {M : ℝ} (hM : 1 < M) (n : ℕ) {c : ℂ} (hc : c.im ≠ 0)
    {w : ProfL2 M}
    (hw : ∀ᵐ r ∂profileMeasure M,
      (radialOmega r : ℂ) * w r - (radialK r : ℂ) * greenN n w r = c * w r) (t : ℝ) :
    Sturm.freeResolvent n (fun s => (Sturm.sqrtPotential s : ℂ) * transferFun n c w s) t =
      greenN n w (Real.exp t) := by
  have hw' : (w : ℝ → ℂ) =ᵐ[profileMeasure M]
      fun r => (radialK r : ℂ) * greenN n w r / ((radialOmega r : ℂ) - c) := by
    filter_upwards [hw] with r hr
    rw [eq_div_iff (omega_sub_ne_zero hc _)]
    linear_combination hr
  have key : ∀ s : ℝ, (Sturm.sqrtPotential s : ℂ) * transferFun n c w s =
      -(((Real.exp (2 * s) : ℝ) : ℂ) * ((radialK (Real.exp s) : ℂ) *
        greenN n w (Real.exp s) / ((radialOmega (Real.exp s) : ℂ) - c))) := by
    intro s
    have hWJ := Wlog_mul_J s
    have hWJc : ((GaussianPotential.Wlog s : ℝ) : ℂ) *
        ((Sturm.neutralOmega s - Sturm.aStar : ℝ) : ℂ) =
        -(((Real.exp (2 * s) : ℝ) : ℂ) * (radialK (Real.exp s) : ℂ)) := by
      rw [← Complex.ofReal_mul, hWJ]
      push_cast
      ring
    have hΩ : radialOmega (Real.exp s) = Sturm.neutralOmega s := GaussianVortex.radialOmega_exp s
    have hsq : (Sturm.sqrtPotential s : ℂ) * (Sturm.sqrtPotential s : ℂ) =
        (GaussianPotential.Wlog s : ℂ) := by
      rw [← Complex.ofReal_mul, ← sq, sqrtPotential_sq]
    rw [hΩ]
    calc (Sturm.sqrtPotential s : ℂ) * transferFun n c w s
        = ((Sturm.sqrtPotential s : ℂ) * (Sturm.sqrtPotential s : ℂ)) *
            ((Sturm.neutralOmega s - Sturm.aStar : ℝ) : ℂ) * greenN n w (Real.exp s) /
              ((Sturm.neutralOmega s : ℂ) - c) := by
          unfold transferFun
          ring
      _ = -(((Real.exp (2 * s) : ℝ) : ℂ) * ((radialK (Real.exp s) : ℂ) *
            greenN n w (Real.exp s) / ((Sturm.neutralOmega s : ℂ) - c))) := by
          rw [hsq, hWJc]
          ring
  rw [greenN_congr n hw' (Real.exp t), greenN_exp_eq_neg_freeResolvent]
  simp only [Sturm.freeResolvent, NonUniqueEuler.Sob.EnergyAux.psi0]
  rw [← mul_neg, ← integral_neg]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only
  rw [key s]
  ring

/-- **The transferred vector is a phase-speed eigenvector** (`eq:st18-t00057`, tex lines
1296–1301, and `eq:st18-t00061`, tex lines 1380–1386): if `Ω w - k Δ_n⁻¹ w = c w` a.e. with
`Im c ≠ 0`, then `C_n f = c f` for `f = transfer hM n hc w`, where `C_n = Ω - J N_n` is the
compiled-layer phase-speed operator. -/
theorem phaseSpeedOp_transfer {M : ℝ} (hM : 1 < M) {n : ℕ} (hn : 0 < (n : ℝ)) {c : ℂ}
    (hc : c.im ≠ 0) {w : ProfL2 M}
    (hw : ∀ᵐ r ∂profileMeasure M,
      (radialOmega r : ℂ) * w r - (radialK r : ℂ) * greenN n w r = c * w r) :
    Sturm.phaseSpeedOp hn (transfer hM n hc w) = c • transfer hM n hc w := by
  set f := transfer hM n hc w with hf
  have hPf : ⇑(Sturm.complexPotentialSqrtOperator f) =ᵐ[volume]
      fun s => (Sturm.sqrtPotential s : ℂ) * transferFun n c w s := by
    filter_upwards [Sturm.coeFn_complexPotentialSqrtOperator f, coeFn_transfer hM n hc w]
      with s h1 h2
    rw [h1, h2]
  have hRPf : ⇑(Sturm.freeResolventOperator hn (Sturm.complexPotentialSqrtOperator f))
      =ᵐ[volume] fun t => greenN n w (Real.exp t) := by
    filter_upwards [Sturm.coeFn_freeResolventOperator hn (Sturm.complexPotentialSqrtOperator f)]
      with t ht
    rw [ht, ← freeResolvent_eigen hM n hc hw t]
    simp only [Sturm.freeResolvent, NonUniqueEuler.Sob.EnergyAux.psi0]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hPf] with s hs
    rw [hs]
  have hBS : ⇑(Sturm.birmanSchwingerOperator hn f) =ᵐ[volume]
      fun t => (Sturm.sqrtPotential t : ℂ) * greenN n w (Real.exp t) := by
    rw [Sturm.birmanSchwingerOperator_apply]
    filter_upwards [Sturm.coeFn_complexPotentialSqrtOperator
      (Sturm.freeResolventOperator hn (Sturm.complexPotentialSqrtOperator f)), hRPf] with t h1 h2
    rw [h1, h2]
  have e : Sturm.phaseSpeedOp hn f =
      Sturm.omegaOp f - Sturm.JOp (Sturm.birmanSchwingerOperator hn f) := rfl
  rw [e]
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (Sturm.omegaOp f) (Sturm.JOp (Sturm.birmanSchwingerOperator hn f)),
    Sturm.coeFn_omegaOp f, Sturm.coeFn_JOp (Sturm.birmanSchwingerOperator hn f), hBS,
    Lp.coeFn_smul c f, coeFn_transfer hM n hc w] with t h1 h2 h3 h4 h5 h6
  rw [h1, Pi.sub_apply, h2, h3, h4, h5, Pi.smul_apply, h6, smul_eq_mul]
  have hne := omega_sub_ne_zero hc (Sturm.neutralOmega t)
  unfold transferFun
  field_simp
  ring

/-- **Injectivity on eigenvectors** (`paper/main.tex` line 1386, "transfers the complete chain
injectively"): if `Ω w - kΔ_n⁻¹w = c w` with `Im c ≠ 0` and the transferred vector vanishes,
then `w = 0`. -/
theorem eq_zero_of_transfer_eq_zero {M : ℝ} (hM : 1 < M) {n : ℕ} {c : ℂ} (hc : c.im ≠ 0)
    {w : ProfL2 M}
    (hw : ∀ᵐ r ∂profileMeasure M,
      (radialOmega r : ℂ) * w r - (radialK r : ℂ) * greenN n w r = c * w r)
    (h0 : transfer hM n hc w = 0) : w = 0 := by
  have h1 : ∀ᵐ t ∂(volume : Measure ℝ), transferFun n c w t = 0 := by
    have hz := Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)
    rw [← h0] at hz
    filter_upwards [hz, coeFn_transfer hM n hc w] with t h1 h2
    rw [← h2, h1]
    rfl
  have hnull : (volume : Measure ℝ) {t : ℝ | Sturm.neutralOmega t = Sturm.aStar} = 0 :=
    Set.Subsingleton.measure_zero
      (fun a ha b hb => Rayleigh.RealSpeed.neutralOmega_injective (ha.trans hb.symm)) _
  have h2 : ∀ᵐ t ∂(volume : Measure ℝ), Sturm.neutralOmega t ≠ Sturm.aStar := by
    rw [ae_iff]
    simpa using hnull
  have h3 : (fun t => greenN n w (Real.exp t)) =ᵐ[volume] fun _ => (0 : ℂ) := by
    filter_upwards [h1, h2] with t ht hJ
    unfold transferFun at ht
    rw [div_eq_zero_iff, mul_eq_zero, mul_eq_zero] at ht
    rcases ht with ((h | h) | h) | h
    · exact absurd h (Complex.ofReal_ne_zero.2 (sqrtPotential_pos t).ne')
    · exact absurd h (Complex.ofReal_ne_zero.2 (sub_ne_zero.2 hJ))
    · exact h
    · exact absurd h (omega_sub_ne_zero hc _)
  have h4 : (fun t => greenN n w (Real.exp t)) = fun _ => (0 : ℂ) :=
    (Continuous.ae_eq_iff_eq volume (continuous_greenN_exp hM n w) continuous_const).1 h3
  apply Lp.ext
  filter_upwards [hw, ae_profile_pos M, Lp.coeFn_zero ℂ 2 (profileMeasure M)] with r hr hr0 hz
  have hψ : greenN n w r = 0 := by
    have := congrFun h4 (Real.log r)
    simpa [Real.exp_log hr0] using this
  rw [hψ, mul_zero, sub_zero] at hr
  have hm : ((radialOmega r : ℂ) - c) * w r = 0 := by linear_combination hr
  rw [hz]
  exact (mul_eq_zero.1 hm).resolve_left (omega_sub_ne_zero hc _)

/-- **G-1** (`transfer_sector_eigen`; scoping note §5, Level G; `paper/main.tex` lines
1380–1386, unit `B0081`(a), and line 1388, unit `B0082`). Let `m ≠ 0` be a sector, `w` an
eigenvector of the sector generator, `Lsec hM m w = z • w`, with `Re z ≠ 0` (in particular
`Re z > 0`), and let `c` be the phase speed, `c m = i z` (`c = iz/m`). Then `Im c ≠ 0`, the
transferred vector `f = transfer hM |m| hc w ∈ L²(ℝ, dt)` satisfies `C_{|m|} f = c f` for the
compiled phase-speed operator `C_{|m|} = Ω - J N_{|m|}`, and `f ≠ 0` whenever `w ≠ 0`. -/
theorem transfer_sector_eigen {M : ℝ} (hM : 1 < M) {m : ℤ} (hm : m ≠ 0) {z c : ℂ}
    (hz : z.re ≠ 0) (hcz : c * m = Complex.I * z) {w : ProfL2 M}
    (hLw : Lsec hM m w = z • w) :
    ∃ (hc : c.im ≠ 0) (hpos : 0 < (m.natAbs : ℝ)),
      Sturm.phaseSpeedOp hpos (transfer hM m.natAbs hc w) =
          c • transfer hM m.natAbs hc w ∧
        (w ≠ 0 → transfer hM m.natAbs hc w ≠ 0) := by
  have hc : c.im ≠ 0 := by
    intro h
    have h1 := congrArg Complex.im hcz
    simp [Complex.mul_im, h] at h1
    exact hz h1.symm
  have hpos : 0 < (m.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.2 hm
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hw : ∀ᵐ r ∂profileMeasure M, (radialOmega r : ℂ) * w r -
      (radialK r : ℂ) * greenN m.natAbs w r = c * w r := by
    have hz' := Lp.coeFn_smul z w
    rw [← hLw] at hz'
    filter_upwards [coeFn_Lsec hM m w, hz'] with r h1 h2
    rw [h1, Pi.smul_apply, smul_eq_mul] at h2
    apply mul_left_cancel₀ hmC
    linear_combination Complex.I * h2 - w r * hcz +
      ((m : ℂ) * (radialOmega r : ℂ) * w r - (m : ℂ) * (radialK r : ℂ) * greenN m.natAbs w r) *
        Complex.I_sq
  refine ⟨hc, hpos, phaseSpeedOp_transfer hM hpos hc hw, fun hw0 ht => hw0 ?_⟩
  exact eq_zero_of_transfer_eq_zero hM hc hw ht

end UnforcedLeray.Planar
