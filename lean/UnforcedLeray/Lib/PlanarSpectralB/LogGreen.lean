import UnforcedLeray.Lib.PlanarSectorsB.Transfer
import UnforcedLeray.Lib.Semigroups.Multiplication

/-!
# The log-radius Green map and the intertwining identity off the eigenspace (INF10 G-2, G-3)


§5, Level G (targets G-2 and G-3) and risk 7 of §6 (two coordinate systems). Manuscript
(`paper/main.tex`): the conjugated phase-speed operator `T̃_n = Ω - J𝒦_n` and the intertwining
identity `eq:st18-t00057` (lines 1296–1301, unit `B0071`), the Green formula `eq:st18-t00060`
and the eigenvector transfer `eq:st18-t00061` (lines 1366–1388, units `B0079`, `B0081`).

The compiled draft `Lib/PlanarSectorsB/Transfer.lean` (target G-1) proves that the transferred
vector `transfer w = √W J ψ(e^t)/(Ω - c)`, `ψ = Δ_n⁻¹ w`, of an *eigenvector* `w` is a
phase-speed eigenvector. This file proves the identity for *every* `w ∈ L²_M`:

* `greenLogOp hM n`: the bounded map `w ↦ √W(t) J(t) (Δ_n⁻¹w)(e^t)` from `L²_M` profiles into
  `L²(ℝ, dt)`; `transfer_eq`: `transfer = (Ω - c)⁻¹ · greenLogOp` (so the transfer is linear);
* `phaseSpeedOp_transfer_sub` (the intertwining identity off the eigenspace): if
  `(Ω - c) u = (Ω - c) w - k Δ_n⁻¹w`, then `(C_n - c) transfer w = greenLogOp u`;
* `greenLog_divP_eigen`: on an eigenvector `q`, `greenLogOp ((Ω - c)⁻¹ q) = F - (C_n - c)((Ω - c)⁻¹F)`
  with `F = transfer q`;
* `inner_star_B_phaseSpeed_sub`: for a phase-speed eigenvector `F`, the bilinear form
  `G ↦ ∫ F (1 - N_m) G` annihilates the range of `C_m - c` (from `eq:st18-t00058`);
* `inner_star_B_ne_zero`: for `m = 2` and `Im c ≠ 0` the bilinear pairing `∫ F (1 - N_2) F` of an
  eigenvector is nonzero (the compiled `Sturm.bilinear_pairing_ne_zero` assumes `Im c > 0`).

Namespace `UnforcedLeray.Planar`. Status: draft; Theorem A is not proved.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Planar

open UnforcedLeray.GaussianVortex (radialOmega radialK radialOmega_pos)

/-! ### Linear algebra of `greenN` -/

theorem greenN_sub {M : ℝ} (hM : 1 < M) (n : ℕ) (f g : ProfL2 M) {r : ℝ} (hr : 0 < r) :
    greenN n (⇑(f - g)) r = greenN n f r - greenN n g r := by
  rw [greenN_eq_inner hM n hr, greenN_eq_inner hM n hr, greenN_eq_inner hM n hr,
    inner_sub_right]
  ring

/-! ### The log-radius Green map -/

/-- `√W(t) J(t) ψ(e^t)`, `ψ = greenN n w`: the numerator of the transferred vector. -/
def greenLogFun (n : ℕ) (w : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Sturm.sqrtPotential t : ℂ) * ((Sturm.neutralOmega t - Sturm.aStar : ℝ) : ℂ) *
    greenN n w (Real.exp t)

theorem continuous_greenLogFun {M : ℝ} (hM : 1 < M) (n : ℕ) (w : ProfL2 M) :
    Continuous (greenLogFun n w) := by
  have hsq : Continuous Sturm.sqrtPotential := Real.continuous_sqrt.comp Sturm.continuous_Wlog
  exact ((Complex.continuous_ofReal.comp hsq).mul
    (Complex.continuous_ofReal.comp (Sturm.continuous_neutralOmega.sub continuous_const))).mul
    (continuous_greenN_exp hM n w)

theorem norm_greenLogFun_le {M : ℝ} (hM : 1 < M) (n : ℕ) (w : ProfL2 M) (t : ℝ) :
    ‖greenLogFun n w t‖ ≤ ((2 * n : ℝ)⁻¹ * ‖wrepLp hM‖ * ‖w‖) * Sturm.sqrtPotential t := by
  have hg := norm_greenN_le_wrep hM n (Real.exp_pos t) w
  have hJ := abs_J_le_one t
  have hs := (sqrtPotential_pos t).le
  rw [greenLogFun, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hs, Real.norm_eq_abs]
  calc Sturm.sqrtPotential t * |Sturm.neutralOmega t - Sturm.aStar| *
        ‖greenN n (⇑w) (Real.exp t)‖
      ≤ Sturm.sqrtPotential t * 1 * ((2 * n : ℝ)⁻¹ * ‖wrepLp hM‖ * ‖w‖) := by gcongr
    _ = ((2 * n : ℝ)⁻¹ * ‖wrepLp hM‖ * ‖w‖) * Sturm.sqrtPotential t := by ring

theorem memLp_greenLogFun {M : ℝ} (hM : 1 < M) (n : ℕ) (w : ProfL2 M) :
    MemLp (greenLogFun n w) 2 (volume : Measure ℝ) := by
  set B : ℝ := (2 * n : ℝ)⁻¹ * ‖wrepLp hM‖ * ‖w‖ with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  refine (memLp_sqrtPotential.const_smul ((B : ℝ) : ℂ)).of_le
    (continuous_greenLogFun hM n w).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hB0,
    Complex.norm_real, Real.norm_of_nonneg (sqrtPotential_pos t).le]
  exact norm_greenLogFun_le hM n w t

/-- `√W` as an element of `L²(ℝ, dt)`. -/
def sqrtWLp : Sturm.ComplexL2 := memLp_sqrtPotential.toLp _

/-- The log-radius Green map as a linear map. -/
def greenLogLin {M : ℝ} (hM : 1 < M) (n : ℕ) : ProfL2 M →ₗ[ℂ] Sturm.ComplexL2 where
  toFun w := (memLp_greenLogFun hM n w).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(memLp_greenLogFun hM n (f + g)).coeFn_toLp,
      (memLp_greenLogFun hM n f).coeFn_toLp, (memLp_greenLogFun hM n g).coeFn_toLp,
      Lp.coeFn_add ((memLp_greenLogFun hM n f).toLp _) ((memLp_greenLogFun hM n g).toLp _)]
      with t h1 h2 h3 h4
    rw [h1, h4, Pi.add_apply, h2, h3, greenLogFun, greenLogFun, greenLogFun,
      greenN_add hM n f g (Real.exp_pos t)]
    ring
  map_smul' a f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [(memLp_greenLogFun hM n (a • f)).coeFn_toLp,
      (memLp_greenLogFun hM n f).coeFn_toLp,
      Lp.coeFn_smul a ((memLp_greenLogFun hM n f).toLp _)] with t h1 h2 h3
    rw [h1, h3, Pi.smul_apply, h2, smul_eq_mul, greenLogFun, greenLogFun,
      greenN_smul hM n a f (Real.exp_pos t)]
    ring

theorem norm_greenLogLin_le {M : ℝ} (hM : 1 < M) (n : ℕ) (w : ProfL2 M) :
    ‖greenLogLin hM n w‖ ≤ ((2 * n : ℝ)⁻¹ * ‖wrepLp hM‖ * ‖sqrtWLp‖) * ‖w‖ := by
  have h : ‖greenLogLin hM n w‖ ≤ ((2 * n : ℝ)⁻¹ * ‖wrepLp hM‖ * ‖w‖) * ‖sqrtWLp‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [(memLp_greenLogFun hM n w).coeFn_toLp,
      memLp_sqrtPotential.coeFn_toLp] with t h1 h2
    change ‖((memLp_greenLogFun hM n w).toLp _ : Sturm.ComplexL2) t‖ ≤ _
    rw [h1, sqrtWLp, h2, Complex.norm_real, Real.norm_of_nonneg (sqrtPotential_pos t).le]
    exact norm_greenLogFun_le hM n w t
  calc _ ≤ _ := h
    _ = _ := by ring

/-- **The log-radius Green map** `w ↦ √W J (Δ_n⁻¹w)(e^·)`, bounded from `L²_M` profiles into
`L²(ℝ, dt)`. -/
def greenLogOp {M : ℝ} (hM : 1 < M) (n : ℕ) : ProfL2 M →L[ℂ] Sturm.ComplexL2 :=
  (greenLogLin hM n).mkContinuous _ (norm_greenLogLin_le hM n)

theorem coeFn_greenLogOp {M : ℝ} (hM : 1 < M) (n : ℕ) (w : ProfL2 M) :
    ⇑(greenLogOp hM n w) =ᵐ[volume] greenLogFun n w :=
  (memLp_greenLogFun hM n w).coeFn_toLp

/-! ### Division by `Ω - c` -/

theorem continuous_inv_neutral_sub {c : ℂ} (hc : c.im ≠ 0) :
    Continuous fun t => ((Sturm.neutralOmega t : ℂ) - c)⁻¹ :=
  ((Complex.continuous_ofReal.comp Sturm.continuous_neutralOmega).sub continuous_const).inv₀
    fun t => omega_sub_ne_zero hc _

theorem continuous_inv_radial_sub {c : ℂ} (hc : c.im ≠ 0) :
    Continuous fun r => ((radialOmega r : ℂ) - c)⁻¹ :=
  ((Complex.continuous_ofReal.comp B0012.continuous_radialOmega).sub continuous_const).inv₀
    fun r => omega_sub_ne_zero hc _

theorem norm_inv_sub_le {c : ℂ} (hc : c.im ≠ 0) (x : ℝ) : ‖((x : ℂ) - c)⁻¹‖ ≤ |c.im|⁻¹ := by
  rw [norm_inv]
  exact inv_anti₀ (abs_pos.2 hc) (norm_omega_sub_ge x)

/-- Multiplication by `(Ω(e^t) - c)⁻¹` on `L²(ℝ, dt)`. -/
def divLog {c : ℂ} (hc : c.im ≠ 0) : Sturm.ComplexL2 →L[ℂ] Sturm.ComplexL2 :=
  Infra.Mult.mulOp (fun t => ((Sturm.neutralOmega t : ℂ) - c)⁻¹)
    (continuous_inv_neutral_sub hc).aestronglyMeasurable
    (Eventually.of_forall fun t => norm_inv_sub_le hc _)

theorem coeFn_divLog {c : ℂ} (hc : c.im ≠ 0) (F : Sturm.ComplexL2) :
    ⇑(divLog hc F) =ᵐ[volume] fun t => ((Sturm.neutralOmega t : ℂ) - c)⁻¹ * F t :=
  Infra.Mult.coeFn_mulOp _ _ F

/-- Multiplication by `(Ω(r) - c)⁻¹` on `L²_M` profiles. -/
def divP (M : ℝ) {c : ℂ} (hc : c.im ≠ 0) : ProfL2 M →L[ℂ] ProfL2 M :=
  Infra.Mult.mulOp (fun r => ((radialOmega r : ℂ) - c)⁻¹)
    (continuous_inv_radial_sub hc).aestronglyMeasurable
    (Eventually.of_forall fun r => norm_inv_sub_le hc _)

theorem coeFn_divP (M : ℝ) {c : ℂ} (hc : c.im ≠ 0) (w : ProfL2 M) :
    ⇑(divP M hc w) =ᵐ[profileMeasure M] fun r => ((radialOmega r : ℂ) - c)⁻¹ * w r :=
  Infra.Mult.coeFn_mulOp _ _ w

/-- `transfer = (Ω - c)⁻¹ · greenLogOp`; in particular the transfer is linear. -/
theorem transfer_eq {M : ℝ} (hM : 1 < M) (n : ℕ) {c : ℂ} (hc : c.im ≠ 0) (w : ProfL2 M) :
    transfer hM n hc w = divLog hc (greenLogOp hM n w) := by
  apply Lp.ext
  filter_upwards [coeFn_transfer hM n hc w, coeFn_divLog hc (greenLogOp hM n w),
    coeFn_greenLogOp hM n w] with t h1 h2 h3
  rw [h1, h2, h3, transferFun, greenLogFun, div_eq_inv_mul]

theorem transfer_sub {M : ℝ} (hM : 1 < M) (n : ℕ) {c : ℂ} (hc : c.im ≠ 0) (w w' : ProfL2 M) :
    transfer hM n hc (w - w') = transfer hM n hc w - transfer hM n hc w' := by
  rw [transfer_eq, transfer_eq, transfer_eq, map_sub, map_sub]

theorem transfer_smul {M : ℝ} (hM : 1 < M) (n : ℕ) {c : ℂ} (hc : c.im ≠ 0) (a : ℂ)
    (w : ProfL2 M) : transfer hM n hc (a • w) = a • transfer hM n hc w := by
  rw [transfer_eq, transfer_eq, map_smul, map_smul]

/-! ### The phase-speed operator on `√W`-images of profiles -/

/-- The pointwise identity `√W(s) transferFun(s) = -e^{2s} (kψ/(Ω - c))(e^s)` (any `w`). -/
theorem sqrtW_mul_transferFun (n : ℕ) (c : ℂ) (w : ℝ → ℂ) (s : ℝ) :
    (Sturm.sqrtPotential s : ℂ) * transferFun n c w s =
      -(((Real.exp (2 * s) : ℝ) : ℂ) * ((radialK (Real.exp s) : ℂ) *
        greenN n w (Real.exp s) / ((radialOmega (Real.exp s) : ℂ) - c))) := by
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

/-- If `√W G = -e^{2s} g(e^s)` a.e., then `R_n(√W G)(t) = (Δ_n⁻¹ g)(e^t)`
(`greenN_exp_eq_neg_freeResolvent`). -/
theorem freeResolventOperator_sqrtW {n : ℕ} (hn : 0 < (n : ℝ)) (G : Sturm.ComplexL2)
    (g : ℝ → ℂ)
    (hG : ∀ᵐ s ∂(volume : Measure ℝ), (Sturm.sqrtPotential s : ℂ) * G s =
      -(((Real.exp (2 * s) : ℝ) : ℂ) * g (Real.exp s))) :
    ⇑(Sturm.freeResolventOperator hn (Sturm.complexPotentialSqrtOperator G)) =ᵐ[volume]
      fun t => greenN n g (Real.exp t) := by
  filter_upwards [Sturm.coeFn_freeResolventOperator hn (Sturm.complexPotentialSqrtOperator G)]
    with t ht
  rw [ht, greenN_exp_eq_neg_freeResolvent]
  simp only [Sturm.freeResolvent, NonUniqueEuler.Sob.EnergyAux.psi0]
  rw [← mul_neg, ← integral_neg]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [Sturm.coeFn_complexPotentialSqrtOperator G, hG] with s h1 h2
  rw [h1, h2]
  ring

/-- The phase-speed operator on a vector `G` with `√W G = -e^{2s} g(e^s)`:
`C_n G = Ω G - J √W (Δ_n⁻¹ g)(e^t)`. -/
theorem coeFn_phaseSpeedOp_of_sqrtW {n : ℕ} (hn : 0 < (n : ℝ)) (G : Sturm.ComplexL2)
    (g : ℝ → ℂ)
    (hG : ∀ᵐ s ∂(volume : Measure ℝ), (Sturm.sqrtPotential s : ℂ) * G s =
      -(((Real.exp (2 * s) : ℝ) : ℂ) * g (Real.exp s))) :
    ⇑(Sturm.phaseSpeedOp hn G) =ᵐ[volume] fun t =>
      (Sturm.neutralOmega t : ℂ) * G t - ((Sturm.neutralOmega t - Sturm.aStar : ℝ) : ℂ) *
        ((Sturm.sqrtPotential t : ℂ) * greenN n g (Real.exp t)) := by
  have hBS : ⇑(Sturm.birmanSchwingerOperator hn G) =ᵐ[volume]
      fun t => (Sturm.sqrtPotential t : ℂ) * greenN n g (Real.exp t) := by
    rw [Sturm.birmanSchwingerOperator_apply]
    filter_upwards [Sturm.coeFn_complexPotentialSqrtOperator
      (Sturm.freeResolventOperator hn (Sturm.complexPotentialSqrtOperator G)),
      freeResolventOperator_sqrtW hn G g hG] with t h1 h2
    rw [h1, h2]
  have e : Sturm.phaseSpeedOp hn G =
      Sturm.omegaOp G - Sturm.JOp (Sturm.birmanSchwingerOperator hn G) := rfl
  rw [e]
  filter_upwards [Lp.coeFn_sub (Sturm.omegaOp G) (Sturm.JOp (Sturm.birmanSchwingerOperator hn G)),
    Sturm.coeFn_omegaOp G, Sturm.coeFn_JOp (Sturm.birmanSchwingerOperator hn G), hBS]
    with t h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, h3, h4]

/-- **The intertwining identity off the eigenspace** (`eq:st18-t00057`, tex lines 1296–1301, in
the coordinates of `transfer`): if `(Ω - c) u = (Ω - c) w - k Δ_n⁻¹ w` a.e., then
`(C_n - c) transfer w = greenLogOp u`. For an eigenvector (`u = 0`) this is
`phaseSpeedOp_transfer`. -/
theorem phaseSpeedOp_transfer_sub {M : ℝ} (hM : 1 < M) {n : ℕ} (hn : 0 < (n : ℝ)) {c : ℂ}
    (hc : c.im ≠ 0) (w u : ProfL2 M)
    (hu : ∀ᵐ r ∂profileMeasure M, ((radialOmega r : ℂ) - c) * u r =
      ((radialOmega r : ℂ) - c) * w r - (radialK r : ℂ) * greenN n w r) :
    Sturm.phaseSpeedOp hn (transfer hM n hc w) - c • transfer hM n hc w =
      greenLogOp hM n u := by
  set F := transfer hM n hc w with hF
  set g : ℝ → ℂ := fun r => (radialK r : ℂ) * greenN n w r / ((radialOmega r : ℂ) - c) with hg
  have hG : ∀ᵐ s ∂(volume : Measure ℝ), (Sturm.sqrtPotential s : ℂ) * F s =
      -(((Real.exp (2 * s) : ℝ) : ℂ) * g (Real.exp s)) := by
    filter_upwards [coeFn_transfer hM n hc w] with s hs
    rw [hs]
    exact sqrtW_mul_transferFun n c w s
  have hgu : g =ᵐ[profileMeasure M] ⇑(w - u) := by
    filter_upwards [hu, Lp.coeFn_sub w u] with r hr hsub
    rw [hsub, Pi.sub_apply, hg]
    simp only
    rw [div_eq_iff (omega_sub_ne_zero hc _)]
    linear_combination hr
  have hgreen : ∀ t : ℝ, greenN n g (Real.exp t) =
      greenN n w (Real.exp t) - greenN n u (Real.exp t) := by
    intro t
    rw [greenN_congr n hgu, greenN_sub hM n w u (Real.exp_pos t)]
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (Sturm.phaseSpeedOp hn F) (c • F),
    coeFn_phaseSpeedOp_of_sqrtW hn F g hG, Lp.coeFn_smul c F, coeFn_transfer hM n hc w,
    coeFn_greenLogOp hM n u] with t h1 h2 h3 h4 h5
  rw [h1, Pi.sub_apply, h2, h3, Pi.smul_apply, h4, h5, smul_eq_mul, hgreen t, transferFun,
    greenLogFun]
  have hne := omega_sub_ne_zero hc (Sturm.neutralOmega t)
  field_simp
  ring

/-- **The eigenvector identity for the eigenfunctional** (route of target G-3): if `q` is a
nonreal phase-speed eigenvector in profile form (`Ω q - kΔ_n⁻¹q = c q`) and `F = transfer q`,
then `greenLogOp ((Ω - c)⁻¹ q) = F - (C_n - c)((Ω - c)⁻¹ F)`. -/
theorem greenLog_divP_eigen {M : ℝ} (hM : 1 < M) {n : ℕ} (hn : 0 < (n : ℝ)) {c : ℂ}
    (hc : c.im ≠ 0) {q : ProfL2 M}
    (hq : ∀ᵐ r ∂profileMeasure M,
      (radialOmega r : ℂ) * q r - (radialK r : ℂ) * greenN n q r = c * q r) :
    greenLogOp hM n (divP M hc q) = transfer hM n hc q -
      (Sturm.phaseSpeedOp hn (divLog hc (transfer hM n hc q)) -
        c • divLog hc (transfer hM n hc q)) := by
  set F := transfer hM n hc q with hF
  set G := divLog hc F with hGdef
  set g : ℝ → ℂ := fun r => (radialK r : ℂ) * greenN n q r / ((radialOmega r : ℂ) - c) /
    ((radialOmega r : ℂ) - c) with hg
  have hG : ∀ᵐ s ∂(volume : Measure ℝ), (Sturm.sqrtPotential s : ℂ) * G s =
      -(((Real.exp (2 * s) : ℝ) : ℂ) * g (Real.exp s)) := by
    filter_upwards [coeFn_divLog hc F, coeFn_transfer hM n hc q] with s h1 h2
    rw [h1, h2]
    have hk := sqrtW_mul_transferFun n c q s
    have hΩ : radialOmega (Real.exp s) = Sturm.neutralOmega s := GaussianVortex.radialOmega_exp s
    rw [hg]
    simp only
    rw [hΩ] at hk ⊢
    calc (Sturm.sqrtPotential s : ℂ) * (((Sturm.neutralOmega s : ℂ) - c)⁻¹ * transferFun n c q s)
        = ((Sturm.neutralOmega s : ℂ) - c)⁻¹ *
            ((Sturm.sqrtPotential s : ℂ) * transferFun n c q s) := by ring
      _ = _ := by rw [hk]; ring
  have hgq : g =ᵐ[profileMeasure M] ⇑(divP M hc q) := by
    filter_upwards [hq, coeFn_divP M hc q] with r hr hd
    rw [hd, hg]
    simp only
    have hne := omega_sub_ne_zero hc (radialOmega r)
    have hq' : (radialK r : ℂ) * greenN n q r = ((radialOmega r : ℂ) - c) * q r := by
      linear_combination -hr
    rw [hq']
    field_simp
  apply Lp.ext
  filter_upwards [coeFn_greenLogOp hM n (divP M hc q),
    Lp.coeFn_sub F (Sturm.phaseSpeedOp hn G - c • G),
    Lp.coeFn_sub (Sturm.phaseSpeedOp hn G) (c • G), coeFn_phaseSpeedOp_of_sqrtW hn G g hG,
    Lp.coeFn_smul c G, coeFn_divLog hc F] with t h1 h2 h3 h4 h5 h6
  rw [h1, h2, Pi.sub_apply, h3, Pi.sub_apply, h4, h5, Pi.smul_apply, h6, smul_eq_mul,
    greenLogFun, greenN_congr n hgq]
  have hne := omega_sub_ne_zero hc (Sturm.neutralOmega t)
  field_simp
  ring

/-! ### The bilinear pairing -/

/-- For a phase-speed eigenvector `F` (`C_m F = c F`), the bilinear form
`G ↦ ⟪star F, (1 - N_m) G⟫ = ∫ F (1 - N_m) G` vanishes on the range of `C_m - c`
(`eq:st18-t00058`, tex lines 1302–1306). -/
theorem inner_star_B_phaseSpeed_sub {m : ℝ} (hm : 0 < m) {c : ℂ} {F : Sturm.ComplexL2}
    (hF : Sturm.phaseSpeedOp hm F = c • F) (G : Sturm.ComplexL2) :
    ⟪(star F : Sturm.ComplexL2),
      (1 - Sturm.birmanSchwingerOperator hm) (Sturm.phaseSpeedOp hm G - c • G)⟫_ℂ = 0 := by
  have h := Sturm.inner_phaseSpeed_B hm (star F) G
  rw [Sturm.phaseSpeedOp_star, hF, Sturm.star_smul_L2, inner_smul_left,
    starRingEnd_self_apply] at h
  rw [map_sub, map_smul, inner_sub_right, inner_smul_right, ← h, sub_self]

theorem star_ne_zero_L2 {f : Sturm.ComplexL2} (h0 : f ≠ 0) : (star f : Sturm.ComplexL2) ≠ 0 := by
  intro h
  apply h0
  rw [← star_star f, h, Sturm.star_zero_L2]

/-- **Nonvanishing bilinear pairing at `m = 2`, both half-planes** (B0096, tex line 1518, via
bypass B2(c)): an eigenvector `C_2 f = c f` with `Im c ≠ 0`, `f ≠ 0`, has
`∫ f (1 - N_2) f = ⟪star f, (1 - N_2) f⟫ ≠ 0`. -/
theorem inner_star_B_ne_zero {c : ℂ} {f : Sturm.ComplexL2} (hc : c.im ≠ 0) (h0 : f ≠ 0)
    (hf : Sturm.phaseSpeedOp (m := 2) two_pos f = c • f) :
    ⟪(star f : Sturm.ComplexL2), (1 - Sturm.birmanSchwingerOperator (m := 2) two_pos) f⟫_ℂ ≠ 0 := by
  intro hint
  set B := (1 - Sturm.birmanSchwingerOperator (m := 2) two_pos) with hB
  set g : Sturm.ComplexL2 := star f with hg
  have hstar : Sturm.phaseSpeedOp (m := 2) two_pos g = conj c • g := by
    rw [hg, Sturm.phaseSpeedOp_star, hf, Sturm.star_smul_L2]
  have hgim : (conj c).im ≠ 0 := by
    rw [Complex.conj_im]; exact neg_ne_zero.mpr hc
  have hff : ⟪f, B f⟫_ℂ = 0 := Sturm.inner_B_eq_zero_of_eigen (m := 2) two_pos hc hf
  have hgg : ⟪g, B g⟫_ℂ = 0 := Sturm.inner_B_eq_zero_of_eigen (m := 2) two_pos hgim hstar
  have hfg : ⟪f, B g⟫_ℂ = 0 := by
    rw [← Sturm.inner_B_symm (m := 2) two_pos, ← inner_conj_symm, hint, map_zero]
  have hli : LinearIndependent ℂ ![f, g] := by
    refine (LinearIndependent.pair_iff' h0).mpr fun a ha => ?_
    have h1 : Sturm.phaseSpeedOp (m := 2) two_pos g = (a * c) • f := by
      rw [← ha, map_smul, hf, smul_smul]
    rw [hstar, ← ha, smul_smul] at h1
    have h2 : (conj c * a - a * c) • f = 0 := by rw [sub_smul, h1, sub_self]
    have h3 := (smul_eq_zero.mp h2).resolve_right h0
    have h4 : a * (conj c - c) = 0 := by linear_combination h3
    have hne : conj c - c ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
      exact hc (by linarith)
    have ha0 : a = 0 := (mul_eq_zero.mp h4).resolve_right hne
    apply h0
    have hg0 : g = 0 := by rw [← ha, ha0, zero_smul]
    rw [← star_star f, ← hg, hg0, Sturm.star_zero_L2]
  exact Sturm.PlanarIndex.not_neutral_pair (m := 2) one_lt_two hli hff hfg hint hgg

end UnforcedLeray.Planar
