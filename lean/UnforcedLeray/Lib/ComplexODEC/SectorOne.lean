import UnforcedLeray.Lib.ComplexODEC.Mode
import UnforcedLeray.Lib.PlanarSectorsB

/-!
# No growing modes in the sectors `n = ±1` (INF18 O13, bypass B3)

Scoping note `scoping/INF10-INF12-INF18-Planar.md` §4 bypass B3 ("`n = 1`") and §5 target
O13. Manuscript `paper/main.tex` lines 1351--1356 (blueprint unit B0080, eq. `st18-t00059`:
`φ₁ = r(Ω - c)` solves the `n = 1` Rayleigh equation, so there is no nonreal `n = 1`
eigenmode; negative indices by conjugation).

Statement (`sector_one_eigen_eq_zero`): on the profile space `L²(⟨r⟩^{2M} 2πr dr)`, `M > 1`,
the sector operator `𝓛₁ = -iΩ + i k R₁` has no eigenvalue `z` with `Re z > 0`.

Proof (bypass B3). Let `𝓛₁ w = z w`, `ψ = R₁ w = greenN 1 w`, `c = iz` (`Im c = Re z > 0`).
Then `w = kψ/(Ω - c)` a.e., so `Δ₁ψ = kψ/(Ω - c)`; in log radius `F(t) = ψ(e^t)` solves
`F'' = (1 + e^{2t} k(e^t)/(Ω - c)) F`. The explicit solution `F₁ = e^t (Ω(e^t) - c)` of the same
equation (the radial form of `φ₁ = r(Ω - c)`) is `O(e^t)` at `-∞` with its derivative, while
`F` and `F'` are bounded (Green bounds), so the Wronskian vanishes and `F = β F₁`. Since
`F → 0` at `+∞` and `|F₁| ≥ e^t Im c`, `β = 0`; hence `ψ = 0` and `w = 0`.

The sector `n = -1` follows by complex conjugation (tex line 1356); it is not restated here.
-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.ComplexODEC

open UnforcedLeray.GaussianVortex UnforcedLeray.Rayleigh UnforcedLeray.Sturm
open NonUniqueEuler.LinODE

/-! ### The `n = 1` equation in log radius and its explicit solution -/

/-- The `n = 1` potential `V₁(t) = 1 + e^{2t} k(e^t)/(Ω(e^t) - c)`. -/
def pot1 (c : ℂ) (t : ℝ) : ℂ :=
  1 + ((Real.exp t ^ 2 : ℝ) : ℂ) *
    ((radialK (Real.exp t) : ℂ) / ((radialOmega (Real.exp t) : ℂ) - c))

theorem continuous_pot1 {c : ℂ} (hc : c.im ≠ 0) : Continuous (pot1 c) := by
  have e : pot1 c = fun t => 1 + ((Real.exp t ^ 2 : ℝ) : ℂ) * kappa c (Real.exp t ^ 2) := by
    funext t
    rw [pot1, radialK_div_eq_kappa]
  rw [e]
  have hk := (contDiff_kappa hc).continuous
  fun_prop

/-- The explicit solution `F₁(t) = e^t (Ω(e^t) - c)`. -/
def sol1 (c : ℂ) (t : ℝ) : ℂ := ((Real.exp t : ℝ) : ℂ) * ((radialOmega (Real.exp t) : ℂ) - c)

/-- Its derivative `F₁' = e^t (Ω - c) - (e^{3t}/2) Ω`. -/
def sol1' (c : ℂ) (t : ℝ) : ℂ :=
  ((Real.exp t : ℝ) : ℂ) * ((radialOmega (Real.exp t) : ℂ) - c) -
    ((Real.exp t ^ 3 / 2 * radialOmega (Real.exp t) : ℝ) : ℂ)

theorem hasDerivAt_radialOmega_exp (t : ℝ) :
    HasDerivAt (fun t => radialOmega (Real.exp t))
      (-(Real.exp t ^ 2 / 2) * radialOmega (Real.exp t)) t := by
  have h1 : HasDerivAt (fun t => -(Real.exp t ^ 2 / 4)) (-(2 * Real.exp t ^ 2 / 4)) t :=
    ((hasDerivAt_exp_sq t).div_const 4).neg
  have h2 := (Real.hasDerivAt_exp _).comp t h1
  unfold radialOmega
  refine h2.congr_deriv ?_
  ring

theorem hasDerivAt_sol1 (c : ℂ) (t : ℝ) : HasDerivAt (sol1 c) (sol1' c t) t := by
  have hE := (Real.hasDerivAt_exp t).ofReal_comp
  have hΩ := (hasDerivAt_radialOmega_exp t).ofReal_comp
  have h := hE.mul (hΩ.sub_const c)
  refine h.congr_deriv ?_
  simp only [sol1']
  push_cast
  ring

theorem hasDerivAt_sol1' {c : ℂ} (hc : c.im ≠ 0) (t : ℝ) :
    HasDerivAt (sol1' c) (pot1 c t * sol1 c t) t := by
  have hE := (Real.hasDerivAt_exp t).ofReal_comp
  have hΩr := hasDerivAt_radialOmega_exp t
  have hΩ := hΩr.ofReal_comp
  have hE3 : HasDerivAt (fun t => Real.exp t ^ 3 / 2) (3 * Real.exp t ^ 2 * Real.exp t / 2) t := by
    have := ((Real.hasDerivAt_exp t).pow 3).div_const 2
    refine this.congr_deriv ?_
    push_cast
    ring
  have h2 := (hE3.mul hΩr).ofReal_comp
  have h := (hE.mul (hΩ.sub_const c)).sub h2
  refine h.congr_deriv ?_
  have hne := ofReal_sub_ne_zero hc (radialOmega (Real.exp t))
  simp only [pot1, sol1, radialK]
  field_simp
  push_cast
  ring

theorem isSolOn_sol1 {c : ℂ} (hc : c.im ≠ 0) : IsSolOn (pot1 c) univ (sol1 c) (sol1' c) :=
  ⟨fun t _ => (hasDerivAt_sol1 c t).hasDerivWithinAt,
    fun t _ => (hasDerivAt_sol1' hc t).hasDerivWithinAt⟩

theorem norm_sol1_le (c : ℂ) (t : ℝ) : ‖sol1 c t‖ ≤ Real.exp t * (1 + ‖c‖) := by
  rw [sol1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
  refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (Real.exp_pos t).le
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (radialOmega_pos _)]
  linarith [B0012.radialOmega_le_one (Real.exp t)]

theorem tendsto_sol1_atBot (c : ℂ) : Tendsto (sol1 c) atBot (𝓝 0) := by
  refine squeeze_zero_norm (norm_sol1_le c) ?_
  have := Real.tendsto_exp_atBot.mul_const (1 + ‖c‖)
  rwa [zero_mul] at this

theorem tendsto_sol1'_atBot (c : ℂ) : Tendsto (sol1' c) atBot (𝓝 0) := by
  have h2 : Tendsto (fun t => ((Real.exp t ^ 3 / 2 * radialOmega (Real.exp t) : ℝ) : ℂ)) atBot
      (𝓝 0) := by
    have h3 : Tendsto (fun t => Real.exp t ^ 3 / 2 * radialOmega (Real.exp t)) atBot (𝓝 0) := by
      have h3' : Tendsto (fun t => Real.exp t ^ 3 / 2) atBot (𝓝 0) := by
        simpa using (Real.tendsto_exp_atBot.pow 3).div_const 2
      refine squeeze_zero_norm (fun t => ?_) h3'
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := radialOmega_pos (Real.exp t); positivity)]
      have := B0012.radialOmega_le_one (Real.exp t)
      have h0 : 0 ≤ Real.exp t ^ 3 / 2 := by positivity
      simpa using mul_le_of_le_one_right h0 this
    have := (Complex.continuous_ofReal.tendsto 0).comp h3
    rw [Complex.ofReal_zero] at this
    exact this
  have := (tendsto_sol1_atBot c).sub h2
  rw [sub_zero] at this
  exact this

theorem norm_sol1_ge (c : ℂ) (t : ℝ) : Real.exp t * |c.im| ≤ ‖sol1 c t‖ := by
  rw [sol1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
  exact mul_le_mul_of_nonneg_left (abs_im_le_norm_ofReal_sub c _) (Real.exp_pos t).le

/-! ### The Green derivative bound -/

theorem abs_mul_dker_one_le {t ρ : ℝ} (ht : 0 < t) (hρ : 0 < ρ) : |t * B0011.dker 1 t ρ| ≤ ρ := by
  by_cases h : t < ρ
  · rw [B0011.dker_of_lt h, B0011.dL]
    simp only [Nat.cast_one, Nat.sub_self, pow_zero, one_mul, mul_one]
    rw [abs_of_pos ht]
    exact h.le
  · push Not at h
    rw [B0011.dker_of_ge h, B0011.dR]
    simp only [Nat.cast_one]
    rw [abs_mul, abs_neg, abs_of_pos ht, abs_of_nonneg (by positivity)]
    have htne : t ≠ 0 := ht.ne'
    have e : t * (1 * (ρ / t) ^ (1 + 1)) = ρ * (ρ / t) := by
      rw [one_mul, show (1 + 1 : ℕ) = 2 from rfl, div_pow]
      field_simp
    rw [e]
    exact mul_le_of_le_one_right hρ.le (div_le_one_of_le₀ h ht.le)

theorem norm_mul_Phi_one_le {g : ℝ → ℂ} (hg : B0011.WProf g) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) * B0011.Phi 1 g t‖ ≤ ∫ ρ in Ioi (0 : ℝ), ρ * ‖g ρ‖ := by
  rw [B0011.Phi, ← integral_const_mul]
  refine norm_integral_le_of_norm_le hg.int ((ae_restrict_mem measurableSet_Ioi).mono
    fun ρ hρ => ?_)
  have hρ0 : (0 : ℝ) < ρ := hρ
  rw [← mul_assoc, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have : ((t : ℂ) * (B0011.dker 1 t ρ : ℂ)) = ((t * B0011.dker 1 t ρ : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  exact abs_mul_dker_one_le ht hρ0

/-! ### O13 -/

theorem add_I_mul_ne_zero {z : ℂ} (hz : 0 < z.re) (x : ℝ) : z + Complex.I * (x : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

/-- **O13** (scoping `sector_one_eigen_eq_zero`; tex lines 1351--1356, unit B0080, bypass B3;
the manuscript's endpoint Volterra selection is replaced by a Wronskian in log radius): the sector
operator `𝓛₁` on `L²(⟨r⟩^{2M} 2πr dr)`, `M > 1`, has no eigenvalue with positive real part. -/
theorem sector_one_eigen_eq_zero {M : ℝ} (hM : 1 < M) {z : ℂ} (hz : 0 < z.re)
    {w : Planar.ProfL2 M} (hw : Planar.Lsec hM 1 w = z • w) : w = 0 := by
  set c : ℂ := Complex.I * z with hcdef
  have hcim : c.im = z.re := by simp [hcdef]
  have hc : c.im ≠ 0 := by rw [hcim]; exact hz.ne'
  set ψ : ℝ → ℂ := Planar.greenN 1 w with hψdef
  set g : ℝ → ℂ := fun r => (radialK r : ℂ) / ((radialOmega r : ℂ) - c) * ψ r with hgdef
  -- the eigenvalue equation pointwise
  have hae : ∀ᵐ r ∂Planar.profileMeasure M,
      -(Complex.I * ((1 : ℤ) : ℂ)) * (radialOmega r : ℂ) * w r +
        Complex.I * ((1 : ℤ) : ℂ) * (radialK r : ℂ) * Planar.greenN (1 : ℤ).natAbs w r =
          z * w r := by
    have h1 : ⇑(Planar.Lsec hM 1 w) =ᵐ[Planar.profileMeasure M] ⇑(z • w) := by rw [hw]
    filter_upwards [Planar.coeFn_Lsec hM 1 w, Lp.coeFn_smul z w, h1] with r a1 a2 a3
    rw [← a1, a3, a2, Pi.smul_apply, smul_eq_mul]
  have hwg : ⇑w =ᵐ[Planar.profileMeasure M] g := by
    filter_upwards [hae] with r hr
    have hn : ((1 : ℤ).natAbs) = 1 := rfl
    rw [hn, ← hψdef] at hr
    have hne2 := ofReal_sub_ne_zero hc (radialOmega r)
    simp only [hgdef]
    rw [div_mul_eq_mul_div, eq_div_iff hne2]
    push_cast at hr
    rw [hcdef]
    linear_combination Complex.I * hr +
      (w r * (radialOmega r : ℂ) - (radialK r : ℂ) * ψ r) * Complex.I_sq
  have hwp : B0011.WProf ⇑w := (Planar.memL2M_of_memLp (Lp.memLp w)).wprof hM
  have hwg' : ⇑w =ᵐ[volume.restrict (Ioi 0)] g := (Planar.ac_profileMeasure M).ae_le hwg
  have hgp : B0011.WProf g := ⟨hwp.meas.congr hwg', hwp.int.congr (hwg'.mono fun r hr => by
    show r * ‖w r‖ = r * ‖g r‖
    rw [hr])⟩
  have hψg : ∀ r, ψ r = Planar.greenN 1 g r := fun r => Planar.greenN_congr 1 hwg r
  obtain ⟨hd, hcont, hint⟩ := B0079.deltaN_solution_of_wprof (n := 1) one_ne_zero hgp
  set ψ₀ : ℝ → ℂ := fun t => -(1 / (2 * ((1 : ℕ) : ℂ))) * B0011.Psi 1 g t with hψ₀def
  set ψ₀' : ℝ → ℂ := fun t => -(1 / (2 * ((1 : ℕ) : ℂ))) * B0011.Phi 1 g t with hψ₀'def
  have hψ₀ : ∀ r, ψ r = ψ₀ r := fun r => by rw [hψg, Planar.greenN_eq_Psi]
  set G : ℝ → ℂ := fun r => g r - ψ₀' r / (r : ℂ) + ((1 : ℕ) : ℂ) ^ 2 * ψ₀ r / (r : ℂ) ^ 2
    with hGdef
  -- continuity of the second derivative
  have hψcont : ContinuousOn ψ (Ioi 0) := Planar.continuousOn_greenN hM 1 w
  have hψ₀cont : ContinuousOn ψ₀ (Ioi 0) := fun r hr => (hd r hr).continuousAt.continuousWithinAt
  have hgcont : ContinuousOn g (Ioi 0) := by
    have hk : Continuous fun r : ℝ => (radialK r : ℂ) / ((radialOmega r : ℂ) - c) := by
      have e : (fun r : ℝ => (radialK r : ℂ) / ((radialOmega r : ℂ) - c)) =
          fun r => kappa c (r ^ 2) := funext (radialK_div_eq_kappa c)
      rw [e]
      exact (contDiff_kappa hc).continuous.comp (continuous_pow 2)
    exact hk.continuousOn.mul hψcont
  have hGcont : ContinuousOn G (Ioi 0) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr
    have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have c1 := (hgcont r hr).continuousAt (Ioi_mem_nhds hr0)
    have c2 := (hcont r hr).continuousAt (Ioi_mem_nhds hr0)
    have c3 := (hψ₀cont r hr).continuousAt (Ioi_mem_nhds hr0)
    have c4 : ContinuousAt (fun x : ℝ => (x : ℂ)) r := Complex.continuous_ofReal.continuousAt
    exact ((c1.sub (c2.div c4 hrne)).add ((continuousAt_const.mul c3).div (c4.pow 2)
      (pow_ne_zero 2 hrne))).continuousWithinAt
  have hd2 : ∀ r : ℝ, 0 < r → HasDerivAt ψ₀' (G r) r := by
    intro r hr
    have ha : (0 : ℝ) < r / 2 := by linarith
    have hsub : uIcc (r / 2) r ⊆ Ioi 0 := by
      rw [uIcc_of_le (by linarith)]
      exact fun x hx => lt_of_lt_of_le ha hx.1
    have hII : IntervalIntegrable G volume (r / 2) r :=
      (hGcont.mono hsub).intervalIntegrable
    have hmeas : StronglyMeasurableAtFilter G (𝓝 r) :=
      hGcont.stronglyMeasurableAtFilter isOpen_Ioi r hr
    have hcat : ContinuousAt G r := hGcont.continuousAt (Ioi_mem_nhds hr)
    have h2 := (intervalIntegral.integral_hasDerivAt_right hII hmeas hcat).const_add
      (ψ₀' (r / 2))
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hr] with x hx
    have := hint (r / 2) x ha hx
    show ψ₀' x = ψ₀' (r / 2) + ∫ y in (r / 2)..x, G y
    rw [← this]
    ring
  -- the log-radius solution
  set Fl : ℝ → ℂ := fun t => ψ₀ (Real.exp t) with hFl
  set Fl' : ℝ → ℂ := fun t => ((Real.exp t : ℝ) : ℂ) * ψ₀' (Real.exp t) with hFl'
  have hsolF : IsSolOn (pot1 c) univ Fl Fl' := by
    constructor
    · intro t _
      have := (hd (Real.exp t) (Real.exp_pos t)).scomp t (Real.hasDerivAt_exp t)
      refine (this.congr_deriv ?_).hasDerivWithinAt
      rw [Complex.real_smul]
    · intro t _
      have h1 := (Real.hasDerivAt_exp t).ofReal_comp
      have h2 := (hd2 (Real.exp t) (Real.exp_pos t)).scomp t (Real.hasDerivAt_exp t)
      have h := h1.mul h2
      refine (h.congr_deriv ?_).hasDerivWithinAt
      have hE : ((Real.exp t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos t).ne'
      have hne := ofReal_sub_ne_zero hc (radialOmega (Real.exp t))
      simp only [Function.comp_apply, Pi.mul_apply, Complex.real_smul, hGdef, pot1, hFl,
        hgdef, Complex.ofReal_pow]
      rw [hψ₀]
      field_simp
      ring
  -- bounds
  set Bψ : ℝ := (2 * ((1 : ℕ) : ℝ))⁻¹ * ‖Planar.wrepLp hM‖ * ‖w‖
  have hB1 : ∀ t, ‖Fl t‖ ≤ Bψ := fun t => by
    show ‖ψ₀ (Real.exp t)‖ ≤ Bψ
    rw [← hψ₀]
    exact Planar.norm_greenN_le_wrep hM 1 (Real.exp_pos t) w
  set B' : ℝ := 1 / 2 * ∫ ρ in Ioi (0 : ℝ), ρ * ‖g ρ‖
  have hB2 : ∀ t, ‖Fl' t‖ ≤ B' := fun t => by
    have h := norm_mul_Phi_one_le hgp (Real.exp_pos t)
    show ‖((Real.exp t : ℝ) : ℂ) * ψ₀' (Real.exp t)‖ ≤ B'
    rw [hψ₀'def]
    simp only
    rw [mul_left_comm, norm_mul]
    have : ‖-(1 / (2 * ((1 : ℕ) : ℂ)))‖ = 1 / 2 := by norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  -- the Wronskian vanishes
  set W : ℝ → ℂ := fun t => Fl t * sol1' c t - Fl' t * sol1 c t with hWdef
  have hWc : ∀ t, W t = W 0 := fun t => wronskian_const hsolF (isSolOn_sol1 hc) t 0
  have hWlim : Tendsto W atBot (𝓝 0) := by
    have hb : Tendsto (fun t => Bψ * ‖sol1' c t‖ + B' * ‖sol1 c t‖) atBot (𝓝 0) := by
      have := ((tendsto_sol1'_atBot c).norm.const_mul Bψ).add
        ((tendsto_sol1_atBot c).norm.const_mul B')
      simpa using this
    refine squeeze_zero_norm (fun t => ?_) hb
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hB1 t) (norm_nonneg _)
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hB2 t) (norm_nonneg _)
  have hW0 : W 0 = 0 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr fun t => (hWc t).symm) hWlim
  -- proportionality
  have hpos : 0 < |c.im| := abs_pos.mpr hc
  have hs0 : sol1 c 0 ≠ 0 := by
    intro h
    have := norm_sol1_ge c 0
    rw [h, norm_zero, Real.exp_zero, one_mul] at this
    linarith
  set β : ℂ := Fl 0 / sol1 c 0 with hβdef
  have h0 : Fl 0 = β * sol1 c 0 := by rw [hβdef]; field_simp
  have h0' : Fl' 0 = β * sol1' c 0 := by
    have hw0 : Fl 0 * sol1' c 0 - Fl' 0 * sol1 c 0 = 0 := hW0
    rw [hβdef]
    field_simp
    linear_combination -hw0
  have heq := IsSolOn.eqOn ordConnected_univ (continuous_pot1 hc).continuousOn hsolF
    ((isSolOn_sol1 hc).const_mul β) (mem_univ 0) h0 h0'
  -- `β = 0` from the decay at `+∞`
  have hFtop : Tendsto Fl atTop (𝓝 0) := by
    have h := (Planar.tendsto_greenN_atTop (n := 1) le_rfl hgp).comp Real.tendsto_exp_atTop
    refine h.congr fun t => ?_
    simp only [Function.comp_apply, hFl]
    rw [← hψ₀, hψg]
  have hβ : β = 0 := by
    by_contra hβne
    have hβpos : 0 < ‖β‖ * |c.im| := mul_pos (norm_pos_iff.mpr hβne) hpos
    obtain ⟨t, ht, ht0⟩ := ((hFtop.norm.eventually (gt_mem_nhds (by
      rw [norm_zero]; exact hβpos))).and (eventually_ge_atTop (0 : ℝ))).exists
    have h1 : ‖Fl t‖ = ‖β‖ * ‖sol1 c t‖ := by
      rw [heq.1 (mem_univ t), norm_mul]
    have h2 := norm_sol1_ge c t
    have h3 : 1 ≤ Real.exp t := Real.one_le_exp ht0
    have h4 : |c.im| ≤ ‖sol1 c t‖ := le_trans (le_mul_of_one_le_left hpos.le h3) h2
    have h5 : ‖β‖ * |c.im| ≤ ‖Fl t‖ := by
      rw [h1]; exact mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
    linarith
  -- conclusion
  have hψ0 : ∀ r : ℝ, 0 < r → ψ r = 0 := fun r hr => by
    have h := heq.1 (mem_univ (Real.log r))
    simp only [hFl, hβ, zero_mul, Real.exp_log hr] at h
    rw [hψ₀]
    exact h
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hwg, Planar.ae_profile_pos M] with r h1 h2
  rw [h1, Pi.zero_apply]
  simp [hgdef, hψ0 r h2]

end UnforcedLeray.ComplexODEC
