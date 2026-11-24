import UnforcedLeray.Units.B0011
import UnforcedLeray.Units.B0010

/-!
# Unit B0086 (`eq:st18-t00062`): pointwise Green bound on `X_G`

Blueprint unit `B0086`, label `eq:st18-t00062`, `paper/main.tex` lines 1417–1422 (inside the
proof "Gaussian boundedness and the complement estimate", lines 1415–1430).

**Statement (tex lines 1417–1422).** With `R` the Green inverse `eq:st18-t00007` (B0011,
lines 685–688) and `X_G` the Gaussian angular-two space `eq:st18-t00005` (B0010, lines
672–677), there is `C < ∞` such that for every `f ∈ X_G` and every `r > 0`
`|Rf(r)| ≤ C ‖f‖_{X_G} min(r, r⁻²)`,
and "the same estimate holds for `R((x-2)f)`", `x = r²/4` (line 1422).
The proof sketch (lines 1421–1422) asserts, before the prefactors `r⁻²` and `r²` of
`eq:st18-t00007`: near `0` the first integral is `O(r³)` and the second is `O(r⁻¹)`; at `∞`
the first is bounded by the finite third radial moment and the second is Gaussian-small.

**Formalization.**
* Profiles are functions `f : ℝ → ℂ` with `B0011.MemXG f` (the defining condition of `X_G`);
  `xGNorm f = (∫₀^∞ |f|² G⁻¹ r dr)^{1/2}` is the norm of `X_G` (`xGNorm_eq_norm`: it is the norm
  of B0010's Hilbert space `XG = Lp ℂ 2 xGMeasure`). Both forms of the main bound are given:
  `green_bound` (profiles) and `green_bound_XG` (elements of B0010's `XG`).
* `(x-2)f` need not lie in `X_G`; its Green transform is `R` applied to the function
  `s ↦ (s²/4 - 2) f(s)`, whose two integrals converge absolutely (`integrable_parts_xm2`), so no
  Bochner junk value enters; for `f` itself this is B0011's `WProf.integrable_R_parts`.
* The proof is the manuscript's: Cauchy–Schwarz with the Gaussian weight (`cauchySchwarz`, in
  the form `2ab ≤ t a² + t⁻¹ b²` optimized over `t > 0`), applied to a general real multiplier
  `m` (`Admissible`), then specialized to `m = 1` and `m = x - 2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.B0086

open UnforcedLeray.B0011

/-! ### The variable `x` and the norm of `X_G` -/

/-- The variable `x = r²/4` of tex line 1422 (`R((x-2)f)`). -/
def xVar (r : ℝ) : ℝ := r ^ 2 / 4

/-- The norm `‖f‖_{X_G} = (∫₀^∞ |f(r)|² G(r)⁻¹ r dr)^{1/2}` of a profile of `X_G`
(`eq:st18-t00005`, tex lines 673–676; unit B0010). -/
def xGNorm (f : ℝ → ℂ) : ℝ := Real.sqrt (∫ s in Ioi 0, ‖f s‖ ^ 2 * (gaussG s)⁻¹ * s)

theorem xGNorm_nonneg (f : ℝ → ℂ) : 0 ≤ xGNorm f := Real.sqrt_nonneg _

theorem xGNorm_sq (f : ℝ → ℂ) :
    xGNorm f ^ 2 = ∫ s in Ioi 0, ‖f s‖ ^ 2 * (gaussG s)⁻¹ * s := by
  unfold xGNorm
  rw [Real.sq_sqrt]
  refine setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
  have h1 := gaussG_pos s
  have hs' : (0 : ℝ) < s := hs
  positivity

/-! ### Cauchy–Schwarz with the Gaussian weight -/

/-- If `2I ≤ t n² + t⁻¹ β²` for every `t > 0`, then `I ≤ β n`. -/
theorem le_mul_of_forall_two_mul_le {I n β : ℝ} (hn : 0 ≤ n) (hβ : 0 ≤ β)
    (h : ∀ t : ℝ, 0 < t → 2 * I ≤ t * n ^ 2 + t⁻¹ * β ^ 2) : I ≤ β * n := by
  rcases hn.eq_or_lt with hn0 | hnpos
  · subst hn0
    rw [mul_zero]
    by_contra hI
    push Not at hI
    have ht : 0 < β ^ 2 / I + 1 := by positivity
    have h1 := h _ ht
    have h2 : (β ^ 2 / I + 1)⁻¹ * β ^ 2 ≤ I := by
      rw [inv_mul_le_iff₀ ht, add_mul, div_mul_cancel₀ _ hI.ne', one_mul]
      linarith
    have h3 : (β ^ 2 / I + 1) * (0 : ℝ) ^ 2 = 0 := by ring
    linarith
  · rcases hβ.eq_or_lt with hβ0 | hβpos
    · subst hβ0
      rw [zero_mul]
      by_contra hI
      push Not at hI
      have ht : 0 < I / n ^ 2 := by positivity
      have h1 := h _ ht
      have e : I / n ^ 2 * n ^ 2 + (I / n ^ 2)⁻¹ * (0 : ℝ) ^ 2 = I := by
        rw [div_mul_cancel₀ _ (by positivity)]
        ring
      linarith
    · have ht : 0 < β / n := div_pos hβpos hnpos
      have h1 := h _ ht
      have e1 : β / n * n ^ 2 = β * n := by field_simp
      have e2 : (β / n)⁻¹ * β ^ 2 = β * n := by field_simp
      linarith

/-- Pointwise arithmetic–geometric mean inequality behind the Cauchy–Schwarz step:
`2 y x ≤ t (x² G⁻¹ s) + t⁻¹ (y² G / s)`. -/
theorem two_mul_le_aux {x y G s t : ℝ} (hG : 0 < G) (hs : 0 < s) (ht : 0 < t) :
    2 * (y * x) ≤ t * (x ^ 2 * G⁻¹ * s) + t⁻¹ * (y ^ 2 * G / s) := by
  have e : t * (x ^ 2 * G⁻¹ * s) + t⁻¹ * (y ^ 2 * G / s) - 2 * (y * x) =
      (t * s * x - y * G) ^ 2 / (t * s * G) := by
    field_simp
    ring
  have : 0 ≤ (t * s * x - y * G) ^ 2 / (t * s * G) := by positivity
  linarith

/-- **Cauchy–Schwarz with Gaussian weight** (INF27): for `f ∈ X_G`, a measurable set
`S ⊆ (0, ∞)` and a measurable weight `w`, if `w² G / s ≤ a` on `S` with `∫_S a ≤ β²`, then
`|w| |f|` is integrable on `S` and `∫_S |w| |f| ≤ β ‖f‖_{X_G}`. -/
theorem cauchySchwarz {f : ℝ → ℂ} (hf : MemXG f) {S : Set ℝ} (hS : MeasurableSet S)
    (hS0 : S ⊆ Ioi 0) {w a : ℝ → ℝ} (hw : Measurable w) (ha : IntegrableOn a S)
    (hwa : ∀ s ∈ S, w s ^ 2 * gaussG s / s ≤ a s) {β : ℝ} (hβ : 0 ≤ β)
    (haβ : ∫ s in S, a s ≤ β ^ 2) :
    IntegrableOn (fun s => |w s| * ‖f s‖) S ∧ ∫ s in S, |w s| * ‖f s‖ ≤ β * xGNorm f := by
  have hF : IntegrableOn (fun s => ‖f s‖ ^ 2 * (gaussG s)⁻¹ * s) S :=
    IntegrableOn.mono_set hf.2 hS0
  have key : ∀ t : ℝ, 0 < t → ∀ s ∈ S, 2 * (|w s| * ‖f s‖) ≤
      t * (‖f s‖ ^ 2 * (gaussG s)⁻¹ * s) + t⁻¹ * a s := by
    intro t ht s hs
    have hs0 : (0 : ℝ) < s := hS0 hs
    have h1 := two_mul_le_aux (x := ‖f s‖) (y := |w s|) (gaussG_pos s) hs0 ht
    rw [sq_abs] at h1
    have h2 : t⁻¹ * (w s ^ 2 * gaussG s / s) ≤ t⁻¹ * a s :=
      mul_le_mul_of_nonneg_left (hwa s hs) (inv_nonneg.2 ht.le)
    linarith
  have hmeas : AEStronglyMeasurable (fun s => |w s| * ‖f s‖) (volume.restrict S) :=
    (continuous_abs.measurable.comp hw).aestronglyMeasurable.mul (hf.1.mono_set hS0).norm
  have hint : IntegrableOn (fun s => |w s| * ‖f s‖) S := by
    refine Integrable.mono' ((hF.add ha).const_mul (1 / 2)) hmeas ?_
    refine (ae_restrict_iff' hS).2 (Eventually.of_forall fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := key 1 one_pos s hs
    simp only [Pi.add_apply]
    rw [one_mul, inv_one, one_mul] at this
    linarith
  refine ⟨hint, ?_⟩
  apply le_mul_of_forall_two_mul_le (xGNorm_nonneg f) hβ
  intro t ht
  have h1 : ∫ s in S, 2 * (|w s| * ‖f s‖) ≤
      ∫ s in S, (t * (‖f s‖ ^ 2 * (gaussG s)⁻¹ * s) + t⁻¹ * a s) :=
    setIntegral_mono_on (hint.const_mul 2) ((hF.const_mul t).add (ha.const_mul t⁻¹)) hS
      (key t ht)
  rw [integral_const_mul, integral_add (hF.const_mul t) (ha.const_mul t⁻¹), integral_const_mul,
    integral_const_mul] at h1
  have hFle : ∫ s in S, ‖f s‖ ^ 2 * (gaussG s)⁻¹ * s ≤ xGNorm f ^ 2 := by
    rw [xGNorm_sq]
    refine setIntegral_mono_set hf.2 ?_ (ae_of_all _ hS0)
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    have h1 := gaussG_pos s
    have hs' : (0 : ℝ) < s := hs
    simp only [Pi.zero_apply]
    positivity
  calc 2 * ∫ s in S, |w s| * ‖f s‖
      ≤ t * (∫ s in S, ‖f s‖ ^ 2 * (gaussG s)⁻¹ * s) + t⁻¹ * ∫ s in S, a s := h1
    _ ≤ t * xGNorm f ^ 2 + t⁻¹ * β ^ 2 := by
      have := inv_pos.2 ht
      gcongr

/-! ### Admissible real multipliers -/

/-- A real multiplier `m` for which the Green bound holds for `R(m f)`: `m` is continuous,
`m² G ≤ c` on `(0, ∞)`, and the moment `∫₀^∞ s⁵ m² G` is finite. Used with `m = 1` and
`m = x - 2` (tex line 1422). -/
structure Admissible (m : ℝ → ℝ) (c : ℝ) : Prop where
  cont : Continuous m
  bdd : ∀ s : ℝ, 0 < s → m s ^ 2 * gaussG s ≤ c
  int5 : IntegrableOn (fun s => s ^ 5 * (m s ^ 2 * gaussG s)) (Ioi 0)

/-- The fifth Gaussian moment `∫₀^∞ s⁵ m(s)² G(s) ds` of a multiplier. -/
def moment5 (m : ℝ → ℝ) : ℝ := ∫ s in Ioi 0, s ^ 5 * (m s ^ 2 * gaussG s)

theorem Admissible.c_nonneg {m : ℝ → ℝ} {c : ℝ} (hm : Admissible m c) : 0 ≤ c :=
  le_trans (mul_nonneg (sq_nonneg _) (gaussG_pos 1).le) (hm.bdd 1 one_pos)

theorem moment5_nonneg (m : ℝ → ℝ) : 0 ≤ moment5 m := by
  refine setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
  have h1 := gaussG_pos s
  have hs' : (0 : ℝ) < s := hs
  positivity

/-- The norm of the first integral of `eq:st18-t00007` for `R(m f)`. -/
theorem norm_firstIntegral_le (m : ℝ → ℝ) (f : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    ‖∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * ((m s : ℂ) * f s)‖ ≤
      ∫ s in Ioc 0 r, |s ^ 3 * m s| * ‖f s‖ := by
  rw [intervalIntegral.integral_of_le hr.le]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow]
  ring

/-- The norm of the second integral of `eq:st18-t00007` for `R(m f)`. -/
theorem norm_secondIntegral_le (m : ℝ → ℝ) (f : ℝ → ℂ) (r : ℝ) :
    ‖∫ s in Ioi r, (s : ℂ)⁻¹ * ((m s : ℂ) * f s)‖ ≤
      ∫ s in Ioi r, |s⁻¹ * m s| * ‖f s‖ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_inv]
  ring

/-! ### Elementary Gaussian bounds -/

theorem gaussG_le_exp (s : ℝ) : gaussG s ≤ Real.exp (-(s ^ 2 / 4)) := by
  unfold gaussG GaussianVortex.radialOmega
  have h2 : (4 * Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [Real.two_le_pi])
  calc (4 * Real.pi)⁻¹ * Real.exp (-(s ^ 2 / 4)) ≤ 1 * Real.exp (-(s ^ 2 / 4)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = Real.exp (-(s ^ 2 / 4)) := one_mul _

theorem gaussG_le_one (s : ℝ) : gaussG s ≤ 1 :=
  (gaussG_le_exp s).trans (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg s]))

/-- `∫₀^∞ sⁿ G(s) ds < ∞`. -/
theorem integrableOn_pow_mul_gaussG (n : ℕ) :
    IntegrableOn (fun s : ℝ => s ^ n * gaussG s) (Ioi 0) := by
  have hn : (-1 : ℝ) < n := by have := n.cast_nonneg (α := ℝ); linarith
  refine (integrableOn_rpow_mul_gaussG hn).congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast]

/-- `s⁻³ ≤ r⁻⁸ s⁵` for `0 < r ≤ s`. -/
theorem inv_cube_le {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) : (s ^ 3)⁻¹ ≤ (r ^ 8)⁻¹ * s ^ 5 := by
  have hs : 0 < s := hr.trans_le hrs
  have e2 : (r ^ 8)⁻¹ * s ^ 5 - (s ^ 3)⁻¹ = (s ^ 8 - r ^ 8) / (r ^ 8 * s ^ 3) := by
    field_simp
  have : 0 ≤ (s ^ 8 - r ^ 8) / (r ^ 8 * s ^ 3) :=
    div_nonneg (sub_nonneg.2 (pow_le_pow_left₀ hr.le hrs 8)) (by positivity)
  linarith

/-! ### The two integrals of `eq:st18-t00007` for `R(m f)` -/

section Multiplier

variable {m : ℝ → ℝ} {c : ℝ}

theorem setIntegral_moment5_le (m : ℝ → ℝ) (hm5 : IntegrableOn
    (fun s => s ^ 5 * (m s ^ 2 * gaussG s)) (Ioi 0)) {S : Set ℝ} (hS0 : S ⊆ Ioi 0) :
    ∫ s in S, s ^ 5 * (m s ^ 2 * gaussG s) ≤ moment5 m := by
  refine setIntegral_mono_set hm5 ?_ (ae_of_all _ hS0)
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
  have h1 := gaussG_pos s
  have hs' : (0 : ℝ) < s := hs
  simp only [Pi.zero_apply]
  positivity

/-- Near `0` the first integral of `eq:st18-t00007` is `O(r³)` (tex line 1421):
`∫₀^r |s³ m f| ≤ √c r³ ‖f‖_{X_G}`, and the integrand is integrable. -/
theorem firstIntegral_le_small (hm : Admissible m c) {f : ℝ → ℂ} (hf : MemXG f) {r : ℝ}
    (hr : 0 < r) :
    IntegrableOn (fun s => |s ^ 3 * m s| * ‖f s‖) (Ioc 0 r) ∧
      ∫ s in Ioc 0 r, |s ^ 3 * m s| * ‖f s‖ ≤ Real.sqrt c * r ^ 3 * xGNorm f := by
  have hc := hm.c_nonneg
  refine cauchySchwarz hf measurableSet_Ioc Ioc_subset_Ioi_self
    (w := fun s => s ^ 3 * m s) ((continuous_pow 3).mul hm.cont).measurable
    (a := fun _ => r ^ 5 * c)
    (integrableOn_const measure_Ioc_lt_top.ne) ?_ (by positivity) ?_
  · intro s hs
    have hs0 : 0 < s := hs.1
    have e : (s ^ 3 * m s) ^ 2 * gaussG s / s = s ^ 5 * (m s ^ 2 * gaussG s) := by
      field_simp
    rw [e]
    exact mul_le_mul (pow_le_pow_left₀ hs0.le hs.2 5) (hm.bdd s hs0)
      (mul_nonneg (sq_nonneg _) (gaussG_pos s).le) (by positivity)
  · rw [setIntegral_const, Real.volume_real_Ioc_of_le hr.le, smul_eq_mul, mul_pow,
      Real.sq_sqrt hc]
    exact le_of_eq (by ring)

/-- At `∞` the first integral is bounded (tex line 1421):
`∫₀^r |s³ m f| ≤ (∫₀^∞ s⁵ m² G)^{1/2} ‖f‖_{X_G}`. -/
theorem firstIntegral_le_large (hm : Admissible m c) {f : ℝ → ℂ} (hf : MemXG f) (r : ℝ) :
    ∫ s in Ioc 0 r, |s ^ 3 * m s| * ‖f s‖ ≤ Real.sqrt (moment5 m) * xGNorm f := by
  refine (cauchySchwarz hf measurableSet_Ioc Ioc_subset_Ioi_self
    (w := fun s => s ^ 3 * m s) ((continuous_pow 3).mul hm.cont).measurable
    (a := fun s => s ^ 5 * (m s ^ 2 * gaussG s)) (hm.int5.mono_set Ioc_subset_Ioi_self) ?_
    (Real.sqrt_nonneg _) ?_).2
  · intro s hs
    have hs0 : 0 < s := hs.1
    apply le_of_eq
    field_simp
  · rw [Real.sq_sqrt (moment5_nonneg m)]
    exact setIntegral_moment5_le m hm.int5 Ioc_subset_Ioi_self

/-- Near `0` the second integral of `eq:st18-t00007` is `O(r⁻¹)` (tex line 1421):
`∫_r^∞ |s⁻¹ m f| ≤ √c r⁻¹ ‖f‖_{X_G}`, and the integrand is integrable. -/
theorem secondIntegral_le_small (hm : Admissible m c) {f : ℝ → ℂ} (hf : MemXG f) {r : ℝ}
    (hr : 0 < r) :
    IntegrableOn (fun s => |s⁻¹ * m s| * ‖f s‖) (Ioi r) ∧
      ∫ s in Ioi r, |s⁻¹ * m s| * ‖f s‖ ≤ Real.sqrt c * r⁻¹ * xGNorm f := by
  have hc := hm.c_nonneg
  refine cauchySchwarz hf measurableSet_Ioi (Ioi_subset_Ioi hr.le)
    (w := fun s => s⁻¹ * m s) (measurable_inv.mul hm.cont.measurable)
    (a := fun s => c * s ^ (-3 : ℝ))
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) hr).const_mul c) ?_ (by positivity) ?_
  · intro s hs
    have hs0 : 0 < s := hr.trans hs
    have e : (s⁻¹ * m s) ^ 2 * gaussG s / s = s ^ (-3 : ℝ) * (m s ^ 2 * gaussG s) := by
      rw [Real.rpow_neg hs0.le]
      have e3 : s ^ (3 : ℝ) = s ^ 3 := by exact_mod_cast Real.rpow_natCast s 3
      rw [e3]
      field_simp
    rw [e, mul_comm c]
    exact mul_le_mul_of_nonneg_left (hm.bdd s hs0) (Real.rpow_nonneg hs0.le _)
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hr, mul_pow, Real.sq_sqrt hc]
    have e : (-3 : ℝ) + 1 = -2 := by norm_num
    rw [e, Real.rpow_neg hr.le, neg_div_neg_eq, Real.rpow_two, inv_pow]
    exact mul_le_mul_of_nonneg_left (half_le_self (by positivity)) hc

/-- At `∞` the second integral decays (tex line 1421):
`∫_r^∞ |s⁻¹ m f| ≤ (∫₀^∞ s⁵ m² G)^{1/2} r⁻⁴ ‖f‖_{X_G}`. -/
theorem secondIntegral_le_large (hm : Admissible m c) {f : ℝ → ℂ} (hf : MemXG f) {r : ℝ}
    (hr : 0 < r) :
    ∫ s in Ioi r, |s⁻¹ * m s| * ‖f s‖ ≤ Real.sqrt (moment5 m) * (r ^ 4)⁻¹ * xGNorm f := by
  have hM := moment5_nonneg m
  refine (cauchySchwarz hf measurableSet_Ioi (Ioi_subset_Ioi hr.le)
    (w := fun s => s⁻¹ * m s) (measurable_inv.mul hm.cont.measurable)
    (a := fun s => (r ^ 8)⁻¹ * (s ^ 5 * (m s ^ 2 * gaussG s)))
    ((hm.int5.mono_set (Ioi_subset_Ioi hr.le)).const_mul _) ?_ (by positivity) ?_).2
  · intro s hs
    have hs0 : 0 < s := hr.trans hs
    have e : (s⁻¹ * m s) ^ 2 * gaussG s / s = (s ^ 3)⁻¹ * (m s ^ 2 * gaussG s) := by
      field_simp
    rw [e]
    exact (mul_le_mul_of_nonneg_right (inv_cube_le hr (le_of_lt hs))
      (mul_nonneg (sq_nonneg (m s)) (gaussG_pos s).le)).trans (le_of_eq (by ring))
  · rw [integral_const_mul]
    have e : (Real.sqrt (moment5 m) * (r ^ 4)⁻¹) ^ 2 = (r ^ 8)⁻¹ * moment5 m := by
      rw [mul_pow, Real.sq_sqrt hM, inv_pow, ← pow_mul]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left
      (setIntegral_moment5_le m hm.int5 (Ioi_subset_Ioi hr.le)) (by positivity)

/-- The prefactors of `eq:st18-t00007`: `‖R g r‖ ≤ ¼ (r⁻² ‖∫₀^r s³ g‖ + r² ‖∫_r^∞ s⁻¹ g‖)`. -/
theorem norm_R_le_parts (g : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    ‖R g r‖ ≤ 1 / 4 * ((r ^ 2)⁻¹ * ‖∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * g s‖ +
      r ^ 2 * ‖∫ s in Ioi r, (s : ℂ)⁻¹ * g s‖) := by
  unfold R
  rw [norm_mul]
  have h1 : ‖-(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
  rw [h1]
  gcongr
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr]

/-- **Green bound for `R(m f)`**: for an admissible multiplier `m`, `f ∈ X_G` and `r > 0`,
`|R(m f)(r)| ≤ ½ (√c + (∫₀^∞ s⁵ m² G)^{1/2}) ‖f‖_{X_G} min(r, r⁻²)`. -/
theorem norm_R_mul_le (hm : Admissible m c) {f : ℝ → ℂ} (hf : MemXG f) {r : ℝ} (hr : 0 < r) :
    ‖R (fun s => (m s : ℂ) * f s) r‖ ≤
      (Real.sqrt c + Real.sqrt (moment5 m)) / 2 * xGNorm f * min r (r ^ 2)⁻¹ := by
  have hP := norm_R_le_parts (fun s => (m s : ℂ) * f s) hr
  have hI1 := norm_firstIntegral_le m f hr
  have hI2 := norm_secondIntegral_le m f r
  have h1a := (firstIntegral_le_small hm hf hr).2
  have h1b := firstIntegral_le_large hm hf r
  have h2a := (secondIntegral_le_small hm hf hr).2
  have h2b := secondIntegral_le_large hm hf hr
  have hN := xGNorm_nonneg f
  have sc := Real.sqrt_nonneg c
  have sM := Real.sqrt_nonneg (moment5 m)
  have hK : 0 ≤ (Real.sqrt c + Real.sqrt (moment5 m)) / 2 * xGNorm f := by positivity
  rw [mul_min_of_nonneg _ _ hK]
  refine le_min (hP.trans ?_) (hP.trans ?_)
  · calc 1 / 4 * ((r ^ 2)⁻¹ * ‖∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * ((m s : ℂ) * f s)‖ +
          r ^ 2 * ‖∫ s in Ioi r, (s : ℂ)⁻¹ * ((m s : ℂ) * f s)‖)
        ≤ 1 / 4 * ((r ^ 2)⁻¹ * (Real.sqrt c * r ^ 3 * xGNorm f) +
          r ^ 2 * (Real.sqrt c * r⁻¹ * xGNorm f)) := by
          gcongr
          · exact hI1.trans h1a
          · exact hI2.trans h2a
      _ = Real.sqrt c / 2 * xGNorm f * r := by
          field_simp
          ring
      _ ≤ (Real.sqrt c + Real.sqrt (moment5 m)) / 2 * xGNorm f * r := by
          gcongr
          linarith
  · calc 1 / 4 * ((r ^ 2)⁻¹ * ‖∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * ((m s : ℂ) * f s)‖ +
          r ^ 2 * ‖∫ s in Ioi r, (s : ℂ)⁻¹ * ((m s : ℂ) * f s)‖)
        ≤ 1 / 4 * ((r ^ 2)⁻¹ * (Real.sqrt (moment5 m) * xGNorm f) +
          r ^ 2 * (Real.sqrt (moment5 m) * (r ^ 4)⁻¹ * xGNorm f)) := by
          gcongr
          · exact hI1.trans h1b
          · exact hI2.trans h2b
      _ = Real.sqrt (moment5 m) / 2 * xGNorm f * (r ^ 2)⁻¹ := by
          field_simp
          ring
      _ ≤ (Real.sqrt c + Real.sqrt (moment5 m)) / 2 * xGNorm f * (r ^ 2)⁻¹ := by
          gcongr
          linarith

/-- For an admissible multiplier both integrals of `eq:st18-t00007` for `R(m f)` converge
absolutely, so `R(m f)(r)` is the manuscript's value, not a Bochner junk value. -/
theorem integrable_parts_mul (hm : Admissible m c) {f : ℝ → ℂ} (hf : MemXG f) {r : ℝ}
    (hr : 0 < r) :
    IntervalIntegrable (fun s : ℝ => (s : ℂ) ^ 3 * ((m s : ℂ) * f s)) volume 0 r ∧
      IntegrableOn (fun s : ℝ => (s : ℂ)⁻¹ * ((m s : ℂ) * f s)) (Ioi r) := by
  have hmeas : AEStronglyMeasurable (fun s => (m s : ℂ) * f s) (volume.restrict (Ioi 0)) :=
    (Complex.continuous_ofReal.comp hm.cont).aestronglyMeasurable.mul hf.1
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le]
    refine (firstIntegral_le_small hm hf hr).1.mono'
      ((Complex.continuous_ofReal.pow 3).aestronglyMeasurable.mul
        (hmeas.mono_set Ioc_subset_Ioi_self)) (Eventually.of_forall fun s => le_of_eq ?_)
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow]
    ring
  · refine (secondIntegral_le_small hm hf hr).1.mono'
      ((Complex.measurable_ofReal.inv).aestronglyMeasurable.mul
        (hmeas.mono_set (Ioi_subset_Ioi hr.le))) (Eventually.of_forall fun s => le_of_eq ?_)
    simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_inv]
    ring

/-- If moreover `∫₀^∞ s m² G < ∞`, then `m f` satisfies B0011's hypothesis `WProf`
(`s m f ∈ L¹(0, ∞)`), so B0011's existence and uniqueness theorems apply to `R(m f)`. -/
theorem wprof_mul (hm : Admissible m c)
    (hm1 : IntegrableOn (fun s => s * (m s ^ 2 * gaussG s)) (Ioi 0)) {f : ℝ → ℂ}
    (hf : MemXG f) : WProf (fun s => (m s : ℂ) * f s) := by
  have hmeas : AEStronglyMeasurable (fun s => (m s : ℂ) * f s) (volume.restrict (Ioi 0)) :=
    (Complex.continuous_ofReal.comp hm.cont).aestronglyMeasurable.mul hf.1
  refine ⟨hmeas, ?_⟩
  have h := (cauchySchwarz hf measurableSet_Ioi subset_rfl
    (w := fun s => s * m s) (measurable_id.mul hm.cont.measurable)
    (a := fun s => s * (m s ^ 2 * gaussG s)) hm1
    (fun s hs => by
      have hs0 : (0 : ℝ) < s := hs
      apply le_of_eq
      field_simp) (Real.sqrt_nonneg (∫ s in Ioi 0, s * (m s ^ 2 * gaussG s)))
    (by rw [Real.sq_sqrt (setIntegral_nonneg measurableSet_Ioi fun s hs => by
          have h1 := gaussG_pos s
          have hs' : (0 : ℝ) < s := hs
          positivity)])).1
  refine h.congr_fun (fun s hs => ?_) measurableSet_Ioi
  have hs0 : (0 : ℝ) < s := hs
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hs0]
  ring

end Multiplier

/-! ### The two multipliers of the manuscript: `1` and `x - 2` -/

/-- The multiplier `m = 1` (the bound for `Rf`) is admissible with `c = 1`. -/
theorem admissible_one : Admissible (fun _ => 1) 1 where
  cont := continuous_const
  bdd := fun s _ => by
    rw [one_pow, one_mul]
    exact gaussG_le_one s
  int5 := (integrableOn_pow_mul_gaussG 5).congr_fun (fun s _ => by simp) measurableSet_Ioi

/-- `(x - 2)² G ≤ 6` with `x = r²/4`. -/
theorem xm2_sq_mul_gaussG_le (s : ℝ) : (xVar s - 2) ^ 2 * gaussG s ≤ 6 := by
  have hx : 0 ≤ s ^ 2 / 4 := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hx
  have h1 : 1 ≤ Real.exp (s ^ 2 / 4) := Real.one_le_exp hx
  have hsq : (xVar s - 2) ^ 2 ≤ 6 * Real.exp (s ^ 2 / 4) := by
    unfold xVar
    nlinarith
  have hE : Real.exp (s ^ 2 / 4) * Real.exp (-(s ^ 2 / 4)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc (xVar s - 2) ^ 2 * gaussG s ≤ 6 * Real.exp (s ^ 2 / 4) * Real.exp (-(s ^ 2 / 4)) :=
        mul_le_mul hsq (gaussG_le_exp s) (gaussG_pos s).le (by positivity)
    _ = 6 := by rw [mul_assoc, hE, mul_one]

theorem xm2_expand (s : ℝ) (k : ℕ) :
    s ^ k * ((xVar s - 2) ^ 2 * gaussG s) =
      1 / 16 * (s ^ (k + 4) * gaussG s) - s ^ (k + 2) * gaussG s + 4 * (s ^ k * gaussG s) := by
  unfold xVar
  ring

theorem integrableOn_pow_mul_xm2 (k : ℕ) :
    IntegrableOn (fun s => s ^ k * ((xVar s - 2) ^ 2 * gaussG s)) (Ioi 0) := by
  have h := (((integrableOn_pow_mul_gaussG (k + 4)).const_mul (1 / 16)).sub
    (integrableOn_pow_mul_gaussG (k + 2))).add ((integrableOn_pow_mul_gaussG k).const_mul 4)
  refine IntegrableOn.congr_fun h (fun s _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [xm2_expand]

/-- The multiplier `m = x - 2`, `x = r²/4` (the bound for `R((x-2)f)`, tex line 1422), is
admissible with `c = 6`. -/
theorem admissible_xm2 : Admissible (fun s => xVar s - 2) 6 where
  cont := by unfold xVar; fun_prop
  bdd := fun s _ => xm2_sq_mul_gaussG_le s
  int5 := integrableOn_pow_mul_xm2 5

/-- `(x - 2) f` satisfies B0011's hypothesis `WProf` for `f ∈ X_G`, so `R((x-2)f)` solves
`Δ₂ψ = (x-2)f` by B0011 (`WProf.isDelta2Sol_R`). -/
theorem wprof_xm2 {f : ℝ → ℂ} (hf : MemXG f) :
    WProf (fun s => ((xVar s - 2 : ℝ) : ℂ) * f s) := by
  refine wprof_mul admissible_xm2 ?_ hf
  refine (integrableOn_pow_mul_xm2 1).congr_fun (fun s _ => ?_) measurableSet_Ioi
  simp only [pow_one]

/-- Both integrals of `eq:st18-t00007` for `R((x-2)f)` converge absolutely (tex line 1422):
no junk value enters the bound for `R((x-2)f)`. -/
theorem integrable_parts_xm2 {f : ℝ → ℂ} (hf : MemXG f) {r : ℝ} (hr : 0 < r) :
    IntervalIntegrable (fun s : ℝ => (s : ℂ) ^ 3 * (((xVar s - 2 : ℝ) : ℂ) * f s)) volume 0 r ∧
      IntegrableOn (fun s : ℝ => (s : ℂ)⁻¹ * (((xVar s - 2 : ℝ) : ℂ) * f s)) (Ioi r) :=
  integrable_parts_mul admissible_xm2 hf hr

theorem R_one_mul (f : ℝ → ℂ) : R (fun s => (((fun _ : ℝ => (1 : ℝ)) s : ℝ) : ℂ) * f s) = R f := by
  congr 1
  funext s
  simp

/-! ### The Green bound `eq:st18-t00062` -/

/-- The constant of `eq:st18-t00062`. -/
def greenConst : ℝ :=
  max ((Real.sqrt 1 + Real.sqrt (moment5 fun _ => 1)) / 2)
    ((Real.sqrt 6 + Real.sqrt (moment5 fun s => xVar s - 2)) / 2)

theorem greenConst_nonneg : 0 ≤ greenConst :=
  le_max_of_le_left (by positivity)

/-- **`eq:st18-t00062`** (`paper/main.tex` lines 1417–1422), with the explicit constant
`greenConst`: for every `f ∈ X_G` and every `r > 0`,
`|Rf(r)| ≤ C ‖f‖_{X_G} min(r, r⁻²)` and `|R((x-2)f)(r)| ≤ C ‖f‖_{X_G} min(r, r⁻²)`,
`x = r²/4`. -/
theorem green_bound_const {f : ℝ → ℂ} (hf : MemXG f) {r : ℝ} (hr : 0 < r) :
    ‖R f r‖ ≤ greenConst * xGNorm f * min r (r ^ 2)⁻¹ ∧
      ‖R (fun s => ((xVar s - 2 : ℝ) : ℂ) * f s) r‖ ≤
        greenConst * xGNorm f * min r (r ^ 2)⁻¹ := by
  have hN := xGNorm_nonneg f
  have hmin : 0 ≤ min r (r ^ 2)⁻¹ := le_min hr.le (by positivity)
  constructor
  · have h := norm_R_mul_le admissible_one hf hr
    rw [R_one_mul] at h
    refine h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hN) hmin)
  · have h := norm_R_mul_le admissible_xm2 hf hr
    refine h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hN) hmin)

/-- **`eq:st18-t00062`** (`paper/main.tex` lines 1417–1422): there is `C < ∞` such that for
every `f = f₂(r)e^{2iϑ} ∈ X_G` (profile `f₂ = f`, `MemXG f`) and every `r > 0`,
`|Rf(r)| ≤ C ‖f‖_{X_G} min(r, r⁻²)`; the same estimate holds for `R((x-2)f)`, `x = r²/4`. -/
theorem green_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ, MemXG f → ∀ r : ℝ, 0 < r →
      ‖R f r‖ ≤ C * xGNorm f * min r (r ^ 2)⁻¹ ∧
      ‖R (fun s => ((xVar s - 2 : ℝ) : ℂ) * f s) r‖ ≤ C * xGNorm f * min r (r ^ 2)⁻¹ :=
  ⟨greenConst, greenConst_nonneg, fun _ hf _ hr => green_bound_const hf hr⟩

/-! ### The same bound on B0010's Hilbert space `XG` -/

/-- Every element of B0010's `XG = Lp ℂ 2 xGMeasure` is a profile of `X_G`. -/
theorem memXG_coe (f : B0010.XG) : MemXG (f : ℝ → ℂ) := by
  have hm : AEStronglyMeasurable (f : ℝ → ℂ) (volume.restrict (Ioi 0)) :=
    (Lp.stronglyMeasurable f).aestronglyMeasurable
  refine ⟨hm, ?_⟩
  have h := (B0010.memLp_iff_integrableOn hm).1 (Lp.memLp f)
  refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
  rw [mul_assoc]
  rfl

/-- `xGNorm` is the norm of B0010's Hilbert space `XG`. -/
theorem xGNorm_eq_norm (f : B0010.XG) : xGNorm (f : ℝ → ℂ) = ‖f‖ := by
  have h := B0010.norm_sq_toLp (Lp.memLp f)
  rw [Lp.toLp_coeFn] at h
  rw [xGNorm, ← Real.sqrt_sq (norm_nonneg f), h]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
  rw [mul_assoc]
  rfl

/-- **`eq:st18-t00062`** on the Hilbert space `X_G` of B0010: there is `C < ∞` with
`|Rf(r)| ≤ C ‖f‖_{X_G} min(r, r⁻²)` and `|R((x-2)f)(r)| ≤ C ‖f‖_{X_G} min(r, r⁻²)` for every
`f ∈ X_G` and `r > 0` (`R` only integrates `f`, so it does not depend on the representative). -/
theorem green_bound_XG :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : B0010.XG, ∀ r : ℝ, 0 < r →
      ‖R f r‖ ≤ C * ‖f‖ * min r (r ^ 2)⁻¹ ∧
      ‖R (fun s => ((xVar s - 2 : ℝ) : ℂ) * f s) r‖ ≤ C * ‖f‖ * min r (r ^ 2)⁻¹ := by
  refine ⟨greenConst, greenConst_nonneg, fun f r hr => ?_⟩
  rw [← xGNorm_eq_norm]
  exact green_bound_const (memXG_coe f) hr

/-! ### The proof sketch of tex line 1421, before the prefactors -/

theorem firstIntegral_one (f : ℝ → ℂ) (r : ℝ) :
    (∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * f s) =
      ∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * ((((fun _ : ℝ => (1 : ℝ)) s : ℝ) : ℂ) * f s) := by
  simp

theorem secondIntegral_one (f : ℝ → ℂ) (r : ℝ) :
    (∫ s in Ioi r, (s : ℂ)⁻¹ * f s) =
      ∫ s in Ioi r, (s : ℂ)⁻¹ * ((((fun _ : ℝ => (1 : ℝ)) s : ℝ) : ℂ) * f s) := by
  simp

/-- Tex line 1421: near zero the first integral of `eq:st18-t00007` is `O(r³)`:
`|∫₀^r s³ f(s) ds| ≤ ‖f‖_{X_G} r³` for `f ∈ X_G`, `r > 0`. -/
theorem firstIntegral_le_cube {f : ℝ → ℂ} (hf : MemXG f) {r : ℝ} (hr : 0 < r) :
    ‖∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * f s‖ ≤ xGNorm f * r ^ 3 := by
  rw [firstIntegral_one]
  refine (norm_firstIntegral_le _ f hr).trans
    (((firstIntegral_le_small admissible_one hf hr).2).trans (le_of_eq ?_))
  rw [Real.sqrt_one]
  ring

/-- Tex line 1421: near zero the second integral of `eq:st18-t00007` is `O(r⁻¹)`:
`|∫_r^∞ s⁻¹ f(s) ds| ≤ ‖f‖_{X_G} r⁻¹` for `f ∈ X_G`, `r > 0`. -/
theorem secondIntegral_le_inv {f : ℝ → ℂ} (hf : MemXG f) {r : ℝ} (hr : 0 < r) :
    ‖∫ s in Ioi r, (s : ℂ)⁻¹ * f s‖ ≤ xGNorm f * r⁻¹ := by
  rw [secondIntegral_one]
  refine (norm_secondIntegral_le _ f r).trans
    (((secondIntegral_le_small admissible_one hf hr).2).trans (le_of_eq ?_))
  rw [Real.sqrt_one]
  ring

/-- Tex line 1421: at infinity the first integral of `eq:st18-t00007` is bounded by the
third radial moment `∫₀^∞ s³ |f(s)| ds`, which is finite for `f ∈ X_G`
(`B0011.MemXG.integrable_cube`). -/
theorem firstIntegral_le_thirdMoment {f : ℝ → ℂ} (hf : MemXG f) {r : ℝ} (hr : 0 < r) :
    ‖∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * f s‖ ≤ ∫ s in Ioi 0, s ^ 3 * ‖f s‖ := by
  rw [intervalIntegral.integral_of_le hr.le]
  refine (norm_integral_le_integral_norm _).trans ?_
  have e : ∫ s in Ioc 0 r, ‖(s : ℂ) ^ 3 * f s‖ = ∫ s in Ioc 0 r, s ^ 3 * ‖f s‖ := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    have hs0 : 0 < s := hs.1
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
  rw [e]
  refine setIntegral_mono_set hf.integrable_cube ?_ (ae_of_all _ Ioc_subset_Ioi_self)
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
  have hs' : (0 : ℝ) < s := hs
  simp only [Pi.zero_apply]
  positivity

/-- Tex line 1421: at infinity the second integral of `eq:st18-t00007` is Gaussian-small:
there is `C < ∞` with `|∫_r^∞ s⁻¹ f(s) ds| ≤ C ‖f‖_{X_G} r⁻⁴ e^{-r²/16}` for `f ∈ X_G`,
`r > 0`. -/
theorem secondIntegral_gaussianSmall :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ, MemXG f → ∀ r : ℝ, 0 < r →
      ‖∫ s in Ioi r, (s : ℂ)⁻¹ * f s‖ ≤
        C * xGNorm f * ((r ^ 4)⁻¹ * Real.exp (-(r ^ 2 / 16))) := by
  have hint : IntegrableOn (fun s : ℝ => s ^ (5 : ℝ) * Real.exp (-(1 / 8) * s ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num) (by norm_num)
  have hM : 0 ≤ ∫ s in Ioi 0, s ^ (5 : ℝ) * Real.exp (-(1 / 8) * s ^ 2) :=
    setIntegral_nonneg measurableSet_Ioi fun s hs => by
      have : (0 : ℝ) < s := hs
      positivity
  refine ⟨Real.sqrt (∫ s in Ioi 0, s ^ (5 : ℝ) * Real.exp (-(1 / 8) * s ^ 2)),
    Real.sqrt_nonneg _, fun f hf r hr => ?_⟩
  rw [secondIntegral_one]
  refine (norm_secondIntegral_le _ f r).trans ?_
  have hCS := (cauchySchwarz hf measurableSet_Ioi (Ioi_subset_Ioi hr.le)
    (w := fun s => s⁻¹ * (fun _ : ℝ => (1 : ℝ)) s) (measurable_inv.mul measurable_const)
    (a := fun s => (r ^ 8)⁻¹ * Real.exp (-(r ^ 2 / 8)) *
      (s ^ (5 : ℝ) * Real.exp (-(1 / 8) * s ^ 2)))
    ((hint.mono_set (Ioi_subset_Ioi hr.le)).const_mul _) ?_
    (β := Real.sqrt (∫ s in Ioi 0, s ^ (5 : ℝ) * Real.exp (-(1 / 8) * s ^ 2)) *
      ((r ^ 4)⁻¹ * Real.exp (-(r ^ 2 / 16)))) (by positivity) ?_).2
  · exact hCS.trans (le_of_eq (by ring))
  · intro s hs
    have hs0 : 0 < s := hr.trans hs
    have hrs : r ≤ s := le_of_lt hs
    have e5 : s ^ (5 : ℝ) = s ^ 5 := by exact_mod_cast Real.rpow_natCast s 5
    have e : (s⁻¹ * 1) ^ 2 * gaussG s / s = (s ^ 3)⁻¹ * gaussG s := by
      field_simp
    have hG : gaussG s ≤ Real.exp (-(r ^ 2 / 8)) * Real.exp (-(1 / 8) * s ^ 2) := by
      rw [← Real.exp_add]
      refine (gaussG_le_exp s).trans (Real.exp_le_exp.2 ?_)
      nlinarith
    rw [e, e5]
    calc (s ^ 3)⁻¹ * gaussG s
        ≤ (r ^ 8)⁻¹ * s ^ 5 * (Real.exp (-(r ^ 2 / 8)) * Real.exp (-(1 / 8) * s ^ 2)) :=
          mul_le_mul (inv_cube_le hr hrs) hG (gaussG_pos s).le (by positivity)
      _ = _ := by ring
  · rw [integral_const_mul]
    have hx : Real.exp (-(r ^ 2 / 16)) ^ 2 = Real.exp (-(r ^ 2 / 8)) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have e : (Real.sqrt (∫ s in Ioi 0, s ^ (5 : ℝ) * Real.exp (-(1 / 8) * s ^ 2)) *
        ((r ^ 4)⁻¹ * Real.exp (-(r ^ 2 / 16)))) ^ 2 = (r ^ 8)⁻¹ * Real.exp (-(r ^ 2 / 8)) *
          ∫ s in Ioi 0, s ^ (5 : ℝ) * Real.exp (-(1 / 8) * s ^ 2) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hM, hx, inv_pow, ← pow_mul]
      ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine setIntegral_mono_set hint ?_ (ae_of_all _ (Ioi_subset_Ioi hr.le))
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    have hs' : (0 : ℝ) < s := hs
    simp only [Pi.zero_apply]
    positivity

end UnforcedLeray.B0086
