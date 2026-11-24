import UnforcedLeray.Lib.Kernels.GaussDeriv
import UnforcedLeray.Lib.Kernels.ParamIntegral
import UnforcedLeray.Lib.Kernels.IterApply

/-!
# INF22 K1: the heat-time potential Φ_t = ∫_t^∞ G_a da


(§5, bypasses BP4 and BP5). The manuscript writes the Oseen kernel as
(K_t)_{ij} = δ_{ij}G_t + ∂_i∂_j∫_t^∞ G_a da (`paper/main.tex` 8882–8918, blueprint units B0554,
B0557). This module defines `Φ_t = heatTimePotential t` and proves:

* `iteratedFDeriv_heatTimePotential`: Dⁿ Φ_t(x) = ∫_t^∞ Dⁿ G_a(x) da for t ≥ 0 and x ≠ 0 or t > 0;
* `contDiffOn_heatTimePotential`: Φ_t is smooth on {x ≠ 0} (on all of ℝ³ if t > 0);
* `norm_iteratedFDeriv_heatTimePotential_le`: ‖Dⁿ Φ_t(x)‖ ≤ Cₙ |x|^{-(1+n)}, **uniformly in t ≥ 0**;
* `heatTimePotential_zero`: Φ_0 = N = (4π|x|)^{-1} off the origin (compiled `integral_heatKernel_time`);
* `iteratedFDeriv_heatTimePotential_sub` and `norm_iteratedFDeriv_heatTimePotential_sub_le`:
  Dⁿ Φ_t − Dⁿ Φ_0 = −∫_0^t Dⁿ G_a, with ‖·‖ ≤ C t |x|^{-(3+n)} (the input of (3.8), tex 8919–8924).

The time supremum `rpow_mul_exp_le_rpow` (a^{-m/2} e^{-r²/(8a)} ≤ C_m r^{-m}) is the part of G2 that
K1 and K4 need.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ContDiff Topology Nat

namespace UnforcedLeray.Kernels

/-! ### The time supremum (part of INF22 G2) -/

/-- `u^s e^{-u} ≤ 1 + ⌈s⌉!` for `u, s ≥ 0`. -/
theorem rpow_mul_exp_neg_le {s : ℝ} (hs : 0 ≤ s) {u : ℝ} (hu : 0 ≤ u) :
    u ^ s * Real.exp (-u) ≤ 1 + ((⌈s⌉₊)! : ℝ) := by
  set k := ⌈s⌉₊
  have hk : s ≤ k := Nat.le_ceil s
  have hexp : 0 < Real.exp (-u) := Real.exp_pos _
  have hf0 : (0 : ℝ) ≤ k ! := by positivity
  rcases le_or_gt u 1 with h1 | h1
  · have h2 : u ^ s ≤ 1 := Real.rpow_le_one hu h1 hs
    have h3 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h4 : 0 ≤ u ^ s := Real.rpow_nonneg hu s
    nlinarith
  · have hus : u ^ s ≤ u ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le h1.le hk
    rw [Real.rpow_natCast] at hus
    have hfac : u ^ k ≤ k ! * Real.exp u := by
      have := Real.pow_div_factorial_le_exp (x := u) hu k
      have hf : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
      rw [div_le_iff₀ hf] at this
      linarith
    calc u ^ s * Real.exp (-u) ≤ (k ! * Real.exp u) * Real.exp (-u) := by gcongr; linarith
      _ = k ! := by rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ 1 + k ! := by linarith

/-- The constant of `rpow_mul_exp_le_rpow`. -/
def timeSupConst (m : ℝ) : ℝ := 8 ^ (m / 2) * (1 + ((⌈m / 2⌉₊)! : ℝ))

theorem timeSupConst_nonneg (m : ℝ) : 0 ≤ timeSupConst m := by
  unfold timeSupConst; positivity

/-- The supremum over time of a Gaussian majorant (INF22 G2 `sup_time_le`):
`a^{-m/2} e^{-r²/(8a)} ≤ C_m r^{-m}` for `a, r > 0`, `m ≥ 0`. -/
theorem rpow_mul_exp_le_rpow {m : ℝ} (hm : 0 ≤ m) {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    a ^ (-(m / 2)) * Real.exp (-r ^ 2 / (8 * a)) ≤ timeSupConst m * r ^ (-m) := by
  set u := r ^ 2 / (8 * a) with hu_def
  have hu0 : 0 ≤ u := by positivity
  have hu : u ^ (m / 2) = r ^ m / (8 ^ (m / 2) * a ^ (m / 2)) := by
    rw [hu_def, Real.div_rpow (by positivity) (by positivity),
      Real.mul_rpow (by norm_num) ha.le]
    congr 1
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    congr 1
    push_cast
    ring
  have hid : a ^ (-(m / 2)) = 8 ^ (m / 2) * u ^ (m / 2) * r ^ (-m) := by
    rw [hu, Real.rpow_neg hr.le, Real.rpow_neg ha.le]
    have h1 : (0 : ℝ) < r ^ m := Real.rpow_pos_of_pos hr m
    have h2 : (0 : ℝ) < 8 ^ (m / 2) := by positivity
    have h3 : (0 : ℝ) < a ^ (m / 2) := Real.rpow_pos_of_pos ha _
    field_simp
  have hexp : -r ^ 2 / (8 * a) = -u := by rw [hu_def]; ring
  rw [hid, hexp]
  have hb := rpow_mul_exp_neg_le (s := m / 2) (by linarith) hu0
  have h8 : (0 : ℝ) ≤ 8 ^ (m / 2) := by positivity
  have hr' : (0 : ℝ) ≤ r ^ (-m) := Real.rpow_nonneg hr.le _
  calc 8 ^ (m / 2) * u ^ (m / 2) * r ^ (-m) * Real.exp (-u)
      = 8 ^ (m / 2) * r ^ (-m) * (u ^ (m / 2) * Real.exp (-u)) := by ring
    _ ≤ 8 ^ (m / 2) * r ^ (-m) * (1 + ((⌈m / 2⌉₊)! : ℝ)) := by gcongr
    _ = timeSupConst m * r ^ (-m) := by unfold timeSupConst; ring

/-! ### Definition and domination -/

/-- The heat-time potential Φ_t(x) = ∫_t^∞ G_a(x) da (INF22 K1; tex 8882–8918). For t = 0 and
x = 0 the integral diverges and Lean's value is the junk value 0; every statement below assumes
x ≠ 0 or t > 0. -/
def heatTimePotential (t : ℝ) (x : Space) : ℝ := ∫ a in Ioi t, Heat.kernel a x

/-- The set where Φ_t is finite and smooth: x ≠ 0, or every x when t > 0. -/
def potentialDomain (t : ℝ) : Set Space := {x | x ≠ 0 ∨ 0 < t}

theorem isOpen_potentialDomain (t : ℝ) : IsOpen (potentialDomain t) := by
  by_cases ht : 0 < t
  · have : potentialDomain t = univ := by ext x; simp [potentialDomain, ht]
    rw [this]; exact isOpen_univ
  · have : potentialDomain t = {x | x ≠ 0} := by ext x; simp [potentialDomain, ht]
    rw [this]; exact isOpen_ne

theorem heatKernel_zero : Heat.kernel 0 = 0 := by
  funext x
  rw [Heat.kernel_formula]
  simp [Real.zero_rpow (by norm_num : -(3 : ℝ) / 2 ≠ 0)]

theorem aestronglyMeasurable_heat {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (x : Space) :
    AEStronglyMeasurable (fun a => iteratedFDeriv ℝ n (Heat.kernel a) x)
      (volume.restrict (Ioi t)) :=
  ((continuousOn_iteratedFDeriv_heatKernel n x).mono (Ioi_subset_Ioi ht)).aestronglyMeasurable
    measurableSet_Ioi

/-- The heat majorant in the inverse-time Gamma form. -/
theorem heatMajorant_eq (n : ℕ) (a r : ℝ) :
    heatDerivConst n * a ^ (-((3 + n : ℝ) / 2)) * Real.exp (-r ^ 2 / (8 * a)) =
      heatDerivConst n * (a ^ (-(((1 + n : ℝ) / 2) + 1)) * Real.exp (-(r ^ 2 / 8) / a)) := by
  have h1 : -((3 + n : ℝ) / 2) = -(((1 + n : ℝ) / 2) + 1) := by ring
  have h2 : -r ^ 2 / (8 * a) = -(r ^ 2 / 8) / a := by ring
  rw [h1, h2, mul_assoc]

theorem integrableOn_heatMajorant (n : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun a => heatDerivConst n * a ^ (-((3 + n : ℝ) / 2)) *
      Real.exp (-r ^ 2 / (8 * a))) (Ioi 0) := by
  have h := (PressureAnalysis.integrableOn_inverseTimeGamma (a := r ^ 2 / 8) (p := (1 + n : ℝ) / 2)
    (by positivity) (by positivity)).const_mul (heatDerivConst n)
  have hfun : (fun a => heatDerivConst n * a ^ (-((3 + n : ℝ) / 2)) *
      Real.exp (-r ^ 2 / (8 * a))) = fun a => heatDerivConst n *
        (a ^ (-(((1 + n : ℝ) / 2) + 1)) * Real.exp (-(r ^ 2 / 8) / a)) :=
    funext fun a => heatMajorant_eq n a r
  rw [hfun]
  exact h

theorem locDominated_heat {t : ℝ} (ht : 0 ≤ t) :
    LocDominated (volume.restrict (Ioi t)) Heat.kernel (potentialDomain t) := by
  intro n x hx
  rcases hx with hx | htpos
  · have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
    refine ⟨ball x (‖x‖ / 2), ball_mem_nhds x (by positivity),
      fun a => heatDerivConst n * a ^ (-((3 + n : ℝ) / 2)) * Real.exp (-(‖x‖ / 2) ^ 2 / (8 * a)),
      ?_, ?_⟩
    · exact (integrableOn_heatMajorant n (r := ‖x‖ / 2) (by positivity)).mono_set
        (Ioi_subset_Ioi ht)
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun a (ha : t < a) y hy => ?_
      have ha0 : 0 < a := lt_of_le_of_lt ht ha
      refine (norm_iteratedFDeriv_heatKernel_le n ha0 y).trans ?_
      have hy' : ‖x‖ / 2 ≤ ‖y‖ := by
        have h1 := mem_ball.1 hy
        rw [dist_eq_norm] at h1
        have h2 := norm_sub_norm_le x y
        rw [norm_sub_rev] at h2
        linarith
      have hexp : Real.exp (-‖y‖ ^ 2 / (8 * a)) ≤ Real.exp (-(‖x‖ / 2) ^ 2 / (8 * a)) := by
        apply Real.exp_le_exp.2
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : (‖x‖ / 2) ^ 2 ≤ ‖y‖ ^ 2 := by gcongr
        linarith
      have hc := (heatDerivConst_pos n).le
      have hp : 0 ≤ a ^ (-((3 + n : ℝ) / 2)) := Real.rpow_nonneg ha0.le _
      exact le_of_le_of_eq (mul_le_mul_of_nonneg_left hexp (mul_nonneg hc hp)) rfl
  · refine ⟨univ, univ_mem, fun a => heatDerivConst n * a ^ (-((3 + n : ℝ) / 2)), ?_, ?_⟩
    · exact (integrableOn_Ioi_rpow_of_lt (by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith) htpos).const_mul _
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun a (ha : t < a) y _ => ?_
      have ha0 : 0 < a := htpos.trans ha
      refine (norm_iteratedFDeriv_heatKernel_le n ha0 y).trans ?_
      have h1 : Real.exp (-‖y‖ ^ 2 / (8 * a)) ≤ 1 := by
        apply Real.exp_le_one_iff.2
        apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
        nlinarith [sq_nonneg ‖y‖]
      have hc := (heatDerivConst_pos n).le
      have hp : 0 ≤ a ^ (-((3 + n : ℝ) / 2)) := Real.rpow_nonneg ha0.le _
      calc heatDerivConst n * a ^ (-((3 + n : ℝ) / 2)) * Real.exp (-‖y‖ ^ 2 / (8 * a))
          ≤ heatDerivConst n * a ^ (-((3 + n : ℝ) / 2)) * 1 := by gcongr
        _ = heatDerivConst n * a ^ (-((3 + n : ℝ) / 2)) := mul_one _

/-! ### K1 statements -/

theorem integrableOn_heatKernel_time {t : ℝ} (ht : 0 ≤ t) {x : Space} (hx : x ≠ 0 ∨ 0 < t) :
    IntegrableOn (fun a => Heat.kernel a x) (Ioi t) :=
  (locDominated_heat ht).integrable_apply (aestronglyMeasurable_heat ht) hx

theorem integrableOn_iteratedFDeriv_heatKernel_time (n : ℕ) {t : ℝ} (ht : 0 ≤ t) {x : Space}
    (hx : x ≠ 0 ∨ 0 < t) :
    IntegrableOn (fun a => iteratedFDeriv ℝ n (Heat.kernel a) x) (Ioi t) :=
  (locDominated_heat ht).integrable (aestronglyMeasurable_heat ht) n hx

/-- Differentiation under the integral: Dⁿ Φ_t(x) = ∫_t^∞ Dⁿ G_a(x) da (INF22 K1). -/
theorem iteratedFDeriv_heatTimePotential (n : ℕ) {t : ℝ} (ht : 0 ≤ t) {x : Space}
    (hx : x ≠ 0 ∨ 0 < t) :
    iteratedFDeriv ℝ n (heatTimePotential t) x =
      ∫ a in Ioi t, iteratedFDeriv ℝ n (Heat.kernel a) x :=
  iteratedFDeriv_integral_eq (isOpen_potentialDomain t) (ae_of_all _ heatKernel_smooth)
    (aestronglyMeasurable_heat ht) (locDominated_heat ht) n hx

/-- Smoothness of Φ_t on {x ≠ 0} (on all of ℝ³ when t > 0) (INF22 K1). -/
theorem contDiffOn_heatTimePotential {t : ℝ} (ht : 0 ≤ t) :
    ContDiffOn ℝ ∞ (heatTimePotential t) {x | x ≠ 0 ∨ 0 < t} :=
  contDiffOn_integral (isOpen_potentialDomain t) (ae_of_all _ heatKernel_smooth)
    (aestronglyMeasurable_heat ht) (locDominated_heat ht)

theorem contDiffAt_heatTimePotential {t : ℝ} (ht : 0 ≤ t) {x : Space} (hx : x ≠ 0 ∨ 0 < t) :
    ContDiffAt ℝ ∞ (heatTimePotential t) x :=
  (contDiffOn_heatTimePotential ht).contDiffAt ((isOpen_potentialDomain t).mem_nhds hx)

/-- Φ_0 is the Newton potential off the origin (compiled `integral_heatKernel_time`). -/
theorem heatTimePotential_zero {x : Space} (hx : x ≠ 0) :
    heatTimePotential 0 x = PressureAnalysis.newtonPotential x := by
  unfold heatTimePotential
  rw [PressureAnalysis.integral_heatKernel_time hx]
  rfl

/-- The constant of `norm_iteratedFDeriv_heatTimePotential_le`. -/
def potentialConst (n : ℕ) : ℝ :=
  heatDerivConst n * 8 ^ ((1 + n : ℝ) / 2) * Real.Gamma ((1 + n : ℝ) / 2)

theorem integral_heatMajorant (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫ a in Ioi (0 : ℝ), heatDerivConst n * a ^ (-((3 + n : ℝ) / 2)) * Real.exp (-r ^ 2 / (8 * a)) =
      potentialConst n * r ^ (-(1 + n : ℝ)) := by
  simp_rw [heatMajorant_eq n _ r]
  rw [integral_const_mul, PressureAnalysis.integral_inverseTimeGamma (by positivity)
    (by positivity)]
  have hpow : (r ^ 2 / 8) ^ (-((1 + n : ℝ) / 2)) = 8 ^ ((1 + n : ℝ) / 2) * r ^ (-(1 + n : ℝ)) := by
    rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8),
      div_inv_eq_mul, ← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    rw [show ((2 : ℕ) : ℝ) * -((1 + n : ℝ) / 2) = -(1 + n : ℝ) by push_cast; ring]
    ring
  rw [hpow, potentialConst]
  ring

/-- The bound ‖Dⁿ Φ_t(x)‖ ≤ Cₙ |x|^{-(1+n)}, uniform in t ≥ 0 (INF22 K1, BP4; tex 8882–8918). -/
theorem norm_iteratedFDeriv_heatTimePotential_le' (n : ℕ) {t : ℝ} (ht : 0 ≤ t) {x : Space}
    (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ n (heatTimePotential t) x‖ ≤ potentialConst n * ‖x‖ ^ (-(1 + n : ℝ)) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hx' : x ∈ potentialDomain t := Or.inl hx
  have h1 := norm_iteratedFDeriv_integral_le (isOpen_potentialDomain t)
    (ae_of_all _ heatKernel_smooth) (aestronglyMeasurable_heat ht) (locDominated_heat ht) n hx'
  refine h1.trans ?_
  have hmaj := integrableOn_heatMajorant n hr
  calc ∫ a in Ioi t, ‖iteratedFDeriv ℝ n (Heat.kernel a) x‖
      ≤ ∫ a in Ioi t, heatDerivConst n * a ^ (-((3 + n : ℝ) / 2)) *
          Real.exp (-‖x‖ ^ 2 / (8 * a)) := by
        refine setIntegral_mono_on ?_ (hmaj.mono_set (Ioi_subset_Ioi ht)) measurableSet_Ioi ?_
        · exact (integrableOn_iteratedFDeriv_heatKernel_time n ht hx').norm
        · intro a ha
          exact norm_iteratedFDeriv_heatKernel_le n (lt_of_le_of_lt ht ha) x
    _ ≤ ∫ a in Ioi (0 : ℝ), heatDerivConst n * a ^ (-((3 + n : ℝ) / 2)) *
          Real.exp (-‖x‖ ^ 2 / (8 * a)) := by
        refine setIntegral_mono_set hmaj ?_ (Eventually.of_forall (Ioi_subset_Ioi ht))
        rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
        refine Eventually.of_forall fun a (ha : 0 < a) => ?_
        have := (heatDerivConst_pos n).le
        have : 0 ≤ a ^ (-((3 + n : ℝ) / 2)) := Real.rpow_nonneg ha.le _
        simp only [Pi.zero_apply]
        positivity
    _ = potentialConst n * ‖x‖ ^ (-(1 + n : ℝ)) := integral_heatMajorant n hr

/-- INF22 K1 `norm_iteratedFDeriv_heatTimePotential_le`, in the quantifier form of the note:
one constant for all t ≥ 0 and x ≠ 0. -/
theorem norm_iteratedFDeriv_heatTimePotential_le (n : ℕ) : ∃ C, ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
    x ≠ 0 → ‖iteratedFDeriv ℝ n (heatTimePotential t) x‖ ≤ C * ‖x‖ ^ (-(1 + n : ℝ)) :=
  ⟨potentialConst n, fun _ ht _ hx => norm_iteratedFDeriv_heatTimePotential_le' n ht hx⟩

/-! ### The difference Φ_t − Φ_0 (input of (3.8)) -/

/-- Dⁿ Φ_t(x) − Dⁿ Φ_0(x) = −∫_0^t Dⁿ G_a(x) da for x ≠ 0, t ≥ 0. -/
theorem iteratedFDeriv_heatTimePotential_sub (n : ℕ) {t : ℝ} (ht : 0 ≤ t) {x : Space}
    (hx : x ≠ 0) :
    iteratedFDeriv ℝ n (heatTimePotential t) x - iteratedFDeriv ℝ n (heatTimePotential 0) x =
      -∫ a in Ioc 0 t, iteratedFDeriv ℝ n (Heat.kernel a) x := by
  rw [iteratedFDeriv_heatTimePotential n ht (Or.inl hx),
    iteratedFDeriv_heatTimePotential n le_rfl (Or.inl hx)]
  have hint := integrableOn_iteratedFDeriv_heatKernel_time n le_rfl (Or.inl hx)
  rw [← Ioc_union_Ioi_eq_Ioi ht, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi ht))]
  abel

/-- ‖Dⁿ Φ_t(x) − Dⁿ Φ_0(x)‖ ≤ C t |x|^{-(3+n)} (input of (3.8), tex 8919–8924). -/
theorem norm_iteratedFDeriv_heatTimePotential_sub_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) {x : Space}
    (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ n (heatTimePotential t) x - iteratedFDeriv ℝ n (heatTimePotential 0) x‖ ≤
      heatDerivConst n * timeSupConst (3 + n) * t * ‖x‖ ^ (-(3 + n : ℝ)) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [iteratedFDeriv_heatTimePotential_sub n ht hx, norm_neg]
  have hbound : ∀ a ∈ Ioc (0 : ℝ) t, ‖iteratedFDeriv ℝ n (Heat.kernel a) x‖ ≤
      heatDerivConst n * timeSupConst (3 + n) * ‖x‖ ^ (-(3 + n : ℝ)) := by
    intro a ha
    refine (norm_iteratedFDeriv_heatKernel_le n ha.1 x).trans ?_
    have hs := rpow_mul_exp_le_rpow (m := 3 + n) (by positivity) ha.1 hr
    have hc := (heatDerivConst_pos n).le
    calc heatDerivConst n * a ^ (-((3 + n : ℝ) / 2)) * Real.exp (-‖x‖ ^ 2 / (8 * a))
        = heatDerivConst n * (a ^ (-((3 + n : ℝ) / 2)) * Real.exp (-‖x‖ ^ 2 / (8 * a))) := by
          ring
      _ ≤ heatDerivConst n * (timeSupConst (3 + n) * ‖x‖ ^ (-(3 + n : ℝ))) := by gcongr
      _ = _ := by ring
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (by simp) hbound
  rw [Real.volume_real_Ioc_of_le ht, sub_zero] at h
  calc _ ≤ heatDerivConst n * timeSupConst (3 + n) * ‖x‖ ^ (-(3 + n : ℝ)) * t := h
    _ = _ := by ring

end UnforcedLeray.Kernels
