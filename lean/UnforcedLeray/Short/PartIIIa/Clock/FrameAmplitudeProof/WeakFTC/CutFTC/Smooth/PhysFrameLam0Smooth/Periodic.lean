import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.Smooth.PhysFrameLam0Smooth.Term
import UnforcedLeray.Lib.Gaussian.Periodization

/-!
# Joint smoothness of the periodized physical-variable dual rows

Helper for `PartIII-a:T21/c5/1/1/2/2` (SP 2891-2905).  For a `Good` kernel `L` the function
`P_L(r, x) = perSum c (physAdj (clockA ν r) L) x` is differentiable on `{a(r) > 0}` with
`∂_v P_L = ν v₁ a⁻¹ P_{EL} + a^{-1/2} P_{∂_{v₂} L}` (`fderiv_perPhys_apply`): termwise
differentiation with summable bounds on boxes.  Since `Good` is closed under `L ↦ EL` and
`L ↦ ∂_w L`, induction on the order gives `C^∞` (`contDiffOn_perPhys`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.LamJetInf

open UnforcedLeray.Short.IIIa.SeedJet2Aux

/-- The shift `(r, x) ↦ (r, (x₁ + n c, x₂))`. -/
def shiftV (c : ℝ) (n : ℤ) : ℝ × (ℝ × ℝ) := (0, ((n : ℝ) * c, 0))

/-- `P_L(r, x) = perSum c (physAdj (clockA ν r) L) x`. -/
def perPhys (ν c : ℝ) (L : ℝ × ℝ → ℂ) (p : ℝ × (ℝ × ℝ)) : ℂ :=
  perSum c (physAdj (clockA ν p.1) L) p.2

/-- The open set `{a(r) > 0}`. -/
def physU (ν : ℝ) : Set (ℝ × (ℝ × ℝ)) := {p | 0 < clockA ν p.1}

theorem isOpen_physU (ν : ℝ) : IsOpen (physU ν) :=
  isOpen_lt continuous_const ((CutFTCSmooth.contDiff_clockA ν).continuous.comp continuous_fst)

theorem shiftV_fst (c : ℝ) (n : ℤ) (p : ℝ × (ℝ × ℝ)) : (p + shiftV c n).1 = p.1 := by
  simp [shiftV]

theorem shiftV_snd_fst (c : ℝ) (n : ℤ) (p : ℝ × (ℝ × ℝ)) :
    (p + shiftV c n).2.1 = p.2.1 + n * c := by
  simp [shiftV]

theorem perPhys_eq (ν c : ℝ) (L : ℝ × ℝ → ℂ) (p : ℝ × (ℝ × ℝ)) :
    perPhys ν c L p = ∑' n : ℤ, physTerm ν L (p + shiftV c n) := by
  unfold perPhys perSum physTerm
  refine tsum_congr fun n => ?_
  rw [shiftV_fst]
  congr 1
  ext <;> simp [shiftV]

/-- `∑_{n∈ℤ} (1 + |x₀ + n c|)^{-2} < ∞`. -/
theorem summable_inv_sq_shift {c : ℝ} (hc : c ≠ 0) (x₀ : ℝ) :
    Summable (fun n : ℤ => ((1 + |x₀ + n * c|) ^ 2)⁻¹) := by
  have h := Gaussian.summable_translate (s := 2) (by norm_num) (neg_ne_zero.2 hc) x₀
  refine h.congr fun n => ?_
  rw [show x₀ - n * -c = x₀ + n * c by ring, Real.rpow_neg (by positivity), Real.rpow_two]

/-- The scaled point `ι(q)` is at distance `≳ |x₀|` when `|q.2.1 - x₀| < 1` and `a(q) ≤ A`. -/
theorem inv_sq_iota_le {ν A x₀ : ℝ} {q : ℝ × (ℝ × ℝ)} (ha : 0 < clockA ν q.1)
    (haA : clockA ν q.1 ≤ A) (hx : |q.2.1 - x₀| < 1) :
    ((1 + ‖iotaP ν q‖) ^ 2)⁻¹ ≤ 4 * max 1 A * ((1 + |x₀|) ^ 2)⁻¹ := by
  set a := clockA ν q.1 with ha_def
  set S := max 1 A with hS
  have hS1 : 1 ≤ S := le_max_left _ _
  have haS : a ≤ S := haA.trans (le_max_right _ _)
  have hsa0 : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsS1 : 1 ≤ Real.sqrt S := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hS1
  have hsaS : Real.sqrt a ≤ Real.sqrt S := Real.sqrt_le_sqrt haS
  have hι : |q.2.1| / Real.sqrt a ≤ ‖iotaP ν q‖ := by
    rw [iotaP, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hsa0, inv_mul_eq_div]
    gcongr
    rw [← Real.norm_eq_abs]
    exact norm_fst_le q.2
  have hkey : 1 + |q.2.1| ≤ Real.sqrt S * (1 + ‖iotaP ν q‖) := by
    have h1 : |q.2.1| ≤ Real.sqrt S * (|q.2.1| / Real.sqrt a) := by
      rw [mul_div_assoc', le_div_iff₀ hsa0]
      exact mul_le_mul_of_nonneg_left hsaS (abs_nonneg _) |>.trans_eq (by ring)
    nlinarith [norm_nonneg (iotaP ν q)]
  have hx0 : 1 + |x₀| ≤ 2 * (1 + |q.2.1|) := by
    have := abs_sub_abs_le_abs_sub x₀ q.2.1
    rw [abs_sub_comm] at hx
    linarith [abs_nonneg q.2.1]
  have hsq : (1 + |x₀|) ^ 2 ≤ 4 * S * (1 + ‖iotaP ν q‖) ^ 2 := by
    have h2 : 1 + |x₀| ≤ 2 * Real.sqrt S * (1 + ‖iotaP ν q‖) := by nlinarith
    have h3 : (1 + |x₀|) ^ 2 ≤ (2 * Real.sqrt S * (1 + ‖iotaP ν q‖)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    calc (1 + |x₀|) ^ 2 ≤ (2 * Real.sqrt S * (1 + ‖iotaP ν q‖)) ^ 2 := h3
      _ = 4 * Real.sqrt S ^ 2 * (1 + ‖iotaP ν q‖) ^ 2 := by ring
      _ = 4 * S * (1 + ‖iotaP ν q‖) ^ 2 := by rw [Real.sq_sqrt (by linarith)]
  have hp1 : 0 < (1 + ‖iotaP ν q‖) ^ 2 := by positivity
  have hp2 : 0 < (1 + |x₀|) ^ 2 := by positivity
  rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ hp1 hp2]
  linarith

/-- Summability of `n ↦ L(ι(p + n c e₁))` for `Good L`. -/
theorem summable_good_shift {ν c : ℝ} (hc : c ≠ 0) {L : ℝ × ℝ → ℂ} (hL : Good L)
    {p : ℝ × (ℝ × ℝ)} (ha : 0 < clockA ν p.1) :
    Summable (fun n : ℤ => L (iotaP ν (p + shiftV c n))) := by
  obtain ⟨C, hC0, hC⟩ := hL.norm_le
  refine Summable.of_norm_bounded
    ((summable_inv_sq_shift hc p.2.1).mul_left (C * (4 * max 1 (clockA ν p.1)))) fun n => ?_
  have ha' : 0 < clockA ν (p + shiftV c n).1 := by rw [shiftV_fst]; exact ha
  have hι := inv_sq_iota_le (x₀ := p.2.1 + n * c) (A := clockA ν p.1) ha'
    (by rw [shiftV_fst]) (by rw [shiftV_snd_fst, sub_self, abs_zero]; norm_num)
  have h1 := hC (iotaP ν (p + shiftV c n))
  have hp : 0 < (1 + ‖iotaP ν (p + shiftV c n)‖) ^ 2 := by positivity
  have h2 : ‖L (iotaP ν (p + shiftV c n))‖ ≤ C * ((1 + ‖iotaP ν (p + shiftV c n)‖) ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hp]; exact h1
  calc ‖L (iotaP ν (p + shiftV c n))‖ ≤ C * ((1 + ‖iotaP ν (p + shiftV c n)‖) ^ 2)⁻¹ := h2
    _ ≤ C * (4 * max 1 (clockA ν p.1) * ((1 + |p.2.1 + n * c|) ^ 2)⁻¹) := by gcongr
    _ = C * (4 * max 1 (clockA ν p.1)) * ((1 + |p.2.1 + n * c|) ^ 2)⁻¹ := by ring

/-- Termwise differentiation of `P_L` with summable bounds on a box around `p₀`. -/
theorem hasFDerivAt_perPhys {ν c : ℝ} (hν : 0 < ν) (hc : c ≠ 0) {L : ℝ × ℝ → ℂ} (hL : Good L)
    {p₀ : ℝ × (ℝ × ℝ)} (ha₀ : 0 < clockA ν p₀.1) :
    HasFDerivAt (perPhys ν c L) (∑' n : ℤ, physTermD ν L (p₀ + shiftV c n)) p₀ ∧
      Summable (fun n : ℤ => physTermD ν L (p₀ + shiftV c n)) := by
  set a₀ := clockA ν p₀.1 with ha₀_def
  set δ := a₀ / (2 * ν) with hδ
  have hδ0 : 0 < δ := by positivity
  set A := 2 * a₀ with hA
  set box : Set (ℝ × (ℝ × ℝ)) :=
    Ioo (p₀.1 - δ) (p₀.1 + δ) ×ˢ (Ioo (p₀.2.1 - 1) (p₀.2.1 + 1) ×ˢ (univ : Set ℝ)) with hbox
  have hbox_a : ∀ p ∈ box, 0 < clockA ν p.1 ∧ clockA ν p.1 ≤ A := by
    intro p hp
    obtain ⟨⟨h1, h2⟩, -⟩ := hp
    have e : clockA ν p.1 = a₀ + ν * (p.1 - p₀.1) := by
      simp only [ha₀_def, clockA]; ring
    have hνδ : ν * δ = a₀ / 2 := by rw [hδ]; field_simp
    have h3 : ν * (p.1 - p₀.1) < ν * δ := mul_lt_mul_of_pos_left (by linarith) hν
    have h4 : -(ν * δ) < ν * (p.1 - p₀.1) := by nlinarith
    constructor <;> nlinarith
  have hbox_x : ∀ p ∈ box, |p.2.1 - p₀.2.1| < 1 := by
    intro p hp
    obtain ⟨-, ⟨h1, h2⟩, -⟩ := hp
    rw [abs_lt]; constructor <;> linarith
  have hp₀ : p₀ ∈ box := by
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, mem_univ _⟩
  have hopen : IsOpen box := isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_univ)
  have hpre : IsPreconnected box :=
    ((convex_Ioo _ _).prod ((convex_Ioo _ _).prod convex_univ)).isPreconnected
  obtain ⟨CE, hCE0, hCE⟩ := hL.eulerK.norm_le
  obtain ⟨CD, hCD0, hCD⟩ := hL.fderiv_norm_le
  set M := (ν * CE + Real.sqrt A * CD) * (4 * max 1 A) with hM
  set u : ℤ → ℝ := fun n => M * ((1 + |p₀.2.1 + n * c|) ^ 2)⁻¹ with hu_def
  have hu : Summable u := (summable_inv_sq_shift hc _).mul_left M
  have hD : ∀ (n : ℤ) (p : ℝ × (ℝ × ℝ)), p ∈ box →
      ‖physTermD ν L (p + shiftV c n)‖ ≤ u n := by
    intro n p hp
    obtain ⟨ha, haA⟩ := hbox_a p hp
    set q := p + shiftV c n with hq
    have hq1 : q.1 = p.1 := shiftV_fst c n p
    rw [← hq1] at ha haA
    have hxq : |q.2.1 - (p₀.2.1 + n * c)| < 1 := by
      rw [hq, shiftV_snd_fst, show p.2.1 + n * c - (p₀.2.1 + n * c) = p.2.1 - p₀.2.1 by ring]
      exact hbox_x p hp
    have hι := inv_sq_iota_le ha haA hxq
    set w := ((1 + ‖iotaP ν q‖) ^ 2)⁻¹ with hw
    have hw0 : 0 ≤ w := by positivity
    have hp1 : 0 < (1 + ‖iotaP ν q‖) ^ 2 := by positivity
    have hE : ‖eulerK L (iotaP ν q)‖ ≤ CE * w := by
      rw [hw, ← div_eq_mul_inv, le_div_iff₀ hp1]; exact hCE _
    have hDb : ‖fderiv ℝ L (iotaP ν q)‖ ≤ CD * w := by
      rw [hw, ← div_eq_mul_inv, le_div_iff₀ hp1]
      refine le_trans ?_ (hCD (iotaP ν q))
      gcongr
      · exact le_add_of_nonneg_right (norm_nonneg _)
      · norm_num
    have hsa : Real.sqrt (clockA ν q.1) ≤ Real.sqrt A := Real.sqrt_le_sqrt haA
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [physTermD_apply ν L ha v]
    have hv1 : |v.1| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le v
    have hv2 : ‖v.2‖ ≤ ‖v‖ := norm_snd_le v
    calc ‖((ν * v.1 : ℝ) : ℂ) * eulerK L (iotaP ν q) +
          ((Real.sqrt (clockA ν q.1) : ℝ) : ℂ) * fderiv ℝ L (iotaP ν q) v.2‖
        ≤ ν * |v.1| * ‖eulerK L (iotaP ν q)‖ +
            Real.sqrt (clockA ν q.1) * (‖fderiv ℝ L (iotaP ν q)‖ * ‖v.2‖) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_mul, abs_of_pos hν, abs_of_nonneg (Real.sqrt_nonneg _)]
          gcongr
          exact (fderiv ℝ L (iotaP ν q)).le_opNorm v.2
      _ ≤ ν * ‖v‖ * (CE * w) + Real.sqrt A * ((CD * w) * ‖v‖) := by gcongr
      _ = (ν * CE + Real.sqrt A * CD) * w * ‖v‖ := by ring
      _ ≤ (ν * CE + Real.sqrt A * CD) * (4 * max 1 A * ((1 + |p₀.2.1 + n * c|) ^ 2)⁻¹) * ‖v‖ := by
          gcongr
      _ = u n * ‖v‖ := by rw [hu_def, hM]; ring
  have hf : ∀ (n : ℤ) (p : ℝ × (ℝ × ℝ)), p ∈ box →
      HasFDerivAt (fun p => physTerm ν L (p + shiftV c n)) (physTermD ν L (p + shiftV c n)) p := by
    intro n p hp
    have ha : 0 < clockA ν (p + shiftV c n).1 := by rw [shiftV_fst]; exact (hbox_a p hp).1
    have h1 := hasFDerivAt_physTerm ν hL.differentiable ha
    have h2 : HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => p + shiftV c n)
        (ContinuousLinearMap.id ℝ (ℝ × (ℝ × ℝ))) p := (hasFDerivAt_id p).add_const _
    have h3 := h1.comp p h2
    rw [ContinuousLinearMap.comp_id] at h3
    exact h3
  have hf0 : Summable (fun n : ℤ => physTerm ν L (p₀ + shiftV c n)) := by
    have hs := (summable_good_shift (ν := ν) hc hL ha₀).mul_left ((a₀ : ℝ) : ℂ)
    refine hs.congr fun n => ?_
    rw [physTerm_eq]
    simp only [shiftV_fst, Complex.real_smul, ← ha₀_def]
  refine ⟨?_, Summable.of_norm_bounded hu fun n => hD n p₀ hp₀⟩
  have h := hasFDerivAt_tsum_of_isPreconnected hu hopen hpre hf hD hp₀ hf0 hp₀
  have heq : perPhys ν c L = fun y => ∑' n : ℤ, physTerm ν L (y + shiftV c n) :=
    funext (perPhys_eq ν c L)
  rw [heq]
  exact h

/-- The partial derivatives of `P_L` are again of the form `P_{L'}` with `Good L'`. -/
theorem fderiv_perPhys_apply {ν c : ℝ} (hν : 0 < ν) (hc : c ≠ 0) {L : ℝ × ℝ → ℂ} (hL : Good L)
    {p : ℝ × (ℝ × ℝ)} (ha : 0 < clockA ν p.1) (v : ℝ × (ℝ × ℝ)) :
    fderiv ℝ (perPhys ν c L) p v =
      ((ν * v.1 * (clockA ν p.1)⁻¹ : ℝ) : ℂ) * perPhys ν c (eulerK L) p +
        ((Real.sqrt (clockA ν p.1) * (clockA ν p.1)⁻¹ : ℝ) : ℂ) *
          perPhys ν c (fun z => fderiv ℝ L z v.2) p := by
  obtain ⟨hD, hsum⟩ := hasFDerivAt_perPhys hν hc hL ha
  rw [hD.fderiv]
  have h1 : (∑' n : ℤ, physTermD ν L (p + shiftV c n)) v =
      ∑' n : ℤ, physTermD ν L (p + shiftV c n) v := by
    have := (ContinuousLinearMap.apply ℝ ℂ v).map_tsum hsum
    simpa using this
  rw [h1]
  have hterm : ∀ n : ℤ, physTermD ν L (p + shiftV c n) v =
      ((ν * v.1 : ℝ) : ℂ) * eulerK L (iotaP ν (p + shiftV c n)) +
        ((Real.sqrt (clockA ν p.1) : ℝ) : ℂ) * fderiv ℝ L (iotaP ν (p + shiftV c n)) v.2 := by
    intro n
    have ha' : 0 < clockA ν (p + shiftV c n).1 := by rw [shiftV_fst]; exact ha
    rw [physTermD_apply ν L ha' v, shiftV_fst]
  rw [tsum_congr hterm]
  have hsE := summable_good_shift (ν := ν) hc hL.eulerK ha
  have hsD := summable_good_shift (ν := ν) hc (hL.fderiv_apply v.2) ha
  rw [(hsE.mul_left _).tsum_add (hsD.mul_left _), tsum_mul_left, tsum_mul_left]
  have hP : ∀ L' : ℝ × ℝ → ℂ, perPhys ν c L' p =
      ((clockA ν p.1 : ℝ) : ℂ) * ∑' n : ℤ, L' (iotaP ν (p + shiftV c n)) := by
    intro L'
    rw [perPhys_eq, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [physTerm_eq]
    simp only [shiftV_fst, Complex.real_smul]
  rw [hP, hP]
  have ha0 : ((clockA ν p.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  push_cast
  field_simp

/-- `P_L` is `C^n` on `{a > 0}` for every `n` and every `Good L`. -/
theorem contDiffOn_perPhys_nat {ν c : ℝ} (hν : 0 < ν) (hc : c ≠ 0) (n : ℕ) :
    ∀ L : ℝ × ℝ → ℂ, Good L → ContDiffOn ℝ n (perPhys ν c L) (physU ν) := by
  induction n with
  | zero =>
    intro L hL
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun p hp => (hasFDerivAt_perPhys hν hc hL hp).1.continuousAt.continuousWithinAt
  | succ n ih =>
    intro L hL
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen (isOpen_physU ν)]
    refine ⟨fun p hp => (hasFDerivAt_perPhys hν hc hL hp).1.differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    rw [contDiffOn_clm_apply]
    intro v
    have hE := ih (eulerK L) hL.eulerK
    have hDv := ih (fun z => fderiv ℝ L z v.2) (hL.fderiv_apply v.2)
    have hA : ContDiffOn ℝ n (fun p : ℝ × (ℝ × ℝ) => clockA ν p.1) (physU ν) :=
      (((CutFTCSmooth.contDiff_clockA ν).comp contDiff_fst).of_le (le_top_nat n)).contDiffOn
    have hAinv : ContDiffOn ℝ n (fun p : ℝ × (ℝ × ℝ) => (clockA ν p.1)⁻¹) (physU ν) :=
      hA.inv fun p hp => (ne_of_gt hp)
    have hsq : ContDiffOn ℝ n (fun p : ℝ × (ℝ × ℝ) => Real.sqrt (clockA ν p.1)) (physU ν) :=
      hA.sqrt fun p hp => (ne_of_gt hp)
    have hc1 : ContDiffOn ℝ n
        (fun p : ℝ × (ℝ × ℝ) => (((ν * v.1 * (clockA ν p.1)⁻¹ : ℝ)) : ℂ)) (physU ν) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.mul hAinv)
    have hc2 : ContDiffOn ℝ n
        (fun p : ℝ × (ℝ × ℝ) => ((Real.sqrt (clockA ν p.1) * (clockA ν p.1)⁻¹ : ℝ) : ℂ))
        (physU ν) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (hsq.mul hAinv)
    refine ((hc1.mul hE).add (hc2.mul hDv)).congr fun p hp => ?_
    exact fderiv_perPhys_apply hν hc hL hp v

/-- **Joint `C^∞` smoothness of `P_L` on `{a > 0}`** for `Good L`. -/
theorem contDiffOn_perPhys {ν c : ℝ} (hν : 0 < ν) (hc : c ≠ 0) {L : ℝ × ℝ → ℂ} (hL : Good L) :
    ContDiffOn ℝ ∞ (perPhys ν c L) (physU ν) :=
  contDiffOn_infty.2 fun n => contDiffOn_perPhys_nat hν hc n L hL

end UnforcedLeray.Short.IIIa.LamJetInf
