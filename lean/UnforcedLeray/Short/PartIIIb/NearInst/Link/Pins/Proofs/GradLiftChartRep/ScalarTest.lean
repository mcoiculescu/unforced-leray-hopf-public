import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_3_2

/-!
# `gradLiftScalarTest` (task `PartIII-b:C/near/pins/3/3/2/2`)

Source `the November 2 reference manuscript` 1666, 1675-1677, 2666-2668, 2683.

`ψ(τ, y) = Ψ(chartOf ε⁻¹ c y τ)` equals `Ψ(Gpt x)` for the unreduced chart point `Gpt`, because
`Ψ` is `c`-periodic in `q`.  `Gpt` is smooth off the axis, and `ψ` vanishes near the axis since
the band `s₀ ≤ s` keeps the chart away from `s = 0`.  The phase `τ` shifts `q` by `c` when `τ`
shifts by `2εc`, and the band in `s` and `η` bounds the support in `y`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

/-- The unreduced chart point of a similarity point with `R = ε⁻¹` (source 2666-2668). -/
private def Gpt (ε : ℝ) (x : ℝ × Space) : Chart :=
  (ε⁻¹ ^ 2 / hRad x.2 ^ 2,
    (ε⁻¹ * Real.log (hRad x.2 / ε⁻¹) + ε⁻¹ * x.1 / 2, ε⁻¹ * x.2 2 / hRad x.2))

/-- The lift equals `Ψ` of the unreduced chart point (periodicity in `q`). -/
private theorem liftScalar_eq {c ε : ℝ} (Ψ : UnforcedLeray.B0226.ProfileTest c)
    (x : ℝ × Space) : liftScalar c ε Ψ x = Ψ.1 (Gpt ε x) := by
  unfold liftScalar chartOf Gpt
  have hper : Function.Periodic
      (fun q : ℝ => Ψ.1 (ε⁻¹ ^ 2 / hRad x.2 ^ 2, q, ε⁻¹ * x.2 2 / hRad x.2)) c :=
    fun q => Ψ.2.periodic (ε⁻¹ ^ 2 / hRad x.2 ^ 2, q, ε⁻¹ * x.2 2 / hRad x.2)
  have h : Ψ.1 (ε⁻¹ ^ 2 / hRad x.2 ^ 2,
      (ε⁻¹ * Real.log (hRad x.2 / ε⁻¹) + ε⁻¹ * x.1 / 2 -
        ↑(⌊(ε⁻¹ * Real.log (hRad x.2 / ε⁻¹) + ε⁻¹ * x.1 / 2) / c + 1 / 2⌋ : ℤ) * c,
        ε⁻¹ * x.2 2 / hRad x.2)) =
      Ψ.1 (ε⁻¹ ^ 2 / hRad x.2 ^ 2, (ε⁻¹ * Real.log (hRad x.2 / ε⁻¹) + ε⁻¹ * x.1 / 2,
        ε⁻¹ * x.2 2 / hRad x.2)) :=
    hper.sub_int_mul_eq _
  have h2 : ε⁻¹ * Real.log (hRad x.2 / ε⁻¹) + ε⁻¹ * x.1 / 2 -
      c * ↑⌊(ε⁻¹ * Real.log (hRad x.2 / ε⁻¹) + ε⁻¹ * x.1 / 2) / c + 1 / 2⌋ =
      ε⁻¹ * Real.log (hRad x.2 / ε⁻¹) + ε⁻¹ * x.1 / 2 -
      ↑⌊(ε⁻¹ * Real.log (hRad x.2 / ε⁻¹) + ε⁻¹ * x.1 / 2) / c + 1 / 2⌋ * c := by
    ring
  rw [h2, h]

/-- The unreduced chart point moves by `(0, c, 0)` under `τ ↦ τ + 2εc`. -/
private theorem Gpt_shift (c ε : ℝ) (hε : 0 < ε) (τ : ℝ) (y : Space) :
    Gpt ε (τ + 2 * ε * c, y) =
      ((Gpt ε (τ, y)).1, ((Gpt ε (τ, y)).2.1 + c, (Gpt ε (τ, y)).2.2)) := by
  have hε' : ε ≠ 0 := hε.ne'
  have hQ : ε⁻¹ * (τ + 2 * ε * c) / 2 = ε⁻¹ * τ / 2 + c := by
    field_simp <;> ring
  unfold Gpt
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  show ε⁻¹ * Real.log (hRad y / ε⁻¹) + ε⁻¹ * (τ + 2 * ε * c) / 2 =
    (ε⁻¹ * Real.log (hRad y / ε⁻¹) + ε⁻¹ * τ / 2) + c
  rw [hQ]
  ring

/-- Smoothness of the unreduced chart point off the axis. -/
private theorem contDiffAt_Gpt {ε : ℝ} (hε : 0 < ε) (x : ℝ × Space) (hx : 0 < hRad x.2) :
    ContDiffAt ℝ ∞ (Gpt ε) x := by
  have hz : ∀ i : Fin 3, ContDiff ℝ ∞ (fun z : Space => z i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff
  have hsq : ContDiffAt ℝ ∞ (fun y : ℝ × Space => y.2 0 ^ 2 + y.2 1 ^ 2) x :=
    ((((hz 0).comp contDiff_snd).pow 2).add (((hz 1).comp contDiff_snd).pow 2)).contDiffAt
  have hpos : (fun y : ℝ × Space => y.2 0 ^ 2 + y.2 1 ^ 2) x ≠ 0 := by
    have h := hx
    unfold hRad at h
    exact (Real.sqrt_pos.1 h).ne'
  have hR : ContDiffAt ℝ ∞ (fun y : ℝ × Space => hRad y.2) x := by
    unfold hRad
    exact hsq.sqrt hpos
  have hR0 : hRad x.2 ≠ 0 := hx.ne'
  have hz2 : ContDiffAt ℝ ∞ (fun y : ℝ × Space => y.2 2) x :=
    ((hz 2).comp contDiff_snd).contDiffAt
  have hlog : hRad x.2 / ε⁻¹ ≠ 0 := div_ne_zero hR0 (inv_ne_zero hε.ne')
  unfold Gpt
  refine ContDiffAt.prodMk ?_ (ContDiffAt.prodMk ?_ ?_)
  · exact contDiffAt_const.div (hR.pow 2) (pow_ne_zero 2 hR0)
  · refine ContDiffAt.add ?_ ?_
    · exact contDiffAt_const.mul ((hR.div_const _).log hlog)
    · exact (contDiffAt_const.mul contDiffAt_fst).div_const 2
  · exact (contDiffAt_const.mul hz2).div hR hR0

theorem gradLiftScalarTest : GradLiftScalarTest := by
  intro c ε hc hε Ψ
  obtain ⟨s0, s1, L, hs0, hband⟩ := Ψ.2.band
  have hRpos : 0 < ε⁻¹ := inv_pos.2 hε
  -- the lift vanishes near the axis
  have hsmall : ∀ x : ℝ × Space, s1 * hRad x.2 ^ 2 < ε⁻¹ ^ 2 →
      Ψ.1 (Gpt ε x) = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨hI, -⟩ := hband _ hne
    have hI0 : s0 ≤ ε⁻¹ ^ 2 / hRad x.2 ^ 2 := hI.1
    have hI1 : ε⁻¹ ^ 2 / hRad x.2 ^ 2 ≤ s1 := hI.2
    have hpos : 0 < hRad x.2 ^ 2 := by
      rcases (sq_nonneg (hRad x.2)).lt_or_eq with h | h
      · exact h
      · rw [← h, div_zero] at hI0
        linarith
    rw [div_le_iff₀ hpos] at hI1
    linarith
  refine ⟨?_, ?_, ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hA : s1 * hRad x.2 ^ 2 < ε⁻¹ ^ 2
    · have hcontR : Continuous (fun y : ℝ × Space => hRad y.2) := by
        unfold hRad
        fun_prop
      have hfc : ContinuousAt (fun y : ℝ × Space => s1 * hRad y.2 ^ 2) x :=
        (continuous_const.mul (hcontR.pow 2)).continuousAt
      have hcont : ∀ᶠ y in nhds x, s1 * hRad y.2 ^ 2 < ε⁻¹ ^ 2 :=
        ContinuousAt.eventually_lt hfc continuousAt_const hA
      have hz : (fun y : ℝ × Space => ((liftScalar c ε Ψ y : ℝ) : ℂ)) =ᶠ[nhds x]
          fun _ => (0 : ℂ) := by
        filter_upwards [hcont] with y hy
        show ((liftScalar c ε Ψ y : ℝ) : ℂ) = 0
        rw [liftScalar_eq, hsmall y hy]
        simp
      exact contDiffAt_const.congr_of_eventuallyEq hz
    · push_neg at hA
      have hpos2 : 0 < hRad x.2 ^ 2 := by
        rcases (sq_nonneg (hRad x.2)).lt_or_eq with h | h
        · exact h
        · rw [← h, mul_zero] at hA
          linarith [pow_pos hRpos 2]
      have hnn : 0 ≤ hRad x.2 := Real.sqrt_nonneg _
      have hx : 0 < hRad x.2 := by
        rcases hnn.lt_or_eq with h | h
        · exact h
        · rw [← h] at hpos2
          norm_num at hpos2
      have hΨ : ContDiffAt ℝ ∞ Ψ.1 (Gpt ε x) := Ψ.2.smooth.contDiffAt
      have hcomp : ContDiffAt ℝ ∞ (fun y => Ψ.1 (Gpt ε y)) x :=
        ContDiffAt.comp x hΨ (contDiffAt_Gpt hε x hx)
      simp only [liftScalar_eq]
      exact (Complex.ofRealCLM.contDiff.contDiffAt).comp x hcomp
  · intro τ y
    have hp := Ψ.2.periodic (Gpt ε (τ, y))
    simp only [liftScalar_eq]
    rw [Gpt_shift c ε hε τ y]
    exact congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) hp
  · refine ⟨Real.sqrt ((ε⁻¹ ^ 2 + L ^ 2) / s0), fun τ y hy => ?_⟩
    by_contra hne
    have hne' : Ψ.1 (Gpt ε (τ, y)) ≠ 0 := by
      intro h
      apply hne
      show ((liftScalar c ε Ψ (τ, y) : ℝ) : ℂ) = 0
      rw [liftScalar_eq, h]
      simp
    obtain ⟨hI, hL⟩ := hband _ hne'
    have hI0 : s0 ≤ ε⁻¹ ^ 2 / hRad y ^ 2 := hI.1
    have hL' : |ε⁻¹ * y 2 / hRad y| ≤ L := hL
    have hnn : 0 ≤ hRad y := Real.sqrt_nonneg _
    have hϱpos : 0 < hRad y := by
      rcases hnn.lt_or_eq with h | h
      · exact h
      · rw [← h] at hI0
        simp at hI0
        linarith
    have hne0 : hRad y ≠ 0 := hϱpos.ne'
    have hsq : hRad y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
      unfold hRad
      exact Real.sq_sqrt (by positivity)
    have hpos2 : 0 < hRad y ^ 2 := pow_pos hϱpos 2
    have F1 : s0 * hRad y ^ 2 ≤ ε⁻¹ ^ 2 := (le_div_iff₀ hpos2).1 hI0
    have h2 : (ε⁻¹ * y 2 / hRad y) ^ 2 ≤ L ^ 2 :=
      sq_le_sq' (abs_le.1 hL').1 (abs_le.1 hL').2
    have h3 : ε⁻¹ ^ 2 * y 2 ^ 2 ≤ L ^ 2 * hRad y ^ 2 := by
      have e : (ε⁻¹ * y 2 / hRad y) ^ 2 * hRad y ^ 2 = ε⁻¹ ^ 2 * y 2 ^ 2 := by
        field_simp
      calc ε⁻¹ ^ 2 * y 2 ^ 2 = (ε⁻¹ * y 2 / hRad y) ^ 2 * hRad y ^ 2 := e.symm
        _ ≤ L ^ 2 * hRad y ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    have F3 : s0 * y 2 ^ 2 ≤ L ^ 2 := by
      have hR2 : 0 < ε⁻¹ ^ 2 := pow_pos hRpos 2
      have h4 : ε⁻¹ ^ 2 * (s0 * y 2 ^ 2) ≤ ε⁻¹ ^ 2 * L ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left h3 hs0.le, mul_le_mul_of_nonneg_left F1 (sq_nonneg L)]
      exact le_of_mul_le_mul_left h4 hR2
    have F4 : s0 * (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) ≤ ε⁻¹ ^ 2 + L ^ 2 := by
      rw [← hsq]
      nlinarith [F1, F3]
    have hnorm : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
    have F5 : ‖y‖ ^ 2 ≤ (ε⁻¹ ^ 2 + L ^ 2) / s0 := by
      rw [le_div_iff₀ hs0, hnorm]
      nlinarith [F4]
    have hB : ‖y‖ ≤ Real.sqrt ((ε⁻¹ ^ 2 + L ^ 2) / s0) := by
      calc ‖y‖ = Real.sqrt (‖y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt ((ε⁻¹ ^ 2 + L ^ 2) / s0) := Real.sqrt_le_sqrt F5
    linarith

end UnforcedLeray.Short.PartIIIb.NearInst
