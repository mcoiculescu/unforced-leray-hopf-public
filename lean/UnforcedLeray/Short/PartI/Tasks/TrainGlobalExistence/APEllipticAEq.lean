import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEllipticAInt.Helpers

/-!


Source: `the November 2 reference manuscript` lines 285-287. With `Q_k = ∂_q ∂_w f_k`
and `E_k = ∂_η ∂_w f_k`, the divergence `Q_0 + E_1` vanishes, so pointwise
`∑_k |∇ ∂_w f_k|² = (∂_w curl f)² + 2 (Q_1 E_0 - E_1 Q_0)`. The cross term integrates to zero:
the `q`-integration by parts gives `∫ Q_1 E_0 = -∫ ∂_w f_1 · ∂_q ∂_η ∂_w f_0`, the `η`-integration
by parts gives `∫ E_1 Q_0 = -∫ ∂_w f_1 · ∂_η ∂_q ∂_w f_0`, and the two mixed derivatives agree.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open APEllipticHelp

theorem apEllipticAEq : APEllipticAEq := by
  intro j c f hf w _hw
  have hf' := apData_smooth hf
  have hc : 0 < c := lt_of_lt_of_le one_pos (apData_le hf)
  have hs0 := vcomp_smooth hf' 0
  have hs1 := vcomp_smooth hf' 1
  have hpv : ∀ k : Fin 2, B0151.IsPeriodicQ c (vcomp f k) := fun k q η => by
    have h := apData_periodic hf (q, η)
    dsimp only at h
    show f (q + c, η) k = f (q, η) k
    rw [h]
  have hQ : ∀ k : Fin 2, Cyl.partialQ (wordComp w f k) =
      B0151.derivWord (true :: w) (vcomp f k) := fun k => rq_word (vcomp_smooth hf' k) w
  have hE : ∀ k : Fin 2, Cyl.partialEta (wordComp w f k) =
      B0151.derivWord (false :: w) (vcomp f k) := fun k => re_word (vcomp_smooth hf' k) w
  -- periodicity and smoothness of the word derivatives used in the integrations by parts
  have hp1 : Cyl.IsPeriodic c (B0151.derivWord w (vcomp f 1)) :=
    fun z => B0151.periodic_derivWord (hpv 1) w z.1 z.2
  have hp2 : Cyl.IsPeriodic c (B0151.derivWord (false :: w) (vcomp f 0)) :=
    fun z => B0151.periodic_derivWord (hpv 0) (false :: w) z.1 z.2
  have hd1 : Differentiable ℝ (B0151.derivWord w (vcomp f 1)) :=
    (B0151.contDiff_derivWord hs1 w).differentiable (by simp)
  have hd2 : Differentiable ℝ (B0151.derivWord (false :: w) (vcomp f 0)) :=
    (B0151.contDiff_derivWord hs0 (false :: w)).differentiable (by simp)
  -- the `q` integration by parts
  have hI1 : IntegrableOn (fun z => Cyl.partialQ (B0151.derivWord w (vcomp f 1)) z *
      B0151.derivWord (false :: w) (vcomp f 0) z) (Cyl.cell c) := by
    simp only [rq_word hs1 w]
    exact integrableOn_mul_word hf 1 0 (true :: w) (false :: w)
  have hI2 : IntegrableOn (fun z => B0151.derivWord w (vcomp f 1) z *
      Cyl.partialQ (B0151.derivWord (false :: w) (vcomp f 0)) z) (Cyl.cell c) := by
    simp only [rq_word hs0 (false :: w)]
    exact integrableOn_mul_word hf 1 0 w (true :: false :: w)
  have kq := Cyl.integral_cell_partialQ_mul hc (f := B0151.derivWord w (vcomp f 1))
    (g := B0151.derivWord (false :: w) (vcomp f 0)) hd1 hd2 hp1 hp2 hI1 hI2
  rw [rq_word hs1 w, rq_word hs0 (false :: w)] at kq
  -- the `η` integration by parts
  have hJ0 : IntegrableOn (fun z => B0151.derivWord w (vcomp f 1) z *
      B0151.derivWord (true :: w) (vcomp f 0) z) (Cyl.cell c) :=
    integrableOn_mul_word hf 1 0 w (true :: w)
  have hJ1 : IntegrableOn (fun z => Cyl.partialEta (B0151.derivWord w (vcomp f 1)) z *
      B0151.derivWord (true :: w) (vcomp f 0) z) (Cyl.cell c) := by
    simp only [re_word hs1 w]
    exact integrableOn_mul_word hf 1 0 (false :: w) (true :: w)
  have hJ2 : IntegrableOn (fun z => B0151.derivWord w (vcomp f 1) z *
      Cyl.partialEta (B0151.derivWord (true :: w) (vcomp f 0)) z) (Cyl.cell c) := by
    simp only [re_word hs0 (true :: w)]
    exact integrableOn_mul_word hf 1 0 w (false :: true :: w)
  have ke := Cyl.integral_cell_partialEta_mul (f := B0151.derivWord w (vcomp f 1))
    (g := B0151.derivWord (true :: w) (vcomp f 0))
    (hd1) ((B0151.contDiff_derivWord hs0 (true :: w)).differentiable (by simp)) hJ0 hJ1 hJ2
  rw [re_word hs1 w, re_word hs0 (true :: w)] at ke
  -- commutation of the mixed derivatives
  have hG0 : ContDiff ℝ ∞ (B0151.derivWord w (vcomp f 0)) := B0151.contDiff_derivWord hs0 w
  have hcomm : B0151.derivWord (false :: true :: w) (vcomp f 0) =
      B0151.derivWord (true :: false :: w) (vcomp f 0) := by
    have m := mixed_partial hG0
    rw [rq_word hs0 w, re_word hs0 (true :: w), re_word hs0 w, rq_word hs0 (false :: w)] at m
    exact m
  rw [hcomm] at ke
  have hX : ∫ z in Cyl.cell c, B0151.derivWord (true :: w) (vcomp f 1) z *
      B0151.derivWord (false :: w) (vcomp f 0) z =
      ∫ z in Cyl.cell c, B0151.derivWord (false :: w) (vcomp f 1) z *
      B0151.derivWord (true :: w) (vcomp f 0) z := by
    rw [kq, ke]
  -- the cross term integrates to zero
  have hA := integrableOn_mul_word hf 1 0 (true :: w) (false :: w)
  have hB := integrableOn_mul_word hf 1 0 (false :: w) (true :: w)
  have hcross0 : ∫ z in Cyl.cell c, (B0151.derivWord (true :: w) (vcomp f 1) z *
      B0151.derivWord (false :: w) (vcomp f 0) z - B0151.derivWord (false :: w) (vcomp f 1) z *
      B0151.derivWord (true :: w) (vcomp f 0) z) = 0 := by
    rw [integral_sub hA hB, hX, sub_self]
  -- the pointwise identity
  have pw : ∀ z : Plane, ∑ k : Fin 2, (Cyl.partialQ (wordComp w f k) z ^ 2 +
      Cyl.partialEta (wordComp w f k) z ^ 2) =
      (B0151.derivWord (true :: w) (vcomp f 1) z - B0151.derivWord (false :: w) (vcomp f 0) z) ^ 2
      + 2 * (B0151.derivWord (true :: w) (vcomp f 1) z * B0151.derivWord (false :: w) (vcomp f 0) z
        - B0151.derivWord (false :: w) (vcomp f 1) z * B0151.derivWord (true :: w) (vcomp f 0) z) := by
    intro z
    simp only [Fin.sum_univ_two, hQ, hE]
    have hd := div_word_zero hf w z
    linear_combination (B0151.derivWord (true :: w) (vcomp f 0) z
      + B0151.derivWord (false :: w) (vcomp f 1) z) * hd
  simp only [pw]
  have hI_sq := integrableOn_curl_sq hf w
  have hI_cross : IntegrableOn (fun z => B0151.derivWord (true :: w) (vcomp f 1) z *
      B0151.derivWord (false :: w) (vcomp f 0) z - B0151.derivWord (false :: w) (vcomp f 1) z *
      B0151.derivWord (true :: w) (vcomp f 0) z) (Cyl.cell c) := Integrable.sub hA hB
  rw [integral_add hI_sq (hI_cross.const_mul 2), integral_const_mul, hcross0, mul_zero, add_zero]
  have hc2 : (fun z => B0151.derivWord w (Cyl.curl f) z ^ 2) =
      fun z => (B0151.derivWord (true :: w) (vcomp f 1) z
        - B0151.derivWord (false :: w) (vcomp f 0) z) ^ 2 := by
    funext z
    rw [curl_word_eq hf' w z]
  rw [hc2]

end UnforcedLeray.Short.PartI
