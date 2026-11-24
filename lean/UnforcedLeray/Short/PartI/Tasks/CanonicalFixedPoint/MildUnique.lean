import UnforcedLeray.Short.PartI.Sub.PartI_C06
import UnforcedLeray.Short.PartI.Tasks.SmallDiffusionAssembly.MildCocycle
import UnforcedLeray.Units.B0123
import NonUniqueEuler.P.Infra.ODE.Gronwall

/-!


Source of record: `the November 2 reference manuscript`, lines 1117-1119 and the
mild evolution of `lem:short-diffusion-complement`, lines 1014-1058.

Method. Two mild complementary evolutions `U`, `U'` with the same clock `β` satisfy the same
Duhamel identity with the same free term. Subtracting, `D(t) = U(t,s)x - U'(t,s)x` satisfies
`D(t) = ∫_s^t e^{D∫_r^tβ} B_β(r) D(r) dr`, so `‖D(t)‖ ≤ M ∫_s^t ‖D‖` with `M` a bound for
`‖B_β(r)‖`, and the integral Gronwall inequality with zero constant gives `D ≡ 0` on `[s,t]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- Uniqueness core: two solutions of the same Duhamel system with the same generator bound
coincide on `[s,t]`. -/
theorem mcu_core {β : ℝ → ℝ} (hβm : Measurable β) (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ 1)
    {B : ℝ → B0010.XG →L[ℂ] B0010.XG} {M : ℝ} (hBM : ∀ u, ‖B u‖ ≤ M)
    {U U' : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG}
    (hcont : ∀ (s : ℝ) (x : B0010.XG), ContinuousOn (fun t => U t s x) (Ici s))
    (hcont' : ∀ (s : ℝ) (x : B0010.XG), ContinuousOn (fun t => U' t s x) (Ici s))
    (hint : ∀ s t : ℝ, s ≤ t → ∀ x : B0010.XG,
      IntervalIntegrable (fun r => B0123.expD (∫ u in r..t, β u) (B r (U r s x))) volume s t)
    (hint' : ∀ s t : ℝ, s ≤ t → ∀ x : B0010.XG,
      IntervalIntegrable (fun r => B0123.expD (∫ u in r..t, β u) (B r (U' r s x))) volume s t)
    (hdu : ∀ s t : ℝ, s ≤ t → ∀ x : B0010.XG,
      U t s x = B0123.expD (∫ u in s..t, β u) x +
        ∫ r in s..t, B0123.expD (∫ u in r..t, β u) (B r (U r s x)))
    (hdu' : ∀ s t : ℝ, s ≤ t → ∀ x : B0010.XG,
      U' t s x = B0123.expD (∫ u in s..t, β u) x +
        ∫ r in s..t, B0123.expD (∫ u in r..t, β u) (B r (U' r s x)))
    {s t : ℝ} (hst : s ≤ t) (x : B0010.XG) :
    U t s x = U' t s x := by
  have key : ∀ t' : ℝ, t' ∈ Icc s t →
      U t' s x - U' t' s x = ∫ r in s..t',
        B0123.expD (∫ u in r..t', β u) (B r (U r s x - U' r s x)) := by
    intro t' ht'
    have h1 := hdu s t' ht'.1 x
    have h2 := hdu' s t' ht'.1 x
    have hI := hint s t' ht'.1 x
    have hI' := hint' s t' ht'.1 x
    rw [h1, h2, add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub hI hI']
    exact intervalIntegral.integral_congr fun r _ => by simp only [map_sub]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hBM 0)
  have hDc : ContinuousOn (fun u => U u s x - U' u s x) (Ici s) :=
    (hcont s x).sub (hcont' s x)
  have hnD : ContinuousOn (fun u => ‖U u s x - U' u s x‖) (Icc s t) :=
    (hDc.mono Icc_subset_Ici_self).norm
  have hbd : ∀ t' ∈ Icc s t,
      ‖U t' s x - U' t' s x‖ ≤ ∫ u in s..t', M * ‖U u s x - U' u s x‖ := by
    intro t' ht'
    rw [key t' ht']
    refine intervalIntegral.norm_integral_le_of_norm_le ht'.1
      (Filter.Eventually.of_forall fun u hu => ?_) ?_
    · have hBu := hBM u
      calc ‖B0123.expD (∫ v in u..t', β v) (B u (U u s x - U' u s x))‖
          ≤ ‖B0123.expD (∫ v in u..t', β v)‖ * ‖B u (U u s x - U' u s x)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * (‖B u‖ * ‖U u s x - U' u s x‖) :=
            mul_le_mul (B0123.norm_expD_le _) (ContinuousLinearMap.le_opNorm (B u) _)
              (norm_nonneg _) zero_le_one
        _ ≤ 1 * (M * ‖U u s x - U' u s x‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hBu (norm_nonneg _)) zero_le_one
        _ = M * ‖U u s x - U' u s x‖ := one_mul _
    · have hc : ContinuousOn (fun u => M * ‖U u s x - U' u s x‖) (uIcc s t') := by
        rw [Set.uIcc_of_le ht'.1]
        exact continuousOn_const.mul (hnD.mono (Icc_subset_Icc le_rfl ht'.2))
      exact hc.intervalIntegrable
  have hG := NonUniqueEuler.LinODE.int_gronwall
    (u := fun u => ‖U u s x - U' u s x‖) (b := fun _ => M) (c := 0)
    (α := s) (β := t) hnD continuousOn_const (fun _ _ => hM0) le_rfl
    (fun x' hx' => by simpa only [zero_add] using hbd x' hx')
  have h0 := hG t ⟨hst, le_rfl⟩
  simp only [zero_add, zero_mul] at h0
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

/-- **Target `PartI:C06/1`** (source lines 1117-1119): uniqueness of the mild complementary
evolution. -/
theorem mildComplementUnique : MildComplementUnique := by
  intro lam q l _hseed qd _hl hq hqd β hβm hβ U U' hU hU' s t hst
  have hU1 : IsMildComplementEvolution lam (seedKappa l q hq) l q (seedRf l q qd hq hqd) β U := hU
  have hU2 : IsMildComplementEvolution lam (seedKappa l q hq) l q (seedRf l q qd hq hqd) β U' := hU'
  have hBM : ∀ u, ‖(Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q -
      (β u * seedKappa l q hq) • (1 : B0010.XG →L[ℂ] B0010.XG) +
        (β u : ℂ) • seedRf l q qd hq hqd)‖ ≤
      ‖Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - l.smulRight q‖ +
        ‖seedKappa l q hq‖ + ‖seedRf l q qd hq hqd‖ :=
    fun u => mcc_norm_B_le lam l q _ _ (hβ u)
  refine ContinuousLinearMap.ext fun x => ?_
  show U t s x = U' t s x
  exact mcu_core hβm hβ (B := fun u => Planar.L0 - lam • (1 : B0010.XG →L[ℂ] B0010.XG) -
      l.smulRight q - (β u * seedKappa l q hq) • (1 : B0010.XG →L[ℂ] B0010.XG) +
        (β u : ℂ) • seedRf l q qd hq hqd) hBM (U := U) (U' := U')
    (fun s' x' => hU1.cont s' x') (fun s' x' => hU2.cont s' x')
    (fun s' t' hst' x' => hU1.integrable s' t' hst' x')
    (fun s' t' hst' x' => hU2.integrable s' t' hst' x')
    (fun s' t' hst' x' => hU1.duhamel s' t' hst' x')
    (fun s' t' hst' x' => hU2.duhamel s' t' hst' x') hst x

end UnforcedLeray.Short.PartI
