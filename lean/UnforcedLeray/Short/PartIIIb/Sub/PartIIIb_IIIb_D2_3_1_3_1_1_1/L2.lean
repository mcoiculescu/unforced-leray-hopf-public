import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_3_1_1_1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.L4

/-!
# `farPointwise` (`PartIII-b:IIIb-D2/3/1/3/1/1/1/2`)

Source `the November 2 reference manuscript`
3604-3621 (`sep:kernel`), 4155-4186.  On `supp T` (`ϱ z ≤ rOut`) and `2 rOut ≤ ϱ y`,
`|y - l z| ≥ ϱ y - rOut ≥ rOut > 0`, so `sep:kernel` bounds `D^n Φ` by `C farMaj_n`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

lemma farMaj_nonneg (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (n : ℕ)
    (y : Space) (l : ℝ) (z : Space) (hl : 0 < l) : 0 ≤ farMaj μ T τ n y (l, z) := by
  unfold farMaj IIIa.tensorNorm
  simp only
  positivity

lemma far_norm_lower (rOut : ℝ) (y z : Space) (l : ℝ) (hl : l ∈ Ioo (0 : ℝ) 1)
    (hz : ϱ z ≤ rOut) : ϱ y - rOut ≤ ‖y - l • z‖ := by
  have h2 : ϱ y ≤ ‖y - l • z‖ + rOut := by
    have := L4_varrho_tri y (l • z)
    have h' := L4_varrho_le_norm (y - l • z)
    rw [L4_varrho_smul l hl.1.le] at this
    have : l * ϱ z ≤ rOut := by
      nlinarith [ϱ_nonneg z, hl.1, hl.2]
    linarith
  linarith

theorem farPointwise : FarPointwise := by
  intro hK ν μ rOut P T hν hμ hr hP hS τ
  obtain ⟨Cn, hCn0, hCn⟩ := L4_kern hK
  have h2 := heatLerayKSmooth
  refine ⟨18 * Cn, by positivity, ?_⟩
  intro i y hy l hl z
  have hl0 : 0 < l := hl.1
  have key : ∀ n : ℕ, n ≤ 1 →
      ‖iteratedFDeriv ℝ n (sepPhi ν μ T τ i (l, z)) y‖ ≤ 18 * Cn * farMaj μ T τ n y (l, z) := by
    intro n hn
    have hfm := farMaj_nonneg μ T τ n y l z hl0
    by_cases hz : rOut < ϱ z
    · have hT : T (τ + 2 * Real.log l) z = 0 := hS.support _ _ hz
      refine (L4_phi ν μ T τ i l z hl hν h2 n (by omega) y).trans ?_
      have : ∀ j k : Fin 3, ‖(-2 * (l : ℂ) ^ (2 * μ + 2) *
            ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))‖ = 0 := by
        intro j k; simp [hT]
      simp only [this, zero_mul, Finset.sum_const_zero]
      exact mul_nonneg (by positivity) hfm
    · push Not at hz
      have hgeom := far_norm_lower rOut y z l hl hz
      have hx0 : 0 < ‖y - l • z‖ := by linarith
      have hx : y - l • z ≠ 0 := norm_pos_iff.1 hx0
      refine (L4_phi ν μ T τ i l z hl hν h2 n (by omega) y).trans ?_
      have hterm : ∀ j k : Fin 3, ‖(-2 * (l : ℂ) ^ (2 * μ + 2) *
            ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))‖ * ‖coordinateVector k‖ *
          ‖iteratedFDeriv ℝ (n + 1) (fun x => IIIa.heatLerayK (ν * (1 - l ^ 2)) i j x)
            (y - l • z)‖ ≤ 2 * Cn * farMaj μ T τ n y (l, z) := by
        intro j k
        have ht : 0 < ν * (1 - l ^ 2) := by
          have := hl.2; nlinarith [mul_pos hν (sub_pos.2 (show l ^ 2 < 1 by nlinarith))]
        have hk := hCn n (by omega) _ hx i j _ ht
        have he : ‖coordinateVector k‖ = 1 := by simp [coordinateVector]
        have hn1 : ‖(-2 * (l : ℂ) ^ (2 * μ + 2) * ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))‖ ≤
            2 * l ^ (2 * μ.re + 2) * IIIa.tensorNorm (T (τ + 2 * Real.log l) z) := by
          rw [norm_mul, norm_mul, norm_neg, Complex.norm_real,
            Complex.norm_cpow_eq_rpow_re_of_pos hl0]
          simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
            zero_mul, sub_zero, Real.norm_eq_abs]
          have := L4_entry (T (τ + 2 * Real.log l) z) j k
          have hp : 0 ≤ l ^ (2 * μ.re + 2) := by positivity
          have h2' : ‖(2 : ℂ)‖ = 2 := by simp
          rw [h2']
          nlinarith
        rw [he, mul_one]
        have hA : 0 ≤ ‖(-2 * (l : ℂ) ^ (2 * μ + 2) *
            ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ))‖ := norm_nonneg _
        have hp : ‖y - l • z‖ ^ (-4 - (n : ℝ)) = ‖y - l • z‖ ^ (-(4 + (n : ℝ))) := by
          congr 1; ring
        rw [hp] at hk
        calc _ ≤ (2 * l ^ (2 * μ.re + 2) * IIIa.tensorNorm (T (τ + 2 * Real.log l) z)) *
              (Cn * ‖y - l • z‖ ^ (-(4 + (n : ℝ)))) :=
              mul_le_mul hn1 hk (norm_nonneg _)
                (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
          _ = 2 * Cn * farMaj μ T τ n y (l, z) := by
              unfold farMaj; simp only; ring
      refine (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hterm j k).trans ?_
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      nlinarith
  constructor
  · have := key 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero] at this
    exact this
  · have := key 1 (by norm_num)
    rw [norm_iteratedFDeriv_one] at this
    exact this

end UnforcedLeray.Short.PartIIIb.Concrete
