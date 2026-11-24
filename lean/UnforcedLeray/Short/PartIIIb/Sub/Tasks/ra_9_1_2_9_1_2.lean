import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_9_Env
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Cell `L²` bound of the periodised Gaussian envelope (`LatEnvCell`, task `PartIII-b:C/asrc/ra/9/1/2/9/1/2`)

Source `the November 2 reference manuscript` lines 5076-5079.  The lattice sum
`latEnv m ν s` is bounded pointwise on the centred cell by a constant times
`exp(-|η|²/17)` times a polynomial in `η`, using `ageA ν s ∈ [1, 21/10]` (so `1/(8 ageA) ≥ 1/17`)
and `c = cOf ν ≥ 1` (so the lattice terms with `j ≠ 0` decay like `exp(-j²/68)`).  The `avgμ`
integral then reduces by `Cyl.lintegral_cell_eq` to a Gaussian integral in `η`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Polynomial times Gaussian decay: `(1+|η|)^p e^{-γη²} ≤ e^{p²/(2γ)} e^{-γη²/2}`. -/
lemma envDecay (p : ℕ) {γ : ℝ} (hγ : 0 < γ) (η : ℝ) :
    (1 + |η|) ^ p * Real.exp (-γ * η ^ 2)
      ≤ Real.exp ((p : ℝ) ^ 2 / (2 * γ)) * Real.exp (-(γ / 2) * η ^ 2) := by
  have h1 : (1 + |η|) ^ p ≤ Real.exp ((p : ℝ) * |η|) := by
    rw [Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by positivity)
    linarith [Real.add_one_le_exp |η|]
  have h2 : Real.exp ((p : ℝ) * |η|) * Real.exp (-γ * η ^ 2)
      ≤ Real.exp ((p : ℝ) ^ 2 / (2 * γ)) * Real.exp (-(γ / 2) * η ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hX : (p : ℝ) ^ 2 / (2 * γ) * (2 * γ) = (p : ℝ) ^ 2 := by field_simp
    have hab : |η| ^ 2 = η ^ 2 := sq_abs η
    have hmain : (2 * γ) * ((p : ℝ) * |η|)
        ≤ (2 * γ) * ((p : ℝ) ^ 2 / (2 * γ) + (γ / 2) * η ^ 2) := by
      have e : (2 * γ) * ((p : ℝ) ^ 2 / (2 * γ) + (γ / 2) * η ^ 2)
          = (p : ℝ) ^ 2 + γ ^ 2 * η ^ 2 := by
        linear_combination hX
      rw [e]
      nlinarith [sq_nonneg (γ * |η| - p), hab]
    have hmain' := le_of_mul_le_mul_left hmain (by linarith)
    linarith [hmain']
  calc (1 + |η|) ^ p * Real.exp (-γ * η ^ 2)
      ≤ Real.exp ((p : ℝ) * |η|) * Real.exp (-γ * η ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ ≤ _ := h2

/-- Lattice weight: `(1+|j|)^m e^{-j²/68}`. -/
def latEnvW (m : ℕ) (j : ℤ) : ℝ :=
  (1 + |(j : ℝ)|) ^ m * Real.exp (-((1 / 17 : ℝ) / 4) * (j : ℝ) ^ 2)

lemma latEnvW_summable (m : ℕ) : Summable (latEnvW m) := by
  have hg : Summable (fun j : ℤ => Real.exp (-((1 / 17 : ℝ) / 8) * (j : ℝ) ^ 2)) := by
    refine (gp_gauss_summable 0 ((1 / 17 : ℝ) / 8) 1 (by norm_num) one_pos).congr (fun j => ?_)
    congr 1
    ring
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
    (hg.mul_left (Real.exp ((m : ℝ) ^ 2 / (2 * ((1 / 17 : ℝ) / 4)))))
  · unfold latEnvW
    positivity
  · have h := envDecay m (γ := (1 / 17 : ℝ) / 4) (by norm_num) (j : ℝ)
    have e : (1 / 17 : ℝ) / 4 / 2 = (1 / 17 : ℝ) / 8 := by norm_num
    rw [e] at h
    unfold latEnvW
    exact h

/-- The `j`-th lattice term on the centred cell. -/
lemma latEnv_cell_term (m : ℕ) {c q : ℝ} (hc : 1 ≤ c) (hq : |q| ≤ c / 2) (j : ℤ) :
    (1 + |q - (j : ℝ) * c|) ^ m * Real.exp (-(1 / 17 : ℝ) * (q - (j : ℝ) * c) ^ 2)
      ≤ (1 + c) ^ m * latEnvW m j := by
  have hc0 : 0 ≤ c := by linarith
  have hj2 : |(j : ℝ)| ≤ 2 * |q - (j : ℝ) * c| := by
    rcases eq_or_ne (j : ℝ) 0 with hj | hj
    · rw [hj, abs_zero]
      positivity
    · have hj' : j ≠ 0 := by
        intro h
        apply hj
        rw [h]
        simp
      have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
        have h := Int.one_le_abs hj'
        rw [← Int.cast_abs]
        exact_mod_cast h
      have habs : |(j : ℝ) * c| = |(j : ℝ)| * c := by
        rw [abs_mul, abs_of_nonneg hc0]
      have h1 : |(j : ℝ) * c| ≤ |q - (j : ℝ) * c| + |q| := by
        rw [abs_le]
        constructor <;>
          linarith [le_abs_self q, neg_abs_le q, le_abs_self (q - (j : ℝ) * c),
            neg_abs_le (q - (j : ℝ) * c)]
      nlinarith [mul_nonneg (sub_nonneg.2 hj1) hc0, mul_nonneg (abs_nonneg (j : ℝ)) (sub_nonneg.2 hc)]
  have hsq : (j : ℝ) ^ 2 ≤ 4 * (q - (j : ℝ) * c) ^ 2 := by
    have e1 : (2 * |q - (j : ℝ) * c|) ^ 2 = 4 * (q - (j : ℝ) * c) ^ 2 := by
      rw [mul_pow, sq_abs]
      norm_num
    have e2 : |(j : ℝ)| ^ 2 = (j : ℝ) ^ 2 := sq_abs _
    nlinarith [pow_le_pow_left₀ (abs_nonneg _) hj2 2, e1, e2]
  have hexp : Real.exp (-(1 / 17 : ℝ) * (q - (j : ℝ) * c) ^ 2)
      ≤ Real.exp (-((1 / 17 : ℝ) / 4) * (j : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    linarith [hsq]
  have hu1 : |q - (j : ℝ) * c| ≤ |q| + |(j : ℝ)| * c := by
    have e : |(j : ℝ) * c| = |(j : ℝ)| * c := by rw [abs_mul, abs_of_nonneg hc0]
    rw [← e, abs_le]
    constructor <;>
      linarith [le_abs_self q, neg_abs_le q, le_abs_self ((j : ℝ) * c), neg_abs_le ((j : ℝ) * c)]
  have hpow : (1 + |q - (j : ℝ) * c|) ^ m ≤ (1 + c) ^ m * (1 + |(j : ℝ)|) ^ m := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [abs_nonneg (j : ℝ), mul_nonneg (abs_nonneg (j : ℝ)) hc0, hu1, hq]
  calc (1 + |q - (j : ℝ) * c|) ^ m * Real.exp (-(1 / 17 : ℝ) * (q - (j : ℝ) * c) ^ 2)
      ≤ ((1 + c) ^ m * (1 + |(j : ℝ)|) ^ m) * Real.exp (-((1 / 17 : ℝ) / 4) * (j : ℝ) ^ 2) :=
        mul_le_mul hpow hexp (Real.exp_pos _).le
          (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by positivity) _))
    _ = (1 + c) ^ m * latEnvW m j := by
        unfold latEnvW
        ring

/-- Pointwise bound of the lattice sum on the centred cell. -/
lemma latEnv_cell_bound (m : ℕ) {ν s : ℝ} (hc : 1 ≤ cOf ν) (ha : 1 ≤ ageA ν s)
    (ha2 : 8 * ageA ν s ≤ 17) (z : ℝ × ℝ) (hz : |z.1| ≤ cOf ν / 2) :
    latEnv m ν s z ≤ (1 + cOf ν) ^ m * (1 + |z.2|) ^ m * Real.exp (-(1 / 17 : ℝ) * z.2 ^ 2)
      * ∑' j : ℤ, latEnvW m j := by
  have ha0 : 0 < ageA ν s := by linarith
  have h1c : (0 : ℝ) ≤ 1 + cOf ν := by linarith
  have hterm : ∀ j : ℤ,
      (1 + ‖xj ν j z‖) ^ m * Real.exp (-(sq2 (xj ν j z)) / (8 * ageA ν s))
        ≤ (1 + cOf ν) ^ m * (1 + |z.2|) ^ m * Real.exp (-(1 / 17 : ℝ) * z.2 ^ 2)
          * latEnvW m j := by
    intro j
    have hnorm : 1 + ‖xj ν j z‖ ≤ (1 + |z.1 - (j : ℝ) * cOf ν|) * (1 + |z.2|) := by
      have h1 : ‖xj ν j z‖ ≤ |z.1 - (j : ℝ) * cOf ν| + |z.2| := by
        unfold xj
        rw [Prod.norm_def]
        simp only [Real.norm_eq_abs]
        exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
      nlinarith [abs_nonneg (z.1 - (j : ℝ) * cOf ν), abs_nonneg z.2,
        mul_nonneg (abs_nonneg (z.1 - (j : ℝ) * cOf ν)) (abs_nonneg z.2)]
    have hpow1 : (1 + ‖xj ν j z‖) ^ m ≤ (1 + |z.1 - (j : ℝ) * cOf ν|) ^ m * (1 + |z.2|) ^ m := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hnorm m
    have hexp1 : Real.exp (-(sq2 (xj ν j z)) / (8 * ageA ν s))
        ≤ Real.exp (-(1 / 17 : ℝ) * (z.1 - (j : ℝ) * cOf ν) ^ 2) * Real.exp (-(1 / 17 : ℝ) * z.2 ^ 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have e : sq2 (xj ν j z) = (z.1 - (j : ℝ) * cOf ν) ^ 2 + z.2 ^ 2 := rfl
      rw [e]
      have hX : 0 ≤ (z.1 - (j : ℝ) * cOf ν) ^ 2 + z.2 ^ 2 := by positivity
      have hA : (1 / 17 : ℝ) * ((z.1 - (j : ℝ) * cOf ν) ^ 2 + z.2 ^ 2)
          ≤ ((z.1 - (j : ℝ) * cOf ν) ^ 2 + z.2 ^ 2) / (8 * ageA ν s) := by
        rw [le_div_iff₀ (by linarith)]
        nlinarith [mul_nonneg hX (by linarith : (0 : ℝ) ≤ 17 - 8 * ageA ν s)]
      have e2 : -((z.1 - (j : ℝ) * cOf ν) ^ 2 + z.2 ^ 2) / (8 * ageA ν s)
          = -(((z.1 - (j : ℝ) * cOf ν) ^ 2 + z.2 ^ 2) / (8 * ageA ν s)) := neg_div _ _
      rw [e2]
      linarith
    calc (1 + ‖xj ν j z‖) ^ m * Real.exp (-(sq2 (xj ν j z)) / (8 * ageA ν s))
        ≤ ((1 + |z.1 - (j : ℝ) * cOf ν|) ^ m * (1 + |z.2|) ^ m)
            * (Real.exp (-(1 / 17 : ℝ) * (z.1 - (j : ℝ) * cOf ν) ^ 2)
              * Real.exp (-(1 / 17 : ℝ) * z.2 ^ 2)) :=
          mul_le_mul hpow1 hexp1 (Real.exp_pos _).le (by positivity)
      _ = ((1 + |z.2|) ^ m * Real.exp (-(1 / 17 : ℝ) * z.2 ^ 2))
            * ((1 + |z.1 - (j : ℝ) * cOf ν|) ^ m
              * Real.exp (-(1 / 17 : ℝ) * (z.1 - (j : ℝ) * cOf ν) ^ 2)) := by ring
      _ ≤ ((1 + |z.2|) ^ m * Real.exp (-(1 / 17 : ℝ) * z.2 ^ 2))
            * ((1 + cOf ν) ^ m * latEnvW m j) :=
          mul_le_mul_of_nonneg_left (latEnv_cell_term m hc hz j) (by positivity)
      _ = (1 + cOf ν) ^ m * (1 + |z.2|) ^ m * Real.exp (-(1 / 17 : ℝ) * z.2 ^ 2)
            * latEnvW m j := by ring
  unfold latEnv
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum hterm ?_ ?_
  · refine Summable.of_nonneg_of_le (fun j => by positivity) hterm ?_
    exact (latEnvW_summable m).mul_left _
  · exact (latEnvW_summable m).mul_left _

/-- Constant `W = Σ_j (1+|j|)^m e^{-j²/68}` of the lattice sum. -/
def latPhiW (m : ℕ) : ℝ := ∑' j : ℤ, latEnvW m j

/-- Constant `D = e^{((2m+6)²)/(2/17)}` from `envDecay`. -/
def latPhiD (m : ℕ) : ℝ := Real.exp (((2 * m + 6 : ℕ) : ℝ) ^ 2 / (2 * (1 / 17 : ℝ)))

/-- The Gaussian `e^{-η²/34}`. -/
def latPhiG (η : ℝ) : ℝ := Real.exp (-((1 / 17 : ℝ) / 2) * η ^ 2)

/-- The `η`-dominating function of the squared cell integrand. -/
def latPhi (m : ℕ) (ν η : ℝ) : ℝ :=
  latPhiW m ^ 2 * (1 + cOf ν) ^ (2 * m) * (latPhiD m * latPhiG η)

lemma latEnv_sq_bound (m : ℕ) {ν s : ℝ} (hc : 1 ≤ cOf ν) (ha : 1 ≤ ageA ν s)
    (ha2 : 8 * ageA ν s ≤ 17) (z : ℝ × ℝ) (hz : |z.1| ≤ cOf ν / 2) :
    ((1 + |z.2|) ^ 3 * latEnv m ν s z) ^ 2 ≤ latPhi m ν z.2 := by
  have hL := latEnv_cell_bound m hc ha ha2 z hz
  have h1c : (0 : ℝ) ≤ 1 + cOf ν := by linarith
  have hP0 : 0 ≤ (1 + |z.2|) ^ 3 * latEnv m ν s z :=
    mul_nonneg (by positivity) (latEnv_nonneg m ν s z)
  have hR : (1 + |z.2|) ^ 3 * latEnv m ν s z
      ≤ (∑' j : ℤ, latEnvW m j) * (1 + cOf ν) ^ m
          * ((1 + |z.2|) ^ (m + 3) * Real.exp (-(1 / 17 : ℝ) * z.2 ^ 2)) := by
    calc (1 + |z.2|) ^ 3 * latEnv m ν s z
        ≤ (1 + |z.2|) ^ 3 * ((1 + cOf ν) ^ m * (1 + |z.2|) ^ m
            * Real.exp (-(1 / 17 : ℝ) * z.2 ^ 2) * ∑' j : ℤ, latEnvW m j) :=
          mul_le_mul_of_nonneg_left hL (by positivity)
      _ = _ := by ring
  have hR2 := pow_le_pow_left₀ hP0 hR 2
  have he1 : Real.exp (-(1 / 17 : ℝ) * z.2 ^ 2) ≤ 1 := by
    calc Real.exp (-(1 / 17 : ℝ) * z.2 ^ 2) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (by nlinarith [sq_nonneg z.2])
      _ = 1 := Real.exp_zero
  have he : Real.exp (-(1 / 17 : ℝ) * z.2 ^ 2) * Real.exp (-(1 / 17 : ℝ) * z.2 ^ 2)
      ≤ Real.exp (-(1 / 17 : ℝ) * z.2 ^ 2) :=
    mul_le_of_le_one_right (Real.exp_pos _).le he1
  have hdec := envDecay (2 * m + 6) (γ := (1 / 17 : ℝ)) (by norm_num) z.2
  have hW : 0 ≤ ∑' j : ℤ, latEnvW m j :=
    tsum_nonneg (fun j => by unfold latEnvW; positivity)
  have hK0 : 0 ≤ (∑' j : ℤ, latEnvW m j) ^ 2 * (1 + cOf ν) ^ (2 * m) :=
    mul_nonneg (sq_nonneg _) (pow_nonneg h1c _)
  calc ((1 + |z.2|) ^ 3 * latEnv m ν s z) ^ 2
      ≤ ((∑' j : ℤ, latEnvW m j) * (1 + cOf ν) ^ m
          * ((1 + |z.2|) ^ (m + 3) * Real.exp (-(1 / 17 : ℝ) * z.2 ^ 2))) ^ 2 := hR2
    _ = ((∑' j : ℤ, latEnvW m j) ^ 2 * (1 + cOf ν) ^ (2 * m))
          * ((1 + |z.2|) ^ (2 * m + 6)
            * (Real.exp (-(1 / 17 : ℝ) * z.2 ^ 2) * Real.exp (-(1 / 17 : ℝ) * z.2 ^ 2))) := by
        ring
    _ ≤ ((∑' j : ℤ, latEnvW m j) ^ 2 * (1 + cOf ν) ^ (2 * m))
          * ((1 + |z.2|) ^ (2 * m + 6) * Real.exp (-(1 / 17 : ℝ) * z.2 ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (by positivity)) hK0
    _ ≤ ((∑' j : ℤ, latEnvW m j) ^ 2 * (1 + cOf ν) ^ (2 * m))
          * (Real.exp (((2 * m + 6 : ℕ) : ℝ) ^ 2 / (2 * (1 / 17 : ℝ)))
            * Real.exp (-((1 / 17 : ℝ) / 2) * z.2 ^ 2)) :=
        mul_le_mul_of_nonneg_left hdec hK0
    _ = latPhi m ν z.2 := by
        unfold latPhi latPhiW latPhiD latPhiG
        ring

lemma cOf_ge_one {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) : 1 ≤ cOf ν := by
  unfold cOf
  exact (one_le_inv₀ (by positivity)).mpr (by nlinarith)

/-- Final numerical comparison. -/
lemma latFinalNum (W Q c t : ℝ) (m : ℕ) (hQ : 0 ≤ Q)
    (hct : c = t ^ 2) (hc : 1 ≤ c) :
    W ^ 2 * (1 + c) ^ (2 * m) * Q ≤ (W * 2 ^ m * (Q + 1) * t ^ (2 * m)) ^ 2 := by
  have hb : (1 + c) ^ (2 * m) ≤ 4 ^ m * c ^ (2 * m) := by
    calc (1 + c) ^ (2 * m) ≤ (2 * c) ^ (2 * m) :=
          pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = 4 ^ m * c ^ (2 * m) := by
          rw [mul_pow, show (2 : ℝ) ^ (2 * m) = 4 ^ m by rw [pow_mul]; norm_num]
  have hc2 : c ^ (2 * m) = (t ^ (2 * m)) ^ 2 := by
    rw [hct]
    ring
  have h4 : (4 : ℝ) ^ m = (2 ^ m) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hc0 : 0 ≤ c := by linarith
  calc W ^ 2 * (1 + c) ^ (2 * m) * Q
      ≤ W ^ 2 * (4 ^ m * c ^ (2 * m)) * Q :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (sq_nonneg W)) hQ
    _ ≤ W ^ 2 * (4 ^ m * c ^ (2 * m)) * (Q + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith)
          (mul_nonneg (sq_nonneg W) (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg hc0 _)))
    _ = (W * 2 ^ m * (Q + 1) * t ^ (2 * m)) ^ 2 := by
        rw [hc2, h4]
        ring

theorem latEnvCell : LatEnvCell := by
  unfold LatEnvCell
  intro m
  refine ⟨latPhiW m * 2 ^ m * (latPhiD m * (∫ η : ℝ, latPhiG η) + 1), 2 * m, 1, ?_, one_pos, ?_⟩
  · have hW : 0 ≤ latPhiW m := by
      unfold latPhiW
      exact tsum_nonneg (fun j => by unfold latEnvW; positivity)
    have hD : 0 ≤ latPhiD m := (Real.exp_pos _).le
    have hJ : 0 ≤ ∫ η : ℝ, latPhiG η :=
      integral_nonneg (fun η => (Real.exp_pos _).le)
    have hQ : 0 ≤ latPhiD m * (∫ η : ℝ, latPhiG η) + 1 :=
      add_nonneg (mul_nonneg hD hJ) zero_le_one
    exact mul_nonneg (mul_nonneg hW (by positivity)) hQ
  intro ν hν hν1 s hs hs1
  have hc : 1 ≤ cOf ν := cOf_ge_one hν hν1
  have hc0 : 0 < cOf ν := by linarith
  have hsν : ν * s ≤ 11 / 10 := by
    rw [mul_comm]
    exact (le_div_iff₀ hν).mp hs1
  have ha : 1 ≤ ageA ν s := by
    unfold ageA
    nlinarith [mul_pos hν hs]
  have ha2 : 8 * ageA ν s ≤ 17 := by
    unfold ageA
    linarith
  have hct : cOf ν = ν⁻¹ ^ 2 := by
    unfold cOf
    rw [inv_pow]
  have hpt : ∀ z ∈ UnforcedLeray.Cyl.cell (cOf ν),
      ENNReal.ofReal (((1 + |z.2|) ^ 3 * latEnv m ν s z) ^ 2) ≤ ENNReal.ofReal (latPhi m ν z.2) := by
    intro z hz
    apply ENNReal.ofReal_le_ofReal
    have hz1 : z.1 ∈ Set.Ico (-cOf ν / 2) (cOf ν / 2) := (Set.mem_prod.mp hz).1
    exact latEnv_sq_bound m hc ha ha2 z
      (abs_le.mpr ⟨by linarith [hz1.1], by linarith [hz1.2]⟩)
  have hmeasCell : MeasurableSet (UnforcedLeray.Cyl.cell (cOf ν)) :=
    measurableSet_Ico.prod MeasurableSet.univ
  have hgi : Integrable (fun η : ℝ => Real.exp (-((1 / 17 : ℝ) / 2) * η ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hΦint : Integrable (fun η : ℝ => latPhi m ν η) := by
    unfold latPhi latPhiG
    exact (hgi.const_mul (latPhiD m)).const_mul (latPhiW m ^ 2 * (1 + cOf ν) ^ (2 * m))
  have hΦnn : 0 ≤ᵐ[volume] (fun η : ℝ => latPhi m ν η) := by
    refine ae_of_all _ (fun η => ?_)
    unfold latPhi latPhiD latPhiG
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith) _))
      (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  have hmeasΦ : Measurable (fun η : ℝ => latPhi m ν η) := by
    unfold latPhi latPhiG
    fun_prop
  have hmeasF : AEMeasurable (fun z : ℝ × ℝ => ENNReal.ofReal (latPhi m ν z.2))
      (UnforcedLeray.Cyl.cellμ (cOf ν)) :=
    ((hmeasΦ.comp measurable_snd).ennreal_ofReal).aemeasurable
  have hvol : volume (Set.Ico (-cOf ν / 2) (cOf ν / 2)) = ENNReal.ofReal (cOf ν) := by
    rw [Real.volume_Ico]
    congr 1
    ring
  have hstep2 : ∫⁻ z in UnforcedLeray.Cyl.cell (cOf ν), ENNReal.ofReal (latPhi m ν z.2)
      = ENNReal.ofReal (∫ η, latPhi m ν η) * ENNReal.ofReal (cOf ν) := by
    refine (UnforcedLeray.Cyl.lintegral_cell_eq hmeasF).trans ?_
    have hI : ∫⁻ η, ENNReal.ofReal (latPhi m ν η)
        = ENNReal.ofReal (∫ η, latPhi m ν η) :=
      (ofReal_integral_eq_lintegral_ofReal hΦint hΦnn).symm
    simp only [hI]
    rw [setLIntegral_const, hvol]
  have hstep1 : ∫⁻ z in UnforcedLeray.Cyl.cell (cOf ν),
      ENNReal.ofReal (((1 + |z.2|) ^ 3 * latEnv m ν s z) ^ 2)
        ≤ ∫⁻ z in UnforcedLeray.Cyl.cell (cOf ν), ENNReal.ofReal (latPhi m ν z.2) :=
    setLIntegral_mono' hmeasCell hpt
  have key : ENNReal.ofReal (cOf ν)⁻¹ * ENNReal.ofReal (cOf ν) = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc0.le), inv_mul_cancel₀ hc0.ne', ENNReal.ofReal_one]
  have hint : ∫ η : ℝ, latPhi m ν η
      = latPhiW m ^ 2 * (1 + cOf ν) ^ (2 * m) * (latPhiD m * ∫ η : ℝ, latPhiG η) := by
    unfold latPhi
    rw [integral_const_mul, integral_const_mul]
  have hIle : ∫ η : ℝ, latPhi m ν η
      ≤ (latPhiW m * 2 ^ m * (latPhiD m * (∫ η : ℝ, latPhiG η) + 1) * ν⁻¹ ^ (2 * m)) ^ 2 := by
    rw [hint]
    have hJ : 0 ≤ ∫ η : ℝ, latPhiG η :=
      integral_nonneg (fun η => (Real.exp_pos _).le)
    have hQ : 0 ≤ latPhiD m * (∫ η : ℝ, latPhiG η) :=
      mul_nonneg (Real.exp_pos _).le hJ
    exact latFinalNum _ _ _ _ m hQ hct hc
  rw [UnforcedLeray.Cyl.lintegral_avgμ]
  calc ENNReal.ofReal (cOf ν)⁻¹ * ∫⁻ z in UnforcedLeray.Cyl.cell (cOf ν),
        ENNReal.ofReal (((1 + |z.2|) ^ 3 * latEnv m ν s z) ^ 2)
      ≤ ENNReal.ofReal (cOf ν)⁻¹ * ∫⁻ z in UnforcedLeray.Cyl.cell (cOf ν),
          ENNReal.ofReal (latPhi m ν z.2) := by gcongr
    _ = ENNReal.ofReal (cOf ν)⁻¹ * (ENNReal.ofReal (∫ η, latPhi m ν η) * ENNReal.ofReal (cOf ν)) := by
        rw [hstep2]
    _ = (ENNReal.ofReal (cOf ν)⁻¹ * ENNReal.ofReal (cOf ν)) * ENNReal.ofReal (∫ η, latPhi m ν η) := by
        ring
    _ = ENNReal.ofReal (∫ η, latPhi m ν η) := by
        rw [key, one_mul]
    _ ≤ ENNReal.ofReal ((latPhiW m * 2 ^ m * (latPhiD m * (∫ η : ℝ, latPhiG η) + 1)
          * ν⁻¹ ^ (2 * m)) ^ 2) := ENNReal.ofReal_le_ofReal hIle

end UnforcedLeray.Short.PartIIIb.Concrete
